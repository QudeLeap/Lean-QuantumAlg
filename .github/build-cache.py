#!/usr/bin/env python3
"""Build and distribute a source-bound Lake cache for Linux x86_64.

Only current, Git-tracked library modules enter a staged cache. Release packing
includes a mandatory restoration check in an isolated source directory, with
compilation and additional cache downloads disabled. CI staging materializes
complete owner products after the caller's successful build and lint. No
repository or Release is modified.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile


PLATFORM = "x86_64-unknown-linux-gnu"
ARCHIVE_NAME = f"QuantumAlg-{PLATFORM}.tar.gz"
MAX_ARCHIVE_BYTES = 2 * 1024**3
CONFIG_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
LIB_SUFFIXES = ("olean", "ilean", "olean.server", "olean.private", "ir.sig", "ir", "trace")
IR_SUFFIXES = ("c", "bc")
CI_FORMAT = "quantumalg.owner-cache/v2"


class CacheError(ValueError):
    """The source or cache cannot safely be distributed."""


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def canonical_json(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def run(command, root: Path, *, runner=subprocess.run, capture=False, env=None):
    result = runner(command, cwd=root, text=True, capture_output=capture, env=env)
    if result.returncode:
        detail = (result.stderr or "").strip() if capture else ""
        raise CacheError(f"{command[0]} failed ({result.returncode})" + (f": {detail}" if detail else ""))
    return result.stdout.strip() if capture else None


def inventory_digest(root: Path, sources: list[str]) -> str:
    return digest(canonical_json({name: file_digest(root / name) for name in sources}))


def source_identity(root: Path, *, runner=subprocess.run) -> tuple[dict, list[str]]:
    """Reject tracked changes and source shadows before recording committed inputs."""
    sha = run(["git", "rev-parse", "HEAD"], root, runner=runner, capture=True)
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise CacheError("expected a full Git commit identity")
    if run(["git", "status", "--porcelain", "--untracked-files=no"], root,
           runner=runner, capture=True):
        raise CacheError("tracked checkout changes must be committed before packing")
    names = run(["git", "ls-tree", "-rz", "--name-only", "HEAD"], root,
                runner=runner, capture=True).split("\0")
    sources = sorted(name for name in names if name == "QuantumAlg.lean"
                     or (name.startswith("QuantumAlg/") and name.endswith(".lean")))
    if "QuantumAlg.lean" not in sources:
        raise CacheError("the committed library root is missing")
    for name in sources + list(CONFIG_FILES):
        path = root / name
        if name not in names or path.is_symlink() or not path.is_file():
            raise CacheError(f"expected a committed regular source/configuration file: {name}")
    actual = {p.relative_to(root).as_posix() for p in (root / "QuantumAlg").rglob("*.lean")}
    actual.add("QuantumAlg.lean")
    if actual != set(sources):
        raise CacheError("untracked or missing library sources would change the cached module set")
    toolchain_bytes = (root / "lean-toolchain").read_bytes()
    toolchain = toolchain_bytes.decode("utf-8").strip()
    if not toolchain or "\n" in toolchain:
        raise CacheError("invalid Lean toolchain")
    return {
        "source_sha": sha,
        "toolchain": toolchain,
        "toolchain_sha256": digest(toolchain_bytes),
        "manifest_sha256": file_digest(root / "lake-manifest.json"),
        "source_inventory_sha256": inventory_digest(root, sources),
        "module_count": len(sources),
    }, sources


def modules_of(sources: list[str]) -> list[str]:
    return [name[:-5].replace("/", ".") for name in sources]


def active_platform(root: Path, *, runner=subprocess.run) -> str:
    # The pinned Lean CLI exposes the target in --version, not a target-only flag.
    version = run(["lean", "--version"], root, runner=runner, capture=True)
    match = re.search(r"\(version ([^,]+), ([^,]+), commit [0-9a-f]+,", version)
    if not match or match[2] != PLATFORM:
        raise CacheError(f"only the {PLATFORM} Lean toolchain is supported")
    pin = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    if pin != f"leanprover/lean4:v{match[1]}":
        raise CacheError("active Lean version does not match the committed release toolchain")
    return match[2]


def build(root: Path, *, runner=subprocess.run) -> None:
    _, sources = source_identity(root, runner=runner)
    active_platform(root, runner=runner)
    print(f"Building {len(sources)} current library modules with --wfail.", flush=True)
    run(["lake", "build", "--wfail", *modules_of(sources)], root, runner=runner)


def allowed_members(sources: list[str], *, include_hashes=False) -> set[str]:
    paths = set()
    for name in sources:
        module_path = name[:-5]
        for prefix, suffixes in (("lib/lean", LIB_SUFFIXES), ("ir", IR_SUFFIXES)):
            for suffix in suffixes:
                relative = f"{prefix}/{module_path}.{suffix}"
                paths.add(relative)
                if include_hashes and suffix != "trace":
                    paths.add(relative + ".hash")
    return paths


def artifact_roots(root: Path) -> list[Path]:
    """Known Lake content-store locations, plus this package's build directory."""
    pin = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    toolchain_directory = pin.replace("/", "--").replace(":", "---")
    elan_home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    cache_home = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    roots = [root / ".lake/build",
             elan_home / "toolchains" / toolchain_directory / "lake/cache/artifacts",
             cache_home / "lake/artifacts"]
    if os.environ.get("LAKE_CACHE_DIR"):
        roots.append(Path(os.environ["LAKE_CACHE_DIR"]) / "artifacts")
    return [path.resolve() for path in roots]


def check_regular_file(path: Path, allowed_roots: list[Path]) -> None:
    resolved = path.resolve()
    if not path.is_file() or not any(resolved.is_relative_to(base) for base in allowed_roots):
        raise CacheError(f"cache output is not a regular file within a permitted artifact store: {path.name}")


def require_outputs(build_dir: Path, sources: list[str], *, allowed_roots=None,
                    include_hashes=False) -> set[str]:
    """Lake 4.33 module outputs include split olean/IR and generated C files."""
    allowed_roots = allowed_roots or [build_dir.resolve()]
    members = set()
    for name in sources:
        module_path = name[:-5]
        base = "lib/lean/" + module_path
        trace = build_dir / (base + ".trace")
        if trace.exists() or trace.is_symlink():
            check_regular_file(trace, allowed_roots)
        try:
            outputs = json.loads(trace.read_text(encoding="utf-8"))["outputs"]
            is_module = outputs["m"]
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise CacheError(f"missing or malformed build trace for {name}") from error
        if not isinstance(is_module, bool):
            raise CacheError(f"invalid module mode in build trace for {name}")
        required = [base + ".olean", base + ".ilean", "ir/" + module_path + ".c"]
        if is_module:
            required += [base + "." + suffix for suffix in ("olean.server", "olean.private", "ir.sig", "ir")]
        if outputs.get("b") is not None:
            required.append("ir/" + module_path + ".bc")
        if include_hashes:
            required += [relative + ".hash" for relative in required]
        for relative in required:
            if not (build_dir / relative).is_file():
                raise CacheError(f"required cache output is missing: {relative}")
            check_regular_file(build_dir / relative, allowed_roots)
        members.update(required)
        members.add(base + ".trace")
    return members


def stage_outputs(root: Path, sources: list[str], stage: Path, *, include_hashes=False) -> list[str]:
    build_dir = root / ".lake/build"
    roots = artifact_roots(root)
    required = require_outputs(build_dir, sources, allowed_roots=roots,
                               include_hashes=include_hashes)
    members = []
    for relative in sorted(required):
        source = build_dir / relative
        # Lake may link outputs into its content-addressed artifact store. Copy
        # regular referents, never links themselves; the restore gate validates
        # their actual contents before anything enters the output directory.
        check_regular_file(source, roots)
        destination = stage / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        members.append(relative)
    require_outputs(stage, sources, include_hashes=include_hashes)
    return members


def write_archive(stage: Path, members: list[str], archive: Path) -> None:
    with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT) as tar:
            for name in sorted(members):
                source = stage / name
                item = tarfile.TarInfo(name)
                item.size = source.stat().st_size
                item.mode = 0o644
                item.mtime = item.uid = item.gid = 0
                item.uname = item.gname = ""
                with source.open("rb") as content:
                    tar.addfile(item, content)
    if archive.stat().st_size >= MAX_ARCHIVE_BYTES:
        raise CacheError("the build archive must be smaller than 2 GiB")


def extract_archive(archive: Path, destination: Path, sources: list[str]) -> None:
    allowed = allowed_members(sources)
    seen = set()
    with tarfile.open(archive, "r:gz") as tar:
        for item in tar:
            name = item.name
            if (name not in allowed or name in seen or not item.isfile()
                    or PurePosixPath(name).is_absolute() or ".." in PurePosixPath(name).parts):
                raise CacheError(f"unexpected or unsafe archive member: {name}")
            seen.add(name)
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            content = tar.extractfile(item)
            if content is None:
                raise CacheError(f"archive member has no content: {name}")
            with content, target.open("wb") as output:
                shutil.copyfileobj(content, output)
    required = require_outputs(destination, sources)
    if seen != required:
        raise CacheError("archive contains artifacts not referenced by current module traces")


def restore_check(root: Path, archive: Path, sources: list[str], *, runner=subprocess.run) -> None:
    dependencies = root / ".lake/packages"
    if not dependencies.is_dir():
        raise CacheError("the pinned dependency checkout/build tree is required for restore verification")
    with tempfile.TemporaryDirectory(prefix="quantumalg-cache-restore-") as directory:
        restored = Path(directory)
        for name in sources + list(CONFIG_FILES):
            destination = restored / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / name, destination)
        (restored / ".lake").mkdir()
        (restored / ".lake/packages").symlink_to(dependencies.resolve(), target_is_directory=True)
        extract_archive(archive, restored / ".lake/build", sources)
        # This check must not repair a broken archive from a global artifact
        # cache, fetch release caches, or compile missing module artifacts.
        env = dict(os.environ, LAKE_ARTIFACT_CACHE="false", LAKE_CACHE_DIR="")
        run(["lake", "--no-build", "--no-cache", "build", "--wfail", *modules_of(sources)],
            restored, runner=runner, env=env)


def validate_names(repository: str, run_id: str) -> None:
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
        raise CacheError("repository must be OWNER/REPO")
    if not re.fullmatch(r"[1-9][0-9]*", str(run_id)):
        raise CacheError("run-id must be a positive GitHub Actions run identifier")


def pack(root: Path, output: Path, repository: str, run_id: str, *, runner=subprocess.run) -> dict:
    validate_names(repository, run_id)
    identity, sources = source_identity(root, runner=runner)
    platform = active_platform(root, runner=runner)
    names = (ARCHIVE_NAME, ARCHIVE_NAME + ".json", ARCHIVE_NAME + ".sha256")
    if any((output / name).exists() for name in names):
        raise CacheError("cache output already exists; refusing to overwrite it")
    with tempfile.TemporaryDirectory(prefix="quantumalg-cache-pack-") as directory:
        temporary = Path(directory)
        stage = temporary / "build"
        members = stage_outputs(root, sources, stage)
        archive = temporary / ARCHIVE_NAME
        write_archive(stage, members, archive)
        restore_check(root, archive, sources, runner=runner)
        if source_identity(root, runner=runner) != (identity, sources):
            raise CacheError("source identity changed while preparing the cache")
        metadata = {"format_version": 1, "repository": repository, **identity,
                    "platform": platform, "run_id": str(run_id), "archive_name": ARCHIVE_NAME,
                    "archive_sha256": file_digest(archive)}
        (temporary / names[1]).write_bytes(canonical_json(metadata) + b"\n")
        (temporary / names[2]).write_text(f"{metadata['archive_sha256']}  {ARCHIVE_NAME}\n", encoding="utf-8")
        output.mkdir(parents=True, exist_ok=True)
        for name in names:
            # Exclusive creation also rejects races with another producer.
            with (temporary / name).open("rb") as source, (output / name).open("xb") as target:
                shutil.copyfileobj(source, target)
    print(f"Verified cache: {len(sources)} modules, {metadata['archive_sha256'][:12]}, {ARCHIVE_NAME}", flush=True)
    return metadata


def ci_identity(root: Path, *, runner=subprocess.run) -> tuple[dict, list[str]]:
    """Separate compatible build pins from the source inventory used for an exact hit."""
    identity, sources = source_identity(root, runner=runner)
    compatible = {"platform": active_platform(root, runner=runner),
                  **{name: file_digest(root / name) for name in CONFIG_FILES}}
    prefix = "quantumalg-owner-v2-" + digest(canonical_json(compatible)) + "-"
    return {"format": CI_FORMAT, "compatible": compatible, "identity": identity,
            "sources": sources, "key": prefix + identity["source_inventory_sha256"],
            "restore_prefix": prefix}, sources


def ci_key(root: Path, *, runner=subprocess.run) -> dict:
    metadata, _ = ci_identity(root, runner=runner)
    return {name: metadata[name] for name in ("key", "restore_prefix")}


def ci_stage(root: Path, directory: Path, *, runner=subprocess.run) -> dict:
    """Materialize complete current owner products after the workflow's build/lint."""
    metadata, sources = ci_identity(root, runner=runner)
    if directory == root or root.is_relative_to(directory):
        raise CacheError("CI cache directory must not contain the checkout")
    if directory.exists() and not (directory / "cache.json").is_file():
        raise CacheError("refusing to replace a directory without a CI cache manifest")
    directory.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="quantumalg-ci-stage-", dir=directory.parent) as temporary:
        staged = Path(temporary) / "next"
        # Lake reconstructs missing .hash files even when --no-build succeeds.
        # Keep these metadata files so verification needs no owner-tree writes.
        members = stage_outputs(root, sources, staged / "build", include_hashes=True)
        metadata["members"] = {name: file_digest(staged / "build" / name) for name in members}
        (staged / "cache.json").write_bytes(canonical_json(metadata) + b"\n")
        if ci_identity(root, runner=runner)[0] != {k: v for k, v in metadata.items() if k != "members"}:
            raise CacheError("source identity changed while staging the CI cache")
        if directory.exists():
            directory.rename(Path(temporary) / "previous")
        staged.rename(directory)
    return metadata


def inspect_ci_cache(root: Path, directory: Path, *, runner=subprocess.run) -> tuple:
    """Check every staged owner product before applying or verifying the cache."""
    current, sources = ci_identity(root, runner=runner)
    try:
        cached = json.loads((directory / "cache.json").read_text())
        old_sources = cached["sources"]
        members = cached["members"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise CacheError("missing or malformed CI cache manifest") from error
    if (cached.get("format") != CI_FORMAT or cached.get("compatible") != current["compatible"]
            or not isinstance(old_sources, list) or not old_sources
            or not all(isinstance(name, str) and (name == "QuantumAlg.lean"
                       or (name.startswith("QuantumAlg/") and name.endswith(".lean")))
                       and not PurePosixPath(name).is_absolute() and ".." not in PurePosixPath(name).parts
                       for name in old_sources)
            or len(set(old_sources)) != len(old_sources)
            or not isinstance(members, dict)):
        raise CacheError("CI cache format, configuration or source inventory is incompatible")
    required = require_outputs(directory / "build", old_sources, include_hashes=True)
    actual = {p.relative_to(directory / "build").as_posix()
              for p in (directory / "build").rglob("*") if p.is_file() or p.is_symlink()}
    if set(members) != required or actual != required:
        raise CacheError("CI cache member inventory does not match complete owner products")
    for name, expected in members.items():
        path = directory / "build" / name
        if path.is_symlink() or not isinstance(expected, str) or file_digest(path) != expected:
            raise CacheError(f"CI cache member is linked or changed: {name}")
    return current, sources, cached, old_sources, required


def ci_restore(root: Path, directory: Path, *, runner=subprocess.run) -> dict:
    """Retain current owners only; the subsequent full build validates sources."""
    current, sources, cached, _, required = inspect_ci_cache(root, directory, runner=runner)
    # A source-compatible fallback may include retired owners. Do not restore
    # them, and remove only this package's obsolete owner products from a reused
    # build directory. Dependency caches and other packages are untouched.
    allowed = allowed_members(sources, include_hashes=True)
    build_dir = root / ".lake/build"
    removed = []
    for prefix in ("lib/lean", "ir"):
        owner_root = build_dir / prefix
        candidates = list((owner_root / "QuantumAlg").rglob("*"))
        candidates += list(owner_root.glob("QuantumAlg.*"))
        for path in candidates:
            if (path.is_file() or path.is_symlink()) and path.relative_to(build_dir).as_posix() not in allowed:
                removed.append(path.relative_to(build_dir).as_posix())
                path.unlink()
    restored = 0
    for name in sorted(required & allowed):
        target = build_dir / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.is_symlink():
            target.unlink()
        shutil.copyfile(directory / "build" / name, target)
        restored += 1
    exact = cached.get("key") == current["key"]
    if exact:
        require_outputs(build_dir, sources, include_hashes=True)
    return {"exact_source": exact, "restored_products": restored, "removed_products": sorted(removed)}


def ci_verify(root: Path, directory: Path, *, runner=subprocess.run) -> dict:
    """Prove an exact staged cache builds without compilation in an isolated tree."""
    if directory.is_relative_to(root) or root.is_relative_to(directory):
        raise CacheError("CI cache verification staging must be outside the source checkout")
    current, sources, cached, old_sources, required = inspect_ci_cache(root, directory, runner=runner)
    if cached.get("key") != current["key"] or old_sources != sources:
        raise CacheError("no-build verification requires an exact owner-source cache")
    dependencies = root / ".lake/packages"
    if not dependencies.is_dir():
        raise CacheError("the pinned dependency checkout/build tree is required for restore verification")
    # Hard-link the already hashed regular files into a separate build tree.
    # This avoids a second multi-GiB copy on GitHub-hosted runners; verifying
    # their hashes again after Lake also detects any unexpected write.
    with tempfile.TemporaryDirectory(prefix="quantumalg-ci-verify-", dir=directory.parent) as temporary:
        restored = Path(temporary)
        for name in sources + list(CONFIG_FILES):
            destination = restored / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / name, destination)
        (restored / ".lake").mkdir()
        (restored / ".lake/packages").symlink_to(dependencies.resolve(), target_is_directory=True)
        build_dir = restored / ".lake/build"
        for name in sorted(required):
            destination = build_dir / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            os.link(directory / "build" / name, destination)
        require_outputs(build_dir, sources, include_hashes=True)
        env = dict(os.environ, LAKE_ARTIFACT_CACHE="false", LAKE_CACHE_DIR="")
        run(["lake", "--no-build", "--no-cache", "build", "--wfail", *modules_of(sources)],
            restored, runner=runner, env=env)
        actual = {p.relative_to(build_dir).as_posix() for p in build_dir.rglob("*")
                  if p.is_file() or p.is_symlink()}
        if actual != required:
            raise CacheError("no-build verification changed the owner product inventory")
        for name in required:
            staged = directory / "build" / name
            linked = build_dir / name
            if (linked.is_symlink() or not linked.is_file()
                    or linked.stat().st_ino != staged.stat().st_ino
                    or file_digest(staged) != cached["members"][name]):
                raise CacheError(f"CI cache member changed during no-build verification: {name}")
    if ci_identity(root, runner=runner)[0] != current:
        raise CacheError("source identity changed during CI cache verification")
    return {"verified_modules": len(sources), "verified_products": len(required), "key": current["key"]}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "pack", "ci-key", "ci-stage", "ci-restore", "ci-verify"):
        command = commands.add_parser(name)
        command.add_argument("--root", type=Path, default=Path.cwd())
        if name == "pack":
            command.add_argument("--repository", required=True)
            command.add_argument("--run-id", required=True)
            command.add_argument("--output-dir", type=Path, required=True)
        if name in ("ci-stage", "ci-restore", "ci-verify"):
            command.add_argument("--directory", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        if args.command == "build":
            build(root)
        elif args.command == "pack":
            pack(root, args.output_dir.resolve(), args.repository, args.run_id)
        elif args.command == "ci-key":
            for name, value in ci_key(root).items():
                print(f"{name}={value}")
        elif args.command == "ci-stage":
            metadata = ci_stage(root, args.directory.resolve())
            print(f"Staged {len(metadata['sources'])} complete owner products for {metadata['key']}")
        elif args.command == "ci-verify":
            print(json.dumps(ci_verify(root, args.directory.resolve()), sort_keys=True))
        else:
            print(json.dumps(ci_restore(root, args.directory.resolve()), sort_keys=True))
    except (CacheError, OSError, tarfile.TarError) as error:
        print(f"build-cache: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
