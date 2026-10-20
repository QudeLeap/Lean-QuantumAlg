#!/usr/bin/env python3
"""Build and distribute a source-bound Lake cache for Linux x86_64.

Only current, Git-tracked library modules enter the archive. Packing includes a
mandatory restoration check in an isolated source directory, with compilation
and additional cache downloads disabled. No repository or Release is modified.
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


def allowed_members(sources: list[str]) -> set[str]:
    paths = set()
    for name in sources:
        module_path = name[:-5]
        for prefix, suffixes in (("lib/lean", LIB_SUFFIXES), ("ir", IR_SUFFIXES)):
            for suffix in suffixes:
                relative = f"{prefix}/{module_path}.{suffix}"
                paths.add(relative)
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


def require_outputs(build_dir: Path, sources: list[str], *, allowed_roots=None) -> set[str]:
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
        for relative in required:
            if not (build_dir / relative).is_file():
                raise CacheError(f"required cache output is missing: {relative}")
            check_regular_file(build_dir / relative, allowed_roots)
        members.update(required)
        members.add(base + ".trace")
    return members


def stage_outputs(root: Path, sources: list[str], stage: Path) -> list[str]:
    build_dir = root / ".lake/build"
    roots = artifact_roots(root)
    required = require_outputs(build_dir, sources, allowed_roots=roots)
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
    require_outputs(stage, sources)
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


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "pack"):
        command = commands.add_parser(name)
        command.add_argument("--root", type=Path, default=Path.cwd())
        if name == "pack":
            command.add_argument("--repository", required=True)
            command.add_argument("--run-id", required=True)
            command.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        if args.command == "build":
            build(root)
        else:
            pack(root, args.output_dir.resolve(), args.repository, args.run_id)
    except (CacheError, OSError, tarfile.TarError) as error:
        print(f"build-cache: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
