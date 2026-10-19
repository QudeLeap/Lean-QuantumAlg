#!/usr/bin/env python3
"""Run the pinned Batteries custom linter over every tracked library module.

A temporary, declaration-free aggregate imports the complete source inventory.
The existing driver then loads one environment and checks each declaration once,
including modules outside the public root's import closure. Probe sources stay
outside the checkout. Compiled probe artifacts occupy an exclusively owned
temporary directory in the package's build tree and are removed on failure too.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib


SPEC = importlib.util.spec_from_file_location(
    "full_lint_build_cache", Path(__file__).with_name("build-cache.py"))
cache = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cache)


def module_names(sources: list[str]) -> list[str]:
    """Reject paths that cannot be emitted as unescaped Lean module names."""
    for source in sources:
        path = PurePosixPath(source)
        if (path.as_posix() != source or path.suffix != ".lean"
                or any(part == "_" or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", part)
                       for part in path.with_suffix("").parts)):
            raise cache.CacheError(f"unsupported Lean module path: {source!r}")
    return cache.modules_of(sources)


def write_receipt(path: Path, identity: dict) -> None:
    """Publish only a successful receipt, without replacing an earlier result."""
    path.parent.mkdir(parents=True, exist_ok=True)
    stream = path.open("x", encoding="utf-8")
    try:
        with stream:
            json.dump({"format_version": 1, **identity}, stream, sort_keys=True, indent=2)
            stream.write("\n")
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def full_lint(root: Path, *, receipt: Path | None = None, runner=subprocess.run) -> dict:
    root = root.resolve()
    if receipt is not None and (receipt.exists() or receipt.is_symlink()):
        raise cache.CacheError("lint receipt already exists")
    identity, sources = cache.source_identity(root, runner=runner)
    modules = module_names(sources)
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    if (config.get("lintDriver") != "batteries/runLinter"
            or config.get("lintDriverArgs", []) != []):
        raise cache.CacheError("full lint requires batteries/runLinter without configured module arguments")
    print(f"Full custom lint: {len(modules)} tracked modules at {identity['source_sha']}.", flush=True)
    cache.run(["lake", "build", "@batteries/runLinter"], root, runner=runner)
    with tempfile.TemporaryDirectory(prefix="quantumalg-full-lint-",
                                     dir=os.environ.get("RUNNER_TEMP") or None) as directory:
        temporary = Path(directory).resolve()
        if temporary.is_relative_to(root):
            raise cache.CacheError("full-lint temporary directory must be outside the source checkout")
        stem = "ReleaseLintAudit_" + secrets.token_hex(16)
        module = "QuantumAlg." + stem + ".Aggregate"
        probe = temporary / "QuantumAlg" / stem / "Aggregate.lean"
        probe.parent.mkdir(parents=True)
        probe.write_text("module\n\n" + "".join(f"public import {name}\n" for name in modules),
                         encoding="utf-8")
        # Lean selects the first search-path directory containing QuantumAlg,
        # without falling back for absent individual modules. Keep probe outputs
        # beside the existing package products, never in its source directory.
        artifact_parent = root / ".lake/build/lib/lean/QuantumAlg"
        if not artifact_parent.is_dir():
            raise cache.CacheError("build all library modules before running full lint")
        artifacts = artifact_parent / stem
        artifacts.mkdir()  # Exclusive ownership; an existing directory is never removed.
        env = os.environ.copy()
        try:
            print("Compiling the isolated full-library import probe.", flush=True)
            cache.run(["lake", "env", "lean", "--root=" + str(temporary),
                       "-o", str(artifacts / "Aggregate.olean"), str(probe)],
                      root, runner=runner, env=env)
            print("Running the pinned custom lint driver on the complete library.", flush=True)
            cache.run(["lake", "--no-build", "lint", "--", "--no-build", module],
                      root, runner=runner, env=env)
        finally:
            shutil.rmtree(artifacts)
    if cache.source_identity(root, runner=runner) != (identity, sources):
        raise cache.CacheError("source identity changed during full lint")
    if receipt is not None:
        write_receipt(receipt, identity)
    print(f"Full custom lint passed for {len(modules)} tracked modules.", flush=True)
    return identity


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args(argv)
    try:
        full_lint(args.root, receipt=args.receipt)
    except (ValueError, OSError) as error:
        print(f"full-lint: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
