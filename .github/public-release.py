#!/usr/bin/env python3
"""Build and finish a source-bound release within its own GitHub repository.

The handoff is an annotated tag, a draft Release and one verified site archive.
Release CI publishes its cache directly. Publication restores that exact cache
and requires a separate full-library lint receipt before Pages or Release writes.
Network/process boundaries are injectable.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

VERSION = re.compile(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\Z")
SHA = re.compile(r"[0-9a-f]{40}\Z")
HASH = re.compile(r"[0-9a-f]{64}\Z")
RUN_ID = re.compile(r"[1-9][0-9]*\Z")
WORKFLOW = ".github/workflows/release-ci.yml"
BUILD_STEPS = {"Build all library modules", "Pack and restore cache", "Upload cache archive"}
PLATFORM = "x86_64-unknown-linux-gnu"
ARCHIVE = f"QuantumAlg-{PLATFORM}.tar.gz"
SITE_ASSET = "release-site.tar.gz"
MAX_BYTES = 2 * 1024**3
SITE_KEYS = {"format_version", "version", "source_sha", "notes_sha256", "site_sha256", "index_sha256"}


class ReleaseError(RuntimeError):
    """A failed release precondition; existing remote content is never replaced."""


class APIError(ReleaseError):
    def __init__(self, status, path):
        self.status = status
        super().__init__(f"GitHub API HTTP {status}: {path}")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def validate_version(value):
    if not isinstance(value, str) or not VERSION.fullmatch(value):
        raise ReleaseError("version must be a bare X.Y.Z")
    return value


def validate_sha(value):
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise ReleaseError("a full source commit SHA is required")
    return value


def run_process(args, *, cwd=None, env=None, runner=subprocess.run, check=True):
    result = runner(list(map(str, args)), cwd=cwd, env=env, text=True,
                    capture_output=True, encoding="utf-8", errors="replace")
    if check and result.returncode:
        message = (result.stderr or result.stdout or "").strip()
        for key in ("GH_TOKEN", "GITHUB_TOKEN", "GIT_CONFIG_VALUE_0"):
            if secret := (env or os.environ).get(key):
                message = message.replace(secret, "[redacted]")
        raise ReleaseError(f"{args[0]} failed ({result.returncode}): {message}")
    return result


class GitHub:
    def __init__(self, repository, token="", *, opener=urllib.request.urlopen):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise ReleaseError("repository must be OWNER/REPO")
        self.repository, self.token, self.opener = repository, token, opener

    def request(self, method, path, data=None):
        headers = {"Accept": "application/vnd.github+json", "User-Agent": "quantumalg-release",
                   "X-GitHub-Api-Version": "2022-11-28"}
        if self.token:
            headers["Authorization"] = f"Bearer {self.token}"
        payload = None if data is None else json.dumps(data).encode()
        if payload is not None:
            headers["Content-Type"] = "application/json"
        request = urllib.request.Request("https://api.github.com/" + path.lstrip("/"),
                                         data=payload, headers=headers, method=method)
        try:
            with self.opener(request, timeout=60) as response:
                content = response.read()
            return json.loads(content) if content else None
        except urllib.error.HTTPError as error:
            raise APIError(error.code, path) from None

    def optional(self, path):
        try:
            return self.request("GET", path)
        except APIError as error:
            if error.status == 404:
                return None
            raise

    def pages(self, path, key=None):
        separator = "&" if "?" in path else "?"
        for page in range(1, 101):
            result = self.request("GET", f"{path}{separator}per_page=100&page={page}")
            rows = result[key] if key else result
            yield from rows
            if len(rows) < 100:
                return
        raise ReleaseError("GitHub pagination exceeded its bound")


def endpoint(api, suffix):
    return f"repos/{api.repository}/{suffix}"


def annotated_tag(api, version):
    ref = api.optional(endpoint(api, f"git/ref/tags/{validate_version(version)}"))
    if not ref or ref.get("object", {}).get("type") != "tag":
        raise ReleaseError("the release must have an annotated tag")
    tag = api.request("GET", endpoint(api, f"git/tags/{ref['object']['sha']}"))
    if tag.get("tag") != version or tag.get("object", {}).get("type") != "commit":
        raise ReleaseError("the release tag must directly annotate its source commit")
    return {"source_sha": validate_sha(tag["object"]["sha"]), "tag_sha": ref["object"]["sha"]}


def get_release(api, version):
    # Listing authenticated releases includes drafts, unlike the tag lookup route.
    matches = [item for item in api.pages(endpoint(api, "releases")) if item.get("tag_name") == version]
    if len(matches) != 1:
        raise ReleaseError("expected exactly one existing Release for the selected tag")
    release = matches[0]
    if release.get("prerelease") or not isinstance(release.get("body"), str) or not release["body"].strip():
        raise ReleaseError("the selected Release must have stable, nonempty release notes")
    return release


def require_no_newer_release(api, version):
    """A delayed draft must not replace a newer release or its deployed website."""
    selected = tuple(map(int, validate_version(version).split(".")))
    latest = api.optional(endpoint(api, "releases/latest"))
    if latest is None:
        return
    latest_version = latest.get("tag_name")
    if not isinstance(latest_version, str) or not VERSION.fullmatch(latest_version):
        raise ReleaseError("Latest Release has an unrecognized version; resolve its ordering before publication")
    if tuple(map(int, latest_version.split("."))) > selected:
        raise ReleaseError(f"newer Latest Release {latest_version} already exists; refusing to roll back to {version}")


def assets_for(api, release):
    assets = list(api.pages(endpoint(api, f"releases/{release['id']}/assets")))
    result = {}
    for asset in assets:
        name = asset.get("name")
        if name in result or name not in (ARCHIVE, SITE_ASSET):
            raise ReleaseError("unexpected or duplicate Release attachment")
        result[name] = asset
    return result


def asset_digest(asset):
    value = asset.get("digest") or ""
    if (asset.get("state") != "uploaded" or type(asset.get("size")) is not int
            or not 0 < asset["size"] < MAX_BYTES
            or not re.fullmatch(r"sha256:[0-9a-f]{64}", value)):
        raise ReleaseError("Release asset must have complete bytes and a GitHub SHA-256 digest")
    return value[7:]


def successful_build(api, run_id, attempt):
    # Pin the current attempt: an older successful attempt must not excuse
    # skipped build or upload steps in the run supplied for publication.
    if type(attempt) is not int or attempt < 1:
        raise ReleaseError("Release CI must identify its current attempt")
    jobs = list(api.pages(endpoint(api, f"actions/runs/{run_id}/attempts/{attempt}/jobs"), "jobs"))
    return any(job.get("name") == "build" and job.get("conclusion") == "success"
               and BUILD_STEPS <= {step.get("name") for step in job.get("steps", [])
                                   if step.get("conclusion") == "success"} for job in jobs)


def require_run(api, run_id, source_sha, *, completed=True, full_build=False):
    if not RUN_ID.fullmatch(str(run_id)):
        raise ReleaseError("run-id must be a positive GitHub Actions run identifier")
    run = api.request("GET", endpoint(api, f"actions/runs/{run_id}"))
    if (str(run.get("id")) != str(run_id) or run.get("head_sha") != source_sha
            or run.get("head_branch") != "main"
            or run.get("path", "").split("@", 1)[0] != WORKFLOW
            or run.get("event") not in ("repository_dispatch", "workflow_dispatch")):
        raise ReleaseError("release producer must be trusted Release CI on main at the selected source")
    if completed and (run.get("status") != "completed" or run.get("conclusion") != "success"):
        raise ReleaseError("Release CI has not completed successfully; select a successful Release CI run")
    if full_build and not successful_build(api, run_id, run.get("run_attempt")):
        raise ReleaseError("Release CI lacks the complete successful build, pack and upload gates")
    return run


def require_cache(assets):
    if ARCHIVE not in assets:
        raise ReleaseError("the release cache archive is missing")
    return asset_digest(assets[ARCHIVE])


def tree_digest(root):
    result = hashlib.sha256()
    for path in sorted(Path(root).rglob("*")):
        if path.is_symlink():
            raise ReleaseError("site tree contains a symlink")
        if path.is_file():
            result.update(path.relative_to(root).as_posix().encode() + b"\0")
            result.update(bytes.fromhex(file_digest(path)))
    return result.hexdigest()


def validate_site(directory, version, source_sha, body):
    directory = Path(directory)
    path = directory / "release.json"
    if path.is_symlink() or not path.is_file():
        raise ReleaseError("the site handoff metadata is missing")
    metadata = json.loads(path.read_text(encoding="utf-8"))
    if (not isinstance(metadata, dict) or set(metadata) != SITE_KEYS
            or type(metadata.get("format_version")) is not int or metadata["format_version"] != 1
            or metadata.get("version") != validate_version(version)
            or metadata.get("source_sha") != validate_sha(source_sha)):
        raise ReleaseError("site handoff metadata does not match the selected version and source")
    if any(not isinstance(metadata.get(key), str) or not HASH.fullmatch(metadata[key])
           for key in ("notes_sha256", "site_sha256", "index_sha256")):
        raise ReleaseError("invalid site handoff digest")
    if metadata["notes_sha256"] != digest(body.encode("utf-8")):
        raise ReleaseError("existing Release body conflicts with the handoff; refusing to overwrite")
    site = directory / "site"
    if not (site / "index.html").is_file() or not (site / ".nojekyll").is_file():
        raise ReleaseError("the site requires index.html and .nojekyll")
    if (tree_digest(site) != metadata["site_sha256"]
            or file_digest(site / "index.html") != metadata["index_sha256"]):
        raise ReleaseError("site content differs from its handoff digests")
    return metadata


def extract_site(archive, directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    if any(directory.iterdir()):
        raise ReleaseError("site extraction directory must be empty")
    seen, total = set(), 0
    with tarfile.open(archive, "r:gz") as tar:
        for item in tar:
            path = PurePosixPath(item.name)
            name = path.as_posix()
            if (path.is_absolute() or ".." in path.parts or "\\" in item.name
                    or name in seen or not path.parts or ".git" in path.parts
                    or not (name == "release.json" or path.parts[0] == "site")
                    or not (item.isdir() or item.isfile())
                    or (name == "release.json" and not item.isfile())):
                raise ReleaseError("site archive contains an unsafe or unexpected member")
            seen.add(name)
            total += item.size
            if total >= MAX_BYTES or len(seen) > 100000:
                raise ReleaseError("site archive exceeds the extraction bound")
            target = directory.joinpath(*path.parts)
            if item.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(item) as source, target.open("xb") as output:
                    shutil.copyfileobj(source, output)


def download_site(api, release, asset, output, *, runner=subprocess.run):
    expected = asset_digest(asset)
    with tempfile.TemporaryDirectory(prefix="release-site-download-") as temporary:
        run_process(["gh", "release", "download", release["tag_name"], "--repo", api.repository,
                     "--pattern", SITE_ASSET, "--dir", temporary], runner=runner)
        archive = Path(temporary) / SITE_ASSET
        if archive.is_symlink() or not archive.is_file() or archive.stat().st_size != asset["size"] or file_digest(archive) != expected:
            raise ReleaseError("downloaded site archive differs from GitHub's asset digest")
        extract_site(archive, output)


def verify_handoff(api, version, source_sha, *, runner=subprocess.run):
    tag = annotated_tag(api, version)
    if tag["source_sha"] != validate_sha(source_sha):
        raise ReleaseError("annotated tag source conflicts with the requested commit")
    release = get_release(api, version)
    assets = assets_for(api, release)
    if SITE_ASSET in assets:
        with tempfile.TemporaryDirectory(prefix="release-handoff-") as temporary:
            directory = Path(temporary) / "handoff"
            download_site(api, release, assets[SITE_ASSET], directory, runner=runner)
            validate_site(directory, version, source_sha, release["body"])
    elif release.get("draft"):
        raise ReleaseError("draft Release is missing its site handoff")
    return tag, release, assets


def resolve_build(api, version, source_sha, *, runner=subprocess.run):
    _, release, assets = verify_handoff(api, version, source_sha, runner=runner)
    if ARCHIVE in assets or not release.get("draft"):
        require_cache(assets)
    # Drafts always execute their own complete build and restore gates. A
    # completed release needs no new build, upload or publication.
    return {"version": version, "source_sha": source_sha,
            "ready": "true" if release.get("draft") else "false"}


def cache_helper():
    spec = importlib.util.spec_from_file_location("quantumalg_build_cache", Path(__file__).with_name("build-cache.py"))
    cache = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cache)
    return cache


def validate_cache(directory, source_root, repository, source_sha, run_id, *, runner=subprocess.run):
    cache = cache_helper()
    identity, _ = cache.source_identity(Path(source_root), runner=runner)
    if identity["source_sha"] != source_sha:
        raise ReleaseError("cache checkout does not match the selected annotated source")
    directory = Path(directory)
    names = {ARCHIVE, ARCHIVE + ".json", ARCHIVE + ".sha256"}
    if {path.name for path in directory.iterdir()} != names:
        raise ReleaseError("cache staging must contain exactly its archive, metadata and checksum")
    if any(path.is_symlink() or not path.is_file() for path in directory.iterdir()):
        raise ReleaseError("cache staging files must be regular files")
    record = json.loads((directory / (ARCHIVE + ".json")).read_text(encoding="utf-8"))
    expected = {"format_version": 1, "repository": repository, **identity,
                "platform": PLATFORM, "archive_name": ARCHIVE, "run_id": str(run_id)}
    if not isinstance(record, dict) or any(record.get(key) != value for key, value in expected.items()):
        raise ReleaseError("cache provenance differs from the source, toolchain or producer")
    archive_hash = file_digest(directory / ARCHIVE)
    if (not 0 < (directory / ARCHIVE).stat().st_size < MAX_BYTES
            or record.get("archive_sha256") != archive_hash
            or (directory / (ARCHIVE + ".sha256")).read_text() != f"{archive_hash}  {ARCHIVE}\n"):
        raise ReleaseError("cache archive/checksum digest mismatch")
    return record


def upload_cache(api, version, source_sha, run_id, source_root, directory, *, runner=subprocess.run):
    record = validate_cache(directory, source_root, api.repository, source_sha, run_id, runner=runner)
    require_run(api, run_id, source_sha, completed=False)
    _, release, assets = verify_handoff(api, version, source_sha, runner=runner)
    if not release.get("draft"):
        require_cache(assets)
    path = Path(directory) / ARCHIVE
    if existing := assets.get(ARCHIVE):
        if asset_digest(existing) != record["archive_sha256"] or existing["size"] != path.stat().st_size:
            raise ReleaseError("existing cache bytes conflict; refusing to replace the archive")
    else:
        run_process(["gh", "release", "upload", version, path, "--repo", api.repository], runner=runner)
    actual = assets_for(api, release).get(ARCHIVE)
    if not actual or asset_digest(actual) != record["archive_sha256"] or actual["size"] != path.stat().st_size:
        raise ReleaseError("uploaded cache bytes failed readback")


def prepare_finalize(api, run_id, output, *, version=None, runner=subprocess.run):
    run = api.request("GET", endpoint(api, f"actions/runs/{run_id}"))
    source_sha = validate_sha(run.get("head_sha"))
    require_run(api, run_id, source_sha)
    versions = [validate_version(version)] if version else [item["tag_name"]
        for item in api.pages(endpoint(api, "releases")) if VERSION.fullmatch(item.get("tag_name", ""))]
    candidates = [value for value in versions if annotated_tag(api, value)["source_sha"] == source_sha]
    if len(candidates) != 1:
        raise ReleaseError("successful Release CI must identify exactly one matching release version")
    version = candidates[0]
    tag = annotated_tag(api, version)
    release = get_release(api, version)
    assets = assets_for(api, release)
    require_cache(assets)
    if SITE_ASSET not in assets:
        if release.get("draft"):
            raise ReleaseError("draft Release is missing its site handoff")
        return {"version": version, "source_sha": source_sha, "ready": "false"}
    require_run(api, run_id, source_sha, full_build=True)
    output = Path(output)
    download_site(api, release, assets[SITE_ASSET], output, runner=runner)
    metadata = validate_site(output, version, source_sha, release["body"])
    prepared = {"repository": api.repository, **metadata, "run_id": str(run_id),
                "tag_sha": tag["tag_sha"],
                "release_id": release["id"], "site_asset_id": assets[SITE_ASSET]["id"],
                "site_asset_sha256": asset_digest(assets[SITE_ASSET]),
                "cache_asset_id": assets[ARCHIVE]["id"], "cache_sha256": asset_digest(assets[ARCHIVE])}
    (output / "prepared.json").write_text(json.dumps(prepared, sort_keys=True) + "\n", encoding="utf-8")
    return {"version": version, "source_sha": source_sha, "ready": "true"}


def check_prepared(api, directory):
    directory = Path(directory)
    prepared = json.loads((directory / "prepared.json").read_text(encoding="utf-8"))
    if prepared.get("repository") != api.repository:
        raise ReleaseError("prepared release belongs to a different repository")
    version, sha = prepared["version"], prepared["source_sha"]
    tag = annotated_tag(api, version)
    if tag != {"source_sha": sha, "tag_sha": prepared["tag_sha"]}:
        raise ReleaseError("annotated tag changed after preparation")
    require_run(api, prepared["run_id"], sha, full_build=True)
    release = get_release(api, version)
    if release["id"] != prepared["release_id"]:
        raise ReleaseError("Release identity changed after preparation")
    metadata = validate_site(directory, version, sha, release["body"])
    if any(prepared.get(key) != value for key, value in metadata.items()):
        raise ReleaseError("prepared site metadata changed")
    assets = assets_for(api, release)
    require_cache(assets)
    if (assets[ARCHIVE]["id"] != prepared["cache_asset_id"]
            or asset_digest(assets[ARCHIVE]) != prepared["cache_sha256"]):
        raise ReleaseError("cache archive changed after preparation")
    if SITE_ASSET in assets:
        if (assets[SITE_ASSET]["id"] != prepared["site_asset_id"]
                or asset_digest(assets[SITE_ASSET]) != prepared["site_asset_sha256"]):
            raise ReleaseError("site handoff asset changed after preparation")
    elif release.get("draft"):
        raise ReleaseError("draft site handoff disappeared after preparation")
    return prepared, release, assets


def restore_lint_cache(api, directory, source_root, *, runner=subprocess.run):
    """Restore verified draft bytes into the exact source checkout, without compiling it."""
    prepared, release, assets = check_prepared(api, directory)
    source_root = Path(source_root).resolve()
    cache = cache_helper()
    identity, sources = cache.source_identity(source_root, runner=runner)
    if identity["source_sha"] != prepared["source_sha"]:
        raise ReleaseError("lint checkout differs from the selected annotated source")
    cache.active_platform(source_root, runner=runner)
    destination = source_root / ".lake/build"
    if destination.is_symlink() or (destination.exists() and any(destination.iterdir())):
        raise ReleaseError("lint cache restore requires an empty library build directory")
    with tempfile.TemporaryDirectory(prefix="release-lint-cache-") as temporary:
        run_process(["gh", "release", "download", prepared["version"], "--repo", api.repository,
                     "--pattern", ARCHIVE, "--dir", temporary], runner=runner)
        archive = Path(temporary) / ARCHIVE
        if (archive.is_symlink() or not archive.is_file()
                or archive.stat().st_size != assets[ARCHIVE]["size"]
                or file_digest(archive) != prepared["cache_sha256"]):
            raise ReleaseError("downloaded lint cache differs from the verified Release asset")
        cache.extract_archive(archive, destination, sources)
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="false", LAKE_CACHE_DIR="")
    cache.run(["lake", "--no-build", "--no-cache", "build", "--wfail", *cache.modules_of(sources)],
              source_root, runner=runner, env=env)
    if cache.source_identity(source_root, runner=runner) != (identity, sources):
        raise ReleaseError("source identity changed during lint cache restoration")
    check_prepared(api, directory)
    prepared["lint_identity"] = identity
    (Path(directory) / "prepared.json").write_text(json.dumps(prepared, sort_keys=True) + "\n")


def require_full_lint(directory, prepared):
    path = Path(directory) / "lint.json"
    identity = prepared.get("lint_identity")
    if (not isinstance(identity, dict) or identity.get("source_sha") != prepared["source_sha"]
            or type(identity.get("module_count")) is not int or identity["module_count"] <= 0
            or path.is_symlink() or not path.is_file()):
        raise ReleaseError("full-library lint of the restored release source has not passed")
    receipt = json.loads(path.read_text(encoding="utf-8"))
    if receipt != {"format_version": 1, **identity}:
        raise ReleaseError("full-library lint receipt differs from the restored release source")


class Git:
    def __init__(self, token="", *, runner=subprocess.run):
        self.runner = runner
        self.env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
        if token:
            encoded = base64.b64encode(f"x-access-token:{token}".encode()).decode()
            self.env.update(GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="http.https://github.com/.extraheader",
                            GIT_CONFIG_VALUE_0=f"AUTHORIZATION: basic {encoded}")

    def run(self, *args, cwd=None, check=True):
        return run_process(["git", *args], cwd=cwd, env=self.env, runner=self.runner, check=check)


def sync_site(api, git, directory):
    prepared, release, _ = check_prepared(api, directory)
    require_full_lint(directory, prepared)
    require_no_newer_release(api, prepared["version"])
    source = Path(directory) / "site"
    url = f"https://github.com/{api.repository}.git"
    with tempfile.TemporaryDirectory(prefix="release-pages-") as temporary:
        checkout = Path(temporary) / "repo"
        exists = git.run("ls-remote", "--exit-code", "--heads", url, "gh-pages", check=False)
        if exists.returncode not in (0, 2):
            raise ReleaseError("could not inspect the Pages branch")
        git.run("clone", "--depth", "1", "--branch", "gh-pages" if exists.returncode == 0 else "main", url, checkout)
        if exists.returncode == 2:
            git.run("switch", "--orphan", "gh-pages", cwd=checkout)
        cname = (checkout / "CNAME").read_bytes() if (checkout / "CNAME").is_file() else None
        if not (checkout / ".git").is_dir():
            raise ReleaseError("Pages destination must be a disposable Git checkout")
        for path in checkout.iterdir():
            if path.name == ".git":
                continue
            if path.is_dir() and not path.is_symlink():
                shutil.rmtree(path)
            else:
                path.unlink()
        shutil.copytree(source, checkout, dirs_exist_ok=True)
        if cname is not None:
            (checkout / "CNAME").write_bytes(cname)
        git.run("config", "user.name", "Lean-QuantumAlg Maintainers", cwd=checkout)
        git.run("config", "user.email", "noreply@github.com", cwd=checkout)
        git.run("config", "commit.gpgsign", "false", cwd=checkout)
        git.run("add", "-A", cwd=checkout)
        changed = git.run("diff", "--cached", "--quiet", cwd=checkout, check=False)
        if changed.returncode not in (0, 1):
            raise ReleaseError("could not compare the Pages projection")
        if not release.get("draft") and (changed.returncode or exists.returncode == 2):
            raise ReleaseError("published documentation differs; refusing to roll the site back")
        if changed.returncode or exists.returncode == 2:
            check_prepared(api, directory)
            require_no_newer_release(api, prepared["version"])
            git.run("commit", "-m", f"Release {prepared['version']} documentation", cwd=checkout)
            git.run("push", "origin", "HEAD:gh-pages", cwd=checkout)
        sha = git.run("rev-parse", "HEAD", cwd=checkout).stdout.strip()
        remote = git.run("ls-remote", "origin", "refs/heads/gh-pages", cwd=checkout).stdout.split()
        if not remote or remote[0] != sha:
            raise ReleaseError("Pages branch readback differs from the selected commit")
        return validate_sha(sha)


def wait_pages(api, pages_sha, *, timeout=1800, interval=30, clock=time.monotonic, sleep=time.sleep):
    validate_sha(pages_sha)
    deadline = clock() + timeout
    while True:
        ref = api.request("GET", endpoint(api, "git/ref/heads/gh-pages"))
        if ref.get("object", {}).get("sha") != pages_sha:
            raise ReleaseError("Pages branch moved during release finalization")
        runs = [item for item in api.pages(endpoint(api, f"actions/runs?head_sha={pages_sha}"), "workflow_runs")
                if item.get("head_sha") == pages_sha and item.get("name") == "pages build and deployment"]
        if any(item.get("status") == "completed" and item.get("conclusion") == "success" for item in runs):
            return
        if runs and all(item.get("status") == "completed" for item in runs):
            raise ReleaseError("Pages deployment did not complete successfully")
        remaining = deadline - clock()
        if remaining <= 0:
            raise ReleaseError("timed out waiting for the exact Pages commit")
        print("Waiting for Pages deployment of the selected commit.", flush=True)
        sleep(min(interval, remaining))


def verify_live_site(api, prepared, *, opener=urllib.request.urlopen, sleep=time.sleep, attempts=10):
    pages = api.request("GET", endpoint(api, "pages"))
    url = pages.get("html_url")
    if not isinstance(url, str) or not url.startswith("https://"):
        raise ReleaseError("Pages did not report an HTTPS site URL")
    separator = "&" if "?" in url else "?"
    url += separator + urllib.parse.urlencode({"release": prepared["version"], "source": prepared["source_sha"]})
    for attempt in range(attempts):
        request = urllib.request.Request(url, headers={"Cache-Control": "no-cache"})
        try:
            with opener(request, timeout=60) as response:
                current = digest(response.read())
            if current == prepared["index_sha256"]:
                return
        except (urllib.error.HTTPError, urllib.error.URLError):
            pass
        if attempt + 1 < attempts:
            sleep(30)
    raise ReleaseError("deployed homepage does not match the selected site bytes")


def finish(api, directory, pages_sha, *, waiter=wait_pages, live_check=verify_live_site):
    prepared, _, _ = check_prepared(api, directory)
    require_full_lint(directory, prepared)
    waiter(api, pages_sha)
    live_check(api, prepared)
    prepared, release, assets = check_prepared(api, directory)
    require_full_lint(directory, prepared)
    if api.request("GET", endpoint(api, "git/ref/heads/gh-pages")).get("object", {}).get("sha") != pages_sha:
        raise ReleaseError("Pages branch moved before formal Release publication")
    require_no_newer_release(api, prepared["version"])
    if release.get("draft"):
        api.request("PATCH", endpoint(api, f"releases/{release['id']}"),
                    {"draft": False, "prerelease": False, "make_latest": "true"})
    actual = get_release(api, prepared["version"])
    if actual.get("draft") or actual.get("prerelease") or digest(actual["body"].encode()) != prepared["notes_sha256"]:
        raise ReleaseError("formal Release body/status readback failed")
    latest = api.request("GET", endpoint(api, "releases/latest"))
    if latest.get("id") != actual["id"]:
        raise ReleaseError("formal Release is not the repository's Latest Release")
    # Publishing first keeps the handoff recoverable if Pages or publication fails.
    # A retry after publication still verifies all the same receipts before cleanup.
    check_prepared(api, directory)
    if SITE_ASSET in assets:
        api.request("DELETE", endpoint(api, f"releases/assets/{assets[SITE_ASSET]['id']}"))
    final = assets_for(api, actual)
    if set(final) != {ARCHIVE}:
        raise ReleaseError("formal Release must retain only its build cache archive")
    require_cache(final)
    if asset_digest(final[ARCHIVE]) != prepared["cache_sha256"]:
        raise ReleaseError("final cache archive changed during publication")
    return actual["html_url"]


def output_value(name, value):
    print(f"{name}: {value}", flush=True)
    if path := os.environ.get("GITHUB_OUTPUT"):
        with open(path, "a", encoding="utf-8") as stream:
            stream.write(f"{name}={value}\n")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", "QudeLeap/Lean-QuantumAlg"))
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("resolve-build", "upload-cache"):
        child = commands.add_parser(name)
        child.add_argument("--version", required=True)
        child.add_argument("--sha", required=True)
        if name == "upload-cache":
            child.add_argument("--run-id", required=True)
            child.add_argument("--source-root", type=Path, required=True)
            child.add_argument("--directory", type=Path, required=True)
    child = commands.add_parser("prepare-finalize")
    child.add_argument("--run-id", required=True)
    child.add_argument("--version")
    child.add_argument("--output", type=Path, required=True)
    for name in ("restore-lint-cache", "sync-site", "finish"):
        child = commands.add_parser(name)
        child.add_argument("--prepared", type=Path, required=True)
        if name == "restore-lint-cache":
            child.add_argument("--source-root", type=Path, required=True)
        if name == "finish":
            child.add_argument("--pages-sha", required=True)
    args = parser.parse_args(argv)
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN", "")
    api = GitHub(args.repository, token)
    try:
        if args.command == "resolve-build":
            result = resolve_build(api, args.version, args.sha)
        elif args.command == "upload-cache":
            upload_cache(api, args.version, args.sha, args.run_id, args.source_root, args.directory)
            result = {"archive": ARCHIVE}
        elif args.command == "prepare-finalize":
            result = prepare_finalize(api, args.run_id, args.output, version=args.version)
        elif args.command == "restore-lint-cache":
            restore_lint_cache(api, args.prepared, args.source_root)
            result = {"restored": "true"}
        elif args.command == "sync-site":
            result = {"pages_sha": sync_site(api, Git(token), args.prepared)}
        else:
            result = {"release_url": finish(api, args.prepared, args.pages_sha)}
        for name, value in result.items():
            output_value(name, value)
        return 0
    except (ReleaseError, OSError, ValueError, KeyError, tarfile.TarError) as error:
        print(f"release: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
