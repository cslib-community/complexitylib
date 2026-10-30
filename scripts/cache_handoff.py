#!/usr/bin/env python3
"""Reuse a successful exact-revision merge-group build on its push to main.

This optional cache never replaces validation. Only the latest current attempt of the
authoritative Lean workflow may supply an artifact; misses leave the normal build to run.
Reusable root build outputs are validated and swapped as a unit, preserving Lake's
shared hardlinked artifacts and avoiding partially restored module/trace bundles.
Lake's transient module setup inputs are omitted; compilation recreates them when needed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import tarfile
import tempfile
from urllib.parse import urlencode

from check_abstract_ci import (
    WORKFLOW_FILE, WORKFLOW_PATH, Rejected, gh_download_artifact, gh_get, positive, require,
)


ROOT = Path(__file__).resolve().parents[1]
INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
MAX_FILES = 100_000
MAX_BYTES = 4 * 1024 ** 3
MAX_ARCHIVE_BYTES = 1024 ** 3
MAX_METADATA_BYTES = 64 * 1024


def digest(path: Path) -> str:
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def directory(path: Path) -> None:
    require(stat.S_ISDIR(path.lstat().st_mode), f"Not a real directory: {path}")


def source_context(root: Path, env: dict, event: str) -> dict:
    disabled = str(env.get("DISABLE_BUILD_HANDOFF", "")).strip().lower()
    require(disabled in ("", "0", "false", "no"), "Build handoff is disabled by DISABLE_BUILD_HANDOFF")
    require(env.get("GITHUB_EVENT_NAME") == event, f"Expected {event} event")
    if event == "push":
        require(env.get("GITHUB_REF") == "refs/heads/main", "Not a push to main")
    repository, sha = env.get("GITHUB_REPOSITORY", ""), env.get("GITHUB_SHA", "")
    require(bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)),
            "Invalid repository")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", sha)), "Invalid source SHA")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    require(head == sha, "Checkout does not match event SHA")
    dirty = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=root, text=True,
    )
    require(not dirty.strip(), "Tracked sources are modified")
    platform = {key: env.get(key, "")
                for key in ("RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion")}
    require(all(isinstance(value, str) and value for value in platform.values()),
            "Runner platform is unknown")
    return {"version": 1, "repository": repository, "source_sha": sha,
            "inputs": {name: digest(root / name) for name in INPUTS}, "platform": platform}


def artifact_name(sha: str, run_id: int, attempt: int) -> str:
    return f"lean-build-{sha}-{run_id}-{attempt}"


def module_setup_input(path: Path) -> bool:
    """Recognize only Lake's module/IR compiler setup inputs, relative to the build directory.

    Lake 4.36's Module.setupFile/irSetupFile use these suffixes under ir/. They are
    written inside the compile actions, absent from checkArtifactsExist/getMTime and
    ModuleOutputArtifacts, and unnecessary for reusing a completed module build.
    Other JSON outputs and every artifact, hash and trace remain in the handoff.
    """
    return (len(path.parts) > 1 and path.parts[0] == "ir"
            and path.name.endswith((".setup.json", ".irsetup.json")))


def pack(root: Path, output: Path, env: dict) -> str:
    context = source_context(root, env, "merge_group")
    run_id, attempt = (int(env.get(key, "0")) for key in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"))
    require(positive(run_id) and positive(attempt), "Invalid producer run identity")
    require(not output.resolve().is_relative_to(root.resolve()),
            "Handoff output must be outside the checkout")
    require(not output.exists() and not output.is_symlink(), "Handoff output already exists")
    directory(root / ".lake")
    build = root / ".lake/build"
    directory(build)
    files = []
    omitted_files = omitted_bytes = 0
    for path in sorted(build.rglob("*")):
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            continue
        require(stat.S_ISREG(info.st_mode), f"Non-regular build output: {path}")
        # Validate the file type before omitting anything: setup-named links are
        # rejected by the same boundary checks as every other build entry.
        if module_setup_input(path.relative_to(build)):
            omitted_files += 1
            omitted_bytes += info.st_size
            continue
        files.append((path, info))
    total = sum(info.st_size for _, info in files)
    require(0 < len(files) <= MAX_FILES and 0 < total <= MAX_BYTES,
            f"Build output count or size is outside handoff limits: {len(files)} files / "
            f"{total} bytes (limits {MAX_FILES} files / {MAX_BYTES} bytes; omitted "
            f"{omitted_files} module setup inputs / {omitted_bytes} bytes)")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lean-handoff-pack-", dir=output.parent) as temp:
        stage = Path(temp)
        archive = stage / "build.tar.gz"
        with tarfile.open(archive, "w:gz", compresslevel=1) as bundle:
            for path, info in files:
                # Write every regular file's bytes, including hardlinks to Lake's artifact
                # cache. The archive must not contain links into another checkout/cache.
                member = tarfile.TarInfo(path.relative_to(root).as_posix())
                member.size = info.st_size
                member.mode = 0o755 if info.st_mode & 0o111 else 0o644
                member.mtime = int(info.st_mtime)
                with path.open("rb") as source:
                    bundle.addfile(member, source)
        compressed = archive.stat().st_size
        require(compressed <= MAX_ARCHIVE_BYTES,
                f"Handoff archive is too large: {compressed} bytes (limit {MAX_ARCHIVE_BYTES})")
        require(source_context(root, env, "merge_group") == context,
                "Sources changed while packing the build")
        metadata = {**context, "producer": {"event": "merge_group", "run_id": run_id,
                                            "run_attempt": attempt},
                    "archive": {"sha256": digest(archive), "files": len(files), "bytes": total,
                                "compressed_bytes": compressed}}
        (stage / "metadata.json").write_text(json.dumps(metadata, sort_keys=True) + "\n")
        stage.rename(output)
    name = artifact_name(context["source_sha"], run_id, attempt)
    if env.get("GITHUB_OUTPUT"):
        with Path(env["GITHUB_OUTPUT"]).open("a") as handle:
            handle.write(f"artifact-name={name}\n")
    print(f"Build handoff packed: {len(files)} files / {total} bytes, "
          f"{compressed} compressed bytes; omitted {omitted_files} module setup inputs / "
          f"{omitted_bytes} bytes ({name})")
    return name


def check_run(run: dict, context: dict, workflow_id: int) -> None:
    require(isinstance(run, dict), "Malformed workflow run")
    require(run.get("head_sha") == context["source_sha"] and run.get("event") == "merge_group",
            "Run is not the exact-source merge group")
    branch = run.get("head_branch", "")
    require(isinstance(branch, str) and branch.startswith("gh-readonly-queue/main/")
            and len(branch) > len("gh-readonly-queue/main/"), "Run is not from the main merge queue")
    require(run.get("workflow_id") == workflow_id and run.get("path") == WORKFLOW_PATH,
            "Wrong Lean workflow identity")
    repo, head = run.get("repository"), run.get("head_repository")
    require(isinstance(repo, dict) and isinstance(head, dict), "Missing run repositories")
    require(repo.get("full_name") == context["repository"]
            and head.get("full_name") == context["repository"]
            and positive(repo.get("id")) and repo.get("id") == head.get("id"),
            "Run came from another repository")
    require(all(positive(run.get(key)) for key in ("id", "run_number", "run_attempt")),
            "Malformed run identity")


def latest_success(api, context: dict, workflow_id: int) -> dict:
    repository = context["repository"]
    query = urlencode({"head_sha": context["source_sha"], "event": "merge_group", "per_page": 100})
    pages = api(f"repos/{repository}/actions/workflows/{workflow_id}/runs?{query}", paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed run listing")
    runs = []
    for page in pages:
        require(isinstance(page, dict) and isinstance(page.get("workflow_runs"), list),
                "Malformed run page")
        runs.extend(page["workflow_runs"])
    require(bool(runs) and all(page.get("total_count") == len(runs) for page in pages),
            "No complete exact-source merge-group listing")
    for run in runs:
        check_run(run, context, workflow_id)
    require(len({run["id"] for run in runs}) == len(runs)
            and len({run["run_number"] for run in runs}) == len(runs), "Ambiguous latest run")
    selected = max(runs, key=lambda run: run["run_number"])
    current = api(f"repos/{repository}/actions/runs/{selected['id']}")
    check_run(current, context, workflow_id)
    require(current["id"] == selected["id"] and current["run_number"] == selected["run_number"]
            and current["run_attempt"] >= selected["run_attempt"], "Run identity changed")
    require(current.get("status") == "completed" and current.get("conclusion") == "success",
            "Latest current merge-group attempt has not succeeded")
    return current


def find_artifact(api, context: dict, run: dict) -> dict:
    name = artifact_name(context["source_sha"], run["id"], run["run_attempt"])
    pages = api(f"repos/{context['repository']}/actions/runs/{run['id']}/artifacts?per_page=100",
                paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed artifact listing")
    artifacts = []
    for page in pages:
        require(isinstance(page, dict) and isinstance(page.get("artifacts"), list),
                "Malformed artifact page")
        artifacts.extend(page["artifacts"])
    require(all(page.get("total_count") == len(artifacts) for page in pages),
            "Incomplete artifact listing")
    require(all(isinstance(item, dict) for item in artifacts), "Malformed artifact record")
    matches = [item for item in artifacts if item.get("name") == name]
    require(len(matches) == 1, "Missing or ambiguous run-attempt artifact")
    artifact = matches[0]
    require(positive(artifact.get("id")) and artifact.get("expired") is False
            and positive(artifact.get("size_in_bytes"))
            and artifact["size_in_bytes"] <= MAX_ARCHIVE_BYTES + MAX_METADATA_BYTES,
            "Artifact expired or exceeds handoff limits")
    identity = artifact.get("workflow_run")
    require(isinstance(identity, dict) and identity.get("id") == run["id"]
            and identity.get("head_sha") == context["source_sha"]
            and identity.get("repository_id") == run["repository"]["id"]
            and identity.get("head_repository_id") == run["head_repository"]["id"],
            "Artifact run identity mismatch")
    return artifact


def unpack(download: Path, stage: Path, context: dict, run: dict) -> Path:
    require({path.name for path in download.iterdir()} == {"metadata.json", "build.tar.gz"},
            "Unexpected artifact contents")
    archive, manifest = download / "build.tar.gz", download / "metadata.json"
    for path, limit in ((archive, MAX_ARCHIVE_BYTES), (manifest, MAX_METADATA_BYTES)):
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and 0 < info.st_size <= limit,
                "Artifact file is not regular or exceeds handoff limits")
    metadata = json.loads(manifest.read_text())
    require(isinstance(metadata, dict)
            and all(metadata.get(key) == value for key, value in context.items()),
            "Artifact source, configuration or platform mismatch")
    require(metadata.get("producer") == {"event": "merge_group", "run_id": run["id"],
                                         "run_attempt": run["run_attempt"]},
            "Artifact producer attempt mismatch")
    inventory = metadata.get("archive")
    require(isinstance(inventory, dict) and positive(inventory.get("files"))
            and inventory["files"] <= MAX_FILES and positive(inventory.get("bytes"))
            and inventory["bytes"] <= MAX_BYTES
            and inventory.get("compressed_bytes") == archive.stat().st_size
            and inventory.get("sha256") == digest(archive), "Invalid archive inventory or digest")
    seen, size = set(), 0
    with tarfile.open(archive, "r:gz") as bundle:
        for member in bundle:
            parts = member.name.split("/")
            require(member.isfile() and not member.sparse and "\\" not in member.name
                    and parts[:2] == [".lake", "build"] and len(parts) > 2
                    and all(part not in ("", ".", "..") for part in parts)
                    and member.name not in seen, "Unsafe or duplicate archive member")
            seen.add(member.name)
            size += member.size
            require(0 <= member.size <= MAX_BYTES and len(seen) <= inventory["files"]
                    and size <= inventory["bytes"], "Archive exceeds its declared inventory")
            require(type(member.mtime) in (int, float) and 0 <= member.mtime <= 2 ** 32,
                    "Invalid archive timestamp")
            target = stage.joinpath(*parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            with bundle.extractfile(member) as source, target.open("xb") as output:
                shutil.copyfileobj(source, output)
            target.chmod(0o755 if member.mode & 0o111 else 0o644)
            os.utime(target, (member.mtime, member.mtime))
    require(len(seen) == inventory["files"] and size == inventory["bytes"],
            "Archive inventory mismatch")
    return stage / ".lake/build"


def install_build(root: Path, staged: Path, backup: Path) -> None:
    directory(root / ".lake")
    build = root / ".lake/build"
    if build.exists() or build.is_symlink():
        directory(build)
        build.rename(backup)
    try:
        staged.rename(build)
    except BaseException:
        if backup.exists():
            backup.rename(build)
        raise


def restore(root: Path, env: dict, *, api=gh_get, downloader=gh_download_artifact) -> None:
    context = source_context(root, env, "push")
    workflow = api(f"repos/{context['repository']}/actions/workflows/{WORKFLOW_FILE}")
    require(isinstance(workflow, dict) and workflow.get("path") == WORKFLOW_PATH
            and workflow.get("state") == "active" and positive(workflow.get("id")),
            "Authoritative Lean workflow is unavailable")
    run = latest_success(api, context, workflow["id"])
    artifact = find_artifact(api, context, run)
    directory(root / ".lake")
    stage = Path(tempfile.mkdtemp(prefix="handoff-", dir=root / ".lake"))
    backup, installed = stage / "previous", False
    try:
        download = stage / "download"
        download.mkdir()
        downloader(context["repository"], run["id"], artifact["name"], download)
        staged = unpack(download, stage / "unpacked", context, run)
        current = latest_success(api, context, workflow["id"])
        require((current["id"], current["run_attempt"]) == (run["id"], run["run_attempt"]),
                "Merge-group run changed during download")
        require(find_artifact(api, context, current)["id"] == artifact["id"],
                "Artifact changed during download")
        require(source_context(root, env, "push") == context, "Checkout changed during download")
        install_build(root, staged, backup)
        installed = True
        print(f"Build handoff restored from run {run['id']} attempt {run['run_attempt']}; "
              "normal build and checks still run")
    finally:
        # A failed rollback must leave the original build available for recovery. With the
        # build directory absent, the normal Lake invocation safely recompiles from sources.
        if backup.exists() and not installed:
            print(f"Build handoff retained original outputs at {backup}")
        else:
            shutil.rmtree(stage)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("pack").add_argument("--output", type=Path, required=True)
    commands.add_parser("restore")
    args = parser.parse_args()
    try:
        if args.command == "pack":
            pack(ROOT, args.output, os.environ)
        else:
            restore(ROOT, os.environ)
    except (Rejected, OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError,
            tarfile.TarError, EOFError) as error:
        print(f"Build handoff unavailable: {error}; continuing without this optional cache")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
