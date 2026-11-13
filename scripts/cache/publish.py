#!/usr/bin/env python3
"""Stage Lake outputs once, then publish the same immutable files to GCS or HTTPS."""

import argparse
import base64
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tarfile
import tempfile
import time
from urllib.parse import urlsplit

try:
    import resource
except ImportError:
    resource = None

ROOT = Path(__file__).resolve().parents[2]
SCOPE = "cslib-community/complexitylib"


def valid_password_token(password):
    """Check the canonical encoding of a generated 256-bit publisher token.

    A format check cannot establish entropy: operators must generate these tokens
    with a CSPRNG, never choose a password and pad it to the required length.
    """
    if not re.fullmatch(r"[A-Za-z0-9_-]{43}", password):
        return False
    decoded = base64.urlsafe_b64decode(password + "=")
    return len(decoded) == 32 and base64.urlsafe_b64encode(decoded).decode().rstrip("=") == password


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, check=True, **kwargs)


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def require_clean_revision(expected=None):
    """Return HEAD only when its tracked and potentially compiled source state is clean."""
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if expected is not None and revision != expected:
        raise ValueError("Refusing to stage outputs after the checkout revision changed")
    if subprocess.check_output(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=ROOT
    ):
        raise ValueError("Refusing to stage outputs from modified or untracked sources")
    ignored = subprocess.check_output([
        "git", "ls-files", "-z", "--others", "--ignored", "--exclude-standard", "--",
        "CslibFrontier", "CslibFrontierTests",
    ], cwd=ROOT)
    if any(ignored.split(b"\0")):
        raise ValueError("Refusing to stage outputs with ignored entries in compiled source trees")
    return revision


def archive_snapshot():
    """Count root build archives; sizes include hard-linked copies."""
    archives = list((ROOT / ".lake/build").rglob("*.ltar"))
    return {"count": len(archives), "bytes": sum(path.stat().st_size for path in archives)}


@contextmanager
def stage_phase(name, phases):
    """Report wall time and completed child CPU, preserving command failures."""
    started = time.monotonic()
    cpu_started = time.process_time()
    before = resource.getrusage(resource.RUSAGE_CHILDREN) if resource else None
    print(f"Cache staging: {name} started", flush=True)
    phase = {"name": name, "status": "failed"}
    try:
        yield
        phase["status"] = "success"
    finally:
        phase["wall_seconds"] = round(time.monotonic() - started, 6)
        phase["process_cpu_seconds"] = round(time.process_time() - cpu_started, 6)
        if before is not None:
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            phase["child_user_seconds"] = round(after.ru_utime - before.ru_utime, 6)
            phase["child_system_seconds"] = round(after.ru_stime - before.ru_stime, 6)
        phases.append(phase)
        print(f"Cache staging: {name} {phase['status']} after "
              f"{phase['wall_seconds']:.2f}s", flush=True)


def stage(destination, report=None):
    if report is not None and report.resolve().is_relative_to(destination.resolve()):
        raise ValueError("The staging report must be outside the publication directory")
    started = time.monotonic()
    revision = require_clean_revision()
    toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    if not re.fullmatch(r"[A-Za-z0-9_.+-]+", toolchain):
        raise ValueError("Unsupported toolchain scope")
    metrics = {"version": 1, "revision": revision, "toolchain": toolchain,
               "platform": platform.system(), "architecture": platform.machine(),
               "lean_num_threads": os.environ.get("LEAN_NUM_THREADS"), "phases": []}
    destination.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix=".stage-", dir=destination.resolve()) as temporary:
        work = Path(temporary)
        mapping = work / "mapping.jsonl"
        metrics["archives_before"] = archive_snapshot()
        print(f"Cache staging: {metrics['archives_before']['count']} root archives present "
              f"({metrics['archives_before']['bytes']} bytes)", flush=True)
        with stage_phase("mapping and archive build", metrics["phases"]):
            run(["lake", "build", "CslibFrontier", "CslibFrontierTests", "-o", str(mapping)])
        metrics["archives_after"] = archive_snapshot()
        metrics["mapping_entries"] = sum(line.startswith("[") for line in mapping.read_text().splitlines())
        print(f"Cache staging: {metrics['archives_after']['count']} root archives now present; "
              f"{metrics['mapping_entries']} mapping entries", flush=True)
        with stage_phase("archive staging", metrics["phases"]):
            run(["lake", "cache", "stage", str(mapping), str(work / "archives")])
        artifacts = destination / "a0" / SCOPE
        artifacts.mkdir(parents=True)
        # Lake also writes outputs.jsonl here; publish the build's original mapping below.
        archives = sorted((work / "archives").glob("*.ltar"))
        if not archives:
            raise ValueError("Lake staged no artifacts")
        for archive in archives:
            if not archive.is_file() or archive.is_symlink() or not re.fullmatch(r"[0-9a-f]{16}\.ltar", archive.name):
                raise ValueError(f"Unexpected Lake archive: {archive.name}")
            archive.replace(artifacts / (archive.stem + ".art"))
        target = destination / "r0" / SCOPE / "tc" / toolchain / (revision + ".jsonl")
        target.parent.mkdir(parents=True)
        mapping.replace(target)
    # A build can run arbitrary project code. Refuse the result if it changed the checkout or if
    # another process moved HEAD or edited/created a source while the build was in progress.
    require_clean_revision(revision)
    with stage_phase("inventory hashing", metrics["phases"]):
        files = {p.relative_to(destination).as_posix(): digest(p)
                 for p in sorted(destination.rglob("*")) if p.is_file()}
    (destination / "publication.json").write_text(json.dumps({
        "version": 1, "revision": revision, "toolchain": toolchain, "files": files,
    }, sort_keys=True) + "\n")
    metrics["wall_seconds"] = round(time.monotonic() - started, 6)
    metrics["staged_artifacts"] = len(files) - 1
    if report is not None:
        report.write_text(json.dumps(metrics, indent=2, sort_keys=True) + "\n")
    print("CACHE_STAGING_METRICS " + json.dumps(metrics, sort_keys=True), flush=True)
    print(f"Staged {len(files) - 1} artifacts for {revision}")


def validate(directory):
    """Reject damaged, incomplete or non-regular transfers before publishing any file."""
    if directory.is_symlink() or not directory.is_dir():
        raise ValueError("Publication must be a real directory")
    metadata = directory / "publication.json"
    if metadata.is_symlink() or metadata.stat().st_size > 16 * 1024 * 1024:
        raise ValueError("Invalid publication metadata")
    data = json.loads(metadata.read_text())
    if not isinstance(data, dict) or data.get("version") != 1 or not re.fullmatch(r"[0-9a-f]{40}", data.get("revision", "")):
        raise ValueError("Invalid publication revision/version")
    if not re.fullmatch(r"[A-Za-z0-9_.+-]+", data.get("toolchain", "")):
        raise ValueError("Invalid publication toolchain")
    mapping = f"r0/{SCOPE}/tc/{data['toolchain']}/{data['revision']}.jsonl"
    files = data.get("files")
    if not isinstance(files, dict) or mapping not in files or not 1 < len(files) <= 100000:
        raise ValueError("Missing mapping or invalid artifact inventory")
    for name, expected in files.items():
        if name != mapping and not re.fullmatch(r"a0/" + re.escape(SCOPE) + r"/[0-9a-f]{16}\.art", name):
            raise ValueError(f"Invalid publication path: {name}")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("Invalid publication digest")
    actual = set()
    for path in directory.rglob("*"):
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise ValueError(f"Non-regular publication entry: {path}")
        if path.is_file() and path != metadata:
            actual.add(path.relative_to(directory).as_posix())
    if actual != set(files):
        raise ValueError("Publication inventory differs from metadata")
    for name, expected in files.items():
        if digest(directory / name) != expected:
            raise ValueError(f"Publication digest mismatch: {name}")
    return data, directory / mapping


def gcs(bucket, directory):
    if not re.fullmatch(r"[a-z0-9][a-z0-9._-]{1,221}[a-z0-9]", bucket):
        raise ValueError("Invalid GCS bucket name")
    data, mapping = validate(directory)
    artifacts = sorted(str(directory / name) for name in data["files"] if name.startswith("a0/"))
    run(["gcloud", "storage", "cp", "--no-clobber", "--quiet",
         "--content-type=application/vnd.reservoir.artifact", "-I", f"gs://{bucket}/a0/{SCOPE}/"],
        input="\n".join(artifacts) + "\n", text=True)
    # A failed artifact transfer must never publish a mapping to missing outputs.
    run(["gcloud", "storage", "cp", "--no-clobber", "--quiet",
         "--content-type=application/vnd.reservoir.outputs+json-lines", str(mapping),
         f"gs://{bucket}/{mapping.relative_to(directory).as_posix()}"])
    print(f"Published {data['revision']} to gs://{bucket}")


def http(endpoint, directory):
    parsed = urlsplit(endpoint)
    if (parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password
            or parsed.path not in ("", "/") or parsed.query or parsed.fragment):
        raise ValueError("Upload endpoint must be an HTTPS origin without credentials or a path")
    data, _ = validate(directory)
    user = os.environ.get("CACHE_SERVER_USER", "")
    password = os.environ.get("CACHE_SERVER_PASSWORD", "")
    if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", user) or not valid_password_token(password):
        raise ValueError("Set CACHE_SERVER_USER and a generated 32-byte base64url CACHE_SERVER_PASSWORD")
    # Keep the password out of argv, URLs and error messages. curl reads its quoted
    # configuration from stdin; escape the only special characters allowed here.
    credential = (user + ":" + password).replace("\\", "\\\\").replace('"', '\\"')
    config = f'user = "{credential}"\n'
    with tempfile.TemporaryDirectory(prefix="cache-upload-") as temporary:
        package = Path(temporary) / "publication.tar"
        with tarfile.open(package, "w", format=tarfile.USTAR_FORMAT) as archive:
            for name in ["publication.json", *sorted(data["files"])]:
                archive.add(directory / name, arcname=name, recursive=False)
        result = run(["curl", "--disable", "--config", "-", "--silent", "--show-error",
             "--fail-with-body", "--proto", "=https", "--connect-timeout", "30",
             "--max-time", "360", "--retry", "5", "--retry-max-time", "600",
             "--output", str(Path(temporary) / "response"), "--write-out", "%{http_code}",
             "--retry-connrefused", "--header", "Content-Type: application/x-tar",
             "--upload-file", str(package),
             endpoint.rstrip("/") + "/publish/" + data["revision"]],
             input=config, text=True, stdout=subprocess.PIPE)
        if result.stdout.strip() != "201":
            raise ValueError("Cache origin did not acknowledge publication with HTTP 201")
    print(f"Published {data['revision']} to {endpoint}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    staging = commands.add_parser("stage")
    staging.add_argument("directory", type=Path)
    staging.add_argument("--report", type=Path,
                         help="write timing/archive metrics outside the published directory")
    checking = commands.add_parser("verify")
    checking.add_argument("directory", type=Path)
    checking.add_argument("--revision", help="Require this exact producer revision")
    google = commands.add_parser("gcs")
    google.add_argument("bucket")
    google.add_argument("directory", type=Path)
    server = commands.add_parser("http")
    server.add_argument("endpoint")
    server.add_argument("directory", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "stage":
            stage(args.directory, args.report)
        elif args.command == "verify":
            data, _ = validate(args.directory)
            if args.revision is not None and data["revision"] != args.revision:
                raise ValueError("Publication is from a different revision")
        elif args.command == "http":
            http(args.endpoint, args.directory)
        else:
            gcs(args.bucket, args.directory)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Cache publication failed: {error}\n")


if __name__ == "__main__":
    main()
