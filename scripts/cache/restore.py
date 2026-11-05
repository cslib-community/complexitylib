#!/usr/bin/env python3
"""Restore optional Complexitylib artifacts from the nearest cached ancestor and its mirrors.

Only revision discovery and .lake filtering live here. Lake remains responsible for artifact
downloads, content-hash validation and reuse; repeating its ordinary get retains completed files.
"""

import argparse
from datetime import date
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.parse import urlsplit

if __package__:
    from .get_mathlib import stop_attempt
else:
    from get_mathlib import stop_attempt

ROOT = Path(__file__).resolve().parents[2]
SCOPE = "cslib-community/complexitylib"
MAX_REVISIONS = 100
DISCOVERY_SECONDS = 30
MAX_MAPPING_BYTES = 64 * 1024 * 1024
MAX_REDIRECTS = 5


def endpoints(root, env):
    """An explicit URL (including empty) replaces the checked-in ordered read endpoints."""
    if "COMPLEXITYLIB_CACHE_URL" in env:
        values = [env["COMPLEXITYLIB_CACHE_URL"]] if env["COMPLEXITYLIB_CACHE_URL"] else []
    else:
        path = root / "scripts/cache/endpoints.json"
        if not path.exists() and root != ROOT:
            path = ROOT / "scripts/cache/endpoints.json"
        config = json.loads(path.read_text())
        if not isinstance(config, dict) or config.get("version") != 1:
            raise ValueError("cache endpoint configuration must have version 1")
        values = config.get("read")
        if not isinstance(values, list):
            raise ValueError("cache endpoint configuration must contain a read list")
    result = []
    for value in values:
        if not isinstance(value, str):
            raise ValueError("cache endpoints must be URLs")
        url = urlsplit(value)
        secure = url.scheme == "https" or (url.scheme == "http" and
                 url.hostname in ("127.0.0.1", "localhost", "::1"))
        if (not secure or not url.netloc or url.username is not None
                or url.password is not None or url.query or url.fragment):
            raise ValueError("cache endpoints require HTTPS (or loopback HTTP) without credentials or queries")
        value = value.rstrip("/")
        if value not in result:
            result.append(value)
    return result


def run_bounded(command, root, env, timeout, capture=False):
    """Bound our process group, including curl children created by Lake or Git."""
    if timeout <= 0:
        raise TimeoutError("cache restoration time budget exhausted")
    process = subprocess.Popen(command, cwd=root, env=env, start_new_session=(os.name == "posix"),
                               stdout=subprocess.PIPE if capture else None,
                               stderr=subprocess.PIPE if capture else None)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        return process.returncode, stdout or b"", stderr or b""
    except subprocess.TimeoutExpired:
        return None, b"", b""
    finally:
        # A finished parent does not establish that its descendants have finished. Reuse the
        # Mathlib helper's bounded shutdown; never overlap retries after uncertain cleanup.
        if not stop_attempt(process):
            raise RuntimeError("cache process group did not disappear; stopping restoration")


def curl_policy(url):
    """Return the endpoint protocol and its permitted redirect count."""
    protocol = urlsplit(url).scheme
    if protocol not in ("https", "http"):
        raise ValueError("unsupported cache endpoint protocol")
    return protocol, MAX_REDIRECTS if protocol == "https" else 0


def curl_redirect_args(url):
    """Restrict curl to the endpoint's secure transport; loopback HTTP never redirects."""
    protocol, redirects = curl_policy(url)
    return ["--proto", f"={protocol}", "--proto-redir", f"={protocol}",
            "--max-redirs", str(redirects)]


def prepare_lake_curl_home(directory, url):
    """Give Lake's curl subprocess an isolated HTTPS-only redirect policy."""
    protocol, redirects = curl_policy(url)
    directory.mkdir()
    config = (f'proto = "={protocol}"\n'
              f'proto-redir = "={protocol}"\n'
              f'max-redirs = {redirects}\n')
    # curl uses .curlrc on POSIX and _curlrc on Windows. CURL_HOME keeps both variants away from
    # user configuration while Lake retains control of its ordinary transfer arguments.
    for name in (".curlrc", "_curlrc"):
        (directory / name).write_text(config)
    return directory


def read_mapping(path):
    lines = path.read_text().splitlines()
    if not lines:
        raise ValueError("missing Lake revision mapping header")
    version = json.loads(lines[0])
    if not isinstance(version, str) or re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", version) is None:
        raise ValueError("invalid Lake revision mapping date")
    date.fromisoformat(version)
    entries = []
    for line in lines[1:]:
        if not line.strip():
            continue
        entry = json.loads(line)
        if (not isinstance(entry, list) or len(entry) < 2 or not isinstance(entry[0], str)
                or re.fullmatch(r"[0-9a-fA-F]{16}", entry[0]) is None):
            raise ValueError("invalid Lake revision mapping entry")
        entries.append((entry[0], line))
    return lines[0], entries


def current_inputs(root):
    """Only root build traces count; dependency outputs do not suppress root downloads."""
    hashes = set()
    for path in (root / ".lake/build").rglob("*.trace"):
        try:
            trace = json.loads(path.read_text())
            value = trace.get("depHash")
            if isinstance(value, str):
                hashes.add(value)
        except (OSError, ValueError, AttributeError):
            pass  # Incomplete/stale traces leave that module eligible for a download.
    return hashes


def restore(root, env, *, missing_only=False, timeout=180, request_timeout=5, artifact_timeout=120):
    urls = endpoints(root, env)
    if not urls:
        print("No Complexitylib cache endpoints enabled; skipping the Complexitylib cache.")
        return
    deadline = time.monotonic() + timeout
    status, output, _ = run_bounded(["git", "rev-parse", "--is-shallow-repository"], root, env,
                                    min(5, deadline - time.monotonic()), capture=True)
    if status != 0:
        raise ValueError("cannot inspect checkout history")
    if output.strip() == b"true":
        status, head, _ = run_bounded(["git", "rev-parse", "HEAD"], root, env,
                                      min(5, deadline - time.monotonic()), capture=True)
        if status != 0:
            raise ValueError("cannot identify shallow checkout revision")
        status, _, _ = run_bounded(["git", "fetch", "--quiet", "--no-tags", f"--depth={MAX_REVISIONS}",
                                    "origin", head.decode().strip()], root, env,
                                   min(15, deadline - time.monotonic()))
        if status != 0:
            print("warning: could not deepen the shallow clone; using available history", file=sys.stderr)
    status, output, _ = run_bounded(["git", "rev-list", "-n", str(MAX_REVISIONS), "HEAD"], root,
                                    env, min(5, deadline - time.monotonic()), capture=True)
    if status != 0:
        raise ValueError("cannot list checkout history")
    revisions = output.decode().splitlines()
    toolchain = "".join((root / "lean-toolchain").read_text().split()).replace("/", "--").replace(":", "---")
    discovery_deadline = min(deadline, time.monotonic() + DISCOVERY_SECONDS)
    unavailable = set()
    with tempfile.TemporaryDirectory(prefix="complexitylib-cache-") as work:
        mapping = Path(work) / "mapping.jsonl"
        selected = None
        examined = 0
        # Ancestors take precedence over mirror preference. A secondary mirror's HEAD is
        # preferable to an older primary revision, especially during an incremental cutover.
        for back, revision in enumerate(revisions):
            examined = back + 1
            for url in urls:
                if url in unavailable:
                    continue
                remaining = min(request_timeout, discovery_deadline - time.monotonic())
                if remaining <= 0:
                    break
                remote = f"{url}/r0/{SCOPE}/tc/{toolchain}/{revision}.jsonl"
                status, output, _ = run_bounded([
                    "curl", "--silent", "--show-error", "--location", "--fail",
                    *curl_redirect_args(remote),
                    "--connect-timeout", str(remaining), "--max-time", str(remaining),
                    "--max-filesize", str(MAX_MAPPING_BYTES), "--output", str(mapping),
                    "--write-out", "%{http_code}", remote,
                ], root, env, remaining + .5, capture=True)
                if output.strip() == b"404":
                    continue
                if status != 0:
                    unavailable.add(url)
                    print(f"warning: revision lookup failed at {url}; trying other mirrors", file=sys.stderr)
                    continue
                try:
                    header, entries = read_mapping(mapping)
                except (OSError, UnicodeError, ValueError) as error:
                    unavailable.add(url)
                    print(f"warning: invalid revision mapping from {url}: {error}", file=sys.stderr)
                    continue
                selected = revision, back, url, header, entries
                break
            if selected or len(unavailable) == len(urls) or time.monotonic() >= discovery_deadline:
                break
        if selected is None:
            print(f"No outputs uploaded for the last {examined} commits of HEAD; "
                  "lake build will compile them (lookup is time bounded).")
            return
        revision, back, origin, header, entries = selected
        current = current_inputs(root) if missing_only else set()
        missing = [line for input_hash, line in entries if input_hash not in current]
        summary = (f"{len(missing)} of them are not current in .lake." if missing_only
                   else "restoring the complete mapping.")
        print(f"Remote cache: {revision} ({back} commits back in git rev-list HEAD) has outputs for "
              f"{len(entries)} modules; {summary}", flush=True)
        if not missing:
            return
        mapping.write_text(header + "\n" + "\n".join(missing) + "\n")
        # Reuse exactly the selected mapping on every mirror. Lake keeps completed,
        # hash-validated artifacts and retries only absent ones; no mixed-revision mappings.
        mirrors = [origin] + [url for url in urls if url != origin and url not in unavailable]
        for index, url in enumerate(mirrors):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            allowance = min(artifact_timeout, remaining / (len(mirrors) - index))
            curl_home = prepare_lake_curl_home(Path(work) / f"curl-{index}", url)
            child_env = {**env, "CURL_HOME": str(curl_home),
                         "LAKE_CACHE_ARTIFACT_ENDPOINT": f"{url}/a0",
                         "LAKE_CACHE_REVISION_ENDPOINT": f"{url}/r0"}
            status, _, _ = run_bounded(["lake", "cache", "get", f"--repo={SCOPE}", str(mapping)],
                                       root, child_env, allowance)
            if status == 0:
                return
            print(f"warning: artifact download failed at {url}; trying remaining mirrors", file=sys.stderr)
        print("warning: some cache downloads failed; lake build will compile those modules", file=sys.stderr)


def positive_seconds(value):
    value = float(value)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError("timeout must be a positive finite number of seconds")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--missing-only", action="store_true", help="skip input hashes already in root .lake traces")
    parser.add_argument("--checkout", type=Path, default=None, help="checkout to restore")
    parser.add_argument("--timeout", type=positive_seconds, default=180, help="total time budget (seconds)")
    parser.add_argument("--request-timeout", type=positive_seconds, default=5, help="one revision request's time limit")
    parser.add_argument("--artifact-timeout", type=positive_seconds, default=120, help="one mirror's artifact time limit")
    args = parser.parse_args()
    root = (args.checkout or Path(os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT") or ROOT)).resolve()
    try:
        restore(root, os.environ, missing_only=args.missing_only, timeout=args.timeout,
                request_timeout=args.request_timeout, artifact_timeout=args.artifact_timeout)
    except (OSError, ValueError, RuntimeError, TimeoutError) as error:
        print(f"warning: cache restoration unavailable: {error}; lake build will compile missing outputs",
              file=sys.stderr)
    return 0  # Optional caches never replace the subsequent strict build.


if __name__ == "__main__":
    raise SystemExit(main())
