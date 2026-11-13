#!/usr/bin/env python3
"""Try ordered native Lake cache endpoints with a deadline per origin."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
from urllib.parse import urlsplit

from bounded import UnsafeShutdown, interruptible, run, seconds

DEFAULT_URLS = (
    "https://storage.googleapis.com/complexitylib-lake-cache",
    "https://complexitycache.csail.mit.edu",
)
SCOPE = "cslib-community/complexitylib"
ROOT = Path(__file__).resolve().parents[2]


def origins(env):
    # The old single-URL override remains authoritative, including empty=disable.
    if "COMPLEXITYLIB_CACHE_URL" in env:
        values = [env["COMPLEXITYLIB_CACHE_URL"]] if env["COMPLEXITYLIB_CACHE_URL"] else []
    else:
        values = env.get("COMPLEXITYLIB_CACHE_URLS", "").split() or list(DEFAULT_URLS)
    if len(values) > 8:
        raise ValueError("At most eight cache origins may be configured")
    for value in values:
        parsed = urlsplit(value)
        if (parsed.scheme not in ("https", "http") or not parsed.hostname or parsed.username
                or parsed.password or parsed.query or parsed.fragment or any(c.isspace() for c in value)):
            raise ValueError("Cache endpoints must be HTTP(S) URLs without credentials/query/fragment")
    return list(dict.fromkeys(value.rstrip("/") for value in values))


def disabled(env):
    return env.get("DISABLE_CACHE_RESTORE", "").lower() in ("1", "true")


def one_origin(root, origin, work, missing):
    """This worker and all curl/Lake children share the parent's supervised group."""
    env = {**os.environ, "LAKE_CACHE_ARTIFACT_ENDPOINT": origin + "/a0",
           "LAKE_CACHE_REVISION_ENDPOINT": origin + "/r0"}
    args = ["lake", "cache", "get", "--repo=" + SCOPE]
    if missing:
        toolchain = (root / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        revisions = subprocess.check_output(["git", "rev-list", "-n", "100", "HEAD"],
                                             cwd=root, text=True).splitlines()
        mapping = work / "map.jsonl"
        for back, revision in enumerate(revisions):
            result = subprocess.run([
                "curl", "--disable", "--fail", "--silent",
                "--connect-timeout", "5", "--max-time", "20", "--retry", "2",
                "--retry-max-time", "20", "--max-filesize", str(8 * 1024 * 1024),
                "--output", str(mapping), "--write-out", "%{http_code}",
                f"{origin}/r0/{SCOPE}/tc/{toolchain}/{revision}.jsonl"], cwd=root,
                stdout=subprocess.PIPE, text=True)
            if result.returncode == 0:
                break
        else:
            detail = (f"last lookup HTTP {result.stdout.strip() or 'unknown'}, "
                      f"curl exit {result.returncode}") if revisions else "no revisions to check"
            print(f"No usable cached mapping among {len(revisions)} revisions at {origin} "
                  f"({detail})", flush=True)
            return 1
        current = set()
        for trace in (root / ".lake/build").rglob("*.trace"):
            try:
                current.update(re.findall(r'"depHash": *"([0-9a-f]+)"', trace.read_text()))
            except (OSError, UnicodeError):
                pass
        lines = mapping.read_text().splitlines(keepends=True)
        def already_current(line):
            try:
                row = json.loads(line)
            except ValueError:
                return False
            # Preserve unknown/malformed rows for Lake's parser, even if they
            # start with an input fingerprint already present in a local trace.
            return (isinstance(row, list) and len(row) == 2 and isinstance(row[0], str)
                    and row[0] in current and isinstance(row[1], str)
                    and re.fullmatch(r"[0-9a-f]{16}\.ltar", row[1]) is not None)

        needed = [line for line in lines if not already_current(line)]
        # Match the existing optimization: retain the original version/header and JSON rows;
        # native Lake still parses/verifies the mapping and output archives.
        mapping = work / "missing.jsonl"
        mapping.write_text("".join(needed))
        count = sum(line.startswith('["') for line in needed)
        total = sum(line.startswith('["') for line in lines)
        print(f"Remote cache: {revision} ({back} commits back in git rev-list HEAD) has outputs for "
              f"{total} modules; "
              f"{count} of them are not current in .lake.", flush=True)
        # Even an empty filtered mapping must pass Lake's version/syntax parser;
        # a 200 HTML error page must not suppress the next mirror.
        args.append(str(mapping))
    return subprocess.run(args, cwd=root, env=env).returncode


def restore(root, env, missing=False):
    if disabled(env):
        print("DISABLE_CACHE_RESTORE is set; skipping optional cache restoration.", flush=True)
        return False
    urls = origins(env)
    timeout = seconds(env, "COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT", 180)
    if not urls:
        print("COMPLEXITYLIB_CACHE_URL is empty; skipping the cslib-frontier cache.", flush=True)
        return False
    if missing:
        shallow = run(["git", "rev-parse", "--is-shallow-repository"], timeout=10,
                      cwd=root, env=env, capture_output=True)
        if shallow.returncode == 0 and shallow.stdout.strip() == "true":
            head = run(["git", "rev-parse", "HEAD"], timeout=10, cwd=root, env=env, capture_output=True)
            if head.returncode == 0:
                deepened = run(["git", "fetch", "--quiet", "--no-tags", "--depth=100", "origin",
                                head.stdout.strip()], timeout=30, cwd=root, env=env)
                if deepened.returncode:
                    print("warning: could not deepen clone; using available history", file=sys.stderr)
    for index, origin in enumerate(urls, 1):
        print(f"cslib-frontier cache origin {index}/{len(urls)}: {origin}", flush=True)
        started = time.monotonic()
        with tempfile.TemporaryDirectory(prefix="cslib-frontier-cache-") as temporary:
            args = [sys.executable, "-B", str(Path(__file__).resolve()), "--one", origin,
                    "--work", temporary, "--checkout", str(root)]
            if missing:
                args.append("--missing")
            result = run(args, timeout=timeout, cwd=root, env=env)
        outcome = ("completed" if result.returncode == 0 else "timed out"
                   if result.returncode == 124 else f"failed (exit {result.returncode})")
        print(f"cslib-frontier cache origin {index}/{len(urls)}: {outcome} in "
              f"{time.monotonic() - started:.1f}s: {origin}", flush=True)
        if result.returncode == 0:
            return True
        print("note: origin missed, failed or timed out; trying the next configured origin", flush=True)
    print("note: no configured origin completed restoration; lake build will compile missing outputs",
          file=sys.stderr, flush=True)
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--missing", action="store_true")
    parser.add_argument("--checkout", type=Path,
                        default=Path(os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT") or ROOT))
    parser.add_argument("--one", help=argparse.SUPPRESS)
    parser.add_argument("--work", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.one is not None:
        return one_origin(args.checkout, args.one, args.work, args.missing)
    try:
        with interruptible():
            restore(args.checkout, os.environ, args.missing)
    except UnsafeShutdown as error:
        print(f"error: {error}", file=sys.stderr)
        return 125
    except KeyboardInterrupt:
        return 124
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"note: cache restoration unavailable; building from source: {error}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
