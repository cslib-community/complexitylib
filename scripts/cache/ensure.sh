#!/usr/bin/env bash
# Attempt cache restoration before a build or MCP session, reusing a completed attempt for
# the same checkout state for ten minutes. The stamp is not a cache hit; --refresh retries now.
set -u
SCRIPT_ROOT="$(cd "$(dirname "$0")/../.." && pwd)" || exit 1
export COMPLEXITYLIB_CACHE_SCRIPT_ROOT="$SCRIPT_ROOT"
exec python3 -B - "$@" <<'PY'
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

parser = argparse.ArgumentParser(description="Restore optional build caches before using Lean.")
parser.add_argument("--refresh", action="store_true", help="retry even after a recent attempt")
parser.add_argument(
    "--checkout",
    type=Path,
    default=None,
    help="target checkout directory (defaults to COMPLEXITYLIB_CACHE_CHECKOUT or this script's repo)",
)
args = parser.parse_args()
if (os.environ.get("COMPLEXITYLIB_CACHE_AUTO") == "0"
        or os.environ.get("DISABLE_CACHE_RESTORE", "").lower() in ("true", "1")):
    raise SystemExit(0)

script_root = Path(os.environ["COMPLEXITYLIB_CACHE_SCRIPT_ROOT"]).resolve()
sys.path.insert(0, str(script_root / "scripts/cache"))
from bounded import UnsafeShutdown, interruptible, run, seconds
from restore import origins

try:
    cache_origins = origins(os.environ)
    origin_timeout = seconds(os.environ, "COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT", 180)
    bootstrap_timeout = seconds(os.environ, "COMPLEXITYLIB_CACHE_BOOTSTRAP_TIMEOUT",
                                630 + len(cache_origins) * (origin_timeout + 10), 7200)
except ValueError as error:
    print(f"note: invalid optional cache configuration; building from source: {error}", file=sys.stderr)
    raise SystemExit(0)
checkout_env = os.environ.get("COMPLEXITYLIB_CACHE_CHECKOUT")
if args.checkout is not None:
    root = args.checkout.resolve()
elif checkout_env:
    root = Path(checkout_env).resolve()
else:
    root = script_root

try:
    os.chdir(root)
except OSError as error:
    print(f"note: cannot access target checkout for cache bootstrap: {error}", file=sys.stderr)
    raise SystemExit(0)

stamp = root / ".lake/cache-bootstrap/attempt.json"
try:
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    files = {}
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"):
        path = root / name
        files[name] = hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None
    state = {"checkout": str(root), "head": head, "files": files,
             "endpoints": cache_origins,
             "origin_timeout": origin_timeout, "bootstrap_timeout": bootstrap_timeout,
             "recovery_generation": os.environ.get("CACHE_RECOVERY_GENERATION", "0"),
             "cache_dir": os.environ.get("LAKE_CACHE_DIR")}
    fingerprint = hashlib.sha256(json.dumps(state, sort_keys=True).encode()).hexdigest()
except (OSError, subprocess.CalledProcessError) as error:
    print(f"note: cannot identify cache bootstrap state; continuing without restoration: {error}",
          file=sys.stderr)
    raise SystemExit(0)

try:
    previous = json.loads(stamp.read_text())
    age = time.time() - previous["attempted_at"]
    if not args.refresh and previous["fingerprint"] == fingerprint and 0 <= age < 600:
        print(f"Cache bootstrap: skipping repeated attempt ({age:.0f}s old, previous fetch "
              f"exit {previous.get('fetch_exit_code', 'unknown')}); use --refresh to retry. "
              "The attempt record does not certify a cache hit.", flush=True)
        raise SystemExit(0)
except (OSError, ValueError, KeyError, TypeError):
    pass

# get.sh deliberately succeeds after optional cache misses/errors. Finishing it means only
# that restoration was attempted; retry after ten minutes, a state change, or --refresh.
get_script = root / "scripts/cache/get.sh"
if not get_script.exists():
    get_script = script_root / "scripts/cache/get.sh"
child_env = {**os.environ, "COMPLEXITYLIB_CACHE_CHECKOUT": str(root)}
started = time.monotonic()
print(f"Cache bootstrap: attempting optional downloads (budget {bootstrap_timeout:g}s).",
      flush=True)
try:
    # Nested download supervisors handle SIGTERM by draining their own groups.
    # Give them longer than their ten-second shutdown bound before a forced kill.
    with interruptible():
        result = run([str(get_script)], timeout=bootstrap_timeout, cwd=root, env=child_env, grace=15)
except UnsafeShutdown as error:
    print(f"error: {error}", file=sys.stderr)
    raise SystemExit(125)
except KeyboardInterrupt:
    raise SystemExit(124)
except OSError as error:
    print(f"note: cache bootstrap unavailable; continuing without restoration: {error}",
          file=sys.stderr)
    raise SystemExit(0)
if result.returncode == 125:
    raise SystemExit(125)
if result.returncode:
    print("note: cache bootstrap did not complete; continuing with the build",
          file=sys.stderr)
print(f"Cache bootstrap: attempt finished in {time.monotonic() - started:.1f}s "
      f"(fetch exit {result.returncode}). Completion does not certify a cache hit.", flush=True)

temporary = None
try:
    stamp.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=stamp.parent, delete=False) as output:
        temporary = Path(output.name)
        json.dump({"fingerprint": fingerprint, "attempted_at": time.time(),
                   "fetch_exit_code": result.returncode}, output)
        output.write("\n")
    temporary.replace(stamp)
except OSError as error:
    print(f"note: cache attempt could not be recorded: {error}", file=sys.stderr)
finally:
    if temporary is not None:
        temporary.unlink(missing_ok=True)
PY
