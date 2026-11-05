#!/usr/bin/env bash
# Attempt cache restoration before a build or MCP session, reusing a completed attempt for
# the same checkout state for ten minutes. The stamp is not a cache hit; --refresh retries now.
set -u
SCRIPT_ROOT="$(cd "$(dirname "$0")/../.." && pwd)" || exit 1
export COMPLEXITYLIB_CACHE_SCRIPT_ROOT="$SCRIPT_ROOT"
exec python3 - "$@" <<'PY'
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
if os.environ.get("COMPLEXITYLIB_CACHE_AUTO") == "0":
    raise SystemExit(0)

script_root = Path(os.environ["COMPLEXITYLIB_CACHE_SCRIPT_ROOT"]).resolve()
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
             "endpoint": os.environ.get("COMPLEXITYLIB_CACHE_URL",
                                        "https://storage.googleapis.com/complexitylib-lake-cache"),
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
        raise SystemExit(0)
except (OSError, ValueError, KeyError, TypeError):
    pass

# get.sh deliberately succeeds after optional cache misses/errors. Finishing it means only
# that restoration was attempted; retry after ten minutes, a state change, or --refresh.
get_script = root / "scripts/cache/get.sh"
if not get_script.exists():
    get_script = script_root / "scripts/cache/get.sh"
child_env = {**os.environ, "COMPLEXITYLIB_CACHE_CHECKOUT": str(root)}
try:
    result = subprocess.run([str(get_script)], cwd=root, env=child_env)
except OSError as error:
    print(f"note: cache bootstrap unavailable; continuing without restoration: {error}",
          file=sys.stderr)
    raise SystemExit(0)
if result.returncode:
    print("note: cache bootstrap did not complete; continuing with the build",
          file=sys.stderr)

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
