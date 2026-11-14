#!/usr/bin/env python3
"""Select an exact, native-compatible cache entry for Guide-only dependencies."""

import hashlib
import json
import os
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
DEPENDENCIES = ("verso", "subverso", "MD4Lean", "illuminate")
PATHS = tuple(f".lake/packages/{name}/.lake/build" for name in DEPENDENCIES)
INPUTS = (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "guide/lakefile.toml", "guide/lake-manifest.json",
    ".github/actions/cache-guide-deps/action.yml",
    ".github/actions/cache-guide-deps/key.py",
)
MACHINE = ("RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion")


def cache_key(root, env):
    # An unknown image must miss rather than share native objects with a guessed ABI.
    missing = [name for name in MACHINE if not env.get(name)]
    if missing:
        raise ValueError("Missing runner identity: " + ", ".join(missing))
    identity = {name: env[name] for name in MACHINE}
    identity["generation"] = env.get("GUIDE_CACHE_GENERATION", "0")
    identity["inputs"] = {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in INPUTS
    }
    digest = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    return "guide-deps-v1-" + digest


def main():
    key = cache_key(ROOT, os.environ)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"key={key}\npaths<<GUIDE_CACHE_PATHS\n")
        output.write("\n".join(PATHS) + "\nGUIDE_CACHE_PATHS\n")
    print(f"Guide dependency cache: {key}")


if __name__ == "__main__":
    main()
