#!/usr/bin/env bash
# Build the guide (guide/, written with Verso) and write its pages to
# guide/.lake/build/site/html-multi.
#
# Usage: scripts/guide.sh            (from the repository root or any worktree)
#
# Building elaborates every chapter, which checks its Lean examples against the library; the
# generator then writes the pages. In a fresh checkout, run scripts/cache/get.sh first so that the
# library modules the guide imports are downloaded rather than compiled. The first build also
# compiles Verso, which takes a few minutes. The generator then runs in Lean
# without compiling the imported library to native code. Preview the result with
#   python3 -m http.server --bind 127.0.0.1 --directory guide/.lake/build/site/html-multi
set -euo pipefail
cd "$(dirname "$0")/.."

# The guide shares .lake/packages with the library: a stale lockfile would check out other
# revisions there.
python3 scripts/check_docs.py --config-only
# Warnings in the chapters are errors (guide/lakefile.toml); this hides the Verso package's own.
lake -q -d guide build --log-level=error CslibFrontierGuide
out=guide/.lake/build/site
rm -rf "$out"
# `lake lean` builds the generator's imports and applies its Lake options and plugin setup.
# Lean's --run takes a filename as well as the one Lake uses to prepare that setup.
main=guide/CslibFrontierGuideMain.lean
lake -q --log-level=error -d guide lean "$main" -- --run "$main" --output "$out"
echo "Guide written to $out/html-multi"
