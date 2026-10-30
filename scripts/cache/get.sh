#!/usr/bin/env bash
# Download prebuilt build outputs, so that `lake build` only compiles what you changed.
#
# Usage: scripts/cache/get.sh            (from the repository root or any worktree)
#
# Fetches Mathlib's cache, then Complexitylib's outputs for the nearest ancestor of HEAD that
# `main` CI has uploaded (Lake looks back up to 100 commits). Missing outputs are not an error:
# `lake build` compiles whatever the cache did not provide. See scripts/cache/README.md.
set -u
script_dir="$(cd "$(dirname "$0")" && pwd)" || exit 1
if [ -n "${COMPLEXITYLIB_CACHE_CHECKOUT:-}" ]; then
  cd "$COMPLEXITYLIB_CACHE_CHECKOUT" || exit 1
else
  cd "$(dirname "$0")/../.." || exit 1
fi

url="${COMPLEXITYLIB_CACHE_URL-https://storage.googleapis.com/complexitylib-lake-cache}"

COMPLEXITYLIB_CACHE_CHECKOUT="$PWD" python3 "$script_dir/get_mathlib.py"
if [ -z "$url" ]; then
  echo "COMPLEXITYLIB_CACHE_URL is empty; skipping the Complexitylib cache." >&2
  exit 0
fi
if ! LAKE_CACHE_ARTIFACT_ENDPOINT="$url/a0" LAKE_CACHE_REVISION_ENDPOINT="$url/r0" \
    lake cache get --repo=cslib-community/complexitylib; then
  echo "note: no cached Complexitylib outputs found for this history; lake build will compile them" >&2
fi
