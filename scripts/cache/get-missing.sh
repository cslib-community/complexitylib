#!/usr/bin/env bash
# Download from the remote cache only the build outputs that `.lake` does not already have, so
# that `lake build` compiles only what changed. CI runs this after restoring `.lake` from the
# GitHub Actions cache; `scripts/cache/get.sh` is the local equivalent.
#
# Usage: scripts/cache/get-missing.sh
#
# Like `lake cache get`, this looks for the nearest of the first 100 commits of
# `git rev-list HEAD` that `main` CI has uploaded (deepening a shallow clone first). It then
# drops the entries of that commit's mapping whose input hash already matches a trace in
# `.lake/build`: Lake replays those modules from `.lake`, and a fresh CI runner would otherwise
# download a complete set (about 200 MB) on every run. Lake uses a downloaded output only where a
# module's input hash matches it. Failures are not errors: `lake build` compiles whatever is
# missing. See scripts/cache/README.md.
set -u
cd "$(dirname "$0")/../.." || exit 1

url="${COMPLEXITYLIB_CACHE_URL-https://storage.googleapis.com/complexitylib-lake-cache}"
scope="cslib-community/complexitylib"
max_revs=100
if [ -z "$url" ]; then
  echo "COMPLEXITYLIB_CACHE_URL is empty; skipping the Complexitylib cache."
  exit 0
fi
# `leanprover/lean4:v4.36.0` → `leanprover--lean4---v4.36.0`, as in scripts/cache/upload.sh.
toolchain="$(tr -d '[:space:]' < lean-toolchain | sed 's#/#--#; s#:#---#')"
work="$(mktemp -d "${TMPDIR:-/tmp}/complexitylib-cache.XXXXXX")" || exit 0
trap 'rm -rf "$work"' EXIT

if [ "$(git rev-parse --is-shallow-repository)" = true ]; then
  git fetch --quiet --no-tags --depth="$max_revs" origin "$(git rev-parse HEAD)" ||
    echo "warning: could not deepen the shallow clone; looking up only the commits it has"
fi

rev=""
back=0
for r in $(git rev-list -n "$max_revs" HEAD); do
  if curl -sf --retry 3 -o "$work/map.jsonl" "$url/r0/$scope/tc/$toolchain/$r.jsonl"; then
    rev="$r"
    break
  fi
  back=$((back + 1))
done
if [ -z "$rev" ]; then
  echo "No outputs uploaded for the last $back commits of HEAD; lake build will compile them."
  exit 0
fi

# Mapping lines are `["<input hash>",<outputs>]` after a version header; Lake's traces record
# the input hash of the outputs in `.lake/build` as `"depHash"`.
find .lake/build -name '*.trace' -exec grep -ho '"depHash": *"[0-9a-f]*"' {} + 2>/dev/null |
  sed 's/.*"\([0-9a-f]*\)"$/["\1",/' > "$work/current"
grep -vF -f "$work/current" "$work/map.jsonl" > "$work/missing.jsonl"
total="$(grep -c '^\["' "$work/map.jsonl")"
missing="$(grep -c '^\["' "$work/missing.jsonl")"
echo "Remote cache: $rev ($back commits back in git rev-list HEAD) has outputs for" \
  "$total modules; $missing of them are not current in .lake."
if [ "$missing" -le 0 ]; then
  exit 0
fi
if ! LAKE_CACHE_ARTIFACT_ENDPOINT="$url/a0" \
    lake cache get --repo="$scope" "$work/missing.jsonl"; then
  echo "warning: some downloads failed; lake build will compile those modules"
fi
