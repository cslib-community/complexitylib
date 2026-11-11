#!/usr/bin/env bash
# Check the manuals, then run the required steps of CI's `ci-checks` job (scripts/full_check.py)
# or, with --quick, the affected-client checks (scripts/quick_check.py); report each gate.
# REF (default origin/main) is the comparison base for checks of changed files and modules.
# Usage: scripts/check.sh [--quick] [--base REF] (from the repository root or any worktree)
set -u
cd "$(dirname "$0")/.." || exit 1
usage() {
  echo "Usage: scripts/check.sh [--quick] [--base REF]" >&2
  exit 2
}
quick=0
base=origin/main
while (($#)); do
  case $1 in
    --quick) quick=1 ;;
    --base) (($# > 1)) || usage; shift; base=$1 ;;
    --base=*) base=${1#--base=} ;;
    *) usage ;;
  esac
  shift
done
log_dir=$(mktemp -d "${TMPDIR:-/tmp}/cslib-frontier-check.XXXXXX") || exit 1
status=0
gate=0
run() {
  local name=$1
  shift
  gate=$((gate + 1))
  local log="$log_dir/$gate.log"
  if "$@" >"$log" 2>&1; then
    printf 'ok    %s\n' "$name"
  else
    printf 'FAIL  %s\n' "$name"
    cat "$log"
    status=1
  fi
}
finish() {
  if ((status)); then
    printf 'Full logs: %s\n' "$log_dir"
  else
    rm "$log_dir"/*.log
    rmdir "$log_dir"
  fi
}
# Run on both the full and quick routes. Lean-only edits can invalidate a manual excerpt,
# and these stdlib checks can report drift before a cold checkout restores any build cache.
run "operator manual links and excerpts" python3 -B scripts/check_operator_manual.py
run "operator manual tooling tests" python3 -B scripts/test_operator_manual.py
if ((status)); then
  finish
  exit "$status"
fi
# A quick check may restart this script for the full check. Restore only once in that process
# chain, even if planning takes longer than the bootstrap's ordinary retry window.
if [ "${COMPLEXITYLIB_CACHE_CHECK_STARTED-}" != "1" ]; then
  scripts/cache/ensure.sh || { cache_status=$?; finish; exit "$cache_status"; }
  export COMPLEXITYLIB_CACHE_CHECK_STARTED=1
fi
finish
if ((quick)); then
  exec python3 scripts/quick_check.py --base "$base"
fi
exec python3 -B scripts/full_check.py --base "$base"
