#!/usr/bin/env bash
# Check the manuals, then run the locally reproducible steps behind CI's required `ci-checks`
# aggregator (scripts/full_check.py) or, with --quick, the affected-client checks
# (scripts/quick_check.py); report each gate.
# REF (default origin/main) is the comparison base for checks of changed files and modules.
# --no-full-fallback (with --quick) reports a change quick mode cannot plan instead of running the
# full check.
# Usage: scripts/check.sh [--quick [--no-full-fallback]] [--base REF] (from the repository root
# or any worktree)
set -u
cd "$(dirname "$0")/.." || exit 1
usage() {
  echo "Usage: scripts/check.sh [--quick [--no-full-fallback]] [--base REF]" >&2
  exit 2
}
quick=0
no_fallback=()
base=origin/main
while (($#)); do
  case $1 in
    --quick) quick=1 ;;
    --no-full-fallback) no_fallback=(--no-full-fallback) ;;
    --base) (($# > 1)) || usage; shift; base=$1 ;;
    --base=*) base=${1#--base=} ;;
    *) usage ;;
  esac
  shift
done
((quick || ${#no_fallback[@]} == 0)) || usage
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
if ((!quick)); then
  run "Linux vm.max_map_count preflight" python3 -B scripts/check_vm_map_count.py
fi
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
  exec python3 scripts/quick_check.py --base "$base" ${no_fallback[@]+"${no_fallback[@]}"}
fi
exec python3 -B scripts/full_check.py --base "$base"
