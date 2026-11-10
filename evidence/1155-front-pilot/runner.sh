#!/usr/bin/env bash
# Run the front-end probe over a list of Lean files (relative to the worktree), sequentially.
S=/usr/local/google/home/samschlesinger/.gemini/jetski/brain/390fc9e3-9ea4-4744-a6fc-6478ae22563b/scratch/front
WT=/usr/local/google/home/samschlesinger/code/complexitylib/.worktrees/wt-390f-front
LOG=${LOG:-$S/log.jsonl}
cd "$WT"
for f in "$@"; do
  mod=${f%.lean}; mod=${mod//\//.}
  echo "=== $f" >> $S/runner.out
  LEAN_NUM_THREADS=16 lake build "$mod" >> $S/runner.out 2>&1 || echo "BUILD FAIL $f" >> $S/runner.out
  base=$(echo "$f" | tr '/' '_')
  python3 $S/inject.py "$f" "$S/run/$base" $S/Probe.lean.inc >> $S/runner.out
  start=$(date +%s)
  FRONT_LOG=$LOG LEAN_NUM_THREADS=16 timeout 1800 lake env lean "$S/run/$base" > "$S/run/$base.out" 2>&1
  rc=$?
  echo "rc=$rc secs=$(( $(date +%s) - start )) errors=$(grep -c 'error' "$S/run/$base.out")" >> $S/runner.out
done
echo DONE >> $S/runner.out
