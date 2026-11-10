#!/usr/bin/env bash
# Usage: measure.sh <label> files...   (uses Probe2; records per-call tactic heartbeats and per-file CPU/wall time)
S=/usr/local/google/home/samschlesinger/.gemini/jetski/brain/390fc9e3-9ea4-4744-a6fc-6478ae22563b/scratch/front
WT=/usr/local/google/home/samschlesinger/code/complexitylib/.worktrees/wt-390f-front
label=$1; shift
mkdir -p $S/m/$label
cd "$WT"
for f in "$@"; do
  base=$(echo "$f" | tr '/' '_')
  python3 $S/inject.py "$f" "$S/m/$label/$base" $S/Probe2.lean.inc > /dev/null
  /usr/bin/time -f "%e %U %S" -o $S/m/$label/$base.time env FRONT_LOG=$S/m/$label/calls.jsonl LEAN_NUM_THREADS=16 \
    timeout 1800 lake env lean "$S/m/$label/$base" > "$S/m/$label/$base.out" 2>&1
  echo "$f rc=$? time=$(cat $S/m/$label/$base.time | tail -1) errors=$(grep -c ': error' $S/m/$label/$base.out)" >> $S/m/$label/files.txt
done
echo DONE >> $S/m/$label/files.txt
