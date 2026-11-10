#!/usr/bin/env bash
# Interleaved timing: rounds of (old build: all files) then (new build: all files), unmodified sources.
S=/usr/local/google/home/samschlesinger/.gemini/jetski/brain/390fc9e3-9ea4-4744-a6fc-6478ae22563b/scratch/front
WT=/usr/local/google/home/samschlesinger/code/complexitylib/.worktrees/wt-390f-front
OUT=$S/timing2.txt
cd "$WT"
FILES="CslibFrontierTests/PPTTactic.lean CslibFrontierTests/AutomationCloudPremises.lean CslibFrontierTests/PolyTimeTactic.lean"
for round in 1 2 3 4 5; do
  for variant in old new; do
    if [ $variant = old ]; then
      cp $S/t/old_PolyTime.lean CslibFrontier/Tactic/PolyTime.lean; cp $S/t/old_PPT.lean CslibFrontier/Tactic/PPT.lean
    else
      git checkout HEAD -- CslibFrontier/Tactic/PolyTime.lean CslibFrontier/Tactic/PPT.lean
    fi
    LEAN_NUM_THREADS=16 lake build CslibFrontier.Tactic.PPT > /dev/null 2>&1 || echo "BUILD FAIL $variant" >> $OUT
    for f in $FILES; do
      /usr/bin/time -f "%e %U %S" -o $S/t/one.time env LEAN_NUM_THREADS=16 lake env lean "$f" > $S/t/one.out 2>&1
      rc=$?
      echo "$round $variant $f rc=$rc $(tail -1 $S/t/one.time) errs=$(grep -c ': error' $S/t/one.out)" >> $OUT
    done
  done
done
git checkout HEAD -- CslibFrontier/Tactic/PolyTime.lean CslibFrontier/Tactic/PPT.lean
LEAN_NUM_THREADS=16 lake build CslibFrontier.Tactic.PPT > /dev/null 2>&1
echo DONE >> $OUT
