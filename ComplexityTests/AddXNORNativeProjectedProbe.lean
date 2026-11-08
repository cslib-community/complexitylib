/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeProjectedProbe
import all Complexity.Cryptanalysis.AddXNORNativeQuerySelection
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import Mathlib.Tactic.IntervalCases

/-! # Complete raw-input projected-query/construction/witness client -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]

private def input : Data 32 :=
  { regs := fun _ => 99
    mem := fun a => if a = 5 then 1 else if a = 6 then 2 else if a = 7 then 4
      else if a = 8 then 1 else if a = 10 then 1 else if a = 12 then 1
      else if a < 64 then 17 else 0 }

/-- The inverse low-width addition query is three, whereas the forward query is
one. Full first-quarter states three and seven collide in the retained bucket. -/
example :
    (backward ((decode 1 0).zip (middle.map (BitVec.setWidth 2))) 0#2).toNat = 3 ∧
    (eval ((decode 1 0).zip (middle.map (BitVec.setWidth 2))) 0#2).toNat = 1 ∧
    Forward.records first 1#3 2 3 = [(7, 4), (3, 2)] := by
  unfold Forward.records bucketIndices indexedState
  decide +kernel

/-- Every raw premise of the arbitrary-width endpoint is supplied. There is no
projected-array, correct-key, dictionary, execution or witness premise. -/
example : ∃ y, ExecWithin 12
      (projectedProbe 5 3 8 1 10 1 12 1 16 17 4 8 0 1 2 0 0 20 24 52 56 64) input y
      (((10 * 1 + 8) + ((10 * 1 + 8) + ((18 * 1 + 28) + ((11 * 1 + 14) + 5)))) +
        (7 + (4 * 4 + 8 * (11 * 3 + 22) + 10 + (9 + (2 * (11 * 1 + 30) + 2)) +
          (7 + (4 * 4 + 2 * (18 * 1 + 37) + 10)) +
          (10 + ((Backward.bucketIndices middle 2#3 4 1 2).length * (18 * 1 + 39) + 2))))) ∧
    (y.regs operand ≠ 0 →
      eval (((decode 3 (y.regs operand - 1)).zip first) ++
        ((decode 1 (y.regs bits)).zip middle) ++
        ((decode 1 (y.regs operators)).zip middle) ++
        ((decode 1 (y.regs firstOperators)).zip middle)) 1#3 = 2#3) := by
  obtain ⟨y, he, hw⟩ := projectedProbe_exec
    (W := 12) (b := 5) (c := 8) (b₃ := 10) (b₄ := 12) (q₂ := 16) (q₃ := 17)
    (h := 20) (f := 24) (h₄ := 52) (f₄ := 56) (D := 64) (v₂ := 0) (v₃ := 0)
    first middle middle middle 1#3 2#3 0#2 input
    (by intro i hi; simp only [first, List.length_cons, List.length_nil] at hi
        interval_cases i <;> decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a ha; simp [input, show ¬a = 5 by omega, show ¬a = 6 by omega,
      show ¬a = 7 by omega, show ¬a = 8 by omega, show ¬a = 10 by omega,
      show ¬a = 12 by omega, show ¬a < 64 by omega]) (by decide) (by decide)
  have fk : backward ((decode middle.length 0).zip (middle.map (BitVec.setWidth 2))) 0#2 =
      3#2 := by decide +kernel
  have bk : eval ((decode middle.length 0).zip (middle.map (BitVec.setWidth 2))) 0#2 =
      1#2 := by decide +kernel
  have records : Forward.records first 1#3 2 3 = [(7, 4), (3, 2)] := by
    unfold Forward.records bucketIndices indexedState
    decide +kernel
  simp only [fk, bk] at he
  change ExecWithin 12 _ input y _ at he
  simp only [show (3#2).toNat = 3 from rfl, records] at he
  refine ⟨y, ?_, ?_⟩
  · simpa +decide [first, middle] using he
  · simpa only [first, middle, List.length_cons, List.length_nil] using hw

/-- Actual projection, query computation and counter indices from original cells;
dirty projected cells are overwritten, and unrelated memory remains unchanged. -/
example : ((selectQueries 8 1 10 1 16 17 4 0 0 0 20 52).eval 12 16 input).map
    (fun r => ((r.1.regs selectedForward, r.1.regs selectedBackward),
      (r.1.regs state, r.1.regs backwardCounterIndex),
      (r.1.mem 16, r.1.mem 17, r.1.mem 13))) = some ((23, 53), (0, 3), (1, 1, 17)) := by
  decide +kernel

private def emptyInput : Data 32 :=
  { regs := fun _ => 17, mem := fun a => if a < 24 then 17 else 0 }

/-- The entire original-input program executes at width zero and returns four
zero words with a nonzero presence tag. Projection and query setup are charged. -/
example : ((projectedProbe 0 0 0 0 0 0 0 0 2 3 1 1 0 0 0 0 0 4 8 12 16 24).eval
    8 8 emptyInput).map (fun r => (r.1.regs operand, r.1.regs bits,
      r.1.regs operators, r.1.regs firstOperators, r.1.regs backwardCounterIndex)) =
      some (1, 0, 0, 0, 0) := by
  decide +kernel

/-- Class one has no hit in the empty width-one chain, whose only state is zero.
A local miss does not assert that the whole instance is unsatisfiable. -/
example : ((projectedProbe 0 0 0 0 0 0 0 0 2 3 2 2 1 0 0 0 0 4 8 12 16 24).eval
    8 8 emptyInput).map (fun r => r.1.regs operand) = some 0 := by
  decide +kernel

/-- Multiword reversed projection preserves operand order for inverse queries. -/
example : ((selectQueries 5 2 8 1 16 18 4 0 0 0 20 52).eval 12 16 input).map
    (fun r => ((r.1.regs selectedForward, r.1.regs selectedBackward),
      (r.1.mem 16, r.1.mem 17, r.1.mem 18))) = some ((21, 53), (2, 1, 1)) := by
  decide +kernel

/-- A nonzero class uses a different backward counter index. -/
example : ((selectCounterIndices 8 2).eval 8 1 input).map
    (fun r => (r.1.regs state, r.1.regs backwardCounterIndex)) = some (2, 5) := by
  decide +kernel
