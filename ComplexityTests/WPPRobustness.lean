/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.WPP.Robustness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

open Cslib.Complexity Turing.MultiTapeTM

namespace WPPRobustnessTests

private def language : Set (List Bool) := {w | w.headD false = true}

private def gap (w : List Bool) : ℤ := if w.headD false then -1 else 0

private theorem gap_mem : gap ∈ GapP encBits := mem_GapP_of_polyTime
  (.of_tidy (by unfold gap; fun_prop))

private def targets (n : ℕ) : List ℤ := -1 :: -1 :: List.replicate n (-2)

private theorem targets_polyTime :
    ComputableInPolyTime targets encUnary (encList encIntBin) :=
  .of_tidy (by unfold targets; fun_prop)

private theorem targets_nonzero (n : ℕ) : (0 : ℤ) ∉ targets n := by simp [targets]

private theorem accepts (w : List Bool) (h : w ∈ language) : gap w ∈ targets w.length := by
  have ht : w.headD false = true := h
  simp only [gap, ht, ite_true, targets, List.mem_cons, true_or, eq_self]

private theorem rejects (w : List Bool) (h : w ∉ language) : gap w = 0 := by
  have ht : w.headD false = false := Bool.eq_false_iff.mpr h
  simp only [gap, ht, Bool.false_eq_true, ite_false]

-- A nonconstant language with a growing signed target list, including repeated targets.
example : language ∈ LWPP encBits :=
  mem_LWPP_of_polyTime_targets gap_mem targets_polyTime targets_nonzero accepts rejects

example : language ∈ WPP encBits :=
  mem_WPP_of_polyTime_targets gap_mem
    (targets_polyTime.comp
      (ComputableTidilyInPolyTime.encoding_length encBits).computableInPolyTime)
    (fun w => targets_nonzero w.length) accepts rejects

-- The plain characterization consumes a growing list certificate with unary input length.
example : language ∈ LWPP encBits :=
  mem_LWPP_iff_exists_polyTime_targets.mpr
    ⟨gap, gap_mem, targets, targets_polyTime, targets_nonzero, accepts, rejects⟩

-- A plain list certificate can be used directly in the uniform interpolation product theorem.
example : (fun w => ((targets w.length).map (fun z => z - gap w)).prod) ∈ GapP encBits :=
  GapP.prod_sub_mem
    (targets_polyTime.comp
      (ComputableTidilyInPolyTime.encoding_length encBits).computableInPolyTime)
    gap_mem

example : [true] ∈ language ∧ [false] ∉ language := by simp [language]
example : targets 0 = [-1, -1] := rfl
example : targets 3 = [-1, -1, -2, -2, -2] := rfl

-- Empty lists are allowed only when the accepting side is empty; their product target is one.
example : (∅ : Set (List Bool)) ∈ WPP encBits :=
  mem_WPP_of_polyTime_targets (GapP.zero_mem (enc := encBits))
    (ComputableInPolyTime.const ([] : List ℤ)) (by simp) (by simp) (by simp)

example : (∅ : Set (List Bool)) ∈ LWPP encBits :=
  mem_LWPP_of_polyTime_targets (GapP.zero_mem (enc := encBits))
    (ComputableInPolyTime.const ([] : List ℤ)) (by simp) (by simp) (by simp)

-- The interpolation polynomial retains multiplicity and signs.
example : (([-1, -1, -2] : List ℤ).map (fun z => z - (-1))).prod = 0 := by decide
example : (([-1, -1, -2] : List ℤ).map (fun z => z - 0)).prod = -2 := by decide

private def indexedGap (w : List Bool) : ℤ :=
  if w.headD false then -((w.length : ℤ) + 1) else 0

-- The indexed target-list API returns plain computability with the same unary count bound.
example : ComputableInPolyTime
    (indexedTargets (fun ni : ℕ × ℕ => -((ni.2 : ℤ) + 1)) (fun n => n + 1))
    encUnary (encList encIntBin) :=
  polyTime_indexedTargets (by fun_prop) (by fun_prop)

-- A varying last target witnesses acceptance; the theorem receives only its existence.
example : language ∈ LWPP encBits := by
  apply mem_LWPP_of_indexed_targets
    (g := indexedGap) (f := fun ni : ℕ × ℕ => -((ni.2 : ℤ) + 1)) (r := fun n => n + 1)
  · apply mem_GapP_of_polyTime
    have hl : ComputableTidilyInPolyTime (fun w : List Bool => (w.length : ℤ))
        encBits encIntBin := ComputableTidilyInPolyTime.intBin_natCast.comp
          (ComputableTidilyInPolyTime.unary_to_binary.comp (.encoding_length encBits))
    have hv : ComputableTidilyInPolyTime (fun w : List Bool => -((w.length : ℤ) + 1))
        encBits encIntBin := ComputableTidilyInPolyTime.intBin_neg.comp
          (ComputableTidilyInPolyTime.intBin_add' hl (.const 1))
    unfold indexedGap
    fun_prop
  · fun_prop
  · fun_prop
  · intro n i _
    lia
  · intro w hw
    refine ⟨w.length, by simp only [encBits_apply]; lia, ?_⟩
    have ht : w.headD false = true := hw
    simp only [indexedGap, ht, ite_true]
  · intro w hw
    have ht : w.headD false = false := Bool.eq_false_iff.mpr hw
    simp only [indexedGap, ht, Bool.false_eq_true, ite_false]

/-- info: 'Cslib.Complexity.GapP.prod_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.GapP.prod_sub_mem

/-- info: 'Cslib.Complexity.mem_WPP_iff_exists_polyTime_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.mem_WPP_iff_exists_polyTime_targets

/-- info: 'Cslib.Complexity.mem_LWPP_iff_exists_polyTime_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.mem_LWPP_iff_exists_polyTime_targets

end WPPRobustnessTests
