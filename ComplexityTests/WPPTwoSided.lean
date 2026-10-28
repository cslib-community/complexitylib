/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.WPP.TwoSided
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

open Cslib.Complexity Turing.MultiTapeTM

namespace WPPTwoSidedTests

private def language : Set (List Bool) := {w | w.headD false = true}

private def gap (w : List Bool) : ℤ := if w.headD false then 0 else 1

private theorem gap_mem : gap ∈ GapP encBits := mem_GapP_of_polyTime
  (by unfold gap; fun_prop)

private def yesTargets (n : ℕ) : List ℤ := 0 :: List.replicate n (-2)
private def noTargets (n : ℕ) : List ℤ := 1 :: List.replicate (2 * n) 3

private theorem yes_polyTime :
    ComputableInPolyTime yesTargets encUnary (encList encIntBin) := by
  unfold yesTargets; fun_prop

private theorem no_polyTime :
    ComputableInPolyTime noTargets encUnary (encList encIntBin) := by
  unfold noTargets; fun_prop

private theorem disjoint (n : ℕ) : (yesTargets n).Disjoint (noTargets n) := by
  simp [yesTargets, noTargets, List.disjoint_left]

private theorem accepts (w : List Bool) (h : w ∈ language) : gap w ∈ yesTargets w.length := by
  have ht : w.headD false = true := h
  simp only [gap, ht, ite_true, yesTargets, List.mem_cons, true_or, eq_self]

private theorem rejects (w : List Bool) (h : w ∉ language) : gap w ∈ noTargets w.length := by
  have ht : w.headD false = false := Bool.eq_false_iff.mpr h
  simp only [gap, ht, Bool.false_eq_true, ite_false, noTargets, List.mem_cons, true_or, eq_self]

-- Zero is an accepting target. Both lists grow, with signed and repeated entries.
example : language ∈ LWPP encBits :=
  mem_LWPP_of_disjoint_targets gap_mem yes_polyTime no_polyTime disjoint accepts rejects

example : language ∈ WPP encBits :=
  mem_WPP_of_disjoint_targets gap_mem
    (yes_polyTime.comp (ComputableInPolyTime.encoding_length encBits))
    (no_polyTime.comp (ComputableInPolyTime.encoding_length encBits))
    (fun w => disjoint w.length) accepts rejects

-- The plain characterization retains zero and signed/repeated targets on disjoint sides.
example : language ∈ LWPP encBits :=
  mem_LWPP_iff_exists_disjoint_targets.mpr
    ⟨gap, gap_mem, yesTargets, noTargets, yes_polyTime, no_polyTime, disjoint, accepts, rejects⟩

-- Swapping the lists gives zero as a rejecting target, without a zero-free hypothesis.
example : languageᶜ ∈ LWPP encBits := by
  apply mem_LWPP_of_disjoint_targets gap_mem no_polyTime yes_polyTime
    (fun n => (disjoint n).symm)
  · intro w hw
    exact rejects w hw
  · intro w hw
    exact accepts w (by simpa using hw)

example : [true] ∈ language ∧ [false] ∉ language := by simp [language]
example : yesTargets 0 = [0] ∧ noTargets 0 = [1] := by simp [yesTargets, noTargets]
example : yesTargets 2 = [0, -2, -2] := rfl
example : noTargets 1 = [1, 3, 3] := rfl
example : ¬([0] : List ℤ).Disjoint [0] := by simp

-- Empty rejection lists are consistent with a full language, even with gap zero.
example : (Set.univ : Set (List Bool)) ∈ WPP encBits :=
  mem_WPP_of_disjoint_targets (GapP.zero_mem (enc := encBits))
    (ComputableInPolyTime.const ([0] : List ℤ))
    (ComputableInPolyTime.const ([] : List ℤ)) (by simp) (by simp) (by simp)

-- Empty acceptance lists are consistent with an empty language and rejection target zero.
example : (∅ : Set (List Bool)) ∈ LWPP encBits :=
  mem_LWPP_of_disjoint_targets (GapP.zero_mem (enc := encBits))
    (ComputableInPolyTime.const ([] : List ℤ))
    (ComputableInPolyTime.const ([0] : List ℤ)) (by simp) (by simp) (by simp)

-- The source-style indexed interface uses two independent growing target counts.
example : language ∈ LWPP encBits := by
  apply mem_LWPP_of_disjoint_indexed_targets gap_mem
    (yes := fun _ => 0) (no := fun _ => 1) (ry := fun n => n + 1) (rn := fun n => 2 * n + 1)
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · simp
  · intro w hw
    refine ⟨0, by lia, ?_⟩
    have ht : w.headD false = true := hw
    simp only [gap, ht, ite_true]
  · intro w hw
    refine ⟨0, by lia, ?_⟩
    have ht : w.headD false = false := Bool.eq_false_iff.mpr hw
    simp only [gap, ht, Bool.false_eq_true, ite_false]

end WPPTwoSidedTests
