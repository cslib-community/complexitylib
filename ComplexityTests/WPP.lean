/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.WPP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete nonvacuous clients for `WPP` and `LWPP` multiple-target robustness,
unary-indexed target normalization, many-one reduction closure, Boolean closures, and
`intBin_prod`. -/

namespace ComplexityTests.WPP

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped symmDiff

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem head_mem_LWPP : {w : List Bool | w.headD false = true} ∈ LWPP encBits :=
  UP_subset_LWPP (P_subset_UP head_mem_P)

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

private theorem univ_mem_FewP : Set.univ ∈ FewP encBits := by
  refine mem_FewP.mpr ⟨1, 2, fun _ => true, .const true, ?_, ?_⟩ <;> intro a <;> simp

/-- `PolyTimeReducible.mem_LWPP` and `PolyTimeReducible.mem_WPP` pull back membership across a
length-altering reduction, while `UP`, `coUP`, and `FewP` witnesses embed into both classes. -/
example :
    ({w : List Bool | w.tail.headD false = true} ∈ LWPP encBits ∧
      {w : List Bool | w.tail.headD false = true} ∈ WPP encBits) ∧
    ({w : List Bool | w.headD false = true}ᶜ ∈ LWPP encBits ∧
      {w : List Bool | w.headD false = true}ᶜ ∈ WPP encBits) ∧
    (Set.univ ∈ LWPP encBits ∧ Set.univ ∈ WPP encBits) :=
  have h_up := P_subset_UP head_mem_P
  have h_coup := compl_mem_coUP.mpr h_up
  ⟨⟨tail_reduces_head.mem_LWPP head_mem_LWPP,
    tail_reduces_head.mem_WPP (UP_subset_WPP h_up)⟩,
   ⟨coUP_subset_LWPP h_coup, coUP_subset_WPP h_coup⟩,
   ⟨FewP_subset_LWPP univ_mem_FewP, FewP_subset_WPP univ_mem_FewP⟩⟩

/-- Set-difference and symmetric-difference closures in `LWPP` and `WPP`. -/
example :
    ({w : List Bool | w.headD false = true} \ Set.univ ∈ LWPP encBits ∧
      {w : List Bool | w.headD false = true} ∆ Set.univ ∈ LWPP encBits) ∧
    ({w : List Bool | w.headD false = true} \ Set.univ ∈ WPP encBits ∧
      {w : List Bool | w.headD false = true} ∆ Set.univ ∈ WPP encBits) :=
  ⟨⟨diff_mem_LWPP head_mem_LWPP (FewP_subset_LWPP univ_mem_FewP),
    symmDiff_mem_LWPP head_mem_LWPP (FewP_subset_LWPP univ_mem_FewP)⟩,
   ⟨diff_mem_WPP (LWPP_subset_WPP head_mem_LWPP) (FewP_subset_WPP univ_mem_FewP),
    symmDiff_mem_WPP (LWPP_subset_WPP head_mem_LWPP) (FewP_subset_WPP univ_mem_FewP)⟩⟩

/-- A concrete two-target family `{1, -2}` witnessing `LWPP` membership via
`mem_LWPP_of_finset_targets` when members can take either of two distinct nonzero gap values. -/
private def twoTargets (b : Bool) (_ : ℕ) : ℤ := if b then 1 else -2

private theorem twoTargets_poly (b : Bool) :
    ComputableInPolyTime (twoTargets b) encUnary encIntBin := by
  cases b <;> exact .const _

private theorem twoTargets_ne_zero (b : Bool) (n : ℕ) : twoTargets b n ≠ 0 := by
  unfold twoTargets
  cases b <;> decide

private def twoTargetGap (w : List Bool) : ℤ :=
  if w.headD false then (if w.tail.headD false then 1 else -2) else 0

private theorem twoTargetGap_poly :
    ComputableInPolyTime twoTargetGap encBits encIntBin := by
  unfold twoTargetGap
  fun_prop

example : {w : List Bool | w.headD false = true} ∈ LWPP encBits := by
  refine mem_LWPP_of_finset_targets (Finset.univ : Finset Bool)
    (mem_GapP_of_polyTime twoTargetGap_poly)
    (fun b _ => twoTargets_poly b)
    (fun b _ => twoTargets_ne_zero b)
    (fun w => ?_) (fun w => ?_)
  · unfold twoTargetGap twoTargets
    cases w.headD false
    · exact Or.inl rfl
    · cases w.tail.headD false
      · exact Or.inr ⟨false, Finset.mem_univ _, rfl⟩
      · exact Or.inr ⟨true, Finset.mem_univ _, rfl⟩
  · change (w.headD false = true) ↔ _
    unfold twoTargetGap twoTargets
    cases w.headD false
    · simp
    · cases w.tail.headD false
      · exact ⟨fun _ => ⟨false, Finset.mem_univ _, rfl⟩, fun _ => rfl⟩
      · exact ⟨fun _ => ⟨true, Finset.mem_univ _, rfl⟩, fun _ => rfl⟩

example : {w : List Bool | w.headD false = true} ∈ WPP encBits := by
  refine mem_WPP_of_finset_targets (Finset.univ : Finset Bool)
    (mem_GapP_of_polyTime twoTargetGap_poly)
    (fun b _ => (twoTargets_poly b).comp (.encoding_length encBits))
    (fun b _ w => twoTargets_ne_zero b w.length)
    (fun w => ?_) (fun w => ?_)
  · unfold twoTargetGap twoTargets
    cases w.headD false
    · exact Or.inl rfl
    · cases w.tail.headD false
      · exact Or.inr ⟨false, Finset.mem_univ _, rfl⟩
      · exact Or.inr ⟨true, Finset.mem_univ _, rfl⟩
  · change (w.headD false = true) ↔ _
    unfold twoTargetGap twoTargets
    cases w.headD false
    · simp
    · cases w.tail.headD false
      · exact ⟨fun _ => ⟨false, Finset.mem_univ _, rfl⟩, fun _ => rfl⟩
      · exact ⟨fun _ => ⟨true, Finset.mem_univ _, rfl⟩, fun _ => rfl⟩

end ComplexityTests.WPP
