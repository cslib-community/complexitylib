/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.WPP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Concrete nonvacuous clients and axiom guards for `WPP` and `LWPP` multiple-target robustness,
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

/-- `PolyTimeReducible.mem_LWPP` pulls back `LWPP` membership across a length-altering reduction. -/
example : {w : List Bool | w.tail.headD false = true} ∈ LWPP encBits :=
  tail_reduces_head.mem_LWPP head_mem_LWPP

example : {w : List Bool | w.headD false = true} ∈ WPP encBits :=
  UP_subset_WPP (P_subset_UP head_mem_P)

example : {w : List Bool | w.headD false = true}ᶜ ∈ LWPP encBits :=
  coUP_subset_LWPP (compl_mem_coUP.mpr (P_subset_UP head_mem_P))

example : {w : List Bool | w.headD false = true}ᶜ ∈ WPP encBits :=
  coUP_subset_WPP (compl_mem_coUP.mpr (P_subset_UP head_mem_P))

private theorem univ_mem_FewP : Set.univ ∈ FewP encBits := by
  refine mem_FewP.mpr ⟨1, 2, fun _ => true, .const true, ?_, ?_⟩ <;> intro a <;> simp

example : Set.univ ∈ LWPP encBits :=
  FewP_subset_LWPP univ_mem_FewP

example : Set.univ ∈ WPP encBits :=
  FewP_subset_WPP univ_mem_FewP

example : {w : List Bool | w.headD false = true} \ Set.univ ∈ LWPP encBits :=
  diff_mem_LWPP head_mem_LWPP (FewP_subset_LWPP univ_mem_FewP)

example : {w : List Bool | w.headD false = true} ∆ Set.univ ∈ LWPP encBits :=
  symmDiff_mem_LWPP head_mem_LWPP (FewP_subset_LWPP univ_mem_FewP)

example : {w : List Bool | w.headD false = true} \ Set.univ ∈ WPP encBits :=
  diff_mem_WPP (LWPP_subset_WPP head_mem_LWPP) (FewP_subset_WPP univ_mem_FewP)

example : {w : List Bool | w.headD false = true} ∆ Set.univ ∈ WPP encBits :=
  symmDiff_mem_WPP (LWPP_subset_WPP head_mem_LWPP) (FewP_subset_WPP univ_mem_FewP)

/-- A concrete two-target family `{1, -2}` witnessing `LWPP` membership via
`mem_LWPP_of_finset_targets` when members can take either of two distinct nonzero gap values. -/
private def twoTargets (b : Bool) (_ : ℕ) : ℤ := if b then 1 else -2

private theorem twoTargets_poly (b : Bool) :
    ComputableTidilyInPolyTime (twoTargets b) encUnary encIntBin := by
  cases b <;> exact .const _

private theorem twoTargets_ne_zero (b : Bool) (n : ℕ) : twoTargets b n ≠ 0 := by
  unfold twoTargets
  cases b <;> decide

private def twoTargetGap (w : List Bool) : ℤ :=
  if w.headD false then (if w.tail.headD false then 1 else -2) else 0

private theorem twoTargetGap_poly :
    ComputableTidilyInPolyTime twoTargetGap encBits encIntBin := by
  unfold twoTargetGap
  fun_prop

example : {w : List Bool | w.headD false = true} ∈ LWPP encBits := by
  refine mem_LWPP_of_finset_targets (Finset.univ : Finset Bool)
    (mem_GapP_of_polyTime (.of_tidy twoTargetGap_poly))
    (fun b _ => .of_tidy (twoTargets_poly b))
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
    (mem_GapP_of_polyTime (.of_tidy twoTargetGap_poly))
    (fun b _ => .of_tidy ((twoTargets_poly b).comp (.encoding_length encBits)))
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

/--
info: 'Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_prod' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableTidilyInPolyTime.intBin_prod

/--
info: 'Cslib.Complexity.FewP_subset_LWPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FewP_subset_LWPP

/--
info: 'Cslib.Complexity.FewP_subset_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.FewP_subset_WPP

/--
info: 'Cslib.Complexity.mem_WPP_of_finset_targets' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_WPP_of_finset_targets

/--
info: 'Cslib.Complexity.mem_LWPP_of_finset_targets' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_LWPP_of_finset_targets

/--
info: 'Cslib.Complexity.mem_LWPP_of_polyTime_index' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_LWPP_of_polyTime_index

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_LWPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_LWPP
