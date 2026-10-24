/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.US
import Complexity.Computability.Complexity.Classes.WPP
import Complexity.Computability.Complexity.Classes.ModP
import Complexity.Computability.Complexity.Classes.BooleanHierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Clients of counting targets, unique solutions and the Boolean hierarchy. -/

namespace ComplexityTests.ZooCountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

private theorem head_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem head_mem_US : {w : List Bool | w.headD false = true} ∈ US encBits :=
  UP_subset_US (P_subset_UP head_mem_P)

example : {w : List Bool | w.headD false = true} ∈ CeqP encBits :=
  US_subset_CeqP head_mem_US

/-- A US no-instance may have two accepting witnesses. -/
example : (∅ : Set (List Bool)) ∈ US encBits :=
  ⟨2, SharpP.natCast_mem 2, fun _ => by norm_num⟩

example : {w : List Bool | w.headD false = true} ∩ Set.univ ∈ US encBits :=
  inter_mem_US head_mem_US ⟨1, SharpP.one_mem, fun _ => by simp⟩

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

example : {w : List Bool | w.tail.headD false = true} ∈ US encBits :=
  tail_reduces_head.mem_US head_mem_US

/-- FP counts may be exponentially large: the output encoding is binary. -/
example : (fun w : List Bool => 2 ^ w.length) ∈ SharpP encBits :=
  mem_SharpP_of_polyTime
    (.of_tidy (ComputableTidilyInPolyTime.binary_two_pow.comp (.encoding_length encBits)))

private def target (n : ℕ) : ℤ := -(2 ^ n : ℤ)

private theorem target_poly : ComputableTidilyInPolyTime target encUnary encIntBin := by
  unfold target
  fun_prop

private theorem target_ne_zero (n : ℕ) : target n ≠ 0 := by
  simp [target]

/-- A nonconstant language with a negative target of exponential magnitude. -/
private theorem head_mem_LWPP : {w : List Bool | w.headD false = true} ∈ LWPP encBits := by
  have htarget : ComputableTidilyInPolyTime (fun w : List Bool => target w.length)
      encBits encIntBin := target_poly.comp (.encoding_length encBits)
  have hgap : ComputableTidilyInPolyTime
      (fun w : List Bool => if w.headD false then target w.length else 0) encBits encIntBin := by
    fun_prop
  refine ⟨_, mem_GapP_of_polyTime (.of_tidy hgap), target, .of_tidy target_poly, target_ne_zero,
    fun w => ?_, fun w => ?_⟩
  · cases w.headD false <;> simp
  · change (w.headD false = true) ↔ _
    cases w.headD false <;> simp [(target_ne_zero _).symm]

example : {w : List Bool | w.headD false = true} ∈ WPP encBits :=
  LWPP_subset_WPP head_mem_LWPP

example : {w : List Bool | w.headD false = true}ᶜ ∈ LWPP encBits :=
  compl_mem_LWPP head_mem_LWPP

example : {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ LWPP encBits :=
  inter_mem_LWPP head_mem_LWPP (compl_mem_LWPP head_mem_LWPP)

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ WPP encBits :=
  union_mem_WPP (LWPP_subset_WPP head_mem_LWPP)
    (compl_mem_WPP (LWPP_subset_WPP head_mem_LWPP))

example : {w : List Bool | w.tail.headD false = true} ∈ WPP encBits :=
  tail_reduces_head.mem_WPP (LWPP_subset_WPP head_mem_LWPP)

example : {w : List Bool | w.headD false = true} ∈ CeqP encBits ∩ coCeqP encBits :=
  ⟨WPP_subset_CeqP (LWPP_subset_WPP head_mem_LWPP),
    WPP_subset_coCeqP (LWPP_subset_WPP head_mem_LWPP)⟩

example : Set.univ ∈ coModP 6 encBits :=
  mem_coModP_iff_exists_SharpP.mpr ⟨6, SharpP.natCast_mem 6, fun _ => by norm_num⟩

example : coModP 3 encBits = ModP 3 encBits := coModP_eq_ModP (by decide)

example : (∅ : Set (List Bool)) ∈ BH encBits 0 := rfl
example : BH encBits 1 = NP encBits := BH_one
example : BH encBits 2 = DP encBits := BH_two

private theorem head_mem_BH_one : {w : List Bool | w.headD false = true} ∈ BH encBits 1 := by
  rw [BH_one]
  exact UP_subset_NP (P_subset_UP head_mem_P)

example : {w : List Bool | w.headD false = true} ∈ BH encBits 7 :=
  BH_mono (by decide : 1 ≤ 7) head_mem_BH_one

example : {w : List Bool | w.tail.headD false = true} ∈ BH encBits 1 :=
  tail_reduces_head.mem_BH head_mem_BH_one

example : {w : List Bool | w.headD false = true}ᶜ ∈ BooleanHierarchy encBits :=
  compl_mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩)

example : {w : List Bool | w.headD false = true} ∈ coDP encBits := by
  rw [← coBH_two]
  exact BH_subset_coBH_succ 1 head_mem_BH_one

example : (Set.univ : Set (List Bool)) ∈ coBH encBits 0 := by
  simp [coBH_zero]

example : coBH encBits 1 = coNP encBits := coBH_one
example : coBH encBits 2 = coDP encBits := coBH_two

private theorem head_mem_coBH_two :
    {w : List Bool | w.headD false = true} ∈ coBH encBits 2 :=
  BH_subset_coBH_succ 1 head_mem_BH_one

example : {w : List Bool | w.headD false = true} ∈ coBH encBits 5 :=
  coBH_mono (by decide : 2 ≤ 5) head_mem_coBH_two

example : {w : List Bool | w.headD false = true} ∈ BH encBits 3 :=
  coBH_subset_BH_succ 2 head_mem_coBH_two

example : (⋃ n, coBH encBits n) = BooleanHierarchy encBits :=
  iUnion_coBH_eq_BooleanHierarchy

private theorem head_mem_NP : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  UP_subset_NP (P_subset_UP head_mem_P)

example : {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true} ∈ BH encBits 1 :=
  inter_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP

example : {w : List Bool | w.headD false = true} \ {w | w.headD false = true} ∈ BH encBits 2 :=
  diff_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP

example : {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true} ∈ BH encBits 2 :=
  union_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP

example : {w : List Bool | w.tail.headD false = true} ∈ coBH encBits 2 :=
  tail_reduces_head.mem_coBH head_mem_coBH_two

example : {w : List Bool | w.tail.headD false = true} ∈ BooleanHierarchy encBits :=
  tail_reduces_head.mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩)

example (k : ℕ) : BH encBits (k + 1) ⊆ BH encBits k ↔ coBH encBits k ⊆ BH encBits k :=
  BH_succ_subset_iff_coBH_subset

example (k : ℕ) : BH encBits k = coBH encBits k ↔ BH encBits (k + 1) = BH encBits k :=
  BH_eq_coBH_iff_BH_succ_eq

example (k : ℕ) (h : coBH encBits k ⊆ BH encBits k) :
    BooleanHierarchy encBits = BH encBits k :=
  BooleanHierarchy_eq_BH_of_coBH_subset h

example (h : NP encBits = coNP encBits) : BooleanHierarchy encBits = NP encBits :=
  BooleanHierarchy_eq_NP_of_NP_eq_coNP h

private abbrev trivialClass : Set (Set Bool) := {∅, Set.univ}

private theorem inter_mem_trivialClass :
    ∀ B₁ ∈ trivialClass, ∀ B₂ ∈ trivialClass, B₁ ∩ B₂ ∈ trivialClass := by
  rintro B₁ (rfl | rfl) B₂ (rfl | rfl) <;> simp [trivialClass]

private theorem compl_mem_differenceHierarchy_trivialClass_one :
    ∀ D ∈ differenceHierarchy trivialClass 1, Dᶜ ∈ differenceHierarchy trivialClass 1 := by
  rw [differenceHierarchy_one]
  rintro D (rfl | rfl) <;> simp [trivialClass]

private theorem trivialClass_succ_subset :
    differenceHierarchy trivialClass 2 ⊆ differenceHierarchy trivialClass 1 :=
  differenceHierarchy_succ_subset_of_compl inter_mem_trivialClass
    compl_mem_differenceHierarchy_trivialClass_one

example : differenceHierarchy trivialClass 5 = differenceHierarchy trivialClass 1 :=
  differenceHierarchy_eq_of_succ_subset (by simp [trivialClass]) trivialClass_succ_subset
    (by decide : 1 ≤ 5)

private theorem not_coBH_zero_subset_BH_zero : ¬ (coBH encBool 0 ⊆ BH encBool 0) := by
  intro h
  have huniv : (Set.univ : Set Bool) ∈ BH encBool 0 := h (by simp [coBH_zero])
  rw [BH_zero, Set.mem_singleton_iff] at huniv
  have hmem : true ∈ (Set.univ : Set Bool) := Set.mem_univ true
  rw [huniv] at hmem
  exact hmem

example : ¬ (BH encBool 1 ⊆ BH encBool 0) :=
  fun h => not_coBH_zero_subset_BH_zero (BH_succ_subset_iff_coBH_subset.mp h)

end ComplexityTests.ZooCountingHierarchy

/--
info: 'Cslib.Complexity.UP_subset_US' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.UP_subset_US

/--
info: 'Cslib.Complexity.coNP_subset_US' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coNP_subset_US

/--
info: 'Cslib.Complexity.US_subset_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.US_subset_CeqP

/--
info: 'Cslib.Complexity.inter_mem_US' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_US

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_US' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_US

/--
info: 'Cslib.Complexity.mem_SharpP_of_polyTime' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_SharpP_of_polyTime

/--
info: 'Cslib.Complexity.mem_GapP_of_polyTime' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_GapP_of_polyTime

/--
info: 'Cslib.Complexity.SPP_subset_LWPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SPP_subset_LWPP

/--
info: 'Cslib.Complexity.LWPP_subset_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.LWPP_subset_WPP

/--
info: 'Cslib.Complexity.WPP_subset_CeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.WPP_subset_CeqP

/--
info: 'Cslib.Complexity.WPP_subset_coCeqP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.WPP_subset_coCeqP

/--
info: 'Cslib.Complexity.compl_mem_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_WPP

/--
info: 'Cslib.Complexity.inter_mem_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_WPP

/--
info: 'Cslib.Complexity.compl_mem_LWPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.compl_mem_LWPP

/--
info: 'Cslib.Complexity.inter_mem_LWPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_LWPP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_WPP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_WPP

/--
info: 'Cslib.Complexity.BH_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BH_two

/--
info: 'Cslib.Complexity.BH_mono' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BH_mono

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_BH' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_BH

/--
info: 'Cslib.Complexity.coBH_two' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coBH_two

/--
info: 'Cslib.Complexity.iUnion_coBH_eq_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.iUnion_coBH_eq_BooleanHierarchy

/--
info: 'Cslib.Complexity.inter_mem_BH_of_mem_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.inter_mem_BH_of_mem_NP

/--
info: 'Cslib.Complexity.diff_mem_BH_of_mem_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.diff_mem_BH_of_mem_NP

/--
info: 'Cslib.Complexity.union_mem_BH_of_mem_NP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.union_mem_BH_of_mem_NP

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_coBH' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_coBH

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_BooleanHierarchy' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_BooleanHierarchy

/--
info: 'Cslib.Complexity.BH_succ_subset_iff_coBH_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BH_succ_subset_iff_coBH_subset

/--
info: 'Cslib.Complexity.BH_eq_coBH_iff_BH_succ_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BH_eq_coBH_iff_BH_succ_eq

/--
info: 'Cslib.Complexity.BH_eq_of_coBH_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BH_eq_of_coBH_subset

/--
info: 'Cslib.Complexity.coBH_eq_BH_of_coBH_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coBH_eq_BH_of_coBH_subset

/--
info: 'Cslib.Complexity.BooleanHierarchy_eq_BH_of_coBH_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BooleanHierarchy_eq_BH_of_coBH_subset

/--
info: 'Cslib.Complexity.BooleanHierarchy_eq_NP_of_NP_eq_coNP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BooleanHierarchy_eq_NP_of_NP_eq_coNP

/--
info: 'Cslib.Complexity.mem_coDP_iff_union' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_coDP_iff_union

/--
info: 'Cslib.Complexity.coModP_eq_ModP' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.coModP_eq_ModP
