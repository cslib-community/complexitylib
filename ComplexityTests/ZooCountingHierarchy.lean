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

private theorem tail_reduces_head : PolyTimeReducible encBits encBits
    {w : List Bool | w.tail.headD false = true} {w | w.headD false = true} :=
  ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩

/-- A `US` no-instance may have two accepting witnesses, rather than zero. -/
example : (∅ : Set (List Bool)) ∈ US encBits :=
  ⟨2, SharpP.natCast_mem 2, fun _ => by norm_num⟩

/-- `US` and `CeqP` memberships, intersection closure, and reduction pullback. -/
example :
    {w : List Bool | w.headD false = true} ∈ CeqP encBits ∧
    {w : List Bool | w.headD false = true} ∩ Set.univ ∈ US encBits ∧
    {w : List Bool | w.tail.headD false = true} ∈ US encBits :=
  ⟨US_subset_CeqP head_mem_US,
    inter_mem_US head_mem_US ⟨1, SharpP.one_mem, fun _ => by simp⟩,
    tail_reduces_head.mem_US head_mem_US⟩

/-- FP counts may be exponentially large: the output encoding is binary. -/
example : (fun w : List Bool => 2 ^ w.length) ∈ SharpP encBits :=
  mem_SharpP_of_polyTime
    (ComputableInPolyTime.binary_two_pow.comp (.encoding_length encBits))

private def target (n : ℕ) : ℤ := -(2 ^ n : ℤ)

private theorem target_poly : ComputableInPolyTime target encUnary encIntBin := by
  unfold target
  fun_prop

private theorem target_ne_zero (n : ℕ) : target n ≠ 0 := by
  simp [target]

/-- A nonconstant language with a negative target of exponential magnitude. -/
private theorem head_mem_LWPP : {w : List Bool | w.headD false = true} ∈ LWPP encBits := by
  have htarget : ComputableInPolyTime (fun w : List Bool => target w.length)
      encBits encIntBin := target_poly.comp (.encoding_length encBits)
  have hgap : ComputableInPolyTime
      (fun w : List Bool => if w.headD false then target w.length else 0) encBits encIntBin := by
    fun_prop
  refine ⟨_, mem_GapP_of_polyTime hgap, target, target_poly, target_ne_zero,
    fun w => ?_, fun w => ?_⟩
  · cases w.headD false <;> simp
  · change (w.headD false = true) ↔ _
    cases w.headD false <;> simp [(target_ne_zero _).symm]

example :
    {w : List Bool | w.headD false = true} ∈ WPP encBits ∧
    {w : List Bool | w.headD false = true}ᶜ ∈ LWPP encBits ∧
    {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true}ᶜ ∈ LWPP encBits ∧
    {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true}ᶜ ∈ WPP encBits ∧
    {w : List Bool | w.tail.headD false = true} ∈ WPP encBits ∧
    {w : List Bool | w.headD false = true} ∈ CeqP encBits ∩ coCeqP encBits :=
  ⟨LWPP_subset_WPP head_mem_LWPP,
    compl_mem_LWPP head_mem_LWPP,
    inter_mem_LWPP head_mem_LWPP (compl_mem_LWPP head_mem_LWPP),
    union_mem_WPP (LWPP_subset_WPP head_mem_LWPP)
      (compl_mem_WPP (LWPP_subset_WPP head_mem_LWPP)),
    tail_reduces_head.mem_WPP (LWPP_subset_WPP head_mem_LWPP),
    ⟨WPP_subset_CeqP (LWPP_subset_WPP head_mem_LWPP),
      WPP_subset_coCeqP (LWPP_subset_WPP head_mem_LWPP)⟩⟩

example :
    (Set.univ : Set (List Bool)) ∈ coModP 6 encBits ∧
    (Set.univ : Set (List Bool)) ∈ ModP 3 encBits :=
  ⟨mem_coModP_iff_exists_SharpP.mpr ⟨6, SharpP.natCast_mem 6, fun _ => by norm_num⟩,
    coModP_eq_ModP (by decide : Nat.Prime 3) ▸
      mem_coModP_iff_exists_SharpP.mpr ⟨3, SharpP.natCast_mem 3, fun _ => by norm_num⟩⟩

private theorem head_mem_NP : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  UP_subset_NP (P_subset_UP head_mem_P)

private theorem head_mem_BH_one : {w : List Bool | w.headD false = true} ∈ BH encBits 1 :=
  BH_one ▸ head_mem_NP

private theorem head_mem_coBH_two :
    {w : List Bool | w.headD false = true} ∈ coBH encBits 2 :=
  BH_subset_coBH_succ 1 head_mem_BH_one

example :
    (∅ : Set (List Bool)) ∈ BH encBits 0 ∧
    (Set.univ : Set (List Bool)) ∈ coBH encBits 0 ∧
    {w : List Bool | w.headD false = true}ᶜ ∈ coBH encBits 1 ∧
    {w : List Bool | w.headD false = true} ∈ DP encBits ∧
    {w : List Bool | w.headD false = true} ∈ coDP encBits ∧
    {w : List Bool | w.headD false = true} ∈ BH encBits 3 ∧
    {w : List Bool | w.headD false = true} ∈ coBH encBits 5 ∧
    {w : List Bool | w.headD false = true} ∈ BH encBits 7 :=
  ⟨rfl,
    by simp [coBH_zero],
    by rw [coBH_one, coNP, Set.mem_ofPred_eq, compl_compl]; exact head_mem_NP,
    BH_two ▸ BH_mono (by decide : 1 ≤ 2) head_mem_BH_one,
    by rw [← coBH_two]; exact head_mem_coBH_two,
    coBH_subset_BH_succ 2 head_mem_coBH_two,
    coBH_mono (by decide : 2 ≤ 5) head_mem_coBH_two,
    BH_mono (by decide : 1 ≤ 7) head_mem_BH_one⟩

example :
    {w : List Bool | w.headD false = true} ∈ BooleanHierarchy encBits ∧
    {w : List Bool | w.headD false = true}ᶜ ∈ BooleanHierarchy encBits ∧
    {w : List Bool | w.headD false = true} ∩ {w | w.headD false = true} ∈ BH encBits 1 ∧
    {w : List Bool | w.headD false = true} \ {w | w.headD false = true} ∈ BH encBits 2 ∧
    {w : List Bool | w.headD false = true} ∪ {w | w.headD false = true} ∈ BH encBits 2 :=
  ⟨iUnion_coBH_eq_BooleanHierarchy ▸ Set.mem_iUnion.mpr ⟨2, head_mem_coBH_two⟩,
    compl_mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩),
    inter_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP,
    diff_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP,
    union_mem_BH_of_mem_NP head_mem_BH_one head_mem_NP⟩

example :
    {w : List Bool | w.tail.headD false = true} ∈ BH encBits 1 ∧
    {w : List Bool | w.tail.headD false = true} ∈ coBH encBits 2 ∧
    {w : List Bool | w.tail.headD false = true} ∈ BooleanHierarchy encBits :=
  ⟨tail_reduces_head.mem_BH head_mem_BH_one,
    tail_reduces_head.mem_coBH head_mem_coBH_two,
    tail_reduces_head.mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩)⟩

example (k : ℕ) (h : coBH encBits k ⊆ BH encBits k) :
    BH encBits k = coBH encBits k ∧
    {w : List Bool | w.headD false = true}ᶜ ∈ BH encBits k :=
  ⟨BH_eq_coBH_iff_BH_succ_eq.mpr
     (Set.Subset.antisymm (BH_succ_subset_iff_coBH_subset.mpr h) (BH_mono (Nat.le_succ k))),
   BooleanHierarchy_eq_BH_of_coBH_subset h ▸
     compl_mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩)⟩

example (h : NP encBits = coNP encBits) :
    {w : List Bool | w.headD false = true}ᶜ ∈ NP encBits :=
  BooleanHierarchy_eq_NP_of_NP_eq_coNP h ▸
    compl_mem_BooleanHierarchy (Set.mem_iUnion.mpr ⟨1, head_mem_BH_one⟩)

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
