/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Submodular Set Functions and Marginal Gains

This module defines submodular set functions on `Finset α` and proves their fundamental algebraic
properties ([NemhauserWolseyFisher1978], Section 2, Proposition 2.1):

1. Subtraction-free submodularity `f (A ∪ B) + f (A ∩ B) ≤ f A + f B` over any ordered commutative
   additive monoid (`IsSubmodular`).
2. Exact characterization via diminishing marginal returns (`isSubmodular_iff_insert_add_le` over
   cancellative ordered monoids such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `isSubmodular_iff_marginalGain_le`
   over ordered additive groups).
3. Subadditivity of marginal gains across set differences and unions
   (`IsSubmodular.sub_le_sum_marginalGain_sdiff` and
   `IsSubmodular.sub_le_sum_marginalGain_of_monotone`), which drives the Nemhauser–Wolsey–Fisher
   `(1 - 1/e)` greedy analysis.
4. Closure under constants, addition, finite sums, natural scalar multiplication, and upper
   truncation `min (f S) c` (for monotone submodular `f`), together with modular sums and weighted
   set-coverage constructors.

Monotonicity reuses Mathlib's `Monotone` (`A ⊆ B → f A ≤ f B`) directly on `Finset α`.

## Main definitions

* `Cslib.Algorithms.Lean.Submodular.IsSubmodular`: `∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B`.
* `Cslib.Algorithms.Lean.Submodular.marginalGain`: `f (insert x S) - f S`.
* `Cslib.Algorithms.Lean.Submodular.modularSum`: additive set function `∑ x ∈ S, w x`.
* `Cslib.Algorithms.Lean.Submodular.weightedCoverage`: coverage function
  `∑ u ∈ S.biUnion cover, w u`.

## Main results

* `isSubmodular_iff_insert_add_le`, `isSubmodular_iff_marginalGain_le`: diminishing-returns
  characterizations of `IsSubmodular`.
* `IsSubmodular.sub_le_sum_marginalGain_sdiff`, `IsSubmodular.sub_le_sum_marginalGain_of_monotone`:
  upper bounds on `f (S ∪ T) - f S` and `f T - f S` via single-element marginal gains at `S`.
* `IsSubmodular.add`, `isSubmodular_sum`, `IsSubmodular.nsmul`, `IsSubmodular.min_const`: closure
  properties.
* `isSubmodular_modularSum`, `isSubmodular_weightedCoverage`: canonical submodular constructors.

## References

* [NemhauserWolseyFisher1978] George L. Nemhauser, Laurence A. Wolsey, and Marshall L. Fisher,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—I*, 1978.
-/

public section

namespace Cslib.Algorithms.Lean.Submodular

/-! ## Core definitions -/

/-- A function `f : Finset α → β` is **submodular** if
`f (A ∪ B) + f (A ∩ B) ≤ f A + f B` for all finite sets `A, B`. Stated without subtraction so it
applies directly to `ℕ`-, `ℚ`-, and `ℝ`-valued functions alike. -/
@[expose] def IsSubmodular {α : Type*} {β : Type*} [DecidableEq α] [AddCommMonoid β] [Preorder β]
    (f : Finset α → β) : Prop :=
  ∀ A B : Finset α, f (A ∪ B) + f (A ∩ B) ≤ f A + f B

/-- Marginal gain `f (insert x S) - f S` of adding `x` to `S`. -/
@[expose] def marginalGain {α : Type*} {β : Type*} [DecidableEq α] [Sub β]
    (f : Finset α → β) (S : Finset α) (x : α) : β :=
  f (insert x S) - f S

@[simp] theorem marginalGain_empty_of_map_empty {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommGroup β] {f : Finset α → β} (hf : f ∅ = 0) (x : α) :
    marginalGain f ∅ x = f {x} := by
  simp [marginalGain, hf]

@[simp] theorem marginalGain_of_mem {α : Type*} {β : Type*} [DecidableEq α] [AddCommGroup β]
    {f : Finset α → β} {S : Finset α} {x : α} (hx : x ∈ S) :
    marginalGain f S x = 0 := by
  simp [marginalGain, Finset.insert_eq_of_mem hx]

theorem marginalGain_nonneg_of_monotone {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} (hmono : Monotone f) (S : Finset α) (x : α) :
    0 ≤ marginalGain f S x :=
  sub_nonneg.mpr (hmono (Finset.subset_insert x S))

theorem nonneg_of_empty_nonneg_of_monotone {α : Type*} {β : Type*} [Preorder β] [Zero β]
    {f : Finset α → β} (hf0 : 0 ≤ f ∅) (hmono : Monotone f) (S : Finset α) :
    0 ≤ f S :=
  hf0.trans (hmono (Finset.empty_subset S))

/-! ## Diminishing marginal returns characterization -/

section DiminishingReturns

variable {α : Type*} {β : Type*} [DecidableEq α]

/-- Forward diminishing returns (subtraction-free): if `f` is submodular, `A ⊆ B`, and `x ∉ B`,
then `f (insert x B) + f A ≤ f B + f (insert x A)`. -/
theorem IsSubmodular.insert_add_le [AddCommMonoid β] [Preorder β]
    {f : Finset α → β} (hf : IsSubmodular f)
    ⦃A B : Finset α⦄ (x : α) (hAB : A ⊆ B) (hx : x ∉ B) :
    f (insert x B) + f A ≤ f B + f (insert x A) := by
  have hunion : B ∪ insert x A = insert x B := by
    ext y
    simp only [Finset.mem_union, Finset.mem_insert]
    exact ⟨fun h => h.elim (Or.inr ∘ id) (fun h' => h'.elim Or.inl (Or.inr ∘ fun hA => hAB hA)),
      fun h => h.elim (Or.inr ∘ Or.inl) Or.inl⟩
  have hinter : B ∩ insert x A = A := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert]
    refine ⟨fun ⟨hyB, hy⟩ => hy.elim (fun hyx => absurd (hyx ▸ hyB) hx) id,
      fun hyA => ⟨hAB hyA, Or.inr hyA⟩⟩
  have h := hf B (insert x A)
  rwa [hunion, hinter] at h

/-- When `f` is also monotone, `f (insert x B) + f A ≤ f B + f (insert x A)` holds for every `x`
without needing `x ∉ B`. -/
theorem IsSubmodular.insert_add_le_of_monotone [AddCommMonoid β] [Preorder β] [AddLeftMono β]
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    ⦃A B : Finset α⦄ (x : α) (hAB : A ⊆ B) :
    f (insert x B) + f A ≤ f B + f (insert x A) := by
  by_cases hxB : x ∈ B
  · rw [Finset.insert_eq_of_mem hxB]
    exact add_le_add_right (hmono (Finset.subset_insert x A)) (f B)
  · exact hf.insert_add_le x hAB hxB

private theorem union_add_le_of_insert_add_le
    [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset α → β}
    (hdim : ∀ ⦃A B : Finset α⦄ (x : α), A ⊆ B → x ∉ B → f (insert x B) + f A ≤ f B + f (insert x A))
    {A I : Finset α} (hIA : I ⊆ A) :
    ∀ {D : Finset α}, Disjoint A D → f (A ∪ D) + f I ≤ f A + f (I ∪ D) := by
  intro D
  induction D using Finset.cons_induction with
  | empty =>
    intro _
    simp
  | cons x D' hxD' ih =>
    intro hdisj
    rw [Finset.cons_eq_insert] at hdisj ⊢
    have hxA : x ∉ A := (Finset.disjoint_insert_right.mp hdisj).1
    have hdisj' : Disjoint A D' := (Finset.disjoint_insert_right.mp hdisj).2
    have hstep1 : f (A ∪ D') + f I ≤ f A + f (I ∪ D') := ih hdisj'
    have hsub : I ∪ D' ⊆ A ∪ D' := Finset.union_subset_union hIA (Finset.Subset.refl D')
    have hx_not_AD' : x ∉ A ∪ D' := by
      simp [hxA, hxD']
    have hstep2 : f (insert x (A ∪ D')) + f (I ∪ D') ≤
        f (A ∪ D') + f (insert x (I ∪ D')) :=
      hdim x hsub hx_not_AD'
    rw [Finset.union_insert x A D', Finset.union_insert x I D']
    have hsum : (f (insert x (A ∪ D')) + f I) + (f (A ∪ D') + f (I ∪ D')) ≤
        (f A + f (insert x (I ∪ D'))) + (f (A ∪ D') + f (I ∪ D')) := calc
      (f (insert x (A ∪ D')) + f I) + (f (A ∪ D') + f (I ∪ D'))
          = (f (A ∪ D') + f I) + (f (insert x (A ∪ D')) + f (I ∪ D')) := by ac_rfl
      _ ≤ (f A + f (I ∪ D')) + (f (A ∪ D') + f (insert x (I ∪ D'))) := add_le_add hstep1 hstep2
      _ = (f A + f (insert x (I ∪ D'))) + (f (A ∪ D') + f (I ∪ D')) := by ac_rfl
    exact le_of_add_le_add_right hsum

/-- Converse of diminishing returns: if adding an element `x ∉ B` has smaller incremental effect on
`B` than on any subset `A ⊆ B`, then `f` is submodular. -/
theorem isSubmodular_of_insert_add_le
    [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset α → β}
    (hdim : ∀ ⦃A B : Finset α⦄ (x : α),
      A ⊆ B → x ∉ B → f (insert x B) + f A ≤ f B + f (insert x A)) :
    IsSubmodular f := by
  intro A B
  have hdisj : Disjoint A (B \ A) := Finset.disjoint_sdiff
  have h := union_add_le_of_insert_add_le hdim (Finset.inter_subset_left (s₂ := B)) hdisj
  have hAB : A ∪ (B \ A) = A ∪ B := Finset.union_sdiff_self_eq_union
  have hIB : (A ∩ B) ∪ (B \ A) = B := by
    ext y
    by_cases hyA : y ∈ A <;> simp [hyA]
  rwa [hAB, hIB] at h

/-- **Diminishing-Returns Characterization of Submodularity** ([NemhauserWolseyFisher1978],
Proposition 2.1), subtraction-free form valid over `ℕ`, `ℤ`, `ℚ`, and `ℝ`. -/
theorem isSubmodular_iff_insert_add_le
    [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
    {f : Finset α → β} :
    IsSubmodular f ↔
      ∀ ⦃A B : Finset α⦄ (x : α),
        A ⊆ B → x ∉ B → f (insert x B) + f A ≤ f B + f (insert x A) :=
  ⟨fun hf => hf.insert_add_le, isSubmodular_of_insert_add_le⟩

theorem IsSubmodular.marginalGain_le
    [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} (hf : IsSubmodular f)
    ⦃A B : Finset α⦄ (x : α) (hAB : A ⊆ B) (hx : x ∉ B) :
    marginalGain f B x ≤ marginalGain f A x := by
  have h := hf.insert_add_le x hAB hx
  rw [marginalGain, marginalGain, sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le]
  simpa [add_comm] using h

theorem IsSubmodular.marginalGain_le_of_monotone
    [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    ⦃A B : Finset α⦄ (x : α) (hAB : A ⊆ B) :
    marginalGain f B x ≤ marginalGain f A x := by
  have h := hf.insert_add_le_of_monotone hmono x hAB
  rw [marginalGain, marginalGain, sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le]
  simpa [add_comm] using h

/-- **Diminishing-Returns Characterization of Submodularity** in terms of `marginalGain` over an
ordered commutative group ([NemhauserWolseyFisher1978], Proposition 2.1). -/
theorem isSubmodular_iff_marginalGain_le
    [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} :
    IsSubmodular f ↔
      ∀ ⦃A B : Finset α⦄ (x : α), A ⊆ B → x ∉ B → marginalGain f B x ≤ marginalGain f A x := by
  rw [isSubmodular_iff_insert_add_le]
  refine ⟨fun h A B x hAB hx => ?_, fun h A B x hAB hx => ?_⟩
  · have h' := h x hAB hx
    rw [marginalGain, marginalGain, sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le]
    simpa [add_comm] using h'
  · have h' := h x hAB hx
    rw [marginalGain, marginalGain, sub_le_iff_le_add, sub_add_eq_add_sub, le_sub_iff_add_le] at h'
    simpa [add_comm] using h'

end DiminishingReturns

/-! ## Subadditivity of marginal gains over finite unions -/

section UnionSubadditivity

variable {α : Type*} {β : Type*} [DecidableEq α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]

private theorem sub_union_disjoint_le_sum_marginalGain
    {f : Finset α → β} (hf : IsSubmodular f) (S : Finset α) :
    ∀ {D : Finset α}, Disjoint S D → f (S ∪ D) - f S ≤ ∑ x ∈ D, marginalGain f S x := by
  intro D
  induction D using Finset.cons_induction with
  | empty =>
    intro _
    simp
  | cons x D' hxD' ih =>
    intro hdisj
    rw [Finset.cons_eq_insert] at hdisj ⊢
    have hxS : x ∉ S := (Finset.disjoint_insert_right.mp hdisj).1
    have hdisj' : Disjoint S D' := (Finset.disjoint_insert_right.mp hdisj).2
    have hx_not_SD' : x ∉ S ∪ D' := by simp [hxS, hxD']
    have hgain : marginalGain f (S ∪ D') x ≤ marginalGain f S x :=
      hf.marginalGain_le x Finset.subset_union_left hx_not_SD'
    have hrec : f (S ∪ D') - f S ≤ ∑ y ∈ D', marginalGain f S y := ih hdisj'
    have hsplit : f (S ∪ insert x D') - f S =
        marginalGain f (S ∪ D') x + (f (S ∪ D') - f S) := by
      rw [Finset.union_insert x S D', marginalGain, sub_add_sub_cancel]
    rw [hsplit, Finset.sum_insert hxD']
    exact add_le_add hgain hrec

/-- For any submodular function `f` (not necessarily monotone) and finite sets `S, T`,
`f (S ∪ T) - f S ≤ ∑ x ∈ T \ S, marginalGain f S x` ([NemhauserWolseyFisher1978],
Proposition 2.1(v)). -/
theorem IsSubmodular.sub_le_sum_marginalGain_sdiff
    {f : Finset α → β} (hf : IsSubmodular f) (S T : Finset α) :
    f (S ∪ T) - f S ≤ ∑ x ∈ T \ S, marginalGain f S x := by
  have h := sub_union_disjoint_le_sum_marginalGain hf S (D := T \ S) Finset.disjoint_sdiff
  rwa [Finset.union_sdiff_self_eq_union] at h

/-- **Monotone Submodular Marginal-Gain Bound** ([NemhauserWolseyFisher1978], Section 2,
Proposition 2.2(iv')): for monotone submodular `f` and any `S, T : Finset α`,
`f T - f S ≤ ∑ x ∈ T \ S, marginalGain f S x`. -/
theorem IsSubmodular.sub_le_sum_marginalGain_of_monotone
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (S T : Finset α) :
    f T - f S ≤ ∑ x ∈ T \ S, marginalGain f S x :=
  (sub_le_sub_right (hmono Finset.subset_union_right) (f S)).trans
    (hf.sub_le_sum_marginalGain_sdiff S T)

/-- Variant summing over all of `T` (elements in `T ∩ S` contribute `0`). -/
theorem IsSubmodular.sub_le_sum_marginalGain_full_of_monotone
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (S T : Finset α) :
    f T - f S ≤ ∑ x ∈ T, marginalGain f S x := by
  refine (hf.sub_le_sum_marginalGain_of_monotone hmono S T).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    fun x _ _ => marginalGain_nonneg_of_monotone hmono S x

end UnionSubadditivity

/-! ## Closure properties and canonical constructors -/

section Constructors

theorem isSubmodular_const {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [Preorder β] (c : β) :
    IsSubmodular (fun _ : Finset α => c) := fun _ _ => le_rfl

theorem IsSubmodular.add {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {f g : Finset α → β} (hf : IsSubmodular f) (hg : IsSubmodular g) :
    IsSubmodular (fun S => f S + g S) := fun A B => calc
  (f (A ∪ B) + g (A ∪ B)) + (f (A ∩ B) + g (A ∩ B))
      = (f (A ∪ B) + f (A ∩ B)) + (g (A ∪ B) + g (A ∩ B)) := by ac_rfl
  _ ≤ (f A + f B) + (g A + g B) := add_le_add (hf A B) (hg A B)
  _ = (f A + g A) + (f B + g B) := by ac_rfl

theorem isSubmodular_sum {ι : Type*} {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    (s : Finset ι) {g : ι → Finset α → β} (hg : ∀ i ∈ s, IsSubmodular (g i)) :
    IsSubmodular (fun S => ∑ i ∈ s, g i S) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using isSubmodular_const (α := α) (0 : β)
  | insert i s' hi ih =>
    have hi_sub : IsSubmodular (g i) := hg i (Finset.mem_insert_self i s')
    have hs'_sub : IsSubmodular (fun S => ∑ j ∈ s', g j S) :=
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)
    intro A B
    simpa [Finset.sum_insert hi] using (hi_sub.add hs'_sub) A B

theorem IsSubmodular.nsmul {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} (hf : IsSubmodular f) (n : ℕ) :
    IsSubmodular (fun S => n • f S) := by
  induction n with
  | zero =>
    intro A B
    simp
  | succ m ih =>
    simpa [succ_nsmul] using ih.add hf

/-- Truncating a monotone function above at a constant `c` (`fun S => min (f S) c`) preserves
monotonicity. -/
theorem monotone_min_const {α : Type*} {β : Type*} [LinearOrder β]
    {f : Finset α → β} (hmono : Monotone f) (c : β) :
    Monotone (fun S : Finset α => min (f S) c) :=
  fun _ _ hAB => min_le_min_right c (hmono hAB)

/-- Truncating a monotone submodular function above at a constant `c` (`fun S => min (f S) c`)
preserves submodularity. -/
theorem IsSubmodular.min_const {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (c : β) :
    IsSubmodular (fun S => min (f S) c) := by
  intro A B
  dsimp only
  by_cases hA : c ≤ f A
  · have hU : c ≤ f (A ∪ B) := hA.trans (hmono Finset.subset_union_left)
    rw [min_eq_right hU, min_eq_right hA]
    exact add_le_add le_rfl (min_le_min_right c (hmono Finset.inter_subset_right))
  · by_cases hB : c ≤ f B
    · have hU : c ≤ f (A ∪ B) := hB.trans (hmono Finset.subset_union_right)
      rw [min_eq_right hU, min_eq_right hB, add_comm c (min (f (A ∩ B)) c)]
      exact add_le_add (min_le_min_right c (hmono Finset.inter_subset_left)) le_rfl
    · push Not at hA hB
      rw [min_eq_left hA.le, min_eq_left hB.le]
      exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans (hf A B)

/-- Modular (additive) set function `∑ x ∈ S, w x`. -/
@[expose] def modularSum {α : Type*} {β : Type*} [AddCommMonoid β] (w : α → β) (S : Finset α) : β :=
  ∑ x ∈ S, w x

@[simp] theorem modularSum_empty {α : Type*} {β : Type*} [AddCommMonoid β] (w : α → β) :
    modularSum w ∅ = 0 :=
  Finset.sum_empty

theorem modularSum_union_add_inter {α : Type*} {β : Type*} [DecidableEq α] [AddCommMonoid β]
    (w : α → β) (A B : Finset α) :
    modularSum w (A ∪ B) + modularSum w (A ∩ B) = modularSum w A + modularSum w B :=
  Finset.sum_union_inter

theorem isSubmodular_modularSum {α : Type*} {β : Type*} [DecidableEq α]
    [AddCommMonoid β] [Preorder β] (w : α → β) :
    IsSubmodular (modularSum w) :=
  fun A B => (modularSum_union_add_inter w A B).le

theorem monotone_modularSum {α : Type*} {β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {w : α → β} (hw : ∀ x, 0 ≤ w x) :
    Monotone (modularSum w) :=
  fun _ _ hAB => Finset.sum_le_sum_of_subset_of_nonneg hAB fun x _ _ => hw x

/-- Weighted set-coverage function `∑ u ∈ S.biUnion cover, w u`. -/
@[expose] def weightedCoverage {α : Type*} {U : Type*} {β : Type*} [DecidableEq U] [AddCommMonoid β]
    (cover : α → Finset U) (w : U → β) (S : Finset α) : β :=
  ∑ u ∈ S.biUnion cover, w u

@[simp] theorem weightedCoverage_empty {α : Type*} {U : Type*} {β : Type*}
    [DecidableEq U] [AddCommMonoid β] (cover : α → Finset U) (w : U → β) :
    weightedCoverage cover w ∅ = 0 :=
  Finset.sum_empty

theorem monotone_weightedCoverage {α : Type*} {U : Type*} {β : Type*} [DecidableEq U]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (cover : α → Finset U) {w : U → β} (hw : ∀ u, 0 ≤ w u) :
    Monotone (weightedCoverage cover w) := by
  intro A B hAB
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => hw u)
  intro u hu
  rcases Finset.mem_biUnion.mp hu with ⟨a, ha, hu_cov⟩
  exact Finset.mem_biUnion.mpr ⟨a, hAB ha, hu_cov⟩

/-- Nonnegative weighted set coverage is submodular. -/
theorem isSubmodular_weightedCoverage {α : Type*} {U : Type*} {β : Type*}
    [DecidableEq α] [DecidableEq U]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    (cover : α → Finset U) {w : U → β} (hw : ∀ u, 0 ≤ w u) :
    IsSubmodular (weightedCoverage cover w) := by
  intro A B
  dsimp only [weightedCoverage]
  have hU : (A ∪ B).biUnion cover = A.biUnion cover ∪ B.biUnion cover := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_union]
    exact ⟨fun ⟨a, ha, hu⟩ => ha.elim (fun hA => Or.inl ⟨a, hA, hu⟩) (fun hB => Or.inr ⟨a, hB, hu⟩),
      fun h => h.elim (fun ⟨a, hA, hu⟩ => ⟨a, Or.inl hA, hu⟩)
        (fun ⟨a, hB, hu⟩ => ⟨a, Or.inr hB, hu⟩)⟩
  rw [hU]
  have hsub : (A ∩ B).biUnion cover ⊆ A.biUnion cover ∩ B.biUnion cover := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨a, haAB, hu_cov⟩
    rcases Finset.mem_inter.mp haAB with ⟨haA, haB⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨a, haA, hu_cov⟩, Finset.mem_biUnion.mpr ⟨a, haB, hu_cov⟩⟩
  have hle : ∑ u ∈ (A ∩ B).biUnion cover, w u ≤
      ∑ u ∈ A.biUnion cover ∩ B.biUnion cover, w u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun u _ _ => hw u
  calc
    (∑ u ∈ A.biUnion cover ∪ B.biUnion cover, w u) + ∑ u ∈ (A ∩ B).biUnion cover, w u
        ≤ (∑ u ∈ A.biUnion cover ∪ B.biUnion cover, w u) +
            ∑ u ∈ A.biUnion cover ∩ B.biUnion cover, w u := add_le_add le_rfl hle
    _ = (∑ u ∈ A.biUnion cover, w u) + ∑ u ∈ B.biUnion cover, w u := Finset.sum_union_inter

end Constructors

end Cslib.Algorithms.Lean.Submodular
