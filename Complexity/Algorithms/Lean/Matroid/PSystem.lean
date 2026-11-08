/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Order.Preorder.Finite

/-!
# `p`-Systems of Finite Sets

A finite-set independence system `indep : Finset α → Prop` is a **`p`-system** if it contains `∅`,
is closed under subsets, and for every finite `Y`, any two maximal independent subsets `A, B` of
`Y` satisfy `|A| ≤ p * |B|` ([CalinescuChekuriPalVondrak2011], Section 1, following
[Jenkyns1976] and Korte–Hausmann). Matroids are exactly the `1`-systems among these, and the
intersection of `k ≥ 1` matroids is a `k`-system. `p`-systems are the constraint families for which
the Fisher–Nemhauser–Wolsey greedy algorithm achieves a `1/(p+1)` approximation for monotone
submodular maximization ([FisherNemhauserWolsey1978]; see
`Complexity.Algorithms.Lean.Submodular.MatroidGreedy`).

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.IsPSystem`: the `p`-system property of `indep : Finset α → Prop`.

## Main results

* `IsPSystem.card_le_mul_card_of_blocked`: the blocking form used by greedy analyses. If `S` and
  `T` are independent and every `t ∈ T \ S` is blocked (`¬ indep (insert t S)`), then
  `|T| ≤ p * |S|`.
* `isPSystem_iff_blocked`: the blocking form, together with `indep ∅` and heredity, characterizes
  `p`-systems.
* `isPSystem_matroid`: every Mathlib `Matroid` is a `1`-system on finite sets.
* `isPSystem_iInter_matroid`: the intersection of a nonempty finite family of matroids
  `M : ι → Matroid α` is a `Fintype.card ι`-system.

## References

* [CalinescuChekuriPalVondrak2011] Gruia Calinescu, Chandra Chekuri, Martin Pál, and Jan Vondrák,
  *Maximizing a Monotone Submodular Function Subject to a Matroid Constraint*, 2011.
* [FisherNemhauserWolsey1978] Marshall L. Fisher, George L. Nemhauser, and Laurence A. Wolsey,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—II*, 1978.
* [Jenkyns1976] Thomas A. Jenkyns, *The Efficacy of the "Greedy" Algorithm*, 1976.
-/

public section

namespace Cslib.Algorithms.Lean.Matroid

variable {α : Type*}

/-- `IsPSystem indep p`: the finite-set independence system `indep` contains `∅`, is closed under
subsets, and for every finite `Y`, any two maximal independent subsets `A, B ⊆ Y` satisfy
`A.card ≤ p * B.card` ([CalinescuChekuriPalVondrak2011], Section 1). -/
structure IsPSystem (indep : Finset α → Prop) (p : ℕ) : Prop where
  /-- The empty set is independent. -/
  indep_empty : indep ∅
  /-- Independence is inherited by subsets. -/
  indep_of_subset : ∀ ⦃A B : Finset α⦄, indep B → A ⊆ B → indep A
  /-- Maximal independent subsets of a common finite set have cardinality ratio at most `p`. -/
  card_le_mul_card : ∀ ⦃Y A B : Finset α⦄,
    Maximal (fun Z => Z ⊆ Y ∧ indep Z) A → Maximal (fun Z => Z ⊆ Y ∧ indep Z) B →
      A.card ≤ p * B.card

namespace IsPSystem

variable [DecidableEq α] {indep : Finset α → Prop} {p : ℕ}

/-- **Blocking form of the `p`-system bound.** If `S` and `T` are independent and every element of
`T \ S` is blocked by `S` (`¬ indep (insert t S)`), then `T.card ≤ p * S.card`: extend `T` to a
maximal independent subset of `S ∪ T`, of which `S` is also maximal. -/
theorem card_le_mul_card_of_blocked (h : IsPSystem indep p) {S T : Finset α}
    (hS : indep S) (hT : indep T) (hblock : ∀ t ∈ T, t ∉ S → ¬ indep (insert t S)) :
    T.card ≤ p * S.card := by
  classical
  set Y := S ∪ T
  have hSmax : Maximal (fun Z => Z ⊆ Y ∧ indep Z) S := by
    refine ⟨⟨Finset.subset_union_left, hS⟩, fun Z ⟨hZY, hZ⟩ hSZ => ?_⟩
    intro z hz
    by_contra hzS
    have hzT : z ∈ T := (Finset.mem_union.mp (hZY hz)).resolve_left hzS
    exact hblock z hzT hzS (h.indep_of_subset hZ (Finset.insert_subset hz hSZ))
  obtain ⟨A, hTA, hAmax⟩ := (Y.powerset.filter indep).exists_le_maximal
    (a := T) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.subset_union_right, hT⟩)
  have hAmax' : Maximal (fun Z => Z ⊆ Y ∧ indep Z) A := by
    simpa only [Finset.mem_filter, Finset.mem_powerset] using hAmax
  exact (Finset.card_le_card hTA).trans (h.card_le_mul_card hAmax' hSmax)

end IsPSystem

/-- The blocking form, together with `indep ∅` and heredity, characterizes `p`-systems. -/
theorem isPSystem_iff_blocked [DecidableEq α] {indep : Finset α → Prop} {p : ℕ} :
    IsPSystem indep p ↔ indep ∅ ∧ (∀ ⦃A B : Finset α⦄, indep B → A ⊆ B → indep A) ∧
      ∀ ⦃S T : Finset α⦄, indep S → indep T → (∀ t ∈ T, t ∉ S → ¬ indep (insert t S)) →
        T.card ≤ p * S.card := by
  refine ⟨fun h => ⟨h.indep_empty, h.indep_of_subset,
    fun _ _ hS hT hblock => h.card_le_mul_card_of_blocked hS hT hblock⟩, ?_⟩
  rintro ⟨hempty, hsub, hblock⟩
  refine ⟨hempty, hsub, fun Y A B hA hB => hblock hB.prop.2 hA.prop.2 fun t htA htB hins => ?_⟩
  exact htB (hB.2 ⟨Finset.insert_subset (hA.prop.1 htA) hB.prop.1, hins⟩
    (Finset.subset_insert t B) (Finset.mem_insert_self t B))

/-- Every Mathlib `Matroid` is a `1`-system on finite sets: maximal independent subsets of a finite
set are its bases, which are equicardinal. -/
theorem isPSystem_matroid (M : Matroid α) :
    IsPSystem (fun S : Finset α => M.Indep (S : Set α)) 1 := by
  classical
  refine isPSystem_iff_blocked.mpr ⟨by simp, fun A B hB hAB => hB.subset hAB, ?_⟩
  intro S T hS hT hblock
  rw [one_mul]
  by_contra hlt
  obtain ⟨e, heT, heS, hins⟩ := hS.augment_finset hT (not_le.mp hlt)
  exact hblock e heT heS (by simpa using hins)

/-- The intersection of a nonempty finite family of matroids `M : ι → Matroid α` is a
`Fintype.card ι`-system on finite sets ([FisherNemhauserWolsey1978];
[CalinescuChekuriPalVondrak2011], Section 1). Nonemptiness is necessary: the empty intersection
makes every set independent, which is not a `0`-system. -/
theorem isPSystem_iInter_matroid {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : ι → Matroid α) :
    IsPSystem (fun S : Finset α => ∀ i, (M i).Indep (S : Set α)) (Fintype.card ι) := by
  classical
  refine isPSystem_iff_blocked.mpr ⟨fun i => by simp, fun A B hB hAB i => (hB i).subset hAB, ?_⟩
  intro S T hS hT hblock
  have hwit : ∀ t, ∃ i : ι, t ∈ T → t ∉ S → ¬ (M i).Indep (insert t S : Finset α) := by
    intro t
    by_cases ht : t ∈ T ∧ t ∉ S
    · obtain ⟨i, hi⟩ := not_forall.mp (hblock t ht.1 ht.2)
      exact ⟨i, fun _ _ => hi⟩
    · exact ⟨Classical.arbitrary ι, fun htT htS => absurd ⟨htT, htS⟩ ht⟩
  choose g hg using hwit
  let Ti : ι → Finset α := fun i => T.filter fun t => t ∈ S ∨ g t = i
  have hTi : ∀ i, (Ti i).card ≤ S.card := by
    intro i
    have h1 := (isPSystem_matroid (M i)).card_le_mul_card_of_blocked (S := S) (T := Ti i) (hS i)
      ((hT i).subset (Finset.coe_subset.mpr (Finset.filter_subset _ T)))
      (fun t ht htS => by
        have ht' := Finset.mem_filter.mp ht
        have hgi : g t = i := ht'.2.resolve_left htS
        exact hgi ▸ hg t ht'.1 htS)
    simpa using h1
  have hcover : T ⊆ Finset.univ.biUnion Ti := by
    intro t ht
    refine Finset.mem_biUnion.mpr ⟨g t, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ht, Or.inr rfl⟩⟩
  calc T.card ≤ (Finset.univ.biUnion Ti).card := Finset.card_le_card hcover
    _ ≤ ∑ i, (Ti i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : ι, S.card := Finset.sum_le_sum fun i _ => hTi i
    _ = Fintype.card ι * S.card := by simp

end Cslib.Algorithms.Lean.Matroid
