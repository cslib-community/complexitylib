/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingDeletion

/-!
# Immediate survival in counting sparsification

Appendix A.1, Lemma A.1 [OpenAI2026ETH] shows that the heart and petals are new and survive
immediate reduction. For the B-child, nontautology prevents its additional negated-heart units
from subsuming a petal. This module proves that fact for the actual `countingChild`, and preserves
the pointwise absence of complementary literals along actual counting paths.

The local result needs only a heavy heart, positive thresholds and a reduced nontautological
parent; neither priority in `Choice` is needed. At width at least two, the full counting payload
consists of the heart or petals, so all its clauses survive and are absent from the current node.
The root-subclause invariant additionally excludes the root along a path. The resulting equality
identifies these insertion events with new clauses present in the next node. It does not sum
events or prove the complete Appendix A.2 recurrence, depth, leaf count or native runtime.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.nontautological_countingChild`: preservation at one step.
* `Cslib.Logic.PL.ClauseSet.Sparsification.nontautological_counting_node`: path preservation.
* `Cslib.Logic.PL.ClauseSet.Sparsification.intro_subset_countingChild`: heart and petal survival.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingIntro_filter_eq_node_sdiff`: higher-width
  insertion events are exactly the new marked clauses present in the next node.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.1, Lemma A.1][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- A proper heavy-heart step preserves the absence of complementary literals within each
clause. This concerns clauses individually, not consistency between different unit clauses. -/
theorem nontautological_countingChild {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (h : Heavy θ ψ c H) (b : Bool) :
    ∀ C ∈ countingChild ψ c H b, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  intro C hC l hl hneg
  rw [countingChild_eq_reduce_union] at hC
  rcases mem_union.mp (reduce_subset _ hC) with hC | hC
  · exact hnt C hC l hl hneg
  · have hcore : C ∈ intro ψ c H b ∨ C ∈ negatedHeartUnits H := by
      cases b with
      | false => exact Or.inl hC
      | true => exact mem_union.mp hC
    rcases hcore with hcore | hunit
    · obtain ⟨D, hD, hCD⟩ := exists_flower_ssuperset hθ h hcore
      exact hnt D (flower_subset _ _ _ hD) l (hCD.subset hl) (hCD.subset hneg)
    · obtain ⟨a, -, rfl⟩ := mem_image.mp hunit
      rw [mem_singleton] at hl hneg
      subst l
      rcases a with ⟨v, p⟩
      cases p <;> simp [Std.Sat.Literal.negate] at hneg

/-- Nontautology at the root is preserved along actual counting children. There is no finite
ambient variable type or satisfiability premise, and heaviness suffices in place of `Choice`. -/
theorem nontautological_counting_node {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    {t : ℕ} (ht : t ≤ N) :
    ∀ C ∈ ψ t, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  induction t with
  | zero => exact hnt
  | succ t ih =>
    rw [hstep t (by omega)]
    exact nontautological_countingChild hθ (ih (by omega)) (hheavy t (by omega)) (b t)

/-- Every heart or petal survives immediate counting reduction. This includes unit petals but
does not refer to the B-child's additional negated-heart units. Nontautology prevents those units
from subsuming any petal. -/
theorem intro_subset_countingChild {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} (hred : Reduced ψ)
    (hnt : ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    (h : Heavy θ ψ c H) (b : Bool) : intro ψ c H b ⊆ countingChild ψ c H b := by
  intro a ha
  rw [countingChild_eq_reduce_union, mem_reduce]
  have haI : a ∈ countingIntro ψ c H b := by
    cases b with
    | false => exact ha
    | true => exact mem_union_left _ ha
  refine ⟨mem_union_right _ haI, fun D hD hDa => ?_⟩
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ h ha
  rcases mem_union.mp hD with hD | hD
  · exact hred C (flower_subset _ _ _ hC) D hD (hDa.trans haC)
  · cases b with
    | false =>
      have haH : a = H := mem_singleton.mp ha
      have hDH : D = H := mem_singleton.mp hD
      exact (ne_of_ssubset hDa) (hDH.trans haH.symm)
    | true =>
      rcases mem_union.mp hD with hD | hD
      · have hlt := card_lt_card hDa
        rw [card_of_mem_petals hD, card_of_mem_petals ha] at hlt
        exact lt_irrefl _ hlt
      · obtain ⟨l, hl, rfl⟩ := mem_image.mp hD
        exact hnt C (flower_subset _ _ _ hC) l ((mem_flower.mp hC).2.2 hl)
          (haC.subset (hDa.subset (mem_singleton_self _)))

/-- Every heart or petal is absent from a reduced parent. This newness fact does not require
nontautology; the strict flower superset already rules out membership in the old antichain. -/
theorem notMem_of_mem_intro {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} (hred : Reduced ψ)
    (h : Heavy θ ψ c H) {b : Bool} {a : Finset (Literal V)}
    (ha : a ∈ intro ψ c H b) : a ∉ ψ := by
  obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ h ha
  exact fun haψ => hred C (flower_subset _ _ _ hC) a haψ haC

/-- At width at least two, the counting payload contains only the heart or petals.
The B-child's negated-heart units have width one and are excluded by this hypothesis. -/
theorem mem_intro_of_mem_countingIntro {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} {b : Bool} {a : Finset (Literal V)}
    (ha : a ∈ countingIntro ψ c H b) (ha2 : 2 ≤ a.card) : a ∈ intro ψ c H b := by
  cases b with
  | false => exact ha
  | true =>
    rcases mem_union.mp ha with ha | ha
    · exact ha
    · obtain ⟨l, -, rfl⟩ := mem_image.mp ha
      simp only [card_singleton] at ha2
      omega

/-- Along an actual counting path, every width-`j ≥ 2` payload clause survives and is absent
from both the current node and the root. Thus its insertion event is exactly a new marked clause
present in the next node. No survival or insertion-balance premise is assumed. -/
theorem countingIntro_filter_eq_node_sdiff {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (hnt : ∀ C ∈ ψ 0, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C)
    {m : ℕ} (hm : m < N) {j : ℕ} (hj : 2 ≤ j) :
    (countingIntro (ψ m) (c m) (H m) (b m)).filter (·.card = j) =
      (ψ (m + 1) \ (ψ m ∪ ψ 0)).filter (·.card = j) := by
  have hredm : Reduced (ψ m) := by
    cases m with
    | zero => exact hred
    | succ m =>
      rw [hstep m (by omega), countingChild_eq_reduce_union]
      exact reduced_reduce _
  have hntm := nontautological_counting_node hθ N ψ c H b hstep hheavy hnt hm.le
  ext a
  simp only [mem_filter, mem_sdiff, mem_union]
  constructor
  · rintro ⟨ha, haj⟩
    have hai := mem_intro_of_mem_countingIntro ha (haj ▸ hj)
    have haψ := notMem_of_mem_intro hθ hredm (hheavy m hm) hai
    have haroot : a ∉ ψ 0 := by
      intro ha0
      obtain ⟨D, hD, hDa⟩ := exists_mem_counting_node_subset N ψ c H b hstep hm.le ha0
      obtain ⟨C, hC, haC⟩ := exists_flower_ssuperset hθ (hheavy m hm) hai
      exact hredm C (flower_subset _ _ _ hC) D hD
        (Finset.ssubset_of_subset_of_ssubset hDa haC)
    refine ⟨⟨?_, fun h => h.elim haψ haroot⟩, haj⟩
    rw [hstep m hm]
    exact intro_subset_countingChild hθ hredm hntm (hheavy m hm) (b m) hai
  · rintro ⟨⟨ha, hnot⟩, haj⟩
    rw [hstep m hm, countingChild_eq_reduce_union] at ha
    exact ⟨(mem_union.mp (reduce_subset _ ha)).resolve_left (fun h => hnot (Or.inl h)), haj⟩

end Cslib.Logic.PL.ClauseSet.Sparsification
