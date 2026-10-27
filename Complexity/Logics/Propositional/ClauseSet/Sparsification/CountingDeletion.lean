/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingOccurrences
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# Charging deleted marked clauses to actual counting insertions

The deletion-charge argument of Appendix A.2, Lemma A.3 and (A.3) [OpenAI2026ETH] assigns
a removed marked width-`j` clause to a new strict subclause inserted in that step.
The present-clause bound supplies at most `2 * θ (j - i)` recipients for a width-`i` insertion.

Here the donor is proved absent from both the current node and the root. Every root clause has a
current subclause, directly from the actual reduction steps; a root donor would contradict current
reducedness. This is not the decision-path `Refines` property. The actual counting payload includes
the B-child's negated-heart units.

This bounds deletion of clauses present before one step. It does not assert immediate survival of
new higher-width payload clauses, nor the complete insertion recurrence or a depth/leaf/runtime
bound. Nontautology is not needed for this one-step old-clause charge; its role in immediate
survival and the later insertion-event balance remains separate.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_mem_counting_node_subset`: root witnesses persist.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_counting_deleted_marked_le`: deletion charge.
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- Every root clause contains a clause of each later node of an actual counting path.
This direction of containment holds for reduction after additions, including negated units. -/
theorem exists_mem_counting_node_subset
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    {t : ℕ} (ht : t ≤ N) {C : Finset (Literal V)} (hC : C ∈ ψ 0) :
    ∃ D ∈ ψ t, D ⊆ C := by
  suffices ∀ t, t ≤ N → ∃ D ∈ ψ t, D ⊆ C from this t ht
  intro t
  induction t with
  | zero => exact fun _ => ⟨C, hC, subset_rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨D, hD, hDC⟩ := ih (by omega)
    rw [hstep t (by omega), countingChild_eq_reduce_union]
    obtain ⟨E, hE, hED⟩ := exists_mem_reduce_subset
      (ψ := ψ t ∪ countingIntro (ψ t) (c t) (H t) (b t)) (mem_union_left _ hD)
    exact ⟨E, hE, hED.trans hDC⟩

/-- The width-`j` marked clauses deleted at one actual counting step can be charged to that step's
new marked insertion events of smaller width, with the source's `2 * θ (j - i)` charge bound.

The occurrence bound is derived from the actual path and both `Choice` priorities, not supplied
as a hypothesis. The insertion batch excludes clauses in the current node OR the root. No finite
ambient variable type, model count or native resource bound is assumed. -/
theorem card_counting_deleted_marked_le {θ : ℕ → ℕ} (hθ : ∀ r, 1 ≤ θ r)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    {m : ℕ} (hm : m < N) (j : ℕ) :
    ((ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ C ∉ ψ (m + 1)).card ≤
      ∑ i ∈ Ico 1 j, 2 * θ (j - i) *
        (((countingIntro (ψ m) (c m) (H m) (b m)) \ (ψ m ∪ ψ 0)).filter
          fun D => D.card = i).card := by
  let I := countingIntro (ψ m) (c m) (H m) (b m) \ (ψ m ∪ ψ 0)
  set E := (ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ C ∉ ψ (m + 1)
  change E.card ≤ ∑ i ∈ Ico 1 j, 2 * θ (j - i) * (I.filter fun D => D.card = i).card
  have hredm : Reduced (ψ m) := by
    cases m with
    | zero => exact hred
    | succ m =>
      rw [hstep m (by omega), countingChild_eq_reduce_union]
      exact reduced_reduce _
  have hcover : E ⊆ (I.filter (·.card < j)).biUnion fun D =>
      (ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ D ⊆ C := by
    intro C hC
    obtain ⟨hCψ, hCroot, hCj, hCgone⟩ := mem_filter.mp hC
    rw [hstep m hm, countingChild_eq_reduce_union] at hCgone
    obtain ⟨D, hD, hDC⟩ := exists_ssubset_of_notMem_reduce hredm hCψ hCgone
    have hDψ : D ∉ ψ m := fun h => hredm C hCψ D h hDC
    have hDroot : D ∉ ψ 0 := by
      intro hD0
      obtain ⟨F, hF, hFD⟩ := exists_mem_counting_node_subset N ψ c H b hstep hm.le hD0
      exact hredm C hCψ F hF (Finset.ssubset_of_subset_of_ssubset hFD hDC)
    have hDI : D ∈ I := by
      refine mem_sdiff.mpr ⟨hD, ?_⟩
      exact fun h => (mem_union.mp h).elim hDψ hDroot
    refine mem_biUnion.mpr ⟨D, mem_filter.mpr ⟨hDI, ?_⟩, ?_⟩
    · exact hCj ▸ card_lt_card hDC
    · exact mem_filter.mpr ⟨hCψ, hCroot, hCj, hDC.subset⟩
  have hmaps : ∀ D ∈ I.filter (·.card < j), D.card ∈ Ico 1 j := by
    intro D hD
    obtain ⟨hDI, hDj⟩ := mem_filter.mp hD
    have hDpos := countingIntro_nonempty (hchoice m hm).1.1 (hchoice m hm).1.2.1
      (mem_sdiff.mp hDI).1
    rw [← card_pos] at hDpos
    exact mem_Ico.mpr ⟨by omega, hDj⟩
  have hsum : (∑ D ∈ I.filter (·.card < j),
      ((ψ m).filter fun C => C ∉ ψ 0 ∧ C.card = j ∧ D ⊆ C).card) ≤
      ∑ i ∈ Ico 1 j, 2 * θ (j - i) * (I.filter fun D => D.card = i).card := by
    calc
      _ ≤ ∑ D ∈ I.filter (·.card < j), 2 * θ (j - D.card) := by
        refine sum_le_sum fun D hD => ?_
        exact (card_counting_newContaining_lt hθ N ψ c H b hstep hchoice hm.le
          (mem_Ico.mp (hmaps D hD)).1 (mem_filter.mp hD).2).le
      _ = ∑ i ∈ Ico 1 j, ∑ D ∈ (I.filter (·.card < j)).filter (·.card = i),
          2 * θ (j - i) := (sum_fiberwise_of_maps_to' hmaps fun i => 2 * θ (j - i)).symm
      _ = ∑ i ∈ Ico 1 j, 2 * θ (j - i) * (I.filter fun D => D.card = i).card := by
        refine sum_congr rfl fun i hi => ?_
        have hij := (mem_Ico.mp hi).2
        rw [sum_const, smul_eq_mul, mul_comm]
        congr 2
        ext D
        simp only [mem_filter]
        constructor
        · rintro ⟨⟨hDI, -⟩, hDi⟩
          exact ⟨hDI, hDi⟩
        · rintro ⟨hDI, hDi⟩
          exact ⟨⟨hDI, hDi ▸ hij⟩, hDi⟩
  exact (card_le_card hcover).trans (card_biUnion_le.trans hsum)

end Cslib.Logic.PL.ClauseSet.Sparsification
