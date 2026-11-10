/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedRow
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Global weighted upper clauses

Global deduplication in [ChenJiangZhu2027], Theorem 7.1, proof following
(25), PDF p. 24. Clauses are identified as finite sets of signed literals
before being listed again. Thus permutations as well as repeated clauses disappear.
The binomial bound uses the larger universe of all signed literals; it is independent
of the number of rows and has degree `d + 1` for fixed `d`.
This is a noncomputable finite listing, not an encoded polynomial-time compiler.
-/

public noncomputable section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators

variable {V : Type*} [DecidableEq V] {d h : ℕ}

/-- All upper clauses, identified independently of their literal ordering and source row. -/
@[expose] def upperKeys (R : Fin (h + 1) → Row V d) : Finset (Finset (Literal V)) :=
  (base R).toFinset.image List.toFinset

/-- A single global list of upper clauses. -/
@[expose] def globalBase (R : Fin (h + 1) → Row V d) : CNF V :=
  (upperKeys R).toList.map Finset.toList

/-- Deduplication preserves the base on every assignment. -/
theorem globalBase_eval (R : Fin (h + 1) → Row V d) (σ : V → Bool) :
    (globalBase R).eval σ = (base R).eval σ := by
  apply Bool.eq_iff_iff.mpr
  simp [globalBase, upperKeys, CNF.eval_eq_true_iff, Clause.eval_eq_true_iff]

/-- The deduplicated base enforces all row upper bounds. -/
theorem globalBase_upper_eval (R : Fin (h + 1) → Row V d) (σ : V → Bool) :
    (globalBase R).eval σ = true ↔ ∀ j, (R j).value σ ≤ (R j).demand := by
  rw [globalBase_eval]
  have hb : (base R).eval σ = true ↔ ∀ j, (R j).upper.eval σ = true := by
    simp only [base, CNF.eval_eq_true_iff, List.mem_flatMap, List.mem_finRange, true_and,
      forall_exists_index]
    exact forall_comm
  rw [hb]
  exact forall_congr' fun j => upper_eval (R j) σ

/-- Every retained clause still has the row-local width bound. -/
theorem globalBase_width (R : Fin (h + 1) → Row V d) (c : Clause V)
    (hc : c ∈ globalBase R) : c.length ≤ d + 1 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hs)
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp ha)
  simpa using (List.toFinset_card_le a).trans (upper_width (R j) a hj)

/-- Global upper-clause count with no multiplier for the number of retained rows. -/
theorem globalBase_length [Fintype V] (R : Fin (h + 1) → Row V d) :
    (globalBase R).length ≤
      ∑ k ∈ Finset.range (d + 2), (2 * Fintype.card V).choose k := by
  classical
  let U : Finset (Finset (Literal V)) :=
    (Finset.range (d + 2)).biUnion fun k => (Finset.univ : Finset (Literal V)).powersetCard k
  have hs : upperKeys R ⊆ U := by
    intro s hs
    have hw : s.card ≤ d + 1 := by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp ha)
      exact (List.toFinset_card_le a).trans (upper_width (R j) a hj)
    exact Finset.mem_biUnion.mpr ⟨s.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, rfl⟩⟩
  calc
    _ = (upperKeys R).card := by simp [globalBase]
    _ ≤ U.card := Finset.card_le_card hs
    _ ≤ ∑ k ∈ Finset.range (d + 2),
        ((Finset.univ : Finset (Literal V)).powersetCard k).card := Finset.card_biUnion_le
    _ = _ := by simp [Literal, Nat.mul_comm]

/-- Explicit polynomial domination of the signed-subset budget, including zero variables. -/
theorem globalBase_polynomial [Fintype V] (R : Fin (h + 1) → Row V d) :
    (globalBase R).length ≤ (d + 2) * (2 * Fintype.card V + 1) ^ (d + 1) := by
  apply (globalBase_length R).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range (d + 2), (2 * Fintype.card V + 1) ^ (d + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (by omega : 2 * Fintype.card V ≤
          2 * Fintype.card V + 1) k).trans
          (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hk; omega)))
    _ = _ := by simp

/-- Ordinary two-boundary queries with a globally deduplicated upper base. -/
@[expose] def globalQuery (R : Fin (h + 1) → Row V d) (β : Bool) : CNF (V ⊕ Fin h) :=
  TwoBoundary.query (globalBase R) h (fun j => (R j).attainment) β

/-- Exact count recovery uses the existing ordinary-query semantics. -/
theorem global_counting_identity [Fintype V] (R : Fin (h + 1) → Row V d) :
    Fintype.card {σ : V → Bool // ∀ j, (R j).value σ = (R j).demand} =
      Fintype.card {σ : V ⊕ Fin h → Bool // (globalQuery R false).eval σ = true} -
      Fintype.card {σ : V ⊕ Fin h → Bool // (globalQuery R true).eval σ = true} := by
  classical
  calc
    _ = Fintype.card {σ : V → Bool // (globalBase R).eval σ = true ∧
        ∀ j, (R j).attainment.eval σ = true} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro σ
      rw [globalBase_eval]
      exact (base_attainment_eval R σ).symm
    _ = _ := TwoBoundary.counting_identity (globalBase R) (fun j => (R j).attainment)

/-- Global deduplication retains width `d + 2`. -/
theorem globalQuery_width (R : Fin (h + 1) → Row V d) (β : Bool)
    (c : Clause (V ⊕ Fin h)) (hc : c ∈ globalQuery R β) : c.length ≤ d + 2 := by
  have hw := TwoBoundary.query_width (globalBase R) (fun j => (R j).attainment)
    (d + 1) d (globalBase_width R) (fun j t ht => attainment_width (R j) t ht) β c hc
  simpa using hw

/-- A per-query binomial budget: only attainment terms carry the row factor. -/
theorem globalQuery_length [Fintype V] (R : Fin (h + 1) → Row V d) (β : Bool) :
    (globalQuery R β).length ≤
      (∑ k ∈ Finset.range (d + 2), (2 * Fintype.card V).choose k) +
        2 * ∑ j : Fin (h + 1),
          (∑ k ∈ Finset.range (d + 1), (R j).support.card.choose k) := by
  exact (TwoBoundary.query_length (globalBase R) (fun j => (R j).attainment) β).trans
    (Nat.add_le_add (globalBase_length R)
      (Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun j _ => attainment_length (R j))))

/-- A concrete polynomial query budget; the upper-base term has no row multiplier. -/
theorem globalQuery_polynomial [Fintype V] (R : Fin (h + 1) → Row V d) (β : Bool) :
    (globalQuery R β).length ≤
      (d + 2) * (2 * Fintype.card V + 1) ^ (d + 1) +
        2 * ((h + 1) * ((d + 1) * (Fintype.card V + 1) ^ d)) := by
  have ht (j : Fin (h + 1)) :
      (R j).attainment.length ≤ (d + 1) * (Fintype.card V + 1) ^ d := by
    apply (attainment_length (R j)).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range (d + 1), (Fintype.card V + 1) ^ d := by
        apply Finset.sum_le_sum
        intro k hk
        exact (Nat.choose_le_pow _ _).trans
          ((Nat.pow_le_pow_left ((Finset.card_le_univ _).trans (by omega)) k).trans
            (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hk; omega)))
      _ = _ := by simp
  apply (TwoBoundary.query_length (globalBase R) (fun j => (R j).attainment) β).trans
  apply Nat.add_le_add (globalBase_polynomial R)
  apply Nat.mul_le_mul_left
  simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)

end Cslib.Logic.PL.WeightedRow
