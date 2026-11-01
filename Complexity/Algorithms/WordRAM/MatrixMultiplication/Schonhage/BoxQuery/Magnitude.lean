/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Values
public import Complexity.Foundations.Data.Int.Order

/-!
# Signed envelopes for sparse native query accumulators

Each visited term is a direct leaf product or one stored box value. Its magnitude is
at most `10^L*A*B`. The original encoding span also bounds the number of visited leaves,
so every partial sum fits a single `10^(2L)*A*B` envelope. Operand envelopes are retained
separately when one input array vanishes. These are original resource estimates for
the native traversal, with no assumed execution or intermediate-fit certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every query summand obeys the original full-depth box magnitude envelope. -/
theorem natAbs_leafQueryValue_le {L A B : ℕ} (m t : ℕ) (η : OutStr L)
    (a b : Leaf L → ℤ) (ha : ∀ τ, (a τ).natAbs ≤ A)
    (hb : ∀ τ, (b τ).natAbs ≤ B) (τ : Leaf L) :
    (leafQueryValue m t η a b τ).natAbs ≤ 10 ^ L * (A * B) := by
  unfold leafQueryValue
  split
  · rw [Int.natAbs_mul]
    exact (Nat.mul_le_mul (ha τ) (hb τ)).trans (Nat.le_mul_of_pos_left _ (by positivity))
  · unfold BoxTable.slotValue
    have he : BoxTable.recordStars L (BoxTable.cubeSlot (starBelow η τ)) ≤ L := by
      rw [BoxTable.cubeSlot, BoxTable.recordStars_slot]
      exact (card_le_univ _).trans_eq (by simp)
    exact (BoxTable.natAbs_boxValue_le a b ha hb _ _).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) he))

/-- Bound the sum over any finite collection, without a sign or cancellation assumption. -/
theorem natAbs_sum_leafQueryValue_le {L A B : ℕ} (m t : ℕ) (η : OutStr L)
    (a b : Leaf L → ℤ) (ha : ∀ τ, (a τ).natAbs ≤ A)
    (hb : ∀ τ, (b τ).natAbs ≤ B) (S : Finset (Leaf L)) :
    (∑ τ ∈ S, leafQueryValue m t η a b τ).natAbs ≤ S.card * (10 ^ L * (A * B)) := by
  calc
    _ ≤ ∑ τ ∈ S, (leafQueryValue m t η a b τ).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _τ ∈ S, 10 ^ L * (A * B) :=
      sum_le_sum fun τ _ => natAbs_leafQueryValue_le m t η a b ha hb τ
    _ = _ := by simp

/-- Any partial finite query set has a bound depending only on the original input arrays. -/
theorem natAbs_sum_querySubset_le {L m A B : ℕ} (t : ℕ) (η : OutStr L)
    (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (S : Finset (Leaf L)) (hS : S ⊆ queryLeaves m t η) :
    (∑ τ ∈ S, leafQueryValue m t η a b τ).natAbs ≤ 10 ^ (2 * L) * (A * B) := by
  have hc := (card_le_card hS).trans (card_queryLeaves_le_span t η hη)
  calc
    _ ≤ S.card * (10 ^ L * (A * B)) := natAbs_sum_leafQueryValue_le m t η a b ha hb S
    _ ≤ 10 ^ L * (10 ^ L * (A * B)) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [show 2 * L = L + L by omega, pow_add]; ring

/-- The same envelope covers every prefix of any visited list with at most one span of entries.
The native worklist proves the length bound; no intermediate sum fit is supplied. -/
theorem natAbs_sum_take_leafQueryValue_le {L A B : ℕ} (m t : ℕ) (η : OutStr L)
    (a b : Leaf L → ℤ) (ha : ∀ τ, (a τ).natAbs ≤ A)
    (hb : ∀ τ, (b τ).natAbs ≤ B) (xs : List (Leaf L)) (hx : xs.length ≤ 10 ^ L) (k : ℕ) :
    ((xs.map (leafQueryValue m t η a b)).take k).sum.natAbs ≤ 10 ^ (2 * L) * (A * B) := by
  have hterms : ∀ z ∈ xs.map (leafQueryValue m t η a b), z.natAbs ≤ 10 ^ L * (A * B) := by
    intro z hz
    obtain ⟨τ, _, rfl⟩ := List.mem_map.mp hz
    exact natAbs_leafQueryValue_le m t η a b ha hb τ
  have hlen : (xs.map (leafQueryValue m t η a b)).length ≤ 10 ^ L := by
    simpa only [List.length_map] using hx
  calc
    _ ≤ 10 ^ L * (10 ^ L * (A * B)) :=
      List.natAbs_sum_take_le_of_length_le hlen hterms k
    _ = _ := by rw [show 2 * L = L + L by omega, pow_add]; ring

/-- Include each operand separately, even if the other input is zero. -/
@[expose] def magnitudeBound (L A B : ℕ) : ℕ := A + B + 10 ^ (2 * L) * (A * B)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
