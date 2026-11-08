/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ShortestPaths.Walk
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.BigOperators

/-!
# Shortest distances as (min,+) matrix powers

Over `MinTropical R` the matrix product is the (min,+) product, so `(W ^ m) i j` is the least
weight of a walk from `i` to `j` with exactly `m` edges, and `((1 + W) ^ k) i j` is the least
weight of a walk with at most `k` edges. Without negative cycles a shortest walk can be taken
without repeated vertices, hence with at most `card V - 1` edges: `(1 + W) ^ k` is the
shortest-distance matrix for every `k ≥ card V - 1`. The same powers detect negative cycles:
`W` has none iff the diagonal of `(1 + W) ^ card V` is at least the tropical one.

Without negative cycles `1 + W` is `withOneDiag W`, the weight matrix with zero-weight loops,
which is the initial matrix of Floyd–Warshall and of repeated squaring.

## Main definitions

* `Cslib.Algorithms.ShortestPaths.withOneDiag`: `W` with every diagonal entry replaced by `1`.

## Main results

* `Cslib.Algorithms.ShortestPaths.pow_apply_le_walkWeight`,
  `Cslib.Algorithms.ShortestPaths.exists_walk_of_pow`: `(W ^ m) i j` is the least weight of a
  walk from `i` to `j` with `m` edges.
* `Cslib.Algorithms.ShortestPaths.one_add_pow_apply_le`,
  `Cslib.Algorithms.ShortestPaths.exists_walk_of_one_add_pow`: the same for `(1 + W) ^ k` and
  walks with at most `k` edges.
* `Cslib.Algorithms.ShortestPaths.isShortestDistances_one_add_pow`: without negative cycles,
  `(1 + W) ^ k` is the shortest-distance matrix for every `k ≥ card V - 1`.
* `Cslib.Algorithms.ShortestPaths.isShortestDistances_withOneDiag_pow`: the same for
  `withOneDiag W`.
* `Cslib.Algorithms.ShortestPaths.noNegCycle_iff_one_le_one_add_pow_diag`: negative-cycle
  detection, and a `DecidablePred NoNegCycle` instance.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 25.1.
-/

public section

open MinTropical

namespace Cslib.Algorithms.ShortestPaths

variable {R : Type*} [LinearOrderedAddCommMonoidWithTop R] {V : Type*}

/-- `W` with every diagonal entry replaced by `1`, the tropical `0`: the matrix of `W` with a
zero-weight loop at every vertex. -/
@[expose] def withOneDiag [DecidableEq V] {α : Type*} [One α] (W : Matrix V V α) : Matrix V V α :=
  fun i j => if i = j then 1 else W i j

/-- Without negative cycles, adding the tropical identity replaces the diagonal by `1`. -/
theorem one_add_eq_withOneDiag [DecidableEq V] {W : Matrix V V (MinTropical R)}
    (hW : NoNegCycle W) : 1 + W = withOneDiag W := by
  ext i j
  rw [Matrix.add_apply]
  by_cases h : i = j
  · subst h
    simp only [withOneDiag, Matrix.one_apply_eq, ↓reduceIte]
    exact add_eq_left (by simpa using hW i [i] rfl)
  · simp only [withOneDiag, Matrix.one_apply_ne h, h, ↓reduceIte, zero_add]

variable [Fintype V] [DecidableEq V]

/-- `(W ^ m) i j` is at most the weight of every walk from `i` to `j` with `m` edges. -/
theorem pow_apply_le_walkWeight (W : Matrix V V (MinTropical R)) :
    ∀ (i : V) (l : List V), (W ^ l.length) i (l.getLastD i) ≤ walkWeight W i l
  | i, [] => by simp
  | i, v :: l => by
    rw [List.length_cons, pow_succ', Matrix.mul_apply, List.getLastD_cons, walkWeight_cons]
    exact (sum_le_of_mem _ (Finset.mem_univ v)).trans
      (mul_le_mul_right (pow_apply_le_walkWeight W v l) _)

/-- `(W ^ m) i j` is `0` or the weight of a walk from `i` to `j` with `m` edges. -/
theorem exists_walk_of_pow (W : Matrix V V (MinTropical R)) :
    ∀ (m : ℕ) (i j : V), (W ^ m) i j = 0 ∨
      ∃ l : List V, l.length = m ∧ l.getLastD i = j ∧ walkWeight W i l = (W ^ m) i j
  | 0, i, j => by
    by_cases h : i = j
    · subst h
      exact Or.inr ⟨[], rfl, rfl, by simp⟩
    · left
      simp [h]
  | m + 1, i, j => by
    rw [pow_succ', Matrix.mul_apply]
    obtain ⟨v, -, hv⟩ :=
      exists_sum_eq (Finset.univ_nonempty_iff.2 ⟨i⟩) (fun v => W i v * (W ^ m) v j)
    rw [hv]
    rcases exists_walk_of_pow W m v j with h0 | ⟨l, hl, hlast, hw⟩
    · left
      rw [h0, mul_zero]
    · right
      exact ⟨v :: l, by simp [hl], by rw [List.getLastD_cons, hlast], by rw [walkWeight_cons, hw]⟩

/-- `((1 + W) ^ k) i j` is at most the weight of every walk from `i` to `j` with at most `k`
edges. -/
theorem one_add_pow_apply_le (W : Matrix V V (MinTropical R)) :
    ∀ (k : ℕ) (i : V) (l : List V), l.length ≤ k →
      ((1 + W) ^ k) i (l.getLastD i) ≤ walkWeight W i l
  | 0, i, [], _ => by simp
  | 0, _, _ :: _, h => by simp at h
  | k + 1, i, [], _ => by
    rw [pow_succ', Matrix.mul_apply]
    refine (sum_le_of_mem _ (Finset.mem_univ i)).trans ?_
    have h1 : (1 + W) i i ≤ 1 := by
      rw [Matrix.add_apply, Matrix.one_apply_eq]
      exact add_le_left _ _
    have h2 := one_add_pow_apply_le W k i [] (Nat.zero_le _)
    calc (1 + W) i i * ((1 + W) ^ k) i ([].getLastD i) ≤ 1 * walkWeight W i [] :=
          mul_le_mul' h1 h2
      _ = walkWeight W i [] := one_mul _
  | k + 1, i, v :: l, h => by
    rw [pow_succ', Matrix.mul_apply, List.getLastD_cons, walkWeight_cons]
    refine (sum_le_of_mem _ (Finset.mem_univ v)).trans ?_
    have h1 : (1 + W) i v ≤ W i v := by
      rw [Matrix.add_apply]
      exact add_le_right _ _
    exact mul_le_mul' h1
      (one_add_pow_apply_le W k v l (by simp only [List.length_cons] at h; omega))

/-- `((1 + W) ^ k) i j` is `0` or the weight of a walk from `i` to `j` with at most `k` edges. -/
theorem exists_walk_of_one_add_pow (W : Matrix V V (MinTropical R)) :
    ∀ (k : ℕ) (i j : V), ((1 + W) ^ k) i j = 0 ∨
      ∃ l : List V, l.length ≤ k ∧ l.getLastD i = j ∧ walkWeight W i l = ((1 + W) ^ k) i j
  | 0, i, j => by
    by_cases h : i = j
    · subst h
      exact Or.inr ⟨[], le_rfl, rfl, by simp⟩
    · left
      simp [h]
  | k + 1, i, j => by
    rw [pow_succ', Matrix.mul_apply]
    obtain ⟨u, -, hu⟩ := exists_sum_eq (Finset.univ_nonempty_iff.2 ⟨i⟩)
      (fun u => (1 + W) i u * ((1 + W) ^ k) u j)
    rw [hu, Matrix.add_apply]
    rcases add_eq_or ((1 : Matrix V V (MinTropical R)) i u) (W i u) with h | h <;> rw [h]
    · by_cases hiu : i = u
      · subst hiu
        rw [Matrix.one_apply_eq, one_mul]
        rcases exists_walk_of_one_add_pow W k i j with h0 | ⟨l, hl, hlast, hw⟩
        · exact Or.inl h0
        · exact Or.inr ⟨l, by omega, hlast, hw⟩
      · left
        rw [Matrix.one_apply_ne hiu, zero_mul]
    · rcases exists_walk_of_one_add_pow W k u j with h0 | ⟨l, hl, hlast, hw⟩
      · left
        rw [h0, mul_zero]
      · right
        exact ⟨u :: l, by simp only [List.length_cons]; omega, by rw [List.getLastD_cons, hlast],
          by rw [walkWeight_cons, hw]⟩

variable {W : Matrix V V (MinTropical R)}

/-- **Shortest distances as tropical powers.** Without negative cycles, `(1 + W) ^ k` is the
shortest-distance matrix of `W` for every `k ≥ card V - 1`. -/
theorem isShortestDistances_one_add_pow (hW : NoNegCycle W) {k : ℕ}
    (hk : Fintype.card V - 1 ≤ k) : IsShortestDistances W ((1 + W) ^ k) := by
  refine isShortestDistances_of_sound_complete hW (fun i j => ?_) (fun i l hnd => ?_)
  · rcases exists_walk_of_one_add_pow W k i j with h | ⟨l, -, hl, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨l, hl, hw⟩
  · apply one_add_pow_apply_le
    have := hnd.length_le_card
    simp only [List.length_cons] at this
    omega

/-- Without negative cycles the powers of `1 + W` are constant from `card V - 1` on. -/
theorem one_add_pow_eq_of_le (hW : NoNegCycle W) {k : ℕ} (hk : Fintype.card V - 1 ≤ k) :
    (1 + W) ^ k = (1 + W) ^ (Fintype.card V - 1) :=
  (isShortestDistances_one_add_pow hW hk).unique (isShortestDistances_one_add_pow hW le_rfl)

/-- Without negative cycles, `withOneDiag W ^ k` is the shortest-distance matrix of `W` for every
`k ≥ card V - 1`. -/
theorem isShortestDistances_withOneDiag_pow (hW : NoNegCycle W) {k : ℕ}
    (hk : Fintype.card V - 1 ≤ k) : IsShortestDistances W (withOneDiag W ^ k) := by
  rw [← one_add_eq_withOneDiag hW]
  exact isShortestDistances_one_add_pow hW hk

/-- **Negative-cycle detection.** `W` has no negative cycles iff every diagonal entry of
`(1 + W) ^ card V` is at least `1`, the tropical `0`. -/
theorem noNegCycle_iff_one_le_one_add_pow_diag :
    NoNegCycle W ↔ ∀ i, 1 ≤ ((1 + W) ^ Fintype.card V) i i := by
  constructor
  · intro hW i
    rcases exists_walk_of_one_add_pow W (Fintype.card V) i i with h0 | ⟨l, -, hl, hw⟩
    · rw [h0]
      exact le_zero _
    · rw [← hw]
      exact hW i l hl
  · intro h
    refine noNegCycle_of_forall_length_le fun i l hlen hl => ?_
    have := one_add_pow_apply_le W _ i l hlen
    rw [hl] at this
    exact (h i).trans this

instance [DecidableLE R] : DecidablePred (NoNegCycle (R := R) (V := V)) := fun _ =>
  decidable_of_iff _ noNegCycle_iff_one_le_one_add_pow_diag.symm

end Cslib.Algorithms.ShortestPaths
