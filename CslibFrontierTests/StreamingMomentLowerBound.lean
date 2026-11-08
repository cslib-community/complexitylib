/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Streaming.MomentLowerBound
public import CslibFrontier.Foundations.Data.Code.HammingBound

/-!
# Unit tests for the linear-memory lower bounds for frequency moments

Verifies non-vacuity and concrete behavior of:
1. `Cslib.Streaming.freqMoment_graphStream_append_eq` on a concrete pair of words, and the failure
   of `Cslib.Streaming.freqMoment_graphStream_append_eq_two_mul_iff` for `k = 1` (so `k ≠ 1` is
   needed);
2. `Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist` for length `0`;
3. the hypotheses of the lower bounds: storing every frequency computes `F_k` exactly with
   `|α| log₂ (m + 1)` bits on streams of at most `m` items (`countAlg`), so
   `Cslib.Streaming.Algorithm.le_of_run_eq_freqMoment`,
   `Cslib.Streaming.le_of_solves_freqMoment_one_third`,
   `Cslib.Streaming.Algorithm.le_of_approx_freqMoment` and their `Fin N` forms all apply to it.
-/

public section

namespace ComplexityTests.StreamingMomentLowerBound

open Cslib Cslib.Streaming Finset

/-! ## 1. Graph streams -/

/-- The words `0 2` and `0 1` agree at one position and differ at one. -/
example : freqMoment 2 (graphStream ![(0 : Fin 3), 2] ++ graphStream ![0, 1]) = 4 + 2 := by
  rw [freqMoment_graphStream_append_eq]
  decide

example : freqMoment 0 (graphStream ![(0 : Fin 3), 2] ++ graphStream ![0, 1]) = 3 := by
  rw [freqMoment_graphStream_append_eq]
  decide

/-- For `k = 1` the moment is the length `2 n` of the stream, whether or not the words agree. -/
example : freqMoment 1 (graphStream ![(0 : Fin 3), 2] ++ graphStream ![0, 2]) = 2 * 2 := by
  rw [freqMoment_graphStream_append_eq]
  decide

example : ¬ ∀ i, (![(0 : Fin 3), 2] : Fin 2 → Fin 3) i ≠ ![0, 2] i := by
  decide

/-- With `k = 2` and words agreeing somewhere, the moment is not `2 n`. -/
example : freqMoment 2 (graphStream ![(0 : Fin 3), 2] ++ graphStream ![0, 1]) ≠ 2 * 2 := by
  rw [Ne, freqMoment_graphStream_append_eq_two_mul_iff (by norm_num)]
  decide

/-! ## 2. The code -/

example : ∃ C : Finset (Fin 0 → Fin 16), 1 ≤ #C :=
  let ⟨C, hC, _⟩ := Code.exists_two_pow_le_card_and_le_two_mul_hammingDist 0
  ⟨C, hC⟩

/-! ## 3. An exact algorithm: storing every frequency -/

/-- Computes `F_k` exactly by storing the frequency of every item. -/
def countAlg (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) : Algorithm (α → ℕ) α ℕ where
  init := fun _ => 0
  update q a := Function.update q a (q a + 1)
  output q := ∑ a ∈ univ.filter (fun a => q a ≠ 0), q a ^ k

theorem stateFrom_countAlg {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (q : α → ℕ)
    (s : List α) : (countAlg α k).stateFrom q s = fun a => q a + s.count a := by
  induction s generalizing q with
  | nil => rfl
  | cons x s ih =>
    rw [Algorithm.stateFrom_cons, ih]
    funext a
    simp only [countAlg, List.count_cons, beq_iff_eq]
    by_cases h : a = x
    · subst h
      simp only [Function.update_self, ↓reduceIte]
      omega
    · simp only [Function.update_of_ne h, Ne.symm h, ↓reduceIte]
      omega

theorem run_countAlg {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (s : List α) :
    (countAlg α k).run s = freqMoment k s := by
  rw [Algorithm.run, Algorithm.state, stateFrom_countAlg]
  simp only [countAlg, zero_add, freqMoment]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, ne_eq, List.count_eq_zero, not_not,
    List.mem_toFinset]

theorem spaceLE_countAlg {α : Type*} [Fintype α] [DecidableEq α] (k m b : ℕ)
    (h : (m + 1) ^ Fintype.card α ≤ 2 ^ b) : (countAlg α k).SpaceLE m b := by
  refine Algorithm.spaceLE_of_subset_finset (T := Fintype.piFinset fun _ => range (m + 1)) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    rw [Algorithm.state, stateFrom_countAlg, mem_coe, Fintype.mem_piFinset]
    intro a
    have := List.count_le_length (a := a) (l := s)
    simp only [countAlg, zero_add, mem_range]
    omega
  · rwa [Fintype.card_piFinset, prod_const, card_range, card_univ]

/-- `(n + 1) ^ (c n) ≤ 2 ^ (c n²)`. -/
theorem succ_pow_le_two_pow (n c : ℕ) : (n + 1) ^ (n * c) ≤ 2 ^ (c * n * n) :=
  calc (n + 1) ^ (n * c) ≤ (2 ^ n) ^ (n * c) := Nat.pow_le_pow_left Nat.lt_two_pow_self _
    _ = 2 ^ (c * n * n) := by rw [← pow_mul]; ring_nf

/-- `countAlg` meets the hypotheses of the deterministic exact bound, with `3 n²` bits. -/
example (n : ℕ) : n ≤ 3 * n * n :=
  Algorithm.le_of_run_eq_freqMoment (k := 2) (by norm_num) (countAlg _ 2)
    (fun s _ => run_countAlg 2 s)
    (spaceLE_countAlg 2 n _ (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact succ_pow_le_two_pow n 3))

/-- `countAlg` meets the hypotheses of the randomized bound as a point mass, here for `F₀`. -/
example (n : ℕ) : n ≤ 36864 * (3 * n * n + 1) + 2 ^ 12 :=
  le_of_solves_freqMoment_one_third (k := 0) (by norm_num) (PMF.pure (countAlg _ 0))
    ((Randomized.solves_pure _ fun s _ => run_countAlg 0 s).mono (by norm_num) le_rfl)
    (Randomized.spaceLE_pure (spaceLE_countAlg 0 n _ (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact succ_pow_le_two_pow n 3)))

/-- `countAlg`, read as a real number, meets the hypotheses of the approximation bound with
`η = 0`, with `16 L²` bits. -/
example (L : ℕ) : L ≤ 16 * L * L := by
  have hsp : (countAlg (Fin L × Fin 16) 3).SpaceLE L (16 * L * L) :=
    spaceLE_countAlg 3 L _ (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact succ_pow_le_two_pow L 16)
  refine Algorithm.le_of_approx_freqMoment (k := 3) (η := 0) (by norm_num) (by norm_num)
    ((countAlg _ 3).reduce [] id fun c => (c : ℝ)) (fun s _ => ?_)
    (Algorithm.SpaceLE.reduce [] (by rwa [List.length_nil, Nat.zero_add]) id _)
  rw [Algorithm.run_reduce, List.nil_append, List.map_id, run_countAlg]
  simp

/-- The `Fin N` form of the deterministic exact bound applies to `countAlg` on `Fin N`. -/
example (N : ℕ) : N / 3 ≤ N * N :=
  Algorithm.div_le_of_run_eq_freqMoment (k := 2) (by norm_num) (countAlg (Fin N) 2)
    (fun s _ => run_countAlg 2 s)
    (spaceLE_countAlg 2 (N / 3) _ (by
      rw [Fintype.card_fin]
      calc (N / 3 + 1) ^ N ≤ (2 ^ N) ^ N :=
            Nat.pow_le_pow_left ((Nat.add_le_add_right (Nat.div_le_self N 3) 1).trans
              (Nat.succ_le_of_lt Nat.lt_two_pow_self)) _
        _ = 2 ^ (N * N) := by rw [← pow_mul]))

end ComplexityTests.StreamingMomentLowerBound
