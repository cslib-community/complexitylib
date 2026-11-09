/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.ParallelRepetition
import ComplexityTests.TwoProverGame

/-! # Holenstein's parallel repetition theorem

The CHSH game has value `3/4` (`Cslib.PCP.TwoProverGame.value_chsh`), so the theorem
bounds the value of its `n`-fold repetition by `(1 - (1/4)³ / 6000)^{n / 2}`, and the product
strategies bound it below by `(3/4)^n`. For every
game of value below one, the value of the repetition tends to zero. The theorem is consistent with
the lower bound `v(G)^n ≤ v(Gⁿ)` of product strategies. With nothing conditioned, Lemma 6.5 gives a
coordinate that is won with probability at most `v(G)`.
-/

namespace ComplexityTests.ParallelRepetition

open Filter Topology
open Cslib.PCP
open Cslib.PCP.TwoProverGame (chsh value_chsh)

-- The parallel repetition theorem for CHSH: `|A| |B| = 4`, so the exponent is `n / 2`. With the
-- product strategies, `(3/4)^n ≤ v(CHSHⁿ) ≤ (1 - (1/4)³ / 6000)^{n / 2}`.
example (n : ℕ) :
    (3 / 4 : ℝ) ^ n ≤ (chsh.pow n).value ∧
      (chsh.pow n).value ≤ (1 - (1 / 4) ^ 3 / 6000) ^ ((n : ℝ) / 2) := by
  have hlog : Real.logb 2 (Fintype.card Bool * Fintype.card Bool) = 2 := by
    rw [Fintype.card_bool, show ((2 : ℕ) : ℝ) * (2 : ℕ) = 2 ^ (2 : ℝ) by norm_num,
      Real.logb_rpow two_pos (by norm_num)]
  refine ⟨value_chsh ▸ chsh.pow_value_le_value_pow n, ?_⟩
  have h := chsh.value_pow_le_of_value_le (by simp) (ε := 1 / 4) (by rw [value_chsh]; norm_num) n
  rwa [hlog] at h

-- For every game of value below one, the value of the repetition tends to zero.
example {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : TwoProverGame X Y A B) (hAB : 2 ≤ Fintype.card A * Fintype.card B) (hv : G.value < 1) :
    Tendsto (fun n => (G.pow n).value) atTop (𝓝 0) := by
  have : Nonempty A := Fintype.card_pos_iff.mp (by
    rcases Nat.eq_zero_or_pos (Fintype.card A) with h | h <;> simp_all)
  have : Nonempty B := Fintype.card_pos_iff.mp (by
    rcases Nat.eq_zero_or_pos (Fintype.card B) with h | h <;> simp_all)
  set L := Real.logb 2 (Fintype.card A * Fintype.card B)
  set r := 1 - (1 - G.value) ^ 3 / 6000
  have hL : 0 < L := Real.logb_pos one_lt_two (by exact_mod_cast hAB)
  have hu : 0 < 1 - G.value := by linarith
  have hu1 : 1 - G.value ≤ 1 := by linarith [G.value_nonneg]
  have hr0 : 0 ≤ r := by
    have := pow_le_one₀ hu.le hu1 (n := 3)
    simp only [r]
    linarith
  have hr1 : r < 1 := by
    have := pow_pos hu 3
    simp only [r]
    linarith
  -- `r^{n / L} = (r^{1 / L})^n`, and `r^{1 / L} < 1`.
  have hpow (n : ℕ) : r ^ ((n : ℝ) / L) = (r ^ (1 / L)) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, one_div_mul_eq_div]
  have hlim : Tendsto (fun n : ℕ => (r ^ (1 / L)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hr0 _)
      (Real.rpow_lt_one hr0 hr1 (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (G.pow n).value_nonneg) fun n => ?_
  rw [← hpow n]
  exact G.value_pow_le hAB n

-- The upper bound is consistent with the lower bound of product strategies.
example {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : TwoProverGame X Y A B)
    (hAB : 2 ≤ Fintype.card A * Fintype.card B) (n : ℕ) :
    G.value ^ n ≤ (1 - (1 - G.value) ^ 3 / 6000) ^
      ((n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B)) :=
  (G.pow_value_le_value_pow n).trans (G.value_pow_le hAB n)

-- With nothing conditioned, `Pr[W_∅] = 1` and the error term of Lemma 6.5 vanishes: some coordinate
-- is won with probability at most `v(G)`.
example {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (G : TwoProverGame X Y A B) {n : ℕ} (hn : 0 < n)
    (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B) :
    ∃ j : Fin n, G.winProbOn ha hb {j} ≤ G.value := by
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := by
    rw [ne_comm, ← Finset.nonempty_iff_ne_empty, Finset.univ_nonempty_iff]
    exact ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ := G.exists_winProbOn_insert_le ha hb hne
  refine ⟨j, ?_⟩
  simpa using hj

end ComplexityTests.ParallelRepetition
