/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.ParallelRepetition.Embedding

/-! # The first stage of Holenstein's Lemma 6.4

With nothing conditioned (`C = ∅`), the bounds collapse to zero: the question pair at every
coordinate has the law of `G.questions`, and the questions embed exactly in the law of
`((x_j, y_j), (S, S))`. In general, averaging the errors of the first stage gives a free coordinate
whose error is at most `27 / √2 · √((#C ln (|A| |B|) + ln (1 / Pr[W_C])) / #Cᶜ)`: the coordinate
that Holenstein's Lemma 6.5 picks.
-/

namespace ComplexityTests.RepetitionEmbedding

open Finset
open Cslib.PCP Cslib.PCP.ParallelRepetition Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

variable {X Y A B : Type*} [Fintype X] [Fintype Y] {G : TwoProverGame X Y A B} {n : ℕ}
  {ha : (Fin n → X) → Fin n → A} {hb : (Fin n → Y) → Fin n → B}

-- With nothing conditioned, (6.14) is zero: every coordinate has the law of `G.questions`.
example (hC : ∃ q ∈ G.winsOn ha hb ∅, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ (∅ : Finset (Fin n))}) :
    (condLaw G ∅ ha hb hC).map (fun ω => ω.2 j) = G.questions := by
  have h := sum_dist_map_condLaw_pair_le hC
  simp only [TwoProverGame.winProbOn_empty, div_one, Real.log_one, mul_zero, zero_div,
    Real.sqrt_zero] at h
  exact dist_le_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => dist_nonneg).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ => dist_nonneg)) j (Finset.mem_univ j)).le

variable [Fintype A] [Fintype B]

-- With nothing conditioned, the first stage is exact at every coordinate.
example (hC : ∃ q ∈ G.winsOn ha hb ∅, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ (∅ : Finset (Fin n))}) :
    IsEmbeddable G.questions
      ((condLaw G ∅ ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω))) 0 := by
  obtain ⟨ε, hemb, hsum⟩ := exists_isEmbeddable_condLaw_shared hC
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul, TwoProverGame.winProbOn_empty, div_one,
    Real.log_one, add_zero, mul_zero, Real.sqrt_zero] at hsum
  -- An embedding error is at least a distance, so it is nonnegative.
  have hnn (i : {i // i ∉ (∅ : Finset (Fin n))}) : 0 ≤ ε i := by
    obtain ⟨R, ρ, fA, fB, hd⟩ := hemb i
    exact dist_nonneg.trans hd
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp
    (le_antisymm hsum (Finset.sum_nonneg fun i _ => hnn i)) j (Finset.mem_univ j)
  exact hj ▸ hemb j

-- Averaging: some free coordinate has at most the average error. This is how Holenstein's
-- Lemma 6.5 picks its coordinate.
example (C : Finset (Fin n)) (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support)
    (hfree : C ≠ univ) :
    ∃ j : {i // i ∉ C}, IsEmbeddable G.questions
      ((condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω)))
      (27 / Real.sqrt 2 * Real.sqrt ((#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / #Cᶜ)) := by
  obtain ⟨ε, hemb, hsum⟩ := exists_isEmbeddable_condLaw_shared hC
  set Z := #C * Real.log (Fintype.card A * Fintype.card B) + Real.log (1 / G.winProbOn ha hb C)
  have hk : (0 : ℝ) < #Cᶜ := by
    have hne : Cᶜ.Nonempty := (Finset.compl_ne_univ_iff_nonempty Cᶜ).mp (by rwa [compl_compl])
    exact_mod_cast Finset.card_pos.mpr hne
  have hcard : Fintype.card {i // i ∉ C} = #Cᶜ := by
    simp only [← Finset.mem_compl, Fintype.card_coe]
  have hne : (univ : Finset {i // i ∉ C}).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, hcard]
    exact_mod_cast hk
  -- `#Cᶜ · √(Z / #Cᶜ) = √(#Cᶜ · Z)`.
  have hsqrt : #Cᶜ * Real.sqrt (Z / #Cᶜ) = Real.sqrt (#Cᶜ * Z) := by
    rw [← Real.sqrt_sq hk.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk.le]
    congr 1
    field_simp
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hne (f := ε)
    (g := fun _ => 27 / Real.sqrt 2 * Real.sqrt (Z / #Cᶜ)) (by
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      calc _ ≤ _ := hsum
        _ = _ := by rw [← hsqrt]; ring)
  exact ⟨j, (hemb j).mono hj⟩

end ComplexityTests.RepetitionEmbedding
