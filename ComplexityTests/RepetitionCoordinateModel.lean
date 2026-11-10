/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.ParallelRepetition.CoordinateModel
import Complexity.Computability.PCP.TwoProverGame.CHSH
import Complexity.Probability.PMF.Uniform

/-! # The coordinate model of Holenstein's Lemma 6.4

For the CHSH questions, given Bob's question, Alice's is uniform. A sample of the twofold
repetition with one conditioned coordinate has mass `1 / 32`. With nothing conditioned
(`C = ∅`), the bound (6.5) is zero, so the question pair at each coordinate given the revealed
halves is exactly `pairGiven` of its half. Conditioning on the bit `D_j` leaves the variable `S`
unchanged. An embedding of the questions in the model's conditioned law is exactly the premise of
strategy extraction.
-/

namespace ComplexityTests.RepetitionCoordinateModel

open Cslib.PCP Cslib.PCP.ParallelRepetition Cslib.Probability.CorrelatedSampling
open Cslib.Probability.PMF (uniformOfFintype)
open scoped Cslib.Probability.PMF
open Cslib.PCP.TwoProverGame (chsh)

-- Only the uniform questions `x, y` of the CHSH game (`Cslib.PCP.TwoProverGame.chsh`) matter
-- here. Given Bob's question `y`, Alice's question is uniform.
example (y : Bool) : pairGiven chsh (.inr y) = (uniformOfFintype Bool).map (·, y) := by
  have h : chsh.questions.map Prod.swap =
      (uniformOfFintype Bool).bind fun a => (uniformOfFintype Bool).map (a, ·) := by
    rw [Cslib.Probability.PMF.uniformOfFintype_prod]
    exact Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.prodComm Bool Bool)
  rw [pairGiven, h, Cslib.Probability.PMF.conditionalSnd_bind_pair _ _ _
    (Cslib.Probability.PMF.mem_support_uniformOfFintype y)]

-- In the twofold repetition with `C = {0}`, a sample has one bit and two question pairs.
example (d : {i // i ∉ ({0} : Finset (Fin 2))} → Bool) (q : Fin 2 → Bool × Bool) :
    sampleLaw chsh {0} (d, q) = 32⁻¹ := by
  rw [sampleLaw_apply, show ({0} : Finset (Fin 2))ᶜ.card = 1 by decide, Fin.prod_univ_two]
  simp only [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_prod,
    Fintype.card_bool]
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num), ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

variable {X Y A B : Type*} [Fintype X] [Fintype Y] (G : TwoProverGame X Y A B) {n : ℕ}
  (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)

-- With nothing conditioned, (6.5) has error zero: given `T` and `V`, the pair at `j` is drawn
-- exactly from `pairGiven` of its revealed half.
example [Fintype A] [Fintype B]
    (hC : ∃ q ∈ G.winsOn ha hb ∅, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ (∅ : Finset (Fin n))}) :
    dist ((condLaw G ∅ ha hb hC).map fun ω => ((revealed ∅ ω, answers ∅ ha hb ω.2), ω.2 j))
      (((condLaw G ∅ ha hb hC).map fun ω => (revealed ∅ ω, answers ∅ ha hb ω.2)).bind
        fun s => (pairGiven G (s.1.halves j)).map (s, ·)) = 0 := by
  have h := sum_dist_condLaw_le hC
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul, TwoProverGame.winProbOn_empty, div_one,
    Real.log_one, add_zero, mul_zero, zero_div, Real.sqrt_zero] at h
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => dist_nonneg).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ => dist_nonneg)) j (Finset.mem_univ j)

-- Conditioning on the bit `D_j` does not change the law of `S`, which ignores it.
example (C : Finset (Fin n)) (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ C})
    (h : ∃ ω ∈ {ω : Sample X Y C | ω.1 j = false}, ω ∈ (condLaw G C ha hb hC).support) :
    ((condLaw G C ha hb hC).filter {ω | ω.1 j = false} h).map (shared ha hb j) =
      (condLaw G C ha hb hC).map (shared ha hb j) :=
  map_filter_condLaw_bit hC j false _ (shared_update ha hb j) h

-- An embedding of the questions of `G` in the model's law of `((x_j, y_j), (x, y))` under `W_C`
-- is the premise of strategy extraction.
example [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (C : Finset (Fin n)) (j : Fin n)
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) {ε : ℝ}
    (hε : IsEmbeddable G.questions
      ((condLaw G C ha hb hC).map fun ω => (ω.2 j, (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2))) ε) :
    G.winProbOn ha hb (insert j C) ≤ G.winProbOn ha hb C * (G.value + ε) := by
  refine G.winProbOn_insert_le ha hb C j hC ?_
  rw [← map_condLaw_questions hC, PMF.map_comp]
  exact hε

end ComplexityTests.RepetitionCoordinateModel
