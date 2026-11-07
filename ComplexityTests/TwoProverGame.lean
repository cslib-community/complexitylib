/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.TwoProverGame
import Complexity.Probability.PMF.Filter
import Complexity.Probability.PMF.Map

/-! # Two-prover one-round games

The CHSH game: the constant strategies win with probability `3/4`, so its value is at least `3/4`
and the value of its `n`-fold repetition is at least `(3/4)^n`. A game that accepts every answer
has value one. Strategy extraction on the one-fold repetition, where the questions embed exactly,
bounds every strategy of `chsh.pow 1` by the value of CHSH.
-/

namespace ComplexityTests.TwoProverGame

open Cslib.PCP Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

/-- The **CHSH game**: uniform questions `x, y`, accepted when `a xor b = x && y`. -/
noncomputable def chsh : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts x y a b := (a ^^ b) = (x && y)

theorem winProb_chsh_const : chsh.winProb (fun _ => false) (fun _ => false) = 3 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type]
  norm_num

example : 3 / 4 ≤ chsh.value := winProb_chsh_const ▸ chsh.winProb_le_value _ _

example (n : ℕ) : (3 / 4 : ℝ) ^ n ≤ (chsh.pow n).value := by
  rw [← winProb_chsh_const, ← chsh.winProb_pow n]
  exact (chsh.pow n).winProb_le_value _ _

/-- A game that accepts every answer. -/
noncomputable def always : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts _ _ _ _ := True

example : always.value = 1 := by
  refine le_antisymm always.value_le_one ?_
  have : always.winProb (fun _ => true) (fun _ => true) = 1 := by
    simp [TwoProverGame.winProb, always]
  exact this ▸ always.winProb_le_value _ _

-- Strategy extraction with `C = ∅` on the one-fold repetition: each party copies its question,
-- so the questions embed exactly, and every strategy of `chsh.pow 1` wins with probability at
-- most `chsh.value`.
example (ha : (Fin 1 → Bool) → Fin 1 → Bool) (hb : (Fin 1 → Bool) → Fin 1 → Bool) :
    (chsh.pow 1).winProb ha hb ≤ chsh.value := by
  have hC : ∃ q ∈ chsh.winsOn ha hb ∅, q ∈ (chsh.pow 1).questions.support := by
    obtain ⟨q, hq⟩ := (chsh.pow 1).questions.support_nonempty
    exact ⟨q, by simp, hq⟩
  have hpi : Cslib.Probability.PMF.pi (fun _ : Fin 1 => chsh.questions) =
      chsh.questions.map (Equiv.funUnique (Fin 1) (Bool × Bool)).symm := by
    ext u
    rw [Cslib.Probability.PMF.map_equiv_apply, Cslib.Probability.PMF.pi_apply, Fin.prod_univ_one]
    rfl
  have hemb : IsEmbeddable chsh.questions
      (((chsh.pow 1).questions.filter (chsh.winsOn ha hb ∅) hC).map
        fun (x, y) => ((x 0, y 0), (x, y))) 0 := by
    refine IsEmbeddable.of_dist_le (PMF.pure ()) (fun x _ _ => x) (fun y _ _ => y) (le_of_eq ?_)
    rw [dist_eq_zero, Cslib.Probability.PMF.filter_eq_self_of_support_subset _ _ _ (by simp),
      TwoProverGame.pow, hpi]
    simp only [PMF.pure_map, PMF.map_comp]
    rfl
  have h := chsh.winProbOn_insert_le ha hb ∅ 0 hC hemb
  rwa [TwoProverGame.winProbOn_empty, one_mul, add_zero,
    show insert (0 : Fin 1) ∅ = Finset.univ by decide, TwoProverGame.winProbOn_univ] at h

end ComplexityTests.TwoProverGame
