/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Decode
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Concrete instances of the direct-product decoder

The decoder is evaluated on a perfect direct product of `not` on `Bool`. The trial count is
compared with a direct computation, and the per-seed theorem is instantiated at `ε = 1/2`,
`δ = 1`, which shows that its hypotheses are satisfiable.
-/

namespace CslibFrontierTests.IJKWDecode

open Cslib.Circuits.Boolean.DirectProduct Finset

/-- The perfect direct product of `not`. -/
private def notK (k : ℕ) (y : Fin k → Bool) : Fin k → Bool := fun j => !y j

/-! ### The decoder -/

-- A trial with free position `1 ∉ {0}`: the tuple is `b₀ = (true, false)` on `{0}` and `x` at `1`.
example : trialTuple {0} ![true, false] false ((1 : Fin 2), ![false, false]) = ![true, false] := by
  decide

-- The perfect product accepts that trial, so the decoder outputs `not false = true`.
example : dpDecode (notK 2) false {0} ![true, false] ![((1 : Fin 2), ![false, false])] false =
    true := by
  decide

-- With no trial accepted (the only free position lies in `P`), the decoder outputs the default.
example : dpDecode (notK 2) false {0, 1} ![true, false] ![((1 : Fin 2), ![false, false])] false =
    false := by
  decide

/-! ### Counting trials -/

-- For `k = 2` and `P = {0}`, the trials with free position outside `P` whose tuple has `x = true`
-- at that position number `2 ^ 2` times the single pair `(1, (true, true))`.
example : #{t : Trial Bool 2 | t.1 ∉ ({0} : Finset (Fin 2)) ∧
      (fun j y => y j = true) t.1 (trialTuple {0} ![true, false] true t)} =
    Fintype.card Bool ^ (#({0} : Finset (Fin 2)) + 1) *
      #{p : Fin 2 × (Fin 2 → Bool) | p.1 ∉ ({0} : Finset (Fin 2)) ∧
        (∀ i ∈ ({0} : Finset (Fin 2)), p.2 i = ![true, false] i) ∧ p.2 p.1 = true ∧
          p.2 p.1 = true} :=
  card_filter_trialTuple {0} ![true, false] true fun j y => y j = true

example : #{t : Trial Bool 2 | t.1 ∉ ({0} : Finset (Fin 2)) ∧
      (trialTuple {0} ![true, false] true t) t.1 = true} = 4 := by
  decide

/-! ### The per-seed theorem -/

private theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

private theorem log_sixteen_lt : Real.log 16 < 2.7726 := by
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

-- With `P = ∅`, every tuple is consistent and a perfect product has no disagreements, so the
-- hypotheses hold for `k = 178` and `m = 45`: half of the trial vectors decode `not` with error
-- at most `1`, that is, on at least one of the two inputs.
example : (Fintype.card (Trial Bool 178) ^ 45 : ℝ) / 2 ≤
    #{v : Fin 45 → Trial Bool 178 |
      (#{x | dpDecode (notK 178) false ∅ (fun _ => false) v x ≠ !x} : ℝ) ≤
        1 / 2 * Fintype.card Bool} := by
  have hcons : consistent (notK 178) ∅ (fun _ => false) = univ := by
    ext y; simp
  have hdis : ∀ y, disagreements (notK 178) (fun x => !x) y = ∅ := by
    intro y; ext j; simp [notK]
  refine card_filter_dpDecode_err_le_ge (notK 178) (fun x => !x) false ∅ (fun _ => false) 45
    (ε := 1 / 2) (δ := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl (by simp) ?_ ?_ ?_ ?_
  · rw [compl_empty, card_univ, Fintype.card_fin]
    norm_num [div_div_eq_mul_div]
    linarith [log_four_lt]
  · norm_num
    linarith [log_sixteen_lt]
  · rw [hcons, compl_empty, card_univ, card_univ, Fintype.card_fin, Fintype.card_fun,
      Fintype.card_fin]
    norm_num
  · simp only [hcons, hdis, card_empty, Nat.cast_zero]
    norm_num

end CslibFrontierTests.IJKWDecode
