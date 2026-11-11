/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Hypergeometric.Miss
import CslibFrontier.Probability.IID.FirstAccepted
import CslibFrontier.Probability.TupleSampler

/-! # Concrete instances of the direct-product sampling lemmas

The subset-miss bound, the first-accepted trial and the uniform-tuple sampler lemmas are applied
to small explicit objects. The miss count and the first-accepted value are compared with a direct
computation, and the sampler lemmas are instantiated with the indicator of `true` on `Bool`,
which shows that their hypotheses are satisfiable.
-/

namespace CslibFrontierTests.IJKWSampling

open Cslib Cslib.Probability Finset

/-! ### Subsets missing a fixed set -/

-- Of the 2-subsets of `{0, …, 4}`, the three inside `{2, 3, 4}` miss `{0, 1}`.
example : #{J ∈ (range 5).powersetCard 2 | Disjoint ({0, 1} : Finset ℕ) J} = 3 :=
  card_filter_disjoint_powersetCard (by decide) 2

example : #{J ∈ (range 5).powersetCard 2 | Disjoint ({0, 1} : Finset ℕ) J} = 3 := by decide

-- `C(4, 3) ≤ C(6, 3) exp (-2 · 3 / 6)`, that is `4 ≤ 20 / e`.
example : ((6 - 2).choose 3 : ℝ) ≤ (6).choose 3 * Real.exp (-(2 * 3 / 6)) := by
  exact_mod_cast choose_sub_le_choose_mul_exp (by norm_num : 2 ≤ 6) 3

example : (#{J ∈ (range 5).powersetCard 2 | Disjoint ({0, 1} : Finset ℕ) J} : ℝ) ≤
    #((range 5).powersetCard 2) * Real.exp (-(#({0, 1} : Finset ℕ) * 2 / #(range 5))) :=
  card_filter_disjoint_powersetCard_le (by decide) 2

/-! ### The first accepted trial -/

-- The first entry of `(0, 3, 5)` that is at least `2` is `3`.
example : firstAccepted (fun n : ℕ => decide (2 ≤ n)) ![0, 3, 5] = some 3 := by
  change firstAccepted _ (Fin.cons 0 (Fin.cons 3 (Fin.cons 5 ![]))) = _
  rw [firstAccepted_cons, firstAccepted_cons]; rfl

example : firstAccepted (fun n : ℕ => decide (2 ≤ n)) ![0, 1] = none := by
  change firstAccepted _ (Fin.cons 0 (Fin.cons 1 ![])) = _
  rw [firstAccepted_cons, firstAccepted_cons]; decide

-- With `acc = id` and `bad = id` on `Bool`, every accepted value is bad.
example : #{v : Fin 3 → Bool | (firstAccepted id v).any id} * #{a : Bool | id a = true} ≤
    #{a : Bool | id a ∧ id a} * Fintype.card Bool ^ 3 :=
  card_filter_firstAccepted_bad_mul_le id id 3

/-! ### Uniform tuples -/

/-- The indicator of `true`, which has mean `1 / 2` on `Bool`. -/
private def indTrue (b : Bool) : ℝ := if b then 1 else 0

private theorem indTrue_mem (b : Bool) : indTrue b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> simp [indTrue]

private theorem indTrue_mean : (1 / 2 : ℝ) * Fintype.card Bool ≤ ∑ b, indTrue b := by
  simp [indTrue]

-- Few tuples in `Bool⁴` have at most one `true`.
example : (#{b : Fin 4 → Bool | ∑ i, indTrue (b i) ≤ 1 / 2 * Fintype.card (Fin 4) / 2} : ℝ) ≤
    Fintype.card Bool ^ Fintype.card (Fin 4) *
      Real.exp (-(1 / 2 * Fintype.card (Fin 4) / 8)) :=
  card_filter_sum_le_half_le_exp indTrue indTrue_mem indTrue_mean

example (W : Finset (Fin 4 → Bool)) :
    ((#W : ℝ) - Fintype.card Bool ^ Fintype.card (Fin 4) *
        Real.exp (-(1 / 2 * Fintype.card (Fin 4) / 8))) * (1 / 2 * Fintype.card (Fin 4)) ≤
      2 * ∑ b ∈ W, ∑ i, indTrue (b i) :=
  sub_mul_le_two_mul_sum_sum indTrue indTrue_mem (by norm_num) indTrue_mean W

-- Planting `x` at coordinate `0` of a pair counts each pair twice.
example : ∑ x : Bool, ∑ r : Fin 2 → Bool, indTrue (Function.update r 0 x 1) =
    Fintype.card Bool • ∑ b : Fin 2 → Bool, indTrue (b 1) :=
  sum_sum_update_eq_card_nsmul_sum 0 fun _ b => indTrue (b 1)

example (W : Finset (Fin 2 → Bool)) : ∑ b ∈ W, ∑ i, indTrue (b i) =
    ∑ x, (#((W ×ˢ (univ : Finset (Fin 2))).filter fun p => p.1 p.2 = x) : ℝ) * indTrue x :=
  sum_sum_comp_eq_sum_mul indTrue W

end CslibFrontierTests.IJKWSampling
