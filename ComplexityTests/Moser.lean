/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.CNF.LocalLemma
import Complexity.Logics.Propositional.CNF.Moser.Kolmogorov
import Complexity.Logics.Propositional.CNF.Moser.Probability
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Moser's resampling algorithm for `k`-SAT: a concrete run that resamples once, its log and the
recovered tape, its description for the Kolmogorov bridge, instances of the Local Lemma hypotheses
(constructive and existential), and instances where they fail. -/

namespace ComplexityTests.Moser

open Cslib.Logic.PL Cslib.Logic.PL.Moser Cslib.BitString MeasureTheory
open scoped ENNReal

/-- `(x₀ ∨ x₁ ∨ x₂) ∧ (¬x₃ ∨ x₄ ∨ x₅)`: two exact `3`-clauses on disjoint variables. -/
def φ : CNF (Fin 6) := [[(0, true), (1, true), (2, true)], [(3, false), (4, true), (5, true)]]

theorem φ_exact : φ.IsExactDistinct 3 := by decide

theorem φ_degree : ∀ i : Fin φ.length, degree φ i < 2 ^ (3 - 3) := by decide

example : ¬Shares [(0, true), (1, true), (2, true)] ([(3, false), (4, true), (5, true)] :
    Clause (Fin 6)) := by decide

/-! ### The hypotheses of the Local Lemma are satisfiable -/

example : φ.Satisfiable := satisfiable_of_degree_lt le_rfl φ_exact φ_degree

-- On fair coins the run uses up `t` resamplings with probability at most `2 ^ 3 2⁻ᵗ`, makes at
-- most `m + 2 = 4` resamplings in expectation, and stops with a satisfying assignment almost
-- surely.
example (t : ℕ) : coinFlips {x | Exhausts φ 3 t x} ≤ 2 ^ (2 + 1) * 2⁻¹ ^ t :=
  coinFlips_exhausts_le le_rfl φ_exact φ_degree t

example : ∫⁻ x, (resamplings φ 3 x : ℝ≥0∞) ∂coinFlips ≤ 4 := by
  refine (lintegral_resamplings_le le_rfl φ_exact φ_degree).trans (le_of_eq ?_)
  norm_num [φ]

example : ∀ᵐ x ∂coinFlips, ∃ R : ℕ, resamplings φ 3 x = R ∧
    ∀ t, R < t → φ.eval (final φ 3 t x).assignment = true :=
  ae_exists_eval_final le_rfl φ_exact φ_degree

/-- `(x₀ ∨ x₁ ∨ x₂ ∨ x₃) ∧ (¬x₀ ∨ x₄ ∨ x₅ ∨ x₆)`: two exact `4`-clauses sharing `x₀`, each of degree
`1 < 2 ^ (4 - 3)`. -/
def ψ : CNF (Fin 7) :=
  [[(0, true), (1, true), (2, true), (3, true)], [(0, false), (4, true), (5, true), (6, true)]]

example : Shares [(0, true), (1, true), (2, true), (3, true)]
    ([(0, false), (4, true), (5, true), (6, true)] : Clause (Fin 7)) := by decide

example : ∀ i : Fin ψ.length, degree ψ i = 1 := by decide

example : ψ.Satisfiable := satisfiable_of_degree_lt (k := 4) (by norm_num) (by decide) (by decide)

/-! ### A run that resamples once -/

/-- The tape: the initial assignment is all `false`, which violates the first clause of `φ`, and
every later bit is `true`. -/
def x (i : ℕ) : Bool := decide (6 ≤ i)

-- `Solve` calls `Fix` on the first clause, whose resampling reads the bits `6, 7, 8`. `Fix` then
-- finds no violated clause sharing a variable with it and returns, and `Solve` passes over the
-- second clause. With a budget of two resamplings the run makes one and stops with a satisfying
-- assignment; with a budget of one it uses it up.
example : (final φ 3 2 x).trace.map Fin.val = [0] := by decide

example : φ.eval (final φ 3 2 x).assignment = true := by decide

example : ¬Exhausts φ 3 2 x := by decide

example : Exhausts φ 3 1 x := by decide

-- The log (with `L = 0` position bits): the call of `Fix` by `Solve`, the return of `Fix`, and the
-- pass over the second clause. It has `3 ≤ m + t (L + 2) = 6` bits.
example : log φ 3 2 0 x (fuel φ 2) = [true, false, false] := by decide

-- The decoder recovers the `6 + 3` bits read from the final assignment and the log.
example : ∀ i < 9, decode φ 3 0 (final φ 3 2 x).assignment (log φ 3 2 0 x (fuel φ 2)) i = x i := by
  have h : (final φ 3 2 x).trace.length = 1 := by decide
  intro i hi
  exact decode_run φ_exact φ_degree 2 x (fuel φ 2) i (by rw [← final, h]; omega)

/-! ### The description method of the decoder -/

/-- The first `6 + 1 * 3` bits of the tape `x`. -/
def y : List Bool := List.ofFn fun i : Fin 9 => x i

-- With a budget of one resampling the run on `y` uses it up, and the description (final assignment
-- and log, `L = 0`) decodes to `y`. Its `6 + 3 = 9` bits are within `n + m + t (L + 2) = 10`.
example : Exhausts φ 3 1 fun i => y.getD i false := by decide

example : (description φ 3 1 0 fun i => y.getD i false).length = 9 := by decide

example : decodeWord φ 3 0 (description φ 3 1 0 fun i => y.getD i false) = y :=
  decodeWord_description φ_exact φ_degree rfl (by decide)

example : (descriptionMethod φ 3 0).Produces (description φ 3 1 0 fun i => y.getD i false) y :=
  descriptionMethod_produces φ_exact φ_degree rfl (by decide)

example : (descriptionMethod φ 3 0).ecomplexity y ≤ (6 + 2 + 1 * (0 + 2) : ℕ) :=
  ecomplexity_le_of_exhausts φ_exact φ_degree rfl (by decide)

-- Fortnow's argument: with a budget of `3 > m` resamplings, the run on some tape word of length
-- `6 + 3 * 3` succeeds.
example : ∃ y : List Bool, y.length = 6 + 3 * 3 ∧
    φ.eval (final φ 3 3 fun i => y.getD i false).assignment = true :=
  exists_eval_final_of_degree_lt le_rfl φ_exact φ_degree (by decide)

/-! ### The existential Local Lemma -/

/-- Five exact `4`-clauses sharing `x₀`, each of degree `4`. -/
def ρ : CNF (Fin 16) :=
  [[(0, true), (1, true), (2, true), (3, true)], [(0, true), (4, true), (5, true), (6, true)],
    [(0, false), (7, true), (8, true), (9, true)], [(0, false), (10, true), (11, true), (12, true)],
    [(0, true), (13, false), (14, true), (15, true)]]

example : ∀ i : Fin ρ.length, degree ρ i = 4 := by decide

-- The constructive bound `degree < 2 ^ (4 - 3)` fails ...
example : ¬∀ i : Fin ρ.length, degree ρ i < 2 ^ (4 - 3) := by decide

-- ... but `e (4 + 1) ≤ 2 ^ 4` holds, so the existential Local Lemma applies.
example : ρ.Satisfiable := by
  refine CNF.IsExactDistinct.satisfiable_of_exp_mul_le (k := 4) (d := 4) (by decide)
    (fun i => (by decide : ∀ i : Fin ρ.length, degree ρ i = 4) i ▸ le_rfl) ?_
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  linarith

-- The constructive hypothesis implies the existential one, since `e < 8`.
example {k d : ℕ} (hk : 3 ≤ k) (hd : d < 2 ^ (k - 3)) : Real.exp 1 * (d + 1) ≤ 2 ^ k := by
  have h1 : ((d : ℝ) + 1) ≤ 2 ^ (k - 3) := by exact_mod_cast Nat.succ_le_of_lt hd
  have h2 : Real.exp 1 ≤ 2 ^ 3 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  calc Real.exp 1 * (d + 1) ≤ 2 ^ 3 * 2 ^ (k - 3) := by gcongr
    _ = 2 ^ k := by
      rw [← pow_add]
      congr 1
      omega

/-! ### Instances where the hypotheses fail -/

-- A repeated variable, and a clause of the wrong length.
example : ¬CNF.IsExactDistinct 3 ([[(0, true), (0, false), (1, true)]] : CNF (Fin 2)) := by decide

example : ¬CNF.IsExactDistinct 3 ([[(0, true), (1, true)]] : CNF (Fin 2)) := by decide

/-- All eight exact `3`-clauses on three variables: unsatisfiable, and each clause shares a variable
with the seven others. -/
def χ : CNF (Fin 3) :=
  (List.finRange 8).map fun i =>
    [(0, i.1.testBit 0), (1, i.1.testBit 1), (2, i.1.testBit 2)]

example : χ.IsExactDistinct 3 := by decide

example : ∀ i : Fin χ.length, degree χ i = 7 := by decide

example : ¬χ.Satisfiable := by
  rintro ⟨σ, hσ⟩
  revert hσ
  revert σ
  decide

-- The existential Local Lemma does not apply to `χ`: `e (7 + 1) > 2 ^ 3`.
example : ¬Real.exp 1 * (7 + 1) ≤ 2 ^ 3 := by
  have := Real.exp_one_gt_d9
  intro h
  linarith

end ComplexityTests.Moser
