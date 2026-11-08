/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.SharpDNF

/-! Concrete checks of the Karp–Luby–Madras FPRAS for #DNF: exact model counts, contradictory
terms, the zero-count case, the exact trial law, and the relative-error predicate. -/

namespace ComplexityTests.SharpDNF

open Cslib Cslib.Complexity Cslib.Logic.PL Cslib.Complexity.KarpLubyMadras Turing.MultiTapeTM

/-- `x₀`. -/
private def single : DNF ℕ := [[(0, true)]]

/-- `x₀ ∨ x₁`. -/
private def orTwo : DNF ℕ := [[(0, true)], [(1, true)]]

/-- `(x₀ ∧ ¬x₀) ∨ (x₀ ∧ x₁)`: a narrow contradictory term before a wide consistent one. -/
private def contra : DNF ℕ := [[(0, true), (0, false)], [(0, true), (1, true)]]

/-- `x₀ ∧ ¬x₀`: no models. -/
private def unsat : DNF ℕ := [[(0, true), (0, false)]]

/-! ### Model counts -/

example : SharpDNF single = 1 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

example : SharpDNF orTwo = 3 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

example : SharpDNF contra = 1 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

example : SharpDNF unsat = 0 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

/-- The empty formula is unsatisfiable. -/
example : SharpDNF [] = 0 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

/-- The empty term is satisfied by the unique assignment of no variables. -/
example : SharpDNF [[]] = 1 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

/-- A repeated literal is counted once: `x₀ ∧ x₀` has width `1` and one model. -/
example : SharpDNF [[(0, true), (0, true)]] = 1 := by
  rw [SharpDNF, DNF.modelCount_eq_card_filter]
  decide +kernel

example : Term.width ([(0, true), (0, true)] : Term ℕ) = 1 := by decide +kernel

/-! ### Consistency and the minimum width -/

example : Term.consistent ([(0, true), (1, false)] : Term ℕ) = true := by decide +kernel

example : Term.consistent ([(0, true), (0, false)] : Term ℕ) = false := by decide +kernel

example : minWidth orTwo = 1 := by decide +kernel

/-- The contradictory term of width `1` is ignored: the minimum width is that of the consistent
term, `2`, not `1`. -/
example : minWidth contra = 2 := by decide +kernel

/-- Without consistent terms the minimum width is the number of variables. -/
example : minWidth unsat = 1 := by decide +kernel

/-! ### The exact law of one trial -/

/-- For `x₀ ∨ x₁`: `#φ = 3`, `D = 4`, `n - L = 1`, so a trial accepts with probability `3 / 8`. -/
example : (ProbComp.eval (trial orTwo) true).toReal = 3 / 8 := by
  rw [eval_trial_true_toReal]
  have h1 : DNF.modelCount orTwo = 3 := by
    rw [DNF.modelCount_eq_card_filter]
    decide +kernel
  have h2 : Probability.dyadicSize orTwo.length = 4 := by decide +kernel
  have h3 : CNF.numVars orTwo - minWidth orTwo = 1 := by decide +kernel
  rw [h1, h2, h3]
  norm_num

/-- For the formula with a contradictory term: `#φ = 1`, `D = 4`, `n - L = 0`. -/
example : (ProbComp.eval (trial contra) true).toReal = 1 / 4 := by
  rw [eval_trial_true_toReal]
  have h1 : DNF.modelCount contra = 1 := by
    rw [DNF.modelCount_eq_card_filter]
    decide +kernel
  have h2 : Probability.dyadicSize contra.length = 4 := by decide +kernel
  have h3 : CNF.numVars contra - minWidth contra = 0 := by decide +kernel
  rw [h1, h2, h3]
  norm_num

/-- A formula without models: every trial rejects. -/
example : (ProbComp.eval (trial unsat) true).toReal = 0 := by
  rw [eval_trial_true_toReal]
  have h1 : DNF.modelCount unsat = 0 := by
    rw [DNF.modelCount_eq_card_filter]
    decide +kernel
  rw [h1]
  simp

/-! ### The relative-error predicate -/

/-- `7 / 2` is within relative error `1 / 4` of `3`. -/
example : ApproxWithin 3 4 7 2 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [abs_of_nonneg]

/-- `4 / 1` is not within relative error `1 / 4` of `3`. -/
example : ¬ApproxWithin 3 4 4 1 := by
  rintro ⟨-, h⟩
  norm_num [abs_of_nonneg] at h

/-- A zero count admits only exact estimates. -/
example : ApproxWithin 0 4 0 5 := ⟨by norm_num, by norm_num⟩

example : ¬ApproxWithin 0 4 1 5 := fun h => absurd h.num_eq_zero one_ne_zero

/-! ### The FPRAS -/

example : SharpDNF ∈ FPRAS encDNF := SharpDNF.mem_FPRAS

/-- With `p = 2` and `t = 3`: the estimate is within relative error `1 / 2` with probability at
least `7 / 8`. -/
example (φ : DNF ℕ) : (7 / 8 : ℝ) ≤ ((ProbComp.eval (estimate φ 2 3)).toOuterMeasure
    {out | ApproxWithin (SharpDNF φ) 2 out.1 out.2}).toReal := by
  have h := approxWithin_estimate φ (p := 2) (by norm_num) 3
  norm_num at h
  exact h

/-- A formula without models is counted exactly with probability one, for every `p` and `t`. -/
example (p t : ℕ) : (ProbComp.eval (estimate unsat p t)).toOuterMeasure {out | out.1 = 0} = 1 :=
  estimate_fst_eq_zero (by rw [DNF.modelCount_eq_card_filter]; decide +kernel) p t

/-- The same conclusion from the FPRAS guarantee alone, up to its failure probability. -/
example (t : ℕ) : 1 - (1 / 2 : ℝ) ^ t ≤ ((ProbComp.eval (estimate unsat 1 t)).toOuterMeasure
    {out | out.1 = 0}).toReal := by
  refine (approxWithin_estimate unsat (p := 1) (by norm_num) t).trans ?_
  refine ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono fun out hout => ?_)
  have h1 : DNF.modelCount unsat = 0 := by
    rw [DNF.modelCount_eq_card_filter]
    decide +kernel
  rw [Set.mem_ofPred_eq, h1] at hout
  exact hout.num_eq_zero

end ComplexityTests.SharpDNF
