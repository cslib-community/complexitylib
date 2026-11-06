/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Optimization.OneConstraint
public import Complexity.Probability.PMF
import Mathlib.Tactic

/-!
# Finite probability tables and PMF semantics

The algebraic tables used in finite linear optimization also have ordinary PMF
semantics. Conversion preserves finite mixtures, deterministic maps and expectations.
Rational tables remain in the optimizer; real tables are interpreted as PMFs.

## Main results

* `Distribution.toPMF_bind`, `Distribution.toPMF_map`: preserve probabilistic semantics.
* `Distribution.mean_realify`: exact rational-to-real expectations.
-/

public section
noncomputable section
namespace Cslib.Optimization.OneConstraint.Distribution
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Interpret a normalized real probability table as a PMF. -/
@[expose] def toPMF (w : Distribution α ℝ) : PMF α :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w.weight i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => w.nonneg i), w.total,
      ENNReal.ofReal_one])

/-- The real mass of an interpreted table is its original weight. -/
@[simp] theorem toPMF_real (w : Distribution α ℝ) (i : α) :
    (w.toPMF i).toReal = w.weight i := ENNReal.toReal_ofReal (w.nonneg i)

/-- Interpretation preserves deterministic laws. -/
theorem toPMF_pure (i : α) : (Distribution.pure i : Distribution α ℝ).toPMF = PMF.pure i := by
  classical
  ext j
  by_cases h : j = i <;> simp [toPMF, Distribution.pure, PMF.pure_apply, h]

/-- Interpretation preserves conditional mixtures. -/
theorem toPMF_bind (w : Distribution α ℝ) (k : α → Distribution β ℝ) :
    (w.bind k).toPMF = w.toPMF.bind (fun i => (k i).toPMF) := by
  ext j
  apply (ENNReal.toReal_eq_toReal_iff' ((w.bind k).toPMF.apply_ne_top j)
    ((w.toPMF.bind fun i => (k i).toPMF).apply_ne_top j)).mp
  simp only [toPMF_real, Cslib.Probability.PMF.bind_apply_toReal, Distribution.bind]

/-- Interpretation preserves deterministic postprocessing. -/
theorem toPMF_map (w : Distribution α ℝ) (f : α → β) :
    (w.map f).toPMF = w.toPMF.map f := by
  classical
  ext j
  apply (ENNReal.toReal_eq_toReal_iff' ((w.map f).toPMF.apply_ne_top j)
    ((w.toPMF.map f).apply_ne_top j)).mp
  rw [toPMF_real, PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum (fun i _ => by split_ifs; exacts [w.toPMF.apply_ne_top i, by simp])]
  simp only [Distribution.map]
  apply sum_congr rfl
  intro i _
  by_cases h : f i = j
  · subst j; simp
  · simp only [h, Ne.symm h, ↓reduceIte, ENNReal.toReal_zero]

/-- Interpret a rational table as a real probability table. -/
@[expose] def realify (w : Distribution α ℚ) : Distribution α ℝ :=
  ⟨fun i => (w.weight i : ℝ), fun i => by exact_mod_cast w.nonneg i, by
    exact_mod_cast w.total⟩

/-- Rational two-index mixtures retain their exact weights under interpretation. -/
theorem realify_pair (a b : α) (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    (pair a b q h₀ h₁).realify =
      pair a b (q : ℝ) (by exact_mod_cast h₀) (by exact_mod_cast h₁) := by
  classical
  ext i
  dsimp only [realify, pair]
  split_ifs <;> push_cast <;> rfl

/-- Rational expectations agree with their real interpretations. -/
theorem mean_realify (w : Distribution α ℚ) (f : α → ℚ) :
    w.realify.mean (fun i => (f i : ℝ)) = (w.mean f : ℝ) := by
  simp [Distribution.mean, realify]

end Cslib.Optimization.OneConstraint.Distribution
