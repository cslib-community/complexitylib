/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverNativeRisk
import Mathlib.Tactic

/-!
# Correlated posterior risk recurrence

Two reports share one four-valued hidden seed. The second covers with probability
3/4 marginally but only 1/2 after the first failure. The conditional envelopes
below are derived from that joint experiment, rather than supplied as kernel laws.
-/

noncomputable section
open Cslib Cslib.Probability StochasticOracle PartialCover
open Cslib.Optimization.OneConstraint
open scoped ENNReal

private def I : Instance (Fin 1) (Fin 1) where
  ground := {0}
  sets _ := {0}
  sets_subset _ := Finset.Subset.refl _
  weight _ := 1
  weight_nonneg _ := by norm_num
  dual _ := 1
  dual_nonneg _ := by norm_num
  dual_feasible _ := by norm_num

private def response (k : ℕ) (a : Fin 4) : Finset (Fin 1) :=
  if a.val < (if k = 0 then 2 else 3) then {0} else ∅
private def μ := PMF.uniformOfFintype (Fin 4)
private def K := Disintegration.kernel μ response

private theorem families (P : Finset (Fin 1)) : P = ∅ ∨ P = {0} := by
  by_cases h : 0 ∈ P
  · right; ext i; fin_cases i; simpa using h
  · left; ext i; fin_cases i; simpa using h

private theorem mass (h : List (Finset (Fin 1)))
    (hh : h = [] ∨ h = [∅]) : (K h).weight {0} = 1 / 2 := by
  classical
  have hf := PMF.posterior_map_factor μ (Disintegration.history response h.length)
    (response h.length) h ({0} : Finset (Fin 1))
  have hr := congrArg ENNReal.toReal hf
  have hleft : (μ.map (Disintegration.history response h.length) h).toReal =
      if h = [] then 1 else 1 / 2 := by
    obtain rfl | rfl := hh <;>
      norm_num [μ, response, Disintegration.history, PMF.map_apply, tsum_fintype,
        Fin.sum_univ_succ, PMF.uniformOfFintype_apply, ENNReal.toReal_add,
        ENNReal.toReal_inv]
  have hright : ((μ.map fun a =>
      (Disintegration.history response h.length a, response h.length a)) (h, {0})).toReal =
      if h = [] then 1 / 2 else 1 / 4 := by
    obtain rfl | rfl := hh <;>
      norm_num [μ, response, Disintegration.history, PMF.map_apply, tsum_fintype,
        Fin.sum_univ_succ, PMF.uniformOfFintype_apply, ENNReal.toReal_add,
        ENNReal.toReal_inv]
  rw [ENNReal.toReal_mul, hleft, hright] at hr
  change (((PMF.posterior μ (Disintegration.history response h.length) h).map
    (response h.length)) {0}).toReal = _
  obtain rfl | rfl := hh <;> norm_num at hr ⊢ <;> linarith

-- Unfold the concrete singleton instance inside the classical local test.
set_option backward.isDefEq.respectTransparency false in
private theorem admissible : I.Admissible 1 (1 / 2) K [] ∅ [{0}, {0}] := by
  classical
  have event (h : List (Finset (Fin 1))) (hh : h = [] ∨ h = [∅]) :
      Instance.event (K h) (fun P => I.Certified 1 ∅ P ∧ 0 ∈ I.covered P) = 1 / 2 := by
    unfold Instance.event Distribution.mean
    calc
      _ = ∑ P, (K h).weight P * (if P = {0} then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro P _
        obtain rfl | rfl := families P <;>
          norm_num [Instance.Certified, Instance.covered, Instance.cost, I]
      _ = (K h).weight {0} := by simp
      _ = 1 / 2 := mass h hh
  constructor
  · intro e he _
    have : e = 0 := by simpa using he
    subst e
    exact (event [] (Or.inl rfl)).ge
  · intro P _
    obtain rfl | rfl := families P
    · constructor
      · intro e he _
        have : e = 0 := by simpa using he
        subst e
        simpa [Instance.step, Instance.Certified, Instance.covered, I] using
          (event [∅] (Or.inr rfl)).ge
      · intro _ _; trivial
    · constructor
      · intro e he hn
        have : e = 0 := by simpa using he
        subst e
        norm_num [Instance.step, Instance.Certified, Instance.covered, Instance.cost, I] at hn
      · intro _ _; trivial

-- Positive, genuinely correlated two-report risk; no independence or target-law premise.
example : (3 / 4 : ℝ) ≤
    ((μ.map fun a => decide (I.covered
      (Disintegration.retained I 1 (Disintegration.history response 2 a)) = I.ground ∧
        I.cost (Disintegration.retained I 1 (Disintegration.history response 2 a)) ≤
          1 * ∑ e ∈ I.ground, I.dual e)) true).toReal := by
  have h := Disintegration.risk_bound I 1 μ response [{0}, {0}]
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) admissible
  convert h using 1; norm_num [I, Instance.chances]
