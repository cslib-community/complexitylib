/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF.MonotoneCoupling
import Mathlib.Tactic.NormNum

/-!
# Finite monotone coupling clients

The forward example forces a deterministic increasing pair. The reverse example shows that
the upper-event hypothesis excludes a reversed pair, rather than being vacuous.
-/

namespace Cslib.Probability.PMF

/-- Increasing deterministic laws admit a coupling with both specified marginals. -/
example : ∃ γ : PMF (Fin 2 × Fin 2),
    γ.map Prod.fst = PMF.pure 0 ∧ γ.map Prod.snd = PMF.pure 1 ∧
      ∀ z ∈ γ.support, z.1 ≤ z.2 := by
  apply exists_monotone_coupling
  intro U hU
  simp only [PMF.pure_apply, apply_ite, ENNReal.toReal_one,
    ENNReal.toReal_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
  by_cases h : (0 : Fin 2) ∈ U
  · simp [h, hU (show (0 : Fin 2) ≤ 1 by decide) h]
  · simp only [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- A joint law with reversed deterministic marginals cannot be supported on ordered pairs. -/
example : ¬ ∃ γ : PMF (Fin 2 × Fin 2),
    γ.map Prod.fst = PMF.pure 1 ∧ γ.map Prod.snd = PMF.pure 0 ∧
      ∀ z ∈ γ.support, z.1 ≤ z.2 := by
  rintro ⟨γ, hl, hr, ho⟩
  have hh := upperSet_le_of_monotone_coupling (PMF.pure 1) (PMF.pure 0) γ hl hr ho
    (U := Set.Ici 1) (fun _ _ hxy hx => hx.trans hxy)
  norm_num [PMF.pure_apply, Set.indicator, Set.mem_Ici] at hh

end Cslib.Probability.PMF
