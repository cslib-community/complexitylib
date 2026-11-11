/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable
import Mathlib.Tactic

/-!
# Disintegration of a finite private state by an observed action

The posterior is constructed by normalization on positive-probability actions.
Null actions use the original law. The joint law and all subsequent observable
expectations are preserved, including computations using the retained private
state. This is a finite lemma, with no machine representation premise.

## Main results

* `posterior_factor`: exact joint mass, including null observations.
* `posterior_bind`: equality for every private-state-dependent continuation.
-/

public section
noncomputable section
namespace Cslib.Optimization.OneConstraint.Distribution
open Finset
variable {S A B : Type} [Fintype S] [Fintype A] [Fintype B]

open scoped Classical in
/-- Conditional private-state law given its observed action. Null actions use the
prior as a harmless completion, without any nonempty action-type assumption. -/
@[expose] def posterior (w : Distribution S ℝ) (action : S → A) (a : A) :
    Distribution S ℝ :=
  if h : 0 < (w.map action).weight a then
    { weight := fun s => if action s = a then w.weight s / (w.map action).weight a else 0
      nonneg := fun s => by
        split_ifs
        · exact div_nonneg (w.nonneg s) h.le
        · exact le_rfl
      total := by
        have he (s : S) :
            (if action s = a then w.weight s / (w.map action).weight a else 0) =
              (if action s = a then w.weight s else 0) / (w.map action).weight a := by
          split_ifs <;> simp
        simp only [he, ← sum_div]
        exact div_self (ne_of_gt h) }
  else w

open scoped Classical in
/-- The conditional joint mass is the original private mass on its action fiber,
including null actions. This is the disintegration identity, not a hypothesis. -/
theorem posterior_factor (w : Distribution S ℝ) (action : S → A) (a : A) (s : S) :
    (w.map action).weight a * (w.posterior action a).weight s =
      if action s = a then w.weight s else 0 := by
  classical
  by_cases h : 0 < (w.map action).weight a
  · simp only [posterior, h, dite_true]
    split_ifs
    · field_simp
    · exact mul_zero _
  · have hz : (w.map action).weight a = 0 :=
      le_antisymm (le_of_not_gt h) ((w.map action).nonneg a)
    have hs : action s = a → w.weight s = 0 := by
      intro he
      have hb := single_le_sum (fun t (_ : t ∈ (univ : Finset S)) =>
        show 0 ≤ if action t = a then w.weight t else 0 by
          split_ifs <;> simp [w.nonneg]) (mem_univ s)
      change (if action s = a then w.weight s else 0) ≤ (w.map action).weight a at hb
      rw [he, ite_eq_left rfl, hz] at hb
      exact le_antisymm hb (w.nonneg s)
    rw [hz, zero_mul]
    split_ifs with he
    · exact (hs he).symm
    · rfl

/-- Disintegrating before any private-state-dependent continuation preserves the
complete joint distribution of action and final result. -/
theorem posterior_bind (w : Distribution S ℝ) (action : S → A)
    (next : S → A → Distribution B ℝ) :
    (w.map action).bind (fun a => (w.posterior action a).bind (fun s => next s a)) =
      w.bind (fun s => next s (action s)) := by
  classical
  ext t
  simp only [Distribution.bind, mul_sum, ← mul_assoc, posterior_factor]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  rw [sum_eq_single (action s)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

end Cslib.Optimization.OneConstraint.Distribution
