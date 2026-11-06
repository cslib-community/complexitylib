/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Optimization.OneConstraint
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Rational optima against arbitrary real randomization

For a finite one-constraint LP with rational data, a rational optimum supported
on at most two indices dominates every real feasible probability table. This
supplies the rationality step in [Wang2027], Theorem 1(2), PDF p. 7, without
assuming that the competing policies use rational private randomness.

## Main results

* `exists_rational_optimal_two`: a rational optimum against every feasible real table.
-/

public section
namespace Cslib.Optimization.OneConstraint
open Finset
variable {ι : Type*} [Fintype ι]

private theorem rational_vertex_le (p c : ι → ℚ) (η : ℚ) (w : Distribution ι ℝ)
    (hw : (η : ℝ) ≤ w.mean (fun i => (p i : ℝ))) :
    ∃ v : Distribution ι ℚ, v.support.card ≤ 2 ∧ η ≤ v.mean p ∧
      (v.mean c : ℝ) ≤ w.mean (fun i => (c i : ℝ)) := by
  classical
  obtain ⟨a,b,t,hmem,h₀,h₁,hp,hc⟩ := exists_vertex_le w
    (fun i => (p i : ℝ)) (fun i => (c i : ℝ)) (η : ℝ) hw
  have ht := (mem_vertices (fun i => (p i : ℝ)) (η : ℝ) t a b).mp hmem
  simp only [mem_insert, mem_singleton] at ht
  have hq : ∃ q : ℚ, (q : ℝ) = t := by
    rcases ht with rfl | rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨(η-p b)/(p a-p b), by push_cast; rfl⟩
  obtain ⟨q,rfl⟩ := hq
  have hq₀ : 0 ≤ q := by exact_mod_cast h₀
  have hq₁ : q ≤ 1 := by exact_mod_cast h₁
  refine ⟨pair a b q hq₀ hq₁, pair_support_card a b q hq₀ hq₁, ?_, ?_⟩
  · rw [pair_mean]
    exact_mod_cast hp
  · rw [pair_mean]
    push_cast
    exact hc

/-- A rational attained two-atom optimum competes against every real probability table.
The hypothesis is feasibility, not the existence or rationality of an optimizer. -/
theorem exists_rational_optimal_two (p c : ι → ℚ) (η : ℚ)
    (hfeas : ∃ w : Distribution ι ℝ, (η : ℝ) ≤ w.mean (fun i => (p i : ℝ))) :
    ∃ v : Distribution ι ℚ, v.support.card ≤ 2 ∧ η ≤ v.mean p ∧
      ∀ w : Distribution ι ℝ, (η : ℝ) ≤ w.mean (fun i => (p i : ℝ)) →
        (v.mean c : ℝ) ≤ w.mean (fun i => (c i : ℝ)) := by
  obtain ⟨w,hw⟩ := hfeas
  obtain ⟨u,_,hu,_⟩ := rational_vertex_le p c η w hw
  obtain ⟨v,hv,hvp,hvc⟩ := exists_optimal_two p c η ⟨u,hu⟩
  refine ⟨v,hv,hvp,?_⟩
  intro w hw
  obtain ⟨u,_,hu,huc⟩ := rational_vertex_le p c η w hw
  exact (show (v.mean c : ℝ) ≤ (u.mean c : ℝ) by exact_mod_cast hvc u hu).trans huc

end Cslib.Optimization.OneConstraint
