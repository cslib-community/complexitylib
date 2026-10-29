/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.Basic

/-! PPSZ with w-implication: a value that is 2-implied but not 1-implied, and the PPZ bound for
PPSZ on a uniquely satisfiable instance. -/

namespace ComplexityTests.PPSZ

open Cslib.Logic.PL Cslib.Complexity.PPSZ

/-- `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁)`: together the two clauses imply `x₀ = true`, neither does alone. -/
def χ : CNF (Fin 2) := [[(0, true), (1, true)], [(0, true), (1, false)]]

theorem none_agree (σ : Fin 2 → Bool) :
    ∀ y c, (fun _ => (none : Option Bool)) y = some c → σ y = c := by
  intro y c h
  simp at h

/-- With no values assigned, `x₀ = true` is 2-implied by `χ`. -/
theorem χ_wImplied_two : WImplied χ 2 (fun _ => none) 0 true := by
  refine ⟨χ, fun c hc => hc, le_rfl, fun σ _ h => ?_⟩
  have h1 := (CNF.eval_eq_true_iff σ χ).mp h [(0, true), (1, true)] (by simp [χ])
  have h2 := (CNF.eval_eq_true_iff σ χ).mp h [(0, true), (1, false)] (by simp [χ])
  simp only [Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Bool.or_false] at h1 h2
  revert h1 h2
  generalize σ 0 = a
  generalize σ 1 = b
  cases a <;> cases b <;> decide

/-- With no values assigned, `x₀ = true` is not 1-implied by `χ`. -/
theorem χ_not_wImplied_one : ¬ WImplied χ 1 (fun _ => none) 0 true := by
  rintro ⟨ψ, hψ, hlen, himp⟩
  -- Each clause of `χ` alone is satisfied by an assignment with `x₀ = false`.
  have key : ∀ c ∈ χ, ∃ σ : Fin 2 → Bool, σ 0 = false ∧ c.eval σ = true := by
    intro c hc
    simp only [χ, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨![false, true], rfl, by decide⟩
    · exact ⟨![false, false], rfl, by decide⟩
  rcases ψ with _ | ⟨c, _ | ⟨d, ψ⟩⟩
  · exact absurd (himp (fun _ => false) (none_agree _) rfl) (by decide)
  · obtain ⟨σ, hσ0, hσ⟩ := key c (hψ c (List.mem_singleton_self c))
    have := himp σ (none_agree σ) (by simp [hσ])
    rw [hσ0] at this
    exact absurd this (by decide)
  · simp at hlen

-- PPSZ with `w = 2` sets `x₀` first without guessing.
example : implied χ 2 (fun _ => none) 0 = some true :=
  implied_eq_some (σ := fun _ => true) (by decide) (none_agree _) χ_wImplied_two

-- PPSZ with `w = 1` (like PPZ) has to guess `x₀` first.
example : implied χ 1 (fun _ => none) 0 = none := by
  unfold implied
  split_ifs with h1 h2
  · exact absurd h1 χ_not_wImplied_one
  · exact absurd (h2.eq (σ := fun _ => true) (by decide) (none_agree _)) (by decide)
  · rfl

/-- `x₀ ∧ (¬x₀ ∨ x₁)`: uniquely satisfied by `x₀ = x₁ = true`, with clauses of at most two
literals. -/
def φ : CNF (Fin 2) := [[(0, true)], [(0, false), (1, true)]]

theorem φ_sat : φ.eval (fun _ => true) = true := by decide

theorem φ_unique : ∀ τ, φ.eval τ = true → τ = fun _ => true := by
  intro τ h
  have h0 : τ 0 = true := by
    have := (CNF.eval_eq_true_iff τ φ).mp h [(0, true)] (by simp [φ])
    simpa [Clause.eval, Literal.eval] using this
  have h1 : τ 1 = true := by
    have := (CNF.eval_eq_true_iff τ φ).mp h [(0, false), (1, true)] (by simp [φ])
    simpa [Clause.eval, Literal.eval, h0] using this
  funext i
  fin_cases i <;> assumption

-- One PPSZ round with `w = 3` finds the solution with probability at least
-- `2^{-(1 - 1/2) · 2} = 1/2`.
example : (2 : ℝ) ^ (-((1 - 1 / ((2 : ℕ) : ℝ)) * (2 : ℕ))) ≤
    ((round φ 3) fun x => some ((fun _ => true) x)).toReal :=
  round_success_ppz (by norm_num) (by norm_num) φ_sat φ_unique (by decide)

-- PPSZ outputs the solution at least as often as PPZ.
example : Cslib.Complexity.PPZ.round φ (fun x => some ((fun _ => true) x)) ≤
    round φ 1 (fun x => some ((fun _ => true) x)) :=
  ppz_round_apply_le le_rfl φ_sat

/-- `x₀`: satisfied by two of the four assignments, with unit clauses only. -/
def ψ : CNF (Fin 2) := [[(0, true)]]

-- With unit clauses PPSZ always finds a satisfying assignment: `2^{-(1 - 1/1) · 2} = 1`.
example : (1 : ℝ) ≤ ((round ψ 1).toOuterMeasure
    {τ | ∃ σ, ψ.eval σ = true ∧ τ = fun x => some (σ x)}).toReal :=
  calc
    (1 : ℝ) = 2 ^ (-((1 - 1 / ((1 : ℕ) : ℝ)) * (2 : ℕ))) := by norm_num
    _ ≤ _ := round_success_of_satisfiable_ppz le_rfl le_rfl ⟨fun _ => true, by decide⟩
      (by decide)

end ComplexityTests.PPSZ
