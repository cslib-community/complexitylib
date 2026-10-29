/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.CriticalTree

/-! Critical clause trees for PPSZ: an explicit tree of height two whose cuts force a variable,
a cut that exists only at depth two, and a tree rooted at one variable for a solution that is not
isolated, which has no critical clause tree. -/

namespace ComplexityTests.PPSZCriticalTree

open Cslib.Logic.PL Cslib.BitString Cslib.Complexity Cslib.Complexity.PPSZ

/-- `x₀ ∧ (¬x₀ ∨ x₁)`: uniquely satisfied by `x₀ = x₁ = true`. -/
def φ : CNF (Fin 2) := [[(0, true)], [(0, false), (1, true)]]

theorem φ_sat : φ.eval (fun _ => true) = true := by decide

theorem φ_len : ∀ c ∈ φ, c.length ≤ 2 := by decide

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

/-- A clause labelling: flipping a set containing `x₀` violates `x₀`, and flipping `{x₁}`
violates `¬x₀ ∨ x₁`. -/
def C (p : List (Fin 2)) : Clause (Fin 2) :=
  if (0 : Fin 2) ∈ p then [(0, true)] else [(0, false), (1, true)]

theorem C_critical (h : ℕ) : IsCriticalTree φ (fun _ => true) h C := by
  intro p hp _
  by_cases h0 : (0 : Fin 2) ∈ p
  · simp [C, h0, φ, Clause.eval, flipOn_apply_of_mem (List.mem_toFinset.mpr h0)]
  · have h1 : (1 : Fin 2) ∈ p := by
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil p hp
      rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
      · exact absurd hy h0
      · exact hy
    simp [C, h0, φ, Clause.eval, flipOn_apply_of_mem (List.mem_toFinset.mpr h1),
      flipOn_apply_of_notMem (show (0 : Fin 2) ∉ p.toFinset by simpa using h0)]

-- The unique solution is isolated, so critical clause trees of every height exist.
example : ∃ C, IsCriticalTree φ (fun _ => true) 5 C :=
  exists_isCriticalTree (isIsolated_of_unique φ_unique 5)

-- The tree of `x₁` has the single child `x₀`, which is a leaf below depth two.
example : children C [1] = {0} := by decide
example : children C [0, 1] = ∅ := by decide

-- At depth one, the empty set is no cut; `{x₀}` is.
example : ¬Cut C ∅ 1 [1] := by decide
example : Cut C {0} 1 [1] := by decide

/-- At depth two every path dies out, so even the empty set is a cut. -/
theorem cut_two : Cut C ∅ 2 [1] := by decide

-- With `x₀` set, `x₁ = true` is implied by a single clause.
example : WImplied φ 1 (PPZ.restrict (fun _ => true) {0}) 1 true :=
  wImplied_of_cut (k := 2) (h := 1) φ_sat (C_critical 1) φ_len (by decide) (by decide)

-- With nothing set, two clauses imply `x₁ = true`.
example : WImplied φ 2 (PPZ.restrict (fun _ => true) ∅) 1 true :=
  wImplied_of_cut (k := 2) (h := 2) φ_sat (C_critical 2) φ_len (by decide) cut_two

-- The form of [Scheder, Lemma 3.2], read as a 3-CNF: `w = (3 - 1) ^ 3 = 8`.
example : WImplied φ 8 (PPZ.restrict (fun _ => true) ∅) 1 true :=
  wImplied_of_forall_descends (k := 3) (h := 2) le_rfl φ_sat (C_critical 2)
    (fun c hc => (φ_len c hc).trans (by decide)) (by decide) fun s hs => by
      obtain ⟨y, hy, hyA⟩ := cut_iff_forall_descends.mp cut_two s hs
      exact ⟨y, List.mem_append_left _ hy, hyA⟩

/-! ### A tree rooted at one variable -/

/-- The formula `x₀` on two variables: the solution `x₀ = x₁ = true` is not isolated, since
flipping `x₁` keeps it a solution. -/
def χ : CNF (Fin 2) := [[(0, true)]]

/-- No critical clause tree of height one exists: the root path `[x₁]` has no violated clause. -/
theorem not_isCriticalTree (C : List (Fin 2) → Clause (Fin 2)) :
    ¬IsCriticalTree χ (fun _ => true) 1 C := fun hC => by
  obtain ⟨hmem, heval⟩ := hC [1] (by simp) (by simp)
  simp only [χ, List.mem_singleton] at hmem
  rw [hmem] at heval
  simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval] at heval
  simp [flipOn_apply_of_notMem (show (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) by decide)] at heval

/-- The clause `x₀` labels a critical clause tree of every height rooted at `x₀`: every root path
through `x₀` flips `x₀`. -/
theorem isCriticalTreeAt_χ (h : ℕ) :
    IsCriticalTreeAt χ (fun _ => true) 0 h fun _ => [(0, true)] := fun p hp _ =>
  ⟨by simp [χ], by simp [Clause.eval, flipOn_apply_of_mem (List.mem_toFinset.mpr hp)]⟩

end ComplexityTests.PPSZCriticalTree
