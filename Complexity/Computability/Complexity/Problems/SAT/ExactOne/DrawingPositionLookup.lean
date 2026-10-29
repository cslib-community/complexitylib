/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingPositions
import Mathlib.Data.List.GetD

/-!
# Local-to-global actual variable position lookup

## Main results

* `positiveVariablePoint_profile_auxiliary`: a private local profile variable resolves to its
  prescribed actual clause-box point.

## References

This is an elementary consequence of the actual finite position-table construction.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- A local private variable resolves to its own point in the original clause's actual box. -/
theorem positiveVariablePoint_profile_auxiliary (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {c : Clause ℕ} {i : ℕ} (hci : (c, i) ∈ φ.zipIdx)
    {w : CNF.PositiveExactOneCompile.Variable ℕ} {j : ℕ}
    (hwj : (w, j) ∈ (profileVariables (clauseProfile c)).zipIdx)
    (ha : ∀ n, w ≠ Sum.inl (Sum.inl n)) :
    positiveVariablePoint φ d
      (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c w) =
        positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition j := by
  apply positiveVariablePoint_auxiliary φ d
  apply List.mem_flatMap.mpr
  refine ⟨(c, i), hci, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨(w, j), hwj, ?_⟩
  rcases w with (n | ⟨a, b⟩) | ⟨⟨a, b⟩, s⟩
  · exact False.elim (ha n rfl)
  · rfl
  · rfl

/-- Indexed lookup of an actual local private variable has its prescribed actual point. -/
theorem positiveVariablePoint_profile_auxiliary_getD (φ : CNF ℕ) (d : Graph.OrthogonalDrawing)
    {c : Clause ℕ} {i : ℕ} (hci : (c, i) ∈ φ.zipIdx) {j : ℕ}
    (hj : j < (profileVariables (clauseProfile c)).length)
    (ha : ∀ n, (profileVariables (clauseProfile c)).getD j (.inl (.inl 0)) ≠
      Sum.inl (Sum.inl n)) :
    positiveVariablePoint φ d
      (profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c
        ((profileVariables (clauseProfile c)).getD j (.inl (.inl 0)))) =
          positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition j := by
  apply positiveVariablePoint_profile_auxiliary φ d hci _ ha
  apply List.mem_zipIdx_iff_getElem?.mpr
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩

end Cslib.Complexity.SAT.ExactOne
