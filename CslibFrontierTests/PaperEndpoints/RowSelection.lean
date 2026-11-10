/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.RowSelection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Repeated exact-one rows, a genuinely nonunique system, and inconsistency. -/

open Cslib.LinearSystem Matrix

/-- Five repetitions of the same exact-one constraint on the first two variables. -/
@[expose] public def rows (_ : Fin 5) : Fin 3 → ℚ := ![1, 1, 0]

/-- Five repeated original exact-one rows have equivalent solutions after row selection.
The two witnesses differ on the first two variables; the third remains unused. -/
public theorem repeated_rows :
    ∃ s : Finset (Fin 5), s.card < 3 ∧
      ∀ u : Fin 3 → ℚ, (∀ i ∈ s, rows i ⬝ᵥ u = 1) ↔
        ∀ i, rows i ⬝ᵥ u = 1 := by
  obtain ⟨s, hcard, _, hsol⟩ := exists_original_rows_of_two_solutions rows (fun _ => 1)
    ![1, 0, 0] ![0, 1, 0]
    (by intro i; norm_num [rows, dotProduct, Fin.sum_univ_succ])
    (by intro i; norm_num [rows, dotProduct, Fin.sum_univ_succ])
    (by intro h; have := congrFun h 0; norm_num at this)
  exact ⟨s, hcard, hsol⟩

/-- Inconsistent equations do not admit the consistency witness required by selection. -/
example : ¬ ∃ x : Fin 1 → ℚ, ∀ i : Fin 2,
    (fun _ : Fin 1 => (1 : ℚ)) ⬝ᵥ x = (if i = 0 then 0 else 1) := by
  rintro ⟨x, hx⟩
  have h0 := hx 0
  have h1 := hx 1
  norm_num [dotProduct] at h0 h1
  exact zero_ne_one (h0.symm.trans h1)
