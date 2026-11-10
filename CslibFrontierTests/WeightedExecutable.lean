/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Logics.Propositional.CNF.WeightedExecutable

/-! # Executable bounded-demand query clients -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow

namespace WeightedExecutableTests

/-- A mixed-sign row whose second weight exceeds its demand. -/
def row : Row (Fin 3) 1 where
  support := {0, 1}
  sign := fun i => i == 0
  weight := fun i => if i == 0 then 1 else 2
  demand := 1
  positive := by intro i hi; split <;> decide
  bounded := by decide
  capped := by intro i hi; split <;> decide

example : boundedLists ([] : List ℕ) 2 = [[]] := by decide
example : (boundedLists [0, 1, 2] 1).length = 4 := by decide
example : upperList row = [[(1, true)], [(0, false), (1, true)]] := by decide
example : attainmentList row = [[(0, true)]] := by decide
example : executableBase (fun _ : Fin 2 => row) = upperList row := by decide
example : (executableQuery (fun _ : Fin 2 => row) false).eval
    (Sum.elim (fun _ => true) (fun _ => false)) = true := by decide
example : (executableQuery (fun _ : Fin 2 => row) true).eval
    (Sum.elim (fun _ => true) (fun _ => false)) = false := by decide
example (σ : Fin 3 ⊕ Fin 1 → Bool) (β : Bool) :
    (executableQuery (fun _ : Fin 2 => row) β).eval σ =
      (globalQuery (fun _ : Fin 2 => row) β).eval σ := executableQuery_eval _ _ _

/-- Empty support and zero demand retain the true empty attainment term. -/
def emptyRow : Row (Fin 0) 0 where
  support := ∅
  sign := fun _ => false
  weight := fun _ => 1
  demand := 0
  positive := by simp
  bounded := by decide
  capped := by simp

example : upperList emptyRow = [] := by decide
example : attainmentList emptyRow = [[]] := by decide
example : executableQuery (fun _ : Fin 1 => emptyRow) false = [] := by decide
example : (executableQuery (fun _ : Fin 1 => emptyRow) true).eval
    (fun x => Sum.elim Fin.elim0 Fin.elim0 x) = false := by decide

end WeightedExecutableTests
