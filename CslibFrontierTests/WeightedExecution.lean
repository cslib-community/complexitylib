/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import CslibFrontier.Logics.Propositional.CNF.WeightedExecution

/-! # Actual original-input dispatch and computed solver branches -/

open Cslib.Logic.PL Cslib.Logic.PL.WeightedRow

namespace WeightedExecutionTests

/-- Inspect computational content without comparing function-valued queries. -/
def view {n d : ℕ} : CountingPlan n d → ℕ ⊕ ℕ
  | .direct a => .inl a
  | .queries k _ _ _ _ => .inr k

/-- One positive occurrence, with an independently chosen signed target. -/
def unitRow (n : ℕ) (i : Fin n) (target : ℤ) : Occurrences n 1 where
  var := fun _ => i
  sign := fun _ => true
  weight := fun _ => 1
  positive := by intro j; decide
  target := target

example : view (executableOriginalCountingPlan
    (fun _ : Fin 1 => unitRow 1 0 1) (d := 0) (by decide)).val = .inl 1 := by
  decide

example : view (executableOriginalCountingPlan
    (fun _ : Fin 1 => unitRow 3 0 (-1)) (d := 0) (by decide)).val = .inl 0 := by
  decide

example : view (executableOriginalCountingPlan
    (fun i : Fin 2 => unitRow 2 i 1) (d := 0) (by decide)).val = .inl 1 := by
  decide

/-- Duplicate rows give actual positive deficient rank, with no basis advice. -/
example : view (executableOriginalCountingPlan
    (fun _ : Fin 2 => unitRow 3 0 1) (d := 0) (by decide)).val = .inr 0 := by
  decide

/-- Two inconsistent original equations on the same variable. -/
example : view (executableOriginalCountingPlan
    (fun i : Fin 2 => unitRow 2 0 (if i == 0 then 0 else 1))
    (d := 0) (by decide)).val = .inl 0 := by
  decide

/-- Full computed rank with a fractional rational candidate is rejected by Booleanity. -/
def fractionalRows (i : Fin 2) : Occurrences 2 1 where
  var := fun _ => i
  sign := fun _ => true
  weight := fun _ => if i == 0 then 2 else 1
  positive := by intro j; split <;> decide
  target := if i == 0 then 1 else 0

example : view (executableOriginalCountingPlan fractionalRows (d := 1)
    (by decide)).val = .inl 0 := by decide

example : view (executableOriginalCountingPlan
    (fun j : Fin 0 => Fin.elim0 j : Fin 0 → Occurrences 3 0)
    (d := 0) (by intro j; exact Fin.elim0 j)).val = .inl 8 := by decide

example : view (executableOriginalCountingPlan
    (fun j : Fin 0 => Fin.elim0 j : Fin 0 → Occurrences 0 0)
    (d := 0) (by intro j; exact Fin.elim0 j)).val = .inl 1 := by decide

/-- A retained zero equation tests the computed rank-zero branch. -/
def zeroRow : Row (Fin 2) 0 where
  support := ∅
  sign := fun _ => false
  weight := fun _ => 1
  demand := 0
  positive := by simp
  bounded := by decide
  capped := by simp

example : view (executableCountingPlan [.row zeroRow]).val = .inl 4 := by decide

/-- Actual repeated opposite polarities aggregate to an unattainable demand. -/
def mixedRow : Occurrences 3 3 where
  var := ![0, 0, 1]
  sign := ![true, false, true]
  weight := ![3, 1, 2]
  positive := by decide
  target := 2

example : view (executableOriginalCountingPlan (fun _ : Fin 1 => mixedRow)
    (d := 1) (by decide)).val = .inr 0 := by decide

/-- Materialized fractional full-rank case: consistency is true, Booleanity is false. -/
def fractionalNormalized : List (Normalized 2 1) :=
  (List.finRange 2).map fun i => (fractionalRows i).normalize 1 (by decide +revert)

example : (cappedBasis fractionalNormalized).length = 2 := by decide
example : Cslib.LinearSystem.rectangularConsistent 2 (cappedMatrix fractionalNormalized)
    (cappedRhs fractionalNormalized) = true := by decide
example : Cslib.LinearSystem.rectangularBoolean 2 (cappedMatrix fractionalNormalized)
    (cappedRhs fractionalNormalized) = false := by decide

/-- Test-only exhaustive oracle for the small concrete queries below. -/
def oracleCount {n d : ℕ} : CountingPlan n d → ℕ
  | .direct a => a
  | .queries k q _ _ _ =>
    ((Finset.univ : Finset (Fin n ⊕ Fin k → Bool)).filter fun σ => (q false).eval σ).card -
      ((Finset.univ : Finset (Fin n ⊕ Fin k → Bool)).filter fun σ => (q true).eval σ).card

example : oracleCount (executableOriginalCountingPlan (fun _ : Fin 1 => mixedRow)
    (d := 1) (by decide)).val = 0 := by decide

example : oracleCount (executableOriginalCountingPlan
    (fun _ : Fin 2 => unitRow 3 0 1) (d := 0) (by decide)).val = 4 := by decide

end WeightedExecutionTests
