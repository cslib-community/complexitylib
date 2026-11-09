/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.TwoBoundary
import all CslibFrontier.Logics.Propositional.CNF.TwoBoundary

/-! Cases include no internal variables, empty terms, unused variables, and cancellation. -/

open Cslib.Logic.PL Cslib.Logic.PL.TwoBoundary

private def repeatedPositive : Fin 2 → List (List (Literal (Fin 1))) :=
  fun _ => [[(0, true)]]

example : Fintype.card {σ : Fin 1 ⊕ Fin 1 → Bool //
    (query [] 1 repeatedPositive false).eval σ = true} = 3 := by
  decide +kernel

example : Fintype.card {σ : Fin 1 ⊕ Fin 1 → Bool //
    (query [] 1 repeatedPositive true).eval σ = true} = 2 := by
  decide +kernel

example : Fintype.card {x : Fin 1 → Bool //
    CNF.eval x ([] : CNF (Fin 1)) = true ∧
      ∀ j, DNF.eval x (repeatedPositive j) = true} = 1 := by
  decide +kernel

example : query ([] : CNF (Fin 0)) 0 (fun _ => [[]]) false = [] := by
  decide +kernel

example : query ([] : CNF (Fin 0)) 0 (fun _ => [[]]) true = [[]] := by
  decide +kernel

example : query ([] : CNF (Fin 1)) 0 (fun _ => []) false = [] ∧
    query ([] : CNF (Fin 1)) 0 (fun _ => []) true = [] := by
  decide +kernel

public theorem query_counts (B : CNF (Fin 3)) (P : Fin 4 → List (List (Literal (Fin 3)))) :
    Fintype.card {x : Fin 3 → Bool // B.eval x = true ∧ ∀ j, DNF.eval x (P j) = true} =
      Fintype.card {σ : Fin 3 ⊕ Fin 3 → Bool // (query B 3 P false).eval σ = true} -
      Fintype.card {σ : Fin 3 ⊕ Fin 3 → Bool // (query B 3 P true).eval σ = true} :=
  counting_identity B P
