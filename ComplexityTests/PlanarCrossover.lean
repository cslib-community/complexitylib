/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
import Complexity.Computability.Complexity.Problems.SAT.Planar.CrossoverLayout
import Complexity.Logics.Propositional.CNF.ImplicationCycle

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.Crossover

-- The public fixed table keeps the existing cycle constructor's exact clause order.
example (v : Internal) : ring v = CNF.implicationCycle (List.ofFn (SplitVariable.copy v)) := rfl

example (v : Internal) : (ring v).eval (fun _ => true) = true :=
  (eval_ring_iff _ v).2 (fun _ => rfl)

-- A nonconstant local cycle is rejected, independently of which internal variable is split.
example : ∀ v : Internal, (ring v).eval (fun w => match w with
    | .copy _ i => i == 0
    | _ => false) = false := by decide +kernel

-- Opposite signals are equal within each pair; the two pairs remain independent.
example : Extends true true false false := (extends_iff _ _ _ _).2 ⟨rfl, rfl⟩
example : ¬ Extends true false false false := by
  rw [extends_iff]
  decide

-- The moved drawing modules still expose the same fixed geometric data.
example : incidenceRoutes.length = 154 := drawing_sizes.2
example (i : Fin 4) : (accessRoute i).length = 2 := rfl
