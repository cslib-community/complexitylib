/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Logics.Propositional.CSP.Planar.Embedding.Crossover
import Complexity.Logics.Propositional.CSP.Planar.Embedding.Atom
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Star

/-! Existing checker execution on actual gadget bodies and positional boundary probes. -/

namespace ComplexityTests.PlanarOrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary

example : verify Crossover.figureOneABody (List.ofFn Sum.inl)
    Crossover.figureOneABoundaryCertificate = true := Crossover.figureOneABoundary.accepted

example : verify Crossover.figureOneB.body (List.ofFn Sum.inl)
    Crossover.figureOneBBoundaryCertificate = true := Crossover.figureOneBBoundary.accepted

example : verify NonSelfDual.triangleBody (List.ofFn Sum.inl)
    NonSelfDual.triangleBoundaryCertificate = true := NonSelfDual.triangleBoundary.accepted

-- Inverting the whole rotation changes ternary/quaternary argument chirality.
example : verifyArgumentOrder
    (probeBody Crossover.figureOneABody (List.ofFn Sum.inl))
    ⟨(List.range Crossover.figureOneABoundaryCertificate.successor.length).map
      Crossover.figureOneABoundaryCertificate.successor.idxOf⟩ = false := by decide +kernel

-- Repeated boundary names remain separate probe edge occurrences at a cutvertex.
example : verify ([] : CSP Unit ℕ) [7, 7] ⟨[2, 3, 0, 1]⟩ = true := by decide +kernel

example : verify ([] : CSP Unit ℕ) [7] ⟨[0, 1]⟩ = true := by decide +kernel

example : verify ([] : CSP Empty ℕ) [] ⟨[]⟩ = true := by decide +kernel

-- Both nullary truth values give isolated constraint vertices; truth is a semantic issue.
example : verify ([(true, []), (false, [])] : CSP Bool ℕ) [] ⟨[]⟩ = true := by decide +kernel

example : ¬ CSP.Satisfiable (fun (r : Bool) (_ : List Bool) => r)
    ([(true, []), (false, [])] : CSP Bool ℕ) := by
  simp [CSP.Satisfiable, CSP.eval, Constraint.eval]

-- The general atom-star theorem includes zero, one and unrestricted higher arity.
example : (Graph.RotationSystem.starRotation 0).NumericalGenusZero :=
  Graph.RotationSystem.numericalGenusZero_starRotation 0

example : (Graph.RotationSystem.starRotation 1).NumericalGenusZero :=
  Graph.RotationSystem.numericalGenusZero_starRotation 1

example : (Graph.RotationSystem.starRotation 31).NumericalGenusZero :=
  Graph.RotationSystem.numericalGenusZero_starRotation 31

private def atom (n : ℕ) := PPGadget.atom (arity := fun (_ : Unit) => n)
  (sem := fun (_ : Unit) (_ : List Bool) => true) ()

example : verifyRotationCertificate (atom 0).body (atomBodyCertificate 0) = true := by
  decide +kernel

example : verifyRotationCertificate (atom 1).body (atomBodyCertificate 1) = true := by
  decide +kernel

example : verifyRotationCertificate (atom 5).body (atomBodyCertificate 5) = true := by
  decide +kernel

example : verifyRotationCertificate (atom 31).body (atomBodyCertificate 31) = true :=
  atomBodyCertificate_accepted _ _ _

example : (Witness.empty (Rel := Empty) (List.finRange 31)
    (List.nodup_finRange 31)).certificate = atomBodyCertificate 31 := rfl

example : verify ([] : CSP Unit ℕ) [0, 1, 0, 1]
    ⟨[4, 3, 6, 5, 0, 7, 2, 1]⟩ = false := by decide +kernel

end ComplexityTests.PlanarOrderedBoundary
