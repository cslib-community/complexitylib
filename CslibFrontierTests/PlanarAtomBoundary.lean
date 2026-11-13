/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-! Actual atom/probe tables and indexed duplicate-constraint chirality cases. -/

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary

private def atom (n : ℕ) := PPGadget.atom (arity := fun (_ : Unit) => n)
  (sem := fun (_ : Unit) (_ : List Bool) => false) ()

example : verify (atom 0).body (List.ofFn Sum.inl) (atomBoundaryCertificate 0) = true := by
  decide +kernel

example : verify (atom 1).body (List.ofFn Sum.inl) (atomBoundaryCertificate 1) = true := by
  decide +kernel

example : verify (atom 3).body (List.ofFn Sum.inl) (atomBoundaryCertificate 3) = true := by
  decide +kernel

example (n : ℕ) : verify (atom n).body (List.ofFn Sum.inl) (atomBoundaryCertificate n) = true :=
  atomBoundaryCertificate_accepted (fun (_ : Unit) => n) (fun _ _ => false) ()

example : bodyCertificate (atom 3).body (atomBoundaryCertificate 3) = ⟨[0, 3, 2, 5, 4, 1]⟩ := by
  decide +kernel

private abbrev repeated : CSP Unit (Fin 3) := [⟨(), [0, 1, 2]⟩, ⟨(), [0, 1, 2]⟩]
private abbrev reversed : CSP Unit (Fin 3) := [⟨(), [0, 1, 2]⟩, ⟨(), [0, 2, 1]⟩]

-- Both literal constraint positions survive. Their fixed forward argument rotations
-- produce a positive-genus rotation when the two ternary words have the same chirality.
example : verifyArgumentOrder repeated ⟨[6, 3, 8, 5, 10, 1, 0, 9, 2, 11, 4, 7]⟩ = true := by
  decide +kernel

example : verifyRotationCertificate repeated ⟨[6, 3, 8, 5, 10, 1, 0, 9, 2, 11, 4, 7]⟩ = false := by
  decide +kernel

example : verifyRotationCertificate reversed ⟨[6, 3, 10, 5, 8, 1, 0, 9, 4, 11, 2, 7]⟩ = true := by
  decide +kernel

-- Global mirroring retains a graph sphere rotation but reverses the prescribed ternary
-- argument order. It cannot silently supply a boundary witness for the original scopes.
example : Graph.RotationCertificate.verifyGenusZero
    (incidenceGraph (probeBody (atom 3).body (List.ofFn Sum.inl)))
      ⟨[10, 5, 8, 1, 6, 3, 4, 11, 2, 7, 0, 9]⟩ = true := by decide +kernel

example : verifyRotationCertificate (probeBody (atom 3).body (List.ofFn Sum.inl))
    ⟨[10, 5, 8, 1, 6, 3, 4, 11, 2, 7, 0, 9]⟩ = false := by decide +kernel
