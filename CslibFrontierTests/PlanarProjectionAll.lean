/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetCyclic
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-! Actual middle/wrap projection bodies and semantics, cyclic rotation, and point cases. -/

namespace CslibFrontierTests.PlanarProjectionAll

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary

private abbrev arity (_ : Unit) := 3
private def sem (_ : Unit) (a : List Bool) : Bool := decide (a = [true, false, true])
private abbrev atom := PPGadget.atom (arity := arity) (sem := sem) ()
private noncomputable def middle := (Witness.atom arity sem ()).project (1 : Fin 3)
private noncomputable def last := (Witness.atom arity sem ()).project (2 : Fin 3)
private noncomputable def cyclic := (Witness.atom arity sem ()).rotate

-- These are the existing original-language bodies: no argument of the original atom is erased.
example : (atom.project (1 : Fin 3)).body =
    [((), [Sum.inl 0, Sum.inr (0 : Fin 1), Sum.inl 1])] := by rfl

example : (atom.project (2 : Fin 3)).body =
    [((), [Sum.inl 0, Sum.inl 1, Sum.inr (0 : Fin 1)])] := by rfl

example : (atom.relabelFree (fun i => i + 1)).body =
    [((), [Sum.inl 1, Sum.inl 2, Sum.inl 0])] := by rfl

example : verify (atom.project (1 : Fin 3)).body (List.ofFn Sum.inl) middle.certificate = true :=
  middle.accepted

example : verify (atom.project (2 : Fin 3)).body (List.ofFn Sum.inl) last.certificate = true :=
  last.accepted

example : verify (atom.relabelFree (fun i => i + 1)).body (List.ofFn Sum.inl)
    cyclic.certificate = true := cyclic.accepted

-- The extraction theorem's actual original body/probe and canonical Nodup premise are visible.
example : verifyRotationCertificate (atom.project (1 : Fin 3)).body
    (bodyCertificate (atom.project (1 : Fin 3)).body middle.certificate) = true := by
  have hn : (List.ofFn
      (Sum.inl : Fin 2 → Fin 2 ⊕ Fin (atom.project (1 : Fin 3)).numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  exact bodyCertificate_accepted_of_probe _ (List.ofFn Sum.inl) hn _ middle.probe_accepted

example : (atom.project (1 : Fin 3)).body.eval sem
    (Sum.elim ![true, true] (fun _ => false)) = true ∧
    (atom.project (1 : Fin 3)).body.eval sem
      (Sum.elim ![true, true] (fun _ => true)) = false := by decide +kernel

example : (atom.relabelFree (fun i => i + 1)).body.eval sem
    (Sum.elim ![true, true, false] Fin.elim0) = true ∧
    (atom.relabelFree (fun i => i + 1)).body.eval sem
      (Sum.elim ![true, false, true] Fin.elim0) = false := by decide +kernel

-- Projection at the final boundary position still permits an original degree-five constraint.
private abbrev atomFive := PPGadget.atom (arity := fun (_ : Unit) => 5)
  (sem := fun (_ : Unit) (_ : List Bool) => true) ()

example : verify (atomFive.project (4 : Fin 5)).body (List.ofFn Sum.inl)
    ⟨[16, 3, 14, 5, 12, 7, 10, 9, 8, 1, 6, 13, 4, 15, 2, 17, 0, 11]⟩ = true := by
  decide +kernel

-- Empty original alphabet, all ports unused, and non-head deletion retain survivor order.
private noncomputable def unused :=
  (Witness.empty (Rel := Empty) [2 ^ 250, 7, 9] (by decide)).forgetAt 1 (by decide) (by decide)

example : verify ([] : CSP Empty ℕ) [2 ^ 250, 9] unused.certificate = true := unused.accepted

-- Original false/true nullaries stay present when an unused final port is hidden.
private abbrev points : CSP Bool ℕ := [(false, []), (true, [])]
private def pointWitness : Witness points [2 ^ 250, 7, 9] :=
  Witness.ofProbe (by decide) ⟨[0, 3, 2, 5, 4, 1]⟩ (by decide +kernel)

example : verify points [2 ^ 250, 7]
    (pointWitness.forgetAt 2 (by decide) (by decide)).certificate = true :=
  (pointWitness.forgetAt 2 (by decide) (by decide)).accepted

-- Generic word operations keep positional duplicates, rather than deleting by value.
example : ([7, 7, 9] : List ℕ).eraseIdx 1 = [7, 9] ∧
    (List.ofFn (Fin.cons 7 ![7, 9] ∘ finRotate 3)) = [7, 9, 7] := by decide +kernel

example : (List.ofFn (fun (_ : Fin 0) => (7 : ℕ))).reverse = [] := by decide +kernel

end CslibFrontierTests.PlanarProjectionAll
