/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Logics.Propositional.CSP.Planar.Embedding.Projection
import Complexity.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary

/-! Exact body extraction and actual semantic projection; nullary, repeated and point cases. -/

namespace ComplexityTests.PlanarProbeProjection

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary

-- A cutvertex meets two distinct indexed copies of the same unary constraint.
private abbrev repeated : CSP Unit ℕ := [((), [7]), ((), [7])]
private def repeatedWitness : Witness repeated [7] :=
  Witness.ofProbe (by decide) ⟨[2, 1, 4, 3, 0, 5]⟩ (by decide +kernel)

example : repeatedWitness.certificate = ⟨[2, 1, 4, 3, 0, 5]⟩ ∧
    bodyCertificate repeated repeatedWitness.certificate = ⟨[2, 1, 0, 3]⟩ := by decide +kernel

example : verifyRotationCertificate repeated ⟨[2, 1, 0, 3]⟩ = true :=
  repeatedWitness.body_accepted

-- The two body visits at label 7 are retained after the only boundary marker disappears.
example : (repeatedWitness.forgetHead (by decide)).certificate = ⟨[2, 1, 0, 3]⟩ ∧
    verify repeated [] (repeatedWitness.forgetHead (by decide)).certificate = true := by
  constructor
  · decide +kernel
  · exact (repeatedWitness.forgetHead (by decide)).accepted

-- Automatic body extraction requires distinct boundary names, but the boundary interface
-- itself permits repeated markers. Deleting one marker from an actual parallel bigon works.
private def repeatedBoundary : Witness ([] : CSP Unit ℕ) [7, 7] where
  certificate := ⟨[2, 3, 0, 1]⟩
  accepted := by decide +kernel

example : (repeatedBoundary.forgetHead (by decide)).certificate = ⟨[0, 1]⟩ ∧
    verify ([] : CSP Unit ℕ) [7] ⟨[0, 1]⟩ = true := by decide +kernel

-- True/false nullaries remain in the original body; both are isolated incidence points.
-- A sparse unused port supplies a further point/leaf case without any loop to its value.
private abbrev withNullaries : CSP Bool ℕ := [(true, []), (false, []), (true, [7]), (true, [7])]
private def nullaryWitness : Witness withNullaries [7, 2 ^ 250] :=
  Witness.ofProbe (by decide) ⟨[2, 1, 6, 3, 4, 7, 0, 5]⟩ (by decide +kernel)

example : bodyCertificate withNullaries nullaryWitness.certificate = ⟨[2, 1, 0, 3]⟩ ∧
    verifyRotationCertificate withNullaries ⟨[2, 1, 0, 3]⟩ = true := by decide +kernel

example : ¬withNullaries.Satisfiable (fun (r : Bool) (_ : List Bool) => r) := by
  rintro ⟨a, ha⟩
  simp [withNullaries, CSP.eval, Constraint.eval] at ha

-- Empty body/alphabet and zero boundary require no dart and no relation symbol.
private def emptyWitness : Witness ([] : CSP Empty ℕ) [] :=
  Witness.ofProbe (by decide) ⟨[]⟩ (by decide +kernel)

example : emptyWitness.certificate = ⟨[]⟩ ∧
    bodyCertificate ([] : CSP Empty ℕ) emptyWitness.certificate = ⟨[]⟩ := by decide +kernel

private def atom (n : ℕ) := PPGadget.atom (arity := fun (_ : Unit) => n)
  (sem := fun (_ : Unit) (a : List Bool) => a.all id) ()

-- The witness is for the existing PPGadget.project body, including its hidden label.
private def projected := (Witness.atom (fun (_ : Unit) => 3)
  (fun (_ : Unit) (a : List Bool) => a.all id) ()).projectHead

example : projected.certificate = ⟨[0, 3, 8, 5, 6, 1, 4, 9, 2, 7]⟩ := by
  unfold projected
  rw [GadgetWitness.projectHead_certificate]
  decide +kernel

example : ((atom 3).project 0).body =
    [((), [Sum.inr (0 : Fin 1), Sum.inl 0, Sum.inl 1])] := by rfl

example : verify ((atom 3).project 0).body (List.ofFn Sum.inl) projected.certificate = true :=
  projected.accepted

-- Unary projection reaches arity zero; a degree-five atom exercises the same constructor.
example : ((Witness.atom (fun (_ : Unit) => 1) (fun _ _ => true) ()).projectHead).certificate =
    ⟨[0, 1]⟩ := by
  rw [GadgetWitness.projectHead_certificate]
  decide +kernel

example : verify ((atom 5).project 0).body (List.ofFn Sum.inl)
    ⟨[0, 3, 16, 5, 14, 7, 12, 9, 10, 1, 8, 13, 6, 15, 4, 17, 2, 11]⟩ = true := by
  decide +kernel

-- The actual surviving port word is distinct; this is the guard used by probe extraction.
example : (List.ofFn (Sum.inl : Fin 2 → Fin 2 ⊕ Fin ((atom 3).project 0).numAux)).Nodup :=
  List.nodup_ofFn.mpr Sum.inl_injective

-- Apply the actual-body extraction theorem with its distinct-port hypothesis visible.
-- The source here is literally the structural probe on the existing semantic gadget body.
example : verifyRotationCertificate ((atom 3).project 0).body
    (bodyCertificate ((atom 3).project 0).body ⟨[0, 3, 8, 5, 6, 1, 4, 9, 2, 7]⟩) = true := by
  have hn : (List.ofFn
      (Sum.inl : Fin 2 → Fin 2 ⊕ Fin ((atom 3).project 0).numAux)).Nodup :=
    List.nodup_ofFn.mpr Sum.inl_injective
  apply bodyCertificate_accepted_of_probe ((atom 3).project 0).body (List.ofFn Sum.inl) hn
  decide +kernel

-- Existential projection retains all three original argument slots and their semantics.
example : ((atom 3).project 0).body.eval (fun (_ : Unit) (a : List Bool) => a.all id)
    (Sum.elim ![true, false] (fun _ => true)) = false := by decide +kernel

example : ((atom 3).project 0).body.eval (fun (_ : Unit) (a : List Bool) => a.all id)
    (Sum.elim ![true, true] (fun _ => true)) = true := by decide +kernel

end ComplexityTests.PlanarProbeProjection
