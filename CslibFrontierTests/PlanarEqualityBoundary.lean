/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Equality
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import CslibFrontier.Foundations.Data.List.IdxOfIdentification

/-! Exact adjacent-equality output, original-language NAE disequality, OneHot pins and points. -/

namespace CslibFrontierTests.PlanarEqualityBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary Graph

private abbrev arity (_ : Unit) := 3
private def naeSem (_ : Unit) (scope : List Bool) : Bool :=
  decide (scope.count true ≠ 0 ∧ scope.count true ≠ 3)
private def hotSem (_ : Unit) (scope : List Bool) : Bool := decide (scope.count true = 1)
private abbrev naeAtom := PPGadget.atom (arity := arity) (sem := naeSem) ()
private abbrev hotAtom := PPGadget.atom (arity := arity) (sem := hotSem) ()
private noncomputable def naeBoundary := (Witness.atom arity naeSem ()).equalDrop
private noncomputable def hotBoundary := (Witness.atom arity hotSem ()).equalDrop
private abbrev expected : RotationCertificate := ⟨[8, 3, 0, 5, 6, 1, 4, 9, 2, 7]⟩

-- Complete generated table, followed by execution of both actual checks on that exact table.
example : naeBoundary.certificate = expected := by
  unfold naeBoundary
  rw [GadgetWitness.equalDrop_certificate]
  decide +kernel

example : hotBoundary.certificate = expected := by
  unfold hotBoundary
  rw [GadgetWitness.equalDrop_certificate]
  decide +kernel

example : naeAtom.equalDrop.body = [⟨(), [Sum.inl 0, Sum.inl 0, Sum.inl 1]⟩] := rfl

example : verify naeAtom.equalDrop.body (List.ofFn Sum.inl) expected = true := by
  decide +kernel

example : verify hotAtom.equalDrop.body (List.ofFn Sum.inl) expected = true := by
  decide +kernel

-- NAE(x,x,y) supplies disequality internally, with the original symbol and no auxiliaries.
private def derivedN : PPGadget arity naeSem RelationMinor.disequality :=
  naeAtom.equalDrop.retarget (by
    unfold RelationMinor.disequality RelationMinor.adjacent booleanRelation
    decide +kernel)

private noncomputable def derivedNBoundary : GadgetWitness derivedN := naeBoundary

example : derivedN.numAux = 0 ∧ derivedN.body = naeAtom.equalDrop.body := ⟨rfl, rfl⟩
example : verify derivedN.body (List.ofFn Sum.inl) derivedNBoundary.certificate = true :=
  derivedNBoundary.accepted
example (a : Fin 2 → Bool) : a ∈ RelationMinor.disequality ↔
    ∃ b, derivedN.body.eval naeSem (Sum.elim a b) = true := derivedN.correct a

-- OneHot(x,x,y) forces x=false,y=true; hide x to obtain the actual unary-one gadget.
private def derivedOne : PPGadget arity hotSem (RelationMinor.pin true) :=
  (hotAtom.equalDrop.project 0).retarget (by
    unfold RelationMinor.pin RelationMinor.project RelationMinor.adjacent booleanRelation
    decide +kernel)
private noncomputable def derivedOneBoundary : GadgetWitness derivedOne := hotBoundary.projectHead

example : derivedOne.body = [⟨(), [Sum.inr (0 : Fin 1), Sum.inr (0 : Fin 1), Sum.inl 0]⟩] := rfl
example : derivedOneBoundary.certificate = ⟨[2, 3, 0, 5, 6, 1, 4, 7]⟩ := by
  unfold derivedOneBoundary
  rw [GadgetWitness.projectHead_certificate]
  have hc : hotBoundary.certificate = expected := by
    unfold hotBoundary
    rw [GadgetWitness.equalDrop_certificate]
    decide +kernel
  rw [hc]
  decide +kernel
example : verify derivedOne.body (List.ofFn Sum.inl) ⟨[2, 3, 0, 5, 6, 1, 4, 7]⟩ = true := by
  decide +kernel
example (a : Fin 1 → Bool) : a ∈ RelationMinor.pin true ↔
    ∃ b, derivedOne.body.eval hotSem (Sum.elim a b) = true := derivedOne.correct a

-- Hide the other coordinate: the existing arbitrary-coordinate projection gives unary zero.
private def derivedZero : PPGadget arity hotSem (RelationMinor.pin false) :=
  (hotAtom.equalDrop.project (1 : Fin 2)).retarget (by
    unfold RelationMinor.pin RelationMinor.project RelationMinor.adjacent booleanRelation
    decide +kernel)
private noncomputable def derivedZeroBoundary : GadgetWitness derivedZero :=
  hotBoundary.project (1 : Fin 2)

example : derivedZero.body = [⟨(), [Sum.inl 0, Sum.inl 0, Sum.inr (0 : Fin 1)]⟩] := rfl
example : verify derivedZero.body (List.ofFn Sum.inl) derivedZeroBoundary.certificate = true :=
  derivedZeroBoundary.accepted
example (a : Fin 1 → Bool) : a ∈ RelationMinor.pin false ↔
    ∃ b, derivedZero.body.eval hotSem (Sum.elim a b) = true := derivedZero.correct a

-- There need be no original atom or alphabet symbol. Unused free ports are actual probe leaves.
private def emptyGadget : PPGadget (fun r : Empty => nomatch r) (fun r => nomatch r)
    (Set.univ : Set (Fin 2 → Bool)) where
  numAux := 0
  body := []
  wellFormed := by intro c hc; cases hc
  correct := by intro a; exact ⟨fun _ => ⟨Fin.elim0, rfl⟩, fun _ => Set.mem_univ _⟩

private def emptyBoundary : GadgetWitness emptyGadget where
  certificate := ⟨[0, 3, 2, 1]⟩
  accepted := by decide +kernel

example : emptyBoundary.equalDrop.certificate = ⟨[0, 1]⟩ := by
  rw [GadgetWitness.equalDrop_certificate]
  decide +kernel
example : verify emptyGadget.equalDrop.body (List.ofFn Sum.inl) ⟨[0, 1]⟩ = true := by
  decide +kernel

-- Dense-name comparison allows repeated declarations and selected names absent from the list.
example :
    let l : List ℕ := [7, 7, 9]
    Function.update id (l.idxOf 200) (l.idxOf 100) (l.idxOf 7) =
      Function.update id (l.idxOf 200) (l.idxOf 100) (l.idxOf 9) ↔
    Function.update id 200 100 7 = Function.update id 200 100 9 := by
  exact List.idxOf_update_id_eq_iff [7, 7, 9] 100 200 7 9 (by decide) (by decide)

-- Huge raw indices fund no loops; malformed tables retain the honest raw fallback.
example : RotationCertificate.swapSuccessors ⟨[1, 0]⟩ (2 ^ 250) (2 ^ 251) = ⟨[1, 0]⟩ := by
  decide +kernel
example : RotationCertificate.swapSuccessors ⟨[]⟩ (2 ^ 250) 0 = ⟨[]⟩ := by decide +kernel
example : verify naeAtom.equalDrop.body (List.ofFn Sum.inl)
    ⟨[8, 5, 0, 1, 6, 3, 4, 9, 2, 7]⟩ = false := by decide +kernel

-- Identical original binary constraints retain their distinct positions. Identification
-- leaves repeated boundary visits at the resulting cutvertex, rather than deduplicating them.
private abbrev pairAtom := PPGadget.atom (arity := fun _ : Unit => 2)
  (sem := fun _ _ => true) ()
private abbrev repeatedGadget := pairAtom.conj pairAtom
private def repeatedBoundary : GadgetWitness repeatedGadget where
  certificate := ⟨[4, 3, 8, 1, 10, 7, 2, 5, 6, 11, 0, 9]⟩
  accepted := by decide +kernel

example : repeatedBoundary.equalDrop.certificate = ⟨[4, 3, 0, 1, 8, 7, 2, 5, 6, 9]⟩ := by
  rw [GadgetWitness.equalDrop_certificate]
  decide +kernel
example : repeatedGadget.equalDrop.body =
    [⟨(), [Sum.inl 0, Sum.inl 0]⟩, ⟨(), [Sum.inl 0, Sum.inl 0]⟩] := rfl
example : verify repeatedGadget.equalDrop.body (List.ofFn Sum.inl)
    ⟨[4, 3, 0, 1, 8, 7, 2, 5, 6, 9]⟩ = true := by decide +kernel

-- No degree-four shortcut: identify adjacent ports in a degree-five original atom.
private abbrev highAtom := PPGadget.atom (arity := fun _ : Unit => 5)
  (sem := fun _ _ => false) ()
example : verify highAtom.equalDrop.body (List.ofFn Sum.inl)
    (equalDropCertificate highAtom.body 3 (atomBoundaryCertificate 5)) = true := by
  decide +kernel

-- True and false nullaries remain distinct closed point components; structural order
-- accepts them while the original conjunction is unsatisfiable.
private def nullaryGadget : PPGadget (fun _ : Bool => 0) (fun r _ => r)
    (∅ : Set (Fin 2 → Bool)) where
  numAux := 0
  body := [⟨false, []⟩, ⟨true, []⟩]
  wellFormed := by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                   rcases hc with rfl | rfl <;> rfl
  correct := by decide +kernel
private def nullaryBoundary : GadgetWitness nullaryGadget where
  certificate := ⟨[0, 3, 2, 1]⟩
  accepted := by decide +kernel
example : nullaryBoundary.equalDrop.certificate = ⟨[0, 1]⟩ := by
  rw [GadgetWitness.equalDrop_certificate]
  decide +kernel
example : verify nullaryGadget.equalDrop.body (List.ofFn Sum.inl) ⟨[0, 1]⟩ = true := by
  decide +kernel
example : ∀ (a : Fin 1 → Bool) (b : Fin 0 → Bool),
    nullaryGadget.equalDrop.body.eval (fun r _ => r) (Sum.elim a b) = false := by
  decide +kernel

-- The order congruence does not silently require a wellformed rotation table.
example (a b : ℕ) : verifyArgumentOrder ([⟨(), [7, 7]⟩] : CSP Unit ℕ) ⟨[a, 3, b, 1]⟩ =
    verifyArgumentOrder ([⟨(), [7, 7]⟩] : CSP Unit ℕ) ⟨[0, 3, 0, 1]⟩ := by
  apply verifyArgumentOrder_congr
  intro i hi
  change i < 2 at hi
  have he : i = 0 ∨ i = 1 := by omega
  rcases he with rfl | rfl <;> rfl

end CslibFrontierTests.PlanarEqualityBoundary
