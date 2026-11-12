/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Equality
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetCyclic
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.UnaryAttachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.DifferenceAttachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.FlipAttachment
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BinaryMeet

/-!
# Ordered numerical witnesses for the complete construction grammar

Every existing `RelationMinor.Construction` internally supplies a checked ordered numerical
witness on exactly its existing original-language `Construction.gadget` body. The recursion
includes the enabling pin and disequality trees. No finite alphabet, body-occurrence,
connectedness, degree, target-genus or external gadget-provider hypothesis is needed.

This is static numerical data. It does not identify this model with geometric embeddings,
provide a native compiler or prove the full planar CSP dichotomy. The higher-arity CROSS
and one-hot macro expansion, normalization and geometric source comparison remain separate tasks.

## Main definitions

* `Cslib.Logic.PL.CSP.RelationMinor.Construction.orderedWitness`: exact-body witness.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

open Cslib.Complexity.CSP.OrderedBoundary

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}

/-- Every finite construction tree supplies a checked ordered numerical witness for exactly
its existing PP interpreter. Enabling pin and disequality witnesses recurse to original
atoms; no additional provider premise is present. -/
noncomputable def Construction.orderedWitness {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction arity sem R) : GadgetWitness c.gadget :=
  match c with
  | .atom r => Witness.atom arity sem r
  | .project c j => c.orderedWitness.project j
  | .equalDrop c => c.orderedWitness.equalDrop
  | .differentDrop c d => c.orderedWitness.differentDrop d.orderedWitness
  | .cofactor c j b p => c.orderedWitness.cofactor j b p.orderedWitness
  | .flip (n := k) (R := S) c j d =>
      (Construction.orderedWitness (n := k) (R := S) c).flip j
        (Construction.orderedWitness d)
  | .rotate (n := k) (R := S) c =>
      (Construction.orderedWitness (n := k + 1) (R := S) c).rotate
  | .binaryMeet (R := S) (S := T) c d =>
      (Construction.orderedWitness (n := 2) (R := S) c).binaryMeet
        (Construction.orderedWitness (R := T) d)

/-- Availability supplies an actual original-language gadget together with its checked
ordered numerical witness, without a finite-language or target-embedding assumption. -/
theorem Available.nonempty_orderedGadget {n : ℕ} {R : Set (Fin n → Bool)}
    (h : Available arity sem R) :
    ∃ g : PPGadget arity sem R, Nonempty (GadgetWitness g) := by
  obtain ⟨c⟩ := h
  exact ⟨c.gadget, ⟨c.orderedWitness⟩⟩

end Cslib.Logic.PL.CSP.RelationMinor
