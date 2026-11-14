/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Gadget.PlanarCompiler
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Construction
import Mathlib.Data.Fintype.EquivFin

/-!
# Native certified compilation from fixed construction trees

A fixed construction tree for each source symbol supplies its original-language gadget
and invokes `Construction.orderedWitness` internally, including every enabling subtree.
The finite source family also determines its own auxiliary bound. No target rotation,
boundary words, genus premise or unproved enabling theorem is supplied by the client.

Static preprocessing is noncomputable and nonuniform in the fixed trees and language.
After fixing them, the existing compiler executes in ordinary native polynomial time on
all binary/framed inputs, including rejected inputs. No finite target alphabet is required.
This endpoint uses the ordered numerical incidence model; source-model comparison and the
remaining planar dichotomy assembly are separate objectives.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Turing.MultiTapeTM

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool} [Finite Src]

/-- Static maximum of the actual auxiliary counts in a fixed finite source family.
The empty source alphabet has bound zero. -/
noncomputable def constructionAuxiliaryBound
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r)) : ℕ :=
  letI := Fintype.ofFinite Src
  Finset.univ.sup (fun r => (trees r).gadget.numAux)

/-- The fixed maximum bounds every actual tree-interpreted gadget. -/
theorem numAux_le_constructionAuxiliaryBound
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (r : Src) : (trees r).gadget.numAux ≤ constructionAuxiliaryBound trees := by
  classical
  let := Fintype.ofFinite Src
  exact Finset.le_sup (f := fun r => (trees r).gadget.numAux) (Finset.mem_univ r)

/-- The total deterministic compiler with all static data derived internally from the
actual construction trees. Rejected inputs produce the empty body and certificate `[0]`. -/
@[expose] noncomputable def compileConstructions
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r)) :
    CSP Src ℕ × Graph.RotationCertificate → CSP Rel ℕ × Graph.RotationCertificate :=
  compileGadgets (fun r => (trees r).gadget) (fun r => (trees r).orderedWitness)
    (constructionAuxiliaryBound trees)

/-- Accepted inputs retain exactly the original replacement body and executed block table. -/
theorem compileConstructions_of_sourceGuard_true
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Graph.RotationCertificate) (hp : sourceGuard srcArity p = true) :
    compileConstructions trees p =
      (replaceGadgets (constructionAuxiliaryBound trees) (fun r => (trees r).gadget.template) p.1,
        replacementCertificate (constructionAuxiliaryBound trees)
          (fun r => (trees r).gadget.template)
          (fun r => freeBoundaryBlocks (trees r).gadget (trees r).orderedWitness)
          (fun r => auxiliaryBoundaryBlocks (trees r).gadget (trees r).orderedWitness)
          p.1 p.2) := by
  simp only [compileConstructions, compileGadgets, compile, hp, ite_true]

/-- The rejection branch is available for every target alphabet, including the empty one. -/
theorem compileConstructions_of_sourceGuard_false
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Graph.RotationCertificate) (hp : sourceGuard srcArity p = false) :
    compileConstructions trees p = ([], ⟨[0]⟩) :=
  compile_of_sourceGuard_false _ _ _ _ _ p hp

/-- Every output body has the target arities, including rejected raw inputs. -/
theorem wellFormed_compileConstructions
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    WellFormed arity (compileConstructions trees p).1 :=
  wellFormed_compileGadgets _ _ _ p

/-- On all raw inputs, the full target checker accepts exactly the source guard. -/
theorem verifyRotationCertificate_compileConstructions_iff
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    verifyRotationCertificate (compileConstructions trees p).1
      (compileConstructions trees p).2 = true ↔ sourceGuard srcArity p = true :=
  verifyRotationCertificate_compileGadgets_iff _ _ _
    (numAux_le_constructionAuxiliaryBound trees) p

/-- Complete all-raw certified satisfiability equivalence from actual construction trees.
No separate ordered-witness, target-acceptance or enabling-branch premise is needed. -/
theorem wellFormed_certifiedSatisfiable_compileConstructions_iff
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Graph.RotationCertificate) :
    (WellFormed arity (compileConstructions trees p).1 ∧
      verifyRotationCertificate (compileConstructions trees p).1
        (compileConstructions trees p).2 = true ∧
      (compileConstructions trees p).1.Satisfiable sem) ↔
      WellFormed srcArity p.1 ∧ verifyRotationCertificate p.1 p.2 = true ∧
        p.1.Satisfiable srcSem :=
  wellFormed_certifiedSatisfiable_compileGadgets_iff _ _ _
    (numAux_le_constructionAuxiliaryBound trees) p

/-- Ordinary native polynomial time after fixing the finite source family of trees.
The entire framed certificate and every binary label are part of the input/output encoding. -/
theorem computableInPolyTime_compileConstructions
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r)) :
    ComputableInPolyTime (compileConstructions trees)
      (encCSPRotationCertificate encSrc encNat) (encCSPRotationCertificate encRel encNat) :=
  computableInPolyTime_compileGadgets encSrc encRel _ _ _

/-- Complete polynomial framed output bound on all raw inputs, with constants depending
only on the fixed language encodings and construction trees. -/
theorem exists_framed_bound_compileConstructions
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r)) :
    ∃ c d : ℕ, ∀ p : CSP Src ℕ × Graph.RotationCertificate,
      (encCSPRotationCertificate encRel encNat (compileConstructions trees p)).length ≤
        c * ((encCSPRotationCertificate encSrc encNat p).length + 1) ^ d :=
  (computableInPolyTime_compileConstructions encSrc encRel trees)
    |>.polyBounded_length.exists_le

end Cslib.Complexity.CSP.GadgetRotation
