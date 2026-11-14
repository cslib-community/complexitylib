/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Computability.PolyTime.CSP.Gadget.ConstructionCompiler

/-! Ordinary all-raw native and semantic clients, with no finite target alphabet premise.
The empty-language client tests total rejection without an unsatisfiable target relation. -/

namespace CslibFrontierTests.CSPConstructionCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP
open Cslib.Complexity.CSP.GadgetRotation Turing.MultiTapeTM

example {Src Rel : Type} [Finite Src] {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (compileConstructions trees)
      (encCSPRotationCertificate encSrc encNat) (encCSPRotationCertificate encRel encNat) :=
  computableInPolyTime_compileConstructions encSrc encRel trees

example {Src Rel : Type} [Finite Src] {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    (trees : ∀ r, RelationMinor.Construction arity sem (booleanRelation srcArity srcSem r))
    (p : CSP Src ℕ × Cslib.Complexity.Graph.RotationCertificate) :
    (WellFormed arity (compileConstructions trees p).1 ∧
      verifyRotationCertificate (compileConstructions trees p).1
        (compileConstructions trees p).2 = true ∧
      (compileConstructions trees p).1.Satisfiable sem) ↔
      WellFormed srcArity p.1 ∧ verifyRotationCertificate p.1 p.2 = true ∧
        p.1.Satisfiable srcSem :=
  wellFormed_certifiedSatisfiable_compileConstructions_iff trees p

private def emptyTrees (r : Empty) : RelationMinor.Construction (Empty.elim : Empty → ℕ)
    (fun r _ => Empty.elim r)
    (booleanRelation (Empty.elim : Empty → ℕ) (fun r _ => Empty.elim r) r) :=
  Empty.elim r

private noncomputable def emptyCompiled := compileConstructions emptyTrees

example : emptyCompiled ([], ⟨[2 ^ 250]⟩) = ([], ⟨[0]⟩) :=
  compileConstructions_of_sourceGuard_false emptyTrees _ (by decide +kernel)

example : verifyRotationCertificate (emptyCompiled ([], ⟨[2 ^ 250]⟩)).1
    (emptyCompiled ([], ⟨[2 ^ 250]⟩)).2 = false := by
  rw [show emptyCompiled ([], ⟨[2 ^ 250]⟩) = ([], ⟨[0]⟩) from
    compileConstructions_of_sourceGuard_false emptyTrees _ (by decide +kernel)]
  exact verifyRotationCertificate_empty_invalid

example : verifyRotationCertificate (emptyCompiled ([], ⟨[]⟩)).1
    (emptyCompiled ([], ⟨[]⟩)).2 = true :=
  (verifyRotationCertificate_compileConstructions_iff emptyTrees _).mpr (by decide)

end CslibFrontierTests.CSPConstructionCompiler
