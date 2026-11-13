/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Genus

/-! An ordinary mathematical client applies full actual-table acceptance at arbitrary arity.
Neither relation alphabet is assumed finite, and no native runtime module is imported. -/

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP
open Cslib.Complexity.CSP.GadgetRotation Cslib.Complexity.CSP.OrderedBoundary

example {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : Cslib.Complexity.Graph.RotationCertificate)
    (hc : verifyRotationCertificate F c = true) :
    verifyRotationCertificate (replaceGadgets B (fun r => (gadgets r).template) F)
      (replacementCertificate B (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
        (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c) = true :=
  verifyRotationCertificate_replacementCertificate gadgets witnesses B hB F hF c hc
