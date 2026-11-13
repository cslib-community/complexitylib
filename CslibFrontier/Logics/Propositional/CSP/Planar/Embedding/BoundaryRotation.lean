/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Boundary

/-!
# The literal decoded probe rotation of a checked boundary witness

The probe rotation is decoded directly from the witness's actual accepted table. Its genus
and directed argument order are the original checker's conclusions, without choosing a second
rotation from an existential realization theorem.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V} {ports : List V}

/-- Decode exactly the checked probe table, retaining its literal indexed successors. -/
@[expose] noncomputable def Witness.probeRotation (w : Witness F ports) :
    RotationSystem (incidenceGraph (probeBody F ports)) :=
  RotationCertificate.decode _ w.certificate
    ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).1

/-- The original checked table internally supplies componentwise numerical genus zero. -/
theorem Witness.numericalGenusZero_probeRotation (w : Witness F ports) :
    w.probeRotation.NumericalGenusZero :=
  ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).2.1

/-- The literal decoded probe preserves the original reversed probe scope order. -/
theorem Witness.respectsArgumentOrder_probeRotation (w : Witness F ports) :
    RespectsArgumentOrder w.probeRotation :=
  ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).2.2

end Cslib.Complexity.CSP.OrderedBoundary
