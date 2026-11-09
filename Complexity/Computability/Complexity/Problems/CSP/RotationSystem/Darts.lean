/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem

/-!
# Occurrence coordinates on actual incidence darts

The existing indexed occurrence and its endpoint side parametrize the incidence graph's
actual darts. Repeated variables and identical constraints retain separate positions;
nullary constraints have no darts. This coordinate equivalence has no polygon, genus,
planarity or runtime premise. The declarations are relocated unchanged from Primal.Graph.

## Main definitions

* `Cslib.Complexity.CSP.incidenceDartEquiv`: exact occurrence/end coordinates.

## Main results

* `Cslib.Complexity.CSP.incidenceDartEquiv_apply`: the literal forward coordinate map.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Occurrence/end coordinates on the existing incidence graph. -/
@[expose] noncomputable def incidenceDartEquiv (F : CSP Rel V) :
    F.Occurrence × Bool ≃ Graph.Dart (incidenceGraph F) :=
  Equiv.ofBijective (fun x => incidenceDart x.1 x.2) ⟨by
    rintro ⟨o, b⟩ ⟨p, c⟩ h
    exact Prod.ext (incidenceEdgeIndex_injective (congrArg (fun d => d.1.val) h))
      (congrArg (fun d : Graph.Dart (incidenceGraph F) => d.2) h), fun d => by
    obtain ⟨o, ho⟩ := exists_incidenceDart d
    exact ⟨(o, d.2), ho⟩⟩

/-- The forward incidence coordinate map is the existing occurrence/end map. -/
@[simp] theorem incidenceDartEquiv_apply (x : F.Occurrence × Bool) :
    incidenceDartEquiv F x = incidenceDart x.1 x.2 := rfl

end Cslib.Complexity.CSP
