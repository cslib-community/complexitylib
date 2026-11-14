/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidencePrefix
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Relabel

/-!
# Literal edge positions under arbitrary CSP variable renaming

Actual occurrence positions retain their original edge indices even if variable names are
identified. This does not assert that the incidence vertex partition survives such renaming.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- Renaming variables does not change an occurrence's literal edge-list position. -/
theorem incidenceEdgeIndex_relabelOccurrence {Rel V W : Type}
    [DecidableEq V] [DecidableEq W] (F : CSP Rel V) (f : V → W) (o : F.Occurrence) :
    incidenceEdgeIndex (CSP.relabelOccurrence F f o) = incidenceEdgeIndex o := by
  rw [incidenceEdgeIndex_eq_prefix]
  change (CSP.vars ((F.relabel f).take o.1.val)).length + o.2.val = _
  have ht (i : ℕ) : (F.relabel f).take i = CSP.relabel f (F.take i) := by
    simp only [CSP.relabel, List.map_take]
  rw [ht, CSP.vars_relabel, List.length_map, incidenceEdgeIndex_eq_prefix]

end Cslib.Complexity.CSP
