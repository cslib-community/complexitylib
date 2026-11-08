/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Complexity.Foundations.Data.List.IdxOfInjective

/-!
# Literal certificate transport under injective variable renaming

An injection on occurring variable names preserves the actual dense incidence graph, edge
positions and argument-order check. The very same successor table therefore passes exactly
the same ordered numerical checker. Repeated variables and constraints retain their positions;
the map can behave arbitrarily on unused names. No geometric equivalence is asserted.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
/-- The positive-CNF adapter commutes with variable renaming, preserving every scope position. -/
theorem varCNF_relabel (F : CSP Rel V) (f : V → W) :
    (F.relabel f).varCNF = F.varCNF.relabel f := by
  simp [CSP.relabel, CSP.varCNF, CNF.relabel, Clause.relabel, Constraint.relabel]

/-- Injectivity only on occurring names preserves their first-occurrence order. -/
theorem distinctVars_relabel_of_injOn (F : CSP Rel V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ F.vars}) :
    (F.relabel f).distinctVars = F.distinctVars.map f := by
  have h := CNF.distinctVars_relabel_of_injOn F.varCNF f
    (by simpa only [vars_varCNF] using hf)
  simpa only [← varCNF_relabel, distinctVars_varCNF] using h

/-- Renaming injectively on the occurring names preserves the distinct-variable count. -/
theorem numVars_relabel_of_injOn (F : CSP Rel V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ F.vars}) : (F.relabel f).numVars = F.numVars := by
  rw [← length_distinctVars, ← length_distinctVars, distinctVars_relabel_of_injOn F f hf,
    List.length_map]

omit [DecidableEq V] [DecidableEq W] in
/-- Variable renaming preserves the complete positional occurrence table. -/
theorem occurrences_relabel (F : CSP Rel V) (f : V → W) :
    (F.relabel f).occurrences = F.occurrences.map (fun o => (o.1, o.2.1, f o.2.2)) := by
  simp only [occurrences, varCNF_relabel, Cslib.Logic.PL.occurrences_relabel,
    List.map_map, Function.comp_def]

end Cslib.Logic.PL.CSP

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Injectivity on used names preserves the literal listed incidence multigraph. -/
theorem incidenceGraph_relabel_of_injOn (F : CSP Rel V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ F.vars}) : incidenceGraph (F.relabel f) = incidenceGraph F := by
  apply Prod.ext
  · rw [incidenceGraph_vertices, incidenceGraph_vertices, numVars_relabel_of_injOn F f hf]
    simp only [CSP.relabel, List.length_map]
  · rw [incidenceGraph_edges, incidenceGraph_edges, CSP.occurrences_relabel,
      distinctVars_relabel_of_injOn F f hf, numVars_relabel_of_injOn F f hf, List.map_map]
    apply List.map_congr_left
    intro o ho
    have hv : o.2.2 ∈ F.vars := by
      rw [← map_occurrences F]
      exact List.mem_map_of_mem ho
    have hi := List.idxOf_map_injOn F.distinctVars f
      (fun _ hx _ hy => hf (mem_distinctVars.mp hx) (mem_distinctVars.mp hy))
      (mem_distinctVars.mpr hv)
    simp only [Function.comp_apply, hi]

omit [DecidableEq V] [DecidableEq W] in
/-- Renaming variables does not alter positional constraint and argument indices. -/
theorem argumentPositions_relabel (F : CSP Rel V) (f : V → W) :
    argumentPositions (F.relabel f) = argumentPositions F := by
  simp [argumentPositions, CSP.occurrences_relabel]

omit [DecidableEq V] [DecidableEq W] in
/-- A variable renaming retains every original scope length, including nullary scopes. -/
theorem scopeLength_relabel (F : CSP Rel V) (f : V → W) (i : ℕ) :
    scopeLength (F.relabel f) i = scopeLength F i := by
  simp [scopeLength, CSP.relabel, Constraint.relabel, List.map_map, Function.comp_def]

omit [DecidableEq V] [DecidableEq W] in
/-- Exact cyclic argument successors survive arbitrary variable renaming. -/
theorem argumentNextIndex_relabel (F : CSP Rel V) (f : V → W) (i j : ℕ) :
    argumentNextIndex (F.relabel f) i j = argumentNextIndex F i j := by
  simp [argumentNextIndex, argumentPositions_relabel, scopeLength_relabel]

omit [DecidableEq V] [DecidableEq W] in
/-- The argument-order checker retains its exact Boolean result on every supplied table. -/
theorem verifyArgumentOrder_relabel (F : CSP Rel V) (f : V → W)
    (c : Graph.RotationCertificate) :
    verifyArgumentOrder (F.relabel f) c = verifyArgumentOrder F c := by
  simp [verifyArgumentOrder, CSP.occurrences_relabel, List.zipIdx_map, List.all_map,
    argumentNextIndex_relabel, Function.comp_def]

/-- The same raw certificate has the same acceptance result after an injection on used names.
This preserves argument chirality as well as the componentwise numerical genus check. -/
theorem verifyRotationCertificate_relabel_of_injOn (F : CSP Rel V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ F.vars}) (c : Graph.RotationCertificate) :
    verifyRotationCertificate (F.relabel f) c = verifyRotationCertificate F c := by
  rw [verifyRotationCertificate, verifyRotationCertificate, incidenceGraph_relabel_of_injOn F f hf,
    verifyArgumentOrder_relabel]

end Cslib.Complexity.CSP
