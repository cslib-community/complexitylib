/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.Incidence
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Tactic.FinCases

/-! Ordered CSP occurrences, local/global semantics, and native multigraph construction. -/

namespace CslibFrontierTests.CSPOccurrence

open Cslib Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

-- Four relations: unrestricted, all false, all true, and empty (including at arity zero).
private def sem (r : Fin 4) (xs : List Bool) : Bool :=
  match r.val with
  | 0 => true
  | 1 => xs.all (! ·)
  | 2 => xs.all id
  | _ => false

private abbrev repeated : CSP (Fin 4) ℕ := [(0, [7, 7])]
private abbrev identical : CSP (Fin 4) ℕ := [(0, [7]), (0, [7])]
private abbrev conflict : CSP (Fin 4) ℕ := [(1, [7]), (2, [7])]

-- A repeated variable gives parallel edge records with distinct occurrence identities.
example : repeated.occurrences = [(0, 0, 7), (0, 1, 7)] := by decide
example : CSP.incidenceGraph repeated = ([0, 1], [(0, 1), (0, 1)]) := by decide

private abbrev first : repeated.Occurrence := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
private abbrev second : repeated.Occurrence := ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

example : first ≠ second ∧ first.var = second.var := by decide
example : first.relation = 0 ∧ first.scope = [7, 7] := by decide
example : CSP.incidenceEdgeIndex first = 0 ∧ CSP.incidenceEdgeIndex second = 1 := by decide
example : (CSP.incidenceGraph repeated).edgeEndpoint (CSP.incidenceEdgeIndex second) true = 1 :=
  CSP.edgeEndpoint_incidenceEdgeIndex second true

-- Identical constraints retain different vertices, even with the same relation and scope.
example : CSP.incidenceGraph identical = ([0, 1, 2], [(0, 1), (0, 2)]) := by decide
example : identical.occurrences = [(0, 0, 7), (1, 0, 7)] := by decide
example : identical.EdgeInstance := by
  unfold CSP.EdgeInstance
  decide
example : ¬ repeated.EdgeInstance := by
  unfold CSP.EdgeInstance
  decide
example : ¬ CSP.EdgeInstance ([(0, [7])] : CSP (Fin 4) ℕ) := by
  unfold CSP.EdgeInstance
  decide
example : ¬ CSP.EdgeInstance ([(0, [7]), (0, [7]), (0, [7])] : CSP (Fin 4) ℕ) := by
  unfold CSP.EdgeInstance
  decide

-- Nullary constraints survive as isolated constraint vertices and still affect semantics.
example : CSP.incidenceGraph ([(0, [])] : CSP (Fin 4) ℕ) = ([0], []) := by decide
example : CSP.EdgeInstance ([(0, [])] : CSP (Fin 4) ℕ) := by
  unfold CSP.EdgeInstance
  decide
example : CSP.Satisfiable sem ([(0, [])] : CSP (Fin 4) ℕ) := ⟨fun _ => false, rfl⟩
example : ¬ CSP.Satisfiable sem ([(3, [])] : CSP (Fin 4) ℕ) := by
  rintro ⟨σ, hσ⟩
  cases hσ
example : ¬ ∃ l : CSP.OccurrenceLabeling ([(3, [])] : CSP (Fin 4) ℕ) Bool,
    CSP.ValidLabeling sem l ∧ CSP.ConsistentLabeling l := by
  rw [← CSP.satisfiable_iff_exists_labeling sem false]
  rintro ⟨σ, hσ⟩
  cases hσ

-- Empty instances have no occurrences; a global assignment uses the explicit outside value.
example : CSP.incidenceGraph ([] : CSP (Fin 4) ℕ) = ([], []) := by decide
example : CSP.EdgeInstance ([] : CSP (Fin 4) ℕ) := by
  unfold CSP.EdgeInstance
  decide
example : CSP.Satisfiable sem ([] : CSP (Fin 4) ℕ) := ⟨fun _ => false, rfl⟩
example : CSP.reconstruct (F := ([] : CSP (Fin 4) ℕ)) (fun o => Fin.elim0 o.1) true 9 = true :=
  CSP.reconstruct_of_not_mem _ _ (by decide)

-- Huge binary source names do not generate a huge vertex interval.
example : CSP.incidenceGraph ([(0, [2 ^ 100, 3])] : CSP (Fin 4) ℕ) =
    ([0, 1, 2], [(0, 2), (1, 2)]) := by decide

private def disagree : repeated.OccurrenceLabeling Bool := fun o => o.2.val == 0

example : CSP.ValidLabeling sem disagree := by
  intro i
  fin_cases i
  rfl

example : ¬ CSP.ConsistentLabeling disagree := by
  intro h
  have hf := h first second rfl
  change true = false at hf
  cases hf

-- A model can exist even though a particular locally valid labeling is inconsistent.
example : repeated.Satisfiable sem := ⟨fun _ => false, rfl⟩
example : CSP.ConsistentLabeling (CSP.labelAssignment (F := repeated) fun _ => true) :=
  CSP.consistentLabeling_labelAssignment _
example : CSP.ValidLabeling sem (CSP.labelAssignment (F := repeated) fun _ => true) :=
  (CSP.validLabeling_labelAssignment_iff sem _).mpr rfl

-- A genuine edge instance has a valid local labeling, but no consistent valid labeling.
private def conflictLabels : conflict.OccurrenceLabeling Bool := fun o => o.1.val == 1

example : conflict.EdgeInstance := by
  unfold CSP.EdgeInstance
  decide
example : CSP.ValidLabeling sem conflictLabels := by
  intro i
  fin_cases i <;> rfl
private theorem conflict_inconsistent : ¬ CSP.ConsistentLabeling conflictLabels := by
  intro h
  have hf := h ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ rfl
  change false = true at hf
  cases hf
example (h : conflict.EdgeInstance) : ¬ h.Agrees conflictLabels :=
  fun ha => conflict_inconsistent ((h.agrees_iff_consistent _).mp ha)
example (h : identical.EdgeInstance) :
    h.Agrees (CSP.labelAssignment (F := identical) fun _ => false) :=
  (h.agrees_iff_consistent _).mpr (CSP.consistentLabeling_labelAssignment _)
example : ¬ conflict.Satisfiable sem := by
  rintro ⟨σ, hσ⟩
  cases h : σ 7 <;> simp [CSP.eval, Constraint.eval, sem, h] at hσ

-- The existential theorem uses the same arbitrary-domain CSP semantics and handles empty input.
example (F : CSP (Fin 4) ℕ) (h : F.EdgeInstance) :
    F.Satisfiable sem ↔ ∃ l : F.OccurrenceLabeling Bool, CSP.ValidLabeling sem l ∧ h.Agrees l :=
  h.satisfiable_iff_exists_agrees sem false

example (l : repeated.OccurrenceLabeling Bool) (hc : CSP.ConsistentLabeling l) :
    CSP.reconstruct l false 7 = l second := CSP.reconstruct_variable hc false second
example (l : repeated.OccurrenceLabeling Bool) : CSP.reconstruct l true 99 = true :=
  CSP.reconstruct_of_not_mem _ _ (by decide)

example : ComputableInPolyTime (CSP.incidenceGraph (Rel := Fin 4) (V := ℕ))
    (encCSP (encFinite (Fin 4)) encNat) encGraph :=
  CSP.computableInPolyTime_incidenceGraph _ _
example : ComputableInPolyTime (CSP.occurrences (Rel := Fin 4) (V := ℕ))
    (encCSP (encFinite (Fin 4)) encNat) (encList (CSP.encOccurrenceRecord encNat)) :=
  CSP.computableInPolyTime_occurrences _ _

end CslibFrontierTests.CSPOccurrence
