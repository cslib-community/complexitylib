/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.GadgetCyclic
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Projection
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.AtomBoundary
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Exact generated cyclic tables, clockwise sign, and arbitrary actual gadget projection. -/

namespace CslibFrontierTests.PlanarCyclicBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary Graph

private abbrev body : CSP Unit (Fin 3) := [⟨(), List.ofFn id⟩]
private abbrev scope : Fin 3 → Fin 3 := Fin.rev
private abbrev q : Equiv.Perm (Fin 3) := finRotate 3
private abbrev input : CSP Unit (Fin 3) := body ++ [Constraint.mk () (List.ofFn scope)]
private abbrev supplied : RotationCertificate := ⟨[10, 3, 8, 5, 6, 1, 4, 9, 2, 11, 0, 7]⟩
private abbrev expected : RotationCertificate := ⟨[8, 3, 6, 5, 10, 1, 2, 9, 0, 11, 4, 7]⟩

private theorem source_rotation : RotationCertificate.verifyRotation (incidenceGraph input)
    supplied = true := by decide +kernel

private noncomputable abbrev converted :=
  reindexLastScopeCertificate body () scope q supplied source_rotation

private def bodyOccurrence (j : Fin 3) : body.Occurrence :=
  ⟨0, j⟩

private noncomputable def bodyO (j : Fin 3) : input.Occurrence :=
  appendOfFnOccurrenceEquiv body () scope (Sum.inl (bodyOccurrence j))

private noncomputable def probeO (j : Fin 3) : input.Occurrence :=
  appendOfFnOccurrenceEquiv body () scope (Sum.inr j)

private theorem source_body_index (j : Fin 3) : incidenceEdgeIndex (bodyO j) = j.val := by
  unfold incidenceEdgeIndex bodyO
  rw [record_appendOfFnOccurrenceEquiv_inl]
  fin_cases j <;> decide +kernel

private theorem source_probe_index (j : Fin 3) : incidenceEdgeIndex (probeO j) = 3 + j.val := by
  unfold incidenceEdgeIndex probeO
  rw [record_appendOfFnOccurrenceEquiv_inr]
  fin_cases j <;> decide +kernel

private theorem target_body_index (j : Fin 3) :
    incidenceEdgeIndex (reindexLastScopeOccurrenceEquiv body () scope q (bodyO j)) = j.val := by
  unfold incidenceEdgeIndex bodyO
  rw [reindexLastScopeOccurrenceEquiv_apply]
  change (body ++ [Constraint.mk () (List.ofFn (scope ∘ q))]).occurrences.idxOf
    (appendOfFnOccurrenceEquiv body () (scope ∘ q) (Sum.inl (bodyOccurrence j))).record = _
  rw [record_appendOfFnOccurrenceEquiv_inl]
  fin_cases j <;> decide +kernel

private theorem target_probe_index (j : Fin 3) :
    incidenceEdgeIndex (reindexLastScopeOccurrenceEquiv body () scope q (probeO j)) =
      3 + (q.symm j).val := by
  unfold incidenceEdgeIndex probeO
  rw [reindexLastScopeOccurrenceEquiv_apply]
  change (body ++ [Constraint.mk () (List.ofFn (scope ∘ q))]).occurrences.idxOf
    (appendOfFnOccurrenceEquiv body () (scope ∘ q) (Sum.inr (q.symm j))).record = _
  rw [record_appendOfFnOccurrenceEquiv_inr]
  fin_cases j <;> decide +kernel

private theorem source_steps (j : Fin 3) :
    supplied.successor.getD (incidenceDart (bodyO j) false).index 0 =
        (incidenceDart (probeO j.rev) false).index ∧
    supplied.successor.getD (incidenceDart (bodyO j) true).index 0 =
        (incidenceDart (bodyO (finRotate 3 j)) true).index ∧
    supplied.successor.getD (incidenceDart (probeO j) false).index 0 =
        (incidenceDart (bodyO j.rev) false).index ∧
    supplied.successor.getD (incidenceDart (probeO j) true).index 0 =
        (incidenceDart (probeO (finRotate 3 j)) true).index := by
  simp only [Dart.index, incidenceDart, source_body_index, source_probe_index,
    Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
  fin_cases j <;> decide +kernel

private theorem converted_steps (j : Fin 3) :
    converted.successor.getD (2 * j.val) 0 = 2 * (3 + (q.symm j.rev).val) ∧
    converted.successor.getD (2 * j.val + 1) 0 = 2 * (finRotate 3 j).val + 1 ∧
    converted.successor.getD (2 * (3 + (q.symm j).val)) 0 = 2 * j.rev.val ∧
    converted.successor.getD (2 * (3 + (q.symm j).val) + 1) 0 =
      2 * (3 + (q.symm (finRotate 3 j)).val) + 1 := by
  have h₁ := getD_reindexLastScopeCertificate_of_step body () scope q supplied source_rotation
    (bodyO j) (probeO j.rev) false false (source_steps j).1
  have h₂ := getD_reindexLastScopeCertificate_of_step body () scope q supplied source_rotation
    (bodyO j) (bodyO (finRotate 3 j)) true true (source_steps j).2.1
  have h₃ := getD_reindexLastScopeCertificate_of_step body () scope q supplied source_rotation
    (probeO j) (bodyO j.rev) false false (source_steps j).2.2.1
  have h₄ := getD_reindexLastScopeCertificate_of_step body () scope q supplied source_rotation
    (probeO j) (probeO (finRotate 3 j)) true true (source_steps j).2.2.2
  have hall := And.intro h₁ (And.intro h₂ (And.intro h₃ h₄))
  simpa only [Dart.index, incidenceDart, target_body_index, target_probe_index,
    Bool.toNat_false, Bool.toNat_true, Nat.add_zero] using hall

-- The whole generated certificate, not just its length or a signature, is identified.
example : converted = expected := by
  let rho := RotationCertificate.decode (incidenceGraph input) supplied source_rotation
  let tau := reindexLastScopeRotation body () scope q rho
  change RotationCertificate.ofRotation tau = expected
  apply (RotationCertificate.ofRotation_eq_iff tau expected).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro d
  have hb : d.index < 12 := (Dart.indexEquiv _ d).isLt
  have hs₀ := converted_steps (0 : Fin 3)
  have hs₁ := converted_steps (1 : Fin 3)
  have hs₂ := converted_steps (2 : Fin 3)
  change converted.successor.getD 0 0 = 8 ∧ converted.successor.getD 1 0 = 3 ∧
    converted.successor.getD 10 0 = 4 ∧ converted.successor.getD 11 0 = 7 at hs₀
  change converted.successor.getD 2 0 = 6 ∧ converted.successor.getD 3 0 = 5 ∧
    converted.successor.getD 6 0 = 2 ∧ converted.successor.getD 7 0 = 9 at hs₁
  change converted.successor.getD 4 0 = 10 ∧ converted.successor.getD 5 0 = 1 ∧
    converted.successor.getD 8 0 = 0 ∧ converted.successor.getD 9 0 = 11 at hs₂
  have he (i : ℕ) (hi : i < 12) :
      expected.successor.getD i 0 = converted.successor.getD i 0 := by
    interval_cases i <;> simp_all
  have h := he d.index hb
  change expected.successor.getD d.index 0 =
    (RotationCertificate.ofRotation tau).successor.getD d.index 0 at h
  rw [RotationCertificate.getD_ofRotation] at h
  exact h

example : verifyRotationCertificate (body ++ [Constraint.mk () (List.ofFn (scope ∘ q))])
    converted = true :=
  verifyRotationCertificate_reindexLastScopeCertificate body () scope q (by intro j; rfl)
    supplied source_rotation (by decide +kernel)

example : verifyRotationCertificate (body ++ [Constraint.mk () (List.ofFn (scope ∘ q))])
    expected = true := by
  decide +kernel

-- Reflection fails the exact directed commutation condition at this concrete arity.
example : ¬∀ j : Fin 3, (finRotate 3 j).rev = finRotate 3 j.rev := by decide +kernel

end CslibFrontierTests.PlanarCyclicBoundary
