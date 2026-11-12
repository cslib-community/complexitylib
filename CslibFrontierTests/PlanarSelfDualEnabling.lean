/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.SelfDual

/-! Internally supplied ordered disequality in the nonvacuous language {NAE3, CROSS}. -/

namespace CslibFrontierTests.PlanarSelfDualEnabling

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity
open Cslib.Complexity.CSP Cslib.Complexity.CSP.OrderedBoundary

private def arity (r : Bool) : ℕ := if r then 4 else 3
private def sem (r : Bool) (scope : List Bool) : Bool :=
  if r then decide (scope.getD 0 false = scope.getD 2 false ∧
      scope.getD 1 false = scope.getD 3 false)
  else decide (scope.count true ≠ 0 ∧ scope.count true ≠ 3)

private theorem common_not : HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0)) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
  decide +kernel

private theorem missing_false : ¬HasPolymorphism arity sem (fun _ : Fin 1 → Bool => false) := by
  intro h
  have hh := h false (fun _ => ![true, false, false]) (by intro j; rfl)
  exact Bool.false_ne_true hh

-- Both the original-language body and its exact checker-accepted finite table are supplied
-- by the theorem. There is no hypothesis about a template, pp definition or target rotation.
example : ∃ (g : PPGadget arity sem RelationMinor.disequality) (c : Graph.RotationCertificate),
    verify g.body (List.ofFn Sum.inl) c = true ∧
      (∃ b, g.body.eval sem (Sum.elim ![true, false] b) = true) ∧
      ¬(∃ b, g.body.eval sem (Sum.elim ![false, false] b) = true) := by
  obtain ⟨g, ⟨w⟩⟩ := exists_disequality_of_common_not common_not missing_false
  refine ⟨g, w.certificate, w.accepted, ?_, ?_⟩
  · exact (g.correct ![true, false]).mp (by decide)
  · intro hb
    exact (by decide : ![false, false] ∉ RelationMinor.disequality)
      ((g.correct ![false, false]).mpr hb)

-- The source constant failure genuinely occurs in NAE3. CROSS alone would be tractable;
-- here it is a separate symbol and is not used as an absent-six witness.
example : sem false [true, false, false] = true ∧ sem false [false, false, false] = false := by
  decide +kernel
example : sem true [false, true, false, true] = true ∧
    sem true [false, true, true, false] = false := by decide +kernel

-- Even an inconsistent language of true/false nullaries has the false constant operation.
-- The failed-constant premise therefore does not follow merely from unsatisfiability.
example : HasPolymorphism (fun _ : Bool => 0) (fun r _ => r)
    (fun _ : Fin 1 → Bool => false) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
  decide +kernel
example : HasPolymorphism (fun e : Empty => nomatch e)
    (fun (e : Empty) (_ : List Bool) => nomatch e) (fun _ : Fin 1 → Bool => false) := by
  intro e
  exact nomatch e

end CslibFrontierTests.PlanarSelfDualEnabling
