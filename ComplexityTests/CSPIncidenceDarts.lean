/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Darts

/-! Ordinary generic incidence-coordinate import without polygon/primal definitions. -/

assert_not_exists Cslib.Complexity.CSP.polygonGraph

namespace ComplexityTests.CSPIncidenceDarts

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP

-- Pin the full public types, including original Type universes and DecidableEq binder.
noncomputable example : (∀ {Rel V : Type} [DecidableEq V] (F : CSP Rel V),
    F.Occurrence × Bool ≃ Graph.Dart (incidenceGraph F)) := @incidenceDartEquiv

example : (∀ {Rel V : Type} [DecidableEq V] {F : CSP Rel V} (x : F.Occurrence × Bool),
    incidenceDartEquiv F x = incidenceDart x.1 x.2) := @incidenceDartEquiv_apply

example {Rel V : Type} [DecidableEq V] (F : CSP Rel V) (o : F.Occurrence) (side : Bool) :
    incidenceDartEquiv F (o, side) = incidenceDart o side := by simp

example {Rel V : Type} [DecidableEq V] (F : CSP Rel V) (o : F.Occurrence) (side : Bool) :
    (incidenceDartEquiv F).symm (incidenceDart o side) = (o, side) := by
  simpa only [incidenceDartEquiv_apply] using (incidenceDartEquiv F).symm_apply_apply (o, side)

private abbrev F : CSP Unit ℕ := [((), [7, 7]), ((), []), ((), [7])]
private def first : F.Occurrence := ⟨(0 : Fin 3), (0 : Fin 2)⟩
private def second : F.Occurrence := ⟨(0 : Fin 3), (1 : Fin 2)⟩
private def third : F.Occurrence := ⟨(2 : Fin 3), (0 : Fin 1)⟩

-- Repeated labels keep distinct indexed ends. The nullary constraint has no dart.
example : (incidenceDartEquiv F (first, false)).1.val = 0 ∧
    (incidenceDartEquiv F (second, false)).1.val = 1 ∧
    (incidenceDartEquiv F (third, true)).1.val = 2 ∧
    (incidenceDartEquiv F (third, true)).2 = true := by
  simp only [incidenceDartEquiv_apply]
  decide +kernel

example : incidenceDartEquiv F (first, false) ≠ incidenceDartEquiv F (second, false) ∧
    (incidenceDartEquiv F (first, false)).vertex =
      (incidenceDartEquiv F (second, false)).vertex := by
  simp only [incidenceDartEquiv_apply]
  decide +kernel

example : (incidenceDartEquiv F (first, true)).vertex = 1 ∧
    (incidenceDartEquiv F (third, true)).vertex = 3 := by
  simp only [incidenceDartEquiv_apply]
  decide +kernel

end ComplexityTests.CSPIncidenceDarts
