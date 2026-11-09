/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Graph

/-! The old public import path retains generic coordinates, simp and the polygon API. -/

namespace ComplexityTests.CSPPrimalDartsImport

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP

example {Rel V : Type} [DecidableEq V] (F : CSP Rel V) (o : F.Occurrence) (side : Bool) :
    incidenceDartEquiv F (o, side) = incidenceDart o side := by simp

private abbrev F : CSP Unit ℕ := [((), [7, 9, 7])]
private def final : F.Occurrence := ⟨(0 : Fin 1), (2 : Fin 3)⟩

example : (incidenceDartEquiv F (final, false)).1.val = 2 ∧
    (incidenceDartEquiv F (final, false)).vertex = 0 := by
  simp only [incidenceDartEquiv_apply]
  decide +kernel

example : (polygonDartEquiv F (final, false)).1.val = 2 ∧
    (polygonDartEquiv F (final, true)).1.val = 2 := by
  simp only [polygonDartEquiv_apply]
  decide +kernel

end ComplexityTests.CSPPrimalDartsImport
