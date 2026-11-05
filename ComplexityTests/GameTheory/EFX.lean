/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.GameTheory.FairDivision.EFX

/-!
# Positive EFX counterexample clients

The allocation and strict Pareto improvement are Figure 2 of
[MahabadiRamakrishnanTarnawski2026]. The initial allocation really is EFX: the counterexample
concerns compatibility with Pareto efficiency, rather than failure of EFX to exist.
-/

public section

namespace ComplexityTests.FairDivision

open Cslib.FairDivision Cslib.FairDivision.PositiveCounterexample

/-- Figure 2's allocation `(x,y,cdp,abq)`, as ownership of `x,y,a,b,c,d,p,q`. -/
@[expose] def initial : Fin 8 → Fin 4 := ![0, 1, 3, 3, 2, 2, 2, 3]

/-- Figure 2's dominating allocation `(x,bcq,yp,ad)`. -/
@[expose] def improvement : Fin 8 → Fin 4 := ![0, 2, 3, 1, 1, 3, 2, 1]

theorem initial_is_efx : EFX values initial := by decide

theorem improvement_dominates : ParetoDominates values improvement initial := by decide

example : (fun i : Fin 4 => bundleValue values initial i i) = ![7, 7, 8, 6] := by decide
example : (fun i : Fin 4 => bundleValue values improvement i i) = ![7, 8, 8, 6] := by decide

example : ¬ ParetoOptimal values initial := by
  intro h
  exact h ⟨improvement, improvement_dominates⟩

example (a : Fin 8 → Fin 4) : ¬ (EFX values a ∧ ParetoOptimal values a) :=
  not_efx_and_paretoOptimal a

end ComplexityTests.FairDivision
