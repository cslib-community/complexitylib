/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.DeterministicTransitiveClosure
public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Tuple

/-!
# Deterministic closure as a transported closure semantics

Deterministic closure is the closure semantics `TC.Tuple.closureBy` for the deterministic reduct.
Taking the deterministic reduct commutes with relabelling the vertices along a bijection, so the
full-tuple pullback theorems stated for `closureBy`, such as
`Cslib.Logic.FO.TC.Tuple.realize_onFormula_closureBy`, apply to FO(DTC) unchanged.

## Main results

* `Cslib.Logic.FO.DTC.transports_deterministicReduct`: the deterministic reduct commutes with
  bijections.
* `Cslib.Logic.FO.DTC.interpretation_eq_closureBy`: deterministic closure is closure of the
  deterministic reduct.
-/

public section

namespace Cslib.Logic.FO.DTC

/-- The deterministic reduct commutes with relabelling the vertices along a bijection. -/
theorem transports_deterministicReduct :
    TC.Tuple.Transports fun r => deterministicReduct r := by
  intro β γ e r s h a b
  constructor
  · rintro ⟨hab, hu⟩
    refine ⟨(h a b).mp hab, fun z hz => ?_⟩
    obtain ⟨z, rfl⟩ := e.surjective z
    exact congrArg e (hu z ((h a z).mpr hz))
  · rintro ⟨hab, hu⟩
    exact ⟨(h a b).mpr hab, fun z hz => e.injective (hu (e z) ((h a z).mp hz))⟩

/-- Deterministic closure is closure of the deterministic reduct of the body relation. -/
theorem interpretation_eq_closureBy {M : Type} :
    (interpretation : Operator.Interpretation TC.shape M) =
      TC.Tuple.closureBy fun r => deterministicReduct r :=
  rfl

end Cslib.Logic.FO.DTC
