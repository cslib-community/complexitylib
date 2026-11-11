/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Measurability of unordered-interval threshold crossings

The event `{ω | t ∈ Set.uIoc (f ω) (g ω)}` that a threshold `t` lies in the unordered half-open
interval between two measurable real functions is measurable (`measurableSet_setOf_mem_uIoc`).

## Main results

* `measurableSet_setOf_mem_uIoc`: `{ω | t ∈ Ι (f ω) (g ω)}` is measurable for measurable `f`, `g`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

/-- The event that a threshold lies between two measurable real functions is measurable. -/
theorem measurableSet_setOf_mem_uIoc {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (t : ℝ) : MeasurableSet {ω | t ∈ Ι (f ω) (g ω)} := by
  simp only [mem_uIoc, ofPred_or, ofPred_and]
  exact ((measurableSet_lt hf measurable_const).inter (measurableSet_le measurable_const hg)).union
    ((measurableSet_lt hg measurable_const).inter (measurableSet_le measurable_const hf))
