/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Support.Weight
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Uniform fixed-weight bit strings

Mapping a uniform fixed-cardinality subset of `range n` to its Boolean indicator gives the
uniform law on bit strings of the same fixed weight.

## Main results

* `Cslib.Probability.PMF.uniformOfFinset_map_indicatorVector`: the exact distributional bridge
  from uniform supports to uniform fixed-weight bit strings.
-/

public section

namespace Cslib.Probability.PMF

open BitString Finset

/-- A uniform `w`-element subset of `range n`, represented by its indicator, is a uniform
`n`-bit string of weight `w`. -/
theorem uniformOfFinset_map_indicatorVector {n w : ℕ} (hw : w ≤ n) :
    (uniformOfFinset ((range n).powersetCard w)
      (powersetCard_nonempty.mpr (by simp [hw]))).map (indicatorVector n) =
      uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw) := by
  have : Nonempty ↥((range n).powersetCard w) :=
    (powersetCard_nonempty.mpr (by simp [hw])).coe_sort
  have : Nonempty ↥(weightLayer n w) := (weightLayer_nonempty hw).coe_sort
  have hindicator : indicatorVector n ∘ Subtype.val =
      Subtype.val ∘ (fixedSupportEquiv n w) := by
    funext S
    simp
  rw [← uniformOfFintype_finset_map_val, PMF.map_comp]
  calc
    (uniformOfFintype ↥((range n).powersetCard w)).map
        (indicatorVector n ∘ Subtype.val) =
      (uniformOfFintype ↥(weightLayer n w)).map Subtype.val := by
        rw [← uniformOfFintype_map_equiv (fixedSupportEquiv n w), PMF.map_comp]
        rw [hindicator]
    _ = uniformOfFinset (weightLayer n w) (weightLayer_nonempty hw) :=
      uniformOfFintype_finset_map_val _

end Cslib.Probability.PMF
