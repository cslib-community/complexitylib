/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Defs
public import CslibFrontier.Foundations.Data.BitString.Flip
public import Cslib.Computability.QueryComplexity.Measures

/-!
# Superquadratic sensitivity separation: agreement with the CSLib measures

The separation construction works with its own measures over an arbitrary finite coordinate type
(`Internal.sensitivity`, `Internal.blockSensitivity`), defined in terms of `BitString.flipOn`,
since it composes functions on product coordinate types. On the coordinates `Fin n` these agree
with CSLib's `BitString.flipBlock`, `BitString.sensitivity` and `QueryComplexity.blockSensitivity`.
Internal block families must consist of nonempty blocks, but this is no restriction: flipping
the empty block never changes the value of a function.

## Main results

* `Cslib.BitString.flipOn_eq_flipBlock`: on `Fin n`, `BitString.flipOn` is `BitString.flipBlock`.
* `Internal.sensitivity_eq_bitString_sensitivity`: the internal sensitivity is
  `BitString.sensitivity`.
* `Internal.blockSensitivityAt_eq_queryComplexity_blockSensitivityAt`,
  `Internal.blockSensitivity_eq_queryComplexity_blockSensitivity`: the internal block sensitivity is
  `QueryComplexity.blockSensitivity`, pointwise and globally.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation.Internal

open Finset

variable {n : ℕ}

/-- On `Fin n`, `BitString.flipOn` (with any `DecidableEq (Fin n)` instance) is CSLib's
`BitString.flipBlock`. -/
@[simp] theorem _root_.Cslib.BitString.flipOn_eq_flipBlock {inst : DecidableEq (Fin n)}
    (T : Finset (Fin n)) (x : BitString n) :
    @BitString.flipOn (Fin n) inst T x = BitString.flipBlock T x := by
  funext i
  simp [BitString.flipOn, BitString.flipBlock]

/-- On `Fin n`, the internal pointwise sensitivity is `BitString.sensitivityAt`. -/
private theorem sensitivityAt_eq_bitString_sensitivityAt (f : BooleanFunction n) (x : BitString n) :
    sensitivityAt f x = BitString.sensitivityAt f x := by
  unfold sensitivityAt BitString.sensitivityAt BitString.sensitiveCoords
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, BitString.IsSensitiveCoord,
    BitString.flipOn_eq_flipBlock, BitString.flipBlock_singleton]

/-- On `Fin n`, the internal sensitivity is `BitString.sensitivity`. -/
theorem sensitivity_eq_bitString_sensitivity (f : BooleanFunction n) :
    sensitivity f = BitString.sensitivity f := by
  refine le_antisymm (Finset.sup_le fun x _ => ?_) (Finset.sup_le fun x _ => ?_)
  · exact (sensitivityAt_eq_bitString_sensitivityAt f x).trans_le
      (BitString.sensitivityAt_le_sensitivity f x)
  · exact (sensitivityAt_eq_bitString_sensitivityAt f x).symm.trans_le (Finset.le_sup (by simp))

/-- On `Fin n`, the internal pointwise block sensitivity is
`QueryComplexity.blockSensitivityAt`. -/
theorem blockSensitivityAt_eq_queryComplexity_blockSensitivityAt (f : BooleanFunction n)
    (x : BitString n) :
    blockSensitivityAt f x = QueryComplexity.blockSensitivityAt f x := by
  classical
  refine le_antisymm (Finset.sup_le fun F _ => ?_) (Finset.sup_le fun F hF => ?_)
  · split_ifs with h
    · refine card_le_blockSensitivityAt ⟨fun B hB => ?_, fun A hA B hB hAB => h.1 A hA B hB hAB⟩
      simpa only [IsSensitiveBlock, BitString.flipOn_eq_flipBlock] using (h.2 B hB).2
    · exact Nat.zero_le _
  · obtain ⟨hsens, hdisj⟩ := mem_sensitiveFamilies.mp hF
    refine Finset.le_sup_of_le (mem_univ F) ?_
    split_ifs with h
    · rfl
    · exfalso
      apply h
      refine ⟨fun A hA B hB hAB => hdisj hA hB hAB, fun B hB => ⟨?_, ?_⟩⟩
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hsens _ hB (by rw [BitString.flipBlock_empty])
      · rw [BitString.flipOn_eq_flipBlock]
        exact hsens B hB

/-- On `Fin n`, the internal block sensitivity is `QueryComplexity.blockSensitivity`. -/
theorem blockSensitivity_eq_queryComplexity_blockSensitivity (f : BooleanFunction n) :
    blockSensitivity f = QueryComplexity.blockSensitivity f := by
  refine le_antisymm (Finset.sup_le fun x _ => ?_) (Finset.sup_le fun x _ => ?_)
  · exact (blockSensitivityAt_eq_queryComplexity_blockSensitivityAt f x).trans_le
      (blockSensitivityAt_le_blockSensitivity f x)
  · exact (blockSensitivityAt_eq_queryComplexity_blockSensitivityAt f x).symm.trans_le
      (Finset.le_sup (by simp))

end Cslib.QueryComplexity.SensitivitySeparation.Internal
