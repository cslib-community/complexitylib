/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.OneSided
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.Threshold

/-!
# Query complexity measures of threshold functions and parity

The threshold function `Th^n_j` says that at least `j` of `n` bits are true. A coordinate `i` is
sensitive for it at `x` exactly when `x` has weight `j` and `x i` is true, or (for `j ≥ 1`) weight
`j - 1` and `x i` is false (`BitString.isSensitiveCoord_threshold_iff`). So the sensitivity is `j`
at an input of weight `j` and `n + 1 - j` at an input of weight `j - 1`. Conversely `j` true bits
certify the value `1` and `n + 1 - j` false bits certify the value `0`
(`QueryComplexity.certificateComplexityAt_threshold_le`). With `s(f) ≤ bs(f) ≤ C(f)` all three
measures agree: for `1 ≤ j ≤ n`,
`s(Th^n_j) = bs(Th^n_j) = C(Th^n_j) = max(j, n + 1 - j)`.
In particular majority has sensitivity `⌊n/2⌋ + 1` for `n ≥ 1`. The disjunction `OR_n = Th^n_1`
is sensitive to every bit at the all-false input, so `bs(OR_n) = n`. A single true bit certifies
its value `1`, while certifying the value `0` takes all `n` bits.
Flipping any bit flips the parity, so parity is sensitive to every bit at every input
(`BitString.sensitivityAt_parity`), and its sensitivity, block sensitivity and certificate
complexity all equal `n`. The measures are those of [BuhrmanDeWolf2002].

## Main results

* `Cslib.BitString.isSensitiveCoord_threshold_iff`: the sensitive coordinates of `Th^n_j`.
* `Cslib.BitString.sensitivity_threshold`, `Cslib.QueryComplexity.blockSensitivity_threshold`,
  `Cslib.QueryComplexity.certificateComplexity_threshold`: `s`, `bs` and `C` of `Th^n_j` are
  `max(j, n + 1 - j)` for `1 ≤ j ≤ n`.
* `Cslib.BitString.sensitivity_majority`: `s(MAJ_n) = ⌊n/2⌋ + 1` for `n ≥ 1`.
* `Cslib.QueryComplexity.blockSensitivity_threshold_one_right`: `bs(OR_n) = n`.
* `Cslib.QueryComplexity.certificateComplexity_threshold_one_right`: `C(OR_n) = n`.
* `Cslib.QueryComplexity.certificateComplexityFor_threshold_one_right_true`,
  `Cslib.QueryComplexity.certificateComplexityFor_threshold_one_right_false`: `C₁(OR_n) = 1` for
  `n ≥ 1`, and `C₀(OR_n) = n`.
* `Cslib.BitString.sensitivity_parity`, `Cslib.QueryComplexity.blockSensitivity_parity`,
  `Cslib.QueryComplexity.certificateComplexity_parity`: `s`, `bs` and `C` of `parity n` are `n`.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

public section

namespace Cslib

open Finset

variable {n j : ℕ}

namespace BitString

/-- A coordinate is sensitive for `Th^n_j` exactly when it is a true bit of an input of weight
`j`, or (for `j ≥ 1`) a false bit of an input of weight `j - 1`. -/
theorem isSensitiveCoord_threshold_iff (x : BitString n) (i : Fin n) :
    IsSensitiveCoord (threshold n j) x i ↔
      x i = true ∧ weight x = j ∨ x i = false ∧ weight x + 1 = j := by
  unfold IsSensitiveCoord
  cases hx : x i with
  | true =>
    have h := weight_update_false hx
    simp only [Bool.not_true, threshold_apply, ne_eq, decide_eq_decide, Bool.true_eq_false,
      true_and, false_and, or_false]
    omega
  | false =>
    have h := weight_update_true hx
    simp only [Bool.not_false, threshold_apply, ne_eq, decide_eq_decide, h, Bool.false_eq_true,
      true_and, false_and, false_or]
    omega

/-- At an input of weight `j`, the sensitive coordinates of `Th^n_j` are its true bits. -/
theorem sensitivityAt_threshold_of_weight_eq {x : BitString n} (hx : weight x = j) :
    sensitivityAt (threshold n j) x = j := by
  have : sensitiveCoords (threshold n j) x = univ.filter fun i => x i = true := by
    ext i
    simp [isSensitiveCoord_threshold_iff, hx]
  rw [sensitivityAt, this, ← weight, hx]

/-- At an input of weight `j - 1`, for `j ≥ 1`, the sensitive coordinates of `Th^n_j` are its
false bits. -/
theorem sensitivityAt_threshold_of_weight_add_one_eq {x : BitString n}
    (hx : weight x + 1 = j) : sensitivityAt (threshold n j) x = n + 1 - j := by
  have : sensitiveCoords (threshold n j) x = univ.filter fun i => x i = false := by
    ext i
    have h : weight x ≠ j := by omega
    simp [isSensitiveCoord_threshold_iff, h, hx]
  rw [sensitivityAt, this, card_filter_eq_false_eq_card_sub_weight, Fintype.card_fin]
  omega

end BitString

open BitString

namespace QueryComplexity

/-- Certificate complexity of `Th^n_j` at any input is at most `max(j, n + 1 - j)`: `j` true bits
certify the value `1`, and `n + 1 - j` false bits certify the value `0`. -/
theorem certificateComplexityAt_threshold_le (x : BitString n) :
    certificateComplexityAt (threshold n j) x ≤ max j (n + 1 - j) := by
  have hwy := weight_le_length (n := n)
  by_cases hw : j ≤ weight x
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (s := univ.filter fun i => x i = true)
      (n := j) (by rwa [← weight])
    refine (certificateComplexityAt_le (S := S) fun y hy => ?_).trans
      (hcard.le.trans (le_max_left _ _))
    have hle : #S ≤ weight y := card_le_card fun i hi => by
      have := (mem_filter.1 (hS hi)).2
      simp [hy i hi, this]
    simp only [threshold_apply, decide_eq_decide]
    omega
  · obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (s := univ.filter fun i => x i = false)
      (n := n + 1 - j) (by
        rw [card_filter_eq_false_eq_card_sub_weight, Fintype.card_fin]; have := hwy x; omega)
    refine (certificateComplexityAt_le (S := S) fun y hy => ?_).trans
      (hcard.le.trans (le_max_right _ _))
    have hle : #S ≤ #{i | y i = false} := card_le_card fun i hi => by
      have := (mem_filter.1 (hS hi)).2
      simp [hy i hi, this]
    rw [card_filter_eq_false_eq_card_sub_weight, Fintype.card_fin] at hle
    have := hwy y
    simp only [threshold_apply, decide_eq_decide]
    omega

/-- `bs(Th^n_j) ≤ max(j, n + 1 - j)`. -/
theorem blockSensitivity_threshold_le :
    blockSensitivity (threshold n j) ≤ max j (n + 1 - j) :=
  (blockSensitivity_le_certificateComplexity _).trans
    (Finset.sup_le fun x _ => certificateComplexityAt_threshold_le x)

end QueryComplexity

namespace BitString

/-- **Sensitivity of threshold functions**: `s(Th^n_j) = max(j, n + 1 - j)` for `1 ≤ j ≤ n`. -/
theorem sensitivity_threshold (hj : 1 ≤ j) (hjn : j ≤ n) :
    sensitivity (threshold n j) = max j (n + 1 - j) := by
  refine le_antisymm ((QueryComplexity.sensitivity_le_blockSensitivity _).trans
    QueryComplexity.blockSensitivity_threshold_le) (max_le ?_ ?_)
  · obtain ⟨x, hx⟩ := weightLayer_nonempty (n := n) hjn
    rw [mem_weightLayer] at hx
    exact (sensitivityAt_threshold_of_weight_eq hx).ge.trans (sensitivityAt_le_sensitivity _ x)
  · obtain ⟨x, hx⟩ := weightLayer_nonempty (n := n) (k := j - 1) (by omega)
    rw [mem_weightLayer] at hx
    exact (sensitivityAt_threshold_of_weight_add_one_eq (by omega)).ge.trans
      (sensitivityAt_le_sensitivity _ x)

/-- **Sensitivity of majority**: `s(MAJ_n) = ⌊n/2⌋ + 1` for `n ≥ 1`. -/
theorem sensitivity_majority (hn : 1 ≤ n) : sensitivity (majority n) = n / 2 + 1 := by
  rw [majority, sensitivity_threshold (by omega) (by omega)]
  omega

end BitString

namespace QueryComplexity

/-- **Block sensitivity of threshold functions**: `bs(Th^n_j) = max(j, n + 1 - j)` for
`1 ≤ j ≤ n`. -/
theorem blockSensitivity_threshold (hj : 1 ≤ j) (hjn : j ≤ n) :
    blockSensitivity (threshold n j) = max j (n + 1 - j) :=
  le_antisymm blockSensitivity_threshold_le
    ((sensitivity_threshold hj hjn).ge.trans (sensitivity_le_blockSensitivity _))

/-- **Certificate complexity of threshold functions**: `C(Th^n_j) = max(j, n + 1 - j)` for
`1 ≤ j ≤ n`. -/
theorem certificateComplexity_threshold (hj : 1 ≤ j) (hjn : j ≤ n) :
    certificateComplexity (threshold n j) = max j (n + 1 - j) :=
  le_antisymm (Finset.sup_le fun x _ => certificateComplexityAt_threshold_le x)
    ((blockSensitivity_threshold hj hjn).ge.trans (blockSensitivity_le_certificateComplexity _))

/-! ### Disjunction -/

/-- The disjunction of `n` bits is sensitive to every bit at the all-false input. -/
theorem sensitivityAt_threshold_one_right :
    sensitivityAt (threshold n 1) (fun _ => false) = n := by
  rw [sensitivityAt_threshold_of_weight_add_one_eq (by simp [weight]), Nat.add_sub_cancel]

/-- The disjunction of `n` bits has block sensitivity `n`. -/
theorem blockSensitivity_threshold_one_right : blockSensitivity (threshold n 1) = n :=
  le_antisymm (blockSensitivity_le_card _) (sensitivityAt_threshold_one_right.symm.trans_le
    ((sensitivityAt_le_sensitivity _ _).trans (sensitivity_le_blockSensitivity _)))

/-- Certifying the value `0` of the disjunction at the all-false input takes every bit. -/
theorem certificateComplexityAt_threshold_one_right :
    certificateComplexityAt (threshold n 1) (fun _ => false) = n :=
  le_antisymm (certificateComplexityAt_le_card _ _) (sensitivityAt_threshold_one_right.symm.trans_le
    ((sensitivityAt_le_blockSensitivityAt _ _).trans
      (blockSensitivityAt_le_certificateComplexityAt _ _)))

/-- **Certificate complexity of disjunction**: `C(OR_n) = n`. -/
theorem certificateComplexity_threshold_one_right : certificateComplexity (threshold n 1) = n :=
  le_antisymm (certificateComplexity_le_card _)
    (certificateComplexityAt_threshold_one_right.ge.trans
      (certificateComplexityAt_le_certificateComplexity _ _))

/-- One true bit certifies the value `1` of the disjunction: `C₁(OR_n) = 1` for `n ≥ 1`. -/
theorem certificateComplexityFor_threshold_one_right_true (hn : 1 ≤ n) :
    certificateComplexityFor (threshold n 1) true = 1 := by
  apply le_antisymm
  · refine Finset.sup_le fun x hx => ?_
    have hx : threshold n 1 x = true := (mem_filter.1 hx).2
    rw [threshold_one_right, decide_eq_true_iff] at hx
    obtain ⟨i, hi⟩ := hx
    refine (certificateComplexityAt_le (S := {i}) fun y hy => ?_).trans (by simp)
    rw [threshold_one_right, threshold_one_right, decide_eq_decide]
    exact ⟨fun _ => ⟨i, hi⟩, fun _ => ⟨i, (hy i (mem_singleton_self i)).trans hi⟩⟩
  · have hx : threshold n 1 (fun _ => true) = true := by
      rw [threshold_one_right, decide_eq_true_iff]
      exact ⟨⟨0, hn⟩, rfl⟩
    refine le_trans ?_ (certificateComplexityAt_le_certificateComplexityFor hx)
    refine le_certificateComplexityAt fun S hS => ?_
    rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero]
    rintro rfl
    have := hS (fun _ => false) (by simp)
    rw [hx, threshold_one_right] at this
    simp at this

/-- Certifying the value `0` of the disjunction takes every bit: `C₀(OR_n) = n`. -/
theorem certificateComplexityFor_threshold_one_right_false :
    certificateComplexityFor (threshold n 1) false = n := by
  refine le_antisymm (Finset.sup_le fun x _ => certificateComplexityAt_le_card _ x) ?_
  have hx : threshold n 1 (fun _ => false) = false := by grind [threshold_one_right]
  exact certificateComplexityAt_threshold_one_right.ge.trans
    (certificateComplexityAt_le_certificateComplexityFor hx)

end QueryComplexity

/-! ### Parity -/

namespace BitString

/-- Parity is sensitive to every bit at every input. -/
theorem sensitivityAt_parity (x : BitString n) : sensitivityAt (parity n) x = n := by
  have : (univ.filter fun i => parity n (Function.update x i !x i) ≠ parity n x) = univ := by
    refine eq_univ_of_forall fun i => mem_filter.2 ⟨mem_univ i, ?_⟩
    rw [parity, parityOn_update_not (mem_univ i)]
    cases parityOn univ x <;> decide
  change #(univ.filter fun i => parity n (Function.update x i !x i) ≠ parity n x) = n
  rw [this, card_univ, Fintype.card_fin]

/-- The sensitivity of parity is its number of coordinates. -/
theorem sensitivity_parity : sensitivity (parity n) = n :=
  le_antisymm (sensitivity_le_card _) ((sensitivityAt_parity (fun _ => false)).symm.trans_le
    (sensitivityAt_le_sensitivity _ _))

end BitString

namespace QueryComplexity

/-- The block sensitivity of parity is its number of coordinates. -/
theorem blockSensitivity_parity : blockSensitivity (parity n) = n :=
  le_antisymm (blockSensitivity_le_card _)
    (sensitivity_parity.symm.trans_le (sensitivity_le_blockSensitivity _))

/-- The certificate complexity of parity is its number of coordinates. -/
theorem certificateComplexity_parity : certificateComplexity (parity n) = n :=
  le_antisymm (certificateComplexity_le_card _)
    (blockSensitivity_parity.symm.trans_le (blockSensitivity_le_certificateComplexity _))

end QueryComplexity

end Cslib
