/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.SpecialFunctions.PolynomialSwitch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial preparation, score, and witness cutoffs

These are concrete polynomial versions of the atom threshold template in
[OpenAI2026LogSpace, (5.5)] and the broad witness in the proof of its support-margin lemma.
For a fixed support scale `θ > 0`, they define the preparation `hθ(v) Rθ(r)`, auxiliary score
`Iθ(v,r)`, and witness `Jθ(v,r)`. They take values in `[0,1]`, have globally Lipschitz fourth
roots jointly in the entry and rank, and use rational arithmetic when their inputs are rational.

Their entry-zero and rank-closure thresholds `(e,g)` are respectively
`(θ/2, θ/500)`, `(θ/8, θ/50)`, and `(82θ/1000, 27θ/1000)`. Each has `3g < e`, including the
witness's strict margin `θ/1000`. All rank factors are one near zero. These are scalar laws for
the concrete row functions, suitable for the stationary-reference compression comparison.
The first argument is the full raw entry and the second is the prescribed full-row rank;
only function evaluation applies the switches' scalar clipping.

This is the fourth-moment adaptation in complexitylib issue #1721. The pinned preprint uses
eighth roots. These polynomial cutoffs do not replace the existing exponential `AtomCutoffs`
API, which proves regularity for every positive power. Normalized main atom functions, access
enumeration, eighth-root regularity, and machine-resource bounds are separate obligations.

## Main definitions

* `Cslib.polynomialPrepCutoff4`, `Cslib.polynomialRowCutoff4`: the preparatory and row factors.
* `Cslib.polynomialPrepRow4`, `Cslib.polynomialAuxCutoff4`, `Cslib.polynomialWitnessCutoff4`:
  the three concrete pre-incoming row functions.

## Main results

* The endpoint, rank-flatness, and range lemmas for each function.
* `Cslib.exists_abs_polynomialPrepRow4_root_sub_le`,
  `Cslib.exists_abs_polynomialAuxCutoff4_root_sub_le`,
  `Cslib.exists_abs_polynomialWitnessCutoff4_root_sub_le`: joint fourth-root bounds.
* The `*_ratCast` lemmas: exact compatibility with rational evaluation.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 5.1, (5.5), support-margin lemma and compression-threshold table in Section 5.5
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib

section Definitions

variable {R : Type*} [Field R] [LinearOrder R]

/-- The polynomial preparation factor with transition from `θ/2` to `3θ/4`. -/
@[expose] def polynomialPrepCutoff4 (θ v : R) : R :=
  polynomialSwitch4 (θ / 2) (3 * θ / 4) v

/-- The polynomial row gate, full through `θ/1000` and closed from `θ/500`. -/
@[expose] def polynomialRowCutoff4 (θ r : R) : R :=
  1 - polynomialSwitch4 (θ / 1000) (θ / 500) r

/-- The actual unnormalized pre-incoming preparation `hθ(v) Rθ(r)`. -/
@[expose] def polynomialPrepRow4 (θ v r : R) : R :=
  polynomialPrepCutoff4 θ v * polynomialRowCutoff4 θ r

/-- The auxiliary score with the threshold intervals of [OpenAI2026LogSpace, (5.5)]. -/
@[expose] def polynomialAuxCutoff4 (θ v r : R) : R :=
  polynomialSwitch4 (θ / 8) (θ / 4) v *
    (1 - polynomialSwitch4 (θ / 100) (θ / 50) r)

/-- The broad analytical witness `Jθ` of the support-margin lemma. Its support is not required
to have a further witness. -/
@[expose] def polynomialWitnessCutoff4 (θ v r : R) : R :=
  polynomialSwitch4 (82 * θ / 1000) (90 * θ / 1000) v *
    (1 - polynomialSwitch4 (26 * θ / 1000) (27 * θ / 1000) r)

end Definitions

variable {θ v r : ℝ}

/-! ## Range and threshold laws -/

theorem polynomialPrepCutoff4_nonneg (θ v : ℝ) : 0 ≤ polynomialPrepCutoff4 θ v :=
  polynomialSwitch4_nonneg _ _ _

theorem polynomialPrepCutoff4_le_one (θ v : ℝ) : polynomialPrepCutoff4 θ v ≤ 1 :=
  polynomialSwitch4_le_one _ _ _

theorem polynomialPrepCutoff4_eq_zero (hθ : 0 < θ) (hv : v ≤ θ / 2) :
    polynomialPrepCutoff4 θ v = 0 := polynomialSwitch4_of_le (by linarith) hv

theorem polynomialPrepCutoff4_eq_one (hθ : 0 < θ) (hv : 3 * θ / 4 ≤ v) :
    polynomialPrepCutoff4 θ v = 1 := polynomialSwitch4_of_ge (by linarith) hv

theorem polynomialRowCutoff4_nonneg (θ r : ℝ) : 0 ≤ polynomialRowCutoff4 θ r :=
  sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _)

theorem polynomialRowCutoff4_le_one (θ r : ℝ) : polynomialRowCutoff4 θ r ≤ 1 :=
  sub_le_self _ (polynomialSwitch4_nonneg _ _ _)

theorem polynomialRowCutoff4_eq_one (hθ : 0 < θ) (hr : r ≤ θ / 1000) :
    polynomialRowCutoff4 θ r = 1 := by
  rw [polynomialRowCutoff4, polynomialSwitch4_of_le (by linarith) hr, sub_zero]

theorem polynomialRowCutoff4_eq_zero_iff (hθ : 0 < θ) :
    polynomialRowCutoff4 θ r = 0 ↔ θ / 500 ≤ r := by
  rw [polynomialRowCutoff4, sub_eq_zero, eq_comm, polynomialSwitch4_eq_one_iff (by linarith)]

theorem polynomialRowCutoff4_eq_zero (hθ : 0 < θ) (hr : θ / 500 ≤ r) :
    polynomialRowCutoff4 θ r = 0 := (polynomialRowCutoff4_eq_zero_iff hθ).mpr hr

theorem polynomialPrepRow4_nonneg (θ v r : ℝ) : 0 ≤ polynomialPrepRow4 θ v r :=
  mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (polynomialRowCutoff4_nonneg _ _)

theorem polynomialPrepRow4_le_one (θ v r : ℝ) : polynomialPrepRow4 θ v r ≤ 1 :=
  (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _)
    (polynomialRowCutoff4_le_one _ _)).trans (polynomialPrepCutoff4_le_one _ _)

theorem polynomialPrepRow4_eq_zero_of_entry_le (hθ : 0 < θ) (hv : v ≤ θ / 2) :
    polynomialPrepRow4 θ v r = 0 := by
  rw [polynomialPrepRow4, polynomialPrepCutoff4_eq_zero hθ hv, zero_mul]

theorem polynomialPrepRow4_eq_zero_of_rank_ge (hθ : 0 < θ) (hr : θ / 500 ≤ r) :
    polynomialPrepRow4 θ v r = 0 := by
  rw [polynomialPrepRow4, polynomialRowCutoff4_eq_zero hθ hr, mul_zero]

theorem polynomialPrepRow4_of_rank_le (hθ : 0 < θ) (hr : r ≤ θ / 1000) :
    polynomialPrepRow4 θ v r = polynomialPrepCutoff4 θ v := by
  rw [polynomialPrepRow4, polynomialRowCutoff4_eq_one hθ hr, mul_one]

theorem polynomialAuxCutoff4_nonneg (θ v r : ℝ) : 0 ≤ polynomialAuxCutoff4 θ v r :=
  mul_nonneg (polynomialSwitch4_nonneg _ _ _) (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _))

theorem polynomialAuxCutoff4_le_one (θ v r : ℝ) : polynomialAuxCutoff4 θ v r ≤ 1 :=
  (mul_le_of_le_one_right (polynomialSwitch4_nonneg _ _ _)
    (sub_le_self _ (polynomialSwitch4_nonneg _ _ _))).trans (polynomialSwitch4_le_one _ _ _)

theorem polynomialAuxCutoff4_eq_zero_of_entry_le (hθ : 0 < θ) (hv : v ≤ θ / 8) :
    polynomialAuxCutoff4 θ v r = 0 := by
  rw [polynomialAuxCutoff4, polynomialSwitch4_of_le (by linarith) hv, zero_mul]

theorem polynomialAuxCutoff4_eq_zero_of_rank_ge (hθ : 0 < θ) (hr : θ / 50 ≤ r) :
    polynomialAuxCutoff4 θ v r = 0 := by
  rw [polynomialAuxCutoff4, polynomialSwitch4_of_ge (by linarith) hr, sub_self, mul_zero]

theorem polynomialAuxCutoff4_of_rank_le (hθ : 0 < θ) (hr : r ≤ θ / 100) :
    polynomialAuxCutoff4 θ v r = polynomialSwitch4 (θ / 8) (θ / 4) v := by
  rw [polynomialAuxCutoff4, polynomialSwitch4_of_le (by linarith) hr, sub_zero, mul_one]

theorem polynomialAuxCutoff4_eq_one (hθ : 0 < θ) (hv : θ / 4 ≤ v) (hr : r ≤ θ / 100) :
    polynomialAuxCutoff4 θ v r = 1 := by
  rw [polynomialAuxCutoff4_of_rank_le hθ hr, polynomialSwitch4_of_ge (by linarith) hv]

/-- On the support relevant to the incoming cap, the concrete auxiliary score is one. -/
theorem polynomialAuxCutoff4_eq_one_of_rowCutoff_ne_zero (hθ : 0 < θ) (hv : θ / 4 ≤ v)
    (hr : polynomialRowCutoff4 θ r ≠ 0) : polynomialAuxCutoff4 θ v r = 1 := by
  have hsmall : r < θ / 500 := lt_of_not_ge fun h => hr (polynomialRowCutoff4_eq_zero hθ h)
  exact polynomialAuxCutoff4_eq_one hθ hv (by linarith)

theorem polynomialWitnessCutoff4_nonneg (θ v r : ℝ) : 0 ≤ polynomialWitnessCutoff4 θ v r :=
  mul_nonneg (polynomialSwitch4_nonneg _ _ _) (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _))

theorem polynomialWitnessCutoff4_le_one (θ v r : ℝ) : polynomialWitnessCutoff4 θ v r ≤ 1 :=
  (mul_le_of_le_one_right (polynomialSwitch4_nonneg _ _ _)
    (sub_le_self _ (polynomialSwitch4_nonneg _ _ _))).trans (polynomialSwitch4_le_one _ _ _)

theorem polynomialWitnessCutoff4_eq_zero_of_entry_le (hθ : 0 < θ) (hv : v ≤ 82 * θ / 1000) :
    polynomialWitnessCutoff4 θ v r = 0 := by
  rw [polynomialWitnessCutoff4, polynomialSwitch4_of_le (by linarith) hv, zero_mul]

theorem polynomialWitnessCutoff4_eq_zero_of_rank_ge (hθ : 0 < θ) (hr : 27 * θ / 1000 ≤ r) :
    polynomialWitnessCutoff4 θ v r = 0 := by
  rw [polynomialWitnessCutoff4, polynomialSwitch4_of_ge (by linarith) hr, sub_self, mul_zero]

theorem polynomialWitnessCutoff4_of_rank_le (hθ : 0 < θ) (hr : r ≤ 26 * θ / 1000) :
    polynomialWitnessCutoff4 θ v r = polynomialSwitch4 (82 * θ / 1000) (90 * θ / 1000) v := by
  rw [polynomialWitnessCutoff4, polynomialSwitch4_of_le (by linarith) hr, sub_zero, mul_one]

theorem polynomialWitnessCutoff4_eq_one (hθ : 0 < θ) (hv : 90 * θ / 1000 ≤ v)
    (hr : r ≤ 26 * θ / 1000) : polynomialWitnessCutoff4 θ v r = 1 := by
  rw [polynomialWitnessCutoff4_of_rank_le hθ hr, polynomialSwitch4_of_ge (by linarith) hv]

/-! ## Joint fourth-root regularity -/

private theorem exists_abs_switch_product_root_sub_le (α β γ δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v r v' r',
      |(polynomialSwitch4 α β v * (1 - polynomialSwitch4 γ δ r)) ^ (4⁻¹ : ℝ) -
        (polynomialSwitch4 α β v' * (1 - polynomialSwitch4 γ δ r')) ^ (4⁻¹ : ℝ)| ≤
          C * (|v - v'| + |r - r'|) := by
  obtain ⟨Ka, hKa⟩ := exists_lipschitzWith_polynomialSwitch4_root α β
  obtain ⟨Kb, hKb⟩ := exists_lipschitzWith_one_sub_polynomialSwitch4_root γ δ
  refine ⟨max (Ka : ℝ) Kb, le_max_of_le_left Ka.2, ?_⟩
  intro v r v' r'
  set A : ℝ → ℝ := fun x => polynomialSwitch4 α β x ^ (4⁻¹ : ℝ)
  set B : ℝ → ℝ := fun x => (1 - polynomialSwitch4 γ δ x) ^ (4⁻¹ : ℝ)
  have ha0 (x : ℝ) : 0 ≤ A x := Real.rpow_nonneg (polynomialSwitch4_nonneg _ _ _) _
  have hb0 (x : ℝ) : 0 ≤ B x :=
    Real.rpow_nonneg (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _)) _
  have ha1 (x : ℝ) : A x ≤ 1 :=
    Real.rpow_le_one (polynomialSwitch4_nonneg _ _ _) (polynomialSwitch4_le_one _ _ _)
      (by norm_num)
  have hb1 (x : ℝ) : B x ≤ 1 :=
    Real.rpow_le_one (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _))
      (sub_le_self _ (polynomialSwitch4_nonneg _ _ _)) (by norm_num)
  have hda : |A v - A v'| ≤ Ka * |v - v'| := by
    simpa only [Real.dist_eq] using hKa.dist_le_mul v v'
  have hdb : |B r - B r'| ≤ Kb * |r - r'| := by
    simpa only [Real.dist_eq] using hKb.dist_le_mul r r'
  rw [Real.mul_rpow (polynomialSwitch4_nonneg _ _ _)
      (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _)),
    Real.mul_rpow (polynomialSwitch4_nonneg _ _ _)
      (sub_nonneg.mpr (polynomialSwitch4_le_one _ _ _))]
  change |A v * B r - A v' * B r'| ≤ _
  have hsplit : A v * B r - A v' * B r' =
      (A v - A v') * B r + A v' * (B r - B r') := by ring
  rw [hsplit]
  calc
    _ ≤ |A v - A v'| * B r + A v' * |B r - B r'| := by
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hb0 r), abs_of_nonneg (ha0 v')]
    _ ≤ |A v - A v'| + |B r - B r'| := by
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hb1 r))
        (mul_le_of_le_one_left (abs_nonneg _) (ha1 v'))
    _ ≤ (Ka : ℝ) * |v - v'| + (Kb : ℝ) * |r - r'| := add_le_add hda hdb
    _ ≤ max (Ka : ℝ) Kb * (|v - v'| + |r - r'|) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

/-- The actual preparatory row function has a globally Lipschitz fourth root. -/
theorem exists_abs_polynomialPrepRow4_root_sub_le (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v r v' r',
      |polynomialPrepRow4 θ v r ^ (4⁻¹ : ℝ) - polynomialPrepRow4 θ v' r' ^ (4⁻¹ : ℝ)| ≤
        C * (|v - v'| + |r - r'|) :=
  exists_abs_switch_product_root_sub_le _ _ _ _

/-- The actual auxiliary score has a globally Lipschitz fourth root. -/
theorem exists_abs_polynomialAuxCutoff4_root_sub_le (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v r v' r',
      |polynomialAuxCutoff4 θ v r ^ (4⁻¹ : ℝ) - polynomialAuxCutoff4 θ v' r' ^ (4⁻¹ : ℝ)| ≤
        C * (|v - v'| + |r - r'|) :=
  exists_abs_switch_product_root_sub_le _ _ _ _

/-- The broad witness also has a globally Lipschitz fourth root. -/
theorem exists_abs_polynomialWitnessCutoff4_root_sub_le (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v r v' r',
      |polynomialWitnessCutoff4 θ v r ^ (4⁻¹ : ℝ) -
        polynomialWitnessCutoff4 θ v' r' ^ (4⁻¹ : ℝ)| ≤ C * (|v - v'| + |r - r'|) :=
  exists_abs_switch_product_root_sub_le _ _ _ _

/-! ## Exact rational evaluation -/

@[simp, norm_cast]
theorem polynomialPrepCutoff4_ratCast (θ v : ℚ) :
    polynomialPrepCutoff4 (θ : ℝ) v = (polynomialPrepCutoff4 θ v : ℚ) := by
  simp only [polynomialPrepCutoff4, ← polynomialSwitch4_ratCast, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat]

@[simp, norm_cast]
theorem polynomialRowCutoff4_ratCast (θ r : ℚ) :
    polynomialRowCutoff4 (θ : ℝ) r = (polynomialRowCutoff4 θ r : ℚ) := by
  simp only [polynomialRowCutoff4, Rat.cast_sub, Rat.cast_one, ← polynomialSwitch4_ratCast,
    Rat.cast_div, Rat.cast_ofNat]

@[simp, norm_cast]
theorem polynomialPrepRow4_ratCast (θ v r : ℚ) :
    polynomialPrepRow4 (θ : ℝ) v r = (polynomialPrepRow4 θ v r : ℚ) := by
  simp only [polynomialPrepRow4, polynomialPrepCutoff4_ratCast, polynomialRowCutoff4_ratCast,
    Rat.cast_mul]

@[simp, norm_cast]
theorem polynomialAuxCutoff4_ratCast (θ v r : ℚ) :
    polynomialAuxCutoff4 (θ : ℝ) v r = (polynomialAuxCutoff4 θ v r : ℚ) := by
  simp only [polynomialAuxCutoff4, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    ← polynomialSwitch4_ratCast, Rat.cast_div, Rat.cast_ofNat]

@[simp, norm_cast]
theorem polynomialWitnessCutoff4_ratCast (θ v r : ℚ) :
    polynomialWitnessCutoff4 (θ : ℝ) v r = (polynomialWitnessCutoff4 θ v r : ℚ) := by
  simp only [polynomialWitnessCutoff4, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
    ← polynomialSwitch4_ratCast, Rat.cast_div, Rat.cast_ofNat]

end Cslib
