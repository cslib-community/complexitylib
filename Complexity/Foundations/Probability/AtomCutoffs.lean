/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.SpecialFunctions.SmoothSwitch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smooth cutoffs of the stochastic atoms

The dense and correction atoms (`Complexity.Foundations.Probability.StochasticAtom`,
`Complexity.Foundations.Probability.CorrectionAtom`) take their cutoff functions as parameters,
with only the threshold properties each statement uses. This file supplies the preprint's explicit
choices, built from the smooth switches `Cslib.smoothSwitch` [OpenAI2026LogSpace, (5.5), (5.12)].
Fix a lower support threshold `ϑ > 0` of a main row function, and let `v` be a scaled entry and `r`
the `K`-th rank of its row:

* the preparatory factor `h_ϑ(v) = χ_{ϑ/2, 3ϑ/4}(v)` (`Cslib.prepCutoff`);
* the row gate `R_ϑ(r) = 1 - χ_{ϑ/1000, ϑ/500}(r)` (`Cslib.rowCutoff`);
* the auxiliary score `I_ϑ(v, r) = χ_{ϑ/8, ϑ/4}(v) (1 - χ_{ϑ/100, ϑ/50}(r))` (`Cslib.auxCutoff`);
* the incoming cutoff `1 - χ_{1/4, 1/2}` (`Cslib.incomingCutoff`).

Each lemma below is a hypothesis of the atom identities or support bounds; for example
`Cslib.auxCutoff_eq_one_of_rowCutoff_ne_zero` is the hypothesis of the incoming cap
(`Matrix.card_filter_correctionAtom_col_ne_zero_lt`) for a main function supported above `ϑ/4`.
Every positive power of each cutoff is Lipschitz, the auxiliary score jointly in both arguments
[OpenAI2026LogSpace, Section 5.1: "Products of bounded functions with Lipschitz `s`th roots again
have Lipschitz `s`th roots"].

## Main definitions

* `Cslib.prepCutoff`, `Cslib.rowCutoff`, `Cslib.auxCutoff`, `Cslib.incomingCutoff`.

## Main results

* `Cslib.prepCutoff_eq_one`, `Cslib.rowCutoff_eq_one`, `Cslib.rowCutoff_eq_zero_iff`,
  `Cslib.auxCutoff_eq_zero`, `Cslib.auxCutoff_eq_one_of_rowCutoff_ne_zero`,
  `Cslib.incomingCutoff_eq_one`, `Cslib.incomingCutoff_eq_zero`: the thresholds.
* `Cslib.exists_lipschitzWith_prepCutoff_rpow`, `Cslib.exists_lipschitzWith_rowCutoff_rpow`,
  `Cslib.exists_lipschitzWith_incomingCutoff_rpow`, `Cslib.exists_abs_auxCutoff_rpow_sub_le`: the
  root-Lipschitz properties.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 5.1 and 5.3 (preprint, not peer reviewed)
-/

public section

namespace Cslib

/-- The preparatory factor `h_ϑ = χ_{ϑ/2, 3ϑ/4}` [OpenAI2026LogSpace, (5.5)]. -/
noncomputable def prepCutoff (ϑ v : ℝ) : ℝ :=
  smoothSwitch (ϑ / 2) (3 * ϑ / 4) v

/-- The row gate `R_ϑ = 1 - χ_{ϑ/1000, ϑ/500}`, applied to the `K`-th rank of a row
[OpenAI2026LogSpace, (5.5)]. -/
noncomputable def rowCutoff (ϑ r : ℝ) : ℝ :=
  1 - smoothSwitch (ϑ / 1000) (ϑ / 500) r

/-- The auxiliary score `I_ϑ(v, r) = χ_{ϑ/8, ϑ/4}(v) (1 - χ_{ϑ/100, ϑ/50}(r))` of an entry `v` with
row rank `r` [OpenAI2026LogSpace, (5.5)]. -/
noncomputable def auxCutoff (ϑ v r : ℝ) : ℝ :=
  smoothSwitch (ϑ / 8) (ϑ / 4) v * (1 - smoothSwitch (ϑ / 100) (ϑ / 50) r)

/-- The incoming cutoff `1 - χ_{1/4, 1/2}`, applied to the `K_c`-th auxiliary rank of a column
[OpenAI2026LogSpace, (5.12)]. -/
noncomputable def incomingCutoff (r : ℝ) : ℝ :=
  1 - smoothSwitch (1 / 4) (1 / 2) r

variable {ϑ v r : ℝ}

/-! ### Thresholds -/

theorem prepCutoff_eq_one (hϑ : 0 < ϑ) (hv : 3 * ϑ / 4 ≤ v) : prepCutoff ϑ v = 1 :=
  smoothSwitch_of_ge (by linarith) hv

theorem prepCutoff_eq_zero (hϑ : 0 < ϑ) (hv : v ≤ ϑ / 2) : prepCutoff ϑ v = 0 :=
  smoothSwitch_of_le (by linarith) hv

theorem rowCutoff_nonneg (ϑ r : ℝ) : 0 ≤ rowCutoff ϑ r :=
  sub_nonneg.2 (smoothSwitch_le_one _ _ _)

theorem rowCutoff_le_one (ϑ r : ℝ) : rowCutoff ϑ r ≤ 1 :=
  sub_le_self _ (smoothSwitch_nonneg _ _ _)

theorem rowCutoff_eq_one (hϑ : 0 < ϑ) (hr : r ≤ ϑ / 1000) : rowCutoff ϑ r = 1 := by
  rw [rowCutoff, smoothSwitch_of_le (by linarith) hr, sub_zero]

theorem rowCutoff_eq_zero_iff (hϑ : 0 < ϑ) : rowCutoff ϑ r = 0 ↔ ϑ / 500 ≤ r := by
  rw [rowCutoff, sub_eq_zero, eq_comm, smoothSwitch_eq_one_iff (by linarith)]

theorem rowCutoff_eq_zero (hϑ : 0 < ϑ) (hr : ϑ / 500 ≤ r) : rowCutoff ϑ r = 0 :=
  (rowCutoff_eq_zero_iff hϑ).2 hr

theorem auxCutoff_nonneg (ϑ v r : ℝ) : 0 ≤ auxCutoff ϑ v r :=
  mul_nonneg (smoothSwitch_nonneg _ _ _) (sub_nonneg.2 (smoothSwitch_le_one _ _ _))

theorem auxCutoff_le_one (ϑ v r : ℝ) : auxCutoff ϑ v r ≤ 1 :=
  (mul_le_of_le_one_right (smoothSwitch_nonneg _ _ _)
    (sub_le_self _ (smoothSwitch_nonneg _ _ _))).trans (smoothSwitch_le_one _ _ _)

theorem auxCutoff_eq_zero (hϑ : 0 < ϑ) (hv : v ≤ ϑ / 8) : auxCutoff ϑ v r = 0 := by
  rw [auxCutoff, smoothSwitch_of_le (by linarith) hv, zero_mul]

theorem auxCutoff_eq_one (hϑ : 0 < ϑ) (hv : ϑ / 4 ≤ v) (hr : r ≤ ϑ / 100) :
    auxCutoff ϑ v r = 1 := by
  rw [auxCutoff, smoothSwitch_of_ge (by linarith) hv, smoothSwitch_of_le (by linarith) hr]
  norm_num

/-- Where the row gate is open and the entry is at least `ϑ/4`, the auxiliary score is one. This
is the hypothesis of the incoming cap [OpenAI2026LogSpace, proof of Lemma 5.6]. -/
theorem auxCutoff_eq_one_of_rowCutoff_ne_zero (hϑ : 0 < ϑ) (hv : ϑ / 4 ≤ v)
    (hr : rowCutoff ϑ r ≠ 0) : auxCutoff ϑ v r = 1 := by
  refine auxCutoff_eq_one hϑ hv ?_
  have := mt (rowCutoff_eq_zero hϑ) hr
  linarith

theorem incomingCutoff_nonneg (r : ℝ) : 0 ≤ incomingCutoff r :=
  sub_nonneg.2 (smoothSwitch_le_one _ _ _)

theorem incomingCutoff_le_one (r : ℝ) : incomingCutoff r ≤ 1 :=
  sub_le_self _ (smoothSwitch_nonneg _ _ _)

theorem incomingCutoff_eq_one (hr : r ≤ 1 / 4) : incomingCutoff r = 1 := by
  rw [incomingCutoff, smoothSwitch_of_le (by norm_num) hr, sub_zero]

theorem incomingCutoff_eq_zero (hr : 1 / 2 ≤ r) : incomingCutoff r = 0 := by
  rw [incomingCutoff, smoothSwitch_of_ge (by norm_num) hr, sub_self]

/-! ### Lipschitz roots -/

variable {p : ℝ}

theorem exists_lipschitzWith_prepCutoff_rpow (hϑ : 0 < ϑ) (hp : 0 < p) :
    ∃ K, LipschitzWith K fun v => prepCutoff ϑ v ^ p :=
  exists_lipschitzWith_smoothSwitch_rpow (by linarith) hp

theorem exists_lipschitzWith_rowCutoff_rpow (hϑ : 0 < ϑ) (hp : 0 < p) :
    ∃ K, LipschitzWith K fun r => rowCutoff ϑ r ^ p :=
  exists_lipschitzWith_one_sub_smoothSwitch_rpow (by linarith) hp

theorem exists_lipschitzWith_incomingCutoff_rpow (hp : 0 < p) :
    ∃ K, LipschitzWith K fun r => incomingCutoff r ^ p :=
  exists_lipschitzWith_one_sub_smoothSwitch_rpow (by norm_num) hp

/-- The positive powers of the auxiliary score are Lipschitz in both arguments. -/
theorem exists_abs_auxCutoff_rpow_sub_le (hϑ : 0 < ϑ) (hp : 0 < p) :
    ∃ L : ℝ, ∀ v r v' r', |auxCutoff ϑ v r ^ p - auxCutoff ϑ v' r' ^ p| ≤
      L * (|v - v'| + |r - r'|) := by
  obtain ⟨Ka, hKa⟩ := exists_lipschitzWith_smoothSwitch_rpow (α := ϑ / 8) (β := ϑ / 4)
    (by linarith) hp
  obtain ⟨Kb, hKb⟩ := exists_lipschitzWith_one_sub_smoothSwitch_rpow (α := ϑ / 100)
    (β := ϑ / 50) (by linarith) hp
  refine ⟨max Ka Kb, fun v r v' r' => ?_⟩
  set a : ℝ → ℝ := fun v => smoothSwitch (ϑ / 8) (ϑ / 4) v
  set b : ℝ → ℝ := fun r => 1 - smoothSwitch (ϑ / 100) (ϑ / 50) r
  have ha0 : ∀ v, 0 ≤ a v := fun v => smoothSwitch_nonneg _ _ _
  have hb0 : ∀ r, 0 ≤ b r := fun r => sub_nonneg.2 (smoothSwitch_le_one _ _ _)
  have ha1 : ∀ v, a v ^ p ≤ 1 := fun v =>
    Real.rpow_le_one (ha0 v) (smoothSwitch_le_one _ _ _) hp.le
  have hb1 : ∀ r, b r ^ p ≤ 1 := fun r =>
    Real.rpow_le_one (hb0 r) (sub_le_self _ (smoothSwitch_nonneg _ _ _)) hp.le
  have hda : |a v ^ p - a v' ^ p| ≤ Ka * |v - v'| := by
    simpa only [Real.dist_eq] using hKa.dist_le_mul v v'
  have hdb : |b r ^ p - b r' ^ p| ≤ Kb * |r - r'| := by
    simpa only [Real.dist_eq] using hKb.dist_le_mul r r'
  have hsplit : auxCutoff ϑ v r ^ p - auxCutoff ϑ v' r' ^ p =
      (a v ^ p - a v' ^ p) * b r ^ p + a v' ^ p * (b r ^ p - b r' ^ p) := by
    simp only [auxCutoff, Real.mul_rpow (ha0 _) (hb0 _), a, b]
    ring
  rw [hsplit]
  have hbp : 0 ≤ b r ^ p := Real.rpow_nonneg (hb0 r) p
  have hap : 0 ≤ a v' ^ p := Real.rpow_nonneg (ha0 v') p
  calc |(a v ^ p - a v' ^ p) * b r ^ p + a v' ^ p * (b r ^ p - b r' ^ p)|
      ≤ |a v ^ p - a v' ^ p| * b r ^ p + a v' ^ p * |b r ^ p - b r' ^ p| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg hbp, abs_of_nonneg hap]
    _ ≤ |a v ^ p - a v' ^ p| * 1 + 1 * |b r ^ p - b r' ^ p| := by
        gcongr
        exacts [hb1 r, ha1 v']
    _ ≤ Ka * |v - v'| + Kb * |r - r'| := by rw [mul_one, one_mul]; exact add_le_add hda hdb
    _ ≤ max Ka Kb * (|v - v'| + |r - r'|) := by
        rw [mul_add]
        gcongr
        exacts [le_max_left (Ka : ℝ) Kb, le_max_right (Ka : ℝ) Kb]

end Cslib
