/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.FormulaMagnification.SublinearAverageCase

/-!
# Clients of Theorem 5 with a rounded threshold and ternary devices

The examples check the rounded threshold at a perfect square, show that the device notion is
neither empty nor trivial, translate an actual one-sided formula at `n = 8` into a zero-error
decider, and instantiate the headline, Section 1.2 and general forms of
[OliveiraSanthanam2018, Section 1.2, Theorem 5, p. 8].
-/

namespace CslibFrontierTests.FormulaMagnificationSublinearAverageCase

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Filter Asymptotics

-- The rounding is exact at perfect squares: `⌊2 ^ √16⌋₊ = 16`.
example : MCSP.sqrtThreshold 16 = 16 :=
  MCSP.sqrtThreshold_sq 4

-- Away from perfect squares the floor matters: `⌊2 ^ √3⌋₊ = 3`, as `3 ^ 5 ≤ 2 ^ 8 ≤ 2 ^ (5 √3)`
-- and `√3 < 2`.
example : MCSP.sqrtThreshold 3 = 3 := by
  have hpos : (0 : ℝ) < 2 ^ Real.sqrt 3 := by positivity
  rw [MCSP.sqrtThreshold, Nat.cast_ofNat, Nat.floor_eq_iff hpos.le]
  constructor
  · have h8 : (8 : ℝ) ≤ Real.sqrt 3 * 5 := by
      have : (8 / 5 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt' (by norm_num) |>.mpr (by norm_num)
      linarith
    have h5 : (3 : ℝ) ^ 5 ≤ (2 ^ Real.sqrt 3) ^ 5 := by
      rw [← Real.rpow_natCast (2 ^ Real.sqrt 3) 5, ← Real.rpow_mul (by norm_num)]
      calc (3 : ℝ) ^ 5 ≤ 2 ^ (8 : ℝ) := by norm_num
        _ ≤ 2 ^ (Real.sqrt 3 * ((5 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    exact_mod_cast (pow_le_pow_iff_left₀ (by norm_num) hpos.le (by norm_num)).mp h5
  · have h2 : Real.sqrt 3 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    calc (2 : ℝ) ^ Real.sqrt 3 < 2 ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
      _ = (3 : ℕ) + 1 := by norm_num

-- The threshold lies between `2 ^ ⌊√n⌋` and `2 ^ (⌊√n⌋ + 1)`.
example (n : ℕ) : 2 ^ Nat.sqrt n ≤ MCSP.sqrtThreshold n ∧
    MCSP.sqrtThreshold n ≤ 2 ^ (Nat.sqrt n + 1) :=
  ⟨MCSP.two_pow_sqrt_le_sqrtThreshold n, MCSP.sqrtThreshold_le n⟩

open Classical in
-- Nonvacuity of the device notion: the exact decider solves `MCSP[s]` at every unknown fraction.
example (s k : ℕ → ℕ) :
    MCSP.SolvesOnAverage s k fun _ T => some (decide (List.ofFn T ∈ GapMCSP.yesSet s)) :=
  MCSP.solvesOnAverage_iff.mpr (Eventually.of_forall fun _ => MCSP.isZeroErrorDecider_decide _)

-- Nontriviality: the device that always answers "?" does not solve MCSP on average with unknown
-- fraction `1 / n`.
example (s : ℕ → ℕ) : ¬ MCSP.SolvesOnAverage s (fun n => n) fun _ _ => none := by
  intro h
  obtain ⟨n, hdec, hn⟩ := (MCSP.solvesOnAverage_iff.mp h).and (eventually_ge_atTop 2) |>.exists
  have hcard := hdec.card_unknown_le
  simp only [Finset.filter_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hcard
  have hpos : 0 < 2 ^ 2 ^ n := by positivity
  nlinarith

-- Every family of formula devices of unrestricted size can solve MCSP exactly: the size bound
-- `o(N)` is what makes the hypothesis of Theorem 5 meaningful.
example (s k : ℕ → ℕ) : ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
    MCSP.SolvesOnAverage s k fun n => (D n).eval := by
  classical
  choose F hF using fun n => Formula.exists_computes
    (fun T : BitString (2 ^ n) => decide (List.ofFn T ∈ GapMCSP.yesSet s))
  refine ⟨fun n => ⟨Formula.const false, F n⟩, MCSP.solvesOnAverage_iff.mpr
    (Eventually.of_forall fun n => ⟨fun T b h => ?_, ?_⟩)⟩
  · simp only [ZeroErrorFormula.eval_eq_some_iff, Formula.eval_const, true_and] at h
    rw [← h, hF n T, decide_eq_true_iff]
  · simp

open Classical in
-- A checked instance at `n = 8`: the one-sided formula of the finite projection, for an actual
-- agreeing NP language, gives a zero-error decider with unknown fraction at most `1 / 8`.
example : ∃ D : ZeroErrorFormula (2 ^ 8),
    MCSP.IsZeroErrorDecider (fun _ => 1) 8 8 D.eval := by
  obtain ⟨L, -, hag⟩ := SuccinctMCSP.exists_language_mem_NP
  obtain ⟨F, -, hyes, hcard⟩ := exists_formula_zero_error_average_case_of_agrees
    (s := fun _ => 1) (n := 8) (r := 8) hag (by decide)
  exact ⟨ZeroErrorFormula.ofMask F, isZeroErrorDecider_ofMask hyes hcard (by decide) (by decide)⟩

-- The forward form at the rounded threshold and the Definition 43 unknown fraction.
example {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    (hL : L ∈ FormulaPoly) :
    ∃ D : ∀ n, ZeroErrorFormula (2 ^ n), (∀ᶠ n in atTop, (D n).leafSize ≤ 2 ^ (n / 2)) ∧
      MCSP.SolvesOnAverage MCSP.sqrtThreshold (fun n => n) fun n => (D n).eval :=
  exists_zeroErrorFormula_solvesOnAverage_of_mem_FormulaPoly
    MCSP.subexponentiallyBounded_sqrtThreshold
    (Eventually.of_forall fun _ => Nat.lt_two_pow_self.le) hag hL

-- Theorem 5 with Definition 43.
example (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage MCSP.sqrtThreshold (fun n => n) fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly :=
  exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard hhard

-- Theorem 5 with the half-unknown devices of Section 1.2.
example (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage MCSP.sqrtThreshold (fun _ => 2) fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly :=
  exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_half_average_case_hard hhard

-- The general form with the other rounding `2 ^ ⌊√n⌋` of the threshold.
example (hhard : ¬ ∃ D : ∀ n, ZeroErrorFormula (2 ^ n),
      (fun n => ((D n).leafSize : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n) ∧
        MCSP.SolvesOnAverage (fun n => 2 ^ Nat.sqrt n) (fun n => n) fun n => (D n).eval) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly :=
  exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard
    (MCSP.subexponentiallyBounded_sqrtThreshold.mono_of_le
      MCSP.two_pow_sqrt_le_sqrtThreshold)
    (Eventually.of_forall fun _ => Nat.lt_two_pow_self.le) hhard

end CslibFrontierTests.FormulaMagnificationSublinearAverageCase
