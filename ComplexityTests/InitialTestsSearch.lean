/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.BitString.InitialTestsSearch

/-! Tests for deterministic sequential initial-test search and shortened Tanner check matrices. -/

namespace ComplexityTests.InitialTestsSearch
open Cslib Cslib.BitString Cslib.Complexity.InitialTestsSearch Cslib.Probability.PMF
open Turing.MultiTapeTM
-- Base ell = 0 (qG = 1) schedule values, trivial shift search, degenerate empty cases,
-- and end-to-end check of initialTestsRows_spec and map_ofList_initialTestsRows_spec at (4, 6, 2).
example :
    (greedyRowListLength 1 1 = 20000 ∧ initialRowWeightBound 1 1 = 320000 ∧ ellG 1 1 = 0 ∧
      qG 1 1 = 1 ∧ dG 1 1 = 1 ∧
      checkSmallBiasShifts 0 3 0 1 [[], [], []] = true ∧
      checkSmallBiasShifts 0 3 0 1 [[true], [], []] = false ∧
      findSmallBiasShifts 0 3 0 1 = [[], [], []] ∧
      initialTestsRows 0 1 = [] ∧ initialTestsRows 3 0 = []) ∧
    (initialTestsRows 6 2).length ≤ 12 ∧
    (∀ r ∈ (initialTestsRows 6 2).map (ofList 6), weight r ≤ initialRowWeightBound 2 6) ∧
    ∀ z : Fin 6 → Bool, z ≠ 0 → (∀ r ∈ initialTestsRows 6 2, ofList 6 r ⬝ᵥ z = false) →
      (6 : ℝ) / (greedyRowListLength 2 6 : ℝ) ≤ (weight z : ℝ) :=
  ⟨by decide,
    (initialTestsRows_spec (n := 4) (m := 6) (B := 2) (by decide) (by decide) (by decide)).1,
    (map_ofList_initialTestsRows_spec (n := 4) (by decide) (by decide) (by decide)).2.1,
    fun _ hz0 hz => div_greedyRowListLength_le_weight_of_initialTestsRows (n := 4) (by decide)
      (by decide) (by decide) hz0 hz⟩

set_option maxRecDepth 4096 in
-- Kernel reduction of 2 ^ (3 * 2) = 64 sequential IndexFold.run steps + IsSmallBias soundness.
example :
    let shifts := findSmallBiasShifts 2 3 1 3
    checkSmallBiasShifts 2 3 1 3 shifts = true ∧
      checkSmallBiasShifts 2 3 0 3 [[false, false], [true, false], [false, true]] = false ∧
      shifts.length = 3 ∧ (∀ row ∈ shifts, row.length = 2) ∧
      IsSmallBias ((1 : ℝ) / 3)
        ((uniformOfFintype (Fin 3)).map fun j => ofList 2 (shifts.getD j.val [])) := by
  have hw := ((checkSmallBiasShifts_eq_true_iff (ell := 2) (d := 3) (maxBiasNum := 1)
    (by decide : 0 < 3) [[false, false], [true, false], [false, true]]).1 (by decide)).2.2
  have hs := isSmallBias_findSmallBiasShifts (ell := 2) (d := 3) (maxBiasNum := 1)
    (maxBiasDen := 3) (by decide) ⟨_, by simpa only [Nat.cast_one, Nat.cast_ofNat] using hw⟩
  exact ⟨by decide, by decide, by simpa only [Nat.cast_one, Nat.cast_ofNat] using hs.2⟩

set_option maxRecDepth 4096 in
-- Kernel reduction of 2 ^ (2 * 3) = 64 sequential IndexFold.run steps + distance soundness.
example :
    let H0 := findLocalCheckMatrix 2 3 3
    checkLocalCodeDistance 2 3 3 H0 = true ∧
      checkLocalCodeDistance 2 3 4 [[true, true, false], [false, true, true]] = false ∧
      findLocalCheckMatrix 2 3 4 = [[false, false, false], [false, false, false]] ∧
      H0.length = 2 ∧ (∀ row ∈ H0, row.length = 3) ∧ ∀ w : Fin 3 → Bool, w ≠ 0 →
        (∀ i : Fin 2, ofList 3 (H0.getD i.val []) ⬝ᵥ w = false) → 3 ≤ weight w := by
  have hw := ((checkLocalCodeDistance_eq_true_iff 2 3 3
    [[true, true, false], [false, true, true]]).1 (by decide)).2.2
  exact ⟨by decide, by decide, by decide, (weight_le_of_findLocalCheckMatrix ⟨_, hw⟩).2⟩

set_option maxRecDepth 4096 in
-- Kernel reduction of 64-step findLocalCheckMatrix inside shortened Tanner assembly.
example :
    let rows := buildShortenedTannerRows 5 1 3 2
      (findSmallBiasShifts 1 3 1 3) (findLocalCheckMatrix 2 3 3)
    rows.length = 8 ∧ (∀ r ∈ rows, r.length = 5 ∧ r.count true ≤ 3) ∧
      (rows.any fun r => ofList 5 r ⬝ᵥ ofList 5 [true, false, false, false, false]) = true ∧
      ∀ z : Fin 5 → Bool, z ≠ 0 → (∀ r ∈ rows, ofList 5 r ⬝ᵥ z = false) →
        (12 : ℝ) ≤ 3 * (weight z : ℝ) := by
  refine ⟨by decide, by decide, by decide, fun z hz0 hz => ?_⟩
  have h := le_weight_of_buildShortenedTannerRows (m := 5) (ell := 1) (d := 3) (c := 2)
    (maxBiasNum := 1) (maxBiasDen := 3) (h := 2) (by decide) (by decide) (by decide) (by decide)
    hz0 hz
  norm_num at h; exact h
private abbrev TestIn := (ℕ × ℕ) × (List (List Bool) × List (List Bool))
-- Compositional fun_prop across schedule defs, checkSmallBiasShifts, Tanner rows, and enc guard.
example :
    let encIn : TestIn ↪ List Bool :=
      encPair (encPair encUnary encUnary) (encPair (encList encBits) (encList encBits))
    ComputableInPolyTime (fun x : TestIn =>
      (greedyRowListLength x.1.2 x.1.1 + initialRowWeightBound x.1.2 x.1.1 + qG x.1.1 x.1.2,
        (checkSmallBiasShifts (ellG x.1.1 x.1.2) (dG x.1.1 x.1.2) 1 (biasDen x.1.1 x.1.2) x.2.1,
          buildShortenedTannerRows x.1.1 (ellG x.1.1 x.1.2) (dG x.1.1 x.1.2) (cG x.1.1 x.1.2)
            x.2.1 x.2.2))) encIn (encPair encUnary (encPair encBool (encList encBits))) := by
  intro encIn; dsimp only [encIn]
  fail_if_success exact (by fun_prop :
    ComputableInPolyTime (fun p : ℕ × ℕ => qG p.1 p.2) (encPair encNat encUnary) encUnary)
  refine ComputableInPolyTime.prod (by fun_prop) (ComputableInPolyTime.prod
    (checkSmallBiasShifts_polyTime_of_two_pow_le (m := fun x => x.1.1) (by fun_prop) (by fun_prop)
      (by fun_prop) (.const 1) (.of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp
        (biasDen_polyTime (by fun_prop) (by fun_prop)).tidy)) (by fun_prop)
      fun x => qG_le_two_mul_add_one x.1.1 x.1.2)
    (buildShortenedTannerRows_polyTime (bound := fun x => 2 * x.1.1 + 1) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      fun x => qG_le_two_mul_add_one x.1.1 x.1.2))

end ComplexityTests.InitialTestsSearch
