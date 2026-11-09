/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Protocols.VOLE.RingMulCheck
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for IT-MACs and the masked multiplication check over `ZMod n`

The bounds of `RingMAC.lean` and `RingMulCheck.lean` are instantiated at the Damgård–Jurik
modulus `n = (3 * 5) ^ 2 = 225`, whose smallest prime factor is `3`. The binding bound `75` and the
quadratic bound `150` are attained, so the premises are satisfiable and the bounds are not
vacuous. Small cases over `ZMod 15` are checked by evaluation, and the masked multiplication check
is run on concrete values.
-/

namespace ComplexityTests.Crypto.VOLERing

open Cslib Cslib.Probability Cslib.Crypto.Protocols.VOLE
open scoped ENNReal

/-- The smallest prime factor of the Damgård–Jurik modulus `(3 * 5) ^ 2 = 225` is `3`. -/
theorem minFac_225 : Nat.minFac 225 = 3 :=
  Nat.minFac_mul_pow (p := 3) (q := 5) (ζ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-! ### Root counts by evaluation over `ZMod 15` -/

-- `5 * Δ = 0` has the `5 = 15 / 3` roots `0, 3, 6, 9, 12`.
example : (Finset.univ.filter fun delta : ZMod 15 => 5 * delta = 0).card = 5 := by decide

-- `5 * χ ^ 2 - 5 * χ = 0` has `10 = 2 * (15 / 3)` roots.
example : (Finset.univ.filter fun χ : ZMod 15 => 5 * χ ^ 2 + -5 * χ + 0 = 0).card = 10 := by
  decide

/-! ### IT-MAC binding at `n = 225` -/

/-- A forged opening `x' = 1 ≠ 0 = x` passes for at most `75` keys. -/
example (m m' : ZMod 225) :
    (Finset.univ.filter fun delta : ZMod 225 => 0 * delta + m = 1 * delta + m').card ≤ 75 := by
  simpa [minFac_225] using card_filter_mac_eq_le (n := 225) (x := 0) (x' := 1) m m' (by decide)

/-- The bound `75` is attained by the value gap `ringMacGap 225 = 75`. -/
example : ringMacGap 225 = 75 := by
  simp [ringMacGap, minFac_225]

example : ringMacGap 225 ≠ 0 :=
  ringMacGap_ne_zero (by norm_num)

example (x m : ZMod 225) :
    (Finset.univ.filter fun delta : ZMod 225 =>
      x * delta + m = (x + ringMacGap 225) * delta + m).card = 75 := by
  simpa [minFac_225] using card_filter_mac_ringMacGap x m

/-- A forged vector opening passes under a uniform key with probability at most `1 / 3`. -/
example (v v' : Fin 2 → ZMod 225) :
    (PMF.uniformOfFintype (ZMod 225)).toOuterMeasure
      {delta : ZMod 225 | ∀ i, ![1, 2] i * delta + v i = ![1, 3] i * delta + v' i} ≤
      1 / 3 := by
  have h := toOuterMeasure_voleVerifyOpening_le_minFac (n := 225) (x := ![1, 2])
    (x' := ![1, 3]) (v := v) (v' := v') (by decide)
  rw [minFac_225] at h
  exact_mod_cast h

/-- The paper's form of Lemma 3 at `(p, q, ζ) = (3, 5, 2)`. -/
example (v v' : Fin 1 → ZMod ((3 * 5) ^ 2)) :
    (PMF.uniformOfFintype (ZMod ((3 * 5) ^ 2))).toOuterMeasure
      {delta | ∀ i, ![0] i * delta + v i = ![1] i * delta + v' i} ≤ 1 / (3 : ℝ≥0∞) := by
  have h := toOuterMeasure_voleVerifyOpening_le_inv_prime (p := 3) (q := 5) (ζ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (x := ![0]) (x' := ![1]) (v := v)
    (v' := v') (by decide)
  exact_mod_cast h

/-! ### Quadratic root bound at `n = 225` -/

/-- The paper's form of Lemma 4: at most `2 * 3 ^ 1 * 5 ^ 2 = 150` roots. -/
example (b c : ZMod ((3 * 5) ^ 2)) :
    (Finset.univ.filter fun χ : ZMod ((3 * 5) ^ 2) => 7 * χ ^ 2 + b * χ + c = 0).card ≤
      2 * 3 ^ (2 - 1) * 5 ^ 2 :=
  card_filter_quadratic_eq_zero_le_mul_pow (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) b c (by decide)

example (b c : ZMod 225) :
    (Finset.univ.filter fun χ : ZMod 225 => 7 * χ ^ 2 + b * χ + c = 0).card ≤ 150 := by
  simpa [minFac_225] using card_filter_quadratic_eq_zero_le (n := 225) (a := 7) b c (by decide)

/-- The bound `150` is attained. -/
example :
    (Finset.univ.filter fun χ : ZMod 225 =>
      ringMacGap 225 * χ ^ 2 + -ringMacGap 225 * χ + 0 = 0).card = 150 := by
  simpa [minFac_225] using card_filter_quadratic_ringMacGap (n := 225) (by norm_num)

/-- Fibres of `ZMod 225 → ZMod 3` have `75` elements. -/
example (r : ZMod 3) :
    (Finset.univ.filter fun x : ZMod 225 =>
      ZMod.castHom (show 3 ∣ 225 by norm_num) (ZMod 3) x = r).card = 75 :=
  ZMod.card_filter_castHom_eq _ r

/-! ### The masked multiplication check -/

/-- The honest coefficients for `x = 2`, `y = 3`, `z = 6` with masks `1, 4, 5` and `r = 7`,
`m_r = 8` pass at the key `Δ = 9` over `ZMod 225`. -/
example :
    RingMulCheckAccepts (2 * 9 + 1) (3 * 9 + 4) (6 * 9 + 5) (7 * 9 + 8) (9 : ZMod 225)
      (ringMulCheckReply 2 1 3 4 5 7 8) := by
  decide

example (m_x m_y m_z r m_r delta : ZMod 225) :
    RingMulCheckAccepts (2 * delta + m_x) (3 * delta + m_y) (6 * delta + m_z) (r * delta + m_r)
      delta (ringMulCheckReply 2 m_x 3 m_y m_z r m_r) :=
  ringMulCheck_complete m_x m_y m_z r m_r delta (by decide)

/-- The honest view of the true product `2 * 3 = 6` has the simulator's distribution. -/
example (m_x m_y m_z delta : ZMod 225) :
    (PMF.uniformOfFintype (ZMod 225 × ZMod 225)).map (ringMulCheckView 2 m_x 3 m_y m_z delta) =
      (PMF.uniformOfFintype (ZMod 225 × ZMod 225)).map
        (ringMulCheckSimulate (2 * delta + m_x) (3 * delta + m_y) (6 * delta + m_z) delta) :=
  ringMulCheckView_eq_simulate m_x m_y m_z delta (by decide)

/-- The false product `2 * 3 ≠ 7` passes under a uniform key with probability at most `2 / 3`. -/
example (m_x m_y m_z r m_r : ZMod 225) (reply : ZMod 225 × ZMod 225) :
    (PMF.uniformOfFintype (ZMod 225)).toOuterMeasure
      {delta | RingMulCheckAccepts (2 * delta + m_x) (3 * delta + m_y) (7 * delta + m_z)
        (r * delta + m_r) delta reply} ≤ 2 / 3 := by
  have h := toOuterMeasure_ringMulCheck_le (n := 225) (x := 2) (y := 3) (z := 7) m_x m_y m_z r
    m_r reply (by decide)
  rw [minFac_225] at h
  exact_mod_cast h

-- Over `ZMod 15`, the false product `1 * 1 ≠ 0` with zero masks and coefficients `(0, 0)`
-- accepts exactly when `Δ ^ 2 = 0`, that is only at `Δ = 0`, within the bound `2 * (15 / 3)`.
example :
    (Finset.univ.filter fun delta : ZMod 15 =>
      RingMulCheckAccepts (1 * delta + 0) (1 * delta + 0) (0 * delta + 0) (0 * delta + 0) delta
        (0, 0)).card = 1 := by
  decide

example :
    (Finset.univ.filter fun delta : ZMod 15 =>
      RingMulCheckAccepts (1 * delta + 0) (1 * delta + 0) (0 * delta + 0) (0 * delta + 0) delta
        (0, 0)).card ≤ 2 * (15 / Nat.minFac 15) :=
  card_filter_ringMulCheck_le 0 0 0 0 0 (0, 0) (by decide)

/-- A randomized prover that draws its value `x` uniformly and claims `x * 1 = 0` passes with
probability at most `2 / 3` over `ZMod 15`. -/
example :
    (do
      let s ← PMF.uniformOfFintype (ZMod 15)
      let delta ← PMF.uniformOfFintype (ZMod 15)
      return (s, delta)).toOuterMeasure
      {sd : ZMod 15 × ZMod 15 | sd.1 * 1 ≠ 0 ∧
        RingMulCheckAccepts (sd.1 * sd.2 + 0) (1 * sd.2 + 0) (0 * sd.2 + 0) (0 * sd.2 + 0) sd.2
          (0, 0)} ≤ 2 / 3 := by
  have h := toOuterMeasure_ringMulCheck_bind_le (n := 15) (PMF.uniformOfFintype (ZMod 15))
    id (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => (0, 0))
  rw [show Nat.minFac 15 = 3 by norm_num] at h
  exact_mod_cast h

end ComplexityTests.Crypto.VOLERing
