/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.BitString.LazyRandomWalk
import CslibFrontier.Probability.MarkovChain.Metropolis
import CslibFrontier.Probability.StatisticalDistance.ClosedForm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite Markov chains: checked instances

* A deterministic flip on `Bool`: the uniform distribution is reversible, `d(t) = 1/2` for every
  `t`, so `t_mix(ε) = ⊤` for `ε < 1/2` and `t_mix(1/2) = 0`. The `ℕ∞`-valued mixing time does not
  hide a periodicity hypothesis.
* The two-state chain of [LevinPeres2017], Example 1.1, with `p = 1/2` and `q = 1/4`:
  the non-uniform law `π = (1/3, 2/3)` is reversible, `d(t) = (2/3)(1/4)^t` exactly, and
  `t_mix(1/4) = 1`.
* The Metropolis chain for the flip proposal and the target `(1/3, 2/3)` is stationary and accepts
  the move `true ↦ false` with probability `1/2`.
* The independent coupling is a Markovian coupling.
* The lazy hypercube walk with `n = 1`: `t_mix(2/5) = 1`, matching the ceilinged bound
  `⌈n log n + n log ε⁻¹⌉ = 1`, while the right-hand side `n log n + n log ε⁻¹ = log (5/2) < 1`
  of [LevinPeres2017], (5.6), as printed without a ceiling, is too small.
-/

namespace CslibFrontierTests.MarkovChain

open Cslib.Probability Cslib.Probability.PMF Cslib.Probability.MarkovChain Cslib.BitString
open scoped Cslib.Probability.PMF

/-! ### Deterministic flip: reversible but never mixing -/

/-- The deterministic flip `b ↦ !b`. -/
noncomputable def flip : MarkovChain Bool := ⟨fun b => PMF.pure (!b)⟩

theorem flip_pow_apply (t : ℕ) (b : Bool) :
    (flip ^ t) b = PMF.pure (if Even t then b else !b) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ_apply, ih, PMF.pure_bind]
    change PMF.pure (!_) = _
    by_cases ht : Even t <;> simp [ht, Nat.even_add_one]

theorem flip_isReversible : flip.IsReversible (PMF.uniformOfFintype Bool) := by
  intro x y
  simp only [PMF.uniformOfFintype_apply]
  congr 1
  change PMF.pure (!x) y = PMF.pure (!y) x
  cases x <;> cases y <;> simp

theorem flip_distToStationary (t : ℕ) :
    flip.distToStationary (PMF.uniformOfFintype Bool) t = 1 / 2 := by
  have hpt (b : Bool) : dist ((flip ^ t) b) (PMF.uniformOfFintype Bool) = 1 / 2 := by
    rw [flip_pow_apply, dist_pure_left]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_ofNat]
    norm_num
  refine le_antisymm (distToStationary_le _ _ (fun b => (hpt b).le) (by norm_num)) ?_
  exact (hpt true).symm.le.trans (dist_le_distToStationary _ _ t true)

theorem flip_mixingTime_eq_top {ε : ℝ} (hε : ε < 1 / 2) :
    flip.mixingTime (PMF.uniformOfFintype Bool) ε = ⊤ :=
  (mixingTime_eq_top_iff ε).mpr fun t => by rw [flip_distToStationary]; exact hε

theorem flip_mixingTime_half : flip.mixingTime (PMF.uniformOfFintype Bool) (1 / 2) = 0 := by
  refine nonpos_iff_eq_zero.mp ?_
  exact_mod_cast mixingTime_le_of_distToStationary_le (flip_distToStationary 0).le

/-! ### A two-state chain with a non-uniform stationary law -/

/-- The coin with `Pr[true] = p`. -/
noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then p else 1 - p)) (by
    rw [Fintype.sum_bool, ite_eq_left rfl, ite_eq_right Bool.false_ne_true,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp)

theorem coin_apply_toReal (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (coin p h0 h1 b).toReal = if b then p else 1 - p := by
  rw [coin, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  split_ifs <;> linarith

/-- The two-state chain of [LevinPeres2017], Example 1.1, with `false ↦ true` probability
`p = 1/2` and `true ↦ false` probability `q = 1/4`. -/
noncomputable def twoState : MarkovChain Bool :=
  ⟨fun b => if b then coin (3 / 4) (by norm_num) (by norm_num)
    else coin (1 / 2) (by norm_num) (by norm_num)⟩

/-- Its stationary law `π = (q/(p+q), p/(p+q)) = (1/3, 2/3)`. -/
noncomputable def twoStateπ : PMF Bool := coin (2 / 3) (by norm_num) (by norm_num)

theorem twoState_true_true : (twoState true true).toReal = 3 / 4 := by
  simp [twoState, coin_apply_toReal]

theorem twoState_false_true : (twoState false true).toReal = 1 / 2 := by
  simp [twoState, coin_apply_toReal]

theorem twoState_isReversible : twoState.IsReversible twoStateπ := by
  intro x y
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)) (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  cases x <;> cases y <;> simp [twoState, twoStateπ, coin_apply_toReal] <;> norm_num

theorem twoState_isStationary : twoState.IsStationary twoStateπ :=
  twoState_isReversible.isStationary

theorem twoState_pow_true (t : ℕ) (x : Bool) :
    ((twoState ^ t) x true).toReal - 2 / 3 = (1 / 4) ^ t * (if x then 1 / 3 else -(2 / 3)) := by
  induction t with
  | zero => cases x <;> norm_num
  | succ t ih =>
    have hs := sum_toReal ((twoState ^ t) x)
    rw [Fintype.sum_bool] at hs
    rw [pow_succ_apply, bind_apply_toReal, Fintype.sum_bool, twoState_true_true,
      twoState_false_true, pow_succ]
    linear_combination (1 / 4 : ℝ) * ih + (1 / 2 : ℝ) * hs

/-- Exact `d(t) = (2/3)(1/4)^t` for the two-state chain. -/
theorem twoState_distToStationary (t : ℕ) :
    twoState.distToStationary twoStateπ t = 2 / 3 * (1 / 4) ^ t := by
  have hπ : (twoStateπ true).toReal = 2 / 3 := by
    simp only [twoStateπ, coin_apply_toReal, ↓reduceIte]
  have hpt (x : Bool) : dist ((twoState ^ t) x) twoStateπ =
      (1 / 4) ^ t * (if x then 1 / 3 else 2 / 3) := by
    rw [dist_bool, hπ, twoState_pow_true]
    cases x <;> norm_num [abs_mul]
  have h4 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) t
  refine le_antisymm (distToStationary_le _ _ (fun x => ?_) (by positivity)) ?_
  · rw [hpt]
    cases x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      linarith
    · simp only [↓reduceIte]
      linarith
  · refine le_of_eq_of_le ?_ (dist_le_distToStationary _ _ t false)
    rw [hpt]
    simp [mul_comm]

theorem twoState_mixingTime_quarter : twoState.mixingTime twoStateπ (1 / 4) = 1 := by
  refine le_antisymm ?_ ?_
  · exact_mod_cast mixingTime_le_of_distToStationary_le
      (by rw [twoState_distToStationary]; norm_num)
  · refine Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h => ?_)
    have := (twoState_isStationary.mixingTime_le_iff (1 / 4) 0).mp (by rw [h]; rfl)
    rw [twoState_distToStationary] at this
    norm_num at this

/-! ### A Metropolis chain with a non-uniform target -/

/-- The Metropolis chain for the flip proposal and the target `π = (1/3, 2/3)` is stationary. -/
example : (metropolis flip twoStateπ).IsStationary twoStateπ := isStationary_metropolis _ _

/-- It accepts the move `true ↦ false` with probability `π(false)/π(true) = 1/2`. -/
theorem metropolis_flip_true_false : (metropolis flip twoStateπ true false).toReal = 1 / 2 := by
  have h1 : flip true false = 1 := PMF.pure_apply_self _
  have h2 : flip false true = 1 := PMF.pure_apply_self _
  have ht : twoStateπ true = ENNReal.ofReal (2 / 3) := rfl
  have hf : twoStateπ false = ENNReal.ofReal (1 - 2 / 3) := rfl
  have hr : ENNReal.ofReal (1 - 2 / 3) * 1 / (ENNReal.ofReal (2 / 3) * 1) =
      ENNReal.ofReal (1 / 2) := by
    rw [mul_one, mul_one, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [metropolis_apply_of_ne _ _ (by decide : true ≠ false), metropolisRatio, ht, hf, h1, h2, hr,
    one_mul, min_eq_left (ENNReal.ofReal_le_one.mpr (by norm_num)),
    ENNReal.toReal_ofReal (by norm_num)]

/-! ### Nonvacuity of Markovian couplings -/

example : twoState.IsMarkovianCoupling twoState.independentCoupling :=
  isMarkovianCoupling_independentCoupling _

example : (lazyRandomWalk (Fin 3)).IsMarkovianCoupling (lazyRandomWalkCoupling (Fin 3)) :=
  isMarkovianCoupling_lazyRandomWalkCoupling

/-! ### The hypercube for `n = 1`: the ceiling in (5.6) is needed -/

theorem log_five_halves_lt_one : Real.log (5 / 2) < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  linarith [Real.exp_one_gt_d9]

/-- For `n = 1` and `ε = 2/5`, the mixing time is exactly `1`, which the ceilinged bound
`⌈n log n + n log ε⁻¹⌉ = ⌈log (5/2)⌉ = 1` attains. -/
theorem lazyRandomWalk_unit_mixingTime :
    (lazyRandomWalk Unit).mixingTime (PMF.uniformOfFintype _) (2 / 5) = 1 := by
  refine le_antisymm ?_ ?_
  · refine (mixingTime_lazyRandomWalk_le (by norm_num)).trans ?_
    have hb : (Fintype.card Unit : ℝ) * Real.log (Fintype.card Unit) +
        Fintype.card Unit * Real.log (2 / 5)⁻¹ ≤ 1 := by
      norm_num
      exact log_five_halves_lt_one.le
    exact_mod_cast Nat.ceil_le.mpr (by exact_mod_cast hb)
  · refine Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h => ?_)
    have h0 := (isStationary_lazyRandomWalk.mixingTime_le_iff (2 / 5) 0).mp (by rw [h]; rfl)
    have hx := (dist_le_distToStationary _ _ 0 (fun _ => true)).trans h0
    rw [pow_zero, one_apply, dist_pure_left, PMF.uniformOfFintype_apply] at hx
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_unit, pow_one, Nat.cast_ofNat,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hx
    norm_num at hx

/-- The right-hand side `n log n + n log ε⁻¹` of [LevinPeres2017], (5.6), without a ceiling,
is below the true mixing time `1` for `n = 1` and `ε = 2/5`. -/
example : (Fintype.card Unit : ℝ) * Real.log (Fintype.card Unit) +
    Fintype.card Unit * Real.log (2 / 5)⁻¹ < 1 := by
  norm_num
  exact log_five_halves_lt_one

end CslibFrontierTests.MarkovChain
