/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.DyadicCost
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Intermediates

/-!
# Sharper ordinary 3SUM runtime transfer

Quantitative composition of the actual native reduction with a concrete certified callee.
The callee is an actual code object with semantic correctness. An endpoint instantiates its
explicit quantitative premise with the native automatic ET runtime theorem.
No additional solver execution or layout is supplied to the native program.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ThreeSum (HasSolution)
open Cslib.Algorithms.ThreeSum.ChanHe
open Filter

/-- Uniform polynomial-weight ET bounds survive the actual packed side and magnitude. -/
theorem exists_packed_calleeTime_one9992_bound {r : ℕ} (c : Host.Callee r)
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (c.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 33 / 20000 : ℝ)) (κ E : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      let t := Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1
      (c.time t (2 * (n + 2) ^ E + 1) : ℝ) ≤
        C * (t : ℝ) ^ (3 - 33 / 20000 : ℝ) := by
  obtain ⟨C, hC, N, htime⟩ := hc (2 * E + 2) (by omega)
  refine ⟨C, hC, N ^ 2, ?_⟩
  intro n hn
  exact htime _ (le_packed_side_of_sq_le hn _) _ (packed_weight_le κ E n)

/-- Actual native preprocessing fits below the tuned target after fixed logarithmic absorption. -/
theorem preprocessing_eventually_le_one9992 (κ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (ChanHe.Preprocessing.cost κ n : ℝ) ≤ (n : ℝ) ^ (2499 / 1250 : ℝ) := by
  let ε : ℝ := 1 / 65536
  let K := 6 * ChanHe.Preprocessing.costCoefficient κ + 1
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (by decide : 1 < (2 : ℕ))
    2 1 13 (K := (K : ℝ)) (by dsimp only [K]; positivity) (show 0 < ε by norm_num [ε])
  filter_upwards [hlog, packed_side_eventually_le_rpow κ (show 0 < ε by norm_num [ε]),
    eventually_ge_atTop (2 : ℕ)] with n hlog ht hn
  let t := Host.sideLength (instanceLength κ n)
  change (t : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) at ht
  have ht1 : 1 ≤ t := by dsimp only [t, Host.sideLength]; omega
  have hnt : n < t ^ 2 := input_lt_packed_side_sq n _
  have hsqrt : Nat.sqrt (n + 2) + 1 ≤ 3 * t := by
    have h : n + 2 < (t + 2) ^ 2 := by nlinarith
    have h' := Nat.sqrt_lt'.mpr h
    omega
  have hp := ChanHe.Preprocessing.cost_bound κ n
  have hp' : ChanHe.Preprocessing.cost κ n ≤
      K * n * t * (Nat.log 2 (n + 2) + 1) ^ 13 := by
    calc
      _ ≤ ChanHe.Preprocessing.costCoefficient κ * (2 * n) * (3 * t) *
          (Nat.log 2 (n + 2) + 1) ^ 13 := by
            apply hp.trans
            gcongr
            omega
      _ = (6 * ChanHe.Preprocessing.costCoefficient κ) * n * t *
          (Nat.log 2 (n + 2) + 1) ^ 13 := by ring
      _ ≤ K * n * t * (Nat.log 2 (n + 2) + 1) ^ 13 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (show 6 * ChanHe.Preprocessing.costCoefficient κ ≤ K from Nat.le_succ _)))
  have hpR := (Nat.cast_le (α := ℝ)).mpr hp'
  have hm := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (n : ℝ) * t by positivity)
  have hp'' : (ChanHe.Preprocessing.cost κ n : ℝ) ≤
      (n : ℝ) * (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) ^ ε := by
    push_cast at hpR hm
    have hsmall : (ChanHe.Preprocessing.cost κ n : ℝ) ≤
        (n : ℝ) * t * (n : ℝ) ^ ε := by nlinarith only [hpR, hm]
    exact hsmall.trans (by gcongr)
  calc
    _ ≤ (n : ℝ) * (n : ℝ) ^ (1 / 2 + ε : ℝ) * (n : ℝ) ^ ε := hp''
    _ = (n : ℝ) ^ (3 / 2 + 2 * ε : ℝ) := by
      calc
        _ = (n : ℝ) ^ (1 + (1 / 2 + ε) + ε : ℝ) := by
          rw [Real.rpow_add (by positivity) (1 + (1 / 2 + ε) : ℝ) ε,
            Real.rpow_add (by positivity) (1 : ℝ) (1 / 2 + ε : ℝ), Real.rpow_one]
        _ = _ := by congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
      (by norm_num [ε])

/-- The complete charged ordinary-host budget with a concrete callee is at most
`Oκ(n^1.9992)` when its polynomial-weight time exponent is `3-33/20000`. The single coefficient
and threshold depend only on the original fixed weight exponent, not on input data, layout,
physical width or selected primes. -/
theorem exists_cost_one9992_bound {r : ℕ} (c : Host.Callee r)
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (c.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 33 / 20000 : ℝ)) (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (cost κ c n : ℝ) ≤
        C * (n : ℝ) ^ (2499 / 1250 : ℝ) := by
  -- The resulting gain is 6500033/8000000000, strictly larger than 1/1250.
  let ε : ℝ := 1 / 400000
  let E := envelopeExponent κ
  obtain ⟨C, hC, N, htime⟩ := exists_packed_calleeTime_one9992_bound c hc κ E
  have hevent : ∀ᶠ n : ℕ in atTop,
      (cost κ c n : ℝ) ≤
        (2 * C + 4 * E + 388) * (n : ℝ) ^ (2499 / 1250 : ℝ) := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2 : ℕ),
      instanceBound_eventually_le_rpow κ (show 0 < ε by norm_num [ε]),
      packed_side_eventually_le_rpow κ (show 0 < ε by norm_num [ε]),
      preprocessing_eventually_le_one9992 κ] with n hnN hn hq ht hpp
    let t := Host.sideLength (instanceLength κ n)
    let T := c.time t (2 * (n + 2) ^ E + 1)
    have ht1 : (1 : ℝ) ≤ t := by
      have h : 1 ≤ t := by dsimp only [t, Host.sideLength]; omega
      exact_mod_cast h
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have ht0 : (0 : ℝ) < t := by linarith
    change (t : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) at ht
    have hb : (T : ℝ) ≤ C * (t : ℝ) ^ (3 - 33 / 20000 : ℝ) := htime n hnN
    have hpow : (t : ℝ) ^ (4 - 33 / 20000 : ℝ) =
        (t : ℝ) * (t : ℝ) ^ (3 - 33 / 20000 : ℝ) := by
      have h : (4 - 33 / 20000 : ℝ) = 1 + (3 - 33 / 20000) := by ring
      rw [h, Real.rpow_add ht0, Real.rpow_one]
    have hT : 2 * (t : ℝ) * T ≤ 2 * C * (t : ℝ) ^ (4 - 33 / 20000 : ℝ) := by
      calc
        _ ≤ 2 * (t : ℝ) * (C * (t : ℝ) ^ (3 - 33 / 20000 : ℝ)) := by gcongr
        _ = _ := by rw [hpow]; ring
    have hcube : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ (4 - 33 / 20000 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    have hc : ((Host.callerTime (instanceLength κ n) T + 12 : ℕ) : ℝ) ≤
        2 * (t : ℝ) * T + 355 * (t : ℝ) ^ 3 := by
      exact_mod_cast callerTime_add_twelve_le (instanceLength κ n) T
    have hcall : (Host.callerTime (instanceLength κ n) T + 12 : ℕ) ≤
        (2 * C + 355) * (t : ℝ) ^ (4 - 33 / 20000 : ℝ) := by
      nlinarith only [hc, hT, hcube]
    have hscale : (n : ℝ) ^ ε * (t : ℝ) ^ (4 - 33 / 20000 : ℝ) ≤
        (n : ℝ) ^ (2499 / 1250 : ℝ) := by
      calc
        _ ≤ (n : ℝ) ^ ε * ((n : ℝ) ^ (1 / 2 + ε : ℝ)) ^ (4 - 33 / 20000 : ℝ) := by
          gcongr
        _ = (n : ℝ) ^ (ε + (1 / 2 + ε) * (4 - 33 / 20000) : ℝ) := by
          rw [← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num [ε])
    have hprod : (instanceBound κ n : ℝ) * (Host.callerTime (instanceLength κ n) T + 12 : ℕ) ≤
        (2 * C + 355) * (n : ℝ) ^ (2499 / 1250 : ℝ) := by
      calc
        _ ≤ (n : ℝ) ^ ε * ((2 * C + 355) * (t : ℝ) ^ (4 - 33 / 20000 : ℝ)) := by gcongr
        _ = (2 * C + 355) * ((n : ℝ) ^ ε * (t : ℝ) ^ (4 - 33 / 20000 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ (2499 / 1250 : ℝ) := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn1 (show (0 : ℝ) ≤ 2499 / 1250 by norm_num))
    have hconst := mul_le_mul_of_nonneg_left hone (show (0 : ℝ) ≤ 4 * E + 32 by positivity)
    unfold cost
    change ((ChanHe.Preprocessing.cost κ n + 4 * E + 32 +
      instanceBound κ n * (Host.callerTime (instanceLength κ n) T + 12) : ℕ) : ℝ) ≤ _
    push_cast at hprod ⊢
    nlinarith only [hpp, hprod, hconst]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  exact ⟨2 * C + 4 * E + 388, by positivity, M, hM⟩


/-- The fixed native program is correct at every admitted input length; its strict-subquadratic
step bound is uniform beyond one threshold per original magnitude exponent. Both actual runs
use the same initialized state and pre-halt witness, with the halt included in steps. -/
theorem exists_one9992_runs_of_callee_time {r : ℕ} (c : Host.Callee r)
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (c.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 33 / 20000 : ℝ)) (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ¬(program κ c).ReadsWidth ∧ ∀ (input : List ℤ) (W : ℕ),
      width κ c.widthCoefficient input.length ≤ W →
      (∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) →
      InputFits W (input.map Signed.encode) ∧ ∃ (y : Data (registerCount r)) (steps : ℕ),
        Executes W (flatProgram κ c)
          (State.init (input.map Signed.encode))
          (y.regs (controllerRegisters r answer)) steps ∧
        Runs W (flatProgram κ c)
          (State.init (input.map Signed.encode)) ⟨(program κ c).size, y⟩
          (steps - 1) ∧
        steps ≤ cost κ c input.length ∧
        (N ≤ input.length → (steps : ℝ) ≤ C * (input.length : ℝ) ^ (2499 / 1250 : ℝ)) ∧
        y.regs (controllerRegisters r answer) ≤ 1 ∧
        (y.regs (controllerRegisters r answer) = 1 ↔
          HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded W ∧
        ∀ (s : State (registerCount r)) (t : ℕ),
          Runs W (flatProgram κ c)
            (State.init (input.map Signed.encode)) s t →
          (∀ i, s.data.regs i < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
          (∀ a, s.data.mem a < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
          (∀ a, (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient) ≤ a →
            s.data.mem a = 0) := by
  obtain ⟨C, hC, N, hc⟩ := exists_cost_one9992_bound c hc κ
  refine ⟨C, hC, N, not_readsWidth κ c, ?_⟩
  intro input W hW hv
  have hi := ChanHe.Preprocessing.input_fits input
    ((preprocessing_width_le κ c.widthCoefficient input.length).trans hW) hv
  obtain ⟨y, steps, he, hr, ht, hb, hiff, hbounded⟩ :=
    runs_input input c hW hv
  refine ⟨hi, y, steps, he, hr, ht,
    fun hn => ((Nat.cast_le (α := ℝ)).mpr ht).trans (hc input.length hn), hb, hiff, hbounded, ?_⟩
  intro s t hs
  obtain ⟨hregs, hmem⟩ := intermediates_polynomial input c hW hv hs
  refine ⟨?_, ?_, ?_⟩
  · exact hregs
  · exact hmem
  · intro a ha
    apply space_polynomial input c hW hv hs
    exact ha

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
