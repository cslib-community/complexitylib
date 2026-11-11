/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Cost
public import Complexity.Algorithms.ThreeSum.ChanHe.ConvolutionSizes
public import Complexity.Foundations.Data.Nat.LogRpow
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingTime

/-!
# Uniform runtime transfer for the canonical ordinary 3SUM visitor

The ordinary algorithm constructs and consumes a short ordered list of Convolution-3SUM nodes in
place during Chan–He traversal. Each actual packed node leads to Exact Triangle (ET) calls. No
packed-pointer catalogue is retained on this path. The saving comes from the ET calls' square-root
dimension, after charging all frontend, traversal, matrix and solver work.

Write `ℓ = log₂(n+2)+1`, `q = instanceBound κ n`, `s = Host.sideLength (instanceLength κ n)` and
`E = envelopeExponent κ`. The actual ET magnitude argument is `F = 2*(n+2)^E+1`. For fixed `κ`:

* `ChanHe.Preprocessing.cost_bound` bounds the reused preparation/traversal allowance by
  `Kκ*(n+2)*(sqrt(n+2)+1)*ℓ^13`.
* `instanceBound_le_numBound` bounds the emitted-node allowance `q` by `128*(κ+2)^2*ℓ^7`.
* `Cslib.Algorithms.ThreeSum.ChanHe.packed_side_le` gives `s = Oκ(sqrt(n)*ℓ²)`.
  Its companion `packed_weight_le` proves `F ≤ (s+2)^(2E+2)`, so the ET hypothesis applies
  to the actual dimension and magnitude, without padding the original input.
* `callerTime_add_twelve_le` bounds the existing per-call allowance, including outer control,
  by `2*s*c.time s F + 355*s³`.

The unchanged definition `cost` combines that preparation/traversal allowance, the fixed `4E+32`
setup/halt reserve and at most `q` per-call allowances. `Visitor.cost_ledger` separately shows
that it covers the in-place consumer's host charge plus seven instructions and the one-instruction
packed-tail release, giving eight extra instructions per emitted node. The identity retains fixed
slack eighteen and four units per emitted node in the reused allowance. Solver work is charged
only for emitted nodes; skipped descriptors pay traversal work. Tail reuse retains persistent
heavy-buffer allocation and the old table gap, without tightening the proved total-space or
arbitrary-callee high-water envelope. This numerical module uses the shared `Decision.Cost`
definitions without importing the ordinary execution proof.

An ET bound `T(s)=O(s^(3-δ))` contributes `O(q*s^(4-δ))`. Substituting the displayed bounds gives
`n^(2-δ/2)` times a fixed logarithmic factor. `exists_cost_bound` absorbs those logarithms only
after composition, proving every `a > 2-δ/2` for `0 < δ ≤ 1`; the boundary exponent with those
factors removed is not asserted.

All constants and thresholds precede original inputs and physical widths. The hypothesis concerns
the time field of an actual certified `Host.Callee`. No concrete ET supplier is imported here;
`Decision.Transfer` adds initialized correctness and prefix-resource guarantees.

## Main results

* `packed_side_eventually_le_rpow`: packed side below every power above square root.
* `instanceBound_eventually_le_rpow`: every positive power absorbs the emitted-node allowance.
* `exists_packed_calleeTime_bound`: polynomial magnitudes at the actual packed side.
* `preprocessing_eventually_le_rpow`: the reused allowance below every exponent above 3/2.
* `exists_cost_bound`: the shared native cost from a uniform quantitative callee bound.

This is original quantitative composition of the existing native reduction and charged ledger.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.Algorithms.ThreeSum.ChanHe

open Filter

/-- The exact packed side grows more slowly than every fixed power strictly above square
root. All coefficients and logarithmic factors are absorbed before the varying outer input. -/
theorem packed_side_eventually_le_rpow (κ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1 : ℕ) ≤
        (n : ℝ) ^ (1 / 2 + ε : ℝ) := by
  let A := (5 * κ + 16) * (10 * κ + 40)
  have he := Nat.eventually_mul_log_add_pow_le_rpow (by decide : 1 < (2 : ℕ))
    2 1 4 (K := (8 * (3 * A + 1) ^ 2 : ℕ)) (by positivity) (by positivity : 0 < 2 * ε)
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with n hlog hn
  let t := Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1
  have hns : n + 2 ≤ 2 * n := by omega
  have hs := packed_side_sq_le κ n
  have hs' : t ^ 2 ≤ 8 * (3 * A + 1) ^ 2 * n * (Nat.log 2 (n + 2) + 1) ^ 4 := by
    have hm := Nat.mul_le_mul_right ((Nat.log 2 (n + 2) + 1) ^ 4)
      (Nat.mul_le_mul_left (4 * (3 * A + 1) ^ 2) hns)
    change t ^ 2 ≤ 4 * (3 * A + 1) ^ 2 * (n + 2) * _ at hs
    exact hs.trans (hm.trans_eq (by ring))
  have hsR := (Nat.cast_le (α := ℝ)).mpr hs'
  have hmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ n by positivity)
  have hexp : (n : ℝ) * (n : ℝ) ^ (2 * ε) = (n : ℝ) ^ (1 + 2 * ε) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hsq : (t : ℝ) ^ 2 ≤ (n : ℝ) ^ (1 + 2 * ε) := by
    push_cast at hsR hmul
    rw [hexp] at hmul
    nlinarith only [hsR, hmul]
  have hroot : ((n : ℝ) ^ (1 / 2 + ε : ℝ)) ^ 2 =
      (n : ℝ) ^ (1 + 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) := Real.rpow_nonneg (by positivity) _
  change (t : ℝ) ≤ _
  nlinarith only [hsq, hroot, ht0, hr0]

/-- The actual native emitted-node allowance has the same degree-seven logarithmic estimate
as the finite instance count. The shared finite lemma avoids a duplicate counting proof. -/
theorem instanceBound_le_numBound (κ n : ℕ) : instanceBound κ n ≤ numBound κ (n + 2) :=
  shifted_count_bound_le n κ

/-- Every fixed positive real power eventually absorbs the actual emitted-node allowance. -/
theorem instanceBound_eventually_le_rpow (κ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (instanceBound κ n : ℝ) ≤ (n : ℝ) ^ ε := by
  have h := Nat.eventually_mul_log_add_pow_le_rpow (by decide : 1 < (2 : ℕ))
    2 1 7 (K := (128 * (κ + 2) ^ 2 : ℕ)) (by positivity) hε
  filter_upwards [h] with n hn
  have hb := (Nat.cast_le (α := ℝ)).mpr (instanceBound_le_numBound κ n)
  unfold numBound at hb
  push_cast at hb hn
  exact hb.trans hn

/-- Actual Convolution caller work, with its outer control reserve, is a cubic side term
plus the true number of callee invocations. -/
theorem callerTime_add_twelve_le (N T : ℕ) :
    Host.callerTime N T + 12 ≤
      2 * Host.sideLength N * T + 355 * Host.sideLength N ^ 3 := by
  have ht : 1 ≤ Host.sideLength N := by dsimp only [Host.sideLength]; omega
  have hp : Host.sideLength N ≤ Host.sideLength N ^ 3 :=
    Nat.le_self_pow (by decide) _
  have hp1 : 1 ≤ Host.sideLength N ^ 3 := Nat.one_le_pow _ _ ht
  unfold Host.callerTime
  have hs : Nat.sqrt N ≤ Host.sideLength N := by dsimp only [Host.sideLength]; omega
  nlinarith only [hs, hp, hp1]

/-- Uniform polynomial-weight time bounds transfer to the actual packed side and magnitude. -/
theorem exists_packed_calleeTime_bound {r : ℕ} (c : Host.Callee r) {e : ℝ}
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ, (c.time n F : ℝ) ≤ C * (n : ℝ) ^ e) (κ E : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      let t := Nat.sqrt (8 * mPar n (2 * (n + 2) ^ κ) ^ 2) + 1
      (c.time t (2 * (n + 2) ^ E + 1) : ℝ) ≤ C * (t : ℝ) ^ e := by
  obtain ⟨C, hC, N, htime⟩ := hc (2 * E + 2) (by omega)
  exact ⟨C, hC, N ^ 2, fun n hn =>
    htime _ (le_packed_side_of_sq_le hn _) _ (packed_weight_le κ E n)⟩

/-- Charged native preprocessing is eventually below every fixed exponent above 3/2. -/
theorem preprocessing_eventually_le_rpow (κ : ℕ) {a : ℝ} (ha : 3 / 2 < a) :
    ∀ᶠ n : ℕ in atTop,
      (ChanHe.Preprocessing.cost κ n : ℝ) ≤ (n : ℝ) ^ a := by
  let ε : ℝ := (a - 3 / 2) / 4
  let K := 6 * ChanHe.Preprocessing.costCoefficient κ + 1
  have hlog := Nat.eventually_mul_log_add_pow_le_rpow (by decide : 1 < (2 : ℕ))
    2 1 13 (K := (K : ℝ)) (by dsimp only [K]; positivity) (show 0 < ε by dsimp only [ε]; linarith)
  filter_upwards [hlog, packed_side_eventually_le_rpow κ (show 0 < ε by dsimp only [ε]; linarith),
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
      (by dsimp only [ε]; linarith)


/-- A uniform ET saving δ gives the actual charged ordinary host every exponent above 2-δ/2. -/
theorem exists_cost_bound {r : ℕ} (c : Host.Callee r) {δ a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 2 - δ / 2 < a)
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (c.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - δ)) (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (cost κ c n : ℝ) ≤
        C * (n : ℝ) ^ a := by
  let ε : ℝ := (a - (2 - δ / 2)) / 10
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hgap : 10 * ε = a - (2 - δ / 2) := by dsimp only [ε]; ring
  have hscaleExp : ε + (1 / 2 + ε) * (4 - δ) ≤ a := by
    nlinarith [mul_nonneg hε.le hδ.le]
  have hpre : 3 / 2 < a := by linarith
  have hpower : 0 ≤ 4 - δ := by linarith
  let E := envelopeExponent κ
  obtain ⟨C, hC, N, htime⟩ := exists_packed_calleeTime_bound c hc κ E
  have hevent : ∀ᶠ n : ℕ in atTop,
      (cost κ c n : ℝ) ≤
        (2 * C + 4 * E + 388) * (n : ℝ) ^ a := by
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop (2 : ℕ),
      instanceBound_eventually_le_rpow κ hε,
      packed_side_eventually_le_rpow κ hε,
      preprocessing_eventually_le_rpow κ hpre] with n hnN hn hq ht hpp
    let t := Host.sideLength (instanceLength κ n)
    let T := c.time t (2 * (n + 2) ^ E + 1)
    have ht1 : (1 : ℝ) ≤ t := by
      have h : 1 ≤ t := by dsimp only [t, Host.sideLength]; omega
      exact_mod_cast h
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have ht0 : (0 : ℝ) < t := by linarith
    change (t : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε : ℝ) at ht
    have hb : (T : ℝ) ≤ C * (t : ℝ) ^ (3 - δ) := htime n hnN
    have hpow : (t : ℝ) ^ (4 - δ) =
        (t : ℝ) * (t : ℝ) ^ (3 - δ) := by
      have h : (4 - δ) = 1 + (3 - δ) := by ring
      rw [h, Real.rpow_add ht0, Real.rpow_one]
    have hT : 2 * (t : ℝ) * T ≤ 2 * C * (t : ℝ) ^ (4 - δ) := by
      calc
        _ ≤ 2 * (t : ℝ) * (C * (t : ℝ) ^ (3 - δ)) := by gcongr
        _ = _ := by rw [hpow]; ring
    have hcube : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ (4 - δ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num; linarith)
    have hc : ((Host.callerTime (instanceLength κ n) T + 12 : ℕ) : ℝ) ≤
        2 * (t : ℝ) * T + 355 * (t : ℝ) ^ 3 := by
      exact_mod_cast callerTime_add_twelve_le (instanceLength κ n) T
    have hcall : (Host.callerTime (instanceLength κ n) T + 12 : ℕ) ≤
        (2 * C + 355) * (t : ℝ) ^ (4 - δ) := by
      nlinarith only [hc, hT, hcube]
    have hscale : (n : ℝ) ^ ε * (t : ℝ) ^ (4 - δ) ≤
        (n : ℝ) ^ a := by
      calc
        _ ≤ (n : ℝ) ^ ε * ((n : ℝ) ^ (1 / 2 + ε : ℝ)) ^ (4 - δ) := by
          gcongr
        _ = (n : ℝ) ^ (ε + (1 / 2 + ε) * (4 - δ) : ℝ) := by
          rw [← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hscaleExp
    have hprod : (instanceBound κ n : ℝ) * (Host.callerTime (instanceLength κ n) T + 12 : ℕ) ≤
        (2 * C + 355) * (n : ℝ) ^ a := by
      calc
        _ ≤ (n : ℝ) ^ ε * ((2 * C + 355) * (t : ℝ) ^ (4 - δ)) := by gcongr
        _ = (2 * C + 355) * ((n : ℝ) ^ ε * (t : ℝ) ^ (4 - δ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ a := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn1 (show (0 : ℝ) ≤ a by linarith))
    have hconst := mul_le_mul_of_nonneg_left hone (show (0 : ℝ) ≤ 4 * E + 32 by positivity)
    unfold cost
    change ((ChanHe.Preprocessing.cost κ n + 4 * E + 32 +
      instanceBound κ n * (Host.callerTime (instanceLength κ n) T + 12) : ℕ) : ℝ) ≤ _
    push_cast at hprod ⊢
    nlinarith only [hpp, hprod, hconst]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  exact ⟨2 * C + 4 * E + 388, by positivity, M, hM⟩


end Cslib.Algorithms.WordRAM.ThreeSum.Decision
