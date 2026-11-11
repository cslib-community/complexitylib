/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Complexity.Classes.Constructible
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TimePolylog
import CslibFrontier.Computability.Complexity.Classes.Padding.Translation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Deterministic time hierarchies below every power of the logarithm

For every integer `a ≥ 1` and real `ε > 0`, deterministic time `O(n ^ a)` is strictly contained
in deterministic time `O(n ^ a * (log n) ^ ε)` on bit strings, and `O(2 ^ n)` is strictly
contained in `O(2 ^ n * n ^ ε)`. At `t = 2 ^ n` the gap `n ^ ε` is again `(log t) ^ ε`.

The gap function is `iterSqrtLog p n`, which applies `v ↦ ⌊√v⌋ + 1` to `⌊log₂ n⌋ + 1` `p` times
and so lies within constant factors of `(log n) ^ (1 / 2 ^ p)`. Suppose
`DTIME ((n * iterSqrtLog p n) ^ a) ⊆ DTIME (n ^ a)`. The translation lemma
`Cslib.Complexity.DTIME_comp_subset_of_subset` carries the collapse along the chain
`g₀ n = n + 1`, `g_{j+1} n = g_j n * iterSqrtLog p (g_j n)`, so `DTIME (g_J ^ a)` collapses to
`DTIME ((n + 1) ^ a)` for every `J`. Each step multiplies by at least `iterSqrtLog p n`, so
`g_J ^ a` exceeds `(n + 1) ^ a` times any fixed power of `log n` once `J` is a large multiple of
`2 ^ p`. This contradicts the polylogarithmic-gap hierarchy
`Cslib.Complexity.exists_DTIME_ssubset_DTIME_polylog`. Constant factors are absorbed by `DTIME`,
so no gap is lost along the chain.

For `2 ^ n` the chain is additive: `g_{j+1} n = g_j n + ⌊log₂ (g_j n + 1)⌋ / q + 1`, so
`2 ^ g_{j+1}` is `2 ^ g_j` times about `(g_j n) ^ (1 / q)`, and `2 * q * k` steps exceed
`2 ^ n` times the `k`-th power of `log (2 ^ n)`.

This is the translation method [Fortnow and Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
applied to a polylogarithmic-gap diagonal theorem. It covers the bounds `n ^ a` for integers
`a ≥ 1` and `2 ^ n` only. It is not W. J. Paul's hierarchy for a fixed number of tapes
[Paul1979], and it does not give a `(log t) ^ ε` gap for arbitrary time-constructible `t`.

## Main definitions

* `Cslib.Complexity.iterSqrtLog`: the iterated square root of the binary logarithm.

## Main results

* `Cslib.Complexity.DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow`:
  `DTIME (n ^ a) ⊊ DTIME ((n * iterSqrtLog p n) ^ a)`.
* `Cslib.Complexity.DTIME_pow_ssubset_DTIME_of_pow_mul_log_rpow_le`: `DTIME (n ^ a) ⊊ DTIME g`
  whenever `g n ≥ n ^ a * (log n) ^ ε` eventually, for some real `ε > 0`.
* `Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div`:
  `DTIME (2 ^ n) ⊊ DTIME (2 ^ (n + ⌊log₂ (n + 1)⌋ / q))` for `q ≥ 1`.
* `Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_of_two_pow_mul_rpow_le`:
  `DTIME (2 ^ n) ⊊ DTIME g` whenever `g n ≥ 2 ^ n * n ^ ε` eventually, for some real `ε > 0`.

## References

* [L. Fortnow and R. Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
* [W. J. Paul, *On time hierarchies*][Paul1979] (cited for contrast; not formalized here)
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

/-- The iterated square root of the binary logarithm: `⌊log₂ n⌋ + 1` with `v ↦ ⌊√v⌋ + 1` applied
`p` times. It is at least `1` and within constant factors of `(log n) ^ (1 / 2 ^ p)`
(`Cslib.Complexity.le_iterSqrtLog_pow`, `Cslib.Complexity.iterSqrtLog_pow_le`). -/
def iterSqrtLog (p n : ℕ) : ℕ :=
  (fun v => Nat.sqrt v + 1)^[p] (Nat.log 2 n + 1)

theorem iterSqrtLog_zero (n : ℕ) : iterSqrtLog 0 n = Nat.log 2 n + 1 := by simp [iterSqrtLog]

theorem iterSqrtLog_succ (p n : ℕ) : iterSqrtLog (p + 1) n = Nat.sqrt (iterSqrtLog p n) + 1 :=
  Function.iterate_succ_apply' _ _ _

theorem one_le_iterSqrtLog (p n : ℕ) : 1 ≤ iterSqrtLog p n := by
  cases p with
  | zero => exact Nat.succ_pos _
  | succ p => rw [iterSqrtLog_succ]; exact Nat.succ_pos _

theorem iterSqrtLog_mono (p : ℕ) : Monotone (iterSqrtLog p) := fun _ _ h =>
  (show Monotone fun v : ℕ => Nat.sqrt v + 1 from fun _ _ h => Nat.succ_le_succ
    (Nat.sqrt_le_sqrt h)).iterate p (Nat.succ_le_succ (Nat.log_mono_right h))

private theorem le_iterate_sqrt_succ_pow (p v : ℕ) :
    v ≤ ((fun w => Nat.sqrt w + 1)^[p] v) ^ 2 ^ p := by
  induction p generalizing v with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply]
    calc v ≤ (Nat.sqrt v + 1) ^ 2 := (Nat.lt_succ_sqrt' v).le
      _ ≤ (((fun w => Nat.sqrt w + 1)^[p] (Nat.sqrt v + 1)) ^ 2 ^ p) ^ 2 :=
          Nat.pow_le_pow_left (ih _) 2
      _ = _ := by rw [← pow_mul, pow_succ]

private theorem iterate_sqrt_succ_pow_le (p : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    ((fun w => Nat.sqrt w + 1)^[p] v) ^ 2 ^ p ≤ 4 ^ 2 ^ p * v := by
  induction p with
  | zero => simp; omega
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    set w := (fun w => Nat.sqrt w + 1)^[p] v
    have hw1 : 1 ≤ w := by
      cases p with
      | zero => exact hv
      | succ p => simp only [w, Function.iterate_succ_apply']; omega
    have hw : (Nat.sqrt w + 1) ^ 2 ≤ 4 * w := by
      nlinarith [Nat.sqrt_le w, Nat.sqrt_le_self w]
    calc (Nat.sqrt w + 1) ^ 2 ^ (p + 1) = ((Nat.sqrt w + 1) ^ 2) ^ 2 ^ p := by
          rw [← pow_mul, pow_succ']
      _ ≤ (4 * w) ^ 2 ^ p := Nat.pow_le_pow_left hw _
      _ = 4 ^ 2 ^ p * w ^ 2 ^ p := mul_pow _ _ _
      _ ≤ 4 ^ 2 ^ p * (4 ^ 2 ^ p * v) := Nat.mul_le_mul_left _ ih
      _ = 4 ^ 2 ^ (p + 1) * v := by rw [pow_succ 2 p, pow_mul]; ring

/-- `iterSqrtLog p n ^ 2 ^ p` is at least `⌊log₂ n⌋ + 1`. -/
theorem le_iterSqrtLog_pow (p n : ℕ) : Nat.log 2 n + 1 ≤ iterSqrtLog p n ^ 2 ^ p :=
  le_iterate_sqrt_succ_pow p _

/-- `iterSqrtLog p n ^ 2 ^ p` is at most `4 ^ 2 ^ p * (⌊log₂ n⌋ + 1)`. -/
theorem iterSqrtLog_pow_le (p n : ℕ) :
    iterSqrtLog p n ^ 2 ^ p ≤ 4 ^ 2 ^ p * (Nat.log 2 n + 1) :=
  iterate_sqrt_succ_pow_le p (Nat.succ_pos _)

private theorem computableInPolyTime_iterSqrtLog (p : ℕ) :
    ComputableInPolyTime (iterSqrtLog p) encNat encNat := by
  induction p with
  | zero =>
    exact .binary_add' (ComputableInPolyTime.unary_to_binary.comp
      ComputableInPolyTime.binary_log_two) (.const 1)
  | succ p ih =>
    rw [show iterSqrtLog (p + 1) = fun n => Nat.sqrt (iterSqrtLog p n) + 1 from
      funext (iterSqrtLog_succ p)]
    exact .binary_add' (.binary_sqrt' ih) (.const 1)

/-- The padding chain: `chain p 0 n = n + 1`, and each step multiplies by `iterSqrtLog p`. -/
private def chain (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | j + 1, n => chain p j n * iterSqrtLog p (chain p j n)

private theorem lt_chain (p j n : ℕ) : n < chain p j n := by
  induction j with
  | zero => exact Nat.lt_succ_self n
  | succ j ih => exact ih.trans_le (Nat.le_mul_of_pos_right _ (one_le_iterSqrtLog p _))

private theorem computableInPolyTime_chain (p j : ℕ) :
    ComputableInPolyTime (chain p j) encNat encNat := by
  induction j with
  | zero => exact .binary_add' .id' (.const 1)
  | succ j ih => exact .binary_mul' ih ((computableInPolyTime_iterSqrtLog p).comp ih)

private theorem succ_mul_pow_le_chain (p j n : ℕ) :
    (n + 1) * iterSqrtLog p n ^ j ≤ chain p j n := by
  induction j with
  | zero => simp [chain]
  | succ j ih =>
    change _ ≤ chain p j n * iterSqrtLog p (chain p j n)
    rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul ih (iterSqrtLog_mono p (lt_chain p j n).le)

/-- Far enough along, the chain exceeds the polylogarithmic gap of the diagonal theorem. -/
private theorem eventually_polylog_le_chain {a : ℕ} (ha : 1 ≤ a) (p k : ℕ) :
    ∀ᶠ n in atTop, ((n + 1) ^ a + 1) * (Nat.log 2 ((n + 1) ^ a + 1) + 1) ^ k ≤
      chain p (2 ^ p * (k + 1)) n ^ a := by
  filter_upwards [eventually_ge_atTop (2 ^ (2 * (a + 1) ^ k))] with n hn
  set L := Nat.log 2 n + 1 with hL
  have hLM : 2 * (a + 1) ^ k ≤ L := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn
    omega
  have hn2 : n + 1 ≤ 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
  have hpowL : (n + 1) ^ a ≤ 2 ^ (a * L) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left hn2 a
  have hlog : Nat.log 2 ((n + 1) ^ a + 1) + 1 ≤ (a + 1) * L := by
    have h2 : 2 ≤ 2 ^ (a * L) := Nat.le_self_pow (Nat.mul_pos (by omega) (by omega)).ne' 2
    have hlt : (n + 1) ^ a + 1 < 2 ^ (a * L + 1) := by rw [pow_succ]; omega
    have h3 : Nat.log 2 ((n + 1) ^ a + 1) < a * L + 1 :=
      Nat.log_lt_of_lt_pow (Nat.succ_ne_zero _) hlt
    rw [Nat.add_mul, one_mul]
    omega
  have hchain : (n + 1) * L ^ (k + 1) ≤ chain p (2 ^ p * (k + 1)) n :=
    calc (n + 1) * L ^ (k + 1) ≤ (n + 1) * (iterSqrtLog p n ^ 2 ^ p) ^ (k + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_iterSqrtLog_pow p n) _)
      _ = (n + 1) * iterSqrtLog p n ^ (2 ^ p * (k + 1)) := by rw [← pow_mul]
      _ ≤ _ := succ_mul_pow_le_chain p _ n
  have hone : 1 ≤ (n + 1) ^ a := Nat.one_le_pow _ _ (Nat.succ_pos n)
  calc ((n + 1) ^ a + 1) * (Nat.log 2 ((n + 1) ^ a + 1) + 1) ^ k
      ≤ (2 * (n + 1) ^ a) * ((a + 1) * L) ^ k := by gcongr; omega
    _ = (2 * (a + 1) ^ k) * ((n + 1) ^ a * L ^ k) := by rw [mul_pow]; ring
    _ ≤ L * ((n + 1) ^ a * L ^ k) := Nat.mul_le_mul_right _ hLM
    _ = (n + 1) ^ a * L ^ (k + 1) := by ring
    _ ≤ ((n + 1) * L ^ (k + 1)) ^ a := by
        rw [mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
    _ ≤ _ := Nat.pow_le_pow_left hchain a

/-- **Deterministic time hierarchy with an iterated-root-of-logarithm gap.** For every integer
`a ≥ 1` and every `p`, `DTIME (n ^ a) ⊊ DTIME ((n * iterSqrtLog p n) ^ a)`, where
`iterSqrtLog p n` is within constant factors of `(log n) ^ (1 / 2 ^ p)`. A collapse would
transfer along a padding chain to a collapse across a polylogarithmic gap, contradicting
`Cslib.Complexity.exists_DTIME_ssubset_DTIME_polylog`. -/
theorem DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow {a : ℕ} (ha : 1 ≤ a) (p : ℕ) :
    DTIME encBits (fun n => n ^ a) ⊂ DTIME encBits (fun n => (n * iterSqrtLog p n) ^ a) := by
  refine ⟨DTIME_mono fun n => Nat.pow_le_pow_left
    (Nat.le_mul_of_pos_right _ (one_le_iterSqrtLog p n)) a, fun hcollapse => ?_⟩
  have hstep (j : ℕ) : DTIME encBits (fun n => chain p (j + 1) n ^ a) ⊆
      DTIME encBits (fun n => chain p j n ^ a) :=
    DTIME_comp_subset_of_subset (f₁ := fun n => (n * iterSqrtLog p n) ^ a)
      (f₂ := fun n => n ^ a)
      (fun _ _ h => Nat.pow_le_pow_left (Nat.mul_le_mul h (iterSqrtLog_mono p h)) a)
      (fun n => (Nat.le_mul_of_pos_right _ (one_le_iterSqrtLog p n)).trans
        (Nat.le_self_pow (by omega) _))
      (fun n => Nat.le_self_pow (by omega) _) (computableInPolyTime_chain p j) (lt_chain p j)
      hcollapse
  have hchain (J : ℕ) : DTIME encBits (fun n => chain p J n ^ a) ⊆
      DTIME encBits (fun n => (n + 1) ^ a) := by
    induction J with
    | zero => exact Set.Subset.refl _
    | succ J ih => exact (hstep J).trans ih
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_polylog
  have hsep := hk (f := fun n => (n + 1) ^ a) (g := fun n => chain p (2 ^ p * (k + 1)) n ^ a)
    (timeConstructible_succ_pow a) (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _))
    (eventually_polylog_le_chain ha p k)
  exact hsep.2 (hchain _)

/-- `iterSqrtLog p n ^ a` is eventually at most `(log n) ^ ε` once `a / 2 ^ p < ε`. -/
private theorem eventually_iterSqrtLog_pow_le (p : ℕ) {a : ℕ} {ε : ℝ}
    (hδ : (a : ℝ) / 2 ^ p < ε) :
    ∀ᶠ n : ℕ in atTop, (iterSqrtLog p n : ℝ) ^ a ≤ Real.log n ^ ε := by
  set δ : ℝ := a / 2 ^ p with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  set K : ℝ := 3 * 4 ^ 2 ^ p
  have hT : Tendsto (fun n : ℕ => Real.log n ^ (ε - δ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hδ)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually_ge_atTop (K ^ δ), eventually_ge_atTop 3] with n hK hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log n := by
    have : Real.exp 1 ≤ n := (Real.exp_one_lt_d9.trans (by norm_num)).le.trans hn'
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hlog0 : 0 < Real.log n := by linarith
  have hL : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 3 * Real.log n := by
    have h1 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n :=
      (le_div_iff₀ (Real.log_pos one_lt_two)).1 (by simpa [Real.logb] using Real.natLog_le_logb n 2)
    have h3 : (Nat.log 2 n : ℝ) * 0.6931471803 ≤ Real.log n :=
      (mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg _)).trans h1
    linarith
  have hr' : iterSqrtLog p n ^ 2 ^ p ≤ 4 ^ 2 ^ p * (Nat.log 2 n + 1) := iterSqrtLog_pow_le p n
  have hr : (iterSqrtLog p n : ℝ) ^ 2 ^ p ≤ 4 ^ 2 ^ p * ((Nat.log 2 n : ℝ) + 1) := by
    exact_mod_cast hr'
  have hr0 : (0 : ℝ) ≤ iterSqrtLog p n := Nat.cast_nonneg _
  have hexp : ((2 ^ p : ℕ) : ℝ) * δ = (a : ℝ) := by
    rw [hδdef]
    push_cast
    field_simp
  calc (iterSqrtLog p n : ℝ) ^ a = (iterSqrtLog p n : ℝ) ^ (((2 ^ p : ℕ) : ℝ) * δ) := by
        rw [hexp, Real.rpow_natCast]
    _ = ((iterSqrtLog p n : ℝ) ^ 2 ^ p) ^ δ := by
        rw [Real.rpow_mul hr0, Real.rpow_natCast]
    _ ≤ (K * Real.log n) ^ δ := by
        refine Real.rpow_le_rpow (by positivity) (hr.trans ?_) hδ0
        have h4 : (0 : ℝ) ≤ 4 ^ 2 ^ p := by positivity
        calc (4 : ℝ) ^ 2 ^ p * ((Nat.log 2 n : ℝ) + 1) ≤ 4 ^ 2 ^ p * (3 * Real.log n) :=
              mul_le_mul_of_nonneg_left hL h4
          _ = K * Real.log n := by ring
    _ = K ^ δ * Real.log n ^ δ := Real.mul_rpow (by positivity) hlog0.le
    _ ≤ Real.log n ^ (ε - δ) * Real.log n ^ δ :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hlog0.le _)
    _ = Real.log n ^ ε := by rw [← Real.rpow_add hlog0]; congr 1; ring

/-- **Deterministic time hierarchy below every power of the logarithm.** For every integer
`a ≥ 1` and real `ε > 0`, if `g n ≥ n ^ a * (log n) ^ ε` for all large `n`, then
`DTIME (n ^ a) ⊊ DTIME g`. Choose `p` with `a / 2 ^ p < ε` and apply
`Cslib.Complexity.DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow`. -/
theorem DTIME_pow_ssubset_DTIME_of_pow_mul_log_rpow_le {a : ℕ} (ha : 1 ≤ a) {ε : ℝ} (hε : 0 < ε)
    {g : ℕ → ℕ} (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ a * Real.log n ^ ε ≤ g n) :
    DTIME encBits (fun n => n ^ a) ⊂ DTIME encBits g := by
  obtain ⟨p, hp⟩ := exists_nat_gt ((a : ℝ) / ε)
  have h2p : (p : ℝ) < 2 ^ p := by exact_mod_cast Nat.lt_two_pow_self
  have hδ : (a : ℝ) / 2 ^ p < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hp
    nlinarith
  have hle : ∀ᶠ n in atTop, (n * iterSqrtLog p n) ^ a ≤ g n := by
    filter_upwards [hg, eventually_iterSqrtLog_pow_le p hδ] with n hg hr
    have : (((n * iterSqrtLog p n) ^ a : ℕ) : ℝ) ≤ (g n : ℝ) := by
      push_cast
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans hg
    exact_mod_cast this
  have hsep := DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow ha p
  exact ⟨hsep.1.trans (DTIME_mono_of_eventually_le hle),
    fun h => hsep.2 ((DTIME_mono_of_eventually_le hle).trans h)⟩

/-! ### Exponential time -/

/-- The additive padding chain for exponential time: `expChain q 0 n = n + 1`, and each step adds
`⌊log₂ (v + 1)⌋ / q + 1`. -/
private def expChain (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | j + 1, n => expChain q j n + Nat.log 2 (expChain q j n + 1) / q + 1

private theorem lt_expChain (q j n : ℕ) : n < expChain q j n := by
  induction j with
  | zero => exact Nat.lt_succ_self n
  | succ j ih => exact Nat.lt_succ_of_le (ih.le.trans (Nat.le_add_right _ _))

private theorem computableInPolyTime_expChain (q j : ℕ) :
    ComputableInPolyTime (expChain q j) encNat encNat := by
  induction j with
  | zero => exact .binary_add' .id' (.const 1)
  | succ j ih =>
    exact .binary_add' (.binary_add' ih (.binary_div' (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.binary_log_two.comp (.binary_add' ih (.const 1)))) (.const q)))
      (.const 1)

private theorem le_expChain (q j n : ℕ) :
    n + 1 + j * (Nat.log 2 (n + 1) / q) ≤ expChain q j n := by
  induction j with
  | zero => simp [expChain]
  | succ j ih =>
    change _ ≤ expChain q j n + Nat.log 2 (expChain q j n + 1) / q + 1
    have h : Nat.log 2 (n + 1) / q ≤ Nat.log 2 (expChain q j n + 1) / q :=
      Nat.div_le_div_right (Nat.log_mono_right (by have := lt_expChain q j n; omega))
    rw [add_one_mul]
    omega

/-- Far enough along, the additive chain exceeds the polylogarithmic gap at `2 ^ n`. -/
private theorem eventually_polylog_le_expChain {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    ∀ᶠ n in atTop, (2 ^ n + 1) * (Nat.log 2 (2 ^ n + 1) + 1) ^ k ≤
      2 ^ expChain q (2 * q * k) n := by
  filter_upwards [eventually_ge_atTop (2 ^ (2 * q))] with n hn
  set L := Nat.log 2 (n + 1) with hL
  have h2n : 2 ≤ 2 ^ n :=
    Nat.le_self_pow (by have := @Nat.one_le_two_pow (2 * q); omega) 2
  have hLq : 2 * q ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hM : L + 1 ≤ 2 * (q * (L / q)) := by
    have h1 := Nat.div_add_mod L q
    have h2 := Nat.mod_lt L (by omega : 0 < q)
    generalize q * (L / q) = e at h1 ⊢
    generalize L % q = r at h1 h2
    omega
  have hlogn : Nat.log 2 (2 ^ n + 1) + 1 ≤ n + 1 := by
    have hlt : 2 ^ n + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
    have : Nat.log 2 (2 ^ n + 1) < n + 1 := Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  have hpow : (n + 1) ^ k ≤ 2 ^ (2 * q * k * (L / q)) := by
    calc (n + 1) ^ k ≤ (2 ^ (L + 1)) ^ k :=
          Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) _).le k
      _ ≤ (2 ^ (2 * (q * (L / q)))) ^ k :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right two_pos hM) k
      _ = 2 ^ (2 * q * k * (L / q)) := by rw [← pow_mul]; congr 1; ring
  have hchain : n + 1 + 2 * q * k * (L / q) ≤ expChain q (2 * q * k) n := le_expChain q _ n
  calc (2 ^ n + 1) * (Nat.log 2 (2 ^ n + 1) + 1) ^ k ≤ (2 * 2 ^ n) * (n + 1) ^ k :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hlogn k)
    _ ≤ 2 * 2 ^ n * 2 ^ (2 * q * k * (L / q)) := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ (n + 1 + 2 * q * k * (L / q)) := by rw [pow_add, pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right two_pos hchain

/-- **Deterministic exponential-time hierarchy with a root gap.** For every `q ≥ 1`,
`DTIME (2 ^ n) ⊊ DTIME (2 ^ (n + ⌊log₂ (n + 1)⌋ / q))`; the gap factor
`2 ^ (⌊log₂ (n + 1)⌋ / q)` is within a factor `2` of `(n + 1) ^ (1 / q)`. A collapse would
transfer along the additive padding chain `g₀ n = n + 1`,
`g_{j+1} n = g_j n + ⌊log₂ (g_j n + 1)⌋ / q + 1` to a collapse across the polylogarithmic gap of
`Cslib.Complexity.exists_DTIME_ssubset_DTIME_polylog`. -/
theorem DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div {q : ℕ} (hq : 1 ≤ q) :
    DTIME encBits (fun n => 2 ^ n) ⊂
      DTIME encBits (fun n => 2 ^ (n + Nat.log 2 (n + 1) / q)) := by
  refine ⟨DTIME_mono fun n => Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _),
    fun hcollapse => ?_⟩
  have hstep (j : ℕ) : DTIME encBits (fun n => 2 ^ expChain q (j + 1) n) ⊆
      DTIME encBits (fun n => 2 ^ expChain q j n) :=
    (DTIME_mono_of_le_mul_add (C := 2) fun n => by
      change 2 ^ (expChain q j n + Nat.log 2 (expChain q j n + 1) / q + 1) ≤
        2 * 2 ^ (expChain q j n + Nat.log 2 (expChain q j n + 1) / q) + 2
      rw [pow_succ]
      omega).trans
    (DTIME_comp_subset_of_subset (f₁ := fun n => 2 ^ (n + Nat.log 2 (n + 1) / q))
      (f₂ := fun n => 2 ^ n)
      (fun a b h => Nat.pow_le_pow_right two_pos
        (Nat.add_le_add h (Nat.div_le_div_right (Nat.log_mono_right (by omega)))))
      (fun n => Nat.lt_two_pow_self.le.trans
        (Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _)))
      (fun n => Nat.lt_two_pow_self.le) (computableInPolyTime_expChain q j) (lt_expChain q j)
      hcollapse)
  have hchain (J : ℕ) : DTIME encBits (fun n => 2 ^ expChain q J n) ⊆
      DTIME encBits (fun n => 2 ^ n) := by
    induction J with
    | zero =>
      exact DTIME_mono_of_le_mul_add (C := 2) fun n => by
        change 2 ^ (n + 1) ≤ 2 * 2 ^ n + 2
        rw [pow_succ]
        omega
    | succ J ih => exact (hstep J).trans ih
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_polylog
  have hsep := hk (f := fun n => 2 ^ n) (g := fun n => 2 ^ expChain q (2 * q * k) n)
    timeConstructible_two_pow (fun n => Nat.lt_two_pow_self.le)
    (eventually_polylog_le_expChain hq k)
  exact hsep.2 (hchain _)

/-- `2 ^ (⌊log₂ (n + 1)⌋ / q)` is eventually at most `n ^ ε` once `1 / q < ε`. -/
private theorem eventually_two_pow_log_div_le {q : ℕ} (hq : 1 ≤ q) {ε : ℝ}
    (hε : 1 / (q : ℝ) < ε) :
    ∀ᶠ n : ℕ in atTop, ((2 ^ (Nat.log 2 (n + 1) / q) : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT : Tendsto (fun n : ℕ => (n : ℝ) ^ (ε - 1 / q)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.2 hε)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop ((2 : ℝ) ^ (1 / (q : ℝ))), eventually_ge_atTop 1]
    with n hT hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((2 ^ (Nat.log 2 (n + 1) / q) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Nat.cast_nonneg _
  have hxq : x ^ q ≤ 2 * n := by
    have h1 : (2 ^ (Nat.log 2 (n + 1) / q)) ^ q ≤ 2 * n := by
      rw [← pow_mul]
      calc 2 ^ (Nat.log 2 (n + 1) / q * q) ≤ 2 ^ Nat.log 2 (n + 1) :=
            Nat.pow_le_pow_right two_pos (Nat.div_mul_le_self _ _)
        _ ≤ n + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)
        _ ≤ 2 * n := by omega
    rw [hx]
    exact_mod_cast h1
  rw [← hx]
  calc x = (x ^ q) ^ (1 / (q : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, mul_one_div_cancel hq0.ne', Real.rpow_one]
    _ ≤ (2 * n) ^ (1 / (q : ℝ)) := Real.rpow_le_rpow (pow_nonneg hx0 _) hxq (by positivity)
    _ = 2 ^ (1 / (q : ℝ)) * (n : ℝ) ^ (1 / (q : ℝ)) := Real.mul_rpow (by norm_num) hn0.le
    _ ≤ (n : ℝ) ^ (ε - 1 / q) * (n : ℝ) ^ (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ε := by rw [← Real.rpow_add hn0]; congr 1; ring

/-- **Deterministic exponential-time hierarchy below every power of `n`.** For every real
`ε > 0`, if `g n ≥ 2 ^ n * n ^ ε` for all large `n`, then `DTIME (2 ^ n) ⊊ DTIME g`; at
`t = 2 ^ n` the gap `n ^ ε` is `(log₂ t) ^ ε`. Choose `q` with `1 / q < ε` and apply
`Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div`. -/
theorem DTIME_two_pow_ssubset_DTIME_of_two_pow_mul_rpow_le {ε : ℝ} (hε : 0 < ε) {g : ℕ → ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ n * (n : ℝ) ^ ε ≤ g n) :
    DTIME encBits (fun n => 2 ^ n) ⊂ DTIME encBits g := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
  have hq1 : 1 ≤ q := by
    have : (0 : ℝ) < q := (one_div_pos.2 hε).trans hq
    have : 0 < q := by exact_mod_cast this
    omega
  have hqε : 1 / (q : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hq
    linarith
  have hle : ∀ᶠ n in atTop, 2 ^ (n + Nat.log 2 (n + 1) / q) ≤ g n := by
    filter_upwards [hg, eventually_two_pow_log_div_le hq1 hqε] with n hg hr
    have : ((2 ^ (n + Nat.log 2 (n + 1) / q) : ℕ) : ℝ) ≤ (g n : ℝ) := by
      push_cast [pow_add] at hr ⊢
      exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans hg
    exact_mod_cast this
  have hsep := DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div hq1
  exact ⟨hsep.1.trans (DTIME_mono_of_eventually_le hle),
    fun h => hsep.2 ((DTIME_mono_of_eventually_le hle).trans h)⟩

end Cslib.Complexity
