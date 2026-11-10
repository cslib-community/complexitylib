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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Deterministic time hierarchies below every power of the logarithm

For every integer `a ≥ 1` and real `ε > 0`, deterministic time `O(n ^ a)` is strictly contained
in deterministic time `O(n ^ a * (log n) ^ ε)` on bit strings.

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

This is the translation method [Fortnow and Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
applied to a polylogarithmic-gap diagonal theorem. It covers the bounds `n ^ a` for integers
`a ≥ 1` only. It is not W. J. Paul's hierarchy for a fixed number of tapes (*On time
hierarchies*, 1979), and it does not give a `(log t) ^ ε` gap for arbitrary time-constructible
`t`.

## Main definitions

* `Cslib.Complexity.iterSqrtLog`: the iterated square root of the binary logarithm.

## Main results

* `Cslib.Complexity.DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow`:
  `DTIME (n ^ a) ⊊ DTIME ((n * iterSqrtLog p n) ^ a)`.
* `Cslib.Complexity.DTIME_pow_ssubset_DTIME_of_log_rpow`: `DTIME (n ^ a) ⊊ DTIME g` whenever
  `g n ≥ n ^ a * (log n) ^ ε` eventually, for some real `ε > 0`.

## References

* [L. Fortnow and R. Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
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
    have hpow : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h1 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow
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
theorem DTIME_pow_ssubset_DTIME_of_log_rpow {a : ℕ} (ha : 1 ≤ a) {ε : ℝ} (hε : 0 < ε)
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

end Cslib.Complexity
