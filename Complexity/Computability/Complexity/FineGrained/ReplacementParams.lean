/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingScale
public import Complexity.Foundations.Combinatorics.BinomialTail
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The concrete replacement parameter schedule (Section 4.7, Lemma 4.8)

Section 4.7 of `[OpenAI2026ETH]` instantiates the general replacement-matrix hypotheses of
Lemma 4.7 in the polylogarithmic degree/occurrence regime `b, w ≤ λ ^ β`, where `λ = ⌈log₂ n⌉` and
`ν = ⌈log₂ λ⌉`. Equation (4.17) sets

* `r = ⌊√λ / ν²⌋` (`numGroups`),
* `Q = ⌊λ / (128 ν)⌋` (`numNodes`),
* `R = (β + 3) ⌈√λ⌉` (`rowBound`),
* `τ = 1 / (r λ)` (`tau`), `ε = 1 / (b r² λ)` (`tailBudget`), `D = r ^ (2 Q)` (`auxDim`),
* `μ = Q (r - 1) / (2 r)` (`mean`), `A₀ = ⌊μ - (R - 1) / 2⌋` (`intervalStart`), and
  `I = {A₀, …, A₀ + R - 1}` (`interval`).

This module gives computable integer definitions for the discrete parameters, proves their exact
identities with the real floor/ceiling formulas of equation (4.17), establishes the deterministic
containment, biased Binomial tail (`binomTail_lt_tailBudget`), and row-cost (`rowCost_le`) bounds
once `2 ≤ r`, `32 ≤ R`, and `6 R ≤ Q`, proves Lemma 4.8 (`exists_feasible`) for all sufficiently
large `n`, and connects `n * rowCost β n` to `interpolationScale` from `CountingScale.lean`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.numGroups`: `r = ⌊√λ / ν²⌋`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.numNodes`: `Q = ⌊λ / (128 ν)⌋`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.rowBound`: `R = (β + 3) ⌈√λ⌉`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.auxDim`: `D = r ^ (2 Q)`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.interval`: `I = {A₀, …, A₀ + R - 1}`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.binomTail`: `Pr[W ∉ I]` under
  `Bin(Q, (r - 1) / (2 r))`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.rowCost`: the counting-exponent factor
  `(R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r` of equation (4.18).
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible`: combined Lemma 4.7 and
  Lemma 4.8 numerical conditions.

## Main results

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.auxDim_le_two_pow`: `D ≤ 2 ^ (λ / 128)`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.binomTail_lt_tailBudget`:
  `Pr[W ∉ I] < 1 / (b r² λ) = τ / (r b)`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.rowCost_le`: deterministic `O_β(ν² / √λ)`
  bound on `rowCost`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.exists_feasible`: Lemma 4.8 for
  `1 ≤ b, w ≤ λ ^ β` (and `exists_feasible_of_le_const` for `1 ≤ b, w ≤ β`).
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.isBigO_mul_rowCost_interpolationScale` and
  `isLittleO_mul_rowCost`: asymptotic link to `interpolationScale`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 4.6, Lemma 4.7,
  p. 33; Section 4.7, Lemma 4.8, pp. 34–35.
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT

open Filter Finset Asymptotics
open scoped Topology

namespace ReplacementParams

/-! ### Schedule definitions (equation 4.17) -/

/-- Number of variable/factor groups `r = ⌊√λ / ν²⌋`, computed via integer square root and
division for `λ = Nat.clog 2 n` and `ν = Nat.clog 2 λ`. -/
def numGroups (n : ℕ) : ℕ :=
  (Nat.clog 2 n).sqrt / Nat.clog 2 (Nat.clog 2 n) ^ 2

/-- Number of interpolation nodes per block `Q = ⌊λ / (128 ν)⌋`. -/
def numNodes (n : ℕ) : ℕ :=
  Nat.clog 2 n / (128 * Nat.clog 2 (Nat.clog 2 n))

/-- Degree/interval length parameter `R = (β + 3) ⌈√λ⌉`. -/
def rowBound (β n : ℕ) : ℕ :=
  (β + 3) * (if Nat.clog 2 n = 0 then 0 else (Nat.clog 2 n - 1).sqrt + 1)

/-- Auxiliary replacement dimension `D = r ^ (2 Q)`. -/
def auxDim (n : ℕ) : ℕ :=
  numGroups n ^ (2 * numNodes n)

/-- Measurement step scale `τ = 1 / (r λ)`. -/
noncomputable def tau (n : ℕ) : ℝ :=
  1 / ((numGroups n : ℝ) * Nat.clog 2 n)

/-- Binomial tail budget `ε = 1 / (b r² λ)` of equation (4.17). -/
noncomputable def tailBudget (b n : ℕ) : ℝ :=
  1 / ((b : ℝ) * (numGroups n : ℝ) ^ 2 * Nat.clog 2 n)

/-- Single-trial bias `p = (r - 1) / (2 r)` of Lemma 4.7 and Lemma 4.8. -/
noncomputable def binomProb (n : ℕ) : ℝ :=
  ((numGroups n : ℝ) - 1) / (2 * numGroups n)

/-- Binomial mean `μ = Q (r - 1) / (2 r)` of Lemma 4.8. -/
noncomputable def mean (n : ℕ) : ℝ :=
  (numNodes n : ℝ) * binomProb n

/-- Left endpoint `A₀ = ⌊μ - (R - 1) / 2⌋` of the concentrated weight interval `I`. -/
def intervalStart (β n : ℕ) : ℕ :=
  (numNodes n * (numGroups n - 1) - numGroups n * (rowBound β n - 1)) / (2 * numGroups n)

/-- Discrete weight interval `I = {A₀, …, A₀ + R - 1}`. -/
def interval (β n : ℕ) : Finset ℕ :=
  Finset.Icc (intervalStart β n) (intervalStart β n + rowBound β n - 1)

/-- Binomial tail probability `Pr[W ∉ I]` for `W ~ Bin(Q, (r - 1) / (2 r))`. -/
noncomputable def binomTail (β n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (numNodes n + 1) with k ∉ interval β n,
    ((numNodes n).choose k : ℝ) * binomProb n ^ k * (1 - binomProb n) ^ (numNodes n - k)

/-- The three-term counting-exponent quantity `(R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r`
bounded in equation (4.18). -/
noncomputable def rowCost (β n : ℕ) : ℝ :=
  (rowBound β n : ℝ) / numNodes n * Real.log (2 * (numNodes n : ℝ) / rowBound β n) +
    tau n * Real.log (2 * (auxDim n : ℝ) + 1) + 1 / numGroups n

/-! ### Exact floor/ceiling identities and unconditional `auxDim` bound -/

/-- `tailBudget b n` equals `τ / (r b)`, matching Lemma 4.7's tail threshold. -/
theorem tailBudget_eq_tau_div (b n : ℕ) :
    tailBudget b n = tau n / ((numGroups n : ℝ) * b) := by
  simp only [tailBudget, tau, div_eq_mul_inv, mul_inv_rev]
  ring

/-- `numGroups n` agrees with the real floor `⌊√λ / ν²⌋₊` for every `n`. -/
theorem numGroups_eq_floor (n : ℕ) :
    numGroups n = ⌊Real.sqrt (Nat.clog 2 n) / (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2⌋₊ := by
  unfold numGroups
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  rcases Nat.eq_zero_or_pos nu with hnu | hnu
  · simp only [hnu, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Nat.div_zero,
      Nat.cast_zero, div_zero, Nat.floor_zero]
  have hnu2_pos : 0 < nu ^ 2 := by positivity
  have hnu2_rpos : (0 : ℝ) < (nu : ℝ) ^ 2 := by positivity
  symm
  rw [Nat.floor_eq_iff (by positivity)]
  set q := lam.sqrt / nu ^ 2
  have hsq_le : (lam.sqrt : ℝ) ≤ Real.sqrt lam := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' lam
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hnu2_rpos]
    have hmul : q * nu ^ 2 ≤ lam.sqrt := Nat.div_mul_le_self lam.sqrt (nu ^ 2)
    exact (by exact_mod_cast hmul : (q : ℝ) * (nu : ℝ) ^ 2 ≤ lam.sqrt).trans hsq_le
  · rw [div_lt_iff₀ hnu2_rpos]
    have hlt_mul : lam.sqrt + 1 ≤ (q + 1) * nu ^ 2 := by
      have hdiv : nu ^ 2 * q + lam.sqrt % nu ^ 2 = lam.sqrt := Nat.div_add_mod lam.sqrt (nu ^ 2)
      have hmod := Nat.mod_lt lam.sqrt hnu2_pos
      rw [add_mul, one_mul, mul_comm q]
      omega
    have hlam_lt : lam < ((q + 1) * nu ^ 2) ^ 2 :=
      (Nat.lt_succ_sqrt' lam).trans_le (Nat.pow_le_pow_left hlt_mul 2)
    have hlam_rlt : (lam : ℝ) < (((q : ℝ) + 1) * (nu : ℝ) ^ 2) ^ 2 := by
      exact_mod_cast hlam_lt
    exact (Real.sqrt_lt' (by positivity)).mpr hlam_rlt

/-- Lower integer comparison bound: `r² ν⁴ ≤ λ` for every `n`, where `r = numGroups n`,
`λ = Nat.clog 2 n`, and `ν = Nat.clog 2 λ` ([OpenAI2026ETH], Proposition 6.4, pp. 43–44). -/
theorem sq_mul_pow_four_le_clog (n : ℕ) :
    numGroups n ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 ≤ Nat.clog 2 n := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hsq : (numGroups n * nu ^ 2) ^ 2 ≤ lam.sqrt ^ 2 :=
    Nat.pow_le_pow_left (Nat.div_mul_le_self lam.sqrt (nu ^ 2)) 2
  have hsqrt : lam.sqrt ^ 2 ≤ lam := by simpa only [sq] using Nat.sqrt_le lam
  calc
    numGroups n ^ 2 * nu ^ 4 = (numGroups n * nu ^ 2) ^ 2 := by ring
    _ ≤ lam := hsq.trans hsqrt

/-- Upper integer comparison bound: `λ < (r + 1)² ν⁴` whenever `1 ≤ ν` (`3 ≤ n`), where
`r = numGroups n`, `λ = Nat.clog 2 n`, and `ν = Nat.clog 2 λ`
([OpenAI2026ETH], Proposition 6.4, pp. 43–44). -/
theorem clog_lt_succ_sq_mul_pow_four {n : ℕ} (hnu : 1 ≤ Nat.clog 2 (Nat.clog 2 n)) :
    Nat.clog 2 n < (numGroups n + 1) ^ 2 * Nat.clog 2 (Nat.clog 2 n) ^ 4 := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hdiv : lam.sqrt + 1 ≤ (numGroups n + 1) * nu ^ 2 := by
    have hlt : lam.sqrt < nu ^ 2 * (numGroups n + 1) :=
      Nat.lt_mul_div_succ lam.sqrt (pow_pos hnu 2)
    rw [mul_comm] at hlt
    omega
  have hsqrt : lam < (lam.sqrt + 1) ^ 2 := by simpa only [sq] using Nat.lt_succ_sqrt lam
  calc
    lam < (lam.sqrt + 1) ^ 2 := hsqrt
    _ ≤ ((numGroups n + 1) * nu ^ 2) ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ = (numGroups n + 1) ^ 2 * nu ^ 4 := by ring

/-- `numNodes n` agrees with the real floor `⌊λ / (128 ν)⌋₊` for every `n`. -/
theorem numNodes_eq_floor (n : ℕ) :
    numNodes n = ⌊(Nat.clog 2 n : ℝ) / (128 * Nat.clog 2 (Nat.clog 2 n))⌋₊ := by
  unfold numNodes
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  rcases Nat.eq_zero_or_pos nu with hnu | hnu
  · simp only [hnu, mul_zero, Nat.div_zero, Nat.cast_zero, div_zero, Nat.floor_zero]
  have hd_pos : 0 < 128 * nu := by positivity
  have hd_rpos : (0 : ℝ) < 128 * (nu : ℝ) := by positivity
  symm
  rw [Nat.floor_eq_iff (by positivity)]
  set q := lam / (128 * nu)
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hd_rpos]
    exact_mod_cast Nat.div_mul_le_self lam (128 * nu)
  · rw [div_lt_iff₀ hd_rpos]
    have hlt : lam < (q + 1) * (128 * nu) := by
      have hdiv : 128 * nu * q + lam % (128 * nu) = lam := Nat.div_add_mod lam (128 * nu)
      have hmod := Nat.mod_lt lam hd_pos
      rw [add_mul, one_mul, mul_comm q]
      omega
    exact_mod_cast hlt

/-- `rowBound β n` agrees with `(β + 3) * ⌈√λ⌉₊` for every `β` and `n`. -/
theorem rowBound_eq_mul_ceil (β n : ℕ) :
    rowBound β n = (β + 3) * ⌈Real.sqrt (Nat.clog 2 n)⌉₊ := by
  unfold rowBound
  congr 1
  set m := Nat.clog 2 n
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp only [hm, ↓reduceIte, Nat.cast_zero, Real.sqrt_zero, Nat.ceil_zero]
  simp only [hm.ne', ↓reduceIte]
  symm
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero _), Nat.succ_sub_one]
  set s := (m - 1).sqrt
  refine ⟨?_, ?_⟩
  · have hs2 : s ^ 2 < m := (Nat.sqrt_le' (m - 1)).trans_lt (Nat.sub_lt hm one_pos)
    rw [Real.lt_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast hs2
  · have hm_le : m ≤ (s + 1) ^ 2 := by
      have hlt : m - 1 < (s + 1) ^ 2 := Nat.lt_succ_sqrt' (m - 1)
      omega
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by exact_mod_cast hm_le⟩

/-- Unconditional integer auxiliary dimension bound `D ≤ 2 ^ (λ / 128)` of Lemma 4.8. -/
theorem auxDim_le_two_pow (n : ℕ) : auxDim n ≤ 2 ^ (Nat.clog 2 n / 128) := by
  unfold auxDim numGroups numNodes
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  rcases Nat.eq_zero_or_pos nu with hnu | hnu
  · simp only [hnu, mul_zero, Nat.div_zero, pow_zero]
    exact Nat.one_le_two_pow
  set Q := lam / (128 * nu)
  have hr2 : (lam.sqrt / nu ^ 2) ^ 2 ≤ 2 ^ nu := by
    calc (lam.sqrt / nu ^ 2) ^ 2
        ≤ lam.sqrt ^ 2 := Nat.pow_le_pow_left (Nat.div_le_self _ _) 2
      _ ≤ lam := Nat.sqrt_le' lam
      _ ≤ 2 ^ nu := Nat.le_pow_clog one_lt_two lam
  have hnuQ : nu * Q ≤ lam / 128 := by
    rw [show Q = lam / 128 / nu from (Nat.div_div_eq_div_mul lam 128 nu).symm]
    exact Nat.mul_div_le (lam / 128) nu
  calc (lam.sqrt / nu ^ 2) ^ (2 * Q)
      = ((lam.sqrt / nu ^ 2) ^ 2) ^ Q := pow_mul _ 2 Q
    _ ≤ (2 ^ nu) ^ Q := Nat.pow_le_pow_left hr2 Q
    _ = 2 ^ (nu * Q) := (pow_mul 2 nu Q).symm
    _ ≤ 2 ^ (lam / 128) := Nat.pow_le_pow_right two_pos hnuQ

/-- Real-exponent form `D ≤ 2 ^ ((λ : ℝ) / 128)` of Lemma 4.8. -/
theorem auxDim_le_rpow (n : ℕ) :
    (auxDim n : ℝ) ≤ (2 : ℝ) ^ ((Nat.clog 2 n : ℝ) / 128) := by
  calc (auxDim n : ℝ)
      ≤ ((2 ^ (Nat.clog 2 n / 128) : ℕ) : ℝ) := by exact_mod_cast auxDim_le_two_pow n
    _ = (2 : ℝ) ^ ((Nat.clog 2 n / 128 : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((Nat.clog 2 n : ℝ) / 128) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) Nat.cast_div_le

/-! ### Deterministic interval, Binomial tail, and row-cost bounds -/

private theorem mul_sub_le_mul_sub {β n : ℕ} (hr : 2 ≤ numGroups n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) :
    numGroups n * (rowBound β n - 1) ≤ numNodes n * (numGroups n - 1) := by
  have hr1 : numGroups n ≤ 2 * (numGroups n - 1) := by omega
  calc numGroups n * (rowBound β n - 1)
      ≤ numGroups n * rowBound β n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ 2 * (numGroups n - 1) * rowBound β n := Nat.mul_le_mul_right _ hr1
    _ = 2 * rowBound β n * (numGroups n - 1) := by ring
    _ ≤ numNodes n * (numGroups n - 1) := Nat.mul_le_mul_right _ hRQ

private theorem intervalStart_bounds {β n : ℕ} (hr : 2 ≤ numGroups n) (hR : 1 ≤ rowBound β n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) :
    mean n - ((rowBound β n : ℝ) - 1) / 2 - 1 < (intervalStart β n : ℝ) ∧
      (intervalStart β n : ℝ) ≤ mean n - ((rowBound β n : ℝ) - 1) / 2 := by
  unfold intervalStart mean binomProb
  set r := numGroups n
  set Q := numNodes n
  set R := rowBound β n
  set num := Q * (r - 1) - r * (R - 1)
  have hsub := mul_sub_le_mul_sub hr hRQ
  have hr_pos : 0 < 2 * r := by omega
  have hr_rpos : (0 : ℝ) < r := by positivity
  have h2r_rpos : (0 : ℝ) < 2 * (r : ℝ) := by positivity
  set q := num / (2 * r)
  have hle_nat : 2 * r * q ≤ num := Nat.mul_div_le num (2 * r)
  have hlt_nat : num < 2 * r * (q + 1) := by
    have hdiv : 2 * r * q + num % (2 * r) = num := Nat.div_add_mod num (2 * r)
    have hmod := Nat.mod_lt num hr_pos
    rw [mul_add, mul_one]
    omega
  have hnum_cast : (num : ℝ) = (Q : ℝ) * ((r : ℝ) - 1) - (r : ℝ) * ((R : ℝ) - 1) := by
    have hr1 : (1 : ℕ) ≤ r := by omega
    rw [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_sub hR,
      Nat.cast_one]
  have hmean_eq : (Q : ℝ) * (((r : ℝ) - 1) / (2 * r)) - ((R : ℝ) - 1) / 2 =
      (num : ℝ) / (2 * r) := by
    rw [hnum_cast]
    field_simp
  rw [hmean_eq]
  refine ⟨?_, ?_⟩
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ h2r_rpos]
    have hlt_r : (num : ℝ) < 2 * (r : ℝ) * ((q : ℝ) + 1) := by exact_mod_cast hlt_nat
    linarith
  · rw [le_div_iff₀ h2r_rpos]
    have hle_r : 2 * (r : ℝ) * (q : ℝ) ≤ num := by exact_mod_cast hle_nat
    linarith

/-- `intervalStart β n` equals the `ℕ`-floor `⌊μ - (R - 1) / 2⌋₊` once `2 ≤ r`, `1 ≤ R`, and
`2 R ≤ Q`. -/
theorem intervalStart_eq_natFloor {β n : ℕ} (hr : 2 ≤ numGroups n) (hR : 1 ≤ rowBound β n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) :
    intervalStart β n = ⌊mean n - ((rowBound β n : ℝ) - 1) / 2⌋₊ := by
  obtain ⟨hlt, hle⟩ := intervalStart_bounds hr hR hRQ
  have hnonneg : 0 ≤ mean n - ((rowBound β n : ℝ) - 1) / 2 :=
    (Nat.cast_nonneg (intervalStart β n)).trans hle
  symm
  rw [Nat.floor_eq_iff hnonneg]
  exact ⟨hle, by linarith⟩

/-- `(intervalStart β n : ℤ)` equals the integer floor `⌊μ - (R - 1) / 2⌋` once `2 ≤ r`, `1 ≤ R`,
and `2 R ≤ Q`. -/
theorem intervalStart_eq_intFloor {β n : ℕ} (hr : 2 ≤ numGroups n) (hR : 1 ≤ rowBound β n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) :
    (intervalStart β n : ℤ) = ⌊mean n - ((rowBound β n : ℝ) - 1) / 2⌋ := by
  obtain ⟨hlt, hle⟩ := intervalStart_bounds hr hR hRQ
  symm
  rw [Int.floor_eq_iff]
  exact ⟨by exact_mod_cast hle, by push_cast; linarith⟩

/-- The interval `I = {A₀, …, A₀ + R - 1}` has exact cardinality `R` whenever `1 ≤ R`. -/
theorem card_interval {β n : ℕ} (hR : 1 ≤ rowBound β n) :
    #(interval β n) = rowBound β n := by
  unfold interval
  rw [Nat.card_Icc]
  omega

/-- Whenever `2 ≤ r`, `1 ≤ R`, and `2 R ≤ Q`, the interval `I` lies inside `{0, …, Q}`. -/
theorem interval_subset_range {β n : ℕ} (hr : 2 ≤ numGroups n) (hR : 1 ≤ rowBound β n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) :
    interval β n ⊆ Finset.range (numNodes n + 1) := by
  intro k hk
  simp only [interval, mem_Icc, mem_range] at hk ⊢
  set r := numGroups n
  set Q := numNodes n
  set R := rowBound β n
  set A₀ := intervalStart β n
  have hsub : r * (R - 1) ≤ Q * (r - 1) := mul_sub_le_mul_sub hr hRQ
  have hA₀ : 2 * r * A₀ ≤ Q * (r - 1) - r * (R - 1) := Nat.mul_div_le _ (2 * r)
  have hA₀' : 2 * r * A₀ + r * (R - 1) ≤ Q * (r - 1) :=
    (Nat.add_le_add_right hA₀ _).trans_eq (Nat.sub_add_cancel hsub)
  have htop : 2 * r * (A₀ + R - 1) ≤ 2 * r * Q := by
    rw [show A₀ + R - 1 = A₀ + (R - 1) by omega, mul_add]
    have h2 : Q * (r - 1) ≤ Q * r := Nat.mul_le_mul_left Q (Nat.sub_le r 1)
    have h3 : r * (R - 1) ≤ r * Q := Nat.mul_le_mul_left r (by omega)
    have h4 : Q * r + r * Q = 2 * r * Q := by ring
    have h5 : 2 * r * (R - 1) = r * (R - 1) + r * (R - 1) := by ring
    omega
  have hAQ : A₀ + R - 1 ≤ Q := Nat.le_of_mul_le_mul_left htop (by omega)
  omega

/-- Whenever `2 ≤ r`, `32 ≤ R`, and `2 R ≤ Q`, every natural number within `R / 4` of `μ` belongs
to `interval β n`. -/
theorem mem_interval_of_abs_sub_le {β n k : ℕ} (hr : 2 ≤ numGroups n) (hR : 32 ≤ rowBound β n)
    (hRQ : 2 * rowBound β n ≤ numNodes n) (hk : |(k : ℝ) - mean n| ≤ (rowBound β n : ℝ) / 4) :
    k ∈ interval β n := by
  have hR1 : 1 ≤ rowBound β n := by omega
  obtain ⟨hlt, hle⟩ := intervalStart_bounds hr hR1 hRQ
  obtain ⟨hkl, hku⟩ := abs_sub_le_iff.mp hk
  have hR_real : (32 : ℝ) ≤ rowBound β n := by exact_mod_cast hR
  have hk_low : (intervalStart β n : ℝ) ≤ k := by linarith
  have hk_high : (k : ℝ) ≤ ((intervalStart β n + rowBound β n - 1 : ℕ) : ℝ) := by
    rw [show intervalStart β n + rowBound β n - 1 = intervalStart β n + (rowBound β n - 1) by omega,
      Nat.cast_add, Nat.cast_sub hR1, Nat.cast_one]
    linarith
  simp only [interval, mem_Icc]
  exact ⟨Nat.cast_le.mp hk_low, Nat.cast_le.mp hk_high⟩

/-- **Deterministic Binomial tail bound of Lemma 4.8**: once `1 ≤ β`, `2 ≤ r`, `32 ≤ R`, and
`6 R ≤ Q`, for every `1 ≤ b ≤ λ ^ β` the Binomial tail outside `interval β n` is strictly less than
`tailBudget b n = 1 / (b r² λ)`. -/
theorem binomTail_lt_tailBudget {β n b : ℕ} (hβ : 1 ≤ β) (hr : 2 ≤ numGroups n)
    (hR : 32 ≤ rowBound β n) (hRQ : 6 * rowBound β n ≤ numNodes n) (hb₁ : 1 ≤ b)
    (hb₂ : b ≤ Nat.clog 2 n ^ β) :
    binomTail β n < tailBudget b n := by
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  set r := numGroups n
  set Q := numNodes n
  set R := rowBound β n
  have hQ_pos : 0 < Q := by omega
  have hnu_pos : 1 ≤ nu := by
    rcases Nat.eq_zero_or_pos nu with hnu | hnu
    · have : Q = 0 := by simp only [Q, numNodes, lam, nu, hnu, mul_zero, Nat.div_zero]
      omega
    · omega
  have hlam_pos : 1 ≤ lam := by
    rcases Nat.eq_zero_or_pos lam with hlam | hlam
    · have : Q = 0 := by simp only [Q, numNodes, lam, hlam, Nat.zero_div]
      omega
    · omega
  have hp₀ : 0 ≤ binomProb n := by
    unfold binomProb
    have hr_real : (2 : ℝ) ≤ r := by exact_mod_cast hr
    exact div_nonneg (by linarith) (by positivity)
  have hp₁ : binomProb n ≤ 1 := by
    unfold binomProb
    have hr_real : (2 : ℝ) ≤ r := by exact_mod_cast hr
    rw [div_le_one (by positivity)]
    linarith
  have hhoeff : binomTail β n ≤ 2 * Real.exp (-2 * ((R : ℝ) / 4) ^ 2 / Q) :=
    sum_filter_notMem_choose_mul_pow_le Q (interval β n) hp₀ hp₁ (by positivity)
      fun k _ hk => mem_interval_of_abs_sub_le hr hR (by omega) hk
  have hR_sq : ((β : ℝ) + 3) ^ 2 * lam ≤ (R : ℝ) ^ 2 := by
    have hR_eq : R = (β + 3) * ⌈Real.sqrt lam⌉₊ := rowBound_eq_mul_ceil β n
    have hlam_sq : (lam : ℝ) ≤ (⌈Real.sqrt lam⌉₊ : ℝ) ^ 2 := by
      calc (lam : ℝ) = Real.sqrt lam ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg lam)).symm
        _ ≤ (⌈Real.sqrt lam⌉₊ : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) (Nat.le_ceil _) 2
    rw [hR_eq, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, mul_pow]
    exact mul_le_mul_of_nonneg_left hlam_sq (by positivity)
  have hQ_le : 128 * (nu : ℝ) * Q ≤ lam := by exact_mod_cast Nat.mul_div_le lam (128 * nu)
  have hexp_arg : 16 * ((β : ℝ) + 3) ^ 2 * nu ≤ 2 * ((R : ℝ) / 4) ^ 2 / Q := by
    have hQ_rpos : (0 : ℝ) < Q := by positivity
    rw [show 2 * ((R : ℝ) / 4) ^ 2 / Q = (R : ℝ) ^ 2 / (8 * Q) by ring,
      le_div_iff₀ (by positivity)]
    rw [show 16 * ((β : ℝ) + 3) ^ 2 * (nu : ℝ) * (8 * Q) =
      ((β : ℝ) + 3) ^ 2 * (128 * (nu : ℝ) * Q) by ring]
    exact (mul_le_mul_of_nonneg_left hQ_le (by positivity)).trans hR_sq
  have hexp_step : 2 * Real.exp (-2 * ((R : ℝ) / 4) ^ 2 / Q) ≤
      2 * Real.exp (-(16 * ((β : ℝ) + 3) ^ 2 * nu)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) zero_le_two
    rw [show -2 * ((R : ℝ) / 4) ^ 2 / (Q : ℝ) = -(2 * ((R : ℝ) / 4) ^ 2 / Q) by ring]
    linarith
  set m := (β + 2) * nu
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow_lt : 2 * (2 : ℝ) ^ m < Real.exp (16 * ((β : ℝ) + 3) ^ 2 * nu) := by
    calc 2 * (2 : ℝ) ^ m
        = (2 : ℝ) ^ (m + 1) := by rw [pow_succ']
      _ ≤ Real.exp 1 ^ (m + 1) := pow_le_pow_left₀ zero_le_two h2_le_exp1 (m + 1)
      _ = Real.exp ((m + 1 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ < Real.exp (16 * ((β : ℝ) + 3) ^ 2 * nu) := by
          refine Real.exp_lt_exp.mpr ?_
          have hnu_r : (1 : ℝ) ≤ nu := by exact_mod_cast hnu_pos
          have hsq : (β : ℝ) + 3 ≤ ((β : ℝ) + 3) ^ 2 := by
            have : (0 : ℝ) ≤ β := Nat.cast_nonneg β
            nlinarith
          have hstep : 16 * ((β : ℝ) + 3) * nu ≤ 16 * ((β : ℝ) + 3) ^ 2 * nu := by
            have hmul := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ 16 * nu by positivity)
            linarith
          have hβnu : (0 : ℝ) ≤ (β : ℝ) * nu := by positivity
          simp only [m, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          linarith
  have hexp_lt_pow : 2 * Real.exp (-(16 * ((β : ℝ) + 3) ^ 2 * nu)) < 1 / (2 : ℝ) ^ m := by
    rw [Real.exp_neg, lt_div_iff₀ (by positivity)]
    have hpos : 0 < Real.exp (16 * ((β : ℝ) + 3) ^ 2 * nu) := Real.exp_pos _
    have hmul := mul_lt_mul_of_pos_right hpow_lt (inv_pos.mpr hpos)
    rw [mul_inv_cancel₀ hpos.ne'] at hmul
    linarith
  have hdenom_nat : b * r ^ 2 * lam ≤ 2 ^ m := by
    have hr2_lam : r ^ 2 ≤ lam :=
      (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
    have hlam_pow : lam ≤ 2 ^ nu := Nat.le_pow_clog one_lt_two lam
    calc b * r ^ 2 * lam
        ≤ lam ^ β * lam * lam := Nat.mul_le_mul (Nat.mul_le_mul hb₂ hr2_lam) le_rfl
      _ = lam ^ (β + 2) := by ring
      _ ≤ (2 ^ nu) ^ (β + 2) := Nat.pow_le_pow_left hlam_pow (β + 2)
      _ = 2 ^ m := by rw [← pow_mul, mul_comm]
  have hpow_le_budget : 1 / (2 : ℝ) ^ m ≤ tailBudget b n :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hdenom_nat)
  exact (hhoeff.trans hexp_step).trans_lt (hexp_lt_pow.trans_le hpow_le_budget)

/-- **Deterministic row-cost bound (equation 4.18)**: whenever `2 ≤ r`, `32 ≤ R`, and `6 R ≤ Q`,
`rowCost β n` is bounded by `1028 (β + 3) ν² / √λ`. -/
theorem rowCost_le {β n : ℕ} (hr : 2 ≤ numGroups n) (hR : 32 ≤ rowBound β n)
    (hRQ : 6 * rowBound β n ≤ numNodes n) :
    rowCost β n ≤
      1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) := by
  unfold rowCost
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  set r := numGroups n
  set Q := numNodes n
  set R := rowBound β n
  set D := auxDim n
  have hQ_ge : 192 ≤ Q := by omega
  have hnu_pos : 1 ≤ nu := by
    rcases Nat.eq_zero_or_pos nu with hnu | hnu
    · have : Q = 0 := by simp only [Q, numNodes, lam, nu, hnu, mul_zero, Nat.div_zero]
      omega
    · omega
  have hlam_ge : 24576 ≤ lam := by
    have hmul : Q * (128 * nu) ≤ lam := Nat.div_mul_le_self lam (128 * nu)
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr (by positivity)
  have hlog2_le : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- Bound `1 / r ≤ 2 * ν² / √λ`.
  have hinv_r : 1 / (r : ℝ) ≤ 2 * (nu : ℝ) ^ 2 / Real.sqrt lam := by
    have hlt_sqrt : lam.sqrt + 1 ≤ 2 * r * nu ^ 2 := by
      have hdiv : nu ^ 2 * r + lam.sqrt % nu ^ 2 = lam.sqrt := Nat.div_add_mod lam.sqrt (nu ^ 2)
      have hmod := Nat.mod_lt lam.sqrt (show 0 < nu ^ 2 by positivity)
      have hr2 : nu ^ 2 * r + nu ^ 2 ≤ 2 * r * nu ^ 2 := by nlinarith
      omega
    have hsqrt_le : Real.sqrt lam ≤ 2 * (r : ℝ) * (nu : ℝ) ^ 2 := by
      have h1 : Real.sqrt lam ≤ (lam.sqrt + 1 : ℕ) := by
        rw [Real.sqrt_le_iff]
        exact ⟨by positivity, by exact_mod_cast (Nat.lt_succ_sqrt' lam).le⟩
      exact h1.trans (by exact_mod_cast hlt_sqrt)
    rw [div_le_div_iff₀ (by positivity) hsqrt_pos]
    linarith
  -- Bound `τ log(2 D + 1) ≤ 1 / r`.
  have htau_term : tau n * Real.log (2 * (D : ℝ) + 1) ≤ 2 * (nu : ℝ) ^ 2 / Real.sqrt lam := by
    have h2D_nat : 2 * D + 1 ≤ 2 ^ lam := by
      have hD : D ≤ 2 ^ (lam / 128) := auxDim_le_two_pow n
      have hexp : lam / 128 + 2 ≤ lam := by omega
      have h1 : 1 ≤ 2 ^ (lam / 128) := Nat.one_le_two_pow
      calc 2 * D + 1
          ≤ 4 * 2 ^ (lam / 128) := by omega
        _ = 2 ^ (lam / 128 + 2) := by rw [pow_add]; ring
        _ ≤ 2 ^ lam := Nat.pow_le_pow_right two_pos hexp
    have hlog_D : Real.log (2 * (D : ℝ) + 1) ≤ lam := by
      calc Real.log (2 * (D : ℝ) + 1)
          ≤ Real.log ((2 : ℝ) ^ lam) :=
            Real.log_le_log (by positivity) (by exact_mod_cast h2D_nat)
        _ = (lam : ℝ) * Real.log 2 := Real.log_pow 2 lam
        _ ≤ (lam : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg lam)
        _ = lam := mul_one _
    have htau_le : tau n * Real.log (2 * (D : ℝ) + 1) ≤ 1 / (r : ℝ) := by
      unfold tau
      have hlam_rpos : (0 : ℝ) < lam := by positivity
      have hr_rpos : (0 : ℝ) < r := by positivity
      calc 1 / ((r : ℝ) * lam) * Real.log (2 * (D : ℝ) + 1)
          ≤ 1 / ((r : ℝ) * lam) * lam :=
            mul_le_mul_of_nonneg_left hlog_D (by positivity)
        _ = 1 / r := by field_simp
    exact htau_le.trans hinv_r
  -- Bound `(R / Q) log(2 Q / R) ≤ 1024 (β + 3) ν² / √λ`.
  have hRQ_term : (R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R) ≤
      1024 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam := by
    have hR_upper : (R : ℝ) ≤ 2 * ((β : ℝ) + 3) * Real.sqrt lam := by
      have hlam_ne : lam ≠ 0 := by omega
      have hR_def : R = (β + 3) * ((lam - 1).sqrt + 1) := by
        simp only [R, rowBound, lam, hlam_ne, ↓reduceIte]
      have hs_le : ((lam - 1).sqrt : ℝ) ≤ Real.sqrt lam := by
        rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        exact_mod_cast (Nat.sqrt_le' (lam - 1)).trans (Nat.sub_le lam 1)
      have h1_le : (1 : ℝ) ≤ Real.sqrt lam := by
        rw [Real.le_sqrt zero_le_one (Nat.cast_nonneg _)]
        have : (1 : ℝ) ≤ lam := by exact_mod_cast (by omega : 1 ≤ lam)
        linarith
      rw [hR_def, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      nlinarith
    have hQ_lower : (lam : ℝ) ≤ 256 * (nu : ℝ) * Q := by
      have hlt : lam < (Q + 1) * (128 * nu) := by
        have hdiv : 128 * nu * Q + lam % (128 * nu) = lam := Nat.div_add_mod lam (128 * nu)
        have hmod := Nat.mod_lt lam (show 0 < 128 * nu by positivity)
        rw [add_mul, one_mul, mul_comm Q]
        omega
      have hle_nat : lam ≤ 256 * nu * Q := by nlinarith
      exact_mod_cast hle_nat
    have hratio : (R : ℝ) / Q ≤ 512 * ((β : ℝ) + 3) * nu / Real.sqrt lam := by
      rw [div_le_div_iff₀ (by positivity) hsqrt_pos]
      have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (Nat.cast_nonneg lam)
      calc (R : ℝ) * Real.sqrt lam
          ≤ 2 * ((β : ℝ) + 3) * Real.sqrt lam * Real.sqrt lam :=
            mul_le_mul_of_nonneg_right hR_upper hsqrt_pos.le
        _ = 2 * ((β : ℝ) + 3) * lam := by rw [mul_assoc, hsq]
        _ ≤ 2 * ((β : ℝ) + 3) * (256 * (nu : ℝ) * Q) :=
            mul_le_mul_of_nonneg_left hQ_lower (by positivity)
        _ = 512 * ((β : ℝ) + 3) * (nu : ℝ) * Q := by ring
    have hlog_Q : Real.log (2 * (Q : ℝ) / R) ≤ 2 * nu := by
      have hQR_le : 2 * (Q : ℝ) / R ≤ (2 : ℝ) ^ (2 * nu) := by
        have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (by omega : 1 ≤ R)
        have h2Q_nat : 2 * Q ≤ 2 ^ (2 * nu) := by
          calc 2 * Q ≤ 2 * 2 ^ nu :=
                Nat.mul_le_mul_left 2 ((Nat.div_le_self _ _).trans (Nat.le_pow_clog one_lt_two lam))
            _ = 2 ^ (nu + 1) := (pow_succ' 2 nu).symm
            _ ≤ 2 ^ (2 * nu) := Nat.pow_le_pow_right two_pos (by omega)
        calc 2 * (Q : ℝ) / R ≤ 2 * (Q : ℝ) / 1 :=
              div_le_div_of_nonneg_left (by positivity) one_pos hR1
          _ = ((2 * Q : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (2 : ℝ) ^ (2 * nu) := by exact_mod_cast h2Q_nat
      calc Real.log (2 * (Q : ℝ) / R)
          ≤ Real.log ((2 : ℝ) ^ (2 * nu)) :=
            Real.log_le_log (by positivity) hQR_le
        _ = (2 * nu : ℕ) * Real.log 2 := Real.log_pow 2 (2 * nu)
        _ ≤ (2 * nu : ℕ) * 1 := mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg _)
        _ = 2 * nu := by push_cast; ring
    have hlog_nonneg : 0 ≤ Real.log (2 * (Q : ℝ) / R) := by
      refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
      exact_mod_cast (by omega : R ≤ 2 * Q)
    calc (R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R)
        ≤ (512 * ((β : ℝ) + 3) * nu / Real.sqrt lam) * (2 * nu) :=
          mul_le_mul hratio hlog_Q hlog_nonneg (by positivity)
      _ = 1024 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam := by ring
  have h4 : 4 * (nu : ℝ) ^ 2 / Real.sqrt lam ≤
      4 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam := by
    refine div_le_div_of_nonneg_right ?_ hsqrt_pos.le
    have hβ_nn : (0 : ℝ) ≤ β := Nat.cast_nonneg β
    nlinarith [sq_nonneg (nu : ℝ)]
  calc (R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R) + tau n * Real.log (2 * (D : ℝ) + 1) + 1 / r
      ≤ 1024 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam +
          2 * (nu : ℝ) ^ 2 / Real.sqrt lam + 2 * (nu : ℝ) ^ 2 / Real.sqrt lam :=
        add_le_add (add_le_add hRQ_term htau_term) hinv_r
    _ = 1024 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam +
          4 * (nu : ℝ) ^ 2 / Real.sqrt lam := by ring
    _ ≤ 1024 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam +
          4 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam := add_le_add le_rfl h4
    _ = 1028 * ((β : ℝ) + 3) * (nu : ℝ) ^ 2 / Real.sqrt lam := by ring

/-! ### Asymptotics and Lemma 4.8 master theorem -/

private theorem clog_two_le_mul_log {m : ℕ} (hm : 3 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ 2 / Real.log 2 * Real.log m := by
  have hm1 : 1 < m := by omega
  have hcl_ge : 2 ≤ Nat.clog 2 m := by
    rw [← Nat.lt_iff_add_one_le, Nat.lt_clog_iff_pow_lt one_lt_two]
    omega
  have hpow : (2 : ℝ) ^ (Nat.clog 2 m - 1) ≤ m := by
    exact_mod_cast (Nat.pow_pred_clog_lt_self one_lt_two hm1).le
  have hlog : ((Nat.clog 2 m - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcl_cast : (Nat.clog 2 m : ℝ) ≤ 2 * ((Nat.clog 2 m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : Nat.clog 2 m ≤ 2 * (Nat.clog 2 m - 1))
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  nlinarith

private theorem tendsto_clog_atTop : Tendsto (Nat.clog 2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨2 ^ b, fun _ hn =>
    (Nat.clog_pow 2 b one_lt_two).symm.trans_le (Nat.clog_mono_right 2 hn)⟩

private theorem tendsto_clog_pow_div_sqrt (k : ℕ) :
    Tendsto (fun m : ℕ => (Nat.clog 2 m : ℝ) ^ k / Real.sqrt m) atTop (𝓝 0) := by
  have hbase : Tendsto (fun m : ℕ =>
      (2 / Real.log 2) ^ k * (Real.log (m : ℝ) ^ k / Real.sqrt m)) atTop (𝓝 0) := by
    have hl := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := (1 / 2 : ℝ))
      (by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    have hl' : Tendsto (fun m : ℕ => Real.log (m : ℝ) ^ k / Real.sqrt m) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using hl
    simpa only [mul_zero] using tendsto_const_nhds.mul hl'
  refine squeeze_zero' (Eventually.of_forall fun m => by positivity) ?_ hbase
  filter_upwards [eventually_ge_atTop 3] with m hm
  calc (Nat.clog 2 m : ℝ) ^ k / Real.sqrt m
      ≤ (2 / Real.log 2 * Real.log m) ^ k / Real.sqrt m :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (clog_two_le_mul_log hm) k)
          (Real.sqrt_nonneg _)
    _ = (2 / Real.log 2) ^ k * (Real.log (m : ℝ) ^ k / Real.sqrt m) := by
        rw [mul_pow, mul_div_assoc]

/-- Combined numerical guarantees of Lemma 4.7 and Lemma 4.8 for `(β, n, b, w, M)`. -/
structure Feasible (β n b w M : ℕ) : Prop where
  /-- Manuscript domain guard `20 ≤ n`. -/
  twenty_le : 20 ≤ n
  /-- At least two groups: `2 ≤ r`. -/
  two_le_numGroups : 2 ≤ numGroups n
  /-- Degree/interval lower bound `32 ≤ R`. -/
  thirtyTwo_le_rowBound : 32 ≤ rowBound β n
  /-- Block-length separation `6 R ≤ Q`. -/
  six_mul_rowBound_le_numNodes : 6 * rowBound β n ≤ numNodes n
  /-- Step size positivity `0 < τ`. -/
  tau_pos : 0 < tau n
  /-- Step size upper bound `τ ≤ 1 / 2`. -/
  tau_le_half : tau n ≤ 1 / 2
  /-- Auxiliary dimension power bound `D ≤ 2 ^ (λ / 128)`. -/
  auxDim_le : auxDim n ≤ 2 ^ (Nat.clog 2 n / 128)
  /-- First Lemma 4.7 balance inequality `2 (b + w) D² ≤ M`. -/
  aux_balance : 2 * (b + w) * auxDim n ^ 2 ≤ M
  /-- Second Lemma 4.7 balance inequality `2 Q r² ≤ n`. -/
  var_balance : 2 * numNodes n * numGroups n ^ 2 ≤ n
  /-- Exact interval cardinality `#I = R`. -/
  card_interval_eq : #(interval β n) = rowBound β n
  /-- Interval containment `I ⊆ {0, …, Q}`. -/
  interval_subset : interval β n ⊆ Finset.range (numNodes n + 1)
  /-- Concentration band `|k - μ| ≤ R / 4` lies in `I` and `{0, …, Q}`. -/
  mem_interval_of_close :
    ∀ k : ℕ, |(k : ℝ) - mean n| ≤ (rowBound β n : ℝ) / 4 → k ∈ interval β n ∧ k ≤ numNodes n
  /-- Strict Binomial tail bound `Pr[W ∉ I] < 1 / (b r² λ) = τ / (r b)`. -/
  binomTail_lt : binomTail β n < tailBudget b n
  /-- Counting-exponent bound (equation 4.18) `rowCost β n ≤ 1028 (β + 3) ν² / √λ`. -/
  rowCost_bound :
    rowCost β n ≤
      1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)

/-- Eventually in `n`, all `n`-only structural thresholds of Lemma 4.8 hold simultaneously. -/
private theorem eventually_thresholds {β : ℕ} (hβ : 1 ≤ β) :
    ∀ᶠ n : ℕ in atTop,
      20 ≤ n ∧ 2 ≤ numGroups n ∧ 32 ≤ rowBound β n ∧ 6 * rowBound β n ≤ numNodes n ∧
        4 * Nat.clog 2 n ^ β * 2 ^ (2 * (Nat.clog 2 n / 128)) ≤ n ∧
        2 * numNodes n * numGroups n ^ 2 ≤ n := by
  have ht2 := (tendsto_clog_pow_div_sqrt 2).comp tendsto_clog_atTop
  have ht1 := (tendsto_clog_pow_div_sqrt 1).comp tendsto_clog_atTop
  have hlam_ge := tendsto_clog_atTop.eventually (eventually_ge_atTop 256)
  have hev2 := ht2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hev1 := ht1.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 / (2048 * ((β : ℝ) + 3)) by positivity))
  filter_upwards [eventually_ge_atTop 20, hlam_ge, hev2, hev1] with n hn20 hlam h2 h1
  simp only [Function.comp_def, pow_one] at h2 h1
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr (by positivity)
  have hr : 2 ≤ numGroups n := by
    rw [div_lt_iff₀ hsqrt_pos] at h2
    have h4nu : 4 * (nu : ℝ) ^ 2 < Real.sqrt lam := by linarith
    have h3nu_sq : (3 * nu ^ 2 : ℕ) ^ 2 ≤ lam := by
      have hr_le : ((3 * nu ^ 2 : ℕ) : ℝ) ^ 2 ≤ (Real.sqrt lam) ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        push_cast
        nlinarith [sq_nonneg (nu : ℝ)]
      rw [Real.sq_sqrt (Nat.cast_nonneg lam)] at hr_le
      exact_mod_cast hr_le
    have hnu_pos : 0 < nu ^ 2 := by
      have : 1 ≤ nu := by
        rw [← Nat.lt_iff_add_one_le, Nat.lt_clog_iff_pow_lt one_lt_two]
        omega
      positivity
    unfold numGroups
    exact (by omega : 2 ≤ 3).trans ((Nat.le_div_iff_mul_le hnu_pos).mpr (Nat.le_sqrt'.mpr h3nu_sq))
  have hR : 32 ≤ rowBound β n := by
    unfold rowBound
    have hlam_ne : lam ≠ 0 := by omega
    simp only [lam, hlam_ne, ↓reduceIte]
    have hs : 15 ≤ (lam - 1).sqrt := Nat.le_sqrt.mpr (by omega)
    nlinarith
  have hnu_sqrt : 2048 * ((β : ℝ) + 3) * (nu : ℝ) * Real.sqrt lam < lam := by
    rw [div_lt_iff₀ hsqrt_pos] at h1
    have hmul := mul_lt_mul_of_pos_right h1 hsqrt_pos
    have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (Nat.cast_nonneg lam)
    have hrhs : 1 / (2048 * ((β : ℝ) + 3)) * Real.sqrt lam * Real.sqrt lam =
        (lam : ℝ) / (2048 * ((β : ℝ) + 3)) := by
      rw [mul_assoc, hsq]
      ring
    rw [hrhs, lt_div_iff₀ (by positivity)] at hmul
    linarith
  have hRQ : 6 * rowBound β n ≤ numNodes n := by
    have hnu_pos : 0 < 128 * nu := by
      have : 1 ≤ nu := by
        rw [← Nat.lt_iff_add_one_le, Nat.lt_clog_iff_pow_lt one_lt_two]
        omega
      positivity
    unfold numNodes
    rw [Nat.le_div_iff_mul_le hnu_pos]
    have hR_le : (rowBound β n : ℝ) ≤ 2 * ((β : ℝ) + 3) * Real.sqrt lam := by
      unfold rowBound
      have hlam_ne : lam ≠ 0 := by omega
      simp only [lam, hlam_ne, ↓reduceIte, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one]
      have hs : ((lam - 1).sqrt : ℝ) ≤ Real.sqrt lam := by
        rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        exact_mod_cast (Nat.sqrt_le' (lam - 1)).trans (Nat.sub_le lam 1)
      have h1_sqrt : (1 : ℝ) ≤ Real.sqrt lam := by
        rw [Real.le_sqrt zero_le_one (Nat.cast_nonneg _)]
        have : (1 : ℝ) ≤ lam := by exact_mod_cast (by omega : 1 ≤ lam)
        linarith
      nlinarith
    have hprod_r : ((6 * rowBound β n * (128 * nu) : ℕ) : ℝ) ≤ lam := by
      push_cast
      calc 6 * (rowBound β n : ℝ) * (128 * (nu : ℝ))
          ≤ 6 * (2 * ((β : ℝ) + 3) * Real.sqrt lam) * (128 * (nu : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR_le (by norm_num))
              (by positivity)
        _ = 1536 * ((β : ℝ) + 3) * (nu : ℝ) * Real.sqrt lam := by ring
        _ ≤ 2048 * ((β : ℝ) + 3) * (nu : ℝ) * Real.sqrt lam := by
            nlinarith [Real.sqrt_nonneg lam]
        _ ≤ lam := hnu_sqrt.le
    exact_mod_cast hprod_r
  have h2pow_n : 2 ^ (lam - 1) ≤ n := (Nat.pow_pred_clog_lt_self one_lt_two (by omega)).le
  have hβnu_le : β * nu ≤ lam / 4 := by
    have hsqrt_ge : (16 : ℝ) ≤ Real.sqrt lam := by
      rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
      have : (256 : ℝ) ≤ lam := by exact_mod_cast hlam
      linarith
    have h_r : ((β * nu : ℕ) : ℝ) * 4 ≤ lam := by
      push_cast
      nlinarith [Real.sqrt_nonneg lam]
    have h_nat : (β * nu) * 4 ≤ lam := by exact_mod_cast h_r
    omega
  have hnu_le : nu ≤ lam / 4 := (Nat.le_mul_of_pos_left nu hβ).trans hβnu_le
  have hbal1 : 4 * lam ^ β * 2 ^ (2 * (lam / 128)) ≤ n := by
    have hlam_pow : lam ≤ 2 ^ nu := Nat.le_pow_clog one_lt_two lam
    calc 4 * lam ^ β * 2 ^ (2 * (lam / 128))
        ≤ 2 ^ 2 * (2 ^ nu) ^ β * 2 ^ (2 * (lam / 128)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hlam_pow β))
      _ = 2 ^ (2 + nu * β + 2 * (lam / 128)) := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ (lam - 1) := by
          refine Nat.pow_le_pow_right two_pos ?_
          have : nu * β = β * nu := mul_comm nu β
          omega
      _ ≤ n := h2pow_n
  have hbal2 : 2 * numNodes n * numGroups n ^ 2 ≤ n := by
    have hQ_lam : numNodes n ≤ lam := Nat.div_le_self _ _
    have hr2_lam : numGroups n ^ 2 ≤ lam :=
      (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2).trans (Nat.sqrt_le' lam)
    have hlam_pow : lam ≤ 2 ^ nu := Nat.le_pow_clog one_lt_two lam
    calc 2 * numNodes n * numGroups n ^ 2
        ≤ 2 ^ 1 * 2 ^ nu * 2 ^ nu :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hQ_lam.trans hlam_pow)) (hr2_lam.trans hlam_pow)
      _ = 2 ^ (1 + nu + nu) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (lam - 1) := Nat.pow_le_pow_right two_pos (by omega)
      _ ≤ n := h2pow_n
  exact ⟨hn20, hr, hR, hRQ, hbal1, hbal2⟩

/-- **Lemma 4.8 of `[OpenAI2026ETH]`**: for every integer `1 ≤ β`, there exists `n₀ ≥ 20` such that
for all `n ≥ n₀`, `1 ≤ b ≤ λ ^ β`, `1 ≤ w ≤ λ ^ β`, and `n ≤ M ≤ b n`, the schedule (4.17)
satisfies every numerical requirement of Lemma 4.7 and Lemma 4.8. -/
theorem exists_feasible {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧ ∀ ⦃n b w M : ℕ⦄, n₀ ≤ n →
      1 ≤ b → b ≤ Nat.clog 2 n ^ β →
      1 ≤ w → w ≤ Nat.clog 2 n ^ β →
      n ≤ M → M ≤ b * n → Feasible β n b w M := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (eventually_thresholds hβ)
  refine ⟨max n₀ 20, le_max_right _ _, fun {n b w M} hn hb₁ hb₂ hw₁ hw₂ hnM _hMbn => ?_⟩
  obtain ⟨h20, hr, hR, hRQ, hbal1, hbal2⟩ := hn₀ n ((le_max_left _ _).trans hn)
  have hlam_pos : 1 ≤ Nat.clog 2 n := by
    rw [← Nat.lt_iff_add_one_le, Nat.lt_clog_iff_pow_lt one_lt_two]
    omega
  have htau_pos : 0 < tau n := by
    unfold tau
    positivity
  have htau_le : tau n ≤ 1 / 2 := by
    unfold tau
    have hprod : (2 : ℝ) ≤ (numGroups n : ℝ) * Nat.clog 2 n := by
      exact_mod_cast (by nlinarith : 2 ≤ numGroups n * Nat.clog 2 n)
    exact one_div_le_one_div_of_le zero_lt_two hprod
  have haux_bal : 2 * (b + w) * auxDim n ^ 2 ≤ M := by
    have hbw : 2 * (b + w) ≤ 4 * Nat.clog 2 n ^ β := by omega
    have hD2 : auxDim n ^ 2 ≤ 2 ^ (2 * (Nat.clog 2 n / 128)) := by
      calc auxDim n ^ 2 ≤ (2 ^ (Nat.clog 2 n / 128)) ^ 2 :=
            Nat.pow_le_pow_left (auxDim_le_two_pow n) 2
        _ = 2 ^ (2 * (Nat.clog 2 n / 128)) := by rw [← pow_mul, mul_comm]
    exact (Nat.mul_le_mul hbw hD2).trans (hbal1.trans hnM)
  have hsub := interval_subset_range (β := β) hr (by omega) (by omega)
  refine
    { twenty_le := h20
      two_le_numGroups := hr
      thirtyTwo_le_rowBound := hR
      six_mul_rowBound_le_numNodes := hRQ
      tau_pos := htau_pos
      tau_le_half := htau_le
      auxDim_le := auxDim_le_two_pow n
      aux_balance := haux_bal
      var_balance := hbal2
      card_interval_eq := card_interval (by omega)
      interval_subset := hsub
      mem_interval_of_close := fun k hk => by
        have hmem := mem_interval_of_abs_sub_le hr hR (by omega) hk
        exact ⟨hmem, Nat.lt_succ_iff.mp (mem_range.mp (hsub hmem))⟩
      binomTail_lt := binomTail_lt_tailBudget hβ hr hR hRQ hb₁ hb₂
      rowCost_bound := rowCost_le hr hR hRQ }

/-- Constant-occurrence specialization of `exists_feasible` for `1 ≤ b, w ≤ β`. -/
theorem exists_feasible_of_le_const {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧ ∀ ⦃n b w M : ℕ⦄, n₀ ≤ n →
      1 ≤ b → b ≤ β → 1 ≤ w → w ≤ β →
      n ≤ M → M ≤ b * n → Feasible β n b w M := by
  obtain ⟨n₀, hn₀20, hfeas⟩ := exists_feasible hβ
  refine ⟨n₀, hn₀20, fun {n b w M} hn hb₁ hb₂ hw₁ hw₂ hnM hMbn => ?_⟩
  have h2_le_lam : 2 ≤ Nat.clog 2 n :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  have hβ_le_pow : β ≤ Nat.clog 2 n ^ β :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h2_le_lam β)
  exact hfeas hn hb₁ (hb₂.trans hβ_le_pow) hw₁ (hw₂.trans hβ_le_pow) hnM hMbn

/-- Equation (4.18) in `IsBigO` form: `rowCost β = O(ν² / √λ)`. -/
theorem isBigO_rowCost {β : ℕ} (hβ : 1 ≤ β) :
    rowCost β =O[atTop] fun n : ℕ =>
      (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) := by
  refine IsBigO.of_bound (1028 * ((β : ℝ) + 3)) ?_
  filter_upwards [eventually_thresholds hβ] with n ⟨_, hr, hR, hRQ, _, _⟩
  have hpos_r : (0 : ℝ) < numGroups n := by positivity
  have hpos_Q : (0 : ℝ) < numNodes n := Nat.cast_pos.mpr (by omega)
  have hnonneg : 0 ≤ rowCost β n := by
    unfold rowCost tau
    have hlog1 : 0 ≤ Real.log (2 * (numNodes n : ℝ) / rowBound β n) := by
      refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
      exact_mod_cast (by omega : rowBound β n ≤ 2 * numNodes n)
    have hlog2 : 0 ≤ Real.log (2 * (auxDim n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (auxDim n) : (0 : ℝ) ≤ auxDim n)])
    positivity
  have hnonneg_rhs : 0 ≤ (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n) := by
    positivity
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg hnonneg_rhs, ← mul_div_assoc]
  exact rowCost_le hr hR hRQ

/-- The counting-cost factor `rowCost β n` tends to `0` as `n → ∞`. -/
theorem tendsto_rowCost {β : ℕ} (hβ : 1 ≤ β) :
    Tendsto (rowCost β) atTop (𝓝 0) :=
  (isBigO_rowCost hβ).trans_tendsto ((tendsto_clog_pow_div_sqrt 2).comp tendsto_clog_atTop)

/-- `rowCost β` is `o(1)` as `n → ∞`. -/
theorem isLittleO_rowCost_one {β : ℕ} (hβ : 1 ≤ β) :
    rowCost β =o[atTop] fun _ : ℕ => (1 : ℝ) :=
  (isLittleO_one_iff ℝ).mpr (tendsto_rowCost hβ)

/-- `n * rowCost β n` is `O(interpolationScale n)`, linking Lemma 4.8 directly to the counting
scale of `CountingScale.lean`. -/
theorem isBigO_mul_rowCost_interpolationScale {β : ℕ} (hβ : 1 ≤ β) :
    (fun n : ℕ => (n : ℝ) * rowCost β n) =O[atTop] interpolationScale := by
  have hscale : (fun n : ℕ =>
      (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 n)) =O[atTop]
      fun n : ℕ => Real.log (Real.log ((n : ℝ) + 16)) ^ 2 /
        Real.sqrt (Real.log ((n : ℝ) + 16)) := by
    have hll_tendsto : Tendsto (fun n : ℕ => Real.log (Real.log ((n : ℝ) + 16))) atTop atTop :=
      Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <|
        tendsto_atTop_add_const_right atTop (16 : ℝ) tendsto_natCast_atTop_atTop
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set K : ℝ := 2 / Real.log 2 * (Real.log (2 / Real.log 2) + 1)
    refine IsBigO.of_bound (K ^ 2 * Real.sqrt 2) ?_
    filter_upwards [eventually_ge_atTop 16, hll_tendsto.eventually (eventually_ge_atTop 1),
        tendsto_clog_atTop.eventually (eventually_ge_atTop 3)] with n hn16 hll1 hlam3
    set L := Real.log ((n : ℝ) + 16)
    set LL := Real.log L
    set lam := Nat.clog 2 n
    set nu := Nat.clog 2 lam
    have hL_pos : 0 < L := Real.log_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hlog2_le : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hL_le_2lam : L ≤ 2 * (lam : ℝ) := by
      have hn_pow : (n : ℝ) + 16 ≤ (2 : ℝ) ^ (2 * lam) := by
        have hlam_pow : n ≤ 2 ^ lam := Nat.le_pow_clog one_lt_two n
        have hn2 : n + 16 ≤ n ^ 2 := by nlinarith
        have hnat : n + 16 ≤ 2 ^ (2 * lam) := by
          calc n + 16 ≤ n ^ 2 := hn2
            _ ≤ (2 ^ lam) ^ 2 := Nat.pow_le_pow_left hlam_pow 2
            _ = 2 ^ (2 * lam) := by rw [← pow_mul, mul_comm]
        exact_mod_cast hnat
      calc L ≤ Real.log ((2 : ℝ) ^ (2 * lam)) := Real.log_le_log (by positivity) hn_pow
        _ = (2 * lam : ℕ) * Real.log 2 := Real.log_pow 2 (2 * lam)
        _ ≤ (2 * lam : ℕ) * 1 := mul_le_mul_of_nonneg_left hlog2_le (Nat.cast_nonneg _)
        _ = 2 * lam := by push_cast; ring
    have hnu_le : (nu : ℝ) ≤ K * LL := by
      have hlam_le_L : (lam : ℝ) ≤ 2 / Real.log 2 * L :=
        (clog_two_le_mul_log (by omega)).trans <|
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (by positivity) (by linarith)) (by positivity)
      have hlog_lam : Real.log (lam : ℝ) ≤ (Real.log (2 / Real.log 2) + 1) * LL := by
        calc Real.log (lam : ℝ)
            ≤ Real.log (2 / Real.log 2 * L) := Real.log_le_log (by positivity) hlam_le_L
          _ = Real.log (2 / Real.log 2) + LL := Real.log_mul (by positivity) hL_pos.ne'
          _ ≤ Real.log (2 / Real.log 2) * LL + LL := by
              have hpos_c : 0 ≤ Real.log (2 / Real.log 2) :=
                Real.log_nonneg ((one_le_div hlog2).mpr (by linarith))
              nlinarith
          _ = (Real.log (2 / Real.log 2) + 1) * LL := by ring
      calc (nu : ℝ) ≤ 2 / Real.log 2 * Real.log lam := clog_two_le_mul_log hlam3
        _ ≤ 2 / Real.log 2 * ((Real.log (2 / Real.log 2) + 1) * LL) :=
            mul_le_mul_of_nonneg_left hlog_lam (by positivity)
        _ = K * LL := by ring
    have hsqrt_inv : 1 / Real.sqrt lam ≤ Real.sqrt 2 / Real.sqrt L := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hL_pos), one_mul,
        ← Real.sqrt_mul zero_le_two]
      exact Real.sqrt_le_sqrt hL_le_2lam
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc (nu : ℝ) ^ 2 / Real.sqrt lam
        = (nu : ℝ) ^ 2 * (1 / Real.sqrt lam) := div_eq_mul_one_div _ _
      _ ≤ (K * LL) ^ 2 * (Real.sqrt 2 / Real.sqrt L) :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hnu_le 2) hsqrt_inv
            (by positivity) (by positivity)
      _ = K ^ 2 * Real.sqrt 2 * (LL ^ 2 / Real.sqrt L) := by ring
  have hmul := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul ((isBigO_rowCost hβ).trans hscale)
  unfold interpolationScale
  simpa only [mul_div_assoc] using hmul

/-- Multiplying `rowCost β n` by `n` gives a sublinear counting exponent `o(n)`. -/
theorem isLittleO_mul_rowCost {β : ℕ} (hβ : 1 ≤ β) :
    (fun n : ℕ => (n : ℝ) * rowCost β n) =o[atTop] fun n : ℕ => (n : ℝ) :=
  (isBigO_mul_rowCost_interpolationScale hβ).trans_isLittleO isLittleO_interpolationScale

end ReplacementParams

end Cslib.Complexity.SubexponentialSAT
