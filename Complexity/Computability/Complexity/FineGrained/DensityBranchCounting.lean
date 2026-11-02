/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingScale
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Computability.Complexity.FineGrained.ContractionCounting
import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
import Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# One model counter with both bounds of Theorem 1.1

For every fixed clause width `k`, one machine computes the number of satisfying assignments
`CNF.modelCount φ` of every formula `φ` whose clauses have at most `k` literals, in polynomial
space, with a single time function `T` that satisfies three bounds at once
(`DensityBranchCounting.exists_modelCounter`). Write `n` for the number of variables, `m` for
the number of clauses, `L` for the encoding length and `ν = ⌈log₂ ⌈log₂ n⌉⌉`.

* On every formula, `T` is `2 ^ O_k(ρ(n))` times a polynomial in `L`, where `ρ` is the
  interpolation scale `n (log log n)² / √log n` of Section 6.4 of [OpenAI2026ETH].
* On formulas with `m ≤ n ν`, it is `2 ^ O_k(n ν / √log n)` times a polynomial.
* For each density `D`, on formulas with `m ≤ D n` it is `2 ^ O_{k,D}(n / √log n)` times a
  polynomial. Only the constant in the exponent depends on `D`; the machine, `T` and the degree
  of the polynomial do not.

The machine is the single algorithm in the last paragraph of Appendix D.3 of [OpenAI2026ETH]
(p. 57): it tests `m ≤ n ν` (`DensityBranchCounting.threshold`), runs the tensor-contraction
counter `ContractionCounting.exists_modelCounter` when the test passes, and otherwise runs a dense
counter. In the paper the dense branch is the parity-query proof of the arbitrary-density bound
(p. 57), with exponent `O_k(n log log n / √log n)`. It evaluates its queries by Lemma D.2
(pp. 54–56), which applies Theorem D.1 with truncation order `ℓ = n + 1`. That is not formalized,
so the dense branch here is the Section 6.4 counter `CountingNativeEndpoint.exists_modelCounter`,
and the bound on every formula stays at the interpolation scale `ρ(n)`. The arbitrary-density
bound of Theorem 1.1 remains open.

As in the two counters it combines, `n` is the number of variables occurring in `φ`
(`CNF.numVars`); the paper counts declared variables, with `n ≥ 20`.

## Main definitions

* `Cslib.Complexity.DensityBranchCounting.threshold`: the clause-count threshold `n ν`.

## Main results

* `Cslib.Complexity.DensityBranchCounting.exists_modelCounter`: the counter and its three bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem 1.1 (p. 2) and
  the last paragraph of Appendix D.3 (p. 57).
-/

public section

namespace Cslib.Complexity.DensityBranchCounting

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- The clause-count threshold of the single algorithm, `n ⌈log₂ ⌈log₂ n⌉⌉` for `n` variables.
Formulas with at most this many clauses are counted by tensor contraction. -/
@[expose] def threshold (n : ℕ) : ℕ := n * Nat.clog 2 (Nat.clog 2 n)

/-- The test of the single algorithm: at most `threshold n` clauses. -/
private def guard (φ : CNF ℕ) : Bool := decide (φ.length ≤ threshold φ.numVars)

private theorem computableInPolyTime_guard : ComputableInPolyTime guard encCNF encBool := by
  unfold guard threshold
  fun_prop

/-! ### Arithmetic of the exponents -/

/-- The divisor `√⌊log₂ (n + 2)⌋` of the contraction exponent is positive. -/
private theorem one_le_sqrt_log (n : ℕ) : 1 ≤ Nat.sqrt (Nat.log 2 (n + 2)) :=
  Nat.le_sqrt.mpr (by have := Nat.log_pos (b := 2) (n := n + 2) (by norm_num) (by omega); omega)

/-- For a positive number of variables, the divisor `√⌊log₂ (n + 2)⌋` is at most `n`. -/
private theorem sqrt_log_le {n : ℕ} (hn : 1 ≤ n) : Nat.sqrt (Nat.log 2 (n + 2)) ≤ n := by
  refine (Nat.sqrt_le_self _).trans (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) ?_))
  have := Nat.lt_two_pow_self (n := n)
  rw [Nat.pow_succ]
  omega

/-- Below `16384` variables the threshold is at most `65536`. -/
private theorem threshold_le_of_lt {n : ℕ} (hn : n < 16384) : threshold n ≤ 65536 := by
  have h14 : Nat.clog 2 n ≤ 14 :=
    Nat.clog_le_of_le_pow (by norm_num; omega)
  have h4 : Nat.clog 2 (Nat.clog 2 n) ≤ 4 :=
    Nat.clog_le_of_le_pow (by norm_num; omega)
  unfold threshold
  nlinarith

/-- Above `2 ^ 2 ^ D` variables the threshold is at least `D n`. -/
private theorem mul_le_threshold {D n : ℕ} (hn : 2 ^ 2 ^ D ≤ n) : D * n ≤ threshold n := by
  have h1 : 2 ^ D ≤ Nat.clog 2 n := by
    simpa only [Nat.clog_pow 2 _ one_lt_two] using Nat.clog_mono_right 2 hn
  have h2 : D ≤ Nat.clog 2 (Nat.clog 2 n) := by
    simpa only [Nat.clog_pow 2 _ one_lt_two] using Nat.clog_mono_right 2 h1
  unfold threshold
  rw [Nat.mul_comm D n]
  exact Nat.mul_le_mul_left n h2

/-- **The contraction exponent at the threshold is at most the interpolation scale**, up to the
factor `32`, from `16384` variables on: `n ν / √⌊log₂ (n + 2)⌋ ≤ 32 ρ(n)`. -/
private theorem threshold_div_le_interpolationScale {n : ℕ} (hn : 16384 ≤ n) :
    (threshold n : ℝ) / Nat.sqrt (Nat.log 2 (n + 2)) ≤ 32 * interpolationScale n := by
  have hmain := ReplacementParams.mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale hn
  set lam := Nat.clog 2 n
  set nu := Nat.clog 2 lam
  set q := Nat.sqrt (Nat.log 2 (n + 2))
  have hlam : 14 ≤ lam := by
    simpa only [show (16384 : ℕ) = 2 ^ 14 by norm_num, Nat.clog_pow 2 _ one_lt_two] using
      Nat.clog_mono_right 2 hn
  have hnu : 1 ≤ nu := by
    simpa only [Nat.clog_pow 2 1 one_lt_two] using Nat.clog_mono_right 2 (by omega : 2 ^ 1 ≤ lam)
  have hq : 1 ≤ q := one_le_sqrt_log n
  -- `λ ≤ ⌊log₂ (n + 2)⌋ + 1 < (q + 1) ^ 2 + 1 ≤ (2 q) ^ 2 + 1`
  have hlamq : lam ≤ (2 * q) ^ 2 := by
    have h1 : lam ≤ Nat.log 2 (n + 2) + 1 := Nat.clog_le_of_le_pow
      (by have := Nat.lt_pow_succ_log_self (b := 2) one_lt_two (n + 2); omega)
    have h2 := Nat.lt_succ_sqrt' (Nat.log 2 (n + 2))
    change Nat.log 2 (n + 2) < (q + 1) ^ 2 at h2
    nlinarith
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlamR : (0 : ℝ) < Real.sqrt lam :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsqrt : Real.sqrt lam ≤ 2 * q := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by exact_mod_cast hlamq⟩
  have hnuR : (nu : ℝ) ≤ (nu : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ nu := Nat.one_le_cast.mpr hnu
    nlinarith
  have hstep : (threshold n : ℝ) / q ≤ 2 * ((n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt lam) := by
    rw [div_le_iff₀ hqR, show 2 * ((n : ℝ) * (nu : ℝ) ^ 2 / Real.sqrt lam) * q =
      (n : ℝ) * (nu : ℝ) ^ 2 * (2 * q) / Real.sqrt lam by ring, le_div_iff₀ hlamR]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnu0 : (0 : ℝ) ≤ nu := Nat.cast_nonneg nu
    calc (threshold n : ℝ) * Real.sqrt lam = (n : ℝ) * nu * Real.sqrt lam := by
          simp only [threshold, Nat.cast_mul, nu, lam]
      _ ≤ (n : ℝ) * nu * (2 * q) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ (n : ℝ) * (nu : ℝ) ^ 2 * (2 * q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnuR hn0) (by positivity)
  linarith

/-- The length of a formula's encoding is at least its number of clauses. -/
private theorem length_le_length_encCNF (φ : CNF ℕ) : φ.length ≤ (encCNF φ).length :=
  length_le_length_encList _ φ

/-- `2 ^ (A m / √⌊log₂ (n + 2)⌋)` on formulas with at most `threshold n` clauses is at most
`2 ^ O(ρ(n))` times a polynomial in the encoding length: the contraction branch obeys the
interpolation-scale bound. -/
private theorem two_pow_le_of_le_threshold (A₁ : ℕ) {φ : CNF ℕ}
    (hφ : φ.length ≤ threshold φ.numVars) :
    2 ^ (A₁ * φ.length / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) ≤
      ⌈(2 : ℝ) ^ (((32 * A₁ : ℕ) : ℝ) * interpolationScale φ.numVars)⌉₊ *
        ((encCNF φ).length + 1) ^ (65536 * A₁) := by
  set E := A₁ * φ.length / Nat.sqrt (Nat.log 2 (φ.numVars + 2))
  set X := (2 : ℝ) ^ (((32 * A₁ : ℕ) : ℝ) * interpolationScale φ.numVars)
  set Y := (encCNF φ).length + 1
  have hX : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  have hY : 1 ≤ Y := Nat.le_add_left 1 _
  rcases Nat.lt_or_ge φ.numVars 16384 with hn | hn
  · -- few variables: the exponent is bounded, and charged to the encoding length
    have hE : E ≤ 65536 * A₁ :=
      (Nat.div_le_self _ _).trans (by have := threshold_le_of_lt hn; nlinarith)
    have h2Y : 2 ^ E ≤ Y ^ E := by
      rcases Nat.eq_zero_or_pos φ.length with h0 | h0
      · simp only [E, h0, Nat.mul_zero, Nat.zero_div, pow_zero, le_refl]
      · exact Nat.pow_le_pow_left (by have := length_le_length_encCNF φ; omega) E
    calc 2 ^ E ≤ Y ^ E := h2Y
      _ ≤ Y ^ (65536 * A₁) := Nat.pow_le_pow_right hY hE
      _ ≤ ⌈X⌉₊ * Y ^ (65536 * A₁) := Nat.le_mul_of_pos_left _ hX
  · -- many variables: the exponent is at most `32 ρ(n)`
    have hscale := threshold_div_le_interpolationScale hn
    have hER : (E : ℝ) ≤ ((32 * A₁ : ℕ) : ℝ) * interpolationScale φ.numVars := by
      refine Nat.cast_div_le.trans ?_
      have hq : (0 : ℝ) < Nat.sqrt (Nat.log 2 (φ.numVars + 2)) :=
        Nat.cast_pos.mpr (one_le_sqrt_log _)
      have hm : (φ.length : ℝ) ≤ threshold φ.numVars := by exact_mod_cast hφ
      calc ((A₁ * φ.length : ℕ) : ℝ) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))
          ≤ A₁ * ((threshold φ.numVars : ℝ) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) := by
            rw [Nat.cast_mul, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm hq.le)
              (Nat.cast_nonneg _)
        _ ≤ A₁ * (32 * interpolationScale φ.numVars) :=
            mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
        _ = ((32 * A₁ : ℕ) : ℝ) * interpolationScale φ.numVars := by push_cast; ring
    have h2E : ((2 ^ E : ℕ) : ℝ) ≤ ⌈X⌉₊ := by
      calc ((2 ^ E : ℕ) : ℝ) = (2 : ℝ) ^ (E : ℝ) := by
            rw [Real.rpow_natCast]; push_cast; rfl
        _ ≤ X := Real.rpow_le_rpow_of_exponent_le (by norm_num) hER
        _ ≤ ⌈X⌉₊ := Nat.le_ceil X
    calc 2 ^ E ≤ ⌈X⌉₊ := by exact_mod_cast h2E
      _ ≤ ⌈X⌉₊ * Y ^ (65536 * A₁) := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY)

/-! ### The counter -/

/-- The contraction counter of `ContractionCounting.exists_modelCounter`, with the exponent
`A m / √⌊log₂ (n + 2)⌋` in place of `A (m + 1) / √⌊log₂ (n + 2)⌋`. -/
private theorem exists_contractionCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => 2 ^ (A * φ.length / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := ContractionCounting.exists_modelCounter k
  refine ⟨count, A, e, b, hcount, hc.mono (2 ^ A) (fun φ => ?_) (fun φ => ?_)⟩
  · set s := Nat.sqrt (Nat.log 2 (φ.numVars + 2))
    have hs : 0 < s := one_le_sqrt_log _
    have hdiv : A * (φ.length + 1) / s ≤ A * φ.length / s + A := by
      calc A * (φ.length + 1) / s ≤ (A * φ.length + s * A) / s :=
            Nat.div_le_div_right (by rw [Nat.mul_succ]; nlinarith)
        _ = A * φ.length / s + A := Nat.add_mul_div_left _ _ hs
    calc 2 ^ (A * (φ.length + 1) / s) * ((encCNF φ).length + 1) ^ e
        ≤ 2 ^ (A * φ.length / s + A) * ((encCNF φ).length + 1) ^ e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hdiv)
      _ = 2 ^ A * (2 ^ (A * φ.length / s) * ((encCNF φ).length + 1) ^ e) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · exact (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos A)).trans
      (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- **One model counter with both bounds of Theorem 1.1.** For each clause width `k`, one machine
computes `φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in
polynomial space, and its time function `T` satisfies, for `n` variables, `m` clauses and
encoding length `L`:

* on every formula, `T φ ≤ ⌈2 ^ (A ρ(n))⌉ (L + 1) ^ e`, where `ρ = interpolationScale`;
* when `m ≤ threshold n = n ⌈log₂ ⌈log₂ n⌉⌉`,
  `T φ ≤ 2 ^ (A · threshold n / √⌊log₂ (n + 2)⌋) (L + 1) ^ e`;
* for each density bound `D`, when `m ≤ D n`, `T φ ≤ 2 ^ (A' n / √⌊log₂ (n + 2)⌋) (L + 1) ^ e`
  for a constant `A'` depending on `D`.

The machine, `T`, `S` and the constants `A`, `e`, `b` are fixed before `D`; only `A'` depends on
`D`. -/
theorem exists_modelCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (T S : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat T S ∧
      (∀ φ, S φ = ((encCNF φ).length + 1) ^ b) ∧
      (∀ φ, T φ ≤ ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
        ((encCNF φ).length + 1) ^ e) ∧
      (∀ φ : CNF ℕ, φ.length ≤ threshold φ.numVars →
        T φ ≤ 2 ^ (A * threshold φ.numVars / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e) ∧
      ∀ D : ℕ, ∃ A' : ℕ, ∀ φ : CNF ℕ, φ.length ≤ D * φ.numVars →
        T φ ≤ 2 ^ (A' * φ.numVars / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e := by
  obtain ⟨count₁, A₁, e₁, b₁, hcount₁, hc₁⟩ := exists_contractionCounter k
  obtain ⟨count₂, A₂, e₂, b₂, hcount₂, hc₂⟩ := CountingNativeEndpoint.exists_modelCounter k
  obtain ⟨d, _, hd⟩ := computableInPolyTime_guard.exists_degree
  -- `e₀` is the polynomial degree of `T`; `e` absorbs the contraction branch on few variables
  set e₀ := d + e₁ + e₂ with he₀
  set A := 32 * A₁ + A₂ with hA
  set e := e₀ + 65536 * A₁ with he
  set b := d + b₁ + b₂ with hb
  set q : CNF ℕ → ℕ := fun φ => Nat.sqrt (Nat.log 2 (φ.numVars + 2)) with hq
  set Y : CNF ℕ → ℕ := fun φ => (encCNF φ).length + 1 with hY
  set T : CNF ℕ → ℕ := fun φ => if guard φ then 2 ^ (A₁ * φ.length / q φ) * Y φ ^ e₀
    else ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ e₀ with hT
  have hY1 (φ : CNF ℕ) : 1 ≤ Y φ := Nat.le_add_left 1 _
  have hYe (φ : CNF ℕ) : Y φ ^ e₀ ≤ Y φ ^ e := Nat.pow_le_pow_right (hY1 φ) (by omega)
  have hT1 (φ : CNF ℕ) : Y φ ^ e₀ ≤ T φ := by
    simp only [T]
    split
    · exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    · exact Nat.le_mul_of_pos_left _
        (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  refine ⟨fun φ => if guard φ then count₁ φ else count₂ φ, T, fun φ => Y φ ^ b, A, e, b,
    fun φ hφ => ?_, (hd.inO.ite hc₁ hc₂).mono 2 (fun φ => ?_) (fun φ => ?_), fun _ => rfl,
    fun φ => ?_, fun φ hφ => ?_, fun D => ?_⟩
  · -- correctness: both branches count models
    dsimp only
    split
    · exact hcount₁ φ hφ
    · exact hcount₂ φ hφ
  · -- time: the test and either branch are within `T`
    have hd' : Y φ ^ d ≤ T φ := (Nat.pow_le_pow_right (hY1 φ) (by omega)).trans (hT1 φ)
    have hbr : (if guard φ then 2 ^ (A₁ * φ.length / q φ) * Y φ ^ e₁
        else ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ e₂) ≤ T φ := by
      simp only [T]
      split
      · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (hY1 φ) (by omega))
      · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (hY1 φ) (by omega))
    change Y φ ^ d + (if guard φ then 2 ^ (A₁ * φ.length / q φ) * Y φ ^ e₁
        else ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ e₂) ≤ 2 * (T φ + 1)
    omega
  · -- space: the test and either branch are within `Y ^ b`
    have hd' : Y φ ^ d ≤ Y φ ^ b := Nat.pow_le_pow_right (hY1 φ) (by omega)
    have hbr : (if guard φ then Y φ ^ b₁ else Y φ ^ b₂) ≤ Y φ ^ b := by
      split
      · exact Nat.pow_le_pow_right (hY1 φ) (by omega)
      · exact Nat.pow_le_pow_right (hY1 φ) (by omega)
    change Y φ ^ d + (if guard φ then Y φ ^ b₁ else Y φ ^ b₂) ≤ 2 * (Y φ ^ b + 1)
    omega
  · -- every formula: the interpolation scale
    simp only [T]
    split
    · next hg =>
      have hφ : φ.length ≤ threshold φ.numVars := of_decide_eq_true hg
      have h := two_pow_le_of_le_threshold A₁ hφ
      have hceil : ⌈(2 : ℝ) ^ (((32 * A₁ : ℕ) : ℝ) * interpolationScale φ.numVars)⌉₊ ≤
          ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ :=
        Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 32 * A₁ ≤ A))
            (interpolationScale_nonneg _)))
      calc 2 ^ (A₁ * φ.length / q φ) * Y φ ^ e₀
          ≤ ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ (65536 * A₁) *
              Y φ ^ e₀ := Nat.mul_le_mul_right _ (h.trans (Nat.mul_le_mul_right _ hceil))
        _ = ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ e := by
            rw [he, pow_add]; ring
    · refine Nat.mul_le_mul (Nat.ceil_le_ceil (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : A₂ ≤ A))
          (interpolationScale_nonneg _)))) (hYe φ)
  · -- at most `threshold n` clauses: the contraction branch
    have hg : guard φ = true := decide_eq_true hφ
    simp only [T, hg, ↓reduceIte]
    refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right ?_)) (hYe φ)
    exact Nat.mul_le_mul (by omega) hφ
  · -- fixed density: few variables fall back on a constant
    set K := (Finset.range (2 ^ 2 ^ D)).sup
      fun n => ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale n)⌉₊ with hK
    refine ⟨A₁ * D + K, fun φ hφ => ?_⟩
    simp only [T]
    split
    · refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right ?_))
        (hYe φ)
      calc A₁ * φ.length ≤ A₁ * (D * φ.numVars) := Nat.mul_le_mul_left _ hφ
        _ ≤ (A₁ * D + K) * φ.numVars := by nlinarith
    · next hg =>
      have hgt : threshold φ.numVars < φ.length := by
        simpa only [guard, decide_eq_true_eq, not_le] using hg
      have hsmall : φ.numVars < 2 ^ 2 ^ D := by
        by_contra hbig
        have := mul_le_threshold (not_lt.mp hbig)
        omega
      have hn : 1 ≤ φ.numVars := by
        rcases Nat.eq_zero_or_pos φ.numVars with h0 | h0
        · rw [h0] at hφ hgt; omega
        · exact h0
      have hK' : ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale φ.numVars)⌉₊ ≤ K :=
        Finset.le_sup (f := fun n => ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale n)⌉₊)
          (Finset.mem_range.mpr hsmall)
      have hexp : K ≤ (A₁ * D + K) * φ.numVars / q φ := by
        calc K ≤ A₁ * D + K := Nat.le_add_left _ _
          _ = (A₁ * D + K) * φ.numVars / φ.numVars := (Nat.mul_div_cancel _ hn).symm
          _ ≤ (A₁ * D + K) * φ.numVars / q φ :=
              Nat.div_le_div_left (sqrt_log_le hn) (one_le_sqrt_log _)
      calc ⌈(2 : ℝ) ^ ((A₂ : ℝ) * interpolationScale φ.numVars)⌉₊ * Y φ ^ e₀
          ≤ 2 ^ ((A₁ * D + K) * φ.numVars / q φ) * Y φ ^ e :=
            Nat.mul_le_mul (hK'.trans ((Nat.lt_two_pow_self).le.trans
              (Nat.pow_le_pow_right (by norm_num) hexp))) (hYe φ)

end Cslib.Complexity.DensityBranchCounting
