/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Padding
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Statements of fine mass production

For a rational copy exponent `γ = num / den < 1`, fine mass production bounds the cost of every
allowed batch by `(1 + 1 / P) / (1 - γ) · 2 ^ n / n` for every positive precision `P`, eventually
in `n`.
The core form `FineMassProducesThrough` allows `2 ^ (⌊γ n⌋ + 1)` copies, including zero copies;
`FineMassProducesAt` is the source's statement over the floor budget `rationalCopyBudget` and
positive copy counts. The real-rate statement `RealFineMassProduction` quantifies over real
`0 ≤ γ < 1` and additive errors `ε > 0`, with copy counts at most `2 ^ (γ n)`.

*Fine* refers to the explicit leading coefficient `1 / (1 - γ)`, as opposed to the unspecified
constant of `MassProducesAt` (`4 den` via `FineMassProducesThrough.massProducesAt`); it does not
claim optimality. One copy of most functions already needs `(1 - o(1)) 2 ^ n / n` nonconstant
gates, by the counting argument of [Shannon1949] for gate circuits
[Jukna, Theorem 1.14][Jukna2012] (cslib's `Cslib.Circuits.Boolean.Shannon.lt_complexity` gives one
such function, counting constant gates, of which at most two are needed), so the coefficient is
optimal at `γ = 0`; no matching lower bound is claimed for `γ > 0`.

The core form implies the other two (`FineMassProducesThrough.fineMassProducesAt`,
`realFineMassProduction_of_fine`) and, at precision one, the exponential-range theorem with
a constant coefficient at every positive input length
(`exponentialMassProduction_of_fine`).

All statements bound `massComplexity`, which charges NOT, AND and OR once and constants never.
They are bounds on circuit cost, not on the running time of any circuit constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.FineMassProducesThrough`: the core fine bound.
* `Cslib.Circuits.Boolean.MassProduction.FineMassProducesAt`: the source's rational statement.
* `Cslib.Circuits.Boolean.MassProduction.RealFineMassProduction`: the real-rate statement.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.FineMassProducesThrough.massProducesAt`: the
  coefficient `4 den` at one rational exponent.
* `Cslib.Circuits.Boolean.MassProduction.exponentialMassProduction_of_fine`,
  `Cslib.Circuits.Boolean.MassProduction.realFineMassProduction_of_fine`: the corollaries.

## References

* Adapted from MassProduction/Nonuniform/{SharpTheorem,RealParameters,RealTheorem}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
* [C. E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949]
* [Stasys Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012], Theorem 1.14
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open Filter

/-- The core fine bound at rational exponent `num / den`: for every precision `P`, eventually
every function on `n` inputs has `k ≤ 2 ^ (⌊num n / den⌋ + 1)` copies with
`P (den - num) n · cost ≤ (P + 1) den 2 ^ n`. For `P > 0` this is the coefficient
`(1 + 1 / P) den / (den - num)`; `P = 0` holds trivially. -/
def FineMassProducesThrough (num den : ℕ) : Prop :=
  ∀ P : ℕ, ∀ᶠ n in atTop, ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), k ≤ 2 ^ (num * n / den + 1) →
    ((P * (den - num) * n : ℕ) : ℕ∞) * massComplexity f k ≤ ((P + 1) * den * 2 ^ n : ℕ)

/-- The source's statement at rational exponent `num / den`, over the floor budget and
positive copy counts. -/
def FineMassProducesAt (num den : ℕ) : Prop :=
  ∀ P : ℕ, 0 < P → ∃ cutoff : ℕ, ∀ n, cutoff ≤ n →
    ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), 0 < k → k ≤ rationalCopyBudget num den n →
      ((P * (den - num) * n : ℕ) : ℕ∞) * massComplexity f k ≤ ((P + 1) * den * 2 ^ n : ℕ)

/-- The source's real-rate statement: for every real `0 ≤ γ < 1` and every `ε > 0`, eventually
every positive copy count at most `2 ^ (γ n)` has a finite cost bound below
`(1 / (1 - γ) + ε) 2 ^ n / n`. -/
def RealFineMassProduction : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → γ < 1 → ∀ ε : ℝ, 0 < ε → ∃ cutoff : ℕ, ∀ n, cutoff ≤ n →
    ∀ (f : (Fin n → Bool) → Bool) (k : ℕ), 0 < k → (k : ℝ) ≤ (2 : ℝ) ^ (γ * n) →
      ∃ bound : ℕ, massComplexity f k ≤ bound ∧
        (bound : ℝ) ≤ (1 / (1 - γ) + ε) * ((2 : ℝ) ^ n / n)

variable {num den : ℕ}

/-- The floor budget is within the core budget. -/
theorem rationalCopyBudget_le_two_pow (n : ℕ) :
    rationalCopyBudget num den n ≤ 2 ^ (num * n / den + 1) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)

/-- The core fine bound implies the rational-rate statement over `rationalCopyBudget`. -/
theorem FineMassProducesThrough.fineMassProducesAt (h : FineMassProducesThrough num den) :
    FineMassProducesAt num den := by
  intro P _
  obtain ⟨cutoff, hc⟩ := eventually_atTop.mp (h P)
  exact ⟨cutoff, fun n hn f k _ hk => hc n hn f k (hk.trans (rationalCopyBudget_le_two_pow n))⟩

/-- At precision one the core bound gives the constant `4 den`: eventually every allowed batch
costs at most `4 den (2 ^ n / n)`. -/
theorem FineMassProducesThrough.massProducesAt (hnd : num < den)
    (h : FineMassProducesThrough num den) : MassProducesAt num den := by
  obtain ⟨cutoff, hc⟩ := eventually_atTop.mp (h 1)
  refine ⟨4 * den, max cutoff 1, fun n hn hcut f k _ hk => ?_⟩
  have hbound := hc n (le_of_max_le_left hcut) f k
    (hk.trans (rationalCopyBudget_le_two_pow n))
  obtain ⟨c, hcost⟩ := ENat.ne_top_iff_exists.mp (massComplexity_ne_top (f := f) (k := k))
  rw [← hcost] at hbound ⊢
  have hfin : 1 * (den - num) * n * c ≤ (1 + 1) * den * 2 ^ n := by
    rw [← Nat.cast_mul] at hbound
    exact ENat.natCast_le_natCast.mp hbound
  have hn1 : 1 ≤ n := le_of_max_le_right hcut
  have hq : 2 ^ n < n * (2 ^ n / n + 1) := by
    have := Nat.lt_mul_div_succ (2 ^ n) (show 0 < n by omega)
    simpa [Nat.mul_comm] using this
  have hgap : 1 ≤ den - num := by omega
  have hc' : n * c ≤ n * (4 * den * (2 ^ n / n)) := by
    have h1 : n * c ≤ 1 * (den - num) * n * c := by
      calc n * c = 1 * 1 * n * c := by ring
        _ ≤ 1 * (den - num) * n * c := by gcongr
    have hq' : 2 ^ n / n + 1 ≤ 2 * (2 ^ n / n) := by
      have : 1 ≤ 2 ^ n / n := (Nat.le_div_iff_mul_le (by omega)).mpr
        (by simpa using (Nat.lt_two_pow_self (n := n)).le)
      omega
    calc n * c ≤ (1 + 1) * den * 2 ^ n := h1.trans hfin
      _ ≤ (1 + 1) * den * (n * (2 ^ n / n + 1)) := by gcongr
      _ ≤ (1 + 1) * den * (n * (2 * (2 ^ n / n))) := by gcongr
      _ = n * (4 * den * (2 ^ n / n)) := by ring
  exact ENat.natCast_le_natCast.mpr (Nat.le_of_mul_le_mul_left hc' (by omega))

/-- **Exponential-range mass production** from the core fine bound: every fixed rational
exponent below one has a constant coefficient at every positive input length. -/
theorem exponentialMassProduction_of_fine
    (h : ∀ num den : ℕ, num < den → FineMassProducesThrough num den) :
    ExponentialMassProduction :=
  fun num den _ hnd => ((h num den hnd).massProducesAt hnd).allLengths

/-- Real rates and additive errors admit a rational rate above `γ` and an integer precision
whose coefficient `(1 + 1 / P) den / (den - num)` is at most `1 / (1 - γ) + ε`. -/
theorem exists_rat_coefficient {γ ε : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 < ε) :
    ∃ num den P : ℕ, num < den ∧ 0 < P ∧ γ < (num : ℝ) / den ∧
      ((P : ℝ) + 1) * den ≤ (1 / (1 - γ) + ε) * P * ((den - num : ℕ) : ℝ) := by
  set target := 1 / (1 - γ) + ε with htarget
  have hgap : 0 < 1 - γ := by linarith
  obtain ⟨κ, hlow, hup⟩ := exists_rat_btwn (show 1 / (1 - γ) < target by rw [htarget]; linarith)
  have hκ : 0 < (κ : ℝ) := (one_div_pos.mpr hgap).trans hlow
  set ρ : ℚ := 1 - 1 / κ with hρ
  have hρv : (ρ : ℝ) = 1 - 1 / (κ : ℝ) := by simp [hρ]
  have hρlow : γ < (ρ : ℝ) := by
    rw [hρv]
    have := (div_lt_iff₀ hgap).mp hlow
    have : 1 / (κ : ℝ) < 1 - γ := (div_lt_iff₀ hκ).mpr (by nlinarith)
    linarith
  have hρup : (ρ : ℝ) < 1 := by
    rw [hρv]
    have := one_div_pos.mpr hκ
    linarith
  have hρ0 : 0 ≤ ρ := by exact_mod_cast hγ.trans hρlow.le
  have hnum : 0 ≤ ρ.num := Rat.num_nonneg.mpr hρ0
  have hfrac : (ρ : ℝ) = (ρ.num.toNat : ℝ) / ρ.den := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hnum).symm
  have hden : 0 < (ρ.den : ℝ) := by exact_mod_cast ρ.den_pos
  have hproper : ρ.num.toNat < ρ.den := by
    rw [hfrac] at hρup
    have := (div_lt_iff₀ hden).mp hρup
    exact_mod_cast (by simpa using this : (ρ.num.toNat : ℝ) < ρ.den)
  have hident : (κ : ℝ) * ((ρ.den - ρ.num.toNat : ℕ) : ℝ) = ρ.den := by
    rw [Nat.cast_sub hproper.le]
    have h1 := div_mul_cancel₀ (1 : ℝ) (ne_of_gt hκ)
    have h2 := (eq_div_iff (ne_of_gt hden)).mp hfrac
    rw [hρv] at h2
    nlinarith
  have herr : 0 < target - (κ : ℝ) := sub_pos.mpr hup
  obtain ⟨P, hP⟩ := exists_nat_gt ((κ : ℝ) / (target - κ))
  have hP0 : 0 < P := by
    have : (0 : ℝ) < P := (div_pos hκ herr).trans hP
    exact_mod_cast this
  have hPs := (div_lt_iff₀ herr).mp hP
  refine ⟨ρ.num.toNat, ρ.den, P, hproper, hP0, by rwa [← hfrac], ?_⟩
  have hlead : ((P : ℝ) + 1) * κ ≤ target * P := by nlinarith
  calc ((P : ℝ) + 1) * ρ.den = (((P : ℝ) + 1) * κ) * ((ρ.den - ρ.num.toNat : ℕ) : ℝ) := by
        rw [mul_assoc, hident]
    _ ≤ target * P * ((ρ.den - ρ.num.toNat : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hlead (Nat.cast_nonneg _)

/-- A real copy budget `2 ^ (γ n)` below a rational exponent `num / den` is within the core
budget `2 ^ (⌊num n / den⌋ + 1)`. -/
private theorem le_two_pow_of_real {γ : ℝ} {n k : ℕ} (hden : 0 < den) (hγ : γ ≤ (num : ℝ) / den)
    (hk : (k : ℝ) ≤ (2 : ℝ) ^ (γ * n)) : k ≤ 2 ^ (num * n / den + 1) := by
  have hpos : 0 < (den : ℝ) := by exact_mod_cast hden
  have hq : (num : ℝ) * n < ((num * n / den + 1 : ℕ) : ℝ) * den := by
    have h := Nat.lt_mul_div_succ (num * n) hden
    rw [Nat.mul_comm den] at h
    exact_mod_cast h
  have hexp : γ * n ≤ ((num * n / den + 1 : ℕ) : ℝ) := by
    calc γ * n ≤ ((num : ℝ) / den) * n := mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _)
      _ = ((num : ℝ) * n) / den := by ring
      _ ≤ _ := ((div_lt_iff₀ hpos).mpr hq).le
  have := hk.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
  rw [Real.rpow_natCast] at this
  exact_mod_cast this

/-- **Real-rate fine mass production** from the core fine bound at every rational exponent. -/
theorem realFineMassProduction_of_fine
    (h : ∀ num den : ℕ, num < den → FineMassProducesThrough num den) :
    RealFineMassProduction := by
  intro γ hγ hγ1 ε hε
  obtain ⟨num, den, P, hnd, hP, hrate, hcoef⟩ := exists_rat_coefficient hγ hγ1 hε
  obtain ⟨cutoff, hc⟩ := eventually_atTop.mp (h num den hnd P)
  refine ⟨max cutoff 1, fun n hn f k _ hk => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hbound := hc n (le_of_max_le_left hn) f k (le_two_pow_of_real (by omega) hrate.le hk)
  obtain ⟨c, hcost⟩ := ENat.ne_top_iff_exists.mp (massComplexity_ne_top (f := f) (k := k))
  refine ⟨c, hcost.ge, ?_⟩
  rw [← hcost, ← Nat.cast_mul] at hbound
  have hfin : P * (den - num) * n * c ≤ (P + 1) * den * 2 ^ n :=
    ENat.natCast_le_natCast.mp hbound
  have hfinR : (P : ℝ) * ((den - num : ℕ) : ℝ) * n * c ≤ ((P : ℝ) + 1) * den * 2 ^ n := by
    exact_mod_cast hfin
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hscale : 0 < (P : ℝ) * ((den - num : ℕ) : ℝ) := by
    have : 0 < P * (den - num) := Nat.mul_pos hP (by omega)
    exact_mod_cast this
  have hpow : (0 : ℝ) ≤ 2 ^ n := by positivity
  have key : (P : ℝ) * ((den - num : ℕ) : ℝ) * (n * c) ≤
      (P : ℝ) * ((den - num : ℕ) : ℝ) * ((1 / (1 - γ) + ε) * 2 ^ n) := by
    calc (P : ℝ) * ((den - num : ℕ) : ℝ) * (n * c) = (P : ℝ) * ((den - num : ℕ) : ℝ) * n * c := by
          ring
      _ ≤ ((P : ℝ) + 1) * den * 2 ^ n := hfinR
      _ ≤ (1 / (1 - γ) + ε) * P * ((den - num : ℕ) : ℝ) * 2 ^ n :=
          mul_le_mul_of_nonneg_right hcoef hpow
      _ = (P : ℝ) * ((den - num : ℕ) : ℝ) * ((1 / (1 - γ) + ε) * 2 ^ n) := by ring
  have hnc := le_of_mul_le_mul_left key hscale
  rw [← mul_div_assoc, le_div_iff₀ hnR]
  linarith

end Cslib.Circuits.Boolean.MassProduction
