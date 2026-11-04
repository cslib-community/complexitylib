/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Convolution
public import Complexity.Foundations.BooleanAnalysis.LongCode
public import Complexity.Foundations.BooleanAnalysis.Noise
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.Chebyshev

/-!
# Håstad's 3-Bit Linear Test and Spectral Decoding Weights

This module formalizes Håstad's noisy 3-bit linear test on folded (odd, `Cslib.BitString.IsOdd`)
Long Code tables over a single projection `π : β → γ`, its exact Walsh–Fourier expansion, and the
Cauchy–Schwarz and Parseval soundness bound via low-degree spectral decoding weights [Hastad2001].
The Long Code, folding and the mod-2 projection `Cslib.BitString.projectSet` live in
`Complexity.Foundations.BooleanAnalysis.LongCode`.

## Main definitions

* `Cslib.PCP.Hastad.linearCorr`, `Cslib.PCP.Hastad.linearProb`: correlation and
  acceptance probability of Håstad's 3-bit linear test on an edge `π : β → γ`.
* `Cslib.PCP.Hastad.spectralWeight`: low-degree Fourier decoding weights on `α`.

## Main results

* `Cslib.PCP.Hastad.linearCorr_longCode`, `Cslib.PCP.Hastad.linearProb_longCode`:
  completeness `1 - δ` for 3-bit linear tests on valid Long Code tables.
* `Cslib.PCP.Hastad.linearCorr_eq_sum`: exact Walsh–Fourier expansion of Håstad's 3-bit test
  correlation.
* `Cslib.PCP.Hastad.sum_spectralWeight_le_one`: Parseval bound showing that `spectralWeight k B` is
  a sub-probability distribution on `γ`.
* `Cslib.PCP.Hastad.linearCorr_sq_le`: single-edge Cauchy–Schwarz + Parseval soundness bound.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
* [R. O'Donnell, *Analysis of Boolean Functions*, Chapter 7][ODonnell2014]
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Cslib.PCP.Hastad

open Cslib.BitString

variable {α β γ : Type*}

/-! ### Håstad's 3-bit linear test and its Fourier expansion -/

section LinearTest

variable [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **correlation** of Håstad's 3-bit linear test on a projection `π : β → γ` at noise rate `δ`
between tables `B : (γ → Bool) → Bool` and `A : (β → Bool) → Bool` [Håstad, Section 5][Hastad2001]:
the expected product of the `±1` signs of `B f`, `A g`, and `A ((f ∘ π) + g + μ)` over uniform
`f : γ → Bool`, uniform `g : β → Bool`, and `δ`-biased Bernoulli noise `μ : β → Bool`. -/
noncomputable def linearCorr (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))

/-- The **acceptance probability** of Håstad's 3-bit linear test: the probability that
`(B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false` under uniform `f, g` and `δ`-biased noise `μ`. -/
noncomputable def linearProb (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) : ℝ :=
  𝔼 f : γ → Bool, 𝔼 g : β → Bool,
    bernoulliAverage δ fun μ =>
      if (B f ^^ A g ^^ A ((f ∘ π) + g + μ)) = false then 1 else 0

/-- The acceptance probability of Håstad's 3-bit linear test is
`1 / 2 + 1 / 2 * linearCorr π δ B A`. -/
theorem linearProb_eq_add_linearCorr (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    linearProb π δ B A = 1 / 2 + 1 / 2 * linearCorr π δ B A := by
  have h (b₁ b₂ b₃ : Bool) :
      (if (b₁ ^^ b₂ ^^ b₃) = false then (1 : ℝ) else 0) =
        1 / 2 + 1 / 2 * (signVal b₁ * signVal b₂ * signVal b₃) := by
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp only [signVal] <;> norm_num
  simp only [linearProb, linearCorr, h, bernoulliAverage_add, bernoulliAverage_const,
    bernoulliAverage_const_mul, expect_add_distrib, Fintype.expect_const, mul_expect]

/-- **Completeness of Håstad's 3-bit linear test (correlation)**: on matching Long Code tables
`longCode (π x)` and `longCode x`, the correlation is `1 - 2 * δ`. -/
theorem linearCorr_longCode (π : β → γ) (δ : ℝ) (x : β) :
    linearCorr π δ (longCode (π x)) (longCode x) = 1 - 2 * δ := by
  have hsign (f : γ → Bool) (g μ : β → Bool) :
      signVal (longCode (π x) f) * signVal (longCode x g) *
        signVal (longCode x ((f ∘ π) + g + μ)) = chi ℝ {x} μ := by
    rw [chi_singleton]
    change signVal (f (π x)) * signVal (g x) * signVal (f (π x) + g x + μ x) = signVal (μ x)
    cases f (π x) <;> cases g x <;> cases μ x <;> simp [signVal, Bool.add_eq_xor]
  simp only [linearCorr, hsign, bernoulliAverage_chi, card_singleton, pow_one,
    Fintype.expect_const]

/-- **Completeness of Håstad's 3-bit linear test (probability)**: matching Long Code tables
`longCode (π x)` and `longCode x` pass the test with probability `1 - δ`. -/
theorem linearProb_longCode (π : β → γ) (δ : ℝ) (x : β) :
    linearProb π δ (longCode (π x)) (longCode x) = 1 - δ := by
  rw [linearProb_eq_add_linearCorr, linearCorr_longCode]
  ring

/-- **Walsh–Fourier expansion of Håstad's 3-bit linear test**
[Håstad, proof of Lemma 5.2, Eqs. (9)–(12)][Hastad2001]:
the correlation equals
`∑ T : Finset β, (1 - 2 * δ) ^ #T * fourierCoeff F_A T ^ 2 * fourierCoeff F_B (projectSet π T)`. -/
theorem linearCorr_eq_sum (π : β → γ) (δ : ℝ) (B : (γ → Bool) → Bool)
    (A : (β → Bool) → Bool) :
    linearCorr π δ B A =
      ∑ T : Finset β,
        (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          fourierCoeff (fun f => signVal (B f)) (projectSet π T) := by
  have hδ : (1 - (1 - 2 * δ)) / 2 = δ := by ring
  have hinner (f : γ → Bool) (g : β → Bool) :
      (bernoulliAverage δ fun μ =>
          signVal (B f) * signVal (A g) * signVal (A ((f ∘ π) + g + μ))) =
        signVal (B f) *
          (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g)) := by
    simp only [mul_assoc, bernoulliAverage_const_mul, noiseOp, hδ]
  have hconv (f : γ → Bool) :
      (𝔼 g : β → Bool,
          signVal (B f) *
            (signVal (A g) * noiseOp (1 - 2 * δ) (fun h => signVal (A h)) ((f ∘ π) + g))) =
        signVal (B f) * ∑ T : Finset β,
          (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f := by
    rw [← mul_expect]
    congr 1
    change convolution (fun g => signVal (A g))
      (noiseOp (1 - 2 * δ) (fun h => signVal (A h))) (f ∘ π) = _
    rw [← sum_fourierCoeff_mul_chi
      (convolution (fun g => signVal (A g)) (noiseOp (1 - 2 * δ) (fun h => signVal (A h))))
      (f ∘ π)]
    refine sum_congr rfl fun T _ => ?_
    rw [fourierCoeff_convolution, fourierCoeff_noiseOp, chi_comp_eq_chi_projectSet]
    ring
  simp only [linearCorr, hinner, hconv, mul_sum]
  rw [expect_sum_comm]
  refine sum_congr rfl fun T _ => ?_
  have hterm (f : γ → Bool) :
      signVal (B f) *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            chi ℝ (projectSet π T) f) =
        ((1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2) *
          (signVal (B f) * chi ℝ (projectSet π T) f) := by
    ring
  simp only [hterm, ← mul_expect]
  rfl

end LinearTest

/-! ### Spectral decoding weights and Cauchy–Schwarz soundness bound -/

section Soundness

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- The **low-degree spectral decoding weight** of `x : α` for table `A : (α → Bool) → Bool` at
degree cutoff `k`: `∑_{T : #T < k, x ∈ T} fourierCoeff F_A T ^ 2 / #T`
[Håstad, Proof of Lemma 5.2][Hastad2001]. -/
noncomputable def spectralWeight (k : ℕ) (A : (α → Bool) → Bool) (x : α) : ℝ :=
  ∑ T ∈ univ.filter (fun T : Finset α => #T < k ∧ x ∈ T),
    fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T

theorem spectralWeight_nonneg (k : ℕ) (A : (α → Bool) → Bool) (x : α) :
    0 ≤ spectralWeight k A x :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **By Parseval's identity, the spectral decoding weights form a sub-probability distribution**:
`∑ x, spectralWeight k A x ≤ 1`. -/
theorem sum_spectralWeight_le_one (k : ℕ) (A : (α → Bool) → Bool) :
    ∑ x : α, spectralWeight k A x ≤ 1 := by
  simp only [spectralWeight, sum_filter]
  rw [sum_comm]
  rw [← sum_fourierCoeff_sq_signVal A]
  refine sum_le_sum fun T _ => ?_
  by_cases hTk : #T < k
  · by_cases hT0 : T = ∅
    · subst hT0
      simp only [notMem_empty, and_false, ↓reduceIte, sum_const_zero]
      exact sq_nonneg _
    · have hpos : (0 : ℝ) < #T := by
        exact_mod_cast card_pos.2 (nonempty_iff_ne_empty.2 hT0)
      have hsum :
          (∑ x : α, if #T < k ∧ x ∈ T then
            fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) =
          ∑ x ∈ T, fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext x
        simp [hTk]
      rw [hsum, sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']
  · simp only [hTk, false_and, ↓reduceIte, sum_const_zero]
    exact sq_nonneg _

/-- For a character `S` of size `< k` containing `y`, its squared Fourier coefficient is at most
`k * spectralWeight k B y`. -/
private theorem fourierCoeff_sq_le_mul_spectralWeight {k : ℕ} (B : (α → Bool) → Bool)
    {S : Finset α} (hSk : #S < k) {y : α} (hy : y ∈ S) :
    fourierCoeff (fun f => signVal (B f)) S ^ 2 ≤ (k : ℝ) * spectralWeight k B y := by
  have hpos : (0 : ℝ) < #S := by exact_mod_cast card_pos.2 ⟨y, hy⟩
  have hle : (#S : ℝ) ≤ k := by exact_mod_cast hSk.le
  have hsingle : fourierCoeff (fun f => signVal (B f)) S ^ 2 / #S ≤ spectralWeight k B y := by
    rw [spectralWeight]
    exact single_le_sum
      (f := fun S : Finset α => fourierCoeff (fun f => signVal (B f)) S ^ 2 / #S)
      (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (mem_filter.2 ⟨mem_univ S, hSk, hy⟩)
  calc fourierCoeff (fun f => signVal (B f)) S ^ 2
    _ = #S * (fourierCoeff (fun f => signVal (B f)) S ^ 2 / #S) :=
        (mul_div_cancel₀ _ hpos.ne').symm
    _ ≤ (k : ℝ) * spectralWeight k B y :=
        mul_le_mul hle hsingle (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg k)

/-- Each low-degree character `T` with `#T < k` and `projectSet π T ≠ ∅` contributes at most
`k ^ 2` times the sum over `x ∈ T` of `(fourierCoeff F_A T ^ 2 / #T) * spectralWeight k B (π x)`. -/
private theorem ite_fourierCoeff_sq_mul_le (π : β → γ) (k : ℕ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) (T : Finset β) :
    (if #T < k ∧ projectSet π T ≠ ∅ then
      fourierCoeff (fun g => signVal (A g)) T ^ 2 *
        fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
    else 0) ≤
      (k : ℝ) ^ 2 * ∑ x : β,
        (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
          spectralWeight k B (π x) := by
  have hnn (x : β) : 0 ≤ (if #T < k ∧ x ∈ T then
      fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) * spectralWeight k B (π x) := by
    split_ifs
    · exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
        (spectralWeight_nonneg k B (π x))
    · simp
  split_ifs with hT
  · obtain ⟨hTk, hne⟩ := hT
    obtain ⟨_, hy⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨x₀, hx₀T, rfl⟩ := exists_mem_of_mem_projectSet hy
    have hpos : (0 : ℝ) < #T := by exact_mod_cast card_pos.2 ⟨x₀, hx₀T⟩
    have hA : fourierCoeff (fun g => signVal (A g)) T ^ 2 ≤
        (k : ℝ) * (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) := by
      rw [mul_div_assoc', le_div_iff₀' hpos]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTk.le : (#T : ℝ) ≤ k) (sq_nonneg _)
    have hB := fourierCoeff_sq_le_mul_spectralWeight B ((card_projectSet_le π T).trans_lt hTk) hy
    have hsingle : (fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T) *
        spectralWeight k B (π x₀) ≤ ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := by
      simpa [hTk, hx₀T] using single_le_sum (fun x _ => hnn x) (mem_univ x₀)
    nlinarith [mul_le_mul hA hB (sq_nonneg _) (by positivity), sq_nonneg (k : ℝ)]
  · exact mul_nonneg (sq_nonneg _) (sum_nonneg fun x _ => hnn x)

/-- Low-degree terms in the Cauchy–Schwarz bound are controlled by the collision probability of the
spectral decoding distributions along `π`. -/
private theorem sum_lowDegree_fourierCoeff_sq_le (π : β → γ) (k : ℕ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    (∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
      fourierCoeff (fun g => signVal (A g)) T ^ 2 *
        fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2) ≤
      (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  rw [sum_filter]
  calc (∑ T : Finset β,
        if #T < k ∧ projectSet π T ≠ ∅ then
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2
        else 0)
    _ ≤ ∑ T : Finset β, (k : ℝ) ^ 2 * ∑ x : β,
          (if #T < k ∧ x ∈ T then fourierCoeff (fun g => signVal (A g)) T ^ 2 / #T else 0) *
            spectralWeight k B (π x) := sum_le_sum fun T _ => ite_fourierCoeff_sq_mul_le π k B A T
    _ = (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
      rw [← mul_sum, sum_comm]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_mul]
      congr 1
      rw [spectralWeight, sum_filter]

/-- By Cauchy–Schwarz and Parseval's identity on `A`, `linearCorr π δ B A ^ 2` is at most the
`fourierCoeff F_A T ^ 2`-weighted sum of the squared attenuated coefficients of `B`. -/
private theorem linearCorr_sq_le_sum_fourierCoeff_sq (π : β → γ) (δ : ℝ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    linearCorr π δ B A ^ 2 ≤
      ∑ T : Finset β,
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2 := by
  rw [linearCorr_eq_sum, show (∑ T : Finset β,
      (1 - 2 * δ) ^ #T * fourierCoeff (fun g => signVal (A g)) T ^ 2 *
        fourierCoeff (fun f => signVal (B f)) (projectSet π T)) =
    ∑ T : Finset β, fourierCoeff (fun g => signVal (A g)) T *
      (fourierCoeff (fun g => signVal (A g)) T *
        ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T))) from
    sum_congr rfl fun _ _ => by ring]
  have h1 := sum_mul_sq_le_sq_mul_sq univ
    (fun T : Finset β => fourierCoeff (fun g => signVal (A g)) T)
    (fun T : Finset β =>
      fourierCoeff (fun g => signVal (A g)) T *
        ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)))
  rw [sum_fourierCoeff_sq_signVal, one_mul] at h1
  exact h1.trans_eq (sum_congr rfl fun _ _ => by ring)

/-- **Cauchy–Schwarz and Parseval soundness bound for Håstad's 3-bit linear test**
[Håstad, Lemma 5.2][Hastad2001]: for any folded (odd) table `B`, any table `A`, noise rate
`0 ≤ δ ≤ 1 / 2`, and degree cutoff `k`, the squared correlation `linearCorr π δ B A ^ 2` is
at most `(1 - 2 * δ) ^ (2 * k) + k ^ 2 * ∑ x, spectralWeight k A x * spectralWeight k B (π x)`. -/
theorem linearCorr_sq_le (π : β → γ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (k : ℕ) {B : (γ → Bool) → Bool} (hB : IsOdd B) (A : (β → Bool) → Bool) :
    linearCorr π δ B A ^ 2 ≤
      (1 - 2 * δ) ^ (2 * k) +
        (k : ℝ) ^ 2 * ∑ x : β, spectralWeight k A x * spectralWeight k B (π x) := by
  have hρ0 : 0 ≤ 1 - 2 * δ := by linarith
  have hρ1 : 1 - 2 * δ ≤ 1 := by linarith
  have hsplit :
      (∑ T : Finset β,
        fourierCoeff (fun g => signVal (A g)) T ^ 2 *
          ((1 - 2 * δ) ^ #T * fourierCoeff (fun f => signVal (B f)) (projectSet π T)) ^ 2) ≤
      (1 - 2 * δ) ^ (2 * k) * (∑ T : Finset β, fourierCoeff (fun g => signVal (A g)) T ^ 2) +
        ∑ T ∈ univ.filter (fun T : Finset β => #T < k ∧ projectSet π T ≠ ∅),
          fourierCoeff (fun g => signVal (A g)) T ^ 2 *
            fourierCoeff (fun f => signVal (B f)) (projectSet π T) ^ 2 := by
    rw [mul_sum, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun T _ => ?_
    have hnn : 0 ≤ (1 - 2 * δ) ^ (2 * k) * fourierCoeff (fun g => signVal (A g)) T ^ 2 :=
      mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
    by_cases hTk : #T < k
    · by_cases hne : projectSet π T ≠ ∅
      · simp only [hTk, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ 1 := by
          rw [← pow_mul]
          exact pow_le_one₀ hρ0 hρ1
        nlinarith [mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (sq_nonneg (fourierCoeff (fun g => signVal (A g)) T))
            (sq_nonneg (fourierCoeff (fun f => signVal (B f)) (projectSet π T))))]
      · push Not at hne
        simpa only [hTk, hne, ne_eq, not_true_eq_false, and_false, ↓reduceIte, add_zero,
          hB.fourierCoeff_empty, mul_zero, sq (0 : ℝ)] using hnn
    · simp only [hTk, false_and, ↓reduceIte, add_zero]
      have hpow : ((1 - 2 * δ) ^ #T) ^ 2 ≤ (1 - 2 * δ) ^ (2 * k) := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
      have hFB := Cslib.BitString.fourierCoeff_sq_signVal_le_one B (projectSet π T)
      nlinarith [mul_le_mul hpow hFB (sq_nonneg _) (pow_nonneg hρ0 _),
        sq_nonneg (fourierCoeff (fun g => signVal (A g)) T)]
  rw [sum_fourierCoeff_sq_signVal, mul_one] at hsplit
  linarith [linearCorr_sq_le_sum_fourierCoeff_sq π δ B A, hsplit,
    sum_lowDegree_fourierCoeff_sq_le π k B A]

end Soundness

end Cslib.PCP.Hastad
