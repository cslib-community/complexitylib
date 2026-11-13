/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AuxiliaryFormula
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Complex.Exponential
import CslibFrontier.Foundations.Combinatorics.DistinctValues
import CslibFrontier.Foundations.Data.BitString.Block
import Mathlib.Tactic

/-!
# Predictors of random functions

[ChukhinKulikovMihajlinSmal2026], Lemma 6.4 (printed pp. 16–17; PDF pp. 17–18). Fix
`m ≥ 1` and any map `τ : U_m → {0, 1}ᵐ ∪ {⊥}` on the `m × n` matrices, for example the predictor
`τ_φ` of a formula (`predictor`). For a uniformly random `g : {0, 1}ⁿ → {0, 1}`, let `q_τ(g)` be
the fraction of matrices `Z` with `τ(Z) = gᵐ(Z)` (`agreeFraction`). Then:

* `sum_agreeFraction_pow_le`, `sum_agreeFraction_pow_le_exp`: for every `k`,
  `E_g[q_τ(g)^k] ≤ 2^{-mk} ∏_{r < mk} (1 + r/N) ≤ 2^{-mk} exp(m²k²/(2N))`, where `N = 2ⁿ`;
* `card_le_agreeFraction_le`: `Pr_g[q_τ(g) ≥ 2^{1-m}] ≤ 2^{-k} exp(m²k²/(2N))` for every `k`;
* `card_le_agreeFraction_le_two_thirds_pow`: `Pr_g[q_τ(g) ≥ 2^{1-m}] ≤ (2/3)^{⌊N/(2m²)⌋}`, the
  source's `2^{-Ω(N/m²)}`.

The probability model is the finite uniform one: expectations and probabilities over `g` are sums
over all `2^{2ⁿ}` functions divided by `2^{2ⁿ}`, and `q_τ(g)` is a count over all `2^{mn}`
matrices.

The proof follows the source. Expanding `q_τ(g)^k` samples `k` matrices. All `k` predictions are
correct for at most `2^{N - |J|}` functions `g`, where `J` is the set of distinct rows among the
`mk` rows (`Finset.card_filter_le_two_pow_card_sub`). The rows form a uniform tuple, so
`E[2^{-|J|}] ≤ ∏_{r < mk} ((1 + r/N)/2)` (`Finset.sum_half_pow_card_image_le`). The source's tail
takes `k = ⌊N ln 2/m²⌋` and needs `N ≥ 4m²`; here `k = ⌊N/(2m²)⌋`, which needs no assumption on
`N` and gives the base `e^{1/4}/2 ≤ 2/3`.

Lemma 6.5 (a union bound over the formulas with auxiliary variables of Lemma 6.1, counted with
`depthFunctions`) and Theorem 6.6 are not formalized yet.

## Main definitions

* `Cslib.Circuits.Boolean.agreeFraction`: the fraction `q_τ(g)`.

## Main results

* `Cslib.Circuits.Boolean.sum_agreeFraction_pow_le`,
  `Cslib.Circuits.Boolean.sum_agreeFraction_pow_le_exp`: the moment bound.
* `Cslib.Circuits.Boolean.card_le_agreeFraction_le`,
  `Cslib.Circuits.Boolean.card_le_agreeFraction_le_two_thirds_pow`: the tail.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset Cslib.BitString

variable {m n : ℕ}

open scoped Classical in
/-- The fraction `q_τ(g) = Pr_{Z ∈ U_m}[τ(Z) = gᵐ(Z)]` of the `2^{mn}` matrices `Z` on which a
fixed map `τ : U_m → {0, 1}ᵐ ∪ {⊥}` (`none` is `⊥`) predicts the row values `gᵐ(Z)`. -/
@[expose] noncomputable def agreeFraction (τ : (Fin m → BitString n) → Option (BitString m))
    (g : BitString n → Bool) : ℝ :=
  ((univ.filter fun Z => τ Z = some (rowValues g Z)).card : ℝ) /
    Fintype.card (Fin m → BitString n)

theorem agreeFraction_nonneg (τ : (Fin m → BitString n) → Option (BitString m))
    (g : BitString n → Bool) : 0 ≤ agreeFraction τ g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

open scoped Classical in
/-- **The moment bound of [ChukhinKulikovMihajlinSmal2026], Lemma 6.4** (printed p. 16; PDF
p. 17). For a uniformly random `g : {0, 1}ⁿ → {0, 1}` and every `k`,
`E_g[q_τ(g)^k] ≤ 2^{-mk} ∏_{r < mk} (1 + r/N)` with `N = 2ⁿ`.

Expanding the `k`-th power samples `k` matrices. Given them, all `k` predictions are correct for at
most `2^{N - |J|}` functions, where `J` is the set of their distinct rows
(`Finset.card_filter_le_two_pow_card_sub`). The `mk` rows are a uniform tuple, so
`E[2^{-|J|}] ≤ ∏_{r < mk} ((1 + r/N)/2)` (`Finset.sum_half_pow_card_image_le`). -/
theorem sum_agreeFraction_pow_le (τ : (Fin m → BitString n) → Option (BitString m)) (k : ℕ) :
    (∑ g : BitString n → Bool, agreeFraction τ g ^ k) / 2 ^ 2 ^ n ≤
      (1 / 2) ^ (k * m) * ∏ r ∈ range (k * m), (1 + (r : ℝ) / 2 ^ n) := by
  have hX : (Fintype.card (BitString n) : ℝ) = 2 ^ n := by simp
  have hU : (Fintype.card (Fin m → BitString n) : ℝ) = (2 ^ n) ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, hX]
  have hN0 : (0 : ℝ) < 2 ^ n := by positivity
  set ind : (Fin m → BitString n) → (BitString n → Bool) → ℝ :=
    fun Z g => if τ Z = some (rowValues g Z) then 1 else 0
  have hq (g : BitString n → Bool) :
      agreeFraction τ g = (∑ Z, ind Z g) / Fintype.card (Fin m → BitString n) := by
    rw [agreeFraction, card_filter]
    push_cast
    rfl
  -- The rows of `k` matrices, and the functions that make all `k` predictions correct.
  let J : (Fin k → (Fin m → BitString n)) → Finset (BitString n) :=
    fun Zs => univ.image fun p : Fin k × Fin m =>
    Zs p.1 p.2
  have hcount (Zs : Fin k → (Fin m → BitString n)) :
      ∑ g : BitString n → Bool, ∏ j, ind (Zs j) g ≤ 2 ^ 2 ^ n * (1 / 2) ^ (J Zs).card := by
    have hcard := card_filter_le_two_pow_card_sub (J Zs)
      (fun g => ∀ j, τ (Zs j) = some (rowValues g (Zs j))) fun g g' hg hg' x hx => by
        obtain ⟨⟨j, i⟩, -, rfl⟩ := mem_image.1 hx
        have := (hg j).symm.trans (hg' j)
        exact congrFun (Option.some_injective _ this) i
    have hle : (J Zs).card ≤ Fintype.card (BitString n) := card_le_univ _
    calc ∑ g : BitString n → Bool, ∏ j, ind (Zs j) g
        = ((univ.filter fun g => ∀ j, τ (Zs j) = some (rowValues g (Zs j))).card : ℝ) := by
          simp only [ind, prod_boole, mem_univ, true_implies, sum_boole]
      _ ≤ (2 : ℝ) ^ (Fintype.card (BitString n) - (J Zs).card) := by exact_mod_cast hcard
      _ = 2 ^ 2 ^ n * (1 / 2) ^ (J Zs).card := by
          rw [pow_sub₀ _ two_ne_zero hle, one_div_pow, div_eq_mul_inv]
          simp
  -- Reindex the `k` matrices as one tuple of `km` rows.
  have hreindex : ∑ Zs : Fin k → (Fin m → BitString n), ((1 : ℝ) / 2) ^ (J Zs).card =
      ∑ w : Fin (k * m) → BitString n, ((1 : ℝ) / 2) ^ (univ.image w).card := by
    rw [← (blocksEquiv (α := BitString n) (m := k) (k := m)).sum_comp]
    refine sum_congr rfl fun w _ => ?_
    congr 2
    ext x
    simp only [J, mem_image, mem_univ, true_and, blocksEquiv_apply, block_apply]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨finProdFinEquiv.symm i, by simp only [Prod.mk.eta, Equiv.apply_symm_apply]⟩
  have hdist := sum_half_pow_card_image_le (α := BitString n) (k * m)
  rw [hX] at hdist
  -- Assemble.
  calc (∑ g : BitString n → Bool, agreeFraction τ g ^ k) / 2 ^ 2 ^ n
      = (∑ Zs : Fin k → (Fin m → BitString n), ∑ g : BitString n → Bool, ∏ j, ind (Zs j) g) /
          (Fintype.card (Fin m → BitString n) : ℝ) ^ k / 2 ^ 2 ^ n := by
        simp only [hq, div_pow, ← sum_div, Fintype.sum_pow]
        rw [sum_comm]
    _ ≤ (∑ Zs : Fin k → (Fin m → BitString n), 2 ^ 2 ^ n * ((1 : ℝ) / 2) ^ (J Zs).card) /
          (Fintype.card (Fin m → BitString n) : ℝ) ^ k / 2 ^ 2 ^ n := by
        gcongr with Zs
        exact hcount Zs
    _ = (∑ w : Fin (k * m) → BitString n, ((1 : ℝ) / 2) ^ (univ.image w).card) /
          ((2 : ℝ) ^ n) ^ (k * m) := by
        rw [← mul_sum, hreindex, hU, ← pow_mul, mul_comm m k]
        field_simp
    _ ≤ ((2 : ℝ) ^ n) ^ (k * m) * (∏ r ∈ range (k * m), ((1 + (r : ℝ) / 2 ^ n) / 2)) /
          ((2 : ℝ) ^ n) ^ (k * m) :=
        div_le_div_of_nonneg_right hdist (by positivity)
    _ = (1 / 2) ^ (k * m) * ∏ r ∈ range (k * m), (1 + (r : ℝ) / 2 ^ n) := by
        rw [mul_div_cancel_left₀ _ (by positivity), prod_div_distrib, prod_const, card_range,
          div_eq_mul_inv, mul_comm, one_div, inv_pow]

/-- **Lemma 6.4, the moment bound in the source's form**:
`E_g[q_τ(g)^k] ≤ 2^{-mk} exp(m²k²/(2N))` with `N = 2ⁿ`. -/
theorem sum_agreeFraction_pow_le_exp (τ : (Fin m → BitString n) → Option (BitString m))
    (k : ℕ) :
    (∑ g : BitString n → Bool, agreeFraction τ g ^ k) / 2 ^ 2 ^ n ≤
      (1 / 2) ^ (k * m) * Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n)) :=
  (sum_agreeFraction_pow_le τ k).trans (mul_le_mul_of_nonneg_left
    (prod_one_add_div_le_exp (k * m) (by positivity)) (by positivity))

open scoped Classical in
/-- **Lemma 6.4, the tail** (Markov's inequality for the `k`-th moment). For every `k`, the
fraction of functions `g` with `q_τ(g) ≥ 2^{1-m}` is at most `2^{-k} exp(m²k²/(2N))`. -/
theorem card_le_agreeFraction_le (τ : (Fin m → BitString n) → Option (BitString m)) (k : ℕ) :
    ((univ.filter fun g : BitString n → Bool => 2 * (1 / 2) ^ m ≤ agreeFraction τ g).card : ℝ) /
        2 ^ 2 ^ n ≤ (1 / 2) ^ k * Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n)) := by
  set B := univ.filter fun g : BitString n → Bool => 2 * (1 / 2) ^ m ≤ agreeFraction τ g
  set c : ℝ := 2 * (1 / 2) ^ m
  have hc : 0 < c := by positivity
  have hmarkov : (B.card : ℝ) * c ^ k ≤ ∑ g : BitString n → Bool, agreeFraction τ g ^ k := by
    calc (B.card : ℝ) * c ^ k = ∑ _g ∈ B, c ^ k := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ g ∈ B, agreeFraction τ g ^ k :=
          sum_le_sum fun g hg => pow_le_pow_left₀ hc.le (mem_filter.1 hg).2 k
      _ ≤ ∑ g : BitString n → Bool, agreeFraction τ g ^ k :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun g _ _ =>
            pow_nonneg (agreeFraction_nonneg τ g) k
  have hmom := sum_agreeFraction_pow_le_exp τ k
  have hck : c ^ k = 2 ^ k * (1 / 2) ^ (k * m) := by
    simp only [c, mul_pow, ← pow_mul, mul_comm m k]
  have h2 : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
  rw [div_le_iff₀ h2]
  rw [div_le_iff₀ h2] at hmom
  have hpos : (0 : ℝ) < c ^ k := by positivity
  rw [← mul_le_mul_iff_of_pos_right hpos]
  calc (B.card : ℝ) * c ^ k ≤ _ := hmarkov
    _ ≤ (1 / 2) ^ (k * m) * Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n)) * 2 ^ 2 ^ n := hmom
    _ = (1 / 2) ^ k * Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n)) * 2 ^ 2 ^ n * c ^ k := by
        have h12 : ((1 : ℝ) / 2) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
        rw [hck]
        linear_combination (-(Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n)) * 2 ^ 2 ^ n *
          (1 / 2) ^ (k * m))) * h12

open scoped Classical in
/-- **Lemma 6.4, the tail with explicit constants**: the fraction of functions `g` with
`q_τ(g) ≥ 2^{1-m}` is at most `(2/3)^{⌊N/(2m²)⌋}`, the source's `2^{-Ω(N/m²)}`. The source's
`N ≥ 4m²` is not needed. For `m > 0` and `N < 2m²`, the exponent is zero and the bound is `1`.
For `m = 0`, natural-number division by zero also gives exponent zero. -/
theorem card_le_agreeFraction_le_two_thirds_pow
    (τ : (Fin m → BitString n) → Option (BitString m)) :
    ((univ.filter fun g : BitString n → Bool => 2 * (1 / 2) ^ m ≤ agreeFraction τ g).card : ℝ) /
        2 ^ 2 ^ n ≤ (2 / 3) ^ (2 ^ n / (2 * m ^ 2)) := by
  set k := 2 ^ n / (2 * m ^ 2)
  refine (card_le_agreeFraction_le τ k).trans ?_
  have hk : 2 * (k * m ^ 2) ≤ 2 ^ n :=
    calc 2 * (k * m ^ 2) = k * (2 * m ^ 2) := by ring
      _ ≤ 2 ^ n := Nat.div_mul_le_self _ _
  have hexp : ((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n) ≤ k / 4 := by
    have hk' : (2 : ℝ) * (k * m ^ 2) ≤ 2 ^ n := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have he : Real.exp (1 / 4) ≤ 4 / 3 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 4) (by norm_num [abs_of_pos])
    have := (abs_le.1 this).2
    norm_num at this ⊢
    linarith
  calc (1 / 2) ^ k * Real.exp (((k * m : ℕ) : ℝ) ^ 2 / (2 * 2 ^ n))
      ≤ (1 / 2) ^ k * Real.exp (1 / 4) ^ k := by
        gcongr
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ (1 / 2) ^ k * (4 / 3) ^ k := by gcongr
    _ = (2 / 3) ^ k := by rw [← mul_pow]; norm_num

end Cslib.Circuits.Boolean
