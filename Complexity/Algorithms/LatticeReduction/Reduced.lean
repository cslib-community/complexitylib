/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# LLL-reduced bases and the approximation to the shortest vector

A family `b : Fin n → E` in a real inner product space has Gram–Schmidt vectors
`b*ᵢ = gramSchmidt ℝ b i` and coefficients `μᵢⱼ = gramSchmidtCoeff ℝ b i j`. Following
[LenstraLenstraLovasz1982], (1.4)–(1.5), with the constant `3/4` replaced by a parameter `δ` as
allowed by the remark after their (1.5), `b` is *`δ`-reduced*
(`Cslib.Algorithms.LatticeReduction.IsReduced δ b`) when

* it is size reduced: `|μᵢⱼ| ≤ 1/2` for `j < i` (`Cslib.Algorithms.LatticeReduction.IsSizeReduced`);
* the exchange condition `δ ‖b*ᵢ‖² ≤ ‖b*ᵢ₊₁ + μᵢ₊₁,ᵢ b*ᵢ‖²` holds for every `i`
  (`Cslib.Algorithms.LatticeReduction.ExchangeCondAt`).

For `1/4 < δ`, consecutive Gram–Schmidt lengths then satisfy `‖b*ᵢ‖² ≤ 4/(4δ-1) · ‖b*ᵢ₊₁‖²`
(`norm_sq_gramSchmidt_le_of_exchangeCondAt`), the first step of the proof of Proposition (1.6).
Chaining these steps and using that every nonzero lattice vector is at least as long as some `b*ᵢ`
gives Proposition (1.11): for `b : Fin (n + 1) → E` and every nonzero `x` in the integer span of
`b`, `‖b₀‖² ≤ (4/(4δ-1))ⁿ ‖x‖²` (`Cslib.Algorithms.LatticeReduction.IsReduced.norm_sq_le`).
For `δ = 3/4` this is `‖b₀‖ ≤ 2^{n/2} ‖x‖`
(`Cslib.Algorithms.LatticeReduction.IsReduced.norm_le_sqrt_two_pow_mul`), i.e. `b₀` approximates
the shortest nonzero lattice vector within a factor `2^{(d-1)/2}` in dimension `d = n + 1`.

The statements hold in an arbitrary real inner product space and do not assume that `b` is
linearly independent. The source works with `b` a basis of a lattice in `ℝⁿ`.

## Main definitions

* `Cslib.Algorithms.LatticeReduction.IsSizeReduced`: condition (1.4).
* `Cslib.Algorithms.LatticeReduction.ExchangeCondAt`: condition (1.5) with parameter `δ`.
* `Cslib.Algorithms.LatticeReduction.IsReduced`: `δ`-reduced bases.

## Main results

* `Cslib.Algorithms.LatticeReduction.IsReduced.norm_sq_le`: Proposition (1.11) for a general
  `δ ∈ (1/4, 1]`.
* `Cslib.Algorithms.LatticeReduction.IsReduced.norm_le_sqrt_two_pow_mul`: the case `δ = 3/4`.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- Size reduction, condition (1.4) of [LenstraLenstraLovasz1982]: `|μᵢⱼ| ≤ 1/2` for `j < i`. -/
@[expose] def IsSizeReduced (b : Fin n → E) : Prop :=
  ∀ i j, j < i → |gramSchmidtCoeff ℝ b i j| ≤ 1 / 2

/-- The exchange condition (1.5) of [LenstraLenstraLovasz1982] with parameter `δ` in place of
`3/4`, at indices `i` and `j`: `δ ‖b*ᵢ‖² ≤ ‖b*ⱼ + μⱼᵢ b*ᵢ‖²`. It is used at `j = i + 1`. -/
@[expose] def ExchangeCondAt (δ : ℝ) (b : Fin n → E) (i j : Fin n) : Prop :=
  δ * ‖gramSchmidt ℝ b i‖ ^ 2 ≤
    ‖gramSchmidt ℝ b j + gramSchmidtCoeff ℝ b j i • gramSchmidt ℝ b i‖ ^ 2

/-- A `δ`-reduced family ([LenstraLenstraLovasz1982], (1.4)–(1.5)): size reduced, with the
exchange condition at every pair of consecutive indices. -/
structure IsReduced (δ : ℝ) (b : Fin n → E) : Prop where
  /-- Condition (1.4). -/
  sizeReduced : IsSizeReduced b
  /-- Condition (1.5) at every pair of consecutive indices. -/
  exchange : ∀ i j : Fin n, (j : ℕ) = i + 1 → ExchangeCondAt δ b i j

/-- Pythagoras for the vector `b*ⱼ + μ b*ᵢ` with `i < j`. -/
theorem norm_sq_gramSchmidt_add_smul (b : Fin n → E) {i j : Fin n} (hij : i < j) (μ : ℝ) :
    ‖gramSchmidt ℝ b j + μ • gramSchmidt ℝ b i‖ ^ 2 =
      ‖gramSchmidt ℝ b j‖ ^ 2 + μ ^ 2 * ‖gramSchmidt ℝ b i‖ ^ 2 := by
  have h0 : inner ℝ (gramSchmidt ℝ b j) (μ • gramSchmidt ℝ b i) = 0 := by
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (ne_of_gt hij), mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [norm_smul, Real.norm_eq_abs] at h
  rw [sq, h, ← sq_abs μ]
  ring

/-- The first step of the proof of (1.6) in [LenstraLenstraLovasz1982], for `δ > 1/4`: size
reduction and the exchange condition give `‖b*ᵢ‖² ≤ 4/(4δ-1) · ‖b*ⱼ‖²`. -/
theorem norm_sq_gramSchmidt_le_of_exchangeCondAt {δ : ℝ} (hδ : 1 / 4 < δ) {b : Fin n → E}
    {i j : Fin n} (hij : i < j) (hsize : |gramSchmidtCoeff ℝ b j i| ≤ 1 / 2)
    (hex : ExchangeCondAt δ b i j) :
    ‖gramSchmidt ℝ b i‖ ^ 2 ≤ 4 / (4 * δ - 1) * ‖gramSchmidt ℝ b j‖ ^ 2 := by
  unfold ExchangeCondAt at hex
  rw [norm_sq_gramSchmidt_add_smul b hij] at hex
  have hμ : gramSchmidtCoeff ℝ b j i ^ 2 ≤ 1 / 4 := by
    have := sq_abs (gramSchmidtCoeff ℝ b j i)
    nlinarith [abs_nonneg (gramSchmidtCoeff ℝ b j i)]
  have hpos : 0 < 4 * δ - 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [sq_nonneg ‖gramSchmidt ℝ b i‖, sq_nonneg ‖gramSchmidt ℝ b j‖,
    mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖gramSchmidt ℝ b i‖)]

/-- Iterating the previous step: `‖b*ⱼ‖² ≤ (4/(4δ-1))ᵏ ‖b*ⱼ₊ₖ‖²` in a `δ`-reduced family. -/
theorem IsReduced.norm_sq_gramSchmidt_chain {δ : ℝ} {b : Fin n → E} (hb : IsReduced δ b)
    (hδ : 1 / 4 < δ) (j : Fin n) :
    ∀ (k : ℕ) (hk : (j : ℕ) + k < n),
      ‖gramSchmidt ℝ b j‖ ^ 2 ≤ (4 / (4 * δ - 1)) ^ k * ‖gramSchmidt ℝ b ⟨j + k, hk⟩‖ ^ 2 := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    have hk' : (j : ℕ) + k < n := by omega
    have hlt : (⟨j + k, hk'⟩ : Fin n) < ⟨j + (k + 1), hk⟩ := by
      rw [Fin.mk_lt_mk]; omega
    have hstep := norm_sq_gramSchmidt_le_of_exchangeCondAt hδ hlt
      (hb.sizeReduced _ _ hlt) (hb.exchange _ _ (by simp; omega))
    have hα : 0 ≤ (4 / (4 * δ - 1)) ^ k := pow_nonneg (by
      apply div_nonneg <;> linarith) k
    calc ‖gramSchmidt ℝ b j‖ ^ 2
        ≤ (4 / (4 * δ - 1)) ^ k * ‖gramSchmidt ℝ b ⟨j + k, hk'⟩‖ ^ 2 := ih hk'
      _ ≤ (4 / (4 * δ - 1)) ^ k *
            (4 / (4 * δ - 1) * ‖gramSchmidt ℝ b ⟨j + (k + 1), hk⟩‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hα
      _ = (4 / (4 * δ - 1)) ^ (k + 1) * ‖gramSchmidt ℝ b ⟨j + (k + 1), hk⟩‖ ^ 2 := by
          rw [pow_succ]; ring

/-- Proposition (1.11) of [LenstraLenstraLovasz1982] for a parameter `δ ∈ (1/4, 1]` in place of
`3/4` (the remark after their (1.5) allows `1/4 < δ < 1`, and the remark after (1.6) replaces the
powers of `2` by powers of `4/(4δ-1)`): if `b : Fin (n + 1) → E` is `δ`-reduced, then
`‖b₀‖² ≤ (4/(4δ-1))ⁿ ‖x‖²` for every nonzero `x` in the integer span of `b`. -/
theorem IsReduced.norm_sq_le {δ : ℝ} {b : Fin (n + 1) → E} (hb : IsReduced δ b)
    (hδ : 1 / 4 < δ) (hδ1 : δ ≤ 1) {x : E} (hx : x ∈ Submodule.span ℤ (Set.range b))
    (hx0 : x ≠ 0) : ‖b 0‖ ^ 2 ≤ (4 / (4 * δ - 1)) ^ n * ‖x‖ ^ 2 := by
  obtain ⟨i, hi⟩ := exists_norm_gramSchmidt_le_of_mem_span_int (𝕜 := ℝ) hx hx0
  have h0 : gramSchmidt ℝ b 0 = b 0 := by
    rw [← bot_eq_zero]; exact gramSchmidt_bot ℝ b
  have hchain := hb.norm_sq_gramSchmidt_chain hδ 0 i (by simp; omega)
  have hidx : (⟨(0 : Fin (n + 1)) + (i : ℕ), by simp; omega⟩ : Fin (n + 1)) = i := by
    ext; simp
  rw [hidx, h0] at hchain
  have hα1 : 1 ≤ 4 / (4 * δ - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hin : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.isLt
  have hsq : ‖gramSchmidt ℝ b i‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hi 2
  calc ‖b 0‖ ^ 2 ≤ (4 / (4 * δ - 1)) ^ (i : ℕ) * ‖gramSchmidt ℝ b i‖ ^ 2 := hchain
    _ ≤ (4 / (4 * δ - 1)) ^ n * ‖x‖ ^ 2 :=
      mul_le_mul (pow_le_pow_right₀ hα1 hin) hsq (sq_nonneg _)
        (pow_nonneg (by linarith) n)

/-- Proposition (1.11) of [LenstraLenstraLovasz1982], `δ = 3/4`: the first vector of a reduced
family `b : Fin (n + 1) → E` satisfies `‖b₀‖ ≤ (√2)ⁿ ‖x‖` for every nonzero `x` in the integer
span of `b`. -/
theorem IsReduced.norm_le_sqrt_two_pow_mul {b : Fin (n + 1) → E} (hb : IsReduced (3 / 4) b)
    {x : E} (hx : x ∈ Submodule.span ℤ (Set.range b)) (hx0 : x ≠ 0) :
    ‖b 0‖ ≤ Real.sqrt 2 ^ n * ‖x‖ := by
  have h := hb.norm_sq_le (by norm_num) (by norm_num) hx hx0
  have h2 : (4 : ℝ) / (4 * (3 / 4) - 1) = 2 := by norm_num
  rw [h2] at h
  have hrhs : (Real.sqrt 2 ^ n * ‖x‖) ^ 2 = 2 ^ n * ‖x‖ ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [← hrhs] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) two_ne_zero).1 h

end Cslib.Algorithms.LatticeReduction
