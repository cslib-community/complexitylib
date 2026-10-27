/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.HermiteInterpolation
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Staged fixed-denominator jet arithmetic and integer Cramer recovery

In the subexponential common-zero counting algorithm of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (§5.4 and Appendix B.2–B.3,
printed pp. 48–50), intermediate polynomials in the Taylor variable `z` and the shared truncation
marker `V` lie in the truncated bivariate algebra `ℚ[V] / (V ^ ℓ)[z] / (z ^ J)`. Rather than
performing rational arithmetic with growing denominators across exponentially many summands, the
algorithm clears denominators in three fixed stages (`Δ = d_den ^ k`, `Γ = Δ ^ (2 * ℓ - 1)`, and
`Ω = Γ ^ m_test`), storing `(J × ℓ)` integer numerator tables and recovering the integer evaluations
`H_s(0)` at `T = 0` by exact integer division of Hermite Cramer determinants.

## Main definitions

* `Cslib.JetTable`: `(J × ℓ)` truncated bivariate jet tables `Fin J → Fin ℓ → R`, equipped with
  `zero`, `const`, `one`, `add`, `neg`, `sub`, `smul`, `conv`, `vPow`, a `CommRing` instance, and
  ring homomorphisms `constRingHom`, `mapRingHom`, `castRingHom`, `ofBivarPoly`, `ofPolyZ`,
  `transpose`, and `ofPolyVPolyZ`.
* `Cslib.JetTable.l1Norm`: integer `ℓ₁` coefficient norm `∑ j, ∑ u, (A j u).natAbs`.
* `Cslib.JetTable.clearedMonomialJet`, `Cslib.JetTable.clearedMonomialSumJet`,
  `Cslib.JetTable.clearedUnivariateJet`, `Cslib.JetTable.parityFactorJet`,
  `Cslib.JetTable.clearedParityFactorJet`, `Cslib.JetTable.signedPrefixJet`: staged
  fixed-denominator numerator constructions for Stages 1–3.
* `Cslib.hermiteCramerNumerator`: integer Cramer determinant `N_H` replacing the `X ^ 0` column of
  `Polynomial.hermiteMatrix` with an `Ω`-scaled integer Taylor jet.

## Main results

* `Cslib.JetTable.l1Norm_add_le`, `Cslib.JetTable.l1Norm_smul`, `Cslib.JetTable.l1Norm_conv_le`:
  triangle inequality, scalar homogeneity, and submultiplicativity under 2D truncated convolution.
* `Cslib.JetTable.cast_clearedMonomialSumJet`, `Cslib.JetTable.l1Norm_clearedMonomialSumJet_le`:
  Stage-1 denominator clearing by `Δ = d_den ^ k` and `M₀ * B₀ ^ k` norm bound.
* `Cslib.JetTable.cast_clearedUnivariateJet`, `Cslib.JetTable.l1Norm_clearedUnivariateJet_le`:
  univariate homogeneous clearing by `Δ ^ D` and `C_amp * B_max ^ D` norm bound.
* `Cslib.JetTable.cast_clearedParityFactorJet`, `Cslib.JetTable.l1Norm_clearedParityFactorJet_le`,
  `Cslib.JetTable.l1Norm_clearedParityFactorJet_le_B1`: Stage-2 denominator clearing by
  `Γ = Δ ^ (2 * ℓ - 1)` and `B₁ = ℓ * E_ℓ * (B + Δ.natAbs + 2) ^ (2 * ℓ - 1)` norm bound.
* `Cslib.JetTable.cast_groupProd_cleared`, `Cslib.JetTable.l1Norm_groupProd_cleared_le`,
  `Cslib.JetTable.cast_signedPrefixJet`, `Cslib.JetTable.l1Norm_signedPrefixJet_le`,
  `Cslib.JetTable.l1Norm_clearedSliceSum_le`: Stage-3 `Ω = Γ ^ m_test` clearing and prefix/slice
  accumulator norm bound `M_star * 2 ^ n * B₁ ^ m_test`.
* `Cslib.hermiteCramerNumerator_eq_mul`, `Cslib.mul_det_hermiteMatrix_dvd_hermiteCramerNumerator`,
  `Cslib.hermiteCramerNumerator_ediv_eq`, `Cslib.hermiteCramerNumerator_emod_two_pow_eq`,
  `Cslib.sum_hermiteCramerNumerator_emod_two_pow_eq`: exact integer Cramer factorization,
  divisibility, Euclidean quotient `N_H / (Ω * D_H) = H_zero` (eq. B.1), and residue recovery
  modulo `2 ^ ℓ`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.4 and Appendix B.2–B.3
-/

@[expose] public section

namespace Cslib

open Finset Polynomial

/-! ### 1. Truncated bivariate jet tables for `R[V] / (V ^ ℓ)[z] / (z ^ J)` -/

/-- A `(J × ℓ)` table of coefficients in `R`, representing a truncated bivariate polynomial in
`R[V] / (V ^ ℓ)[z] / (z ^ J)` via `(j, u) ↦ [z ^ j V ^ u]`. -/
def JetTable (J ℓ : ℕ) (R : Type*) : Type _ :=
  Fin J → Fin ℓ → R

namespace JetTable

section Operations

variable {J ℓ : ℕ} {R : Type*}

@[ext]
theorem ext {A B : JetTable J ℓ R} (h : ∀ j u, A j u = B j u) : A = B :=
  funext fun j => funext fun u => h j u

/-- Explicit constructor casting `Fin J → Fin ℓ → R` to `JetTable J ℓ R` (analogous to
`Matrix.of`). -/
def of (f : Fin J → Fin ℓ → R) : JetTable J ℓ R := f

@[simp]
theorem of_apply (f : Fin J → Fin ℓ → R) (j : Fin J) (u : Fin ℓ) : of f j u = f j u := rfl

/-- The zero `(J × ℓ)` jet table. -/
def zero [Zero R] : JetTable J ℓ R := fun _ _ => 0

/-- Embed a scalar `c : R` at degree `(0, 0)` of a `(J × ℓ)` jet table. -/
def const [Zero R] (c : R) : JetTable J ℓ R :=
  fun j u => if (j : ℕ) = 0 ∧ (u : ℕ) = 0 then c else 0

/-- The multiplicative identity jet table `1 = const 1`. -/
def one [Zero R] [One R] : JetTable J ℓ R := const 1

/-- Pointwise addition of `(J × ℓ)` jet tables. -/
def add [Add R] (A B : JetTable J ℓ R) : JetTable J ℓ R := fun j u => A j u + B j u

/-- Pointwise negation of a `(J × ℓ)` jet table. -/
def neg [Neg R] (A : JetTable J ℓ R) : JetTable J ℓ R := fun j u => -A j u

/-- Pointwise subtraction of `(J × ℓ)` jet tables. -/
def sub [Sub R] (A B : JetTable J ℓ R) : JetTable J ℓ R := fun j u => A j u - B j u

/-- Entrywise scalar multiplication on a `(J × ℓ)` jet table. -/
def smul {S : Type*} [SMul S R] (c : S) (A : JetTable J ℓ R) : JetTable J ℓ R :=
  fun j u => c • A j u

/-- Truncated 2D convolution on `(J × ℓ)` jet tables, implementing multiplication in
`R[V] / (V ^ ℓ)[z] / (z ^ J)`. -/
def conv [Semiring R] (A B : JetTable J ℓ R) : JetTable J ℓ R :=
  fun j u =>
    ∑ j₁ : Fin J, ∑ j₂ ∈ univ.filter (fun j₂ : Fin J => (j₁ : ℕ) + (j₂ : ℕ) = (j : ℕ)),
      ∑ u₁ : Fin ℓ, ∑ u₂ ∈ univ.filter (fun u₂ : Fin ℓ => (u₁ : ℕ) + (u₂ : ℕ) = (u : ℕ)),
        A j₁ u₁ * B j₂ u₂

/-- The monomial `V ^ s` modulo `(z ^ J, V ^ ℓ)` as a `(J × ℓ)` jet table. -/
def vPow [Zero R] [One R] (s : ℕ) : JetTable J ℓ R :=
  fun j u => if (j : ℕ) = 0 ∧ (u : ℕ) = s then 1 else 0

@[simp] theorem zero_apply [Zero R] (j : Fin J) (u : Fin ℓ) : (zero : JetTable J ℓ R) j u = 0 := rfl

@[simp]
theorem const_apply [Zero R] (c : R) (j : Fin J) (u : Fin ℓ) :
    (const c : JetTable J ℓ R) j u = if (j : ℕ) = 0 ∧ (u : ℕ) = 0 then c else 0 := rfl

@[simp]
theorem one_apply [Zero R] [One R] (j : Fin J) (u : Fin ℓ) :
    (one : JetTable J ℓ R) j u = if (j : ℕ) = 0 ∧ (u : ℕ) = 0 then 1 else 0 := rfl

@[simp]
theorem add_apply [Add R] (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    add A B j u = A j u + B j u := rfl

@[simp]
theorem neg_apply [Neg R] (A : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    neg A j u = -A j u := rfl

@[simp]
theorem sub_apply [Sub R] (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    sub A B j u = A j u - B j u := rfl

@[simp]
theorem smul_apply {S : Type*} [SMul S R] (c : S) (A : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    smul c A j u = c • A j u := rfl

@[simp]
theorem vPow_apply [Zero R] [One R] (s : ℕ) (j : Fin J) (u : Fin ℓ) :
    (vPow s : JetTable J ℓ R) j u = if (j : ℕ) = 0 ∧ (u : ℕ) = s then 1 else 0 := rfl

theorem conv_apply [Semiring R] (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    conv A B j u =
      ∑ j₁ : Fin J, ∑ j₂ ∈ univ.filter (fun j₂ : Fin J => (j₁ : ℕ) + (j₂ : ℕ) = (j : ℕ)),
        ∑ u₁ : Fin ℓ, ∑ u₂ ∈ univ.filter (fun u₂ : Fin ℓ => (u₁ : ℕ) + (u₂ : ℕ) = (u : ℕ)),
          A j₁ u₁ * B j₂ u₂ := rfl

end Operations

/-! ### Private index reindexing helpers -/

private theorem conv_eq_prod_sum {J ℓ : ℕ} {R : Type*} [Semiring R]
    (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    conv A B j u =
      ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ,
        if (p₁.1 : ℕ) + (p₂.1 : ℕ) = (j : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (u : ℕ) then
          A p₁.1 p₁.2 * B p₂.1 p₂.2
        else 0 := by
  rw [conv_apply]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun j₁ _ => ?_
  rw [sum_filter, sum_comm]
  refine sum_congr rfl fun j₂ _ => ?_
  by_cases hj : (j₁ : ℕ) + (j₂ : ℕ) = (j : ℕ)
  · simp only [hj, true_and, ↓reduceIte, sum_filter]
  · simp only [hj, false_and, ↓reduceIte, sum_const_zero]

private theorem sum_fin_zero_left {M : Type*} [AddCommMonoid M] {N : ℕ} (k : Fin N)
    (f : Fin N → M) :
    (∑ a : Fin N, ∑ b ∈ univ.filter (fun b : Fin N => (a : ℕ) + (b : ℕ) = (k : ℕ)),
      if (a : ℕ) = 0 then f b else 0) = f k := by
  let z : Fin N := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  rw [Fintype.sum_eq_single z]
  · simp only [z, ↓reduceIte, Nat.zero_add, sum_filter]
    rw [Fintype.sum_eq_single k]
    · simp only [↓reduceIte]
    · intro b hb
      have hne : (b : ℕ) ≠ (k : ℕ) := fun h => hb (Fin.ext h)
      simp only [hne, ↓reduceIte]
  · intro a ha
    have hne : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
    simp only [hne, ↓reduceIte, sum_const_zero]

private theorem sum_fin_zero_right {M : Type*} [AddCommMonoid M] {N : ℕ} (k : Fin N)
    (f : Fin N → M) :
    (∑ a : Fin N, ∑ b ∈ univ.filter (fun b : Fin N => (a : ℕ) + (b : ℕ) = (k : ℕ)),
      if (b : ℕ) = 0 then f a else 0) = f k := by
  let z : Fin N := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  rw [Fintype.sum_eq_single k]
  · simp only [sum_filter]
    rw [Fintype.sum_eq_single z]
    · simp only [z, Nat.add_zero, ↓reduceIte]
    · intro b hb
      have hne : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp only [hne, ↓reduceIte, ite_self]
  · intro a ha
    refine sum_eq_zero fun b hb => ?_
    simp only [mem_filter] at hb
    have hne : (b : ℕ) ≠ 0 := fun hb0 => ha (Fin.ext (by omega))
    simp only [hne, ↓reduceIte]

private theorem sum_prod_assoc_left {J ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (p₁ p₂ p₃ q : Fin J × Fin ℓ) (x : M) :
    (∑ p₁₂ : Fin J × Fin ℓ,
      if (p₁₂.1 : ℕ) + (p₃.1 : ℕ) = (q.1 : ℕ) ∧ (p₁₂.2 : ℕ) + (p₃.2 : ℕ) = (q.2 : ℕ) then
        if (p₁.1 : ℕ) + (p₂.1 : ℕ) = (p₁₂.1 : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (p₁₂.2 : ℕ) then x
        else 0
      else 0) =
      if (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (q.1 : ℕ) ∧
          (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (q.2 : ℕ) then x else 0 := by
  by_cases h : (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (q.1 : ℕ) ∧
      (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (q.2 : ℕ)
  · let p₁₂₀ : Fin J × Fin ℓ :=
      (⟨(p₁.1 : ℕ) + (p₂.1 : ℕ), by omega⟩, ⟨(p₁.2 : ℕ) + (p₂.2 : ℕ), by omega⟩)
    rw [Fintype.sum_eq_single p₁₂₀]
    · simp only [p₁₂₀, h.1, h.2, and_self, ↓reduceIte]
    · intro p₁₂ hp₁₂
      have hne : ¬((p₁.1 : ℕ) + (p₂.1 : ℕ) = (p₁₂.1 : ℕ) ∧
          (p₁.2 : ℕ) + (p₂.2 : ℕ) = (p₁₂.2 : ℕ)) :=
        fun ⟨h1, h2⟩ => hp₁₂ (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))
      simp only [hne, ↓reduceIte, ite_self]
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun p₁₂ _ => ?_
    split_ifs with h1 h2
    · exfalso
      exact h ⟨by omega, by omega⟩
    · rfl
    · rfl

private theorem sum_prod_assoc_right {J ℓ : ℕ} {M : Type*} [AddCommMonoid M]
    (p₁ p₂ p₃ q : Fin J × Fin ℓ) (x : M) :
    (∑ p₂₃ : Fin J × Fin ℓ,
      if (p₁.1 : ℕ) + (p₂₃.1 : ℕ) = (q.1 : ℕ) ∧ (p₁.2 : ℕ) + (p₂₃.2 : ℕ) = (q.2 : ℕ) then
        if (p₂.1 : ℕ) + (p₃.1 : ℕ) = (p₂₃.1 : ℕ) ∧ (p₂.2 : ℕ) + (p₃.2 : ℕ) = (p₂₃.2 : ℕ) then x
        else 0
      else 0) =
      if (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (q.1 : ℕ) ∧
          (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (q.2 : ℕ) then x else 0 := by
  by_cases h : (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (q.1 : ℕ) ∧
      (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (q.2 : ℕ)
  · let p₂₃₀ : Fin J × Fin ℓ :=
      (⟨(p₂.1 : ℕ) + (p₃.1 : ℕ), by omega⟩, ⟨(p₂.2 : ℕ) + (p₃.2 : ℕ), by omega⟩)
    rw [Fintype.sum_eq_single p₂₃₀]
    · have h' : (p₁.1 : ℕ) + ((p₂.1 : ℕ) + (p₃.1 : ℕ)) = (q.1 : ℕ) ∧
          (p₁.2 : ℕ) + ((p₂.2 : ℕ) + (p₃.2 : ℕ)) = (q.2 : ℕ) := ⟨by omega, by omega⟩
      simp only [p₂₃₀, h.1, h.2, h'.1, h'.2, and_self, ↓reduceIte]
    · intro p₂₃ hp₂₃
      have hne : ¬((p₂.1 : ℕ) + (p₃.1 : ℕ) = (p₂₃.1 : ℕ) ∧
          (p₂.2 : ℕ) + (p₃.2 : ℕ) = (p₂₃.2 : ℕ)) :=
        fun ⟨h1, h2⟩ => hp₂₃ (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))
      simp only [hne, ↓reduceIte, ite_self]
  · simp only [h, ↓reduceIte]
    refine sum_eq_zero fun p₂₃ _ => ?_
    split_ifs with h1 h2
    · exfalso
      exact h ⟨by omega, by omega⟩
    · rfl
    · rfl

private theorem sum_fin_filter_add_eq_antidiagonal {M : Type*} [AddCommMonoid M] {N : ℕ}
    (k : Fin N) (f : ℕ → ℕ → M) :
    (∑ a : Fin N, ∑ b ∈ univ.filter (fun b : Fin N => (a : ℕ) + (b : ℕ) = (k : ℕ)),
      f (a : ℕ) (b : ℕ)) =
      ∑ x ∈ antidiagonal (k : ℕ), f x.1 x.2 := by
  simp only [sum_filter]
  rw [← sum_product', ← sum_filter]
  refine sum_bij (fun ab _ => ((ab.1 : ℕ), (ab.2 : ℕ))) ?_ ?_ ?_ fun _ _ => rfl
  · intro ab hab
    simp only [mem_filter] at hab
    exact mem_antidiagonal.mpr hab.2
  · intro ab₁ _ ab₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro x hx
    have hsum : x.1 + x.2 = (k : ℕ) := mem_antidiagonal.mp hx
    refine ⟨((⟨x.1, by omega⟩ : Fin N), (⟨x.2, by omega⟩ : Fin N)), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_univ, and_self, hsum]

/-! ### Ring structure and homomorphisms on `JetTable` -/

section CommRing

variable {J ℓ : ℕ} {R : Type*} [CommRing R]

theorem const_conv (c : R) (A : JetTable J ℓ R) : conv (const c) A = smul c A := by
  ext j u
  rw [conv_apply, smul_apply]
  have inner_u : ∀ j₁ j₂ : Fin J,
      (∑ u₁ : Fin ℓ, ∑ u₂ ∈ univ.filter (fun u₂ : Fin ℓ => (u₁ : ℕ) + (u₂ : ℕ) = (u : ℕ)),
        (const c : JetTable J ℓ R) j₁ u₁ * A j₂ u₂) =
        if (j₁ : ℕ) = 0 then c * A j₂ u else 0 := by
    intro j₁ j₂
    by_cases hj : (j₁ : ℕ) = 0
    · simp only [const_apply, hj, true_and, ↓reduceIte, ite_mul, zero_mul]
      exact sum_fin_zero_left u (fun u₂ => c * A j₂ u₂)
    · simp only [const_apply, hj, false_and, ↓reduceIte, zero_mul, sum_const_zero]
  simp only [inner_u]
  rw [sum_fin_zero_left j (fun j₂ => c * A j₂ u), smul_eq_mul]

theorem conv_const (A : JetTable J ℓ R) (c : R) : conv A (const c) = smul c A := by
  ext j u
  rw [conv_apply, smul_apply]
  have inner_u : ∀ j₁ j₂ : Fin J,
      (∑ u₁ : Fin ℓ, ∑ u₂ ∈ univ.filter (fun u₂ : Fin ℓ => (u₁ : ℕ) + (u₂ : ℕ) = (u : ℕ)),
        A j₁ u₁ * (const c : JetTable J ℓ R) j₂ u₂) =
        if (j₂ : ℕ) = 0 then A j₁ u * c else 0 := by
    intro j₁ j₂
    by_cases hj : (j₂ : ℕ) = 0
    · simp only [const_apply, hj, true_and, ↓reduceIte, mul_ite, mul_zero]
      exact sum_fin_zero_right u (fun u₁ => A j₁ u₁ * c)
    · simp only [const_apply, hj, false_and, ↓reduceIte, mul_zero, sum_const_zero]
  simp only [inner_u]
  rw [sum_fin_zero_right j (fun j₁ => A j₁ u * c), smul_eq_mul, mul_comm]

theorem one_conv (A : JetTable J ℓ R) : conv one A = A := by
  rw [one, const_conv]
  ext j u
  simp only [smul_apply, one_smul]

theorem conv_one (A : JetTable J ℓ R) : conv A one = A := by
  rw [one, conv_const]
  ext j u
  simp only [smul_apply, one_smul]

theorem zero_conv (A : JetTable J ℓ R) : conv zero A = zero := by
  ext j u
  simp only [conv_apply, zero_apply, zero_mul, sum_const_zero]

theorem conv_zero (A : JetTable J ℓ R) : conv A zero = zero := by
  ext j u
  simp only [conv_apply, zero_apply, mul_zero, sum_const_zero]

theorem conv_add (A B C : JetTable J ℓ R) : conv A (add B C) = add (conv A B) (conv A C) := by
  ext j u
  simp only [conv_apply, add_apply, mul_add, sum_add_distrib]

theorem add_conv (A B C : JetTable J ℓ R) : conv (add A B) C = add (conv A C) (conv B C) := by
  ext j u
  simp only [conv_apply, add_apply, add_mul, sum_add_distrib]

theorem conv_comm (A B : JetTable J ℓ R) : conv A B = conv B A := by
  ext j u
  rw [conv_eq_prod_sum, conv_eq_prod_sum, sum_comm]
  refine sum_congr rfl fun p₂ _ => sum_congr rfl fun p₁ _ => ?_
  by_cases h : (p₁.1 : ℕ) + (p₂.1 : ℕ) = (j : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (u : ℕ)
  · have h' : (p₂.1 : ℕ) + (p₁.1 : ℕ) = (j : ℕ) ∧ (p₂.2 : ℕ) + (p₁.2 : ℕ) = (u : ℕ) :=
      ⟨by omega, by omega⟩
    simp only [h, h', and_self, ↓reduceIte, mul_comm]
  · have h' : ¬((p₂.1 : ℕ) + (p₁.1 : ℕ) = (j : ℕ) ∧ (p₂.2 : ℕ) + (p₁.2 : ℕ) = (u : ℕ)) :=
      by omega
    simp only [h, h', ↓reduceIte]

theorem conv_assoc (A B C : JetTable J ℓ R) : conv (conv A B) C = conv A (conv B C) := by
  ext j u
  have lhs_eq : conv (conv A B) C j u =
      ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ, ∑ p₃ : Fin J × Fin ℓ,
        if (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (j : ℕ) ∧
            (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (u : ℕ) then
          A p₁.1 p₁.2 * B p₂.1 p₂.2 * C p₃.1 p₃.2
        else 0 := by
    rw [conv_eq_prod_sum]
    simp only [conv_eq_prod_sum, sum_mul, ite_mul, zero_mul, ite_sum_zero]
    rw [sum_comm]
    trans ∑ p₃ : Fin J × Fin ℓ, ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ,
        ∑ p₁₂ : Fin J × Fin ℓ,
          if (p₁₂.1 : ℕ) + (p₃.1 : ℕ) = (j : ℕ) ∧ (p₁₂.2 : ℕ) + (p₃.2 : ℕ) = (u : ℕ) then
            if (p₁.1 : ℕ) + (p₂.1 : ℕ) = (p₁₂.1 : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (p₁₂.2 : ℕ) then
              A p₁.1 p₁.2 * B p₂.1 p₂.2 * C p₃.1 p₃.2
            else 0
          else 0
    · refine sum_congr rfl fun p₃ _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun p₁ _ => sum_comm
    · trans ∑ p₃ : Fin J × Fin ℓ, ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ,
          if (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (j : ℕ) ∧
              (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (u : ℕ) then
            A p₁.1 p₁.2 * B p₂.1 p₂.2 * C p₃.1 p₃.2
          else 0
      · exact sum_congr rfl fun p₃ _ => sum_congr rfl fun p₁ _ => sum_congr rfl fun p₂ _ =>
          sum_prod_assoc_left p₁ p₂ p₃ (j, u) _
      · rw [sum_comm]
        exact sum_congr rfl fun p₁ _ => sum_comm
  have rhs_eq : conv A (conv B C) j u =
      ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ, ∑ p₃ : Fin J × Fin ℓ,
        if (p₁.1 : ℕ) + (p₂.1 : ℕ) + (p₃.1 : ℕ) = (j : ℕ) ∧
            (p₁.2 : ℕ) + (p₂.2 : ℕ) + (p₃.2 : ℕ) = (u : ℕ) then
          A p₁.1 p₁.2 * (B p₂.1 p₂.2 * C p₃.1 p₃.2)
        else 0 := by
    rw [conv_eq_prod_sum]
    simp only [conv_eq_prod_sum, mul_sum, mul_ite, mul_zero, ite_sum_zero]
    refine sum_congr rfl fun p₁ _ => ?_
    trans ∑ p₂ : Fin J × Fin ℓ, ∑ p₃ : Fin J × Fin ℓ, ∑ p₂₃ : Fin J × Fin ℓ,
        if (p₁.1 : ℕ) + (p₂₃.1 : ℕ) = (j : ℕ) ∧ (p₁.2 : ℕ) + (p₂₃.2 : ℕ) = (u : ℕ) then
          if (p₂.1 : ℕ) + (p₃.1 : ℕ) = (p₂₃.1 : ℕ) ∧ (p₂.2 : ℕ) + (p₃.2 : ℕ) = (p₂₃.2 : ℕ) then
            A p₁.1 p₁.2 * (B p₂.1 p₂.2 * C p₃.1 p₃.2)
          else 0
        else 0
    · rw [sum_comm]
      exact sum_congr rfl fun p₂ _ => sum_comm
    · exact sum_congr rfl fun p₂ _ => sum_congr rfl fun p₃ _ =>
        sum_prod_assoc_right p₁ p₂ p₃ (j, u) _
  rw [lhs_eq, rhs_eq]
  refine sum_congr rfl fun p₁ _ => sum_congr rfl fun p₂ _ => sum_congr rfl fun p₃ _ => ?_
  split_ifs
  · exact mul_assoc _ _ _
  · rfl

instance instCommRing : CommRing (JetTable J ℓ R) where
  zero := zero
  one := one
  add := add
  neg := neg
  sub := sub
  mul := conv
  nsmul := fun n A => smul n A
  zsmul := fun n A => smul n A
  add_assoc := fun A B C => ext fun j u => add_assoc (A j u) (B j u) (C j u)
  zero_add := fun A => ext fun j u => zero_add (A j u)
  add_zero := fun A => ext fun j u => add_zero (A j u)
  add_comm := fun A B => ext fun j u => add_comm (A j u) (B j u)
  nsmul_zero := fun A => ext fun j u => zero_smul ℕ (A j u)
  nsmul_succ := fun n A => ext fun j u => succ_nsmul (A j u) n
  zsmul_zero' := fun A => ext fun j u => zero_smul ℤ (A j u)
  zsmul_succ' := fun n A => ext fun j u => SubNegMonoid.zsmul_succ' n (A j u)
  zsmul_neg' := fun n A => ext fun j u => SubNegMonoid.zsmul_neg' n (A j u)
  sub_eq_add_neg := fun A B => ext fun j u => sub_eq_add_neg (A j u) (B j u)
  neg_add_cancel := fun A => ext fun j u => neg_add_cancel (A j u)
  mul_assoc := conv_assoc
  one_mul := one_conv
  mul_one := conv_one
  zero_mul := zero_conv
  mul_zero := conv_zero
  left_distrib := conv_add
  right_distrib := add_conv
  mul_comm := conv_comm

@[simp] theorem coe_zero (j : Fin J) (u : Fin ℓ) : (0 : JetTable J ℓ R) j u = 0 := rfl
@[simp] theorem one_eq_const : (1 : JetTable J ℓ R) = const 1 := rfl
@[simp]
theorem coe_add (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (A + B : JetTable J ℓ R) j u = A j u + B j u := rfl
@[simp]
theorem coe_neg (A : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (-A : JetTable J ℓ R) j u = -A j u := rfl
@[simp]
theorem coe_sub (A B : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (A - B : JetTable J ℓ R) j u = A j u - B j u := rfl
@[simp]
theorem coe_nsmul (n : ℕ) (A : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (n • A : JetTable J ℓ R) j u = n • A j u := rfl
@[simp]
theorem coe_zsmul (n : ℤ) (A : JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (n • A : JetTable J ℓ R) j u = n • A j u := rfl

theorem mul_eq_conv (A B : JetTable J ℓ R) : A * B = conv A B := rfl

@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (F : ι → JetTable J ℓ R) (j : Fin J) (u : Fin ℓ) :
    (∑ i ∈ s, F i : JetTable J ℓ R) j u = ∑ i ∈ s, F i j u := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => simp only [sum_insert ha, coe_add, ih]

/-- Scalar embedding `c ↦ const c` as a ring homomorphism `R →+* JetTable J ℓ R`. -/
def constRingHom (J ℓ : ℕ) (R : Type*) [CommRing R] : R →+* JetTable J ℓ R where
  toFun := const
  map_one' := rfl
  map_mul' a b := by
    ext j u
    rw [mul_eq_conv, const_conv]
    simp only [smul_apply, const_apply, smul_eq_mul, mul_ite, mul_zero]
  map_zero' := ext fun _ _ => by simp only [const_apply, ite_self, coe_zero]
  map_add' a b := ext fun j u => by
    change const (a + b) j u = const a j u + const b j u
    simp only [const_apply]
    split_ifs <;> simp only [add_zero]

theorem const_mul (c : R) (A : JetTable J ℓ R) : const c * A = smul c A := const_conv c A

@[simp]
theorem const_mul_const (a b : R) : (const a : JetTable J ℓ R) * const b = const (a * b) :=
  ((constRingHom J ℓ R).map_mul a b).symm

@[simp]
theorem const_pow (c : R) (n : ℕ) : (const c : JetTable J ℓ R) ^ n = const (c ^ n) :=
  ((constRingHom J ℓ R).map_pow c n).symm

theorem zsmul_eq_const_mul (c : ℤ) (A : JetTable J ℓ R) : c • A = const (c : R) * A := by
  rw [const_mul]
  ext j u
  simp only [coe_zsmul, smul_apply, smul_eq_mul, zsmul_eq_mul]

/-- Apply a ring homomorphism `f : R →+* S` entrywise to a `(J × ℓ)` jet table. -/
def mapRingHom {S : Type*} [CommRing S] (f : R →+* S) :
    JetTable J ℓ R →+* JetTable J ℓ S where
  toFun := fun A => of fun j u => f (A j u)
  map_one' := ext fun j u => by
    simp only [of_apply, one_eq_const, const_apply]
    split_ifs
    · exact f.map_one
    · exact f.map_zero
  map_mul' A B := ext fun j u => by
    change f (conv A B j u) =
      conv (of fun j' u' => f (A j' u')) (of fun j' u' => f (B j' u')) j u
    simp only [conv_apply, of_apply, map_sum, map_mul]
  map_zero' := ext fun _ _ => f.map_zero
  map_add' A B := ext fun j u => f.map_add (A j u) (B j u)

@[simp]
theorem mapRingHom_apply {S : Type*} [CommRing S] (f : R →+* S) (A : JetTable J ℓ R)
    (j : Fin J) (u : Fin ℓ) : mapRingHom f A j u = f (A j u) := rfl

/-- Canonical integer-cast homomorphism `JetTable J ℓ ℤ →+* JetTable J ℓ R` (in particular
`JetTable J ℓ ℤ →+* JetTable J ℓ ℚ` for `R = ℚ`). -/
def castRingHom (R : Type*) [CommRing R] : JetTable J ℓ ℤ →+* JetTable J ℓ R :=
  mapRingHom (Int.castRingHom R)

@[simp]
theorem castRingHom_apply (A : JetTable J ℓ ℤ) (j : Fin J) (u : Fin ℓ) :
    castRingHom R A j u = (A j u : R) := rfl

@[simp]
theorem castRingHom_const (c : ℤ) :
    castRingHom R (const c : JetTable J ℓ ℤ) = const (c : R) := by
  ext j u
  simp only [castRingHom_apply, const_apply]
  split_ifs <;> simp only [Int.cast_zero]

@[simp]
theorem castRingHom_vPow (s : ℕ) :
    castRingHom R (vPow s : JetTable J ℓ ℤ) = vPow s := by
  ext j u
  simp only [castRingHom_apply, vPow_apply]
  split_ifs <;> simp only [Int.cast_one, Int.cast_zero]

/-- Quotient extraction homomorphism `R[V][z] →+* JetTable J ℓ R` sending a bivariate polynomial
`p : Polynomial (Polynomial R)` to its low-degree coefficient table
`(j, u) ↦ (p.coeff j).coeff u`. -/
noncomputable def ofBivarPoly (J ℓ : ℕ) {R : Type*} [CommRing R] :
    Polynomial (Polynomial R) →+* JetTable J ℓ R where
  toFun := fun p => of fun j u => (p.coeff j).coeff u
  map_one' := ext fun j u => by
    simp only [of_apply, one_eq_const, const_apply]
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, true_and, coeff_one_zero]
      by_cases hu : (u : ℕ) = 0
      · simp only [hu, ↓reduceIte, coeff_one_zero]
      · simp only [hu, ↓reduceIte, coeff_one]
    · simp only [hj, false_and, ↓reduceIte, coeff_one, coeff_zero]
  map_mul' p q := ext fun j u => by
    change ((p * q).coeff j).coeff u =
      conv (of fun j' u' => (p.coeff j').coeff u') (of fun j' u' => (q.coeff j').coeff u') j u
    rw [conv_apply]
    dsimp only [of]
    rw [coeff_mul, finsetSum_coeff]
    simp only [coeff_mul]
    rw [← sum_fin_filter_add_eq_antidiagonal j
      (fun j₁ j₂ => ∑ uu ∈ antidiagonal (u : ℕ),
        (p.coeff j₁).coeff uu.1 * (q.coeff j₂).coeff uu.2)]
    exact sum_congr rfl fun j₁ _ => sum_congr rfl fun j₂ _ =>
      (sum_fin_filter_add_eq_antidiagonal u
        (fun u₁ u₂ => (p.coeff j₁).coeff u₁ * (q.coeff j₂).coeff u₂)).symm
  map_zero' := ext fun _ _ => by simp only [of_apply, coeff_zero, coe_zero]
  map_add' p q := ext fun j u => by
    change ((p + q).coeff j).coeff u = (p.coeff j).coeff u + (q.coeff j).coeff u
    simp only [coeff_add]

@[simp]
theorem ofBivarPoly_apply (p : Polynomial (Polynomial R)) (j : Fin J) (u : Fin ℓ) :
    ofBivarPoly J ℓ p j u = (p.coeff j).coeff u := rfl

/-- Embed a univariate `z`-polynomial `p : R[X]` into `JetTable J ℓ R` along `V ^ 0`. -/
noncomputable def ofPolyZ (J ℓ : ℕ) {R : Type*} [CommRing R] :
    Polynomial R →+* JetTable J ℓ R :=
  (ofBivarPoly J ℓ).comp (Polynomial.mapRingHom Polynomial.C)

@[simp]
theorem ofPolyZ_apply (p : Polynomial R) (j : Fin J) (u : Fin ℓ) :
    ofPolyZ J ℓ p j u = if (u : ℕ) = 0 then p.coeff j else 0 := by
  simp only [ofPolyZ, RingHom.coe_comp, Function.comp_apply, ofBivarPoly_apply,
    coe_mapRingHom, coeff_map, coeff_C]

/-- Transpose homomorphism `JetTable ℓ J R →+* JetTable J ℓ R` swapping the two table indices
`(u, j) ↔ (j, u)`. -/
def transpose {J ℓ : ℕ} {R : Type*} [CommRing R] :
    JetTable ℓ J R →+* JetTable J ℓ R where
  toFun A := of fun j u => A u j
  map_one' := ext fun j u => by
    simp only [of_apply, one_eq_const, const_apply, and_comm]
  map_mul' A B := ext fun j u => by
    change (A * B) u j = (of (fun j' u' => A u' j') * of (fun j' u' => B u' j')) j u
    rw [mul_eq_conv, mul_eq_conv, conv_apply, conv_apply]
    simp only [of_apply]
    trans ∑ u₁ : Fin ℓ, ∑ j₁ : Fin J,
      ∑ j₂ ∈ univ.filter (fun j₂ : Fin J => (j₁ : ℕ) + (j₂ : ℕ) = (j : ℕ)),
        ∑ u₂ ∈ univ.filter (fun u₂ : Fin ℓ => (u₁ : ℕ) + (u₂ : ℕ) = (u : ℕ)),
          A u₁ j₁ * B u₂ j₂
    · refine sum_congr rfl fun u₁ _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun j₁ _ => sum_comm
    · rw [sum_comm]
      exact sum_congr rfl fun j₁ _ => sum_comm
  map_zero' := ext fun _ _ => by simp only [of_apply, coe_zero]
  map_add' _ _ := ext fun _ _ => by simp only [of_apply, coe_add]

@[simp]
theorem transpose_apply {J ℓ : ℕ} {R : Type*} [CommRing R]
    (A : JetTable ℓ J R) (j : Fin J) (u : Fin ℓ) :
    transpose A j u = A u j :=
  rfl

/-- Quotient extraction homomorphism `R[z][V] →+* JetTable J ℓ R` sending a bivariate polynomial
`Q : Polynomial (Polynomial R)` (outer variable `V`, inner variable `z`) to its `(J × ℓ)`
coefficient table `(j, u) ↦ (Q.coeff u).coeff j`, obtained by composing `ofBivarPoly ℓ J` with
`transpose`. -/
noncomputable def ofPolyVPolyZ (J ℓ : ℕ) {R : Type*} [CommRing R] :
    Polynomial (Polynomial R) →+* JetTable J ℓ R :=
  transpose.comp (ofBivarPoly ℓ J)

@[simp]
theorem ofPolyVPolyZ_apply {J ℓ : ℕ} {R : Type*} [CommRing R]
    (Q : Polynomial (Polynomial R)) (j : Fin J) (u : Fin ℓ) :
    ofPolyVPolyZ J ℓ Q j u = (Q.coeff u).coeff j := by
  simp only [ofPolyVPolyZ, RingHom.coe_comp, Function.comp_apply, transpose_apply,
    ofBivarPoly_apply]

/-- Embedding a `z`-polynomial `p : Polynomial R` into `R[z][V]` via `Polynomial.C` and extracting
its `(J × ℓ)` table via `ofPolyVPolyZ J ℓ` agrees with `ofPolyZ J ℓ p`. -/
@[simp]
theorem ofPolyVPolyZ_C {J ℓ : ℕ} {R : Type*} [CommRing R] (p : Polynomial R) :
    ofPolyVPolyZ J ℓ (Polynomial.C p) = ofPolyZ J ℓ p := by
  ext j u
  simp only [ofPolyVPolyZ_apply, ofPolyZ_apply, coeff_C]
  split_ifs <;> simp only [coeff_zero]

/-- Extracting `Polynomial.C (Polynomial.C c)` via `ofPolyVPolyZ J ℓ` yields `const c`. -/
theorem ofPolyVPolyZ_C_C {J ℓ : ℕ} {R : Type*} [CommRing R] (c : R) :
    ofPolyVPolyZ J ℓ (Polynomial.C (Polynomial.C c)) = const c := by
  ext j u
  simp only [ofPolyVPolyZ_apply, const_apply, coeff_C]
  by_cases hu : (u : ℕ) = 0
  · simp only [hu, and_true, ↓reduceIte, coeff_C]
  · simp only [hu, and_false, ↓reduceIte, coeff_zero]

/-- Extracting `Polynomial.X ^ s : Polynomial (Polynomial R)` via `ofPolyVPolyZ J ℓ` yields
`vPow s`. -/
@[simp]
theorem ofPolyVPolyZ_X_pow {J ℓ : ℕ} {R : Type*} [CommRing R] (s : ℕ) :
    ofPolyVPolyZ J ℓ ((Polynomial.X : Polynomial (Polynomial R)) ^ s) = vPow s := by
  ext j u
  simp only [ofPolyVPolyZ_apply, vPow_apply, coeff_X_pow]
  by_cases hs : (u : ℕ) = s
  · simp only [hs, and_true, ↓reduceIte, coeff_one]
  · simp only [hs, and_false, ↓reduceIte, coeff_zero]

/-- `ofPolyZ J ℓ (Polynomial.C c)` is `const c`. -/
@[simp]
theorem ofPolyZ_C {J ℓ : ℕ} {R : Type*} [CommRing R] (c : R) :
    ofPolyZ J ℓ (Polynomial.C c) = const c := by
  rw [← ofPolyVPolyZ_C, ofPolyVPolyZ_C_C]

theorem mul_vPow_apply (A : JetTable J ℓ R) (s : ℕ) (j : Fin J) (u : Fin ℓ) :
    (A * (vPow s : JetTable J ℓ R) : JetTable J ℓ R) j u =
      if _h : s ≤ u then A j ⟨(u : ℕ) - s, Nat.lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩
      else 0 := by
  change conv A (vPow s) j u = _
  rw [conv_eq_prod_sum]
  by_cases hs : s ≤ u
  · simp only [hs, ↓reduceDIte]
    let p₁₀ : Fin J × Fin ℓ := (j, ⟨(u : ℕ) - s, Nat.lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩)
    let p₂₀ : Fin J × Fin ℓ := (⟨0, j.pos⟩, ⟨s, Nat.lt_of_le_of_lt hs u.isLt⟩)
    rw [Fintype.sum_eq_single p₁₀]
    · rw [Fintype.sum_eq_single p₂₀]
      · have hsum : (p₁₀.1 : ℕ) + (p₂₀.1 : ℕ) = (j : ℕ) ∧ (p₁₀.2 : ℕ) + (p₂₀.2 : ℕ) = (u : ℕ) :=
          ⟨Nat.add_zero _, Nat.sub_add_cancel hs⟩
        simp only [p₁₀, p₂₀, vPow_apply, hsum.1, hsum.2, and_self, ↓reduceIte, mul_one]
      · intro p₂ hp₂
        by_cases hv : (p₂.1 : ℕ) = 0 ∧ (p₂.2 : ℕ) = s
        · exact False.elim (hp₂ (Prod.ext (Fin.ext hv.1) (Fin.ext hv.2)))
        · simp only [vPow_apply, hv, ↓reduceIte, mul_zero, ite_self]
    · intro p₁ hp₁
      refine sum_eq_zero fun p₂ _ => ?_
      by_cases hv : (p₂.1 : ℕ) = 0 ∧ (p₂.2 : ℕ) = s
      · have hne : ¬((p₁.1 : ℕ) + (p₂.1 : ℕ) = (j : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (u : ℕ)) :=
          fun ⟨h1, h2⟩ => hp₁ (Prod.ext (Fin.ext (by
            change (p₁.1 : ℕ) = (j : ℕ)
            omega)) (Fin.ext (by
            change (p₁.2 : ℕ) = (u : ℕ) - s
            omega)))
        simp only [hne, ↓reduceIte]
      · simp only [vPow_apply, hv, ↓reduceIte, mul_zero, ite_self]
  · simp only [hs, ↓reduceDIte]
    refine sum_eq_zero fun p₁ _ => sum_eq_zero fun p₂ _ => ?_
    by_cases hv : (p₂.1 : ℕ) = 0 ∧ (p₂.2 : ℕ) = s
    · have hne : ¬((p₁.1 : ℕ) + (p₂.1 : ℕ) = (j : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (u : ℕ)) :=
        by omega
      simp only [hne, ↓reduceIte]
    · simp only [vPow_apply, hv, ↓reduceIte, mul_zero, ite_self]

end CommRing

/-! ### 2. Integer `ℓ₁` coefficient norm on `JetTable` -/

section L1Norm

variable {J ℓ : ℕ}

/-- The integer `ℓ₁` coefficient norm `‖A‖₁ = ∑ j, ∑ u, |A j u|` on `JetTable J ℓ ℤ`
([OpenAI2026ETH, Appendix B, p. 47]). -/
def l1Norm (A : JetTable J ℓ ℤ) : ℕ :=
  ∑ j : Fin J, ∑ u : Fin ℓ, (A j u).natAbs

private theorem l1Norm_eq_prod_sum (A : JetTable J ℓ ℤ) :
    l1Norm A = ∑ p : Fin J × Fin ℓ, (A p.1 p.2).natAbs := by
  unfold l1Norm
  exact (Fintype.sum_prod_type fun p : Fin J × Fin ℓ => (A p.1 p.2).natAbs).symm

@[simp]
theorem l1Norm_zero : l1Norm (0 : JetTable J ℓ ℤ) = 0 := by
  simp only [l1Norm, coe_zero, Int.natAbs_zero, sum_const_zero]

theorem natAbs_apply_le_l1Norm (A : JetTable J ℓ ℤ) (j : Fin J) (u : Fin ℓ) :
    (A j u).natAbs ≤ l1Norm A := by
  rw [l1Norm_eq_prod_sum]
  exact single_le_sum (f := fun p : Fin J × Fin ℓ => (A p.1 p.2).natAbs)
    (fun _ _ => Nat.zero_le _) (mem_univ (j, u))

private theorem sum_ite_coord_eq_le (a b : ℕ) (m : ℕ) :
    (∑ p : Fin J × Fin ℓ, if (p.1 : ℕ) = a ∧ (p.2 : ℕ) = b then m else 0) ≤ m := by
  by_cases h : a < J ∧ b < ℓ
  · let p₀ : Fin J × Fin ℓ := (⟨a, h.1⟩, ⟨b, h.2⟩)
    rw [Fintype.sum_eq_single p₀]
    · simp only [p₀, and_self, ↓reduceIte, le_rfl]
    · intro p hp
      have hne : ¬((p.1 : ℕ) = a ∧ (p.2 : ℕ) = b) :=
        fun ⟨h1, h2⟩ => hp (Prod.ext (Fin.ext h1) (Fin.ext h2))
      simp only [hne, ↓reduceIte]
  · refine (sum_eq_zero fun p _ => ?_).trans_le (Nat.zero_le _)
    have hne : ¬((p.1 : ℕ) = a ∧ (p.2 : ℕ) = b) := fun ⟨h1, h2⟩ => h ⟨h1 ▸ p.1.isLt, h2 ▸ p.2.isLt⟩
    simp only [hne, ↓reduceIte]

theorem l1Norm_const_le (c : ℤ) : l1Norm (const c : JetTable J ℓ ℤ) ≤ c.natAbs := by
  rw [l1Norm_eq_prod_sum]
  refine (sum_le_sum fun p _ => ?_).trans (sum_ite_coord_eq_le 0 0 c.natAbs)
  simp only [const_apply]
  split_ifs <;> simp only [Int.natAbs_zero, le_rfl]

theorem l1Norm_const_of_pos (hJ : 0 < J) (hℓ : 0 < ℓ) (c : ℤ) :
    l1Norm (const c : JetTable J ℓ ℤ) = c.natAbs := by
  apply le_antisymm (l1Norm_const_le c)
  simpa only [const_apply, and_self, ↓reduceIte] using
    natAbs_apply_le_l1Norm (const c) ⟨0, hJ⟩ ⟨0, hℓ⟩

theorem l1Norm_one_le : l1Norm (1 : JetTable J ℓ ℤ) ≤ 1 := l1Norm_const_le 1

@[simp]
theorem l1Norm_neg (A : JetTable J ℓ ℤ) : l1Norm (-A) = l1Norm A := by
  simp only [l1Norm, coe_neg, Int.natAbs_neg]

theorem l1Norm_add_le (A B : JetTable J ℓ ℤ) : l1Norm (A + B) ≤ l1Norm A + l1Norm B := by
  simp only [l1Norm, coe_add, ← sum_add_distrib]
  exact sum_le_sum fun j _ => sum_le_sum fun u _ => Int.natAbs_add_le (A j u) (B j u)

theorem l1Norm_sub_le (A B : JetTable J ℓ ℤ) : l1Norm (A - B) ≤ l1Norm A + l1Norm B := by
  rw [sub_eq_add_neg, ← l1Norm_neg B]
  exact l1Norm_add_le A (-B)

theorem l1Norm_smul (c : ℤ) (A : JetTable J ℓ ℤ) : l1Norm (c • A) = c.natAbs * l1Norm A := by
  simp only [l1Norm, coe_zsmul, smul_eq_mul, Int.natAbs_mul, mul_sum]

/-- Submultiplicativity of `l1Norm` under truncated 2D convolution:
`‖conv A B‖₁ ≤ ‖A‖₁ * ‖B‖₁` ([OpenAI2026ETH, Appendix B.1–B.2, pp. 47–48]). -/
theorem l1Norm_conv_le (A B : JetTable J ℓ ℤ) :
    l1Norm (conv A B) ≤ l1Norm A * l1Norm B := by
  rw [l1Norm_eq_prod_sum, l1Norm_eq_prod_sum, l1Norm_eq_prod_sum, sum_mul_sum]
  have entry_le : ∀ q : Fin J × Fin ℓ, (conv A B q.1 q.2).natAbs ≤
      ∑ p₁ : Fin J × Fin ℓ, ∑ p₂ : Fin J × Fin ℓ,
        if (q.1 : ℕ) = (p₁.1 : ℕ) + (p₂.1 : ℕ) ∧ (q.2 : ℕ) = (p₁.2 : ℕ) + (p₂.2 : ℕ) then
          (A p₁.1 p₁.2).natAbs * (B p₂.1 p₂.2).natAbs
        else 0 := by
    intro q
    rw [conv_eq_prod_sum]
    refine (Int.natAbs_sum_le _ _).trans (sum_le_sum fun p₁ _ => ?_)
    refine (Int.natAbs_sum_le _ _).trans (sum_le_sum fun p₂ _ => ?_)
    by_cases h1 : (p₁.1 : ℕ) + (p₂.1 : ℕ) = (q.1 : ℕ) ∧ (p₁.2 : ℕ) + (p₂.2 : ℕ) = (q.2 : ℕ)
    · simp only [h1, and_self, ↓reduceIte, Int.natAbs_mul, le_rfl]
    · simp only [h1, ↓reduceIte, Int.natAbs_zero]
      exact Nat.zero_le _
  refine (sum_le_sum fun q _ => entry_le q).trans ?_
  rw [sum_comm]
  refine (sum_congr rfl fun p₁ _ => sum_comm).trans_le ?_
  exact sum_le_sum fun p₁ _ => sum_le_sum fun p₂ _ => sum_ite_coord_eq_le _ _ _

theorem l1Norm_mul_le (A B : JetTable J ℓ ℤ) : l1Norm (A * B) ≤ l1Norm A * l1Norm B :=
  l1Norm_conv_le A B

theorem l1Norm_vPow_le (s : ℕ) : l1Norm (vPow s : JetTable J ℓ ℤ) ≤ 1 := by
  rw [l1Norm_eq_prod_sum]
  refine (sum_le_sum fun p _ => ?_).trans (sum_ite_coord_eq_le 0 s 1)
  simp only [vPow_apply]
  split_ifs <;> simp only [Int.natAbs_one, Int.natAbs_zero, le_rfl]

theorem l1Norm_mul_vPow_le (A : JetTable J ℓ ℤ) (s : ℕ) :
    l1Norm (A * vPow s) ≤ l1Norm A :=
  (l1Norm_mul_le A (vPow s)).trans
    ((Nat.mul_le_mul_left _ (l1Norm_vPow_le s)).trans (Nat.mul_one _).le)

theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (F : ι → JetTable J ℓ ℤ) :
    l1Norm (∑ i ∈ s, F i) ≤ ∑ i ∈ s, l1Norm (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, l1Norm_zero, le_rfl]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (l1Norm_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem l1Norm_prod_le {ι : Type*} (s : Finset ι) (F : ι → JetTable J ℓ ℤ) :
    l1Norm (∏ i ∈ s, F i) ≤ ∏ i ∈ s, l1Norm (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty] using l1Norm_one_le
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1Norm_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem l1Norm_pow_le (A : JetTable J ℓ ℤ) (m : ℕ) : l1Norm (A ^ m) ≤ l1Norm A ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using l1Norm_one_le
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact (l1Norm_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

end L1Norm

/-! ### 3. Staged fixed-denominator clearing and prefix norm bounds (Appendix B.2) -/

section StagedClearing

variable {J ℓ : ℕ} {K : Type*} [CommRing K]

/-- Stage-1 integer numerator for a single monomial `M` of degree `#M ≤ k`, cleared by
`Δ = d_den ^ k` via padding `d_den ^ (k - #M)` ([OpenAI2026ETH, Appendix B.2, p. 48]). -/
def clearedMonomialJet {ι : Type*} (d_den : ℤ) (k : ℕ) (θ_int : ι → JetTable J ℓ ℤ)
    (M : Finset ι) : JetTable J ℓ ℤ :=
  (d_den ^ (k - #M)) • ∏ v ∈ M, θ_int v

/-- Stage-1 integer numerator for a sum of listed monomials of degree at most `k`, cleared by
`Δ = d_den ^ k` ([OpenAI2026ETH, Appendix B.2, p. 48]). -/
def clearedMonomialSumJet {α ι : Type*} (d_den : ℤ) (k : ℕ) (θ_int : ι → JetTable J ℓ ℤ)
    (s : Finset α) (M : α → Finset ι) : JetTable J ℓ ℤ :=
  ∑ m ∈ s, clearedMonomialJet d_den k θ_int (M m)

theorem cast_clearedMonomialJet {ι : Type*} (d_den : ℤ) (k : ℕ)
    (θ_rat : ι → JetTable J ℓ K) (θ_int : ι → JetTable J ℓ ℤ)
    (hθ : ∀ v, d_den • θ_rat v = castRingHom K (θ_int v))
    {M : Finset ι} (hM : #M ≤ k) :
    (d_den ^ k) • (∏ v ∈ M, θ_rat v) = castRingHom K (clearedMonomialJet d_den k θ_int M) := by
  rw [clearedMonomialJet, map_zsmul, map_prod]
  simp only [← hθ]
  rw [← smul_prod, smul_smul, ← pow_add, Nat.sub_add_cancel hM]

/-- **Stage-1 denominator clearing (Appendix B.2, p. 48).** If `d_den • θ_rat v` is represented by
`θ_int v`, then `Δ = d_den ^ k` clears any sum of monomials of degree at most `k`. -/
theorem cast_clearedMonomialSumJet {α ι : Type*} (d_den : ℤ) (k : ℕ)
    (θ_rat : ι → JetTable J ℓ K) (θ_int : ι → JetTable J ℓ ℤ)
    (hθ : ∀ v, d_den • θ_rat v = castRingHom K (θ_int v))
    (s : Finset α) (M : α → Finset ι) (hdeg : ∀ m ∈ s, #(M m) ≤ k) :
    (d_den ^ k) • (∑ m ∈ s, ∏ v ∈ M m, θ_rat v) =
      castRingHom K (clearedMonomialSumJet d_den k θ_int s M) := by
  rw [clearedMonomialSumJet, map_sum, smul_sum]
  exact sum_congr rfl fun m hm => cast_clearedMonomialJet d_den k θ_rat θ_int hθ (hdeg m hm)

theorem l1Norm_clearedMonomialJet_le {ι : Type*} {d_den : ℤ} {k B₀ : ℕ}
    (hd : d_den.natAbs ≤ B₀) {θ_int : ι → JetTable J ℓ ℤ} (hθ : ∀ v, l1Norm (θ_int v) ≤ B₀)
    {M : Finset ι} (hM : #M ≤ k) :
    l1Norm (clearedMonomialJet d_den k θ_int M) ≤ B₀ ^ k := by
  rw [clearedMonomialJet, l1Norm_smul, Int.natAbs_pow]
  have hprod : l1Norm (∏ v ∈ M, θ_int v) ≤ B₀ ^ #M :=
    (l1Norm_prod_le M θ_int).trans ((prod_le_prod fun v _ => hθ v).trans_eq (prod_const B₀))
  calc
    d_den.natAbs ^ (k - #M) * l1Norm (∏ v ∈ M, θ_int v)
      ≤ B₀ ^ (k - #M) * B₀ ^ #M := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hprod
    _ = B₀ ^ k := by rw [← pow_add, Nat.sub_add_cancel hM]

/-- **Stage-1 `ℓ₁`-norm bound (Appendix B.2, p. 48).** When `d_den.natAbs ≤ B₀` and every input jet
`θ_int v` has `ℓ₁`-norm at most `B₀`, a sum of at most `M₀` monomials of degree at most `k` cleared
by `Δ = d_den ^ k` has `ℓ₁`-norm at most `M₀ * B₀ ^ k`. -/
theorem l1Norm_clearedMonomialSumJet_le {α ι : Type*} {d_den : ℤ} {k B₀ M₀ : ℕ}
    (hd : d_den.natAbs ≤ B₀) {θ_int : ι → JetTable J ℓ ℤ} (hθ : ∀ v, l1Norm (θ_int v) ≤ B₀)
    {s : Finset α} (hs : #s ≤ M₀) {M : α → Finset ι} (hdeg : ∀ m ∈ s, #(M m) ≤ k) :
    l1Norm (clearedMonomialSumJet d_den k θ_int s M) ≤ M₀ * B₀ ^ k := by
  calc
    l1Norm (clearedMonomialSumJet d_den k θ_int s M)
      ≤ ∑ m ∈ s, l1Norm (clearedMonomialJet d_den k θ_int (M m)) := l1Norm_sum_le s _
    _ ≤ ∑ _m ∈ s, B₀ ^ k :=
        sum_le_sum fun m hm => l1Norm_clearedMonomialJet_le hd hθ (hdeg m hm)
    _ = #s * B₀ ^ k := sum_const _
    _ ≤ M₀ * B₀ ^ k := Nat.mul_le_mul_right _ hs

/-- Homogeneous `Δ ^ D`-cleared integer evaluation of a degree-`≤ D` univariate polynomial
`∑ u ∈ range (D + 1), a u * Y ^ u` on a `Δ`-cleared jet table `A_int`. -/
def clearedUnivariateJet (Δ : ℤ) (D : ℕ) (a : ℕ → ℤ) (A_int : JetTable J ℓ ℤ) : JetTable J ℓ ℤ :=
  ∑ u ∈ range (D + 1), (a u * Δ ^ (D - u)) • A_int ^ u

/-- **Univariate homogeneous denominator clearing.** If `Δ • L_rat = castRingHom K A_int`, then
`Δ ^ D` clears `∑ u ∈ range (D + 1), a u • L_rat ^ u`. -/
theorem cast_clearedUnivariateJet (Δ : ℤ) (D : ℕ) (a : ℕ → ℤ)
    (L_rat : JetTable J ℓ K) (A_int : JetTable J ℓ ℤ)
    (hL : Δ • L_rat = castRingHom K A_int) :
    (Δ ^ D) • (∑ u ∈ range (D + 1), a u • L_rat ^ u) =
      castRingHom K (clearedUnivariateJet Δ D a A_int) := by
  rw [clearedUnivariateJet, map_sum, smul_sum]
  refine sum_congr rfl fun u hu => ?_
  have huD : u ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hu)
  rw [map_zsmul, map_pow, ← hL]
  have hpow : (Δ • L_rat) ^ u = (Δ ^ u) • L_rat ^ u := by
    rw [zsmul_eq_const_mul, mul_pow, const_pow, ← Int.cast_pow, ← zsmul_eq_const_mul]
  rw [hpow, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel huD, mul_comm]

/-- **Univariate homogeneous `ℓ₁`-norm bound.** If `‖A_int‖₁ ≤ B_max`, `Δ.natAbs ≤ B_max`, and
`∑ u ∈ range (D + 1), |a u| ≤ C_amp`, then
`‖clearedUnivariateJet Δ D a A_int‖₁ ≤ C_amp * B_max ^ D`. -/
theorem l1Norm_clearedUnivariateJet_le {Δ : ℤ} {D B_max C_amp : ℕ} {a : ℕ → ℤ}
    {A_int : JetTable J ℓ ℤ} (hA : l1Norm A_int ≤ B_max) (hΔ : Δ.natAbs ≤ B_max)
    (ha : (∑ u ∈ range (D + 1), (a u).natAbs) ≤ C_amp) :
    l1Norm (clearedUnivariateJet Δ D a A_int) ≤ C_amp * B_max ^ D := by
  calc
    l1Norm (clearedUnivariateJet Δ D a A_int)
      ≤ ∑ u ∈ range (D + 1), l1Norm ((a u * Δ ^ (D - u)) • A_int ^ u) := l1Norm_sum_le _ _
    _ ≤ ∑ u ∈ range (D + 1), (a u).natAbs * B_max ^ D := by
        refine sum_le_sum fun u hu => ?_
        have huD : u ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hu)
        rw [l1Norm_smul, Int.natAbs_mul, Int.natAbs_pow, mul_assoc]
        refine Nat.mul_le_mul_left _ ?_
        calc
          Δ.natAbs ^ (D - u) * l1Norm (A_int ^ u)
            ≤ B_max ^ (D - u) * B_max ^ u :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hΔ _)
                ((l1Norm_pow_le A_int u).trans (Nat.pow_le_pow_left hA _))
          _ = B_max ^ D := by rw [← pow_add, Nat.sub_add_cancel huD]
    _ = (∑ u ∈ range (D + 1), (a u).natAbs) * B_max ^ D := (sum_mul _ _ _).symm
    _ ≤ C_amp * B_max ^ D := Nat.mul_le_mul_right _ ha

/-- The substituted shared-`V` parity factor
`B_i(z, V) = ∑ s < ℓ, (a_s + b_s L) (L (L - 1)) ^ s V ^ s` modulo `(z ^ J, V ^ ℓ)`
([OpenAI2026ETH, §5.3 eq. (5.4) and Appendix B.2, p. 48]). -/
def parityFactorJet (L : JetTable J ℓ K) (a b : Fin ℓ → ℤ) : JetTable J ℓ K :=
  ∑ s : Fin ℓ, (const (a s : K) + b s • L) * (L * (L - 1)) ^ (s : ℕ) * vPow (s : ℕ)

/-- Stage-2 integer numerator `Γ • B_i(z, V)` for `Γ = Δ ^ (2 * ℓ - 1)` and `A_int = Δ • L`,
obtained by clearing `e_s(L)` with `Δ`, `L (L - 1)` with `Δ ^ 2`, and padding term `s` by
`Δ ^ (2 * (ℓ - 1 - s))` ([OpenAI2026ETH, Appendix B.2, pp. 48–49]). -/
def clearedParityFactorJet (Δ : ℤ) (A_int : JetTable J ℓ ℤ) (a b : Fin ℓ → ℤ) : JetTable J ℓ ℤ :=
  ∑ s : Fin ℓ,
    (Δ ^ (2 * (ℓ - 1 - (s : ℕ)))) •
      ((a s • const Δ + b s • A_int) * (A_int * (A_int - const Δ)) ^ (s : ℕ) * vPow (s : ℕ))

/-- **Stage-2 denominator clearing (Appendix B.2, pp. 48–49).** If
`Δ • L_rat = castRingHom K A_int`, then `Γ = Δ ^ (2 * ℓ - 1)` clears `parityFactorJet L_rat a b`. -/
theorem cast_clearedParityFactorJet (Δ : ℤ) (L_rat : JetTable J ℓ K) (A_int : JetTable J ℓ ℤ)
    (hL : Δ • L_rat = castRingHom K A_int) (a b : Fin ℓ → ℤ) :
    (Δ ^ (2 * ℓ - 1)) • parityFactorJet L_rat a b =
      castRingHom K (clearedParityFactorJet Δ A_int a b) := by
  rw [parityFactorJet, clearedParityFactorJet, map_sum, smul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [map_zsmul, map_mul, map_mul, map_pow, map_add, map_zsmul, map_zsmul, map_mul, map_sub,
    castRingHom_const, castRingHom_vPow, ← hL]
  let Ck := constRingHom J ℓ K
  have hc : ∀ x : K, (const x : JetTable J ℓ K) = Ck x := fun _ => rfl
  simp only [zsmul_eq_const_mul, hc, Int.cast_pow, map_pow]
  have hquad_pow : (Ck (Δ : K) * L_rat * (Ck (Δ : K) * L_rat - Ck (Δ : K))) ^ (s : ℕ) =
      (Ck (Δ : K) ^ 2) ^ (s : ℕ) * (L_rat * (L_rat - 1)) ^ (s : ℕ) := by
    rw [← mul_pow]
    congr 1
    ring
  have hpow : Ck (Δ : K) ^ (2 * ℓ - 1) =
      Ck (Δ : K) ^ (2 * (ℓ - 1 - (s : ℕ))) * Ck (Δ : K) * (Ck (Δ : K) ^ 2) ^ (s : ℕ) := by
    rw [← pow_mul, ← pow_succ, ← pow_add]
    congr 1
    omega
  rw [hquad_pow, hpow]
  ring

/-- **Stage-2 `ℓ₁`-norm bound (Appendix B.2, p. 49).** If `‖A_int‖₁ ≤ B` and every linear remainder
`e_s(Y) = a_s + b_s Y` satisfies `|a_s| + |b_s| ≤ E_ℓ`, then
`‖clearedParityFactorJet Δ A_int a b‖₁ ≤ ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1)`. -/
theorem l1Norm_clearedParityFactorJet_le {Δ : ℤ} {B E_ℓ : ℕ} {A_int : JetTable J ℓ ℤ}
    (hA : l1Norm A_int ≤ B) {a b : Fin ℓ → ℤ}
    (he : ∀ s : Fin ℓ, (a s).natAbs + (b s).natAbs ≤ E_ℓ) :
    l1Norm (clearedParityFactorJet Δ A_int a b) ≤
      ℓ * E_ℓ * (B + Δ.natAbs) ^ (2 * ℓ - 1) := by
  let M := B + Δ.natAbs
  have hBM : B ≤ M := Nat.le_add_right B Δ.natAbs
  have hΔM : Δ.natAbs ≤ M := Nat.le_add_left Δ.natAbs B
  calc
    l1Norm (clearedParityFactorJet Δ A_int a b)
      ≤ ∑ s : Fin ℓ, l1Norm ((Δ ^ (2 * (ℓ - 1 - (s : ℕ)))) •
          ((a s • const Δ + b s • A_int) * (A_int * (A_int - const Δ)) ^ (s : ℕ) *
            vPow (s : ℕ))) := l1Norm_sum_le _ _
    _ ≤ ∑ _s : Fin ℓ, E_ℓ * M ^ (2 * ℓ - 1) := by
        refine sum_le_sum fun s _ => ?_
        rw [l1Norm_smul, Int.natAbs_pow]
        have hv : l1Norm ((a s • const Δ + b s • A_int) *
            (A_int * (A_int - const Δ)) ^ (s : ℕ) * vPow (s : ℕ)) ≤
            l1Norm (a s • const Δ + b s • A_int) *
              l1Norm (A_int * (A_int - const Δ)) ^ (s : ℕ) :=
          (l1Norm_mul_vPow_le _ _).trans
            ((l1Norm_mul_le _ _).trans (Nat.mul_le_mul_left _ (l1Norm_pow_le _ _)))
        have hE : l1Norm (a s • const Δ + b s • A_int) ≤ E_ℓ * M := by
          calc
            l1Norm (a s • const Δ + b s • A_int)
              ≤ (a s).natAbs * l1Norm (const Δ) + (b s).natAbs * l1Norm A_int := by
                simpa only [l1Norm_smul] using l1Norm_add_le (a s • const Δ) (b s • A_int)
            _ ≤ (a s).natAbs * M + (b s).natAbs * M :=
                Nat.add_le_add (Nat.mul_le_mul_left _ ((l1Norm_const_le Δ).trans hΔM))
                  (Nat.mul_le_mul_left _ (hA.trans hBM))
            _ ≤ E_ℓ * M := (Nat.add_mul _ _ _).symm ▸ Nat.mul_le_mul_right _ (he s)
        have hH : l1Norm (A_int * (A_int - const Δ)) ≤ M ^ 2 := by
          calc
            l1Norm (A_int * (A_int - const Δ))
              ≤ l1Norm A_int * (l1Norm A_int + l1Norm (const Δ)) :=
                (l1Norm_mul_le _ _).trans (Nat.mul_le_mul_left _ (l1Norm_sub_le _ _))
            _ ≤ M * (B + Δ.natAbs) :=
                Nat.mul_le_mul (hA.trans hBM) (Nat.add_le_add hA (l1Norm_const_le Δ))
            _ = M ^ 2 := (sq M).symm
        calc
          Δ.natAbs ^ (2 * (ℓ - 1 - (s : ℕ))) *
              l1Norm ((a s • const Δ + b s • A_int) *
                (A_int * (A_int - const Δ)) ^ (s : ℕ) * vPow (s : ℕ))
            ≤ M ^ (2 * (ℓ - 1 - (s : ℕ))) * ((E_ℓ * M) * (M ^ 2) ^ (s : ℕ)) :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hΔM _)
                (hv.trans (Nat.mul_le_mul hE (Nat.pow_le_pow_left hH _)))
          _ = E_ℓ * (M ^ (2 * (ℓ - 1 - (s : ℕ))) * M * M ^ (2 * (s : ℕ))) := by
              rw [← pow_mul]
              ring
          _ = E_ℓ * M ^ (2 * ℓ - 1) := by
              congr 1
              rw [← pow_succ, ← pow_add]
              congr 1
              omega
    _ = ℓ * E_ℓ * M ^ (2 * ℓ - 1) := by
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

/-- Specialization of `l1Norm_clearedParityFactorJet_le` to the manuscript's explicit parameter
`B₁ = ℓ * E_ℓ * (B + Δ.natAbs + 2) ^ (2 * ℓ - 1)` ([OpenAI2026ETH, Appendix B.2, p. 49]). -/
theorem l1Norm_clearedParityFactorJet_le_B1 {Δ : ℤ} {B E_ℓ : ℕ} {A_int : JetTable J ℓ ℤ}
    (hA : l1Norm A_int ≤ B) {a b : Fin ℓ → ℤ}
    (he : ∀ s : Fin ℓ, (a s).natAbs + (b s).natAbs ≤ E_ℓ) :
    l1Norm (clearedParityFactorJet Δ A_int a b) ≤
      ℓ * E_ℓ * (B + Δ.natAbs + 2) ^ (2 * ℓ - 1) :=
  (l1Norm_clearedParityFactorJet_le hA he).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ 2) _))

/-- The manuscript's dominance inequality `Γ ≤ B₁` (`Δ.natAbs ^ (2 * ℓ - 1) ≤ B₁`) when `1 ≤ ℓ`
and `1 ≤ E_ℓ` ([OpenAI2026ETH, Appendix B.2, p. 49]). -/
theorem pow_natAbs_le_B1 (Δ : ℤ) (B : ℕ) {ℓ E_ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hE : 1 ≤ E_ℓ) :
    Δ.natAbs ^ (2 * ℓ - 1) ≤ ℓ * E_ℓ * (B + Δ.natAbs + 2) ^ (2 * ℓ - 1) := by
  calc
    Δ.natAbs ^ (2 * ℓ - 1) = 1 * Δ.natAbs ^ (2 * ℓ - 1) := (Nat.one_mul _).symm
    _ ≤ (ℓ * E_ℓ) * (B + Δ.natAbs + 2) ^ (2 * ℓ - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hℓ hE) (Nat.pow_le_pow_left (by omega) _)

/-- **Product of `m` `Γ`-cleared factors.** Multiplying `m` rational factor tables cleared by `Γ`
gives an integer table clearing the product by `Γ ^ m`. -/
theorem cast_prod_cleared {ι : Type*} (Γ : ℤ) (s : Finset ι)
    (F_rat : ι → JetTable J ℓ K) (F_int : ι → JetTable J ℓ ℤ)
    (hF : ∀ i ∈ s, Γ • F_rat i = castRingHom K (F_int i)) :
    (Γ ^ #s) • (∏ i ∈ s, F_rat i) = castRingHom K (∏ i ∈ s, F_int i) := by
  rw [map_prod, smul_prod]
  exact prod_congr rfl hF

theorem l1Norm_prod_cleared_le {ι : Type*} (s : Finset ι) (F_int : ι → JetTable J ℓ ℤ)
    {B₁ : ℕ} (hF : ∀ i ∈ s, l1Norm (F_int i) ≤ B₁) :
    l1Norm (∏ i ∈ s, F_int i) ≤ B₁ ^ #s :=
  (l1Norm_prod_le s F_int).trans ((prod_le_prod hF).trans_eq (prod_const B₁))

/-- **Group-product denominator clearing (Appendix B.2, p. 49).** If group `g`'s sum `S_rat g` is
cleared by `Γ ^ (m_group g)` and `∑ g, m_group g = m_test`, then `Ω = Γ ^ m_test` clears the full
product `∏ g, S_rat g`. -/
theorem cast_groupProd_cleared {r m_test : ℕ} (Γ : ℤ) (m_group : Fin r → ℕ)
    (hm : ∑ g : Fin r, m_group g = m_test)
    (S_rat : Fin r → JetTable J ℓ K) (S_int : Fin r → JetTable J ℓ ℤ)
    (hS : ∀ g, (Γ ^ m_group g) • S_rat g = castRingHom K (S_int g)) :
    (Γ ^ m_test) • (∏ g : Fin r, S_rat g) = castRingHom K (∏ g : Fin r, S_int g) := by
  rw [map_prod]
  simp only [← hS, zsmul_eq_const_mul, prod_mul_distrib, Int.cast_pow]
  congr 1
  let Ck := constRingHom J ℓ K
  have hc : ∀ x : K, (const x : JetTable J ℓ K) = Ck x := fun _ => rfl
  simp only [hc, ← map_prod, prod_pow_eq_pow_sum, hm]

/-- **Group-product `ℓ₁`-norm bound (Appendix B.2, p. 49).** If each group sum `S_int g` satisfies
`‖S_int g‖₁ ≤ 2 ^ (s_group g) * B₁ ^ (m_group g)` with `∑ g, s_group g ≤ n` and
`∑ g, m_group g = m_test`, then `‖∏ g, S_int g‖₁ ≤ 2 ^ n * B₁ ^ m_test`. -/
theorem l1Norm_groupProd_cleared_le {r n m_test B₁ : ℕ}
    (s_group m_group : Fin r → ℕ)
    (hs : ∑ g : Fin r, s_group g ≤ n) (hm : ∑ g : Fin r, m_group g = m_test)
    (S_int : Fin r → JetTable J ℓ ℤ)
    (hS : ∀ g, l1Norm (S_int g) ≤ 2 ^ s_group g * B₁ ^ m_group g) :
    l1Norm (∏ g : Fin r, S_int g) ≤ 2 ^ n * B₁ ^ m_test := by
  calc
    l1Norm (∏ g : Fin r, S_int g)
      ≤ ∏ g : Fin r, l1Norm (S_int g) := l1Norm_prod_le univ S_int
    _ ≤ ∏ g : Fin r, (2 ^ s_group g * B₁ ^ m_group g) := prod_le_prod fun g _ => hS g
    _ = 2 ^ (∑ g : Fin r, s_group g) * B₁ ^ (∑ g : Fin r, m_group g) := by
        rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum]
    _ ≤ 2 ^ n * B₁ ^ m_test := by
        rw [hm]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hs)

/-- Intermediate value of the node accumulator `T_t` after `t` signed contribution updates
([OpenAI2026ETH, Appendix B.2, p. 49]). -/
def signedPrefixJet {R : Type*} [CommRing R] (updates : List (ℤ × JetTable J ℓ R)) (t : ℕ) :
    JetTable J ℓ R :=
  ((updates.take t).map fun p => p.1 • p.2).sum

/-- **Prefix accumulator denominator clearing (Appendix B.2, p. 49).** At every step `t`, `Ω` clears
the intermediate accumulator `signedPrefixJet`. -/
theorem cast_signedPrefixJet (Ω : ℤ)
    (updates_rat : List (ℤ × JetTable J ℓ K)) (updates_int : List (ℤ × JetTable J ℓ ℤ))
    (hlen : updates_rat.length = updates_int.length)
    (hrel : ∀ idx (hr : idx < updates_rat.length) (hi : idx < updates_int.length),
      (updates_rat[idx]).1 = (updates_int[idx]).1 ∧
        Ω • (updates_rat[idx]).2 = castRingHom K (updates_int[idx]).2)
    (t : ℕ) :
    Ω • signedPrefixJet updates_rat t = castRingHom K (signedPrefixJet updates_int t) := by
  rw [signedPrefixJet, signedPrefixJet, List.smul_sum, map_list_sum, List.map_map, List.map_map]
  congr 1
  refine List.ext_getElem ?_ fun idx h1 _ => ?_
  · simp only [List.length_map, List.length_take, hlen]
  · simp only [List.getElem_map, List.getElem_take, Function.comp_apply, map_zsmul]
    have hr : idx < updates_rat.length := by
      simp only [List.length_map, List.length_take] at h1
      omega
    obtain ⟨hsgn, hval⟩ := hrel idx hr (hlen ▸ hr)
    rw [hsgn, smul_comm Ω, hval]

/-- **Intermediate prefix accumulator `ℓ₁`-norm bound (Appendix B.2, p. 49).** If every signed
contribution `(ε, Π_int)` has `|ε| ≤ 1` and `‖Π_int‖₁ ≤ 2 ^ n * B₁ ^ m_test`, then at every step
`t` with `min t updates_int.length ≤ M_star`, the integer accumulator `Ω • T_t` satisfies
`‖Ω • T_t‖₁ ≤ M_star * 2 ^ n * B₁ ^ m_test`. -/
theorem l1Norm_signedPrefixJet_le {n m_test B₁ M_star : ℕ}
    (updates_int : List (ℤ × JetTable J ℓ ℤ))
    (hbound : ∀ p ∈ updates_int, p.1.natAbs ≤ 1 ∧ l1Norm p.2 ≤ 2 ^ n * B₁ ^ m_test)
    {t : ℕ} (ht : min t updates_int.length ≤ M_star) :
    l1Norm (signedPrefixJet updates_int t) ≤ M_star * 2 ^ n * B₁ ^ m_test := by
  let C := 2 ^ n * B₁ ^ m_test
  have hmem : ∀ x ∈ (updates_int.take t).map (fun p => l1Norm (p.1 • p.2)), x ≤ C := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hsgn, hnrm⟩ := hbound p (List.mem_of_mem_take hp)
    rw [l1Norm_smul]
    exact (Nat.mul_le_mul hsgn hnrm).trans (Nat.one_mul C).le
  calc
    l1Norm (signedPrefixJet updates_int t)
      ≤ (((updates_int.take t).map fun p => p.1 • p.2).map l1Norm).sum :=
        List.le_sum_of_subadditive l1Norm l1Norm_zero.le l1Norm_add_le _
    _ = ((updates_int.take t).map fun p => l1Norm (p.1 • p.2)).sum := by
        rw [List.map_map]
        rfl
    _ ≤ ((updates_int.take t).map fun p => l1Norm (p.1 • p.2)).length • C :=
        List.sum_le_length_nsmul _ C hmem
    _ = min t updates_int.length * C := by
        simp only [List.length_map, List.length_take, smul_eq_mul]
    _ ≤ M_star * (2 ^ n * B₁ ^ m_test) := Nat.mul_le_mul_right _ ht
    _ = M_star * 2 ^ n * B₁ ^ m_test := (Nat.mul_assoc _ _ _).symm

/-- **Finset slice-sum `ℓ₁`-norm bound (Appendix B.2, p. 49).** Summing `m_test`-factor products
with signs `|ε u| ≤ 1` across an index set `slices` of cardinality `#slices ≤ M_star * 2 ^ n`,
where each factor has `ℓ₁`-norm at most `B₁`, yields an integer `(J × ℓ)` table of `ℓ₁`-norm at
most `M_star * 2 ^ n * B₁ ^ m_test`. -/
theorem l1Norm_clearedSliceSum_le {α β : Type*} {n m_test B₁ M_star : ℕ}
    (slices : Finset α) (hslices : #slices ≤ M_star * 2 ^ n)
    (factors : Finset β) (hfactors : #factors = m_test)
    (ε : α → ℤ) (hε : ∀ u ∈ slices, (ε u).natAbs ≤ 1)
    (F_int : α → β → JetTable J ℓ ℤ)
    (hF : ∀ u ∈ slices, ∀ i ∈ factors, l1Norm (F_int u i) ≤ B₁) :
    l1Norm (∑ u ∈ slices, ε u • ∏ i ∈ factors, F_int u i) ≤ M_star * 2 ^ n * B₁ ^ m_test := by
  calc
    l1Norm (∑ u ∈ slices, ε u • ∏ i ∈ factors, F_int u i)
      ≤ ∑ u ∈ slices, l1Norm (ε u • ∏ i ∈ factors, F_int u i) := l1Norm_sum_le _ _
    _ ≤ ∑ _u ∈ slices, B₁ ^ m_test := sum_le_sum fun u hu => by
        rw [l1Norm_smul]
        exact (Nat.mul_le_mul (hε u hu)
          (hfactors ▸ l1Norm_prod_cleared_le factors (F_int u) (hF u hu))).trans (Nat.one_mul _).le
    _ = #slices * B₁ ^ m_test := sum_const _
    _ ≤ M_star * 2 ^ n * B₁ ^ m_test := Nat.mul_le_mul_right _ hslices

end StagedClearing

end JetTable

/-! ### 4. Exact integer Cramer divisibility and modulo-`2 ^ ℓ` recovery (Appendix B.3) -/

section HermiteCramer

/-- The integer Cramer numerator `N_H = det V_{(0)}` ([OpenAI2026ETH, Appendix B.3, eq. (B.1),
p. 50]), obtained by replacing column `(0, 0)` (corresponding to `X ^ 0`) of the integer confluent
Vandermonde matrix `Polynomial.hermiteMatrix nodes J` with the `Ω`-scaled integer Taylor jet
`J_int`. -/
def hermiteCramerNumerator {Q J : ℕ} (nodes : Fin Q → ℤ) (hQ : 0 < Q) (hJ : 0 < J)
    (J_int : Fin Q → Fin J → ℤ) : ℤ :=
  ((Polynomial.hermiteMatrix nodes J).updateCol (⟨0, hQ⟩, ⟨0, hJ⟩)
    (fun r => J_int r.1 r.2)).det

/-- **Integer Cramer factorization (Appendix B.3, p. 50).** If `H : ℚ[X]` has degree less than
`Q * J`, integer value `H.eval 0 = (H_zero : ℚ)` at `0`, and `Ω`-scaled integer Taylor jet `J_int`
at `nodes`, then `N_H = Ω * D_H * H_zero` in `ℤ`. -/
theorem hermiteCramerNumerator_eq_mul {Q J : ℕ} (nodes : Fin Q → ℤ) (hQ : 0 < Q) (hJ : 0 < J)
    (Ω H_zero : ℤ) (J_int : Fin Q → Fin J → ℤ) {H : ℚ[X]}
    (hdeg : H.natDegree < Q * J)
    (hzero : H.eval 0 = (H_zero : ℚ))
    (hjet : ∀ (i : Fin Q) (j : Fin J),
      (J_int i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes i : ℚ) H).coeff j) :
    hermiteCramerNumerator nodes hQ hJ J_int =
      Ω * (Polynomial.hermiteMatrix nodes J).det * H_zero := by
  have hp : H.degree < ↑(Q * J) :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hdeg)
  let c₀ : Fin Q × Fin J := (⟨0, hQ⟩, ⟨0, hJ⟩)
  have hc₀ : (finProdFinEquiv c₀ : ℕ) = 0 := rfl
  have hcol : (Int.cast : ℤ → ℚ) ∘ (fun r : Fin Q × Fin J => J_int r.1 r.2) =
      (Ω : ℚ) • Polynomial.taylorJet (fun i => (nodes i : ℚ)) J H := by
    funext r
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Polynomial.taylorJet_apply, hjet]
  apply Int.cast_injective (α := ℚ)
  rw [hermiteCramerNumerator, Int.cast_det, Matrix.map_updateCol, hcol, Matrix.det_updateCol_smul,
    ← Polynomial.det_hermiteMatrix_mul_coeff nodes hp c₀, hc₀, Polynomial.coeff_zero_eq_eval_zero,
    hzero]
  push_cast
  ring

/-- At distinct integer nodes and nonzero denominator `Ω ≠ 0`, the integer Cramer denominator
`Ω * det (hermiteMatrix nodes J)` is nonzero ([OpenAI2026ETH, Appendix B.3, p. 50]). -/
theorem mul_det_hermiteMatrix_ne_zero {Q J : ℕ} {nodes : Fin Q → ℤ}
    (hnodes : Function.Injective nodes) {Ω : ℤ} (hΩ : Ω ≠ 0) :
    Ω * (Polynomial.hermiteMatrix nodes J).det ≠ 0 :=
  mul_ne_zero hΩ (Polynomial.det_hermiteMatrix_ne_zero hnodes)

/-- **Exact integer Cramer divisibility (Appendix B.3, p. 50).** Under the hypotheses of
`hermiteCramerNumerator_eq_mul`, `Ω * D_H` divides `N_H` over `ℤ`. -/
theorem mul_det_hermiteMatrix_dvd_hermiteCramerNumerator {Q J : ℕ} (nodes : Fin Q → ℤ)
    (hQ : 0 < Q) (hJ : 0 < J) (Ω H_zero : ℤ) (J_int : Fin Q → Fin J → ℤ) {H : ℚ[X]}
    (hdeg : H.natDegree < Q * J)
    (hzero : H.eval 0 = (H_zero : ℚ))
    (hjet : ∀ (i : Fin Q) (j : Fin J),
      (J_int i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes i : ℚ) H).coeff j) :
    (Ω * (Polynomial.hermiteMatrix nodes J).det) ∣
      hermiteCramerNumerator nodes hQ hJ J_int :=
  ⟨H_zero, hermiteCramerNumerator_eq_mul nodes hQ hJ Ω H_zero J_int hdeg hzero hjet⟩

/-- **Exact integer Cramer recovery (Appendix B.3, eq. (B.1), p. 50).** At distinct integer nodes
with `Ω ≠ 0`, exact Euclidean integer division `N_H / (Ω * D_H)` recovers the integer `H_zero`. -/
theorem hermiteCramerNumerator_ediv_eq {Q J : ℕ} {nodes : Fin Q → ℤ}
    (hnodes : Function.Injective nodes) (hQ : 0 < Q) (hJ : 0 < J)
    {Ω : ℤ} (hΩ : Ω ≠ 0) (H_zero : ℤ) (J_int : Fin Q → Fin J → ℤ) {H : ℚ[X]}
    (hdeg : H.natDegree < Q * J)
    (hzero : H.eval 0 = (H_zero : ℚ))
    (hjet : ∀ (i : Fin Q) (j : Fin J),
      (J_int i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes i : ℚ) H).coeff j) :
    hermiteCramerNumerator nodes hQ hJ J_int /
        (Ω * (Polynomial.hermiteMatrix nodes J).det) = H_zero := by
  rw [hermiteCramerNumerator_eq_mul nodes hQ hJ Ω H_zero J_int hdeg hzero hjet]
  exact Int.mul_ediv_cancel_left H_zero (mul_det_hermiteMatrix_ne_zero hnodes hΩ)

/-- **Modulo-`2 ^ ℓ` recovery from integer-scaled jets.** If `H_zero ≡ Z [ZMOD 2 ^ ℓ]` with
`0 ≤ Z < 2 ^ ℓ`, then `(N_H / (Ω * D_H)) % 2 ^ ℓ = Z`. -/
theorem hermiteCramerNumerator_emod_two_pow_eq {Q J ℓ : ℕ} {nodes : Fin Q → ℤ}
    (hnodes : Function.Injective nodes) (hQ : 0 < Q) (hJ : 0 < J)
    {Ω : ℤ} (hΩ : Ω ≠ 0) (H_zero Z : ℤ) (J_int : Fin Q → Fin J → ℤ) {H : ℚ[X]}
    (hdeg : H.natDegree < Q * J)
    (hzero : H.eval 0 = (H_zero : ℚ))
    (hjet : ∀ (i : Fin Q) (j : Fin J),
      (J_int i j : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes i : ℚ) H).coeff j)
    (hmod : H_zero ≡ Z [ZMOD (2 : ℤ) ^ ℓ])
    (hZ0 : 0 ≤ Z) (hZlt : Z < (2 : ℤ) ^ ℓ) :
    (hermiteCramerNumerator nodes hQ hJ J_int /
        (Ω * (Polynomial.hermiteMatrix nodes J).det)) % ((2 : ℤ) ^ ℓ) = Z := by
  rw [hermiteCramerNumerator_ediv_eq hnodes hQ hJ hΩ H_zero J_int hdeg hzero hjet, hmod]
  exact Int.emod_eq_of_lt hZ0 hZlt

/-- **Summed `ℓ`-coordinate recovery modulo `2 ^ ℓ` (Appendix B.3, p. 50).** Given `(J × ℓ)`
integer jet tables `T_int i` at distinct integer nodes `nodes i` representing `Ω`-scaled Taylor jets
of coordinate polynomials `H s` (`s < ℓ`) whose values at `0` are integers `H_zero s`, if
`∑ s, H_zero s ≡ Z [ZMOD 2 ^ ℓ]` with `0 ≤ Z < 2 ^ ℓ`, then the least nonnegative residue modulo
`2 ^ ℓ` of the summed Cramer quotients equals `Z`. -/
theorem sum_hermiteCramerNumerator_emod_two_pow_eq {Q J ℓ : ℕ} {nodes : Fin Q → ℤ}
    (hnodes : Function.Injective nodes) (hQ : 0 < Q) (hJ : 0 < J)
    {Ω : ℤ} (hΩ : Ω ≠ 0) (H_zero : Fin ℓ → ℤ) (Z : ℤ)
    (T_int : Fin Q → JetTable J ℓ ℤ) (H : Fin ℓ → ℚ[X])
    (hdeg : ∀ s, (H s).natDegree < Q * J)
    (hzero : ∀ s, (H s).eval 0 = (H_zero s : ℚ))
    (hjet : ∀ (i : Fin Q) (j : Fin J) (s : Fin ℓ),
      (T_int i j s : ℚ) = (Ω : ℚ) * (Polynomial.taylor (nodes i : ℚ) (H s)).coeff j)
    (hmod : (∑ s : Fin ℓ, H_zero s) ≡ Z [ZMOD (2 : ℤ) ^ ℓ])
    (hZ0 : 0 ≤ Z) (hZlt : Z < (2 : ℤ) ^ ℓ) :
    (∑ s : Fin ℓ, hermiteCramerNumerator nodes hQ hJ (fun i j => T_int i j s) /
        (Ω * (Polynomial.hermiteMatrix nodes J).det)) % ((2 : ℤ) ^ ℓ) = Z := by
  have hsum : (∑ s : Fin ℓ, hermiteCramerNumerator nodes hQ hJ (fun i j => T_int i j s) /
      (Ω * (Polynomial.hermiteMatrix nodes J).det)) = ∑ s : Fin ℓ, H_zero s :=
    sum_congr rfl fun s _ =>
      hermiteCramerNumerator_ediv_eq hnodes hQ hJ hΩ (H_zero s) (fun i j => T_int i j s)
        (hdeg s) (hzero s) (fun i j => hjet i j s)
  rw [hsum, hmod]
  exact Int.emod_eq_of_lt hZ0 hZlt

end HermiteCramer

end Cslib
