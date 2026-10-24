/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.QuantumSeries
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Weyl matrices and the quantum Fourier lift

The Weyl matrices `D^a S^b` over `ZMod d`, built from a diagonal character matrix `D` and a
cyclic shift `S`, multiply like monomials up to scalars, and for a primitive character they
span all matrices by finite Fourier inversion. Assigning the Weyl unit of `(a, b)` to the
exponent `(a, b) ∈ ℤ ×ₗ ℤ` makes the monomial-line Hahn series of `QuantumSeries` a division
ring, which receives the Fourier lift of every matrix. Splitting matrix-valued Hahn series
entrywise gives a matrix representation of this division ring over a commutative Hahn field.

## Main definitions

* `HahnMatrix.entry`, `HahnMatrix.split`: entries of matrix-valued Hahn series, and the ring
  isomorphism onto matrices of Hahn series.
* `QuantumMatrices.weyl`, `QuantumMatrices.weylUnit`: the Weyl matrix `D^a S^b` and its unit.
* `QuantumMatrices.fourierCoeff`: the Fourier coefficient of a matrix at `(a, b)`.
* `QuantumLift.divisionSubring`: the Weyl-monomial Hahn series, a division ring.
* `QuantumLift.lift`, `QuantumLift.liftD`: the Fourier lift of a matrix.
* `QuantumLift.representation`: the matrix representation of the division subring.

## Main results

* `QuantumMatrices.weyl_mul`: the Weyl commutation rule.
* `QuantumMatrices.fourier_reconstruction`: Fourier inversion for a primitive character.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/QuantumMatrices.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.HahnMatrix
open HahnSeries Matrix
open scoped BigOperators
noncomputable section
variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Ring R]

private lemma coeff_mul_support_superset (x y : HahnSeries Γ R) (a : Γ)
    (s t : Set Γ) (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) :
    (x * y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a,
      x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hnot
    rw [Finset.mem_antidiagonal] at hij
    by_cases hx : x.coeff ij.1 = 0
    · simp [hx]
    by_cases hy : y.coeff ij.2 = 0
    · simp [hy]
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr ⟨hx, hy, hij.2.2⟩))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract one matrix entry from every Hahn-series coefficient. -/
def entry (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) : HahnSeries Γ R :=
  x.map (⟨fun A => A i j, rfl⟩ : ZeroHom (Matrix ι ι R) R)

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Fintype ι] [DecidableEq ι] in
@[simp] lemma entry_coeff (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) (a : Γ) :
    (entry x i j).coeff a = x.coeff a i j := rfl

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Fintype ι] [DecidableEq ι] in
private lemma entry_support (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) :
    (entry x i j).support ⊆ x.support := by
  intro a ha
  change x.coeff a ≠ 0
  intro h
  exact ha (by change x.coeff a i j = 0; rw [h]; rfl)

/-- Identify a matrix-valued Hahn series with a matrix of scalar Hahn series. -/
def split : HahnSeries Γ (Matrix ι ι R) →+* Matrix ι ι (HahnSeries Γ R) where
  toFun x := entry x
  map_zero' := by ext i j a; rfl
  map_one' := by
    ext i j a
    change (1 : HahnSeries Γ (Matrix ι ι R)).coeff a i j =
      (if i = j then (1 : HahnSeries Γ R) else 0).coeff a
    by_cases hi : i = j <;> by_cases ha : a = 0 <;> simp [hi, ha]
  map_add' x y := by ext i j a; rfl
  map_mul' x y := by
    ext i j a
    change (x * y).coeff a i j = (∑ k, entry x i k * entry y k j).coeff a
    rw [HahnSeries.coeff_mul, Matrix.sum_apply, HahnSeries.coeff_sum]
    simp_rw [coeff_mul_support_superset _ _ a x.support y.support
      x.isPWO_support y.isPWO_support (entry_support x i _) (entry_support y _ j)]
    rw [Finset.sum_comm]
    rfl

lemma split_injective : Function.Injective (split (Γ := Γ) (R := R) (ι := ι)) := by
  intro x y h
  ext a i j
  exact congrArg (fun z : Matrix ι ι (HahnSeries Γ R) => (z i j).coeff a) h

end
end Rational.HahnMatrix

namespace Rational.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The Weyl monomial D^a S^b. -/
def weyl (a b : ZMod d) : Matrix (ZMod d) (ZMod d) K :=
  fun i j => if i = j + b then χ (a * i) else 0

omit [NeZero d] in
@[simp] lemma weyl_zero : weyl χ 0 0 = 1 := by
  ext i j
  simp [weyl, Matrix.one_apply]

lemma weyl_mul (a b c e : ZMod d) :
    weyl χ a b * weyl χ c e = χ (-c * b) • weyl χ (a + c) (b + e) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - b)]
  · simp only [weyl, sub_add_cancel, ite_true, Matrix.smul_apply, smul_eq_mul]
    have heq : i - b = j + e ↔ i = j + (b + e) := by
      constructor <;> intro h <;> linear_combination h
    by_cases h : i = j + (b + e)
    · simp only [ite_eq_left (heq.mpr h), ite_eq_left h]
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [heq, h]
  · intro k hk hne
    have h : i ≠ k + b := by intro heq; apply hne; rw [heq]; ring
    simp [weyl, h]
  · simp

lemma weyl_inverse_right (a b : ZMod d) :
    weyl χ a b * (χ (-a * b) • weyl χ (-a) (-b)) = 1 := by
  rw [Matrix.mul_smul, weyl_mul, add_neg_cancel, add_neg_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a * b + -(-a) * b = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

lemma weyl_inverse_left (a b : ZMod d) :
    (χ (-a * b) • weyl χ (-a) (-b)) * weyl χ a b = 1 := by
  rw [Matrix.smul_mul, weyl_mul, neg_add_cancel, neg_add_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a * b + -a * (-b) = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

/-- A Weyl matrix with its explicit two-sided inverse. -/
def weylUnit (a b : ZMod d) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  ⟨weyl χ a b, χ (-a * b) • weyl χ (-a) (-b),
    weyl_inverse_right χ a b, weyl_inverse_left χ a b⟩

@[simp] lemma weylUnit_val (a b : ZMod d) : (weylUnit χ a b : Matrix _ _ K) = weyl χ a b := rfl

@[simp] lemma weylUnit_zero : weylUnit χ 0 0 = 1 := by
  apply Units.ext
  exact weyl_zero χ

end
end Rational.QuantumMatrices

namespace Rational.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive)

/-- The coefficient of a Weyl matrix in the finite Fourier expansion. -/
def fourierCoeff (R : Matrix (ZMod d) (ZMod d) K) (a b : ZMod d) : K :=
  (d : K)⁻¹ * ∑ j, χ (-a * j) * R j (j - b)

include hχ in
/-- Fourier inversion on each cyclic matrix diagonal. -/
theorem fourier_reconstruction (R : Matrix (ZMod d) (ZMod d) K) :
    (∑ a, ∑ b, fourierCoeff χ R a b • weyl χ a b) = R := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl]
  simp_rw [mul_ite, mul_zero]
  have heq (a : ZMod d) :
      (∑ b, if i = j + b then fourierCoeff χ R a b * χ (a * i) else 0) =
      fourierCoeff χ R a (i - j) * χ (a * i) := by
    rw [Finset.sum_eq_single (i - j)]
    · simp
    · intro b hb hne
      rw [ite_eq_right]
      intro h
      apply hne
      linear_combination -h
    · simp
  simp_rw [heq, fourierCoeff, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hc (k : ZMod d) :
      (∑ a, χ (-a * k) * R k (k - (i - j)) * χ (a * i)) =
      (if i = k then (d : K) else 0) * R k (k - (i - j)) := by
    calc
      _ = (∑ a, χ (a * (i - k))) * R k (k - (i - j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [mul_right_comm, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      _ = _ := by
        simp only [AddChar.sum_mulShift _ hχ, ZMod.card, sub_eq_zero, Nat.cast_ite, Nat.cast_zero]
  simp_rw [hc]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

end
end Rational.QuantumMatrices

namespace Rational.QuantumLift
open HahnSeries Matrix
open Rational.QuantumSeries Rational.QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Lexicographically ordered pairs of integer exponents. -/
abbrev Exponents := ℤ ×ₗ ℤ
/-- Hahn series with matrix coefficients and two integer exponents. -/
abbrev Ambient := HahnSeries Exponents (Matrix (ZMod d) (ZMod d) K)

/-- The Weyl unit assigned to an exponent pair. -/
def monomialUnit (g : Exponents) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  weylUnit χ (ofLex g).1 (ofLex g).2

omit [CharZero K] in
lemma monomialUnit_zero : monomialUnit χ 0 = 1 := by
  simp [monomialUnit]

omit [CharZero K] in
lemma monomialUnit_mul (g h : Exponents) :
    ∃ c : K, (monomialUnit χ g : Matrix (ZMod d) (ZMod d) K) *
        (monomialUnit χ h : Matrix (ZMod d) (ZMod d) K) =
      c • (monomialUnit χ (g + h) : Matrix (ZMod d) (ZMod d) K) := by
  refine ⟨χ (-((ofLex h).1 : ZMod d) * ((ofLex g).2 : ZMod d)), ?_⟩
  simp [monomialUnit, weyl_mul]

/-- The Hahn-series subring whose coefficients lie on the Weyl monomial lines. -/
abbrev divisionSubring := coefficientRing (monomialUnit χ) (monomialUnit_zero χ)
    (monomialUnit_mul χ)

/-- The division ring structure of `divisionSubring`. -/
instance : DivisionRing (divisionSubring χ) :=
  divisionRing (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)

/-- The Fourier lift as a finite Hahn series. -/
def lift (R : Matrix (ZMod d) (ZMod d) K) : Ambient (K := K) (d := d) :=
  ∑ a : ZMod d, ∑ b : ZMod d,
    HahnSeries.single (toLex ((a.val : ℤ), (b.val : ℤ))) (fourierCoeff χ R a b • weyl χ a b)

omit [CharZero K] in
lemma lift_mem (R : Matrix (ZMod d) (ZMod d) K) : lift χ R ∈ divisionSubring χ := by
  apply Subring.sum_mem
  intro a ha
  apply Subring.sum_mem
  intro b hb
  apply single_mem (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨fourierCoeff χ R a b, ?_⟩
  simp [monomialUnit]

/-- The finite Fourier lift as an element of the division subring. -/
def liftD (R : Matrix (ZMod d) (ZMod d) K) : divisionSubring χ := ⟨lift χ R, lift_mem χ R⟩

/-- The representation used in the rank-gap argument. Its coefficient field
is a commutative Hahn field; all inversion takes place inside the division
subring, never by adjoining arbitrary matrix-field scalars. -/
def representation : divisionSubring χ →+* Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K) :=
  (Rational.HahnMatrix.split (Γ := Exponents)).comp (divisionSubring χ).subtype

end
end Rational.QuantumLift

end Cslib.Circuits
