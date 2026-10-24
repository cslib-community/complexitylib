/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rational hitting lists: evaluation

Basic properties of the partial evaluation of rational formulas: values are unique, they are
transported along ring homomorphisms, and they lift back along homomorphisms reflecting units.
The second part collects facts on two-by-two block matrices over a possibly noncommutative ring,
notably the Schur-complement criterion for invertibility of a block matrix with a zero corner.

## Main definitions

* `Cslib.Circuits.Rational.NoncommBlocks.matMul`: matrix multiplication over a possibly
  noncommutative ring.

## Main results

* `Cslib.Circuits.Rational.Formula.Eval.unique`: a formula has at most one value.
* `Cslib.Circuits.Rational.Formula.Eval.map`: values are mapped by ring homomorphisms.
* `Cslib.Circuits.Rational.Formula.Eval.lift`: values lift along homomorphisms reflecting units.
* `Cslib.Circuits.Rational.Formula.Eval.unit_of_division_lift`: a nonzero value mapped out of a
  division ring is a unit.
* `Cslib.Circuits.Rational.NoncommBlocks.schur_unit_iff`,
  `Cslib.Circuits.Rational.NoncommBlocks.schur_inverse`: invertibility of a block matrix with a
  zero corner and an invertible corner, through its Schur complement.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Evaluation.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

namespace Formula

variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]

/-- A formula has at most one value at a substitution. -/
theorem Eval.unique {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a b : R}
    (ha : h.Eval c X a) (hb : h.Eval c X b) : a = b := by
  induction h using inductionOn generalizing a b with
  | var i => exact (eval_var_iff.mp ha).trans (eval_var_iff.mp hb).symm
  | const q => exact (eval_const_iff.mp ha).trans (eval_const_iff.mp hb).symm
  | add f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := eval_add_iff.mp hb
    rw [ihf ha₁ hb₁, ihg ha₂ hb₂]
  | mul f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := eval_mul_iff.mp hb
    rw [ihf ha₁ hb₁, ihg ha₂ hb₂]
  | inv f ih =>
    obtain ⟨a', ha', -, hva⟩ := eval_inv_iff.mp ha
    obtain ⟨b', hb', hbw, -⟩ := eval_inv_iff.mp hb
    obtain rfl := ih ha' hb'
    calc
      a = a * (a' * b) := by rw [hbw, mul_one]
      _ = b := by rw [← mul_assoc, hva, one_mul]

/-- A ring homomorphism maps a value of a formula to a value at the mapped substitution. -/
theorem Eval.map {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : R}
    (ha : h.Eval c X a) (f : R →+* S) :
    h.Eval (f.comp c) (fun i => f (X i)) (f a) := by
  induction h using inductionOn generalizing a with
  | var i => rw [eval_var_iff.mp ha]; exact .var i
  | const q => rw [eval_const_iff.mp ha]; exact .const q
  | add g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    simpa only [map_add] using Eval.add (ihg ha₁) (ihk ha₂)
  | mul g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    simpa only [map_mul] using Eval.mul (ihg ha₁) (ihk ha₂)
  | inv g ih =>
    obtain ⟨b, hb, hba, hab⟩ := eval_inv_iff.mp ha
    exact .inv (ih hb) (by rw [← map_mul, hba, map_one]) (by rw [← map_mul, hab, map_one])

/-- Defined evaluations lift through a homomorphism reflecting units. In particular this handles
every inverse occurrence before considering the root. -/
theorem Eval.lift (f : R →+* S) (hf : ∀ x, IsUnit (f x) → IsUnit x)
    {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : S}
    (ha : h.Eval (f.comp c) (fun i => f (X i)) a) :
    ∃ b : R, h.Eval c X b ∧ f b = a := by
  induction h using inductionOn generalizing a with
  | var i => exact ⟨X i, .var i, (eval_var_iff.mp ha).symm⟩
  | const q => exact ⟨c q, .const q, (eval_const_iff.mp ha).symm⟩
  | add g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    obtain ⟨b₁, hb₁, rfl⟩ := ihg ha₁
    obtain ⟨b₂, hb₂, rfl⟩ := ihk ha₂
    exact ⟨b₁ + b₂, .add hb₁ hb₂, map_add f b₁ b₂⟩
  | mul g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    obtain ⟨b₁, hb₁, rfl⟩ := ihg ha₁
    obtain ⟨b₂, hb₂, rfl⟩ := ihk ha₂
    exact ⟨b₁ * b₂, .mul hb₁ hb₂, map_mul f b₁ b₂⟩
  | inv g ih =>
    obtain ⟨b, hb, hba, hab⟩ := eval_inv_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := ih hb
    obtain ⟨u, hu⟩ := hf b' ⟨⟨f b', a, hba, hab⟩, rfl⟩
    have heval : (Formula.inv g).Eval c X (↑u⁻¹ : R) :=
      .inv hb' (by rw [← hu]; exact u.mul_inv) (by rw [← hu]; exact u.inv_mul)
    exact ⟨_, heval, (heval.map f).unique ha⟩

/-- Mapping a defined nonzero value out of a division ring makes it a unit. This is used after the
partial-specialization domain proof, not instead of it. -/
theorem Eval.unit_of_division_lift {D : Type*} [DivisionRing D] [Nontrivial R]
    (f : D →+* R) {c : ℚ →+* D} {X : Fin n → D} {h : Formula n} {a : R}
    (ha : h.Eval (f.comp c) (fun i => f (X i)) a) (ha0 : a ≠ 0) : IsUnit a := by
  have hf : ∀ x, IsUnit (f x) → IsUnit x := by
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hx.ne_zero (by rw [hzero, map_zero])
  obtain ⟨b, hb, heq⟩ := ha.lift f hf
  have hb0 : b ≠ 0 := by
    intro h
    apply ha0
    rw [← heq, h, map_zero]
  exact heq ▸ (isUnit_iff_ne_zero.mpr hb0).map f

end Formula

end Rational

namespace Rational.NoncommBlocks

open Matrix

variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Matrix multiplication over the possibly noncommutative coefficient ring. -/
abbrev matMul {l m n : Type*} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix l n R := A * B

/-- An upper unitriangular block matrix is invertible. -/
private theorem upper_unit (B : Matrix ι κ R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) B 0 (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 (-B) 0 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A lower unitriangular block matrix is invertible. -/
private theorem lower_unit (C : Matrix κ ι R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 0 (-C) 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A block diagonal matrix is invertible exactly when both diagonal blocks are. -/
theorem diag_unit_iff (A : Matrix ι ι R) (D : Matrix κ κ R) :
    IsUnit (fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  constructor
  · rintro ⟨u, hu⟩
    have hh := u.val_inv
    have hh' := u.inv_val
    rw [hu] at hh hh'
    refine ⟨isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁, ?_, ?_⟩,
      isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂, ?_, ?_⟩⟩
    · have h := congrArg Matrix.toBlocks₁₁ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₁₁ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
  · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
    apply isUnit_iff_exists.mpr
    refine ⟨fromBlocks (↑u⁻¹) 0 0 (↑v⁻¹), ?_, ?_⟩ <;>
      simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- The Schur factorization of a block matrix with a zero corner and an invertible corner. -/
private theorem schur_factor (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    fromBlocks A B C 0 =
      fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-C * A' * B) *
      fromBlocks 1 (A' * B) 0 1 := by
  simp only [fromBlocks_multiply, add_zero, zero_add,
    one_mul, mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc A A' B, hAA', Matrix.one_mul, Matrix.mul_assoc C A' A, hA'A,
    Matrix.mul_one]
  simp [Matrix.mul_assoc, Matrix.neg_mul]

/-- A block matrix with a zero corner and an invertible corner is invertible exactly when its
Schur complement is. -/
theorem schur_unit_iff (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    IsUnit (fromBlocks A B C 0) ↔ IsUnit (C * A' * B) := by
  rw [schur_factor A A' B C hAA' hA'A]
  obtain ⟨u, hu⟩ := upper_unit (A' * B)
  obtain ⟨v, hv⟩ := lower_unit (C * A')
  rw [← hu, ← hv, Units.isUnit_mul_units, Units.isUnit_units_mul, diag_unit_iff]
  have hA : IsUnit A := isUnit_iff_exists.mpr ⟨A', hAA', hA'A⟩
  simp [hA, Matrix.neg_mul, IsUnit.neg_iff]

/-- An inverse of a block matrix with a zero corner and an invertible corner, whose corner block
is the inverse of the Schur complement. -/
theorem schur_inverse (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (a b : Matrix κ κ R) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (ha : C * A' * B = a) (hab : a * b = 1) (hba : b * a = 1) :
    ∃ M : Matrix (ι ⊕ κ) (ι ⊕ κ) R,
      fromBlocks A B C 0 * M = 1 ∧ M * fromBlocks A B C 0 = 1 ∧
      matMul (matMul (fromCols (0 : Matrix κ ι R) (-1)) M)
        (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b := by
  let U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 0 (C * A') 1, fromBlocks 1 0 (-(C * A')) 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let V : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 (A' * B) 0 1, fromBlocks 1 (-(A' * B)) 0 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let D : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks A 0 0 (-a), fromBlocks A' 0 0 (-b),
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, hAA', hab],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, hA'A, hba]⟩
  have hS : (↑(U * D * V) : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = fromBlocks A B C 0 := by
    change fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-a) *
      fromBlocks 1 (A' * B) 0 1 = _
    rw [← ha]
    simpa [Matrix.neg_mul] using (schur_factor A A' B C hAA' hA'A).symm
  refine ⟨↑(U * D * V)⁻¹, ?_, ?_, ?_⟩
  · rw [← hS]; exact (U * D * V).mul_inv
  · rw [← hS]; exact (U * D * V).inv_mul
  · change matMul (matMul (fromCols (0 : Matrix κ ι R) (-1))
      (V.inv * (D.inv * U.inv))) (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b
    simp [matMul, V, D, U, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.fromCols_mul_fromBlocks, fromCols_mul_fromRows,
      Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

end Rational.NoncommBlocks

end Cslib.Circuits
