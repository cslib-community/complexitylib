/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-!
# Binary gadgets for GSW encryption

Residues modulo `2 ^ w` decompose into exactly `w` bits, ordered from least to most significant.
The expanded coordinate type is `ι × Fin w`: the original coordinate comes first. Recomposition
accepts arbitrary modular entries, while decomposition and flattening return Boolean matrices.
The same `bitMatrix` lift interprets these bits in the modular computation and in integer noise
witnesses.

These are the row operations from
[Gentry, Sahai and Waters, Sections 2.3 and 3.1][GentrySahaiWaters2013].
The paper uses `⌊log₂ q⌋ + 1` digits for a general modulus `q`. For `q = 2 ^ w`, its last digit is
redundant; this module uses the minimal `w` digits. Width zero is allowed: its residue ring is
`ZMod 1`, and its expanded coordinate type is empty.

## Main definitions

* `bitDecomp`, `bitCompose`, `powersOfTwo`: the binary row operations.
* `bitMatrix`: interpret a Boolean matrix in a type with natural-number casts.
* `decomposeMatrix`, `recomposeMatrix`, `flattenMatrix`: apply the row operations to matrices.

## Main results

* `recomposeMatrix_decomposeMatrix`: recomposition recovers every modular matrix.
* `decomposeMatrix_mulVec`: decomposition preserves multiplication by the expanded secret.
* `flattenMatrix_mulVec`: flattening preserves that multiplication on arbitrary modular inputs.
* `recomposeMatrix_flattenMatrix`: flattening preserves recomposition.
* `recomposeMatrix_sub`, `recomposeMatrix_mul`: row recomposition commutes with subtraction
  and left matrix multiplication, as used by serialized NAND.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Sections 2.3 and 3.1]
  [GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open scoped BigOperators Matrix

variable {ι ρ κ : Type*}

/-- The least-significant-first digits of each residue. -/
def bitDecomp (w : ℕ) (v : ι → ZMod (2 ^ w)) : ι × Fin w → Bool :=
  fun j => (v j.1).val.testBit j.2.val

/-- Recompose a row of arbitrary modular coefficients with binary place values. -/
def bitCompose (w : ℕ) (v : ι × Fin w → ZMod (2 ^ w)) : ι → ZMod (2 ^ w) :=
  fun i => ∑ j : Fin w, v (i, j) * 2 ^ j.val

/-- Expand each secret coordinate by its binary place values. -/
def powersOfTwo (w : ℕ) (s : ι → ZMod (2 ^ w)) : ι × Fin w → ZMod (2 ^ w) :=
  fun j => 2 ^ j.2.val * s j.1

/-- Interpret the same Boolean entries as zero or one in the chosen coefficient type. -/
def bitMatrix (R : Type*) [NatCast R] (C : Matrix ρ κ Bool) : Matrix ρ κ R :=
  C.map fun b => (b.toNat : R)

@[simp] theorem bitMatrix_apply (R : Type*) [NatCast R] (C : Matrix ρ κ Bool) (i j) :
    bitMatrix R C i j = (C i j).toNat := rfl

/-- Decompose each row, retaining the original row index and expanding its column index. -/
def decomposeMatrix (w : ℕ) (A : Matrix ρ ι (ZMod (2 ^ w))) : Matrix ρ (ι × Fin w) Bool :=
  fun i => bitDecomp w (A i)

/-- Recompose each row of an arbitrary modular matrix. -/
def recomposeMatrix (w : ℕ) (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    Matrix ρ ι (ZMod (2 ^ w)) :=
  fun i => bitCompose w (C i)

/-- Normalize arbitrary modular rows to Boolean rows by recomposing and decomposing. -/
def flattenMatrix (w : ℕ) (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    Matrix ρ (ι × Fin w) Bool :=
  decomposeMatrix w (recomposeMatrix w C)

private theorem sum_testBit_two_pow (w n : ℕ) (hn : n < 2 ^ w) :
    (∑ j : Fin w, (n.testBit j.val).toNat * 2 ^ j.val) = n := by
  induction w generalizing n with
  | zero => simp only [pow_zero, Nat.lt_one_iff] at hn; subst n; simp
  | succ w ih =>
    have hdiv : n / 2 < 2 ^ w := by
      rw [pow_succ] at hn
      omega
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.testBit_succ,
      pow_zero, mul_one, pow_succ, ← mul_assoc, ← Finset.sum_mul]
    rw [ih (n / 2) hdiv, Nat.toNat_testBit]
    simp only [pow_zero, Nat.div_one]
    omega

/-- Recomposition recovers a row from its actual binary digits. -/
@[simp] theorem bitCompose_bitDecomp (w : ℕ) (v : ι → ZMod (2 ^ w)) :
    bitCompose w (fun j => ((bitDecomp w v j).toNat : ZMod (2 ^ w))) = v := by
  funext i
  simp only [bitCompose, bitDecomp]
  have h := sum_testBit_two_pow w (v i).val (ZMod.val_lt (v i))
  have hc := congrArg (fun n : ℕ => (n : ZMod (2 ^ w))) h
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ZMod.natCast_zmod_val] using hc

/-- The weighted row sum commutes with addition. -/
theorem bitCompose_add (w : ℕ) (a b : ι × Fin w → ZMod (2 ^ w)) :
    bitCompose w (a + b) = bitCompose w a + bitCompose w b := by
  funext i
  simp [bitCompose, add_mul, Finset.sum_add_distrib]

/-- The weighted row sum commutes with scalar multiplication. -/
theorem bitCompose_smul (w : ℕ) (a : ZMod (2 ^ w)) (v : ι × Fin w → ZMod (2 ^ w)) :
    bitCompose w (a • v) = a • bitCompose w v := by
  funext i
  simp [bitCompose, Finset.mul_sum, mul_assoc]

/-- Recomposition recovers every modular matrix from its Boolean decomposition. -/
@[simp] theorem recomposeMatrix_decomposeMatrix (w : ℕ) (A : Matrix ρ ι (ZMod (2 ^ w))) :
    recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (decomposeMatrix w A)) = A := by
  funext i
  exact bitCompose_bitDecomp w (A i)

/-- Recomposition is additive, including on matrices that are not Boolean. -/
theorem recomposeMatrix_add (w : ℕ) (A B : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    recomposeMatrix w (A + B) = recomposeMatrix w A + recomposeMatrix w B := by
  funext i
  exact bitCompose_add w (A i) (B i)

/-- Row recomposition preserves subtraction before the resulting residues are decomposed. -/
theorem recomposeMatrix_sub (w : ℕ) (A B : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    recomposeMatrix w (A - B) = recomposeMatrix w A - recomposeMatrix w B := by
  ext i j
  simp [recomposeMatrix, bitCompose, sub_mul, Finset.sum_sub_distrib]

/-- Recompose a matrix product by recomposing the right operand, retaining all modular counts. -/
theorem recomposeMatrix_mul [Fintype κ] (w : ℕ)
    (A : Matrix ρ κ (ZMod (2 ^ w))) (B : Matrix κ (ι × Fin w) (ZMod (2 ^ w))) :
    recomposeMatrix w (A * B) = A * recomposeMatrix w B := by
  ext i j
  simp only [recomposeMatrix, bitCompose, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Recomposition commutes with modular scalar multiplication. -/
theorem recomposeMatrix_smul (w : ℕ) (a : ZMod (2 ^ w))
    (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    recomposeMatrix w (a • C) = a • recomposeMatrix w C := by
  funext i
  exact bitCompose_smul w a (C i)

/-- Flattening preserves the recomposed matrix. -/
@[simp] theorem recomposeMatrix_flattenMatrix (w : ℕ)
    (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    recomposeMatrix w (bitMatrix (ZMod (2 ^ w)) (flattenMatrix w C)) =
      recomposeMatrix w C :=
  recomposeMatrix_decomposeMatrix w (recomposeMatrix w C)

variable [Fintype ι]

/-- Recomposition transfers the powers-of-two expansion from the secret to the other row. -/
theorem bitCompose_dotProduct (w : ℕ) (v : ι × Fin w → ZMod (2 ^ w))
    (s : ι → ZMod (2 ^ w)) :
    bitCompose w v ⬝ᵥ s = v ⬝ᵥ powersOfTwo w s := by
  simp only [dotProduct, bitCompose, powersOfTwo, Fintype.sum_prod_type,
    Finset.sum_mul, mul_assoc]

/-- Matrix recomposition transfers multiplication by an expanded secret to the original secret. -/
theorem recomposeMatrix_mulVec (w : ℕ) (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w)))
    (s : ι → ZMod (2 ^ w)) :
    recomposeMatrix w C *ᵥ s = C *ᵥ powersOfTwo w s := by
  funext i
  exact bitCompose_dotProduct w (C i) s

/-- The Boolean decomposition has the same product with the powers-of-two secret. -/
theorem decomposeMatrix_mulVec (w : ℕ) (A : Matrix ρ ι (ZMod (2 ^ w)))
    (s : ι → ZMod (2 ^ w)) :
    bitMatrix (ZMod (2 ^ w)) (decomposeMatrix w A) *ᵥ powersOfTwo w s = A *ᵥ s := by
  rw [← recomposeMatrix_mulVec, recomposeMatrix_decomposeMatrix]

/-- Flattening preserves multiplication by the expanded secret on every modular input. -/
theorem flattenMatrix_mulVec (w : ℕ) (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w)))
    (s : ι → ZMod (2 ^ w)) :
    bitMatrix (ZMod (2 ^ w)) (flattenMatrix w C) *ᵥ powersOfTwo w s =
      C *ᵥ powersOfTwo w s := by
  rw [← recomposeMatrix_mulVec, recomposeMatrix_flattenMatrix, recomposeMatrix_mulVec]

end Cslib.Crypto.Homomorphic.GSW
