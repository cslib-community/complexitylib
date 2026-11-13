/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The negacyclic ring `R[X] / (X^n + 1)` on coefficient vectors

For `n ≠ 0`, an element of `R[X] / (X^n + 1)` has a unique representative of degree less than `n`,
so it is stored as its coefficient vector `Fin n → R`. Multiplication by `a` is the linear action of
the `n × n` negacyclic (anticirculant) matrix `rotMatrix a`, whose column `j` holds the coefficients
of `X^j · a mod (X^n + 1)`: `negacyclicMul a b = rotMatrix a *ᵥ b`. Over a commutative ring
`negacyclicMul` is commutative and associative, `rotMatrix` is multiplicative, and the polynomial
inner product `innerPoly b r = ∑ j, negacyclicMul (b j) (r j)` is symmetric.

`Negacyclic R n` packages the coefficient vector as a ring. It is a one-field structure rather
than a synonym of `Fin n → R`, so that `a * b` always means `negacyclicMul`: a synonym would
unfold to the function type, where `*` also elaborates as the pointwise product. The coefficient
vector is `Negacyclic.coeffs`, and `Negacyclic.ofCoeffs` builds an element from one; addition,
negation and scalar multiplication act coefficientwise. For `[CommRing R]` and every `n`,
`Negacyclic R n` is a commutative `R`-algebra with `1` the constant polynomial. At `n = 0` it is
the zero ring on `Fin 0 → R`, a chosen zero-dimensional extension rather than the quotient:
there `X^0 + 1 = 2` and `R[X] / (2)` is generally nonzero. Sampling, encoding and norm bounds
transfer along `Negacyclic.coeffsEquiv` and `Negacyclic.coeffsLinearEquiv`, and `innerPoly`
becomes the dot product `⬝ᵥ` over `Negacyclic R n` (`Negacyclic.ofCoeffs_innerPoly`).

## Main definitions

* `Cslib.rotMatrix`, `Cslib.negacyclicMul`: the negacyclic multiplication matrix and
  multiplication on coefficient vectors.
* `Cslib.innerPoly`: the inner product `∑ j, negacyclicMul (b j) (r j)` of coefficient-vector
  tuples.
* `Cslib.Negacyclic`: the commutative ring `R[X] / (X^n + 1)` (`n ≠ 0`) on coefficient vectors, with
  `Negacyclic.coeffsEquiv` and `Negacyclic.coeffsLinearEquiv` to `Fin n → R`.

## Main results

* `Cslib.negacyclicMul_add`, `Cslib.add_negacyclicMul`, `Cslib.map_negacyclicMul`: bilinearity and
  ring-map compatibility of `negacyclicMul`.
* `Cslib.negacyclicMul_comm`, `Cslib.rotMatrix_negacyclicMul`, `Cslib.negacyclicMul_assoc`:
  commutativity, multiplicativity of `rotMatrix` and associativity over a commutative ring.
* `Cslib.abs_negacyclicMul_le`, `Cslib.abs_negacyclicMul_le_sum_abs_mul`,
  `Cslib.abs_innerPoly_le`: `ℓ_∞` and `ℓ₁`-`ℓ_∞` coefficient bounds over `ℤ`.
* `Cslib.Negacyclic.instCommRing`, `Cslib.Negacyclic.instAlgebra`: the commutative `R`-algebra
  structure, with `Negacyclic.coeffs_mul` and `Negacyclic.coeffs_one`.
* `Cslib.Negacyclic.ofCoeffs_innerPoly`: `innerPoly` is the dot product over `Negacyclic R n`.
-/

public section

namespace Cslib

open scoped Matrix

/-! ### Negacyclic multiplication of coefficient vectors -/

/-- The `n × n` negacyclic (anticirculant) multiplication matrix of a degree-`< n` polynomial
`a : Fin n → R` in `R[X] / (X^n + 1)`. Column `j` represents `X^j · a(X) mod (X^n + 1)`. -/
@[expose] def rotMatrix {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : j.val ≤ i.val then
      a ⟨i.val - j.val, by omega⟩
    else
      -a ⟨n + i.val - j.val, by omega⟩

/-- Negacyclic polynomial multiplication `a * b mod (X^n + 1)` on coefficient vectors
`Fin n → R`, defined as the matrix-vector product `rotMatrix a *ᵥ b`. -/
@[expose] def negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) : Fin n → R :=
  rotMatrix a *ᵥ b

/-- Negacyclic multiplication is the matrix-vector product with `rotMatrix a`. -/
@[simp] theorem rotMatrix_mulVec {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix a *ᵥ b = negacyclicMul a b :=
  rfl

/-- The negacyclic matrix of the zero polynomial is the zero matrix. -/
@[simp] theorem rotMatrix_zero {n : ℕ} {R : Type*} [Ring R] :
    rotMatrix (0 : Fin n → R) = 0 := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> simp

/-- `rotMatrix` preserves addition of coefficient vectors. -/
theorem rotMatrix_add {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix (a + b) = rotMatrix a + rotMatrix b := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with negation of coefficient vectors. -/
theorem rotMatrix_neg {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    rotMatrix (-a) = -rotMatrix a := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with subtraction of coefficient vectors. -/
theorem rotMatrix_sub {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix (a - b) = rotMatrix a - rotMatrix b := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with scalar multiplication of coefficient vectors. -/
theorem rotMatrix_smul {n : ℕ} {R : Type*} [Ring R] (r : R) (a : Fin n → R) :
    rotMatrix (r • a) = r • rotMatrix a := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- `rotMatrix` commutes with ring homomorphisms. -/
theorem map_rotMatrix {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : Fin n → R) :
    (rotMatrix a).map f = rotMatrix (f ∘ a) := by
  ext i j
  simp only [Matrix.map_apply, rotMatrix, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> simp

/-- Negacyclic multiplication distributes over addition on the right. -/
theorem negacyclicMul_add {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul a (b + c) = negacyclicMul a b + negacyclicMul a c :=
  Matrix.mulVec_add (rotMatrix a) b c

/-- Negacyclic multiplication distributes over addition on the left. -/
theorem add_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul (a + b) c = negacyclicMul a c + negacyclicMul b c := by
  simp only [negacyclicMul, rotMatrix_add, Matrix.add_mulVec]

/-- Negacyclic multiplication with zero on the right is zero. -/
@[simp] theorem negacyclicMul_zero {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    negacyclicMul a 0 = 0 :=
  Matrix.mulVec_zero (rotMatrix a)

/-- Negacyclic multiplication with zero on the left is zero. -/
@[simp] theorem zero_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    negacyclicMul 0 a = 0 := by
  simp only [negacyclicMul, rotMatrix_zero, Matrix.zero_mulVec]

/-- Negacyclic multiplication commutes with negation on the right. -/
@[simp] theorem negacyclicMul_neg {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    negacyclicMul a (-b) = -negacyclicMul a b := by
  simp only [negacyclicMul, Matrix.mulVec_neg]

/-- Negacyclic multiplication commutes with negation on the left. -/
@[simp] theorem neg_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    negacyclicMul (-a) b = -negacyclicMul a b := by
  simp only [negacyclicMul, rotMatrix_neg, Matrix.neg_mulVec]

/-- Negacyclic multiplication distributes over subtraction on the right. -/
theorem negacyclicMul_sub {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul a (b - c) = negacyclicMul a b - negacyclicMul a c := by
  simp only [negacyclicMul, Matrix.mulVec_sub]

/-- Negacyclic multiplication distributes over subtraction on the left. -/
theorem sub_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul (a - b) c = negacyclicMul a c - negacyclicMul b c := by
  simp only [negacyclicMul, rotMatrix_sub, Matrix.sub_mulVec]

/-- Negacyclic multiplication commutes with scalar multiplication on the left. -/
theorem smul_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (r : R) (a b : Fin n → R) :
    negacyclicMul (r • a) b = r • negacyclicMul a b := by
  simp only [negacyclicMul, rotMatrix_smul, Matrix.smul_mulVec]

/-- Negacyclic multiplication commutes with scalar multiplication on the right. -/
theorem negacyclicMul_smul {n : ℕ} {R : Type*} [CommRing R] (r : R) (a b : Fin n → R) :
    negacyclicMul a (r • b) = r • negacyclicMul a b := by
  simp only [negacyclicMul, Matrix.mulVec_smul]

/-- Negacyclic multiplication distributes over finite sums on the left. -/
theorem sum_negacyclicMul {n : ℕ} {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (f : ι → Fin n → R) (b : Fin n → R) :
    negacyclicMul (∑ i ∈ s, f i) b = ∑ i ∈ s, negacyclicMul (f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, add_negacyclicMul, ih, Finset.sum_insert hi]

/-- Negacyclic multiplication distributes over finite sums on the right. -/
theorem negacyclicMul_sum {n : ℕ} {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (a : Fin n → R) (f : ι → Fin n → R) :
    negacyclicMul a (∑ i ∈ s, f i) = ∑ i ∈ s, negacyclicMul a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, negacyclicMul_add, ih, Finset.sum_insert hi]

/-- Negacyclic multiplication commutes with ring homomorphisms applied to coefficients. -/
theorem map_negacyclicMul {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : Fin n → R) :
    f ∘ negacyclicMul a b = negacyclicMul (f ∘ a) (f ∘ b) := by
  funext i
  have h := RingHom.map_mulVec f (rotMatrix a) b i
  rw [map_rotMatrix] at h
  exact h

/-! ### Commutativity and associativity -/

/-- Index involution on `Fin n` swapping `j` with `i - j mod n` in a negacyclic convolution at
output degree `i`. -/
private def negacyclicSwap {n : ℕ} (i j : Fin n) : Fin n :=
  if h : j.val ≤ i.val then
    ⟨i.val - j.val, by omega⟩
  else
    ⟨n + i.val - j.val, by omega⟩

private lemma negacyclicSwap_val {n : ℕ} (i j : Fin n) :
    (negacyclicSwap i j).val = if j.val ≤ i.val then i.val - j.val else n + i.val - j.val := by
  unfold negacyclicSwap
  split_ifs <;> rfl

private theorem negacyclicSwap_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (negacyclicSwap i) := by
  intro j
  ext
  rw [negacyclicSwap_val, negacyclicSwap_val]
  split_ifs <;> omega

private def negacyclicSwapEquiv {n : ℕ} (i : Fin n) : Fin n ≃ Fin n where
  toFun := negacyclicSwap i
  invFun := negacyclicSwap i
  left_inv j := negacyclicSwap_involutive i j
  right_inv j := negacyclicSwap_involutive i j

@[simp]
private lemma negacyclicSwapEquiv_apply {n : ℕ} (i j : Fin n) :
    negacyclicSwapEquiv i j = negacyclicSwap i j := rfl

private lemma rotMatrix_apply_eq_negacyclicSwap {n : ℕ} {R : Type*} [Ring R]
    (a : Fin n → R) (i j : Fin n) :
    rotMatrix a i j =
      if j.val ≤ i.val then a (negacyclicSwap i j) else -a (negacyclicSwap i j) := by
  simp only [rotMatrix, Matrix.of_apply, negacyclicSwap]
  split_ifs <;> rfl

/-- **Commutativity of negacyclic polynomial multiplication**: `a * b = b * a` in
`R[X] / (X^n + 1)` over any commutative ring `R`. -/
theorem negacyclicMul_comm {n : ℕ} {R : Type*} [CommRing R] (a b : Fin n → R) :
    negacyclicMul a b = negacyclicMul b a := by
  funext i
  simp only [negacyclicMul, Matrix.mulVec, dotProduct]
  rw [← (negacyclicSwapEquiv i).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [negacyclicSwapEquiv_apply, rotMatrix_apply_eq_negacyclicSwap,
    negacyclicSwap_involutive i j]
  rw [negacyclicSwap_val]
  split_ifs <;> first | omega | ring

/-- Cyclic index addition `(l + k) mod n` on `Fin n`. -/
private def cyclicAdd {n : ℕ} (k l : Fin n) : Fin n :=
  if h : l.val + k.val < n then
    ⟨l.val + k.val, h⟩
  else
    ⟨l.val + k.val - n, by omega⟩

/-- Cyclic index subtraction `(j - k) mod n` on `Fin n`. -/
private def cyclicSub {n : ℕ} (k j : Fin n) : Fin n :=
  if h : k.val ≤ j.val then
    ⟨j.val - k.val, by omega⟩
  else
    ⟨n + j.val - k.val, by omega⟩

private lemma cyclicAdd_val {n : ℕ} (k l : Fin n) :
    (cyclicAdd k l).val = if l.val + k.val < n then l.val + k.val else l.val + k.val - n := by
  unfold cyclicAdd
  split_ifs <;> rfl

private lemma cyclicSub_val {n : ℕ} (k j : Fin n) :
    (cyclicSub k j).val = if k.val ≤ j.val then j.val - k.val else n + j.val - k.val := by
  unfold cyclicSub
  split_ifs <;> rfl

private theorem cyclicSub_cyclicAdd {n : ℕ} (k l : Fin n) :
    cyclicSub k (cyclicAdd k l) = l := by
  ext
  rw [cyclicSub_val, cyclicAdd_val]
  split_ifs <;> omega

private theorem cyclicAdd_cyclicSub {n : ℕ} (k j : Fin n) :
    cyclicAdd k (cyclicSub k j) = j := by
  ext
  rw [cyclicAdd_val, cyclicSub_val]
  split_ifs <;> omega

private def cyclicShiftEquiv {n : ℕ} (k : Fin n) : Fin n ≃ Fin n where
  toFun := cyclicAdd k
  invFun := cyclicSub k
  left_inv l := cyclicSub_cyclicAdd k l
  right_inv j := cyclicAdd_cyclicSub k j

@[simp]
private lemma cyclicShiftEquiv_apply {n : ℕ} (k l : Fin n) :
    cyclicShiftEquiv k l = cyclicAdd k l := rfl

private lemma rotMatrix_apply_eq_cyclicSub {n : ℕ} {R : Type*} [Ring R]
    (a : Fin n → R) (i j : Fin n) :
    rotMatrix a i j = if j.val ≤ i.val then a (cyclicSub j i) else -a (cyclicSub j i) := by
  simp only [rotMatrix, Matrix.of_apply, cyclicSub]
  split_ifs <;> rfl

private lemma cyclicSub_cyclicAdd_eq {n : ℕ} (i k l : Fin n) :
    cyclicSub (cyclicAdd k l) i = cyclicSub l (cyclicSub k i) := by
  ext
  rw [cyclicSub_val, cyclicAdd_val, cyclicSub_val, cyclicSub_val]
  split_ifs <;> omega

/-- **Multiplicativity of `rotMatrix`**: the negacyclic multiplication matrix of `negacyclicMul a b`
is the matrix product `rotMatrix a * rotMatrix b`. -/
theorem rotMatrix_negacyclicMul {n : ℕ} {R : Type*} [CommRing R] (a b : Fin n → R) :
    rotMatrix (negacyclicMul a b) = rotMatrix a * rotMatrix b := by
  ext i k
  simp only [Matrix.mul_apply]
  rw [← (cyclicShiftEquiv k).sum_comp]
  rw [rotMatrix_apply_eq_cyclicSub (negacyclicMul a b) i k]
  simp only [negacyclicMul, Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]
  by_cases hik : k.val ≤ i.val
  · simp only [hik, ↓reduceIte]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [cyclicShiftEquiv_apply, rotMatrix_apply_eq_cyclicSub, cyclicSub_cyclicAdd,
      cyclicSub_cyclicAdd_eq]
    rw [cyclicSub_val, cyclicAdd_val]
    split_ifs <;> first | omega | ring
  · simp only [hik, ↓reduceIte]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [cyclicShiftEquiv_apply, rotMatrix_apply_eq_cyclicSub, cyclicSub_cyclicAdd,
      cyclicSub_cyclicAdd_eq]
    rw [cyclicSub_val, cyclicAdd_val]
    split_ifs <;> first | omega | ring

/-- **Associativity of negacyclic polynomial multiplication**: `(a * b) * c = a * (b * c)` in
`R[X] / (X^n + 1)` over any commutative ring `R`. -/
theorem negacyclicMul_assoc {n : ℕ} {R : Type*} [CommRing R] (a b c : Fin n → R) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) := by
  rw [negacyclicMul, rotMatrix_negacyclicMul, ← Matrix.mulVec_mulVec, ← rotMatrix_mulVec,
    ← rotMatrix_mulVec]

/-! ### Coefficient bounds over `ℤ` -/

/-- Entrywise absolute-value bound for `rotMatrix` over `ℤ`. -/
theorem abs_rotMatrix_le {n α : ℕ} {a : Fin n → ℤ} (ha : ∀ i, |a i| ≤ α) (i j : Fin n) :
    |rotMatrix a i j| ≤ α := by
  simp only [rotMatrix, Matrix.of_apply]
  split_ifs with h
  · exact ha ⟨i.val - j.val, by omega⟩
  · rw [abs_neg]
    exact ha ⟨n + i.val - j.val, by omega⟩

/-- **Infinity-norm bound for negacyclic multiplication**: if `‖a‖_∞ ≤ α` and `‖b‖_∞ ≤ β`, then
every coefficient of `negacyclicMul a b` has absolute value at most `n * α * β`. -/
theorem abs_negacyclicMul_le {n α β : ℕ} {a b : Fin n → ℤ}
    (ha : ∀ i, |a i| ≤ α) (hb : ∀ j, |b j| ≤ β) (i : Fin n) :
    |negacyclicMul a b i| ≤ n * α * β := by
  calc |negacyclicMul a b i|
      = |∑ j : Fin n, rotMatrix a i j * b j| := rfl
    _ ≤ ∑ j : Fin n, |rotMatrix a i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((α : ℤ) * β) := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (abs_rotMatrix_le ha i j) (hb j) (abs_nonneg _) (by positivity)
    _ = n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Each row of `rotMatrix a` is a signed rearrangement of `a`, so its absolute values sum to
the `ℓ₁` norm of `a`. -/
theorem sum_abs_rotMatrix_apply {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    ∑ j, |rotMatrix a i j| = ∑ j, |a j| :=
  calc ∑ j, |rotMatrix a i j| = ∑ j, |a (negacyclicSwap i j)| :=
        Finset.sum_congr rfl fun j _ => by
          rw [rotMatrix_apply_eq_negacyclicSwap]
          split_ifs <;> simp only [abs_neg]
    _ = ∑ j, |a j| := (negacyclicSwapEquiv i).sum_comp fun j => |a j|

/-- **`ℓ₁`-`ℓ∞` bound for negacyclic multiplication**: if `‖b‖_∞ ≤ β`, then every coefficient of
`negacyclicMul a b` has absolute value at most `‖a‖₁ · β`. -/
theorem abs_negacyclicMul_le_sum_abs_mul {n β : ℕ} {a b : Fin n → ℤ} (hb : ∀ j, |b j| ≤ β)
    (i : Fin n) : |negacyclicMul a b i| ≤ (∑ j, |a j|) * β :=
  calc |negacyclicMul a b i|
      = |∑ j : Fin n, rotMatrix a i j * b j| := rfl
    _ ≤ ∑ j : Fin n, |rotMatrix a i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, |rotMatrix a i j| * β := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
    _ = (∑ j, |a j|) * β := by rw [← Finset.sum_mul, sum_abs_rotMatrix_apply]

/-! ### Inner products of coefficient-vector tuples -/

/-- Polynomial inner product `⟨b, r⟩ = ∑ j : Fin k, negacyclicMul (b j) (r j)` over
`R[X] / (X^n + 1)`. -/
@[expose] def innerPoly {k n : ℕ} {R : Type*} [Ring R]
    (b r : Fin k → Fin n → R) : Fin n → R :=
  ∑ j : Fin k, negacyclicMul (b j) (r j)

/-- `innerPoly` is symmetric over any commutative ring `R`. -/
theorem innerPoly_comm {k n : ℕ} {R : Type*} [CommRing R]
    (a b : Fin k → Fin n → R) :
    innerPoly a b = innerPoly b a := by
  simp only [innerPoly, negacyclicMul_comm]

@[simp] theorem innerPoly_zero_left {k n : ℕ} {R : Type*} [Ring R]
    (r : Fin k → Fin n → R) :
    innerPoly 0 r = 0 := by
  simp [innerPoly]

@[simp] theorem innerPoly_zero_right {k n : ℕ} {R : Type*} [Ring R]
    (b : Fin k → Fin n → R) :
    innerPoly b 0 = 0 := by
  simp [innerPoly]

/-- `innerPoly` is additive in its first argument. -/
theorem innerPoly_add_left {k n : ℕ} {R : Type*} [Ring R]
    (a b r : Fin k → Fin n → R) :
    innerPoly (a + b) r = innerPoly a r + innerPoly b r := by
  simp only [innerPoly, Pi.add_apply, add_negacyclicMul, Finset.sum_add_distrib]

/-- `innerPoly` is additive in its second argument. -/
theorem innerPoly_add_right {k n : ℕ} {R : Type*} [Ring R]
    (b r s : Fin k → Fin n → R) :
    innerPoly b (r + s) = innerPoly b r + innerPoly b s := by
  simp only [innerPoly, Pi.add_apply, negacyclicMul_add, Finset.sum_add_distrib]

/-- `innerPoly` commutes with subtraction in its first argument. -/
theorem innerPoly_sub_left {k n : ℕ} {R : Type*} [Ring R]
    (a b r : Fin k → Fin n → R) :
    innerPoly (a - b) r = innerPoly a r - innerPoly b r := by
  simp only [innerPoly, Pi.sub_apply, sub_negacyclicMul, Finset.sum_sub_distrib]

/-- `innerPoly` commutes with subtraction in its second argument. -/
theorem innerPoly_sub_right {k n : ℕ} {R : Type*} [Ring R]
    (b r s : Fin k → Fin n → R) :
    innerPoly b (r - s) = innerPoly b r - innerPoly b s := by
  simp only [innerPoly, Pi.sub_apply, negacyclicMul_sub, Finset.sum_sub_distrib]

/-- `innerPoly` commutes with ring homomorphisms applied to polynomial coefficients. -/
theorem map_innerPoly {k n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : Fin k → Fin n → R) :
    f ∘ innerPoly a b = innerPoly (fun j => f ∘ a j) (fun j => f ∘ b j) := by
  funext i
  simp only [Function.comp_apply, innerPoly, Finset.sum_apply, map_sum, ← map_negacyclicMul]

/-- **Infinity-norm bound for `innerPoly`**: if every coefficient of `a` has absolute value at most
`α` and every coefficient of `b` has absolute value at most `β`, then every coefficient of
`innerPoly a b` has absolute value at most `k * n * α * β`. -/
theorem abs_innerPoly_le {k n α β : ℕ} {a b : Fin k → Fin n → ℤ}
    (ha : ∀ j i, |a j i| ≤ α) (hb : ∀ j i, |b j i| ≤ β) (i : Fin n) :
    |innerPoly a b i| ≤ k * n * α * β := by
  calc |innerPoly a b i|
      = |∑ j : Fin k, negacyclicMul (a j) (b j) i| := by simp [innerPoly]
    _ ≤ ∑ j : Fin k, |negacyclicMul (a j) (b j) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, ((n : ℤ) * α * β) :=
      Finset.sum_le_sum fun j _ => abs_negacyclicMul_le (ha j) (hb j) i
    _ = k * n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-! ### The ring `Negacyclic R n` -/

/-- For `n ≠ 0`, the negacyclic ring `R[X] / (X^n + 1)`, stored as the coefficient vector of the
unique representative of degree less than `n`. Multiplication is `negacyclicMul`, never the
pointwise product of coefficient vectors. For `n = 0` this is the zero ring, a chosen extension
rather than the quotient `R[X] / (2)`. -/
@[ext]
structure Negacyclic (R : Type*) (n : ℕ) where
  /-- Build the element of `R[X] / (X^n + 1)` with the given coefficients. -/
  ofCoeffs ::
  /-- The coefficient vector of the representative of degree less than `n`. -/
  coeffs : Fin n → R

namespace Negacyclic

variable {R : Type*} {n : ℕ}

@[simp] theorem coeffs_ofCoeffs (a : Fin n → R) : (ofCoeffs a).coeffs = a := rfl

@[simp] theorem ofCoeffs_coeffs (a : Negacyclic R n) : ofCoeffs a.coeffs = a := rfl

theorem coeffs_injective : Function.Injective (coeffs : Negacyclic R n → Fin n → R) :=
  fun _ _ => Negacyclic.ext

/-- Coefficient vectors as a plain equivalence, for transferring sampling and encodings. -/
@[expose, simps]
def coeffsEquiv : Negacyclic R n ≃ (Fin n → R) where
  toFun := coeffs
  invFun := ofCoeffs
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq R] : DecidableEq (Negacyclic R n) := fun a b =>
  decidable_of_iff (a.coeffs = b.coeffs) Negacyclic.ext_iff.symm

instance [Fintype R] : Fintype (Negacyclic R n) :=
  Fintype.ofEquiv _ coeffsEquiv.symm

instance [Zero R] : Zero (Negacyclic R n) := ⟨ofCoeffs 0⟩
instance [Add R] : Add (Negacyclic R n) := ⟨fun a b => ofCoeffs (a.coeffs + b.coeffs)⟩
instance [Neg R] : Neg (Negacyclic R n) := ⟨fun a => ofCoeffs (-a.coeffs)⟩
instance [Sub R] : Sub (Negacyclic R n) := ⟨fun a b => ofCoeffs (a.coeffs - b.coeffs)⟩
instance {S : Type*} [SMul S R] : SMul S (Negacyclic R n) := ⟨fun s a => ofCoeffs (s • a.coeffs)⟩

@[simp] theorem coeffs_zero [Zero R] : (0 : Negacyclic R n).coeffs = 0 := rfl
@[simp] theorem coeffs_add [Add R] (a b : Negacyclic R n) :
    (a + b).coeffs = a.coeffs + b.coeffs := rfl
@[simp] theorem coeffs_neg [Neg R] (a : Negacyclic R n) : (-a).coeffs = -a.coeffs := rfl
@[simp] theorem coeffs_sub [Sub R] (a b : Negacyclic R n) :
    (a - b).coeffs = a.coeffs - b.coeffs := rfl
@[simp] theorem coeffs_smul {S : Type*} [SMul S R] (s : S) (a : Negacyclic R n) :
    (s • a).coeffs = s • a.coeffs := rfl

instance [AddCommGroup R] : AddCommGroup (Negacyclic R n) :=
  coeffs_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance {S : Type*} [Semiring S] [AddCommGroup R] [Module S R] : Module S (Negacyclic R n) :=
  Function.Injective.module S (⟨⟨coeffs, rfl⟩, fun _ _ => rfl⟩ : Negacyclic R n →+ (Fin n → R))
    coeffs_injective fun _ _ => rfl

/-- Coefficient vectors as an `S`-linear equivalence. -/
@[expose, simps]
def coeffsLinearEquiv (S : Type*) [Semiring S] [AddCommGroup R] [Module S R] :
    Negacyclic R n ≃ₗ[S] (Fin n → R) where
  toFun := coeffs
  invFun := ofCoeffs
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coeffs_sum [AddCommGroup R] {ι : Type*} (s : Finset ι)
    (f : ι → Negacyclic R n) : (∑ i ∈ s, f i).coeffs = ∑ i ∈ s, (f i).coeffs :=
  map_sum (coeffsLinearEquiv ℕ) f s

theorem ofCoeffs_sum [AddCommGroup R] {ι : Type*} (s : Finset ι) (f : ι → Fin n → R) :
    ofCoeffs (∑ i ∈ s, f i) = ∑ i ∈ s, ofCoeffs (f i) :=
  map_sum (coeffsLinearEquiv ℕ).symm f s

section Ring

variable [Ring R]

instance : Mul (Negacyclic R n) := ⟨fun a b => ofCoeffs (negacyclicMul a.coeffs b.coeffs)⟩

/-- The constant polynomial `1`: coefficient `1` in degree zero and `0` elsewhere. -/
instance : One (Negacyclic R n) := ⟨ofCoeffs fun i => if (i : ℕ) = 0 then 1 else 0⟩

@[simp] theorem coeffs_mul (a b : Negacyclic R n) :
    (a * b).coeffs = negacyclicMul a.coeffs b.coeffs := rfl

@[simp] theorem coeffs_one (i : Fin n) :
    (1 : Negacyclic R n).coeffs i = if (i : ℕ) = 0 then 1 else 0 := rfl

theorem ofCoeffs_negacyclicMul (a b : Fin n → R) :
    ofCoeffs (negacyclicMul a b) = ofCoeffs a * ofCoeffs b := rfl

/-- The negacyclic matrix of the constant polynomial `1` is the identity matrix. -/
@[simp] theorem rotMatrix_coeffs_one : rotMatrix (1 : Negacyclic R n).coeffs = 1 := by
  ext i j
  have := i.isLt
  have := j.isLt
  simp only [rotMatrix, Matrix.of_apply, coeffs_one, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- Multiplying by the coefficients of the constant polynomial `1` is the identity. -/
@[simp] theorem one_negacyclicMul (a : Fin n → R) :
    negacyclicMul (1 : Negacyclic R n).coeffs a = a := by
  rw [negacyclicMul, rotMatrix_coeffs_one, Matrix.one_mulVec]

/-- `innerPoly` is the dot product over `Negacyclic R n`. -/
theorem ofCoeffs_innerPoly {k : ℕ} (b r : Fin k → Fin n → R) :
    ofCoeffs (innerPoly b r) = (ofCoeffs ∘ b) ⬝ᵥ (ofCoeffs ∘ r) := by
  simp only [innerPoly, ofCoeffs_sum, ofCoeffs_negacyclicMul, dotProduct, Function.comp_apply]

end Ring

section CommRing

variable [CommRing R]

/-- Multiplying by the coefficients of the constant polynomial `1` on the right is the
identity. -/
@[simp] theorem negacyclicMul_one (a : Fin n → R) :
    negacyclicMul a (1 : Negacyclic R n).coeffs = a := by
  rw [negacyclicMul_comm, one_negacyclicMul]

instance instCommRing : CommRing (Negacyclic R n) where
  __ := (inferInstance : AddCommGroup (Negacyclic R n))
  mul := (· * ·)
  one := 1
  mul_assoc a b c := Negacyclic.ext (negacyclicMul_assoc a.coeffs b.coeffs c.coeffs)
  mul_comm a b := Negacyclic.ext (negacyclicMul_comm a.coeffs b.coeffs)
  one_mul a := Negacyclic.ext (one_negacyclicMul a.coeffs)
  mul_one a := Negacyclic.ext (negacyclicMul_one a.coeffs)
  left_distrib a b c := Negacyclic.ext (negacyclicMul_add a.coeffs b.coeffs c.coeffs)
  right_distrib a b c := Negacyclic.ext (add_negacyclicMul a.coeffs b.coeffs c.coeffs)
  zero_mul a := Negacyclic.ext (zero_negacyclicMul a.coeffs)
  mul_zero a := Negacyclic.ext (negacyclicMul_zero a.coeffs)

instance instAlgebra : Algebra R (Negacyclic R n) :=
  Algebra.ofModule (fun r a b => Negacyclic.ext (smul_negacyclicMul r a.coeffs b.coeffs))
    (fun r a b => Negacyclic.ext (negacyclicMul_smul r a.coeffs b.coeffs))

/-- `algebraMap R (Negacyclic R n) r` is the constant polynomial `r`. -/
@[simp] theorem coeffs_algebraMap (r : R) (i : Fin n) :
    (algebraMap R (Negacyclic R n) r).coeffs i = if (i : ℕ) = 0 then r else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, coeffs_smul, Pi.smul_apply, coeffs_one]
  split_ifs <;> simp

/-- A natural-number cast is the constant polynomial with that value. -/
@[simp] theorem coeffs_natCast (m : ℕ) (i : Fin n) :
    (m : Negacyclic R n).coeffs i = if (i : ℕ) = 0 then (m : R) else 0 := by
  rw [← map_natCast (algebraMap R (Negacyclic R n)), coeffs_algebraMap]

/-- An integer cast is the constant polynomial with that value. -/
@[simp] theorem coeffs_intCast (m : ℤ) (i : Fin n) :
    (m : Negacyclic R n).coeffs i = if (i : ℕ) = 0 then (m : R) else 0 := by
  rw [← map_intCast (algebraMap R (Negacyclic R n)), coeffs_algebraMap]

/-- A numeral is the constant polynomial with that value. -/
@[simp] theorem coeffs_ofNat (m : ℕ) [m.AtLeastTwo] (i : Fin n) :
    (ofNat(m) : Negacyclic R n).coeffs i = if (i : ℕ) = 0 then ofNat(m) else 0 := by
  rw [← map_ofNat (algebraMap R (Negacyclic R n)), coeffs_algebraMap]

end CommRing

end Negacyclic

end Cslib
