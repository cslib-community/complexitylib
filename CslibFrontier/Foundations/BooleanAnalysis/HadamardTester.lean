/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Hadamard
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith

/-!
# Testing quadratic equations with the Hadamard code

A system of quadratic equations over the two-element field in the unknowns `x : ι → Bool` can be
written as `⟨x ⊗ x, A e⟩ = b e` for `e : κ`, where `x ⊗ x : ι × ι → Bool` is the tensor product
of `x` with itself (`BitString.tensor`, the outer product `Matrix.vecMulVec x x` read on pairs of
coordinates), and `⟨·, ·⟩` is the inner product modulo two, the dot product in the Boolean ring
`Bool`. Bit strings add coordinatewise in the same ring, and the tensor product is bilinear
(`BitString.tensor_add_left`, `BitString.tensor_add_right`). A proof that the system has a
solution `x` consists of two tables: the Hadamard encodings `f` of `x` and `g` of `x ⊗ x`. Since
`⟨x ⊗ x, y ⊗ z⟩ = ⟨x, y⟩ ⟨x, z⟩` (`BitString.hadamardCode_tensor_tensor`), the tables can be
checked with a constant number of queries, every value being read by self-correction
[Arora and Barak, Section 11.5][AroraBarak09]:

* the *linearity test* on `f` and on `g` (`BitString.blrAcceptance`): passing it, a table is
  close to the encoding of some bit string;
* the *tensor test* (`BitString.tensorTestAcceptance`), comparing `g` at `y ⊗ z` with the product
  of `f` at `y` and at `z` for uniformly random `y` and `z`: when `g` encodes `w ≠ x ⊗ x`, the
  encodings disagree on at least a quarter of the pairs
  (`BitString.one_div_four_le_expect_hadamardCode_tensor`), so the test rejects with probability
  at least `1/4` less the probability that a read is wrong
  (`BitString.eq_tensor_of_lt_tensorTestAcceptance`);
* the *equation test* (`BitString.equationTestAcceptance`), comparing `g` at the sum of a
  uniformly random set of the `A e` with the sum of the corresponding `b e`: when `g` encodes
  some `w` violating an equation, a random set of equations has a violated sum with probability
  one half (`BitString.hadamardCode_eq_of_lt_equationTestAcceptance`).

Together they make the Hadamard tester: the encodings of a solution pass all four tests with
probability one, and tables passing them with high enough probability certify that the system is
solvable, by a solution that `f` encodes
(`BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance`).

## Main definitions

* `Cslib.BitString.tensor`: the tensor product of two bit strings.
* `Cslib.BitString.tensorTestAcceptance`: the acceptance probability of the tensor test.
* `Cslib.BitString.equationTestAcceptance`: the acceptance probability of the equation test.

## Main results

* `Cslib.BitString.hadamardCode_tensor_tensor`: the inner product of tensor products is the
  product of the inner products.
* `Cslib.BitString.one_div_four_le_expect_hadamardCode_tensor`: a nonzero bilinear form is
  nonzero on at least a quarter of the pairs.
* `Cslib.BitString.tensorTestAcceptance_hadamardCode`,
  `Cslib.BitString.eq_tensor_of_lt_tensorTestAcceptance`: completeness and soundness of the
  tensor test.
* `Cslib.BitString.equationTestAcceptance_hadamardCode`,
  `Cslib.BitString.hadamardCode_eq_of_lt_equationTestAcceptance`: completeness and soundness of
  the equation test.
* `Cslib.BitString.exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance`: soundness of the
  Hadamard tester for quadratic equations.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι κ : Type*}

/-! ### Tensor products -/

/-- The tensor product of bit strings `x` and `y`: the outer product `Matrix.vecMulVec x y` in the
Boolean ring `Bool`, read on pairs of coordinates, so its bit at `(i, j)` is `x i && y j`. -/
def tensor (x : ι → Bool) (y : κ → Bool) : ι × κ → Bool :=
  Function.uncurry (Matrix.vecMulVec x y)

/-- The bit of `x ⊗ y` at `(i, j)` is `x i && y j`. -/
@[simp] theorem tensor_apply (x : ι → Bool) (y : κ → Bool) (p : ι × κ) :
    tensor x y p = (x p.1 && y p.2) :=
  rfl

/-- The tensor product is linear in its first argument. -/
theorem tensor_add_left (x x' : ι → Bool) (y : κ → Bool) :
    tensor (x + x') y = tensor x y + tensor x' y :=
  congrArg Function.uncurry (Matrix.add_vecMulVec x x' y)

/-- The tensor product is linear in its second argument. -/
theorem tensor_add_right (x : ι → Bool) (y y' : κ → Bool) :
    tensor x (y + y') = tensor x y + tensor x y' :=
  congrArg Function.uncurry (Matrix.vecMulVec_add x y y')

/-- The tensor product of two unit vectors is a unit vector. -/
theorem tensor_single [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    tensor (Pi.single i true) (Pi.single j true) = Pi.single (i, j) true := by
  funext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;>
    simp [hi, hj, Bool.zero_eq_false]

variable [Fintype ι] [Fintype κ]

/-- **The inner product of tensor products is the product of the inner products**:
`⟨x ⊗ y, a ⊗ b⟩ = ⟨x, a⟩ ⟨y, b⟩`. -/
theorem hadamardCode_tensor_tensor (x a : ι → Bool) (y b : κ → Bool) :
    hadamardCode (tensor x y) (tensor a b) = (hadamardCode x a && hadamardCode y b) := by
  rw [← Bool.mul_eq_and, hadamardCode_apply, hadamardCode_apply, hadamardCode_apply, dotProduct,
    dotProduct, dotProduct, sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_congr _ _ fun p => ?_
  simp only [tensor_apply, ← Bool.mul_eq_and]
  ring

/-- **The inner product with a combination of rows**: the inner product of `w` with the sum of the
`A e` for the `e` with `k e = true` is the sum of the inner products of `w` with those `A e`, that
is, `⟨w, Aᵀ k⟩ = ⟨k, A w⟩`. -/
private theorem hadamardCode_transpose (w : ι → Bool) (k : κ → Bool) (A : κ → ι → Bool) :
    hadamardCode w (fun j => hadamardCode k fun e => A e j) =
      hadamardCode k fun e => hadamardCode w (A e) := by
  simp only [hadamardCode_apply]
  rw [dotProduct_comm]
  exact (Matrix.dotProduct_mulVec k (Matrix.of A) w).symm.trans
    (congrArg _ (funext fun e => dotProduct_comm (A e) w))

variable [DecidableEq ι] [DecidableEq κ]

/-- The Hadamard encoding of the tensor square of `x`, read at a unit vector, is a product of two
bits of `x`. -/
theorem hadamardCode_tensor_single (x : ι → Bool) (p p' : ι) :
    hadamardCode (tensor x x) (Pi.single (p, p') true) = (x p && x p') := by
  rw [hadamardCode_single, tensor_apply]

/-- **A nonzero bilinear form is nonzero on a quarter of the pairs**: if `M` is not all `false`,
then `⟨M, y ⊗ z⟩ = 1` with probability at least `1/4` over uniformly random `y` and `z`. -/
theorem one_div_four_le_expect_hadamardCode_tensor {M : ι × κ → Bool} (hM : ∃ k, M k = true) :
    1 / 4 ≤ 𝔼 y, 𝔼 z, if hadamardCode M (tensor y z) = true then (1 : ℝ) else 0 := by
  obtain ⟨⟨i, j⟩, hk⟩ := hM
  have hrow (y : ι → Bool) :
      1 / 2 * (if hadamardCode M (tensor y (Pi.single j true)) = true then 1 else 0) ≤
        𝔼 z, if hadamardCode M (tensor y z) = true then (1 : ℝ) else 0 := by
    split_ifs with hy
    · rw [mul_one, expect_boole_eq_one_div_two_of_map_add
        (f := fun z => hadamardCode M (tensor y z))
        (fun z z' => by rw [tensor_add_right, hadamardCode_add]) ⟨_, hy⟩]
    · rw [mul_zero]
      exact expect_nonneg fun z _ => by split_ifs <;> norm_num
  have hcol : 𝔼 y, (if hadamardCode M (tensor y (Pi.single j true)) = true then
      (1 : ℝ) else 0) = 1 / 2 :=
    expect_boole_eq_one_div_two_of_map_add
      (f := fun y => hadamardCode M (tensor y (Pi.single j true)))
      (fun y y' => by rw [tensor_add_left, hadamardCode_add])
      ⟨Pi.single i true, by rwa [tensor_single, hadamardCode_single]⟩
  calc (1 / 4 : ℝ) = 𝔼 y, 1 / 2 * (if hadamardCode M (tensor y (Pi.single j true)) = true
        then (1 : ℝ) else 0) := by
        rw [← mul_expect, hcol]
        norm_num
    _ ≤ _ := expect_le_expect fun y _ => hrow y

/-! ### Union bounds -/

/-- One step of a union bound: if `A` implies `F` whenever `G` holds, the indicator of `A` is at
most the indicator of `F` plus the indicator of the failure of `G`. -/
private theorem boole_le_add_one_sub {A F G : Prop} [Decidable A] [Decidable F] [Decidable G]
    (h : A → G → F) :
    (if A then (1 : ℝ) else 0) ≤ (if F then 1 else 0) + (1 - if G then 1 else 0) := by
  split_ifs <;> first | exact absurd (h ‹A› ‹G›) ‹¬F› | norm_num

/-- The union bound over three events `G₁`, `G₂`, `G₃`. -/
private theorem boole_le_add_one_sub₃ {A F G₁ G₂ G₃ : Prop} [Decidable A] [Decidable F]
    [Decidable G₁] [Decidable G₂] [Decidable G₃] (h : A → G₁ → G₂ → G₃ → F) :
    (if A then (1 : ℝ) else 0) ≤ (if F then 1 else 0) + (1 - if G₁ then 1 else 0) +
      (1 - if G₂ then 1 else 0) + (1 - if G₃ then 1 else 0) := by
  split_ifs <;> first | exact absurd (h ‹A› ‹G₁› ‹G₂› ‹G₃›) ‹¬F› | norm_num

/-! ### The tensor test -/

/-- The acceptance probability of the tensor test on tables `f` and `g`: the probability, over
independent uniformly random `y`, `z`, `r`, `s` and `t`, that the self-corrected read of `g` at
`y ⊗ z` with randomness `t` is the product of the self-corrected reads of `f` at `y` with
randomness `r` and at `z` with randomness `s`. -/
noncomputable def tensorTestAcceptance (f : (ι → Bool) → Bool) (g : (ι × ι → Bool) → Bool) : ℝ :=
  𝔼 y, 𝔼 z, 𝔼 r, 𝔼 s, 𝔼 t,
    if selfCorrect g (tensor y z) t = (selfCorrect f y r && selfCorrect f z s) then 1 else 0

/-- **Completeness of the tensor test**: the encodings of `x` and of `x ⊗ x` pass it with
probability one. -/
@[simp] theorem tensorTestAcceptance_hadamardCode (x : ι → Bool) :
    tensorTestAcceptance (hadamardCode x) (hadamardCode (tensor x x)) = 1 := by
  simp only [tensorTestAcceptance, selfCorrect_hadamardCode, hadamardCode_tensor_tensor]
  simp

/-- **Soundness of the tensor test**: if `f` and `g` are within relative distances `ε` and `ε'`
of the encodings of `x` and of `w`, and the test accepts with probability more than
`3/4 + 4ε + 2ε'`, then `w = x ⊗ x`. -/
theorem eq_tensor_of_lt_tensorTestAcceptance {f : (ι → Bool) → Bool}
    {g : (ι × ι → Bool) → Bool} {x : ι → Bool} {w : ι × ι → Bool} {ε ε' : ℝ}
    (hf : (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (hg : (hammingDist g (hadamardCode w) : ℝ) / 2 ^ Fintype.card (ι × ι) ≤ ε')
    (h : 3 / 4 + (4 * ε + 2 * ε') < tensorTestAcceptance f g) : w = tensor x x := by
  by_contra hw
  -- The test made on the codewords themselves, and the events that the reads are correct.
  set D : (ι → Bool) → (ι → Bool) → ℝ := fun y z =>
    if hadamardCode w (tensor y z) = (hadamardCode x y && hadamardCode x z) then 1 else 0
  set c : (ι → Bool) → (ι → Bool) → ℝ := fun y r =>
    if selfCorrect f y r = hadamardCode x y then 1 else 0
  set c' : (ι → Bool) → (ι → Bool) → (ι × ι → Bool) → ℝ := fun y z t =>
    if selfCorrect g (tensor y z) t = hadamardCode w (tensor y z) then 1 else 0
  have hD : 𝔼 y, 𝔼 z, D y z ≤ 3 / 4 := by
    have hM : ∃ k, (w + tensor x x) k = true := by
      by_contra hc
      refine hw (funext fun k => ?_)
      have hk := not_exists.1 hc k
      revert hk
      simp only [Pi.add_apply, Bool.add_eq_xor]
      cases w k <;> cases tensor x x k <;> simp
    have hpt (y z : ι → Bool) : D y z =
        1 - if hadamardCode (w + tensor x x) (tensor y z) = true then 1 else 0 := by
      simp only [D, hadamardCode_add_left, hadamardCode_tensor_tensor]
      cases hadamardCode w (tensor y z) <;> cases (hadamardCode x y && hadamardCode x z) <;>
        norm_num
    simp only [hpt, expect_sub_distrib, Fintype.expect_const]
    linarith [one_div_four_le_expect_hadamardCode_tensor hM]
  have hbound : tensorTestAcceptance f g ≤ 𝔼 y, 𝔼 z, 𝔼 r, 𝔼 s, 𝔼 t,
      (D y z + (1 - c y r) + (1 - c z s) + (1 - c' y z t)) := by
    unfold tensorTestAcceptance
    gcongr with y _ z _ r _ s _ t _
    exact boole_le_add_one_sub₃ fun hA h₁ h₂ h₃ => by rw [← h₁, ← h₂, ← h₃]; exact hA
  simp only [expect_add_distrib, Fintype.expect_const] at hbound
  have hc : 𝔼 y, 𝔼 r, (1 - c y r) ≤ 2 * ε :=
    Fintype.expect_expect_one_sub_le fun y =>
      one_sub_two_mul_le_expect_selfCorrect_hadamardCode hf y
  have hc' : 𝔼 y, 𝔼 z, 𝔼 t, (1 - c' y z t) ≤ 2 * ε' :=
    expect_le univ_nonempty fun y _ => Fintype.expect_expect_one_sub_le fun z =>
      one_sub_two_mul_le_expect_selfCorrect_hadamardCode hg _
  linarith

/-! ### The equation test -/

/-- The acceptance probability of the equation test on a table `g`, for the linear equations
`⟨w, A e⟩ = b e` in `w`: the probability, over independent uniformly random `k` and `t`, that the
self-corrected read of `g` at the sum of the `A e` for the `e` with `k e = true`, with randomness
`t`, is the sum of the corresponding `b e`. -/
noncomputable def equationTestAcceptance (g : (ι → Bool) → Bool) (A : κ → ι → Bool)
    (b : κ → Bool) : ℝ :=
  𝔼 k, 𝔼 t,
    if selfCorrect g (fun j => hadamardCode k fun e => A e j) t = hadamardCode k b then 1 else 0

/-- **Completeness of the equation test**: the encoding of a solution of the equations passes it
with probability one. -/
theorem equationTestAcceptance_hadamardCode {A : κ → ι → Bool} {b : κ → Bool} {w : ι → Bool}
    (h : ∀ e, hadamardCode w (A e) = b e) :
    equationTestAcceptance (hadamardCode w) A b = 1 := by
  simp only [equationTestAcceptance, selfCorrect_hadamardCode, hadamardCode_transpose, h]
  simp

/-- **Soundness of the equation test**: if `g` is within relative distance `ε` of the encoding of
`w`, and the test accepts with probability more than `1/2 + 2ε`, then `w` solves the
equations. -/
theorem hadamardCode_eq_of_lt_equationTestAcceptance {g : (ι → Bool) → Bool}
    {A : κ → ι → Bool} {b : κ → Bool} {w : ι → Bool} {ε : ℝ}
    (hg : (hammingDist g (hadamardCode w) : ℝ) / 2 ^ Fintype.card ι ≤ ε)
    (h : 1 / 2 + 2 * ε < equationTestAcceptance g A b) (e : κ) :
    hadamardCode w (A e) = b e := by
  by_contra he
  -- The test made on the codeword itself, and the event that the read is correct.
  set D : (κ → Bool) → ℝ := fun k =>
    if hadamardCode w (fun j => hadamardCode k fun e' => A e' j) = hadamardCode k b then 1 else 0
  set c : (κ → Bool) → (ι → Bool) → ℝ := fun k t =>
    if selfCorrect g (fun j => hadamardCode k fun e' => A e' j) t =
      hadamardCode w (fun j => hadamardCode k fun e' => A e' j) then 1 else 0
  have hD : 𝔼 k, D k = 1 / 2 := by
    -- The parity of the equations violated by `w` in a random set of equations.
    have hv : ∃ k, hadamardCode ((fun e' => hadamardCode w (A e')) + b) k = true :=
      ⟨Pi.single e true, by simpa [Bool.add_eq_xor] using he⟩
    have hpt (k : κ → Bool) : D k =
        1 - if hadamardCode ((fun e' => hadamardCode w (A e')) + b) k = true then 1 else 0 := by
      simp only [D]
      rw [hadamardCode_transpose, hadamardCode_comm _ k, hadamardCode_add]
      cases hadamardCode k (fun e' => hadamardCode w (A e')) <;> cases hadamardCode k b <;> norm_num
    simp only [hpt, expect_sub_distrib, Fintype.expect_const,
      expect_boole_eq_one_div_two_of_map_add (hadamardCode_add _) hv]
    norm_num
  have hbound : equationTestAcceptance g A b ≤ 𝔼 k, 𝔼 t, (D k + (1 - c k t)) := by
    unfold equationTestAcceptance
    gcongr with k _ t _
    exact boole_le_add_one_sub fun hA hG => by rw [← hG]; exact hA
  simp only [expect_add_distrib, Fintype.expect_const] at hbound
  have hc : 𝔼 k, 𝔼 t, (1 - c k t) ≤ 2 * ε :=
    Fintype.expect_expect_one_sub_le fun k =>
      one_sub_two_mul_le_expect_selfCorrect_hadamardCode hg _
  linarith

/-! ### The Hadamard tester -/

/-- **Soundness of the Hadamard tester for quadratic equations**: if tables `f` and `g` pass the
linearity test with probabilities at least `1 - ε` and `1 - ε'`, the tensor test with probability
more than `3/4 + 4ε + 2ε'`, and the equation test for `A` and `b` with probability more than
`1/2 + 2ε'`, then `f` is within relative distance `ε` of the encoding of a solution `x` of the
quadratic equations `⟨x ⊗ x, A e⟩ = b e`. -/
theorem exists_forall_hadamardCode_tensor_eq_of_le_blrAcceptance {f : (ι → Bool) → Bool}
    {g : (ι × ι → Bool) → Bool} {A : κ → ι × ι → Bool} {b : κ → Bool} {ε ε' : ℝ}
    (hf : 1 - ε ≤ blrAcceptance f) (hg : 1 - ε' ≤ blrAcceptance g)
    (htensor : 3 / 4 + (4 * ε + 2 * ε') < tensorTestAcceptance f g)
    (hequation : 1 / 2 + 2 * ε' < equationTestAcceptance g A b) :
    ∃ x, (hammingDist f (hadamardCode x) : ℝ) / 2 ^ Fintype.card ι ≤ ε ∧
      ∀ e, hadamardCode (tensor x x) (A e) = b e := by
  obtain ⟨x, hx⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance hf
  obtain ⟨w, hw⟩ := exists_hammingDist_hadamardCode_le_of_le_blrAcceptance hg
  obtain rfl := eq_tensor_of_lt_tensorTestAcceptance hx hw htensor
  exact ⟨x, hx, hadamardCode_eq_of_lt_equationTestAcceptance hw hequation⟩

end Cslib.BitString
