/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Pi
import CslibFrontier.Probability.PMF.Uniform

/-!
# Affine wire labels for arithmetic garbling

Arithmetic garbling schemes over a ring `R` label a wire carrying `x : R` by an *affine key
encoding* `k + x • s` of `x`, where `k : ι → R` is the wire's key and `s : ι → R` a slope, as in
the framework of Applebaum, Ishai and Kushilevitz [ApplebaumIshaiKushilevitz2011]. In the scheme
of Li and Liu [LiLiu2024] the slope is a global offset `Δ` shared by all arithmetic wires. With a
shared slope, addition and multiplication by public constants are free: the evaluator combines the
labels and the garbler combines the keys in the same way (`affineLabel_add_affineLabel`,
`smul_affineLabel`, `sum_smul_affineLabel`). A slope with a unit coordinate makes the label of a
known key determine the value (`affineLabel_injective`). The labels `(Δ x + A, x + α)` of
[LiLiu2024] have slope `(Δ, 1)`, so they satisfy this hypothesis.

Multiplication of two wires uses a degree-two affinization gadget in the sense of
[ApplebaumIshaiKushilevitz2011], the interface that [LiLiu2024] uses for multiplication gates; the
concrete four-value encoding below is one such gadget. To give the
evaluator the label `c + (x * y) • s` of the product from separate encodings of `x` and of `y`,
the garbler samples coins `r : R` and `b₁ b₀ : ι → R` and publishes four values
(`mulEncodeWith`): the scalar `r + x` and the vector `(c - r • b₁ - b₀) - x • b₁`, both affine in
`x`, and the vectors `b₁ + y • s` and `b₀ - y • (r • s)`, both affine in `y`. The decoder
`MulEncoding.decode` computes `z • v + u + w` from the four values `(z, u, v, w)`; it returns
the product's label (`decode_mulEncodeWith`). The gadget is perfectly private: over uniform coins
the four values are distributed exactly as the simulator `mulSimulate`, which sees only the output
label (`eval_mulEncode`). The proof is a change of variables `(r, b₁, b₀) ↦ (z, v, u)` that is a
bijection for every `x`, `y`.

This file contains the information-theoretic layer only. How a garbler delivers the encodings of
`x` and of `y` to the evaluator (key extension, random oracles) is not formalized here.

## Main definitions

* `Cslib.Crypto.Garbling.Arithmetic.affineLabel`: the affine key encoding `k + x • s`.
* `Cslib.Crypto.Garbling.Arithmetic.MulEncoding`: the four values of the multiplication gadget.
* `Cslib.Crypto.Garbling.Arithmetic.mulEncodeWith`, `Cslib.Crypto.Garbling.Arithmetic.mulEncode`:
  the gadget with given coins and with uniform coins.
* `Cslib.Crypto.Garbling.Arithmetic.mulSimulateWith`,
  `Cslib.Crypto.Garbling.Arithmetic.mulSimulate`: its simulator.

## Main results

* `Cslib.Crypto.Garbling.Arithmetic.affineLabel_add_affineLabel`,
  `Cslib.Crypto.Garbling.Arithmetic.smul_affineLabel`,
  `Cslib.Crypto.Garbling.Arithmetic.sum_smul_affineLabel`: free linear operations.
* `Cslib.Crypto.Garbling.Arithmetic.affineLabel_injective`: a unit slope coordinate makes the
  label determine the value.
* `Cslib.Crypto.Garbling.Arithmetic.decode_mulEncodeWith`: correctness of the multiplication
  gadget.
* `Cslib.Crypto.Garbling.Arithmetic.eval_mulEncode`: its perfect privacy.

## References

* [B. Applebaum, Y. Ishai, E. Kushilevitz, *How to Garble Arithmetic
  Circuits*][ApplebaumIshaiKushilevitz2011]
* [H. Li, T. Liu, *How to Garble Mixed Circuits that Combine Boolean and Arithmetic
  Computations*][LiLiu2024]
-/

public section

namespace Cslib.Crypto.Garbling.Arithmetic

open Probability

variable {R ι : Type}

section Label

variable [Semiring R]

/-- The affine key encoding of `x` under key `k` and slope `s`: the label `k + x • s`. -/
@[expose] def affineLabel (k s : ι → R) (x : R) : ι → R := k + x • s

@[simp] theorem affineLabel_apply (k s : ι → R) (x : R) (i : ι) :
    affineLabel k s x i = k i + x * s i := rfl

@[simp] theorem affineLabel_zero (k s : ι → R) : affineLabel k s 0 = k := by
  simp [affineLabel]

/-- **Free addition**: the sum of two labels under one slope is the label of the sum under the
sum of the keys. -/
theorem affineLabel_add_affineLabel (k₁ k₂ s : ι → R) (x₁ x₂ : R) :
    affineLabel k₁ s x₁ + affineLabel k₂ s x₂ = affineLabel (k₁ + k₂) s (x₁ + x₂) := by
  simp only [affineLabel, add_smul]
  abel

/-- **Free constant multiplication**: scaling a label by a public constant `c` gives the label of
`c * x` under the scaled key. -/
theorem smul_affineLabel (c : R) (k s : ι → R) (x : R) :
    c • affineLabel k s x = affineLabel (c • k) s (c * x) := by
  simp only [affineLabel, smul_add, mul_smul]

/-- **Free linear combinations**: a public linear combination of labels under one slope is the
label of the combination of the values under the combination of the keys. -/
theorem sum_smul_affineLabel {σ : Type} (t : Finset σ) (c : σ → R) (k : σ → ι → R)
    (s : ι → R) (x : σ → R) :
    ∑ j ∈ t, c j • affineLabel (k j) s (x j) =
      affineLabel (∑ j ∈ t, c j • k j) s (∑ j ∈ t, c j * x j) := by
  simp only [affineLabel, smul_add, mul_smul, Finset.sum_add_distrib, Finset.sum_smul]

/-- Ring homomorphisms carry labels to labels. Through the Chinese remainder isomorphism
`ZMod.prodEquivPi`, a label over `ℤ/N` is therefore a family of labels over the channels. -/
theorem map_affineLabel {S : Type} [Semiring S] (f : R →+* S) (k s : ι → R) (x : R) :
    (fun i => f (affineLabel k s x i)) =
      affineLabel (fun i => f (k i)) (fun i => f (s i)) (f x) := by
  funext i
  simp only [affineLabel_apply, map_add, map_mul]

end Label

section Ring

variable [Ring R]

/-- The difference of two labels under one slope is the label of the difference under the
difference of the keys. -/
theorem affineLabel_sub_affineLabel (k₁ k₂ s : ι → R) (x₁ x₂ : R) :
    affineLabel k₁ s x₁ - affineLabel k₂ s x₂ = affineLabel (k₁ - k₂) s (x₁ - x₂) := by
  simp only [affineLabel, sub_smul]
  abel

/-- If the slope has a unit coordinate `j`, the label under a fixed key determines the value: it
is `(label j - k j) * (s j)⁻¹`. -/
theorem affineLabel_injective (k s : ι → R) {j : ι} (hj : IsUnit (s j)) :
    Function.Injective (affineLabel k s) := by
  intro x₁ x₂ h
  have h' := congrFun h j
  simp only [affineLabel_apply, add_right_inj] at h'
  exact hj.mul_left_injective h'

end Ring

/-! ### The multiplication gadget -/

/-- The four values of the multiplication gadget: `z` and `u` are affine in the left input, `v`
and `w` in the right input. -/
structure MulEncoding (R ι : Type) where
  /-- The left input masked by the scalar coin. -/
  z : R
  /-- A vector affine in the left input. -/
  u : ι → R
  /-- A vector affine in the right input, with slope the target slope. -/
  v : ι → R
  /-- A vector affine in the right input, with slope the target slope scaled by the coin. -/
  w : ι → R

section Mul

variable [CommRing R]

/-- The decoder: `z • v + u + w`. -/
@[expose] def MulEncoding.decode (e : MulEncoding R ι) : ι → R := e.z • e.v + e.u + e.w

/-- The multiplication gadget for target slope `s` and key `c`, with coins `r`, `b₁`, `b₀`: the
left values `r + x` and `affineLabel (c - r • b₁ - b₀) (-b₁) x` depend only on `x`, the right
values `affineLabel b₁ s y` and `affineLabel b₀ (-(r • s)) y` only on `y`. -/
@[expose] def mulEncodeWith (s c : ι → R) (r : R) (b₁ b₀ : ι → R) (x y : R) : MulEncoding R ι where
  z := r + x
  u := affineLabel (c - r • b₁ - b₀) (-b₁) x
  v := affineLabel b₁ s y
  w := affineLabel b₀ (-(r • s)) y

/-- **Correctness**: the decoder returns the label `c + (x * y) • s` of the product. -/
theorem decode_mulEncodeWith (s c : ι → R) (r : R) (b₁ b₀ : ι → R) (x y : R) :
    (mulEncodeWith s c r b₁ b₀ x y).decode = affineLabel c s (x * y) := by
  funext i
  simp only [MulEncoding.decode, mulEncodeWith, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    affineLabel_apply, Pi.sub_apply, Pi.neg_apply]
  ring

/-- The simulator with given coins: from the output label `L`, it publishes `z`, `u`, `v` and
the vector `L - z • v - u` that makes the decoder return `L`. -/
@[expose] def mulSimulateWith (L : ι → R) (z : R) (v u : ι → R) : MulEncoding R ι where
  z := z
  u := u
  v := v
  w := L - z • v - u

/-- Simulated encodings decode to the output label. -/
theorem decode_mulSimulateWith (L : ι → R) (z : R) (v u : ι → R) :
    (mulSimulateWith L z v u).decode = L := by
  simp only [MulEncoding.decode, mulSimulateWith]
  abel

/-- The coins of the gadget, recovered from the simulator's coins `(z, v, u)`. -/
theorem mulEncodeWith_eq_mulSimulateWith (s c : ι → R) (x y z : R) (v u : ι → R) :
    mulEncodeWith s c (z - x) (v - y • s) (c - z • (v - y • s) - u) x y =
      mulSimulateWith (affineLabel c s (x * y)) z v u := by
  simp only [mulEncodeWith, mulSimulateWith, MulEncoding.mk.injEq]
  refine ⟨sub_add_cancel z x, ?_, ?_, ?_⟩ <;> funext i <;>
    simp only [affineLabel_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

variable [Fintype R] [Fintype ι] [DecidableEq ι]

/-- The multiplication gadget with uniform coins. -/
noncomputable def mulEncode (s c : ι → R) (x y : R) : ProbComp (MulEncoding R ι) := do
  let r ← ProbComp.uniform R
  let b₁ ← ProbComp.uniform (ι → R)
  let b₀ ← ProbComp.uniform (ι → R)
  return mulEncodeWith s c r b₁ b₀ x y

/-- The simulator: uniform `z`, `v`, `u`, and the vector fixed by the output label `L`. -/
noncomputable def mulSimulate (L : ι → R) : ProbComp (MulEncoding R ι) := do
  let z ← ProbComp.uniform R
  let v ← ProbComp.uniform (ι → R)
  let u ← ProbComp.uniform (ι → R)
  return mulSimulateWith L z v u

omit [CommRing R] [DecidableEq ι] in
/-- Reparametrizing a uniform sample by a bijection does not change an experiment. -/
private theorem bind_uniform_comp_equiv {α β : Type} [Fintype α] [Nonempty α] (e : α ≃ α)
    (f : α → PMF β) :
    (PMF.uniformOfFintype α).bind (fun a => f (e a)) = (PMF.uniformOfFintype α).bind f :=
  calc _ = (PMF.uniformOfFintype α).bind (f ∘ e) := rfl
    _ = _ := by rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- **Perfect privacy**: over uniform coins, the gadget's encoding of `x` and `y` is distributed
exactly as the simulation from the product's label `c + (x * y) • s` alone. -/
theorem eval_mulEncode (s c : ι → R) (x y : R) :
    (mulEncode s c x y).eval = (mulSimulate (affineLabel c s (x * y))).eval := by
  simp only [mulEncode, mulSimulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure]
  rw [← bind_uniform_comp_equiv (Equiv.subRight x)]
  refine congrArg _ (funext fun z => ?_)
  rw [← bind_uniform_comp_equiv (Equiv.subRight (y • s))]
  refine congrArg _ (funext fun v => ?_)
  rw [← bind_uniform_comp_equiv (Equiv.subLeft (c - z • (v - y • s)))]
  refine congrArg _ (funext fun u => ?_)
  simp only [Equiv.subRight_apply, Equiv.subLeft_apply]
  rw [mulEncodeWith_eq_mulSimulateWith]

end Mul

end Cslib.Crypto.Garbling.Arithmetic
