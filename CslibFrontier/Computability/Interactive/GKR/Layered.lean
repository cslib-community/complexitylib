/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension

/-!
# Layered arithmetic circuits and the GKR identity

A *layered arithmetic circuit* of fan-in two (`Cslib.Interactive.GKR.LayeredCircuit`) has its gates
arranged in layers, with the gates of layer `i` labelled by the bit strings of length `width i`.
Layer `0` is the input. Every gate of layer `i + 1` is an addition or a multiplication of two gates
of layer `i`, its left and right in-neighbours. Evaluating the layers in turn gives the gate values
`value x i` on an input `x` (`Cslib.Interactive.GKR.LayeredCircuit.value`). We number the layers
from the input, while [Thaler, §4.6][Thaler2022] numbers them from the output.

The *wiring predicates* `add_i (a, b, c)` and `mult_i (a, b, c)` of layer `i + 1` are `1` exactly
when gate `a` of layer `i + 1` is an addition, respectively a multiplication, with in-neighbours
`b` and `c` (`addPred`, `multPred`). The identity at the heart of the GKR protocol expresses the
multilinear extension of the gate values of a layer through the multilinear extensions of the
wiring predicates and the gate values of the layer below
(`Cslib.Interactive.GKR.LayeredCircuit.eval_multilinearExtension_step`)
[Thaler, Lemma 4.7][Thaler2022], [Goldwasser, Kalai, Rothblum][GoldwasserKalaiRothblum2015]:
`W̃_{i+1}(z) = ∑_{b, c} ãdd_i(z, b, c) (W_i(b) + W_i(c)) + m̃ult_i(z, b, c) W_i(b) W_i(c)`.

## Main definitions

* `Cslib.Interactive.GKR.LayeredCircuit`: a layered arithmetic circuit of fan-in two.
* `Cslib.Interactive.GKR.LayeredCircuit.step`, `Cslib.Interactive.GKR.LayeredCircuit.value`:
  evaluation of one layer and of the circuit.
* `Cslib.Interactive.GKR.LayeredCircuit.addPred`, `Cslib.Interactive.GKR.LayeredCircuit.multPred`:
  the wiring predicates.

## Main results

* `Cslib.Interactive.GKR.LayeredCircuit.eval_multilinearExtension_wiringPred`: the closed form of
  the multilinear extensions of the wiring predicates (`addPred` and `multPred` are its two cases).
* `Cslib.Interactive.GKR.LayeredCircuit.eval_multilinearExtension_step`: the GKR identity.

## References

* [S. Goldwasser, Y. T. Kalai, G. N. Rothblum, *Delegating computation: interactive proofs for
  muggles*][GoldwasserKalaiRothblum2015]
* [J. Thaler, *Proofs, Arguments, and Zero-Knowledge*][Thaler2022], Section 4.6
-/

@[expose] public section

namespace Cslib.Interactive.GKR

open MvPolynomial Cslib.BitString

/-- The two kinds of gates of an arithmetic circuit of fan-in two. -/
inductive Gate
  /-- An addition gate. -/
  | add
  /-- A multiplication gate. -/
  | mul
  deriving DecidableEq

/-- A **layered arithmetic circuit** of fan-in two. The gates of layer `i` are labelled by bit
strings of length `width i`; layer `0` is the input, and each gate of layer `i + 1` combines two
gates of layer `i`. -/
structure LayeredCircuit where
  /-- The number of layers above the input. -/
  depth : ℕ
  /-- Layer `i` has `2 ^ width i` gates. -/
  width : ℕ → ℕ
  /-- The kind of each gate of layer `i + 1`. -/
  gate : (i : ℕ) → (Fin (width (i + 1)) → Bool) → Gate
  /-- The left in-neighbour, in layer `i`, of each gate of layer `i + 1`. -/
  left : (i : ℕ) → (Fin (width (i + 1)) → Bool) → Fin (width i) → Bool
  /-- The right in-neighbour, in layer `i`, of each gate of layer `i + 1`. -/
  right : (i : ℕ) → (Fin (width (i + 1)) → Bool) → Fin (width i) → Bool

namespace LayeredCircuit

variable (C : LayeredCircuit) {R : Type*} [CommRing R]

/-- The values of layer `i + 1`, given the values `W` of layer `i`. -/
def step (i : ℕ) (W : (Fin (C.width i) → Bool) → R) (a : Fin (C.width (i + 1)) → Bool) : R :=
  match C.gate i a with
  | .add => W (C.left i a) + W (C.right i a)
  | .mul => W (C.left i a) * W (C.right i a)

/-- The gate values of layer `i` on the input `x`. -/
def value (x : (Fin (C.width 0) → Bool) → R) : (i : ℕ) → (Fin (C.width i) → Bool) → R
  | 0 => x
  | i + 1 => C.step i (value x i)

/-- The output values of the circuit. -/
def output (x : (Fin (C.width 0) → Bool) → R) : (Fin (C.width C.depth) → Bool) → R :=
  C.value x C.depth

/-- The variables of a wiring predicate of layer `i + 1`: a gate `a` of layer `i + 1` and two gates
`b`, `c` of layer `i`. -/
abbrev WiringVar (i : ℕ) : Type := Fin (C.width (i + 1)) ⊕ (Fin (C.width i) ⊕ Fin (C.width i))

/-- The wiring predicate of a gate kind: `1` exactly when gate `a` of layer `i + 1` has that kind
and in-neighbours `b` and `c`. -/
def wiringPred (g : Gate) (i : ℕ) (v : C.WiringVar i → Bool) : R :=
  open Classical in
  if C.gate i (v ∘ Sum.inl) = g ∧ C.left i (v ∘ Sum.inl) = v ∘ Sum.inr ∘ Sum.inl ∧
      C.right i (v ∘ Sum.inl) = v ∘ Sum.inr ∘ Sum.inr then 1 else 0

/-- The addition predicate `add_i`. -/
abbrev addPred (i : ℕ) : (C.WiringVar i → Bool) → R := C.wiringPred .add i

/-- The multiplication predicate `mult_i`. -/
abbrev multPred (i : ℕ) : (C.WiringVar i → Bool) → R := C.wiringPred .mul i

/-- The multilinear extension of a wiring predicate at `(z, y, w)` is the sum, over the gates `a`
of that kind, of the product of the basis polynomials of `a`, its left and its right in-neighbour.
-/
theorem eval_multilinearExtension_wiringPred (g : Gate) (i : ℕ) (z : Fin (C.width (i + 1)) → R)
    (y w : Fin (C.width i) → R) :
    eval (Sum.elim z (Sum.elim y w)) (multilinearExtension (C.wiringPred (R := R) g i)) =
      ∑ a, if C.gate i a = g then eval z (indicatorPoly a) * eval y (indicatorPoly (C.left i a)) *
          eval w (indicatorPoly (C.right i a))
        else 0 := by
  simp only [multilinearExtension, map_sum, map_mul, eval_C, eval_indicatorPoly_apply]
  rw [← (Equiv.sumArrowEquivProdArrow _ _ Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Equiv.sumArrowEquivProdArrow _ _ Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, wiringPred]
  by_cases hg : C.gate i a = g
  · rw [ite_eq_left hg]
    rw [Finset.sum_eq_single (C.left i a), Finset.sum_eq_single (C.right i a)]
    · simp only [Function.comp_def, Equiv.sumArrowEquivProdArrow_symm_apply_inl, hg,
        Equiv.sumArrowEquivProdArrow_symm_apply_inr, and_self, ↓reduceIte, one_mul, mul_assoc]
      congr 1
    · intro c _ hc
      simp [Function.comp_def, Ne.symm hc]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun c _ => ?_
      simp [Function.comp_def, Ne.symm hb]
    · simp
  · rw [ite_eq_right hg]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
    simp [Function.comp_def, hg]

/-- **The GKR identity** [Thaler, Lemma 4.7][Thaler2022]. The multilinear extension of the values
of layer `i + 1` is a sum over the pairs of gates `b`, `c` of layer `i` of the multilinear
extensions of the wiring predicates times the sum, respectively the product, of the values of `b`
and `c`. -/
theorem eval_multilinearExtension_step (i : ℕ) (W : (Fin (C.width i) → Bool) → R)
    (z : Fin (C.width (i + 1)) → R) :
    eval z (multilinearExtension (C.step i W)) =
      ∑ b, ∑ c,
        (eval (Sum.elim z (Sum.elim (bitPoint b) (bitPoint c)))
            (multilinearExtension (C.addPred (R := R) i)) * (W b + W c) +
          eval (Sum.elim z (Sum.elim (bitPoint b) (bitPoint c)))
            (multilinearExtension (C.multPred (R := R) i)) * (W b * W c)) := by
  rw [eval_multilinearExtension_eq_sum (C.step i W)]
  simp only [eval_multilinearExtension_wiringPred, eval_indicatorPoly]
  have hinner : ∀ b c, (∑ a, if C.gate i a = .add then eval z (indicatorPoly a) *
        (if C.left i a = b then (1 : R) else 0) * (if C.right i a = c then 1 else 0) else 0) *
        (W b + W c) +
      (∑ a, if C.gate i a = .mul then eval z (indicatorPoly a) *
        (if C.left i a = b then (1 : R) else 0) * (if C.right i a = c then 1 else 0) else 0) *
        (W b * W c) =
      ∑ a, (if C.left i a = b ∧ C.right i a = c then eval z (indicatorPoly a) *
        (if C.gate i a = .add then W b + W c else W b * W c) else 0) := by
    intro b c
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hb : C.left i a = b <;> by_cases hc : C.right i a = c <;>
      cases C.gate i a <;> simp [hb, hc]
  simp only [hinner]
  symm
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (C.left i a), Finset.sum_eq_single (C.right i a)]
  · simp only [and_self, ite_true, step]
    cases C.gate i a <;> simp [mul_comm]
  · intro c _ hc
    simp [Ne.symm hc]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun c _ => by simp [Ne.symm hb]
  · simp

end LayeredCircuit

end Cslib.Interactive.GKR
