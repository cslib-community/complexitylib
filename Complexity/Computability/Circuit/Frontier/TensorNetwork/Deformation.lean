/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Deformed contractions and the Cauchy kernel

This file starts the proof of the Boolean tensor contraction theorem of [OpenAI2026ETH]
(Theorem D.1, §D.1, p. 53) with the deformation of §D.4.3 (p. 59).

**Deformed contraction** (`TensorNetwork.deformedContraction`). Split the vertices of a Boolean
tensor network into *rows* (`side v = true`) and *columns*. Give each edge `e` a *row bit* `Y e`,
read by the row tensors, and a *column bit* `X e`, read by the column tensors. For a matrix `W`
indexed by the edges, the deformed contraction is

  `F(W) = ∑ X Y, A(Y) B(X) ∏ e, l_{Y e}((W X) e)`,

where `A` and `B` are the products of the row and column tensors, `l_false z = 1 - z` and
`l_true z = z` (the manuscript's (D.8), with `l₀`, `l₁`). At the identity matrix the product of
the affine factors is the indicator of `X = Y`, so `F(1)` is the contraction
(`TensorNetwork.deformedContraction_one`). Deforming `W` away from the identity lets the
interactions between groups of ports be expanded separately; that expansion is later work.

**The Cauchy kernel** (`cauchyKernel`). On the grid `S = {-L, …, L - 1}`, with
`C(T) = ∏_{t ∈ S} (T - t)`, the kernel at `d ∈ S` is the polynomial `C(T) / (C'(0) (T - d))` of
(D.7). It is one at `T = 0` when `d = 0` and vanishes at every other grid point
(`eval_zero_cauchyKernel`, `eval_cauchyKernel_of_ne`). The *Cauchy matrix* of a packing of the
edges (`cauchyMatrix`), with entry `cauchyKernel L (slot e' - slot e)` between edges of the same
packet and zero between packets, is therefore the identity at `T = 0` when every edge has its own
slot in its packet (`cauchyMatrix_eval_zero`), and the deformed contraction along it evaluates to
the contraction at zero (`eval_zero_deformedContraction_cauchyMatrix`).

## Main definitions

* `Cslib.Circuits.Frontier.TensorNetwork.map`: a tensor network with its tensors mapped by a
  ring homomorphism.
* `Cslib.Circuits.Frontier.TensorNetwork.affineFactor`: the affine factors `l_b`.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction`: the deformed contraction `F(W)`.
* `Cslib.Circuits.Frontier.cauchyGrid`, `Cslib.Circuits.Frontier.cauchyKernel`,
  `Cslib.Circuits.Frontier.cauchyMatrix`: the grid, the Cauchy kernel and the Cauchy matrix of a
  packing.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.contraction_map`: contraction commutes with ring
  homomorphisms, e.g. reduction of integer entries modulo `2 ^ P`.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_one`: `F(1) = Z`.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_map`: deformed contraction commutes
  with ring homomorphisms.
* `Cslib.Circuits.Frontier.eval_zero_cauchyKernel`,
  `Cslib.Circuits.Frontier.eval_cauchyKernel_of_ne`: values of the kernel on the grid.
* `Cslib.Circuits.Frontier.natDegree_cauchyKernel`: its degree `2 L - 1`.
* `Cslib.Circuits.Frontier.cauchyMatrix_eval_zero`: the Cauchy matrix is the identity at zero.
* `Cslib.Circuits.Frontier.TensorNetwork.eval_zero_deformedContraction_cauchyMatrix`: the
  polynomial `F(T)` along the Cauchy matrix has value `Z` at `T = 0`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.3, (D.7)–(D.8),
  p. 59.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Polynomial

namespace TensorNetwork

variable {R S U V E : Type*}

/-! ### Mapping the tensors -/

section Map

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

/-- The tensor network with every tensor entry mapped by the ring homomorphism `f`. -/
def map (N : TensorNetwork R U V E) : TensorNetwork S U V E where
  toMultigraph := N.toMultigraph
  tensor v x := f (N.tensor v x)
  tensor_congr v x y h := by rw [N.tensor_congr v x y h]

@[simp] theorem map_tensor (N : TensorNetwork R U V E) (v : V) (x : E → U) :
    (N.map f).tensor v x = f (N.tensor v x) :=
  rfl

@[simp] theorem toMultigraph_map (N : TensorNetwork R U V E) :
    (N.map f).toMultigraph = N.toMultigraph :=
  rfl

/-- **Contraction commutes with ring homomorphisms.** For instance, contracting integer tensors
and reducing modulo `2 ^ P` is contracting the reduced tensors. -/
theorem contraction_map [Fintype U] [Fintype V] [Fintype E] [DecidableEq E]
    (N : TensorNetwork R U V E) : (N.map f).contraction = f N.contraction := by
  simp only [contraction, map_tensor, map_sum, map_prod]

end Map

/-! ### Deformed contraction -/

section Deformed

variable [CommRing R] [Fintype V] [Fintype E] [DecidableEq E]

/-- The affine factor `l_b`: `l_b z = z` for `b = true` and `l_b z = 1 - z` for `b = false`. At a
bit `z`, it is the indicator of `z = b`. -/
def affineFactor (b : Bool) (z : R) : R :=
  if b then z else 1 - z

/-- At a bit, the affine factor is the indicator of equality. -/
theorem affineFactor_bit (b c : Bool) :
    affineFactor b (if c then (1 : R) else 0) = if b = c then 1 else 0 := by
  cases b <;> cases c <;> simp [affineFactor]

/-- The *deformed contraction* of a Boolean tensor network whose vertices are split into rows
(`side v = true`) and columns, along a matrix `W` indexed by the edges: every edge carries a row
bit, read by the row tensors, and a column bit, read by the column tensors, joined through the
affine factors of `W`. -/
def deformedContraction (N : TensorNetwork R Bool V E) (side : V → Bool) (W : Matrix E E R) : R :=
  ∑ X : E → Bool, ∑ Y : E → Bool,
    (∏ v ∈ Finset.univ.filter (side · = true), N.tensor v Y) *
      (∏ v ∈ Finset.univ.filter (side · = false), N.tensor v X) *
      ∏ e, affineFactor (Y e) (W.mulVec (fun e' => if X e' then 1 else 0) e)

/-- **The deformed contraction at the identity is the contraction.** The affine factors of the
identity matrix force the row bits to equal the column bits. -/
theorem deformedContraction_one (N : TensorNetwork R Bool V E) (side : V → Bool) :
    N.deformedContraction side 1 = N.contraction := by
  classical
  simp only [deformedContraction, Matrix.one_mulVec, affineFactor_bit, Fintype.prod_boole,
    ← funext_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun X _ => ?_
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => side v = true)
    (fun v => N.tensor v X)
  simp only [Bool.not_eq_true] at h
  exact h

/-- Deformed contraction commutes with ring homomorphisms. -/
theorem deformedContraction_map {S : Type*} [CommRing S] (f : R →+* S)
    (N : TensorNetwork R Bool V E) (side : V → Bool) (W : Matrix E E R) :
    (N.map f).deformedContraction side (W.map f) = f (N.deformedContraction side W) := by
  simp only [deformedContraction, map_sum, map_mul, map_prod, map_tensor]
  refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun Y _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun e _ => ?_
  have hv : (W.map f).mulVec (fun e' => if X e' then (1 : S) else 0) =
      fun e => f (W.mulVec (fun e' => if X e' then (1 : R) else 0) e) := by
    ext e
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, apply_ite f,
      map_one, map_zero]
  rw [hv]
  cases Y e <;> simp [affineFactor]

end Deformed

end TensorNetwork

/-! ### The Cauchy kernel -/

/-- The interpolation grid `S = {-L, …, L - 1}` of a packet with `L` slots. -/
def cauchyGrid (L : ℕ) : Finset ℤ :=
  Finset.Ico (-L : ℤ) L

theorem mem_cauchyGrid {L : ℕ} {t : ℤ} : t ∈ cauchyGrid L ↔ -(L : ℤ) ≤ t ∧ t < L :=
  Finset.mem_Ico

/-- The difference of two slots of a packet lies on the grid. -/
theorem sub_mem_cauchyGrid {L : ℕ} {x y : ℕ} (hx : x < L) (hy : y < L) :
    (y : ℤ) - x ∈ cauchyGrid L := by
  rw [mem_cauchyGrid]
  omega

/-- The *Cauchy kernel* at `d` on the grid of `L` slots: `C(T) / (C'(0) (T - d))`, where
`C(T) = ∏_{t ∈ S} (T - t)`. For `d ∈ S` it is the polynomial `C'(0)⁻¹ ∏_{t ∈ S, t ≠ d} (T - t)`
of degree `2 L - 1`; here `C'(0) = ∏_{t ∈ S, t ≠ 0} (0 - t)`. -/
noncomputable def cauchyKernel (L : ℕ) (d : ℤ) : ℚ[X] :=
  C ((Lagrange.nodal ((cauchyGrid L).erase 0) (Int.cast : ℤ → ℚ)).eval 0)⁻¹ *
    Lagrange.nodal ((cauchyGrid L).erase d) (Int.cast : ℤ → ℚ)

/-- The normalization is `C'(0)`, the derivative of `C(T) = ∏_{t ∈ S} (T - t)` at zero. -/
theorem eval_zero_nodal_erase_zero {L : ℕ} (hL : 0 < L) :
    (Lagrange.nodal ((cauchyGrid L).erase 0) (Int.cast : ℤ → ℚ)).eval 0 =
      (derivative (Lagrange.nodal (cauchyGrid L) (Int.cast : ℤ → ℚ))).eval 0 := by
  have h0 : (0 : ℤ) ∈ cauchyGrid L := by rw [mem_cauchyGrid]; omega
  have := Lagrange.eval_nodal_derivative_eval_node_eq (v := (Int.cast : ℤ → ℚ)) h0
  simpa using this.symm

/-- `C'(0)` is nonzero: the grid has distinct points. -/
theorem eval_zero_nodal_erase_zero_ne_zero (L : ℕ) :
    (Lagrange.nodal ((cauchyGrid L).erase 0) (Int.cast : ℤ → ℚ)).eval 0 ≠ 0 := by
  rw [Lagrange.eval_nodal, Finset.prod_ne_zero_iff]
  intro t ht
  have : t ≠ 0 := Finset.ne_of_mem_erase ht
  simpa [sub_eq_zero, eq_comm] using this

/-- On the grid, the kernel has degree `2 L - 1`, so a deformed contraction along a Cauchy matrix
has degree at most `M (2 L - 1)` in `T` for `M` edges. -/
theorem natDegree_cauchyKernel {L : ℕ} {d : ℤ} (hd : d ∈ cauchyGrid L) :
    (cauchyKernel L d).natDegree = 2 * L - 1 := by
  rw [cauchyKernel, natDegree_C_mul (inv_ne_zero (eval_zero_nodal_erase_zero_ne_zero L)),
    Lagrange.natDegree_nodal, Finset.card_erase_of_mem hd, cauchyGrid, Int.card_Ico]
  omega

/-- **The kernel at zero.** The kernel at `d = 0` is one at `T = 0`. -/
theorem eval_zero_cauchyKernel_zero (L : ℕ) : (cauchyKernel L 0).eval 0 = 1 := by
  rw [cauchyKernel, eval_mul, eval_C]
  exact inv_mul_cancel₀ (eval_zero_nodal_erase_zero_ne_zero L)

/-- **The kernel vanishes at the other grid points.** The kernel at `d` vanishes at every grid
point `t ≠ d`. -/
theorem eval_cauchyKernel_of_ne {L : ℕ} {d t : ℤ} (ht : t ∈ cauchyGrid L) (htd : t ≠ d) :
    (cauchyKernel L d).eval (t : ℚ) = 0 := by
  rw [cauchyKernel, eval_mul, Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨htd, ht⟩),
    mul_zero]

/-- The values of the kernel at `T = 0`: one at `d = 0`, and zero at every `d ≠ 0`, because then
`T = 0` is a root of one of its factors. -/
theorem eval_zero_cauchyKernel {L : ℕ} (hL : 0 < L) (d : ℤ) :
    (cauchyKernel L d).eval 0 = if d = 0 then 1 else 0 := by
  split_ifs with h
  · rw [h, eval_zero_cauchyKernel_zero]
  · have h0 : (0 : ℤ) ∈ cauchyGrid L := by rw [mem_cauchyGrid]; omega
    simpa using eval_cauchyKernel_of_ne h0 (Ne.symm h)

/-- The *Cauchy matrix* of a packing of the edges into packets of `L` slots: between edges `e`
and `e'` of the same packet, the Cauchy kernel at the difference `slot e' - slot e` of their
slots; zero between different packets (the manuscript's (D.7)). -/
noncomputable def cauchyMatrix {E P : Type*} [DecidableEq P] (L : ℕ) (packet : E → P)
    (slot : E → ℕ) : Matrix E E ℚ[X] :=
  fun e e' => if packet e = packet e' then cauchyKernel L ((slot e' : ℤ) - slot e) else 0

/-- **The Cauchy matrix is the identity at zero** when every edge has its own slot in its packet,
below `L`. -/
theorem cauchyMatrix_eval_zero {E P : Type*} [DecidableEq E] [DecidableEq P] {L : ℕ}
    {packet : E → P} {slot : E → ℕ} (hslot : ∀ e, slot e < L)
    (hinj : ∀ e e', packet e = packet e' → slot e = slot e' → e = e') :
    (cauchyMatrix L packet slot).map (eval 0) = 1 := by
  ext e e'
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le _) (hslot e)
  simp only [Matrix.map_apply, cauchyMatrix, Matrix.one_apply]
  split_ifs with hp he he
  · subst he; simp [eval_zero_cauchyKernel_zero]
  · rw [eval_zero_cauchyKernel hL, ite_eq_right]
    intro h
    exact he (hinj e e' hp (by omega))
  · subst he; exact absurd rfl hp
  · exact eval_zero

namespace TensorNetwork

variable {R V E P : Type*} [CommRing R] [Algebra ℚ R] [Fintype V] [Fintype E] [DecidableEq E]
  [DecidableEq P]

/-- **The deformation along the Cauchy matrix starts at the contraction.** Over a `ℚ`-algebra,
the deformed contraction along the Cauchy matrix of a packing is a polynomial `F(T)` whose value at
`T = 0` is the contraction, when every edge has its own slot in its packet. -/
theorem eval_zero_deformedContraction_cauchyMatrix (N : TensorNetwork R Bool V E)
    (side : V → Bool) {L : ℕ} {packet : E → P} {slot : E → ℕ} (hslot : ∀ e, slot e < L)
    (hinj : ∀ e e', packet e = packet e' → slot e = slot e' → e = e') :
    ((N.map Polynomial.C).deformedContraction side
        ((cauchyMatrix L packet slot).map (Polynomial.mapRingHom (algebraMap ℚ R)))).eval 0 =
      N.contraction := by
  have h := deformedContraction_map (Polynomial.evalRingHom (0 : R)) (N.map Polynomial.C) side
    ((cauchyMatrix L packet slot).map (Polynomial.mapRingHom (algebraMap ℚ R)))
  rw [coe_evalRingHom] at h
  rw [← h]
  have hN : (N.map Polynomial.C).map (Polynomial.evalRingHom (0 : R)) = N := by
    cases N
    simp [map]
  have hW : ((cauchyMatrix L packet slot).map (Polynomial.mapRingHom (algebraMap ℚ R))).map
      (eval 0) = 1 := by
    rw [Matrix.map_map]
    have : (eval (0 : R) ∘ ⇑(Polynomial.mapRingHom (algebraMap ℚ R))) =
        (algebraMap ℚ R) ∘ (eval 0) := by
      ext p
      simp only [Function.comp_apply, coe_mapRingHom, eval_map, eval₂_at_zero,
        coeff_zero_eq_eval_zero]
    rw [this, ← Matrix.map_map, cauchyMatrix_eval_zero hslot hinj,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hN, hW, deformedContraction_one]

end TensorNetwork

end Cslib.Circuits.Frontier
