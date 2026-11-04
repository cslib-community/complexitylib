/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CauchyModes

/-!
# The deformed contraction in local coordinates

This file connects the polynomial `F(T)` of (D.8) in [OpenAI2026ETH] (§D.4.3, p. 59) with its
values at the interpolation points of §D.4.4–§D.4.5 (pp. 61–62).

Let `B` be a commutative ring receiving `ℤ_(2)` through `κ`, and let `N` be a Boolean tensor network
with entries in `B`. For a packing of the edges into packets of `2 ^ a` slots and a grid point `t`,
the *local deformation* (`TensorNetwork.localDeformation`) is the deformed contraction of `N` along
the matrix of local kernels `W_{y - x}(t + α z)` over `B[z]` (`cauchyLocalMatrix`), built from
`Cslib.Circuits.Frontier.localKernel`. It is the manuscript's `F(t + α z) ∈ A[z]`:

* in a `ℚ`-algebra `R` receiving `B` compatibly with `ℚ`, its image is `F(t + α z)`, where `F(T)`
  is the deformed contraction along the Cauchy matrix
  (`TensorNetwork.map_localDeformation`), whose value at `0` is the contraction
  (`TensorNetwork.eval_zero_deformedContraction_cauchyMatrix`);
* under any ring homomorphism `π : B → R'`, its value at `z = ζ` is the deformed contraction of the
  reduced network along the Cauchy matrix at `T = t + α ζ`
  (`TensorNetwork.eval₂_localDeformation`), which the child identity
  `TensorNetwork.deformedContraction_cauchyValueMatrix_eq_sum` expands when `2 ^ p = 0` in `R'`.

So the values of the children of §D.4.6 at `ζ` are values of one polynomial over `B`, and
interpolation recovers its reduction.

## Main definitions

* `Cslib.Circuits.Frontier.cauchyLocalMatrix`: the Cauchy matrix of a packing in local
  coordinates, over `B[z]`.
* `Cslib.Circuits.Frontier.TensorNetwork.localDeformation`: `F(t + α z)` over `B`.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.map_localDeformation`: its image in a `ℚ`-algebra is
  `F(t + α z)`.
* `Cslib.Circuits.Frontier.TensorNetwork.eval₂_localDeformation`: its values are deformed
  contractions along `cauchyValueMatrix`.
* `Cslib.Circuits.Frontier.TensorNetwork.natDegree_deformedContraction_le`,
  `Cslib.Circuits.Frontier.TensorNetwork.natDegree_localDeformation_le`,
  `Cslib.Circuits.Frontier.TensorNetwork.natDegree_deformedContraction_cauchyMatrix_le`: both have
  degree at most `M (2 L - 1)` for `M` edges and `L` slots.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.3–§D.4.5,
  pp. 59–62.
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

variable {B V E P : Type*} [CommRing B]

/-- The Cauchy matrix of a packing into packets of `2 ^ a` slots in local coordinates
`z ↦ W(t + α z)`, `α = 2 ^ (a + 1)`, over `B[z]` for a ring `B` receiving `ℤ_(2)` through `κ`:
between two edges of the same packet, the local kernel at the difference of their slots, and zero
between packets. -/
@[expose] noncomputable def cauchyLocalMatrix [DecidableEq P] (κ : ℤ₍₂₎ →+* B) (a : ℕ) (t : ℤ)
    (packet : E → P) (slot : E → ℕ) : Matrix E E B[X] :=
  fun e e' =>
    if packet e = packet e' then (localKernel a t ((slot e' : ℤ) - slot e)).map κ else 0

namespace TensorNetwork

/-- Mapping the tensors twice is mapping them by the composition. -/
theorem map_map {R S T U : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) (N : TensorNetwork R U V E) : (N.map f).map g = N.map (g.comp f) :=
  rfl

variable [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq P]

/-- The deformed contraction along the Cauchy matrix of a packing in local coordinates at the grid
point `t`, as a polynomial in `z` over `B`: the manuscript's `F(t + α z) ∈ A[z]`. -/
@[expose] noncomputable def localDeformation (N : TensorNetwork B Bool V E) (side : V → Bool)
    (κ : ℤ₍₂₎ →+* B) (a : ℕ) (t : ℤ) (packet : E → P) (slot : E → ℕ) : B[X] :=
  (N.map C).deformedContraction side (cauchyLocalMatrix κ a t packet slot)

/-- **The local deformation is `F(t + α z)`.** In a `ℚ`-algebra `R` receiving `B` through `ι`
compatibly with `ℚ`, the image of the local deformation at a grid point `t` is the deformed
contraction `F(T)` along the Cauchy matrix, composed with `T = t + α z`. -/
theorem map_localDeformation {R : Type*} [CommRing R] [Algebra ℚ R] (N : TensorNetwork B Bool V E)
    (side : V → Bool) (κ : ℤ₍₂₎ →+* B) (ι : B →+* R)
    (hκ : ι.comp κ = (algebraMap ℚ R).comp (ℤ₍₂₎).subtype) {a : ℕ} {packet : E → P}
    {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) :
    (N.localDeformation side κ a t packet slot).map ι =
      (((N.map ι).map C).deformedContraction side
        ((cauchyMatrix (2 ^ a) packet slot).map (mapRingHom (algebraMap ℚ R)))).comp
          (C (t : R) + C (2 ^ (a + 1)) * X) := by
  rw [← coe_mapRingHom, localDeformation, ← deformedContraction_map, ← coe_compRingHom_apply,
    ← deformedContraction_map, map_map, map_map, map_map]
  have hlin : (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).map (algebraMap ℚ R) =
      C (t : R) + C (2 ^ (a + 1)) * X := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, map_intCast, map_pow, map_ofNat]
  congr 1
  · congr 1
    ext x : 1
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, Polynomial.map_C,
      coe_compRingHom_apply, C_comp]
  · ext e e'
    simp only [Matrix.map_apply, cauchyLocalMatrix, cauchyMatrix, coe_mapRingHom,
      coe_compRingHom_apply]
    split_ifs with hp
    · rw [Polynomial.map_map, hκ, ← Polynomial.map_map,
        map_localKernel ht (sub_mem_cauchyGrid (hslot e) (hslot e')), Polynomial.map_comp, hlin]
    · rw [Polynomial.map_zero, Polynomial.map_zero, zero_comp]

/-- **Values of the local deformation.** Under a ring homomorphism `π : B → R'`, the value of the
local deformation at `z = ζ` is the deformed contraction of the reduced network along the Cauchy
matrix at `T = t + α ζ`. -/
theorem eval₂_localDeformation {R' : Type*} [CommRing R'] (N : TensorNetwork B Bool V E)
    (side : V → Bool) (κ : ℤ₍₂₎ →+* B) (π : B →+* R') (ζ : R') (a : ℕ) (t : ℤ) (packet : E → P)
    (slot : E → ℕ) :
    (N.localDeformation side κ a t packet slot).eval₂ π ζ =
      (N.map π).deformedContraction side (cauchyValueMatrix (π.comp κ) ζ a t packet slot) := by
  rw [← coe_eval₂RingHom, localDeformation, ← deformedContraction_map, map_map]
  congr 1
  · congr 1
    ext x : 1
    simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C]
  · ext e e'
    simp only [Matrix.map_apply, cauchyLocalMatrix, cauchyValueMatrix, coe_eval₂RingHom]
    split_ifs
    · rw [eval₂_map]
      rfl
    · exact eval₂_zero _ _

/-! ### Degrees -/

/-- **Degree of a deformed contraction.** For tensors that are constants and a matrix whose entries
have degree at most `d`, the deformed contraction has degree at most `d` times the number of
edges: it is a sum of products of one affine factor per edge. -/
theorem natDegree_deformedContraction_le {R : Type*} [CommRing R] (N : TensorNetwork R Bool V E)
    (side : V → Bool) (W : Matrix E E R[X]) {d : ℕ} (hW : ∀ e e', (W e e').natDegree ≤ d) :
    ((N.map C).deformedContraction side W).natDegree ≤ Fintype.card E * d := by
  unfold deformedContraction
  refine natDegree_sum_le_of_forall_le _ _ fun X _ => natDegree_sum_le_of_forall_le _ _
    fun Y _ => ?_
  have hc : ∀ s : Finset V, ∀ x : E → Bool, (∏ v ∈ s, (N.map C).tensor v x).natDegree = 0 :=
    fun s x => by simp only [map_tensor, ← map_prod, natDegree_C]
  have hv : ∀ e, (W.mulVec (fun e' => if X e' then (1 : R[X]) else 0) e).natDegree ≤ d := by
    intro e
    refine natDegree_sum_le_of_forall_le _ _ fun e' _ => ?_
    dsimp only
    split_ifs
    · rw [mul_one]; exact hW e e'
    · rw [mul_zero, natDegree_zero]; exact Nat.zero_le _
  have hprod : (∏ e, affineFactor (Y e)
      (W.mulVec (fun e' => if X e' then (1 : R[X]) else 0) e)).natDegree ≤ Fintype.card E * d := by
    refine (natDegree_prod_le _ _).trans ?_
    rw [← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_le_sum fun e _ => ?_
    unfold affineFactor
    split_ifs
    · exact hv e
    · exact (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; exact Nat.zero_le _)
        (hv e))
  refine (natDegree_mul_le).trans ?_
  have h2 := natDegree_mul_le (p := ∏ v ∈ Finset.univ.filter (side · = true), (N.map C).tensor v Y)
    (q := ∏ v ∈ Finset.univ.filter (side · = false), (N.map C).tensor v X)
  rw [hc, hc] at h2
  omega

/-- On the grid, the local kernel has degree at most `2 L - 1`, `L = 2 ^ a`. -/
theorem natDegree_localKernel_le {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) : (localKernel a t d).natDegree ≤ 2 * 2 ^ a - 1 := by
  rw [← natDegree_map_eq_of_injective (f := (ℤ₍₂₎).subtype) Subtype.val_injective,
    map_localKernel ht hd]
  refine natDegree_comp_le.trans ?_
  rw [natDegree_cauchyKernel hd]
  have : (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by rw [natDegree_C]; exact Nat.zero_le _)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  calc (2 * 2 ^ a - 1) * (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).natDegree
      ≤ (2 * 2 ^ a - 1) * 1 := Nat.mul_le_mul_left _ this
    _ = 2 * 2 ^ a - 1 := mul_one _

/-- The local deformation has degree at most `M (2 L - 1)` for `M` edges. -/
theorem natDegree_localDeformation_le (N : TensorNetwork B Bool V E) (side : V → Bool)
    (κ : ℤ₍₂₎ →+* B) {a : ℕ} {packet : E → P} {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a)
    {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) :
    (N.localDeformation side κ a t packet slot).natDegree ≤ Fintype.card E * (2 * 2 ^ a - 1) := by
  refine natDegree_deformedContraction_le N side _ fun e e' => ?_
  unfold cauchyLocalMatrix
  split_ifs
  · exact natDegree_map_le.trans
      (natDegree_localKernel_le ht (sub_mem_cauchyGrid (hslot e) (hslot e')))
  · rw [natDegree_zero]; exact Nat.zero_le _

/-- The deformed contraction `F(T)` along the Cauchy matrix of a packing into packets of `L` slots
has degree at most `M (2 L - 1)` for `M` edges (§D.4.3 of [OpenAI2026ETH], p. 59). -/
theorem natDegree_deformedContraction_cauchyMatrix_le {R : Type*} [CommRing R] [Algebra ℚ R]
    (N : TensorNetwork R Bool V E) (side : V → Bool) {L : ℕ} {packet : E → P} {slot : E → ℕ}
    (hslot : ∀ e, slot e < L) :
    ((N.map C).deformedContraction side
        ((cauchyMatrix L packet slot).map (mapRingHom (algebraMap ℚ R)))).natDegree ≤
      Fintype.card E * (2 * L - 1) := by
  refine natDegree_deformedContraction_le N side _ fun e e' => ?_
  simp only [Matrix.map_apply, cauchyMatrix, coe_mapRingHom]
  split_ifs
  · exact natDegree_map_le.trans
      (natDegree_cauchyKernel (sub_mem_cauchyGrid (hslot e) (hslot e'))).le
  · rw [Polynomial.map_zero, natDegree_zero]; exact Nat.zero_le _

end TensorNetwork

end Cslib.Circuits.Frontier
