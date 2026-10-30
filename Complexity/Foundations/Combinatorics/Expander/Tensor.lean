/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Loops
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Tensor products of rotation maps

The **tensor product** `G.tensor H` of rotation maps on `V` and `V'` is the rotation map on
`V × V'` that takes a step in `G` and a step in `H` at the same time
[Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]
[Hoory, Linial and Wigderson, Section 9][HooryLinialWigderson2006]. Its walk operator factors as
`(W_G ⊗ I) (I ⊗ W_H)`, where `I ⊗ W_H` is the walk operator of `(loops V Unit).tensor H` on the
copies `{v} × V'` of `H`. Splitting a function on `V × V'` into its averages over the copies of `H`
and a part of average zero on every copy gives `λ(G ⊗ H) ≤ max λ(G) λ(H)`, with equality when
neither factor is empty or without edges.

## Main definitions

* `Cslib.RotationMap.tensorRot`: the underlying functional rotation program, shared with its
  efficiency certificate.
* `Cslib.RotationMap.tensor`: the tensor product `G ⊗ H`.

## Main results

* `Cslib.RotationMap.walk_tensor`: the walk operator of `G ⊗ H` factors as `(W_G ⊗ I) (I ⊗ W_H)`.
* `Cslib.RotationMap.spectralExpansion_tensor_le`, `Cslib.RotationMap.spectralExpansion_tensor`:
  `λ(G ⊗ H) ≤ max λ(G) λ(H)`, with equality when neither factor is empty or without edges.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open Fintype (expect_comp_fst expect_comp_snd
  expect_add_sq_of_expect_fiber_eq_zero exists_eq_add_expect_fiber_eq_zero)
open scoped BigOperators

variable {V D V' D' : Type*}

variable (G : RotationMap V D) (H : RotationMap V' D')

/-- Execute a tensor rotation with one call to each component, retaining both return labels. -/
def tensorRot (rotate : V × D → V × D) (other : V' × D' → V' × D')
    (p : (V × V') × (D × D')) : (V × V') × (D × D') :=
  let first := rotate (p.1.1, p.2.1)
  let second := other (p.1.2, p.2.2)
  ((first.1, second.1), (first.2, second.2))

/-- The **tensor product** `G ⊗ H`
[Reingold, Vadhan and Wigderson, Section 2.3][ReingoldVadhanWigderson2002]: the multigraph on
`V × V'` with labels `D × D'` whose edge `(i, i')` at `(v, v')` takes the edge `i` of `G` at `v` and
the edge `i'` of `H` at `v'` at the same time. -/
@[reducible]
def tensor : RotationMap (V × V') (D × D') where
  rot := tensorRot G.rot H.rot
  rot_involutive p := by simp [tensorRot]

/-- The rotation map of `G ⊗ H` applies those of `G` and of `H` side by side. -/
@[simp]
theorem rot_tensor (v : V) (v' : V') (i : D) (i' : D') :
    (G.tensor H).rot ((v, v'), (i, i')) =
      (((G.rot (v, i)).1, (H.rot (v', i')).1), ((G.rot (v, i)).2, (H.rot (v', i')).2)) :=
  rfl

/-- The neighbors in `G ⊗ H` are the pairs of a neighbor in `G` and a neighbor in `H`. -/
@[simp]
theorem neighbor_tensor (p : V × V') (i : D × D') :
    (G.tensor H).neighbor p i = (G.neighbor p.1 i.1, H.neighbor p.2 i.2) :=
  rfl

variable [Fintype D] [Fintype D']

/-- The walk operator of `G ⊗ H` averages over a neighbor in `G` and a neighbor in `H`. -/
theorem walk_tensor_apply (f : V × V' → ℝ) (p : V × V') :
    (G.tensor H).walk f p = 𝔼 i, 𝔼 i', f (G.neighbor p.1 i, H.neighbor p.2 i') := by
  rw [walk_apply, Fintype.expect_prod_type]
  rfl

/-- The walk operator of `G ⊗ H` is the tensor product of those of `G` and `H`: it sends
`f ⊗ g : (v, v') ↦ f v * g v'` to `G.walk f ⊗ H.walk g`. -/
theorem walk_tensor_mul (f : V → ℝ) (g : V' → ℝ) :
    (G.tensor H).walk (fun p ↦ f p.1 * g p.2) = fun p ↦ G.walk f p.1 * H.walk g p.2 :=
  funext fun p ↦ by rw [walk_tensor_apply, walk_apply, walk_apply, Fintype.expect_mul_expect]

/-- The walk operator of `(loops V Unit).tensor H` is the walk operator `I ⊗ W_H` of `H` on every
copy `{v} × V'` of `H`. -/
theorem walk_loops_tensor_apply (f : V × V' → ℝ) (p : V × V') :
    ((loops V Unit).tensor H).walk f p = H.walk (fun w ↦ f (p.1, w)) p.2 := by
  rw [walk_tensor_apply, walk_apply]
  simp only [neighbor_loops, Fintype.expect_const]

/-- The walk operator of `G.tensor (loops V' Unit)` is the walk operator `W_G ⊗ I` of `G` on every
copy `V × {v'}` of `G`. -/
theorem walk_tensor_loops_apply (f : V × V' → ℝ) (p : V × V') :
    (G.tensor (loops V' Unit)).walk f p = G.walk (fun w ↦ f (w, p.2)) p.1 := by
  rw [walk_tensor_apply, walk_apply]
  simp only [neighbor_loops, Fintype.expect_const]

/-- The walk operator of `G ⊗ H` factors as `W_G ⊗ W_H = (W_G ⊗ I) (I ⊗ W_H)`. -/
theorem walk_tensor :
    (G.tensor H).walk = (G.tensor (loops V' Unit)).walk ∘ₗ ((loops V Unit).tensor H).walk :=
  LinearMap.ext fun f ↦ funext fun p ↦ by
    rw [LinearMap.comp_apply, walk_tensor_loops_apply, walk_tensor_apply, walk_apply]
    simp only [walk_loops_tensor_apply]
    simp only [walk_apply]

/-- When `H` has edges, the walk operator on the copies of `H` fixes the functions that are
constant on every copy. -/
theorem walk_loops_tensor_comp_fst [Nonempty D'] (φ : V → ℝ) :
    ((loops V Unit).tensor H).walk (fun p ↦ φ p.1) = fun p ↦ φ p.1 :=
  funext fun p ↦ by
    rw [walk_loops_tensor_apply]
    exact congrFun (H.walk_const (φ p.1)) p.2

/-- The walk operator on the copies of `H` acts on the part of average zero over every copy. -/
theorem walk_loops_tensor_add [Nonempty D'] (φ : V → ℝ) (g : V × V' → ℝ) :
    ((loops V Unit).tensor H).walk (fun p ↦ φ p.1 + g p) =
      fun p ↦ φ p.1 + ((loops V Unit).tensor H).walk g p := by
  rw [show (fun p ↦ φ p.1 + g p) = (fun p : V × V' ↦ φ p.1) + g from rfl, map_add,
    walk_loops_tensor_comp_fst]
  rfl

/-- On functions of average zero over every copy `{v} × V'` of `H`, the walk operator on the
copies of `H` multiplies the second moment by at most `λ(H) ^ 2`. -/
theorem expect_walk_loops_tensor_sq_le [Fintype V] [Fintype V'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) :
    𝔼 p, ((loops V Unit).tensor H).walk f p ^ 2 ≤ H.spectralExpansion ^ 2 * 𝔼 p, f p ^ 2 := by
  rw [Fintype.expect_prod_type, Fintype.expect_prod_type, mul_expect]
  refine expect_le_expect fun v _ ↦ ?_
  simp only [walk_loops_tensor_apply]
  exact H.expect_walk_sq_le_spectralExpansion_sq_mul (hf v)

/-- The walk operator on the copies of `H` keeps average zero over every copy. -/
theorem expect_walk_loops_tensor_eq_zero [Fintype V'] [Nonempty D'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) (v : V) :
    𝔼 v', ((loops V Unit).tensor H).walk f (v, v') = 0 := by
  simp only [walk_loops_tensor_apply]
  rw [H.expect_walk (fun w ↦ f (v, w)), hf v]

/-- The walk operator on the copies of `G` keeps average zero over the copies of `H`. -/
private theorem expect_walk_tensor_loops_eq_zero [Fintype V'] {f : V × V' → ℝ}
    (hf : ∀ v, 𝔼 v', f (v, v') = 0) (v : V) :
    𝔼 v', (G.tensor (loops V' Unit)).walk f (v, v') = 0 := by
  simp only [walk_tensor_loops_apply]
  simp only [walk_apply]
  rw [expect_comm]
  simp [hf]

variable [Fintype V] [Fintype V']

/-- The spectral expansion of `G ⊗ H` is at most the larger of those of `G` and `H`
[Reingold, Vadhan and Wigderson, Proposition 2.4][ReingoldVadhanWigderson2002]. -/
theorem spectralExpansion_tensor_le :
    (G.tensor H).spectralExpansion ≤ max G.spectralExpansion H.spectralExpansion := by
  have hG := le_max_left G.spectralExpansion H.spectralExpansion
  have hH := le_max_right G.spectralExpansion H.spectralExpansion
  have hG0 := G.spectralExpansion_nonneg
  have hH0 := H.spectralExpansion_nonneg
  refine spectralExpansion_le (hG0.trans hG) fun f hf ↦ ?_
  rcases isEmpty_or_nonempty D' with hD' | hD'
  · have : (G.tensor H).walk f = 0 := funext fun p ↦ by simp [walk_tensor_apply]
    rw [this]
    simpa using mul_nonneg (sq_nonneg _) (expect_nonneg fun p _ ↦ sq_nonneg (f p))
  rcases isEmpty_or_nonempty V' with hV' | hV'
  · simp
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁, hff⟩ := exists_eq_add_expect_fiber_eq_zero f
  rw [hf] at hf₁
  have hW : (G.tensor H).walk (fun p ↦ f₁ p.1 + f₂ p) =
      fun p ↦ G.walk f₁ p.1 +
        (G.tensor (loops V' Unit)).walk (((loops V Unit).tensor H).walk f₂) p := by
    rw [walk_tensor, LinearMap.comp_apply, walk_loops_tensor_add,
      show (fun p ↦ f₁ p.1 + ((loops V Unit).tensor H).walk f₂ p) =
        (fun p : V × V' ↦ f₁ p.1) + ((loops V Unit).tensor H).walk f₂ from rfl, map_add]
    exact funext fun p ↦ by simp [walk_tensor_loops_apply]
  rw [hW, expect_add_sq_of_expect_fiber_eq_zero _
      (G.expect_walk_tensor_loops_eq_zero (H.expect_walk_loops_tensor_eq_zero hf₂)),
    expect_comp_fst (fun v ↦ G.walk f₁ v ^ 2), hff]
  calc
    _ ≤ G.spectralExpansion ^ 2 * 𝔼 v, f₁ v ^ 2 +
          H.spectralExpansion ^ 2 * 𝔼 p, f₂ p ^ 2 := by
      gcongr
      · exact expect_walk_sq_le_spectralExpansion_sq_mul hf₁
      · exact ((G.tensor (loops V' Unit)).expect_walk_sq_le _).trans
          (H.expect_walk_loops_tensor_sq_le hf₂)
    _ ≤ max G.spectralExpansion H.spectralExpansion ^ 2 * 𝔼 v, f₁ v ^ 2 +
          max G.spectralExpansion H.spectralExpansion ^ 2 * 𝔼 p, f₂ p ^ 2 := by
      have h₁ : 0 ≤ 𝔼 v, f₁ v ^ 2 := expect_nonneg fun v _ ↦ sq_nonneg (f₁ v)
      have h₂ : 0 ≤ 𝔼 p, f₂ p ^ 2 := expect_nonneg fun p _ ↦ sq_nonneg (f₂ p)
      gcongr
    _ = _ := by ring

/-- `λ(G) ≤ λ(G ⊗ H)`: functions of the first coordinate see the walk on `G`. -/
private theorem spectralExpansion_le_spectralExpansion_tensor_left [Nonempty V'] [Nonempty D'] :
    G.spectralExpansion ≤ (G.tensor H).spectralExpansion := by
  refine spectralExpansion_le (spectralExpansion_nonneg _) fun f hf ↦ ?_
  have hW : (G.tensor H).walk (fun p ↦ f p.1) = fun p ↦ G.walk f p.1 :=
    funext fun p ↦ by
      rw [walk_tensor_apply, walk_apply]
      simp only [Fintype.expect_const]
  have h := (G.tensor H).expect_walk_sq_le_spectralExpansion_sq_mul (f := fun p ↦ f p.1)
    (by rw [expect_comp_fst f, hf])
  rwa [hW, expect_comp_fst (fun v ↦ G.walk f v ^ 2), expect_comp_fst (fun v ↦ f v ^ 2)] at h

/-- `λ(H) ≤ λ(G ⊗ H)`: functions of the second coordinate see the walk on `H`. -/
private theorem spectralExpansion_le_spectralExpansion_tensor_right [Nonempty V] [Nonempty D] :
    H.spectralExpansion ≤ (G.tensor H).spectralExpansion := by
  refine spectralExpansion_le (spectralExpansion_nonneg _) fun f hf ↦ ?_
  have hW : (G.tensor H).walk (fun p ↦ f p.2) = fun p ↦ H.walk f p.2 :=
    funext fun p ↦ by
      rw [walk_tensor_apply, walk_apply]
      simp only [Fintype.expect_const]
  have h := (G.tensor H).expect_walk_sq_le_spectralExpansion_sq_mul (f := fun p ↦ f p.2)
    (by rw [expect_comp_snd f, hf])
  rwa [hW, expect_comp_snd (fun v ↦ H.walk f v ^ 2), expect_comp_snd (fun v ↦ f v ^ 2)] at h

/-- The spectral expansion of `G ⊗ H` is the larger of those of `G` and `H`
[Reingold, Vadhan and Wigderson, Proposition 2.4][ReingoldVadhanWigderson2002], when neither factor
is empty or without edges. -/
theorem spectralExpansion_tensor [Nonempty V] [Nonempty D] [Nonempty V'] [Nonempty D'] :
    (G.tensor H).spectralExpansion = max G.spectralExpansion H.spectralExpansion :=
  (G.spectralExpansion_tensor_le H).antisymm
    (max_le (G.spectralExpansion_le_spectralExpansion_tensor_left H)
      (G.spectralExpansion_le_spectralExpansion_tensor_right H))

end Cslib.RotationMap
