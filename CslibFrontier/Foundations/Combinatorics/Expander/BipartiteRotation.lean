/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Spectrum
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Variance
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regular bipartite multigraphs, bipartite double covers, and mixing

A `D`-regular bipartite multigraph between left vertices `L` and right vertices `R`—retaining
parallel-edge multiplicities—is presented by a bijection `toRight : L × D ≃ R × D` matching each
left dart `(u, i)` to its right dart `(v, j)` (`Cslib.BipartiteRotationMap`). When `D` is nonempty
and finite, this forces `|L| = |R|` (`card_left_eq_card_right`). Its symmetric rotation map on
`L ⊕ R` is `B.toRotationMap`, and any `D`-regular multigraph `G : RotationMap V D` gives a
bipartite double cover `G.doubleCover : BipartiteRotationMap V V D` whose edges and walk
operators mirror `G`.

The normalized biadjacency walk operator `B.walkLeft : (R → ℝ) →ₗ[ℝ] (L → ℝ)` averages a right-side
function over left-side neighbors, with adjoint `B.walkRight = B.flip.walkLeft`. The **normalized
nontrivial singular value** `B.nontrivialSingularValue` is the operator norm of `B.walkLeft` on
mean-zero functions, equal to `B.flip.nontrivialSingularValue`. It bounds every eigenvalue `μ` of
`B.toRotationMap` orthogonal to both `(1_L, 1_R)` and `(1_L, -1_R)`
(`abs_eigenvalue_le_nontrivialSingularValue_of_isBipartiteBalanced`), equals `G.spectralExpansion`
for `G.doubleCover` (`nontrivialSingularValue_doubleCover`), and yields the **bipartite expander
mixing lemma** (`abs_card_interedges_sub_le`, `abs_card_interedges_sub_le_mul_sqrt`).

## Main definitions

* `Cslib.BipartiteRotationMap`: a `D`-regular bipartite multigraph via its dart bijection.
* `Cslib.BipartiteRotationMap.toRotationMap`, `Cslib.RotationMap.doubleCover`: bipartite double
  covers and symmetric underlying rotation maps.
* `Cslib.BipartiteRotationMap.walkLeft`, `Cslib.BipartiteRotationMap.walkRight`: normalized
  biadjacency walk operators.
* `Cslib.BipartiteRotationMap.nontrivialSingularValue`: the largest nontrivial singular value of the
  normalized biadjacency operator.
* `Cslib.BipartiteRotationMap.interedges`: the edges from a left set `U` to a right set `W`.

## Main results

* `Cslib.BipartiteRotationMap.nontrivialSingularValue_flip`: symmetry of singular values.
* `Cslib.BipartiteRotationMap.nontrivialSingularValue_doubleCover`: the bipartite double cover
  shares the spectral expansion `λ(G)`.
* `Cslib.BipartiteRotationMap.abs_eigenvalue_le_nontrivialSingularValue_of_isBipartiteBalanced`:
  nontrivial eigenvalues of the bipartite graph lie in `[-σ₂, σ₂]`.
* `Cslib.BipartiteRotationMap.abs_card_interedges_sub_le`,
  `Cslib.BipartiteRotationMap.abs_card_interedges_sub_le_mul_sqrt`: the bipartite expander mixing
  lemma.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their applications*]
  [HooryLinialWigderson2006], May 3, 2006 draft (`expanderbookr1.pdf`). The mixing background
  relies on §2.4 (Lemma 2.5), while §12.3.1 serves strictly as GV coding background. The formalized
  typed bipartite/multigraph and asymmetric generalizations explicitly adapt these arguments to
  multigraphs with parallel-edge multiplicities.
* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996], IEEE Trans. Inf. Theory
  42(6):1710–1722 (1996).
-/


public section

namespace Cslib

open Finset RotationMap
open scoped BigOperators RealInnerProductSpace

/-- A `D`-regular bipartite multigraph between left vertices `L` and right vertices `R`, retaining
parallel edges via the dart bijection `toRight : L × D ≃ R × D`. -/
@[ext]
structure BipartiteRotationMap (L R D : Type*) where
  /-- The bijection pairing each left dart `(u, i)` with its opposite right dart `(v, j)`. -/
  toRight : L × D ≃ R × D

namespace BipartiteRotationMap

variable {L R D E : Type*}

/-- Build a `D`-regular bipartite multigraph from left and right edge-port bijections onto a
common edge type `E`. -/
@[expose]
def ofEquiv (eL : L × D ≃ E) (eR : R × D ≃ E) : BipartiteRotationMap L R D :=
  ⟨eL.trans eR.symm⟩

/-- Flip the two sides of a bipartite multigraph. -/
@[expose]
def flip (B : BipartiteRotationMap L R D) : BipartiteRotationMap R L D :=
  ⟨B.toRight.symm⟩

/-- Flipping twice returns the original bipartite rotation map. -/
@[simp]
theorem flip_flip (B : BipartiteRotationMap L R D) : B.flip.flip = B :=
  rfl

/-- The right endpoint reached by left vertex `u` along its `i`-th port. -/
@[expose]
def neighborRight (B : BipartiteRotationMap L R D) (u : L) (i : D) : R :=
  (B.toRight (u, i)).1

/-- The left endpoint reached by right vertex `v` along its `j`-th port. -/
@[expose]
def neighborLeft (B : BipartiteRotationMap L R D) (v : R) (j : D) : L :=
  (B.toRight.symm (v, j)).1

/-- Left neighbors in `B` are right neighbors in `B.flip`. -/
theorem neighborLeft_eq_flip_neighborRight (B : BipartiteRotationMap L R D) (v : R) (j : D) :
    B.neighborLeft v j = B.flip.neighborRight v j :=
  rfl

/-- View a `D`-regular bipartite multigraph as a `D`-regular rotation map on `L ⊕ R`. -/
@[expose]
def toRotationMap (B : BipartiteRotationMap L R D) : RotationMap (L ⊕ R) D where
  rot
    | (.inl u, i) => let q := B.toRight (u, i); (.inr q.1, q.2)
    | (.inr v, j) => let p := B.toRight.symm (v, j); (.inl p.1, p.2)
  rot_involutive p := by
    rcases p with ⟨u | v, i⟩ <;> simp

/-- **Bipartite double cover** of a regular multigraph `G : RotationMap V D`: left vertex `u` is
joined by port `i` to right vertex `(G.rot (u, i)).1` at port `(G.rot (u, i)).2`. -/
@[expose]
def _root_.Cslib.RotationMap.doubleCover {V : Type*} (G : RotationMap V D) :
    BipartiteRotationMap V V D where
  toRight := ⟨G.rot, G.rot, G.rot_involutive, G.rot_involutive⟩

/-- Right neighbors in `G.doubleCover` agree with neighbors in `G`. -/
@[simp]
theorem doubleCover_neighborRight {V : Type*} (G : RotationMap V D) (u : V) (i : D) :
    G.doubleCover.neighborRight u i = G.neighbor u i :=
  rfl

/-- Left neighbors in `G.doubleCover` agree with neighbors in `G`. -/
@[simp]
theorem doubleCover_neighborLeft {V : Type*} (G : RotationMap V D) (v : V) (j : D) :
    G.doubleCover.neighborLeft v j = G.neighbor v j :=
  rfl

/-- When `D` is finite and nonempty, left and right sides have the same cardinality `N`. -/
theorem card_left_eq_card_right (B : BipartiteRotationMap L R D)
    [Fintype L] [Fintype R] [Finite D] [Nonempty D] :
    Fintype.card L = Fintype.card R := by
  let := Fintype.ofFinite D
  have h := Fintype.card_congr B.toRight
  rw [Fintype.card_prod, Fintype.card_prod] at h
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos h

section Walk

variable (B : BipartiteRotationMap L R D) [Fintype D]

/-- The left-side normalized biadjacency operator: averages a function `g : R → ℝ` over the `D`
neighbors of each left vertex. -/
@[expose]
noncomputable def walkLeft : (R → ℝ) →ₗ[ℝ] (L → ℝ) where
  toFun g u := 𝔼 i : D, g (B.neighborRight u i)
  map_add' _ _ := funext fun _ => expect_add_distrib _ _ _
  map_smul' c _ := funext fun _ => (smul_expect c _ _).symm

/-- The right-side normalized biadjacency operator: `B.flip.walkLeft`. -/
@[expose]
noncomputable def walkRight : (L → ℝ) →ₗ[ℝ] (R → ℝ) :=
  B.flip.walkLeft

/-- Pointwise formula for `B.walkLeft`. -/
theorem walkLeft_apply (g : R → ℝ) (u : L) :
    B.walkLeft g u = 𝔼 i : D, g (B.neighborRight u i) :=
  rfl

/-- Pointwise formula for `B.walkRight`. -/
theorem walkRight_apply (f : L → ℝ) (v : R) :
    B.walkRight f v = 𝔼 j : D, f (B.neighborLeft v j) :=
  rfl

/-- `B.walkLeft` preserves constant functions. -/
@[simp]
theorem walkLeft_const [Nonempty D] (c : ℝ) : B.walkLeft (fun _ => c) = fun _ => c :=
  funext fun _ => Fintype.expect_const c

/-- `B.walkRight` preserves constant functions. -/
@[simp]
theorem walkRight_const [Nonempty D] (c : ℝ) : B.walkRight (fun _ => c) = fun _ => c :=
  B.flip.walkLeft_const c

/-- On `L ⊕ R`, `B.toRotationMap.walk` sends `(f, g)` to `(walkLeft g, walkRight f)`. -/
@[simp]
theorem toRotationMap_walk_sumElim (f : L → ℝ) (g : R → ℝ) :
    B.toRotationMap.walk (Sum.elim f g) = Sum.elim (B.walkLeft g) (B.walkRight f) := by
  funext x
  rcases x with u | v <;>
    simp [RotationMap.walk_apply, RotationMap.neighbor, toRotationMap, walkLeft_apply,
      walkRight_apply, neighborRight, neighborLeft]

/-- Left walk of `G.doubleCover` is `G.walk`. -/
@[simp]
theorem doubleCover_walkLeft {V : Type*} (G : RotationMap V D) :
    G.doubleCover.walkLeft = G.walk :=
  rfl

/-- Right walk of `G.doubleCover` is `G.walk`. -/
@[simp]
theorem doubleCover_walkRight {V : Type*} (G : RotationMap V D) :
    G.doubleCover.walkRight = G.walk :=
  rfl

variable [Fintype L] [Fintype R]

/-- Averaging `B.walkLeft g` over left vertices equals averaging `g` over right vertices. -/
theorem expect_walkLeft [Nonempty D] (g : R → ℝ) :
    𝔼 u : L, B.walkLeft g u = 𝔼 v : R, g v := by
  have _ : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  simp only [walkLeft_apply, neighborRight, ← expect_product', univ_product_univ]
  rw [Fintype.expect_equiv B.toRight (fun p => g (B.toRight p).1) (fun q => g q.1)
    fun _ => rfl, Fintype.expect_prod_type]
  dsimp only
  simp only [Fintype.expect_const]

/-- `B.walkLeft` and `B.walkRight` are adjoint with respect to uniform expectations on `L` and `R`.
-/
theorem expect_mul_walkLeft (f : L → ℝ) (g : R → ℝ) :
    𝔼 u : L, f u * B.walkLeft g u = 𝔼 v : R, B.walkRight f v * g v := by
  simp only [walkLeft_apply, walkRight_apply, mul_expect, expect_mul, neighborRight, neighborLeft,
    ← expect_product', univ_product_univ, Prod.mk.eta]
  exact Fintype.expect_equiv B.toRight
    (fun p => f p.1 * g (B.toRight p).1)
    (fun q => f (B.toRight.symm q).1 * g q.1)
    fun p => by simp only [Equiv.symm_apply_apply]

/-- `B.walkLeft` preserves mean zero. -/
theorem expect_walkLeft_eq_zero {g : R → ℝ} (hg : 𝔼 v : R, g v = 0) :
    𝔼 u : L, B.walkLeft g u = 0 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp [walkLeft_apply]
  · rw [B.expect_walkLeft, hg]

/-- `B.walkRight` preserves mean zero. -/
theorem expect_walkRight_eq_zero {f : L → ℝ} (hf : 𝔼 u : L, f u = 0) :
    𝔼 v : R, B.walkRight f v = 0 :=
  B.flip.expect_walkLeft_eq_zero hf

omit [Fintype L] in
/-- For a centered function `g - 𝔼 g`, `B.walkLeft` commutes with subtracting the mean. -/
theorem walkLeft_sub_expect [Nonempty D] (g : R → ℝ) :
    B.walkLeft (fun v => g v - 𝔼 w, g w) = fun u => B.walkLeft g u - 𝔼 w, g w := by
  rw [show (fun v => g v - 𝔼 w, g w) = g - fun _ => 𝔼 w, g w from rfl,
    map_sub, B.walkLeft_const]
  rfl

end Walk

section SingularValue

private noncomputable def walkLeftEuclidean (B : BipartiteRotationMap L R D) [Fintype D] :
    EuclideanSpace ℝ R →ₗ[ℝ] EuclideanSpace ℝ L :=
  (WithLp.linearEquiv 2 ℝ (L → ℝ)).symm.toLinearMap.comp
    (B.walkLeft.comp (WithLp.linearEquiv 2 ℝ (R → ℝ)).toLinearMap)

/-- The **normalized nontrivial singular value** `σ₂(B)` of `B`: the operator norm of
`B.walkLeft` on mean-zero functions, equivalently the second singular value of the normalized
biadjacency matrix `A / |D|`. -/
noncomputable def nontrivialSingularValue (B : BipartiteRotationMap L R D)
    [Fintype L] [Fintype R] [Fintype D] : ℝ :=
  ‖(LinearMap.toContinuousLinearMap B.walkLeftEuclidean).comp
    (orthogonalSubmodule R).subtypeL‖

/-- `B.nontrivialSingularValue` is nonnegative. -/
theorem nontrivialSingularValue_nonneg (B : BipartiteRotationMap L R D)
    [Fintype L] [Fintype R] [Fintype D] : 0 ≤ B.nontrivialSingularValue := by
  rw [nontrivialSingularValue]
  positivity

variable [Fintype L] [Fintype R] [Fintype D] {B : BipartiteRotationMap L R D}

/-- On mean-zero right-side functions, `B.walkLeft` shrinks the second moment by at most
`σ₂(B) ^ 2`. -/
theorem expect_walkLeft_sq_le [Nonempty D] {g : R → ℝ} (hg : 𝔼 v : R, g v = 0) :
    𝔼 u : L, B.walkLeft g u ^ 2 ≤ B.nontrivialSingularValue ^ 2 * 𝔼 v : R, g v ^ 2 := by
  rcases (Fintype.card R).eq_zero_or_pos with hR | hR
  · have : IsEmpty R := Fintype.card_eq_zero_iff.1 hR
    have : IsEmpty L := by
      have := B.card_left_eq_card_right
      exact Fintype.card_eq_zero_iff.1 (by omega)
    simp
  have hL : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  have h := ContinuousLinearMap.le_opNorm
    ((LinearMap.toContinuousLinearMap B.walkLeftEuclidean).comp
      (orthogonalSubmodule R).subtypeL)
    ⟨WithLp.toLp 2 g, (mem_orthogonalSubmodule_iff g).2 hg⟩
  change ‖(WithLp.toLp 2 (B.walkLeft g) : EuclideanSpace ℝ L)‖ ≤
    B.nontrivialSingularValue * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ R)‖ at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, ← card_mul_expect_sq, ← card_mul_expect_sq, hL, mul_left_comm] at h2
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- `σ₂(B) ≤ c` (for `c ≥ 0`) iff `𝔼 (B.walkLeft g)^2 ≤ c^2 𝔼 g^2` for all mean-zero `g`. -/
theorem nontrivialSingularValue_le_iff [Nonempty D] {c : ℝ} (hc : 0 ≤ c) :
    B.nontrivialSingularValue ≤ c ↔
      ∀ g : R → ℝ, 𝔼 v : R, g v = 0 →
        𝔼 u : L, B.walkLeft g u ^ 2 ≤ c ^ 2 * 𝔼 v : R, g v ^ 2 := by
  refine ⟨fun hB g hg => (expect_walkLeft_sq_le hg).trans ?_, fun h => ?_⟩
  · have := B.nontrivialSingularValue_nonneg
    gcongr
  · refine ContinuousLinearMap.opNorm_le_bound _ hc fun ⟨y, hy⟩ => ?_
    set g := y.ofLp
    have hg := h g
      ((mem_orthogonalSubmodule_iff g).1 (by simpa only [g, WithLp.toLp_ofLp] using hy))
    have hL : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
    change ‖(WithLp.toLp 2 (B.walkLeft g) : EuclideanSpace ℝ L)‖ ≤
      c * ‖(WithLp.toLp 2 g : EuclideanSpace ℝ R)‖
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, ← card_mul_expect_sq, ← card_mul_expect_sq, hL, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _)

/-- By adjointness, `σ₂(B.flip) ≤ σ₂(B)`. -/
theorem nontrivialSingularValue_flip_le [Nonempty D] (B : BipartiteRotationMap L R D) :
    B.flip.nontrivialSingularValue ≤ B.nontrivialSingularValue := by
  refine (nontrivialSingularValue_le_iff B.nontrivialSingularValue_nonneg).2 fun f hf => ?_
  change 𝔼 v : R, B.walkRight f v ^ 2 ≤ B.nontrivialSingularValue ^ 2 * 𝔼 u : L, f u ^ 2
  set h : R → ℝ := B.walkRight f
  have hh0 : 𝔼 v : R, h v = 0 := B.expect_walkRight_eq_zero hf
  have hnn : 0 ≤ 𝔼 v : R, h v ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  rcases hnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (sq_nonneg _) (expect_nonneg fun _ _ => sq_nonneg _)
  have hsq : (𝔼 v : R, h v ^ 2) ^ 2 ≤
      (B.nontrivialSingularValue ^ 2 * 𝔼 u : L, f u ^ 2) * (𝔼 v : R, h v ^ 2) := by
    have hadj : 𝔼 v : R, h v ^ 2 = 𝔼 u : L, f u * B.walkLeft h u := by
      simpa only [h, sq] using (B.expect_mul_walkLeft f h).symm
    have hcs : (𝔼 u : L, f u * B.walkLeft h u) ^ 2 ≤
        (𝔼 u : L, f u ^ 2) * 𝔼 u : L, B.walkLeft h u ^ 2 :=
      expect_mul_sq_le_sq_mul_sq univ f (B.walkLeft h)
    have hwl := expect_walkLeft_sq_le (B := B) hh0
    have hf_nn : 0 ≤ 𝔼 u : L, f u ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
    calc (𝔼 v : R, h v ^ 2) ^ 2 = (𝔼 u : L, f u * B.walkLeft h u) ^ 2 := by rw [hadj]
      _ ≤ (𝔼 u : L, f u ^ 2) * 𝔼 u : L, B.walkLeft h u ^ 2 := hcs
      _ ≤ (𝔼 u : L, f u ^ 2) * (B.nontrivialSingularValue ^ 2 * 𝔼 v : R, h v ^ 2) :=
          mul_le_mul_of_nonneg_left hwl hf_nn
      _ = (B.nontrivialSingularValue ^ 2 * 𝔼 u : L, f u ^ 2) * 𝔼 v : R, h v ^ 2 := by ring
  rw [sq] at hsq
  exact le_of_mul_le_mul_right hsq hpos

/-- Symmetry of singular values: `σ₂(B.flip) = σ₂(B)`. -/
@[simp]
theorem nontrivialSingularValue_flip [Nonempty D] (B : BipartiteRotationMap L R D) :
    B.flip.nontrivialSingularValue = B.nontrivialSingularValue :=
  le_antisymm (nontrivialSingularValue_flip_le B)
    (by simpa only [flip_flip] using nontrivialSingularValue_flip_le B.flip)

/-- On mean-zero left-side functions, `B.walkRight` shrinks the second moment by at most
`σ₂(B) ^ 2`. -/
theorem expect_walkRight_sq_le [Nonempty D] {f : L → ℝ} (hf : 𝔼 u : L, f u = 0) :
    𝔼 v : R, B.walkRight f v ^ 2 ≤ B.nontrivialSingularValue ^ 2 * 𝔼 u : L, f u ^ 2 := by
  simpa only [nontrivialSingularValue_flip, walkRight] using expect_walkLeft_sq_le (B := B.flip) hf

/-- Squared bilinear correlation bound for mean-zero functions `f : L → ℝ` and `g : R → ℝ`. -/
theorem expect_mul_walkLeft_sq_le [Nonempty D] {f : L → ℝ} {g : R → ℝ}
    (_ : 𝔼 u : L, f u = 0) (hg : 𝔼 v : R, g v = 0) :
    (𝔼 u : L, f u * B.walkLeft g u) ^ 2 ≤
      B.nontrivialSingularValue ^ 2 * (𝔼 u : L, f u ^ 2) * (𝔼 v : R, g v ^ 2) := by
  have hcs := expect_mul_sq_le_sq_mul_sq univ f (B.walkLeft g)
  have hf_nn : 0 ≤ 𝔼 u : L, f u ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  calc (𝔼 u : L, f u * B.walkLeft g u) ^ 2
      ≤ (𝔼 u : L, f u ^ 2) * 𝔼 u : L, B.walkLeft g u ^ 2 := hcs
    _ ≤ (𝔼 u : L, f u ^ 2) * (B.nontrivialSingularValue ^ 2 * 𝔼 v : R, g v ^ 2) :=
        mul_le_mul_of_nonneg_left (expect_walkLeft_sq_le hg) hf_nn
    _ = B.nontrivialSingularValue ^ 2 * (𝔼 u : L, f u ^ 2) * (𝔼 v : R, g v ^ 2) := by ring

/-- The bipartite double cover of a regular multigraph `G` has the same normalized nontrivial
singular value as `G.spectralExpansion`. -/
@[simp]
theorem nontrivialSingularValue_doubleCover {V : Type*} [Fintype V] [Nonempty D]
    (G : RotationMap V D) :
    G.doubleCover.nontrivialSingularValue = G.spectralExpansion := by
  refine le_antisymm ?_ ?_
  · refine (nontrivialSingularValue_le_iff G.spectralExpansion_nonneg).2 fun g hg => ?_
    simpa only [doubleCover_walkLeft] using G.expect_walk_sq_le_spectralExpansion_sq_mul hg
  · refine G.spectralExpansion_le G.doubleCover.nontrivialSingularValue_nonneg fun f hf => ?_
    simpa only [doubleCover_walkLeft] using
      expect_walkLeft_sq_le (B := G.doubleCover) hf

end SingularValue

section Spectral

/-- A function on `L ⊕ R` is *bipartite-balanced* when its averages on `L` and `R` both vanish
(i.e. orthogonal to both `(1_L, 1_R)` and `(1_L, -1_R)`). -/
@[expose]
def IsBipartiteBalanced [Fintype L] [Fintype R] (f : L ⊕ R → ℝ) : Prop :=
  (𝔼 u : L, f (.inl u) = 0) ∧ (𝔼 v : R, f (.inr v) = 0)

/-- Every eigenfunction `B.toRotationMap.walk f = μ • f` (`f ≠ 0`) that is orthogonal to the
trivial `±1` eigenfunctions `(1_L, ±1_R)` has eigenvalue `|μ| ≤ B.nontrivialSingularValue`. -/
theorem abs_eigenvalue_le_nontrivialSingularValue_of_isBipartiteBalanced
    [Fintype L] [Fintype R] [Fintype D] [Nonempty D]
    (B : BipartiteRotationMap L R D) {f : L ⊕ R → ℝ} {μ : ℝ} (hf0 : f ≠ 0)
    (hf : IsBipartiteBalanced f) (hwalk : B.toRotationMap.walk f = μ • f) :
    |μ| ≤ B.nontrivialSingularValue := by
  let fL : L → ℝ := fun u => f (.inl u)
  let fR : R → ℝ := fun v => f (.inr v)
  have hf_elim : f = Sum.elim fL fR := funext fun x => by cases x <;> rfl
  have hwalk' : Sum.elim (B.walkLeft fR) (B.walkRight fL) = μ • Sum.elim fL fR := by
    rw [← toRotationMap_walk_sumElim, ← hf_elim, hwalk]
  have hL_eq : B.walkLeft fR = μ • fL := funext fun u => congrFun hwalk' (.inl u)
  have hR_eq : B.walkRight fL = μ • fR := funext fun v => congrFun hwalk' (.inr v)
  have h1 := expect_walkLeft_sq_le (B := B) hf.2
  have h2 := expect_walkRight_sq_le (B := B) hf.1
  have h_sum_le :
      μ ^ 2 * (𝔼 u : L, fL u ^ 2 + 𝔼 v : R, fR v ^ 2) ≤
        B.nontrivialSingularValue ^ 2 * (𝔼 u : L, fL u ^ 2 + 𝔼 v : R, fR v ^ 2) := by
    have hs1 : 𝔼 u : L, B.walkLeft fR u ^ 2 = μ ^ 2 * 𝔼 u : L, fL u ^ 2 := by
      simp only [hL_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_expect]
    have hs2 : 𝔼 v : R, B.walkRight fL v ^ 2 = μ ^ 2 * 𝔼 v : R, fR v ^ 2 := by
      simp only [hR_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_expect]
    linarith [h1, h2]
  have hpos : 0 < 𝔼 u : L, fL u ^ 2 + 𝔼 v : R, fR v ^ 2 := by
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hf0
    rcases x₀ with u₀ | v₀
    · have hL : 0 < 𝔼 u : L, fL u ^ 2 :=
        expect_pos' (fun _ _ => sq_nonneg _) ⟨u₀, mem_univ u₀, sq_pos_iff.2 hx₀⟩
      linarith [show 0 ≤ 𝔼 v : R, fR v ^ 2 from expect_nonneg fun _ _ => sq_nonneg _]
    · have hR : 0 < 𝔼 v : R, fR v ^ 2 :=
        expect_pos' (fun _ _ => sq_nonneg _) ⟨v₀, mem_univ v₀, sq_pos_iff.2 hx₀⟩
      linarith [show 0 ≤ 𝔼 u : L, fL u ^ 2 from expect_nonneg fun _ _ => sq_nonneg _]
  have hμ2 : μ ^ 2 ≤ B.nontrivialSingularValue ^ 2 := le_of_mul_le_mul_right h_sum_le hpos
  exact abs_le_of_sq_le_sq hμ2 B.nontrivialSingularValue_nonneg

/-- In the Euclidean space `EuclideanSpace ℝ (L ⊕ R)`, `IsBipartiteBalanced f` holds iff
`WithLp.toLp 2 f` is orthogonal to both `(1_L, 1_R)` and `(1_L, -1_R)`. -/
theorem isBipartiteBalanced_iff_inner_eq_zero [Fintype L] [Fintype R] [Finite D] [Nonempty D]
    (B : BipartiteRotationMap L R D) (hL : 0 < Fintype.card L) (f : L ⊕ R → ℝ) :
    IsBipartiteBalanced f ↔
      ⟪WithLp.toLp 2 (fun _ => 1 : L ⊕ R → ℝ), WithLp.toLp 2 f⟫ = 0 ∧
      ⟪WithLp.toLp 2 (Sum.elim (fun _ => 1) (fun _ => -1) : L ⊕ R → ℝ),
        WithLp.toLp 2 f⟫ = 0 := by
  have hcard : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  have hR : 0 < Fintype.card R := hcard ▸ hL
  have h1 : ⟪WithLp.toLp 2 (fun _ => 1 : L ⊕ R → ℝ), WithLp.toLp 2 f⟫ =
      ∑ u : L, f (.inl u) + ∑ v : R, f (.inr v) := by
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct]
  have h2 : ⟪WithLp.toLp 2 (Sum.elim (fun _ => 1) (fun _ => -1) : L ⊕ R → ℝ),
        WithLp.toLp 2 f⟫ =
      ∑ u : L, f (.inl u) - ∑ v : R, f (.inr v) := by
    simp [EuclideanSpace.inner_toLp_toLp, dotProduct, sub_eq_add_neg]
  simp only [IsBipartiteBalanced, Fintype.expect_eq_sum_div_card, h1, h2]
  have hL0 : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  have hR0 : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hR.ne'
  rw [div_eq_zero_iff, div_eq_zero_iff, or_iff_left hL0, or_iff_left hR0]
  constructor
  · rintro ⟨hsL, hsR⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hp, hm⟩
    exact ⟨by linarith, by linarith⟩

end Spectral

section Mixing

/-- The edges of `B` from left set `U` to right set `W`, represented as left darts `(u, i)` with
`u ∈ U` and `B.neighborRight u i ∈ W`. -/
@[expose]
def interedges [Fintype D] [DecidableEq R]
    (B : BipartiteRotationMap L R D) (U : Finset L) (W : Finset R) : Finset (L × D) :=
  {p ∈ U ×ˢ univ | B.neighborRight p.1 p.2 ∈ W}

/-- Membership in `B.interedges U W` means `p.1 ∈ U` and `B.neighborRight p.1 p.2 ∈ W`. -/
@[simp]
theorem mem_interedges [Fintype D] [DecidableEq R] (B : BipartiteRotationMap L R D)
    {U : Finset L} {W : Finset R} {p : L × D} :
    p ∈ B.interedges U W ↔ p.1 ∈ U ∧ B.neighborRight p.1 p.2 ∈ W := by
  simp [interedges]

/-- No bipartite edges leave the empty left set. -/
@[simp]
theorem interedges_empty_left [Fintype D] [DecidableEq R]
    (B : BipartiteRotationMap L R D) (W : Finset R) :
    B.interedges ∅ W = ∅ := by
  simp [interedges]

/-- No bipartite edges enter the empty right set. -/
@[simp]
theorem interedges_empty_right [Fintype D] [DecidableEq R]
    (B : BipartiteRotationMap L R D) (U : Finset L) :
    B.interedges U ∅ = ∅ := by
  simp [interedges]

/-- The interedge count of `G.doubleCover` agrees with `G.interedges`. -/
@[simp]
theorem card_interedges_doubleCover {V : Type*} [Fintype D] [DecidableEq V]
    (G : RotationMap V D) (U W : Finset V) :
    #(G.doubleCover.interedges U W) = #(G.interedges U W) :=
  rfl

private theorem expect_boole_mem_walkLeft [Fintype L] [Fintype D]
    [DecidableEq L] [DecidableEq R] (B : BipartiteRotationMap L R D)
    (U : Finset L) (W : Finset R) :
    𝔼 u : L, (if u ∈ U then (1 : ℝ) else 0) * B.walkLeft (fun v => if v ∈ W then 1 else 0) u =
      #(B.interedges U W) / (Fintype.card L * Fintype.card D) := by
  simp only [walkLeft_apply, mul_expect]
  rw [← expect_product', univ_product_univ, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Nat.cast_mul]
  simp only [ite_zero_mul_ite_zero, mul_one, sum_boole]
  congr 3
  ext p
  simp

/-- **Bipartite expander mixing lemma**, sharper form: for `B : BipartiteRotationMap L R D` with
`d = |D| > 0` and `N = |L| = |R|`, the number of edges from `U ⊆ L` to `W ⊆ R` differs from
`d |U| |W| / N` by at most `σ₂(B) d √(|U| |Uᶜ| |W| |Wᶜ|) / N`. -/
theorem abs_card_interedges_sub_le [Fintype L] [Fintype R] [Fintype D]
    [DecidableEq L] [DecidableEq R] (B : BipartiteRotationMap L R D) [Nonempty D]
    (U : Finset L) (W : Finset R) :
    |(#(B.interedges U W) : ℝ) - Fintype.card D * #U * #W / Fintype.card L| ≤
      B.nontrivialSingularValue * Fintype.card D * √((#U : ℝ) * #Uᶜ * #W * #Wᶜ) /
        Fintype.card L := by
  rcases (Fintype.card L).eq_zero_or_pos with hL | hL
  · have : IsEmpty L := Fintype.card_eq_zero_iff.1 hL
    have : IsEmpty R := Fintype.card_eq_zero_iff.1 (B.card_left_eq_card_right ▸ hL)
    have hU : U = ∅ := Subsingleton.elim U ∅
    simp [hU]
  have hLR : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  have : Nonempty L := Fintype.card_pos_iff.1 hL
  have hn : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 hL
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  let f : L → ℝ := fun u => if u ∈ U then 1 else 0
  let g : R → ℝ := fun v => if v ∈ W then 1 else 0
  have hcorr :
      𝔼 u : L, f u * B.walkLeft g u =
        (𝔼 u : L, f u) * (𝔼 v : R, g v) +
          𝔼 u : L, (f u - 𝔼 u', f u') * B.walkLeft (fun v => g v - 𝔼 v', g v') u := by
    rw [B.walkLeft_sub_expect g]
    simp only [sub_mul, mul_sub, expect_sub_distrib, ← expect_mul, ← mul_expect,
      B.expect_walkLeft, Fintype.expect_const]
    ring
  have hf0 : 𝔼 u : L, (f u - 𝔼 u', f u') = 0 := Fintype.expect_balance f
  have hg0 : 𝔼 v : R, (g v - 𝔼 v', g v') = 0 := Fintype.expect_balance g
  have hbd := expect_mul_walkLeft_sq_le (B := B) hf0 hg0
  rw [← add_sub_cancel_left ((𝔼 u : L, f u) * 𝔼 v : R, g v)
    (𝔼 u : L, (f u - 𝔼 u', f u') * B.walkLeft (fun v => g v - 𝔼 v', g v') u), ← hcorr,
    Fintype.expect_sub_expect_sq, Fintype.expect_sub_expect_sq] at hbd
  simp only [f, g, expect_boole_mem_walkLeft, Fintype.expect_boole_mem,
    Fintype.expect_boole_mem_sq, nnratCast_dens, hLR] at hbd
  have hlam := B.nontrivialSingularValue_nonneg
  rw [hLR] at hn
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hbd (sq_nonneg ((Fintype.card R : ℝ) * Fintype.card D))
  have hlhs :
      ((#(B.interedges U W) : ℝ) - Fintype.card D * #U * #W / Fintype.card R) ^ 2 =
        (Fintype.card R * Fintype.card D : ℝ) ^ 2 *
          (#(B.interedges U W) / (Fintype.card R * Fintype.card D) -
            #U / Fintype.card R * (#W / Fintype.card R)) ^ 2 := by
    field_simp
  have hrhs :
      (Fintype.card R * Fintype.card D : ℝ) ^ 2 *
          (B.nontrivialSingularValue ^ 2 * (#U / Fintype.card R - (#U / Fintype.card R) ^ 2) *
            (#W / Fintype.card R - (#W / Fintype.card R) ^ 2)) =
        (B.nontrivialSingularValue * Fintype.card D *
            √((#U : ℝ) * #Uᶜ * #W * #Wᶜ) / Fintype.card R) ^ 2 := by
    conv_rhs =>
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), card_compl, card_compl,
        Nat.cast_sub (card_le_univ U), Nat.cast_sub (card_le_univ W), hLR]
    field_simp
  rw [hLR, hlhs, ← hrhs]
  exact hmul

/-- **Bipartite expander mixing lemma**: `|e(U, W) - d |U| |W| / N| ≤ σ₂(B) d √(|U| |W|)`. -/
theorem abs_card_interedges_sub_le_mul_sqrt [Fintype L] [Fintype R] [Fintype D]
    [DecidableEq R] (B : BipartiteRotationMap L R D) [Nonempty D]
    (U : Finset L) (W : Finset R) :
    |(#(B.interedges U W) : ℝ) - Fintype.card D * #U * #W / Fintype.card L| ≤
      B.nontrivialSingularValue * Fintype.card D * √((#U : ℝ) * #W) := by
  classical
  refine (B.abs_card_interedges_sub_le U W).trans ?_
  have hlam := B.nontrivialSingularValue_nonneg
  rcases (Fintype.card L).eq_zero_or_pos with hL | hL
  · rw [hL, Nat.cast_zero, div_zero]
    positivity
  have hn : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 hL
  have hU : (#Uᶜ : ℝ) ≤ Fintype.card L := Nat.cast_le.2 (card_le_univ _)
  have hW : (#Wᶜ : ℝ) ≤ Fintype.card L := by
    simpa only [B.card_left_eq_card_right] using (Nat.cast_le.2 (card_le_univ Wᶜ) : (#Wᶜ : ℝ) ≤ _)
  rw [div_le_iff₀ hn, mul_assoc _ (√_), ← Real.sqrt_sq hn.le, ← Real.sqrt_mul (by positivity)]
  gcongr _ * √?_
  calc (#U : ℝ) * #Uᶜ * #W * #Wᶜ = #U * #W * (#Uᶜ * #Wᶜ) := by ring
    _ ≤ #U * #W * (Fintype.card L * Fintype.card L) := by gcongr
    _ = #U * #W * Fintype.card L ^ 2 := by ring

/-- Upper edge bound for a `d`-regular bipartite graph with singular-value bound `lam`:
`e(U, W) ≤ d |U| |W| / N + lam d √(|U| |W|)`. -/
theorem card_interedges_le_of_nontrivialSingularValue_le [Fintype L] [Fintype R] [Fintype D]
    [DecidableEq R] (B : BipartiteRotationMap L R D)
    [Nonempty D] {lam : ℝ} (hlam : B.nontrivialSingularValue ≤ lam) (U : Finset L) (W : Finset R) :
    (#(B.interedges U W) : ℝ) ≤
      Fintype.card D * #U * #W / Fintype.card L + lam * Fintype.card D * √((#U : ℝ) * #W) := by
  have h := B.abs_card_interedges_sub_le_mul_sqrt U W
  have h1 := (le_abs_self _).trans h
  have hsq : 0 ≤ (Fintype.card D : ℝ) * √((#U : ℝ) * #W) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hlam hsq
  linarith

end Mixing

end BipartiteRotationMap

end Cslib
