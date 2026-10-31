/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Rotation maps and the spectral expansion of regular graphs

A `D`-regular undirected multigraph on `V`, with parallel edges and self-loops allowed, is presented
by its *rotation map* [Reingold, Vadhan and Wigderson, Section 2.1][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]
`rot : V × D → V × D`: `rot (v, i) = (w, j)` when the `i`-th edge at `v` leads to `w` and is the
`j`-th edge at `w`. Following an edge back returns to where it started, so `rot` is an involution;
conversely every involution of `V × D` is the rotation map of a `D`-regular multigraph. Vertices and
labels are types rather than numbers because graph products build graphs whose vertices and labels
are pairs or tuples of those of their factors.

The random walk on `G` moves from `v` along a uniformly random edge. Its action on real functions
is the walk operator `G.walk`, which averages a function over the neighbors of each vertex; it
fixes constants, preserves expectations, is self-adjoint for the uniform inner product
`𝔼 v, f v * g v` and does not increase `𝔼 v, f v ^ 2`.

The spectral expansion `λ(G)` [Arora and Barak, Section 21.1][AroraBarak09] is the operator norm of
the walk operator on the functions orthogonal to the constants
(`spectralExpansion_eq_norm_orthogonalWalk`): the smallest `c ≥ 0` with
`𝔼 v, G.walk f v ^ 2 ≤ c ^ 2 * 𝔼 v, f v ^ 2` for all `f` of expectation zero
(`spectralExpansion_le_iff`), or with `|𝔼 v, f v * G.walk f v| ≤ c * 𝔼 v, f v ^ 2`
(`spectralExpansion_le_iff_abs_expect_mul_walk_le`, `spectralExpansion_eq_ciSup`). It is the
largest absolute value of an eigenvalue of the walk operator on such functions
(`spectralExpansion_eq_ciSup_abs_eigenvalues`), but no spectral theory is needed here: everything
below is proved from these characterizations. `λ(G) ≤ 1` always, and `G` is a good expander when
`λ(G)` is small.

## Main definitions

* `Cslib.RotationMap`: a `D`-regular multigraph on `V`, given by its rotation map.
* `Cslib.RotationMap.neighbor`: the `i`-th neighbor of a vertex.
* `Cslib.RotationMap.ofInvolutive`: the `1`-regular multigraph of an involution.
* `Cslib.RotationMap.interedges`: the edges from one set of vertices to another, as darts.
* `Cslib.RotationMap.edgeCount`: the number of edges from one vertex to another.
* `Cslib.RotationMap.walk`: the walk operator.
* `Cslib.RotationMap.orthogonalSubmodule`: the subspace of `EuclideanSpace ℝ V` orthogonal to the
  constant functions.
* `Cslib.RotationMap.spectralExpansion`: the spectral expansion `λ(G)`.

## Main results

* `Cslib.RotationMap.card_interedges_comm`, `Cslib.RotationMap.edgeCount_comm`,
  `Cslib.RotationMap.sum_edgeCount`: symmetry and degree sum of edge counts.
* `Cslib.RotationMap.expect_expect_neighbor_comm`: every edge is seen once from each of its ends.
* `Cslib.RotationMap.expect_walk`, `Cslib.RotationMap.expect_mul_walk_comm`,
  `Cslib.RotationMap.expect_walk_sq_le`: the walk operator preserves expectations, is
  self-adjoint and does not increase the second moment.
* `Cslib.RotationMap.sq_walk_le`: Jensen's inequality for the walk.
* `Cslib.RotationMap.spectralExpansion_le_iff`,
  `Cslib.RotationMap.abs_expect_mul_walk_le`,
  `Cslib.RotationMap.spectralExpansion_le_iff_abs_expect_mul_walk_le`,
  `Cslib.RotationMap.spectralExpansion_eq_ciSup`: the second-moment and Rayleigh-quotient
  characterizations of `λ(G)`.
* `Cslib.RotationMap.expect_walk_pow_sq_le_spectralExpansion_pow_mul`: walks of length `t` multiply
  the second moment of a function of expectation zero by at most `λ(G) ^ (2 t)`.
* `Cslib.RotationMap.spectralExpansion_le_one`: `λ(G) ≤ 1`.
* `Cslib.RotationMap.spectralExpansion_eq_of_walk_eq`: two regular multigraphs with the same walk
  operator have the same spectral expansion.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib

open Finset
open scoped BigOperators

/-- A `D`-regular undirected multigraph on `V`, parallel edges and self-loops allowed, presented by
its rotation map [Reingold, Vadhan and Wigderson, Section 2.1][ReingoldVadhanWigderson2002]
[Arora and Barak, Section 21.3][AroraBarak09]:
`rot (v, i) = (w, j)` when the `i`-th edge at `v` leads to `w` and is the `j`-th edge at `w`. -/
@[ext]
structure RotationMap (V D : Type*) where
  /-- The rotation map, sending the `i`-th edge at `v` to the same edge seen from its other end. -/
  rot : V × D → V × D
  /-- Seeing an edge from its other end twice returns to the original end. -/
  rot_involutive : Function.Involutive rot

namespace RotationMap

variable {V D : Type*} (G : RotationMap V D)

/-- Seeing an edge from its other end twice returns to the original end. -/
@[simp]
theorem rot_rot (p : V × D) : G.rot (G.rot p) = p :=
  G.rot_involutive p

/-- The `i`-th neighbor of `v`: the other end of the `i`-th edge at `v`. -/
def neighbor (v : V) (i : D) : V :=
  (G.rot (v, i)).1

/-- The `i`-th neighbor of `v` is the first component of the rotation map at `(v, i)`. -/
theorem neighbor_def (v : V) (i : D) : G.neighbor v i = (G.rot (v, i)).1 :=
  rfl

/-- The `1`-regular multigraph of an involution `f`: the single edge at `v` leads to `f v`. A fixed
point of `f` carries a self-loop. -/
def ofInvolutive (f : V → V) (hf : Function.Involutive f) : RotationMap V Unit where
  rot p := (f p.1, p.2)
  rot_involutive p := Prod.ext (hf p.1) rfl

/-- The rotation map of the multigraph of an involution `f` applies `f` to the vertex. -/
@[simp]
theorem rot_ofInvolutive (f : V → V) (hf : Function.Involutive f) (p : V × Unit) :
    (ofInvolutive f hf).rot p = (f p.1, p.2) :=
  rfl

/-- The neighbor of `v` in the multigraph of an involution `f` is `f v`. -/
@[simp]
theorem neighbor_ofInvolutive (f : V → V) (hf : Function.Involutive f) (v : V) (i : Unit) :
    (ofInvolutive f hf).neighbor v i = f v :=
  rfl

/-- `v` is the neighbor of its `i`-th neighbor along the same edge. -/
@[simp]
theorem neighbor_neighbor_rot (v : V) (i : D) :
    G.neighbor (G.neighbor v i) (G.rot (v, i)).2 = v := by
  simp [neighbor]

section Interedges

variable [DecidableEq V] [Fintype D]

/-- The edges from `S` to `T`, as the darts `(v, i)` with `v ∈ S` whose `i`-th edge leads into `T`.
An edge between two vertices of `S ∩ T` is counted once from each end, as in the edge counts
`|E(S, T)|` of [Hoory, Linial and Wigderson, Section 2.1][HooryLinialWigderson2006]. -/
def interedges (S T : Finset V) : Finset (V × D) :=
  {p ∈ S ×ˢ univ | G.neighbor p.1 p.2 ∈ T}

variable {G} in
/-- A dart `(v, i)` goes from `S` to `T` when `v ∈ S` and its `i`-th neighbor is in `T`. -/
@[simp]
theorem mem_interedges {S T : Finset V} {p : V × D} :
    p ∈ G.interedges S T ↔ p.1 ∈ S ∧ G.neighbor p.1 p.2 ∈ T := by
  simp [interedges]

/-- No edges leave the empty set. -/
@[simp]
theorem interedges_empty_left (T : Finset V) : G.interedges ∅ T = ∅ := by
  simp [interedges]

/-- No edges enter the empty set. -/
@[simp]
theorem interedges_empty_right (S : Finset V) : G.interedges S ∅ = ∅ := by
  simp [interedges]

/-- Reversing the darts matches the edges from `S` to `T` with those from `T` to `S`. -/
theorem card_interedges_comm (S T : Finset V) : #(G.interedges S T) = #(G.interedges T S) := by
  refine card_nbij' G.rot G.rot (fun p hp ↦ ?_) (fun p hp ↦ ?_) (fun p _ ↦ G.rot_rot p)
    (fun p _ ↦ G.rot_rot p) <;>
  · rw [mem_coe, mem_interedges] at hp ⊢
    simpa [neighbor] using hp.symm

/-- Every edge at a vertex of `S` leads into `T` or into its complement. -/
theorem card_interedges_add_card_interedges_compl [Fintype V] (S T : Finset V) :
    #(G.interedges S T) + #(G.interedges S Tᶜ) = #S * Fintype.card D := by
  simp only [interedges, mem_compl]
  rw [card_filter_add_card_filter_not, card_product, card_univ]

/-- The number of edges of `G` from `v` to `u`, counted with multiplicity; `G.edgeCount v v` is the
number of self-loops at `v`. -/
def edgeCount (v u : V) : ℕ :=
  #{i | G.neighbor v i = u}

/-- `G.edgeCount v u` is the number of labels `i` with `G.neighbor v i = u`. -/
theorem edgeCount_eq_card_filter (v u : V) : G.edgeCount v u = #{i | G.neighbor v i = u} :=
  rfl

/-- At most `|D|` edges join `v` to `u`. -/
theorem edgeCount_le_card (v u : V) : G.edgeCount v u ≤ Fintype.card D :=
  card_filter_le _ _

/-- The edges of `G` from `v` to `u` are the darts between `{v}` and `{u}`. -/
theorem card_interedges_singleton (v u : V) : #(G.interedges {v} {u}) = G.edgeCount v u := by
  rw [interedges, edgeCount, singleton_product, filter_map, card_map]
  congr 1
  ext i
  simp

/-- Reversing the darts matches the edges from `v` to `u` with those from `u` to `v`. -/
theorem edgeCount_comm (v u : V) : G.edgeCount v u = G.edgeCount u v := by
  rw [← G.card_interedges_singleton, ← G.card_interedges_singleton, G.card_interedges_comm]

/-- The edge multiplicities out of `v` sum to the degree `|D|`. -/
@[simp]
theorem sum_edgeCount [Fintype V] (v : V) : ∑ u, G.edgeCount v u = Fintype.card D := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := G.neighbor v) (t := univ)
    (fun _ _ ↦ mem_univ _)]
  rfl

end Interedges

section Expect

variable [Fintype V] [Fintype D] {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]

/-- Every edge is seen once from each of its ends: averaging `F v (G.neighbor v i)` over the darts
`(v, i)` gives the same as averaging `F (G.neighbor v i) v`. -/
theorem expect_expect_neighbor_comm (F : V → V → M) :
    𝔼 v, 𝔼 i, F v (G.neighbor v i) = 𝔼 v, 𝔼 i, F (G.neighbor v i) v := by
  simp only [← expect_product', univ_product_univ]
  exact Fintype.expect_bijective G.rot G.rot_involutive.bijective _ _ fun p ↦ by simp [neighbor]

/-- The rotation map permutes the darts, so it preserves averages over them. -/
theorem expect_comp_rot (u : V × D → M) : 𝔼 q, u (G.rot q) = 𝔼 q, u q :=
  Fintype.expect_bijective G.rot G.rot_involutive.bijective _ _ fun _ ↦ rfl

/-- Averaging a function of the neighbor over all darts averages it over the vertices. -/
theorem expect_expect_neighbor [Nonempty D] (f : V → M) :
    𝔼 v, 𝔼 i, f (G.neighbor v i) = 𝔼 v, f v := by
  rw [G.expect_expect_neighbor_comm fun _ w ↦ f w]
  simp

end Expect

section Walk

variable [Fintype D]

/-- The walk operator of `G`: `G.walk f v` is the average of `f` over the neighbors of `v`, the
expected value of `f` after one step of the random walk from `v`. -/
noncomputable def walk : (V → ℝ) →ₗ[ℝ] V → ℝ where
  toFun f v := 𝔼 i, f (G.neighbor v i)
  map_add' _ _ := funext fun _ ↦ expect_add_distrib _ _ _
  map_smul' c _ := funext fun _ ↦ (smul_expect c _ _).symm

/-- `G.walk f v` is the average of `f` over the neighbors of `v`. -/
theorem walk_apply (f : V → ℝ) (v : V) : G.walk f v = 𝔼 i, f (G.neighbor v i) :=
  rfl

/-- The walk operator fixes constants. -/
@[simp]
theorem walk_const [Nonempty D] (c : ℝ) : G.walk (fun _ ↦ c) = fun _ ↦ c :=
  funext fun _ ↦ Fintype.expect_const c

/-- Walks of every length fix constants. -/
@[simp]
theorem walk_pow_const [Nonempty D] (t : ℕ) (c : ℝ) : (G.walk ^ t) (fun _ ↦ c) = fun _ ↦ c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [pow_succ, Module.End.mul_apply, walk_const, ih]

/-- **Jensen's inequality for the walk**: the square of an average of neighbors is at most the
average of the squares. -/
theorem sq_walk_le (f : V → ℝ) (v : V) : G.walk f v ^ 2 ≤ G.walk (fun w ↦ f w ^ 2) v := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp [walk_apply]
  simpa [walk_apply] using
    expect_mul_sq_le_sq_mul_sq univ (fun i ↦ f (G.neighbor v i)) fun _ ↦ 1

variable [Fintype V]

/-- The walk operator preserves expectations. -/
@[simp]
theorem expect_walk [Nonempty D] (f : V → ℝ) : 𝔼 v, G.walk f v = 𝔼 v, f v :=
  G.expect_expect_neighbor f

/-- Walks of every length preserve expectations. -/
@[simp]
theorem expect_walk_pow [Nonempty D] (t : ℕ) (f : V → ℝ) : 𝔼 v, (G.walk ^ t) f v = 𝔼 v, f v := by
  induction t with
  | zero => rfl
  | succ t ih => rw [pow_succ', Module.End.mul_apply, expect_walk, ih]

/-- The walk operator preserves expectation zero. -/
theorem expect_walk_eq_zero {f : V → ℝ} (hf : 𝔼 v, f v = 0) : 𝔼 v, G.walk f v = 0 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simp [walk_apply]
  · rw [expect_walk, hf]

/-- Walks of every length preserve expectation zero. -/
theorem expect_walk_pow_eq_zero {f : V → ℝ} (hf : 𝔼 v, f v = 0) (t : ℕ) :
    𝔼 v, (G.walk ^ t) f v = 0 := by
  induction t with
  | zero => exact hf
  | succ t ih => rw [pow_succ', Module.End.mul_apply, G.expect_walk_eq_zero ih]

/-- The walk operator is self-adjoint for the uniform inner product. -/
theorem expect_mul_walk_comm (f g : V → ℝ) :
    𝔼 v, f v * G.walk g v = 𝔼 v, G.walk f v * g v := by
  simp only [walk_apply, mul_expect, expect_mul]
  exact G.expect_expect_neighbor_comm fun v w ↦ f v * g w

/-- The walk operator does not increase the second moment. -/
theorem expect_walk_sq_le (f : V → ℝ) : 𝔼 v, G.walk f v ^ 2 ≤ 𝔼 v, f v ^ 2 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · simpa [walk_apply] using expect_nonneg fun v _ ↦ sq_nonneg (f v)
  exact (expect_le_expect fun v _ ↦ G.sq_walk_le f v).trans_eq (G.expect_walk fun v ↦ f v ^ 2)

end Walk

section SpectralExpansion

variable [Fintype V] [Fintype D]

/-- The subspace of `EuclideanSpace ℝ V` orthogonal to the constant functions. -/
noncomputable def orthogonalSubmodule (V : Type*) [Fintype V] :
    Submodule ℝ (EuclideanSpace ℝ V) :=
  (ℝ ∙ WithLp.toLp 2 (fun _ ↦ 1 : V → ℝ))ᗮ

/-- The **spectral expansion** `λ(G)`: the operator norm, for the Euclidean norm, of the walk
operator on the functions orthogonal to the constants (`spectralExpansion_eq_norm_orthogonalWalk`)
[Arora and Barak, Section 21.1][AroraBarak09].
As the walk operator is self-adjoint, this is the supremum of the absolute Rayleigh quotient
`|𝔼 v, f v * G.walk f v| / 𝔼 v, f v ^ 2` over the nonzero functions `f` of expectation zero
(`spectralExpansion_le_iff_abs_expect_mul_walk_le`, `spectralExpansion_eq_ciSup`) and the largest
absolute value of its eigenvalues on the functions of expectation zero
(`spectralExpansion_eq_ciSup_abs_eigenvalues`), but nothing here depends on spectral theory:
`λ(G)` is used through `spectralExpansion_le_iff`. -/
noncomputable def spectralExpansion : ℝ :=
  ‖(LinearMap.toContinuousLinearMap
      (G.walk.withLpMap 2 : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V)).comp
    (orthogonalSubmodule V).subtypeL‖

/-- The spectral expansion is nonnegative. -/
theorem spectralExpansion_nonneg : 0 ≤ G.spectralExpansion := by
  rw [spectralExpansion]
  positivity

variable {G}

/-- The second moment is the squared Euclidean norm, scaled by the number of vertices. -/
theorem card_mul_expect_sq (f : V → ℝ) :
    Fintype.card V * 𝔼 v, f v ^ 2 = ‖(WithLp.toLp 2 f : EuclideanSpace ℝ V)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ← nsmul_eq_mul, ← card_univ, card_smul_expect]

/-- A vector in `EuclideanSpace ℝ V` is orthogonal to the constants iff its coordinates have
expectation zero. -/
theorem mem_orthogonalSubmodule_iff (f : V → ℝ) :
    WithLp.toLp 2 f ∈ orthogonalSubmodule V ↔ 𝔼 v, f v = 0 := by
  rw [orthogonalSubmodule, Submodule.mem_orthogonal_singleton_iff_inner_right,
    EuclideanSpace.inner_toLp_toLp, Fintype.expect_eq_sum_div_card, div_eq_zero_iff,
    or_iff_left_of_imp]
  · simp [dotProduct]
  · intro h
    have : IsEmpty V := Fintype.card_eq_zero_iff.1 (Nat.cast_eq_zero.1 h)
    simp

/-- On functions of expectation zero, the walk operator multiplies the second moment by at most
`λ(G) ^ 2`. -/
theorem expect_walk_sq_le_spectralExpansion_sq_mul {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    𝔼 v, G.walk f v ^ 2 ≤ G.spectralExpansion ^ 2 * 𝔼 v, f v ^ 2 := by
  have h := ContinuousLinearMap.le_opNorm ((LinearMap.toContinuousLinearMap
      (G.walk.withLpMap 2 : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V)).comp
    (orthogonalSubmodule V).subtypeL)
    ⟨WithLp.toLp 2 f, (mem_orthogonalSubmodule_iff f).2 hf⟩
  change ‖(WithLp.toLp 2 (G.walk f) : EuclideanSpace ℝ V)‖ ≤
    G.spectralExpansion * ‖(WithLp.toLp 2 f : EuclideanSpace ℝ V)‖ at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, ← card_mul_expect_sq, ← card_mul_expect_sq, mul_left_comm] at h2
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    simp
  · exact le_of_mul_le_mul_left h2 (by positivity)

/-- If the walk operator multiplies the second moment of every function of expectation zero by at
most `c ^ 2`, where `c ≥ 0`, then `λ(G) ≤ c`. -/
theorem spectralExpansion_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ f : V → ℝ, 𝔼 v, f v = 0 → 𝔼 v, G.walk f v ^ 2 ≤ c ^ 2 * 𝔼 v, f v ^ 2) :
    G.spectralExpansion ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x ↦ ?_
  obtain ⟨⟨f⟩, hx⟩ := x
  have hf := h f ((mem_orthogonalSubmodule_iff f).1 hx)
  change ‖(WithLp.toLp 2 (G.walk f) : EuclideanSpace ℝ V)‖ ≤
    c * ‖(WithLp.toLp 2 f : EuclideanSpace ℝ V)‖
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, ← card_mul_expect_sq, ← card_mul_expect_sq, mul_left_comm]
  exact mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)

/-- `λ(G) ≤ c`, for `c ≥ 0`, exactly when the walk operator multiplies the second moment of every
function of expectation zero by at most `c ^ 2`. -/
theorem spectralExpansion_le_iff {c : ℝ} (hc : 0 ≤ c) :
    G.spectralExpansion ≤ c ↔
      ∀ f : V → ℝ, 𝔼 v, f v = 0 → 𝔼 v, G.walk f v ^ 2 ≤ c ^ 2 * 𝔼 v, f v ^ 2 := by
  refine ⟨fun hG f hf ↦ (expect_walk_sq_le_spectralExpansion_sq_mul hf).trans ?_,
    spectralExpansion_le hc⟩
  have := G.spectralExpansion_nonneg
  gcongr

/-- Polarization identity for the walk quadratic form on `t • f ± G.walk f`: the difference of the
two quadratic forms is `4 * t * 𝔼 v, G.walk f v ^ 2`. -/
private theorem expect_add_mul_walk_sub_expect_sub_mul_walk (f : V → ℝ) (t : ℝ) :
    𝔼 v, (t • f + G.walk f) v * G.walk (t • f + G.walk f) v -
        𝔼 v, (t • f - G.walk f) v * G.walk (t • f - G.walk f) v =
      4 * t * 𝔼 v, G.walk f v ^ 2 := by
  set g : V → ℝ := G.walk f
  have hfg : 𝔼 v, f v * G.walk g v = 𝔼 v, g v ^ 2 := by
    rw [G.expect_mul_walk_comm]
    exact expect_congr rfl fun v _ ↦ (sq (g v)).symm
  have hwalk_add (v : V) : G.walk (t • f + g) v = t * g v + G.walk g v := by
    simp [map_add, map_smul, g]
  have hwalk_sub (v : V) : G.walk (t • f - g) v = t * g v - G.walk g v := by
    simp [map_sub, map_smul, g]
  rw [← expect_sub_distrib]
  calc
    _ = 𝔼 v, 2 * t * (f v * G.walk g v + g v ^ 2) :=
      expect_congr rfl fun v _ ↦ by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwalk_add,
          hwalk_sub]
        ring
    _ = 2 * t * (𝔼 v, f v * G.walk g v + 𝔼 v, g v ^ 2) := by
      rw [← mul_expect, expect_add_distrib]
    _ = 4 * t * 𝔼 v, g v ^ 2 := by
      rw [hfg]
      ring

/-- If `|𝔼 v, f v * G.walk f v| ≤ c * 𝔼 v, f v ^ 2` for every function `f` of expectation zero,
where `c ≥ 0`, then `λ(G) ≤ c`. -/
theorem spectralExpansion_le_of_abs_expect_mul_walk_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ f : V → ℝ, 𝔼 v, f v = 0 → |𝔼 v, f v * G.walk f v| ≤ c * 𝔼 v, f v ^ 2) :
    G.spectralExpansion ≤ c := by
  refine spectralExpansion_le hc fun f hf ↦ ?_
  set g : V → ℝ := G.walk f
  have hg : 𝔼 v, g v = 0 := G.expect_walk_eq_zero hf
  have hpol (t : ℝ) :
      4 * t * 𝔼 v, g v ^ 2 ≤ 2 * c * (t ^ 2 * 𝔼 v, f v ^ 2 + 𝔼 v, g v ^ 2) := by
    have h₁ := (le_abs_self _).trans (h (t • f + g) (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, expect_add_distrib, ← mul_expect, hf,
        hg, mul_zero, add_zero]))
    have h₂ := (neg_le_abs _).trans (h (t • f - g) (by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, expect_sub_distrib, ← mul_expect, hf,
        hg, mul_zero, sub_zero]))
    have hdiff := G.expect_add_mul_walk_sub_expect_sub_mul_walk f t
    have hsum :
        c * 𝔼 v, (t • f + g) v ^ 2 + c * 𝔼 v, (t • f - g) v ^ 2 =
          2 * c * (t ^ 2 * 𝔼 v, f v ^ 2 + 𝔼 v, g v ^ 2) := by
      rw [← mul_add, ← expect_add_distrib]
      calc
        _ = c * 𝔼 v, 2 * (t ^ 2 * f v ^ 2 + g v ^ 2) := by
          congr 1
          refine expect_congr rfl fun v _ ↦ ?_
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        _ = 2 * c * (t ^ 2 * 𝔼 v, f v ^ 2 + 𝔼 v, g v ^ 2) := by
          rw [← mul_expect, expect_add_distrib, ← mul_expect]
          ring
    linarith
  rcases hc.eq_or_lt with rfl | hc
  · have := hpol 1
    linarith
  · have := hpol c
    refine le_of_mul_le_mul_left ?_ (show 0 < 2 * c by positivity)
    linarith

/-- For `f` of expectation zero, the correlation `𝔼 v, f v * G.walk f v` is at most `λ(G)` times
the second moment of `f` in absolute value. -/
theorem abs_expect_mul_walk_le {f : V → ℝ} (hf : 𝔼 v, f v = 0) :
    |𝔼 v, f v * G.walk f v| ≤ G.spectralExpansion * 𝔼 v, f v ^ 2 := by
  have := G.spectralExpansion_nonneg
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc
    _ ≤ (𝔼 v, f v ^ 2) * 𝔼 v, G.walk f v ^ 2 := expect_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (𝔼 v, f v ^ 2) * (G.spectralExpansion ^ 2 * 𝔼 v, f v ^ 2) := by
      gcongr
      exact expect_walk_sq_le_spectralExpansion_sq_mul hf
    _ = _ := by ring

/-- `λ(G) ≤ c`, for `c ≥ 0`, exactly when `|𝔼 v, f v * G.walk f v| ≤ c * 𝔼 v, f v ^ 2` for every
function `f` of expectation zero. -/
theorem spectralExpansion_le_iff_abs_expect_mul_walk_le {c : ℝ} (hc : 0 ≤ c) :
    G.spectralExpansion ≤ c ↔
      ∀ f : V → ℝ, 𝔼 v, f v = 0 → |𝔼 v, f v * G.walk f v| ≤ c * 𝔼 v, f v ^ 2 := by
  refine ⟨fun hG f hf ↦ (abs_expect_mul_walk_le hf).trans ?_,
    spectralExpansion_le_of_abs_expect_mul_walk_le hc⟩
  gcongr

variable (G)

/-- The spectral expansion `λ(G)` is the supremum of the absolute Rayleigh quotient
`|𝔼 v, f v * G.walk f v| / 𝔼 v, f v ^ 2` over the nonzero functions `f` of expectation zero. -/
theorem spectralExpansion_eq_ciSup :
    G.spectralExpansion =
      ⨆ f : {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0}, |𝔼 v, f.1 v * G.walk f.1 v| / 𝔼 v, f.1 v ^ 2 := by
  have hle (f : {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0}) :
      |𝔼 v, f.1 v * G.walk f.1 v| / 𝔼 v, f.1 v ^ 2 ≤ G.spectralExpansion :=
    div_le_of_le_mul₀ (expect_nonneg fun _ _ ↦ sq_nonneg _) G.spectralExpansion_nonneg
      (abs_expect_mul_walk_le f.2.1)
  refine le_antisymm ?_ (Real.iSup_le hle G.spectralExpansion_nonneg)
  refine spectralExpansion_le_of_abs_expect_mul_walk_le (Real.iSup_nonneg fun _ ↦ by positivity)
    fun f hf ↦ ?_
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hf0
  have hpos : 0 < 𝔼 w, f w ^ 2 :=
    expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v, mem_univ v, sq_pos_iff.2 hv⟩
  rw [← div_le_iff₀ hpos]
  exact le_ciSup ⟨G.spectralExpansion, Set.forall_mem_range.2 hle⟩ ⟨f, hf, hf0⟩

/-- The spectral expansion is at most one. -/
theorem spectralExpansion_le_one : G.spectralExpansion ≤ 1 :=
  spectralExpansion_le zero_le_one fun f _ ↦ by simpa using G.expect_walk_sq_le f

/-- Walks of length `t` multiply the second moment of a function of expectation zero by at most
`λ(G) ^ (2 t)`. -/
theorem expect_walk_pow_sq_le_spectralExpansion_pow_mul {f : V → ℝ}
    (hf : 𝔼 v, f v = 0) (t : ℕ) :
    𝔼 v, (G.walk ^ t) f v ^ 2 ≤ G.spectralExpansion ^ (2 * t) * 𝔼 v, f v ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have := G.spectralExpansion_nonneg
    calc
      _ ≤ G.spectralExpansion ^ 2 * 𝔼 v, (G.walk ^ t) f v ^ 2 := by
        rw [pow_succ', Module.End.mul_apply]
        exact expect_walk_sq_le_spectralExpansion_sq_mul (G.expect_walk_pow_eq_zero hf t)
      _ ≤ G.spectralExpansion ^ 2 * (G.spectralExpansion ^ (2 * t) * 𝔼 v, f v ^ 2) := by gcongr
      _ = G.spectralExpansion ^ (2 * (t + 1)) * 𝔼 v, f v ^ 2 := by ring

/-- On at most one vertex the spectral expansion is zero: the only function of expectation zero is
zero. -/
theorem spectralExpansion_eq_zero_of_subsingleton [Subsingleton V] : G.spectralExpansion = 0 := by
  have h {f : V → ℝ} (hf : 𝔼 v, f v = 0) (v : V) : f v = 0 := by
    have : Nonempty V := ⟨v⟩
    calc f v = 𝔼 _w : V, f v := (Fintype.expect_const _).symm
      _ = 𝔼 w, f w := expect_congr rfl fun w _ ↦ congrArg f (Subsingleton.elim v w)
      _ = 0 := hf
  refine le_antisymm (spectralExpansion_le le_rfl fun f hf ↦ ?_) G.spectralExpansion_nonneg
  simp [h (G.expect_walk_eq_zero hf)]

variable {G} in
/-- Two regular multigraphs on the same vertices with the same walk operator have the same
spectral expansion, whatever their edge labels. -/
theorem spectralExpansion_eq_of_walk_eq {E : Type*} [Fintype E] {H : RotationMap V E}
    (h : G.walk = H.walk) : G.spectralExpansion = H.spectralExpansion := by
  simp only [spectralExpansion, h]

end SpectralExpansion

end RotationMap

end Cslib
