/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.Expander.Cheeger
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral theory of the walk operator on regular graphs

The walk operator `G.walk` of a regular multigraph `G` is self-adjoint for the uniform inner
product `𝔼 v, f v * g v`, and therefore defines a symmetric linear endomorphism `G.walkEuclidean`
on `EuclideanSpace ℝ V` (`isSymmetric_walkEuclidean`). It preserves the subspace
`orthogonalSubmodule V` of functions orthogonal to the constants—equivalently, of expectation zero
(`mem_orthogonalSubmodule_iff`)—and restricts to a symmetric endomorphism `G.orthogonalWalk` on
that subspace (`isSymmetric_orthogonalWalk`).

By the finite-dimensional spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`), the spectral
expansion `λ(G)` (`spectralExpansion`) and the second eigenvalue `λ₂(G)` (`secondEigenvalue`),
which are defined in `Expander.Basic` and `Expander.Cheeger` without spectral theory, agree with the
eigenvalue quantities they name:

* `λ(G)` is the operator norm of `G.orthogonalWalk` (`spectralExpansion_eq_norm_orthogonalWalk`)
  and the maximum absolute value of its eigenvalues (`spectralExpansion_eq_ciSup_abs_eigenvalues`).
* When `V` has at least two vertices, `λ₂(G)` is the maximum eigenvalue of `G.orthogonalWalk`
  (`secondEigenvalue_eq_ciSup_eigenvalues`, `secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero`).
* On the full space `EuclideanSpace ℝ V`, every eigenvalue of `G.walkEuclidean` lies in `[-1, 1]`
  (`abs_walkEuclidean_eigenvalues_le_one`); for a graph of positive degree, the largest eigenvalue
  is `1` (`walkEuclidean_eigenvalues_zero`) and the second largest eigenvalue counted with
  multiplicity is `λ₂(G)` (`secondEigenvalue_eq_walkEuclidean_eigenvalues_one`).

## Main definitions

* `Cslib.RotationMap.walkEuclidean`: the walk operator on `EuclideanSpace ℝ V`.
* `Cslib.RotationMap.orthogonalSubmodule`: the subspace of `EuclideanSpace ℝ V` orthogonal to the
  constant functions.
* `Cslib.RotationMap.orthogonalWalk`: the restriction of `G.walkEuclidean` to
  `orthogonalSubmodule V`.

## Main results

* `Cslib.RotationMap.isSymmetric_walkEuclidean`, `Cslib.RotationMap.isSymmetric_orthogonalWalk`:
  `G.walkEuclidean` and `G.orthogonalWalk` are symmetric.
* `Cslib.RotationMap.mem_orthogonalSubmodule_iff`: `WithLp.toLp 2 f ∈ orthogonalSubmodule V`
  iff `𝔼 v, f v = 0`.
* `Cslib.RotationMap.spectralExpansion_eq_norm_orthogonalWalk`: `λ(G)` is the operator norm of
  `G.orthogonalWalk`.
* `Cslib.RotationMap.abs_orthogonalWalk_eigenvalues_le`,
  `Cslib.RotationMap.orthogonalWalk_eigenvalues_le_secondEigenvalue`: every eigenvalue of
  `G.orthogonalWalk` has absolute value at most `λ(G)` and is at most `λ₂(G)`.
* `Cslib.RotationMap.spectralExpansion_eq_ciSup_abs_eigenvalues`: `λ(G)` is the supremum of the
  absolute values of the eigenvalues of `G.orthogonalWalk`.
* `Cslib.RotationMap.secondEigenvalue_eq_ciSup_eigenvalues`,
  `Cslib.RotationMap.secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero`: on at least two
  vertices, `λ₂(G)` is the largest eigenvalue of `G.orthogonalWalk`.
* `Cslib.RotationMap.abs_walkEuclidean_eigenvalues_le_one`,
  `Cslib.RotationMap.walkEuclidean_eigenvalues_zero`,
  `Cslib.RotationMap.secondEigenvalue_eq_walkEuclidean_eigenvalues_one`: the eigenvalues of
  `G.walkEuclidean` lie in `[-1, 1]`, with top eigenvalue `1` and second eigenvalue `λ₂(G)`.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators RealInnerProductSpace

variable {V D : Type*} [Fintype D] (G : RotationMap V D)

/-- The walk operator of `G` transported to `EuclideanSpace ℝ V`. -/
noncomputable def walkEuclidean : Module.End ℝ (EuclideanSpace ℝ V) :=
  G.walk.withLpMap 2

/-- Applying `G.walkEuclidean` to `WithLp.toLp 2 f` applies `G.walk` to `f`. -/
@[simp]
theorem walkEuclidean_toLp (f : V → ℝ) :
    G.walkEuclidean (WithLp.toLp 2 f) = WithLp.toLp 2 (G.walk f) :=
  rfl

/-- Applying `G.walkEuclidean` and projecting from `EuclideanSpace ℝ V` applies `G.walk`. -/
@[simp]
theorem ofLp_walkEuclidean (x : EuclideanSpace ℝ V) :
    (G.walkEuclidean x).ofLp = G.walk x.ofLp :=
  rfl

variable [Fintype V]

/-- The Euclidean inner product on `EuclideanSpace ℝ V` is the expectation of the pointwise product
scaled by `|V|`. -/
private theorem card_mul_expect_mul (x y : EuclideanSpace ℝ V) :
    (Fintype.card V : ℝ) * 𝔼 v, x.ofLp v * y.ofLp v = ⟪x, y⟫ := by
  rw [Fintype.card_mul_expect, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  exact sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The walk operator on `EuclideanSpace ℝ V` is symmetric. -/
theorem isSymmetric_walkEuclidean : G.walkEuclidean.IsSymmetric := fun x y ↦ by
  rw [← card_mul_expect_mul, ← card_mul_expect_mul, ofLp_walkEuclidean, ofLp_walkEuclidean,
    G.expect_mul_walk_comm]

/-- The walk operator preserves `orthogonalSubmodule V`. -/
theorem walkEuclidean_mem_orthogonalSubmodule {x : EuclideanSpace ℝ V}
    (hx : x ∈ orthogonalSubmodule V) :
    G.walkEuclidean x ∈ orthogonalSubmodule V := by
  rw [← WithLp.toLp_ofLp 2 (G.walkEuclidean x), ofLp_walkEuclidean, mem_orthogonalSubmodule_iff]
  exact G.expect_walk_eq_zero
    ((mem_orthogonalSubmodule_iff x.ofLp).1 (by rwa [WithLp.toLp_ofLp]))

/-- The restriction of `G.walkEuclidean` to the subspace `orthogonalSubmodule V` of functions of
expectation zero. -/
noncomputable def orthogonalWalk : orthogonalSubmodule V →ₗ[ℝ] orthogonalSubmodule V :=
  G.walkEuclidean.restrict fun _ hx ↦ G.walkEuclidean_mem_orthogonalSubmodule hx

/-- Coercing `G.orthogonalWalk u` to `EuclideanSpace ℝ V` applies `G.walkEuclidean` to `u`. -/
@[simp]
theorem coe_orthogonalWalk (u : orthogonalSubmodule V) :
    (G.orthogonalWalk u : EuclideanSpace ℝ V) = G.walkEuclidean u :=
  rfl

/-- The restricted walk operator `G.orthogonalWalk` is symmetric. -/
theorem isSymmetric_orthogonalWalk : G.orthogonalWalk.IsSymmetric :=
  G.isSymmetric_walkEuclidean.restrict_invariant _

/-- The spectral expansion `λ(G)` is the operator norm of the restricted walk operator
`G.orthogonalWalk` on `orthogonalSubmodule V`. -/
theorem spectralExpansion_eq_norm_orthogonalWalk :
    G.spectralExpansion = ‖G.orthogonalWalk.toContinuousLinearMap‖ :=
  le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G.orthogonalWalk.toContinuousLinearMap)
      (ContinuousLinearMap.le_opNorm G.orthogonalWalk.toContinuousLinearMap))
    (ContinuousLinearMap.opNorm_le_bound _ G.spectralExpansion_nonneg
      (ContinuousLinearMap.le_opNorm _))

section SpectralDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : Module.End ℝ E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n)

/-- In the eigenvector basis of a symmetric operator, the squared norm is the sum of squared
coordinates. -/
private theorem norm_sq_eq_sum_eigenvectorBasis_repr (u : E) :
    ‖u‖ ^ 2 = ∑ i : Fin n, (hT.eigenvectorBasis hn).repr u i ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map u, EuclideanSpace.real_norm_sq_eq]

/-- In the eigenvector basis of a symmetric operator, the squared norm of `T u` is the sum of
squared coordinates weighted by the squared eigenvalues. -/
private theorem norm_apply_sq_eq_sum_eigenvalues (u : E) :
    ‖T u‖ ^ 2 =
      ∑ i : Fin n, hT.eigenvalues hn i ^ 2 * (hT.eigenvectorBasis hn).repr u i ^ 2 := by
  rw [norm_sq_eq_sum_eigenvectorBasis_repr hT hn (T u)]
  refine sum_congr rfl fun i _ ↦ ?_
  have h := hT.eigenvectorBasis_apply_self_apply hn u i
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [h, mul_pow]

/-- In the eigenvector basis of a symmetric operator, the quadratic form `⟪u, T u⟫` is the sum of
squared coordinates weighted by the eigenvalues. -/
private theorem inner_self_eq_sum_eigenvalues (u : E) :
    ⟪u, T u⟫ = ∑ i : Fin n, hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr u i ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map u (T u),
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  refine sum_congr rfl fun i _ ↦ ?_
  have h := hT.eigenvectorBasis_apply_self_apply hn u i
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  change (hT.eigenvectorBasis hn).repr (T u) i * (hT.eigenvectorBasis hn).repr u i = _
  rw [h]
  ring

end SpectralDecomposition

section OrthogonalSpectrum

variable {n : ℕ} (hn : Module.finrank ℝ (orthogonalSubmodule V) = n)

/-- Every eigenvalue of `G.orthogonalWalk` has absolute value at most `λ(G)`. -/
theorem abs_orthogonalWalk_eigenvalues_le (i : Fin n) :
    |G.isSymmetric_orthogonalWalk.eigenvalues hn i| ≤ G.spectralExpansion := by
  set u := G.isSymmetric_orthogonalWalk.eigenvectorBasis hn i
  set μ := G.isSymmetric_orthogonalWalk.eigenvalues hn i
  set f : V → ℝ := u.1.ofLp
  have hf : 𝔼 v, f v = 0 := (mem_orthogonalSubmodule_iff f).1 (by simp [f])
  have hu_ne : u ≠ 0 := (G.isSymmetric_orthogonalWalk.eigenvectorBasis hn).toBasis.ne_zero i
  have hf_ne : f ≠ 0 := fun h ↦ hu_ne (Subtype.ext (WithLp.ofLp_injective 2 h))
  obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 hf_ne
  have hpos : 0 < 𝔼 v, f v ^ 2 :=
    expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v₀, mem_univ v₀, sq_pos_iff.2 hv₀⟩
  have hwalk : G.walk f = μ • f :=
    congrArg (fun w : orthogonalSubmodule V ↦ w.1.ofLp)
      (G.isSymmetric_orthogonalWalk.apply_eigenvectorBasis hn i)
  have hmul : 𝔼 v, f v * G.walk f v = μ * 𝔼 v, f v ^ 2 := by
    rw [hwalk, mul_expect]
    exact expect_congr rfl fun v _ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have habs := G.abs_expect_mul_walk_le hf
  rw [hmul, abs_mul, abs_of_pos hpos] at habs
  exact le_of_mul_le_mul_right habs hpos

/-- Every eigenvalue of `G.orthogonalWalk` is at most `λ₂(G)`. -/
theorem orthogonalWalk_eigenvalues_le_secondEigenvalue (i : Fin n) :
    G.isSymmetric_orthogonalWalk.eigenvalues hn i ≤ G.secondEigenvalue := by
  set u := G.isSymmetric_orthogonalWalk.eigenvectorBasis hn i
  set μ := G.isSymmetric_orthogonalWalk.eigenvalues hn i
  set f : V → ℝ := u.1.ofLp
  have hf : 𝔼 v, f v = 0 := (mem_orthogonalSubmodule_iff f).1 (by simp [f])
  have hu_ne : u ≠ 0 := (G.isSymmetric_orthogonalWalk.eigenvectorBasis hn).toBasis.ne_zero i
  have hf_ne : f ≠ 0 := fun h ↦ hu_ne (Subtype.ext (WithLp.ofLp_injective 2 h))
  obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 hf_ne
  have hpos : 0 < 𝔼 v, f v ^ 2 :=
    expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v₀, mem_univ v₀, sq_pos_iff.2 hv₀⟩
  have hwalk : G.walk f = μ • f :=
    congrArg (fun w : orthogonalSubmodule V ↦ w.1.ofLp)
      (G.isSymmetric_orthogonalWalk.apply_eigenvectorBasis hn i)
  have hmul : 𝔼 v, f v * G.walk f v = μ * 𝔼 v, f v ^ 2 := by
    rw [hwalk, mul_expect]
    exact expect_congr rfl fun v _ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hle := G.expect_mul_walk_le_secondEigenvalue_mul hf
  rw [hmul] at hle
  exact le_of_mul_le_mul_right hle hpos

/-- The spectral expansion `λ(G)` is the supremum of the absolute values of the eigenvalues of
`G.orthogonalWalk`. -/
theorem spectralExpansion_eq_ciSup_abs_eigenvalues :
    G.spectralExpansion = ⨆ i : Fin n, |G.isSymmetric_orthogonalWalk.eigenvalues hn i| := by
  set c := ⨆ i : Fin n, |G.isSymmetric_orthogonalWalk.eigenvalues hn i|
  have hc : 0 ≤ c := Real.iSup_nonneg fun _ ↦ abs_nonneg _
  refine le_antisymm ?_
    (Real.iSup_le (G.abs_orthogonalWalk_eigenvalues_le hn) G.spectralExpansion_nonneg)
  refine G.spectralExpansion_le hc fun f hf ↦ ?_
  let u : orthogonalSubmodule V := ⟨WithLp.toLp 2 f, (mem_orthogonalSubmodule_iff f).2 hf⟩
  have hle : ‖G.orthogonalWalk u‖ ^ 2 ≤ c ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_apply_sq_eq_sum_eigenvalues G.isSymmetric_orthogonalWalk hn u,
      norm_sq_eq_sum_eigenvectorBasis_repr G.isSymmetric_orthogonalWalk hn u, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    have hi : |G.isSymmetric_orthogonalWalk.eigenvalues hn i| ≤ c :=
      le_ciSup (f := fun j : Fin n ↦ |G.isSymmetric_orthogonalWalk.eigenvalues hn j|)
        (Finite.bddAbove_range _) i
    have hi2 : G.isSymmetric_orthogonalWalk.eigenvalues hn i ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    exact mul_le_mul_of_nonneg_right hi2 (sq_nonneg _)
  have hnorm_u : ‖u‖ ^ 2 = (Fintype.card V : ℝ) * 𝔼 v, f v ^ 2 :=
    (card_mul_expect_sq f).symm
  have hnorm_wu : ‖G.orthogonalWalk u‖ ^ 2 = (Fintype.card V : ℝ) * 𝔼 v, G.walk f v ^ 2 :=
    (card_mul_expect_sq (G.walk f)).symm
  rw [hnorm_wu, hnorm_u, mul_left_comm] at hle
  rcases (Fintype.card V).eq_zero_or_pos with hV | hV
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hV
    simp
  · exact le_of_mul_le_mul_left hle (Nat.cast_pos.2 hV)

/-- When `orthogonalSubmodule V` has positive dimension `n`, the second eigenvalue `λ₂(G)` is the
largest eigenvalue of `G.orthogonalWalk`. -/
theorem secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero (h0 : 0 < n) :
    G.secondEigenvalue = G.isSymmetric_orthogonalWalk.eigenvalues hn ⟨0, h0⟩ := by
  have : Nontrivial (orthogonalSubmodule V) :=
    Module.nontrivial_of_finrank_pos (hn ▸ h0)
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have hsub : Subsingleton (orthogonalSubmodule V) := by
      refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ Subtype.ext (WithLp.ofLp_injective 2 (funext fun v ↦ ?_))⟩
      have hx0 := (mem_orthogonalSubmodule_iff x.ofLp).1 (by simpa using hx)
      have hy0 := (mem_orthogonalSubmodule_iff y.ofLp).1 (by simpa using hy)
      have : Nonempty V := ⟨v⟩
      have hconst (g : V → ℝ) : g v = 𝔼 w, g w := by
        calc g v = 𝔼 _w : V, g v := (Fintype.expect_const _).symm
          _ = 𝔼 w, g w := expect_congr rfl fun w _ ↦ congrArg g (Subsingleton.elim v w)
      rw [hconst x.ofLp, hconst y.ofLp, hx0, hy0]
    exact not_subsingleton (orthogonalSubmodule V) hsub
  refine le_antisymm ?_ (G.orthogonalWalk_eigenvalues_le_secondEigenvalue hn ⟨0, h0⟩)
  refine G.secondEigenvalue_le_iff.2 fun f hf ↦ ?_
  let u : orthogonalSubmodule V := ⟨WithLp.toLp 2 f, (mem_orthogonalSubmodule_iff f).2 hf⟩
  have hle : ⟪u, G.orthogonalWalk u⟫ ≤
      G.isSymmetric_orthogonalWalk.eigenvalues hn ⟨0, h0⟩ * ‖u‖ ^ 2 := by
    rw [inner_self_eq_sum_eigenvalues G.isSymmetric_orthogonalWalk hn u,
      norm_sq_eq_sum_eigenvectorBasis_repr G.isSymmetric_orthogonalWalk hn u, mul_sum]
    refine sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
      (G.isSymmetric_orthogonalWalk.eigenvalues_antitone hn
        (show (⟨0, h0⟩ : Fin n) ≤ i from Nat.zero_le i.1))
      (sq_nonneg _)
  have hinner : ⟪u, G.orthogonalWalk u⟫ = (Fintype.card V : ℝ) * 𝔼 v, f v * G.walk f v :=
    (card_mul_expect_mul (WithLp.toLp 2 f) (WithLp.toLp 2 (G.walk f))).symm
  have hnorm : ‖u‖ ^ 2 = (Fintype.card V : ℝ) * 𝔼 v, f v ^ 2 :=
    (card_mul_expect_sq f).symm
  rw [hinner, hnorm, mul_left_comm] at hle
  exact le_of_mul_le_mul_left hle (Nat.cast_pos.2 Fintype.card_pos)

/-- On at least two vertices, the second eigenvalue `λ₂(G)` is the supremum of the eigenvalues of
`G.orthogonalWalk`. -/
theorem secondEigenvalue_eq_ciSup_eigenvalues [Nontrivial V] :
    G.secondEigenvalue = ⨆ i : Fin n, G.isSymmetric_orthogonalWalk.eigenvalues hn i := by
  have hnt : Nontrivial (orthogonalSubmodule V) := by
    classical
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    let f : V → ℝ := Pi.single a 1 - Pi.single b 1
    have hf : 𝔼 v, f v = 0 := by
      simp [f, expect_sub_distrib, Fintype.expect_eq_sum_div_card]
    refine ⟨⟨WithLp.toLp 2 f, (mem_orthogonalSubmodule_iff f).2 hf⟩, 0, fun h ↦ ?_⟩
    have h0 : f a = 0 := congrFun (congrArg WithLp.ofLp (congrArg Subtype.val h)) a
    simp [f, hab] at h0
  have h0 : 0 < n := hn ▸ Module.finrank_pos
  have : Nonempty (Fin n) := ⟨⟨0, h0⟩⟩
  rw [G.secondEigenvalue_eq_orthogonalWalk_eigenvalues_zero hn h0]
  refine le_antisymm
    (le_ciSup (f := G.isSymmetric_orthogonalWalk.eigenvalues hn) (Finite.bddAbove_range _) ⟨0, h0⟩)
    (ciSup_le fun i ↦ ?_)
  exact G.isSymmetric_orthogonalWalk.eigenvalues_antitone hn
    (show (⟨0, h0⟩ : Fin n) ≤ i from Nat.zero_le i.1)

end OrthogonalSpectrum

section FullSpectrum

variable {m : ℕ} (hm : Module.finrank ℝ (EuclideanSpace ℝ V) = m)

/-- Every eigenvalue of `G.walkEuclidean` on `EuclideanSpace ℝ V` has absolute value at most `1`. -/
theorem abs_walkEuclidean_eigenvalues_le_one (i : Fin m) :
    |G.isSymmetric_walkEuclidean.eigenvalues hm i| ≤ 1 := by
  set u := G.isSymmetric_walkEuclidean.eigenvectorBasis hm i
  set μ := G.isSymmetric_walkEuclidean.eigenvalues hm i
  set f : V → ℝ := u.ofLp
  have hu_ne : u ≠ 0 := (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).toBasis.ne_zero i
  have hf_ne : f ≠ 0 := fun h ↦ hu_ne (WithLp.ofLp_injective 2 h)
  obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 hf_ne
  have hpos : 0 < 𝔼 v, f v ^ 2 :=
    expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v₀, mem_univ v₀, sq_pos_iff.2 hv₀⟩
  have hwalk : G.walk f = μ • f :=
    congrArg WithLp.ofLp (G.isSymmetric_walkEuclidean.apply_eigenvectorBasis hm i)
  have hmul : 𝔼 v, f v * G.walk f v = μ * 𝔼 v, f v ^ 2 := by
    rw [hwalk, mul_expect]
    exact expect_congr rfl fun v _ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have habs := G.abs_expect_mul_walk_le_expect_sq f
  rw [hmul, abs_mul, abs_of_pos hpos] at habs
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- On a nonempty vertex set and positive degree, the largest eigenvalue of `G.walkEuclidean` is
`1`. -/
theorem walkEuclidean_eigenvalues_zero [Nonempty D] (hm0 : 0 < m) :
    G.isSymmetric_walkEuclidean.eigenvalues hm ⟨0, hm0⟩ = 1 := by
  refine le_antisymm (le_of_abs_le (G.abs_walkEuclidean_eigenvalues_le_one hm ⟨0, hm0⟩)) ?_
  have : Nontrivial (EuclideanSpace ℝ V) := Module.nontrivial_of_finrank_pos (hm ▸ hm0)
  have : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    exact not_subsingleton (EuclideanSpace ℝ V) inferInstance
  let oneVec : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ ↦ 1)
  have hone_ne : oneVec ≠ 0 := fun h ↦ by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    simpa [oneVec] using congrFun (congrArg WithLp.ofLp h) v₀
  have heig : Module.End.HasEigenvalue G.walkEuclidean 1 := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hone_ne⟩
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact WithLp.ofLp_injective 2 (G.walk_const 1)
  obtain ⟨i, hi⟩ := G.isSymmetric_walkEuclidean.exists_eigenvalues_eq hm heig
  calc (1 : ℝ) = G.isSymmetric_walkEuclidean.eigenvalues hm i := hi.symm
    _ ≤ G.isSymmetric_walkEuclidean.eigenvalues hm ⟨0, hm0⟩ :=
      G.isSymmetric_walkEuclidean.eigenvalues_antitone hm
        (show (⟨0, hm0⟩ : Fin m) ≤ i from Nat.zero_le i.1)

/-- Any nonzero `u : EuclideanSpace ℝ V` with `𝔼 v, u.ofLp v = 0` and
`μ * ‖u‖ ^ 2 ≤ ⟪u, G.walkEuclidean u⟫` satisfies `μ ≤ G.secondEigenvalue`. -/
private theorem le_secondEigenvalue_of_mul_norm_sq_le_inner [Nonempty V]
    {u : EuclideanSpace ℝ V} (hu_ne : u ≠ 0) (hu_exp : 𝔼 v, u.ofLp v = 0) {μ : ℝ}
    (hu_quad : μ * ‖u‖ ^ 2 ≤ ⟪u, G.walkEuclidean u⟫) :
    μ ≤ G.secondEigenvalue := by
  set f : V → ℝ := u.ofLp
  have hf_ne : f ≠ 0 := fun h ↦ hu_ne (WithLp.ofLp_injective 2 h)
  obtain ⟨v₀, hv₀⟩ := Function.ne_iff.1 hf_ne
  have hpos : 0 < 𝔼 v, f v ^ 2 :=
    expect_pos' (fun _ _ ↦ sq_nonneg _) ⟨v₀, mem_univ v₀, sq_pos_iff.2 hv₀⟩
  have hinner : ⟪u, G.walkEuclidean u⟫ = (Fintype.card V : ℝ) * 𝔼 v, f v * G.walk f v :=
    (card_mul_expect_mul u (G.walkEuclidean u)).symm
  have hnorm : ‖u‖ ^ 2 = (Fintype.card V : ℝ) * 𝔼 v, f v ^ 2 := by
    simpa [f] using (card_mul_expect_sq f).symm
  rw [hinner, hnorm, mul_left_comm] at hu_quad
  have hle₁ := le_of_mul_le_mul_left hu_quad (Nat.cast_pos.2 Fintype.card_pos)
  have hle₂ := G.expect_mul_walk_le_secondEigenvalue_mul hu_exp
  exact le_of_mul_le_mul_right (hle₁.trans hle₂) hpos

/-- When `eigenvalues hm ⟨1, hm1⟩ < 1`, the top eigenvector of `G.walkEuclidean` spans the constant
functions, so every `x : EuclideanSpace ℝ V` of mean zero has `0`-th coordinate `0` in the
eigenvector basis. -/
private theorem walkEuclidean_eigenvectorBasis_repr_zero_eq_zero [Nonempty V] [Nonempty D]
    (hm1 : 1 < m) (hlt : G.isSymmetric_walkEuclidean.eigenvalues hm ⟨1, hm1⟩ < 1)
    {x : EuclideanSpace ℝ V} (hf : 𝔼 v, x.ofLp v = 0) :
    (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr x ⟨0, by omega⟩ = 0 := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, hm1⟩
  let oneVec : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ ↦ 1)
  have hone_walk : G.walkEuclidean oneVec = oneVec :=
    WithLp.ofLp_injective 2 (G.walk_const 1)
  have hone_repr (i : Fin m) (hi : i ≠ i₀) :
      (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr oneVec i = 0 := by
    have hhi : i₁ ≤ i := Nat.one_le_iff_ne_zero.2 (Fin.val_ne_of_ne hi)
    have hμi : G.isSymmetric_walkEuclidean.eigenvalues hm i < 1 :=
      (G.isSymmetric_walkEuclidean.eigenvalues_antitone hm hhi).trans_lt hlt
    have heq := G.isSymmetric_walkEuclidean.eigenvectorBasis_apply_self_apply hm oneVec i
    simp only [hone_walk, RCLike.ofReal_real_eq_id, id_eq] at heq
    nlinarith
  have hone_ne : oneVec ≠ 0 := fun h ↦ by
    obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
    simpa [oneVec] using congrFun (congrArg WithLp.ofLp h) v₀
  have hone_i₀ : (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr oneVec i₀ ≠ 0 :=
    fun h0 ↦ hone_ne <| (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr.injective <| by
      ext i
      rcases eq_or_ne i i₀ with rfl | hi
      · simp [h0]
      · simp [hone_repr i hi]
  have hx_orth : ⟪oneVec, x⟫ = 0 := by
    rw [← card_mul_expect_mul]
    simp [oneVec, hf]
  rw [← (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr.inner_map_map oneVec x,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    Fintype.sum_eq_single i₀] at hx_orth
  · exact (mul_eq_zero.1 hx_orth).resolve_right hone_i₀
  · intro i hi
    change (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr x i *
      (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr oneVec i = 0
    rw [hone_repr i hi, mul_zero]

/-- On at least two vertices and positive degree, `G.secondEigenvalue` is at most the second
eigenvalue of `G.walkEuclidean`. -/
private theorem secondEigenvalue_le_walkEuclidean_eigenvalues_one [Nonempty D] (hm1 : 1 < m) :
    G.secondEigenvalue ≤ G.isSymmetric_walkEuclidean.eigenvalues hm ⟨1, hm1⟩ := by
  have hm0 : 0 < m := by omega
  have hcard : Fintype.card V = m := by simpa [finrank_euclideanSpace] using hm
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  let i₀ : Fin m := ⟨0, hm0⟩
  let i₁ : Fin m := ⟨1, hm1⟩
  rcases (le_of_abs_le (G.abs_walkEuclidean_eigenvalues_le_one hm i₁)).eq_or_lt with h1 | hlt
  · rw [h1]
    exact G.secondEigenvalue_le_one
  refine G.secondEigenvalue_le_iff.2 fun f hf ↦ ?_
  let x : EuclideanSpace ℝ V := WithLp.toLp 2 f
  have hx_i₀ : (G.isSymmetric_walkEuclidean.eigenvectorBasis hm).repr x i₀ = 0 :=
    G.walkEuclidean_eigenvectorBasis_repr_zero_eq_zero hm hm1 hlt hf
  have hle : ⟪x, G.walkEuclidean x⟫ ≤
      G.isSymmetric_walkEuclidean.eigenvalues hm i₁ * ‖x‖ ^ 2 := by
    rw [inner_self_eq_sum_eigenvalues G.isSymmetric_walkEuclidean hm x,
      norm_sq_eq_sum_eigenvectorBasis_repr G.isSymmetric_walkEuclidean hm x, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [hx_i₀]
      simp
    · have hhi : i₁ ≤ i := Nat.one_le_iff_ne_zero.2 (Fin.val_ne_of_ne hi)
      exact mul_le_mul_of_nonneg_right
        (G.isSymmetric_walkEuclidean.eigenvalues_antitone hm hhi) (sq_nonneg _)
  have hinner : ⟪x, G.walkEuclidean x⟫ = (Fintype.card V : ℝ) * 𝔼 v, f v * G.walk f v :=
    (card_mul_expect_mul x (G.walkEuclidean x)).symm
  have hnorm : ‖x‖ ^ 2 = (Fintype.card V : ℝ) * 𝔼 v, f v ^ 2 :=
    (card_mul_expect_sq f).symm
  rw [hinner, hnorm, mul_left_comm] at hle
  exact le_of_mul_le_mul_left hle (Nat.cast_pos.2 Fintype.card_pos)

/-- On at least two vertices, the second eigenvalue of `G.walkEuclidean` is at most
`G.secondEigenvalue`. -/
private theorem walkEuclidean_eigenvalues_one_le_secondEigenvalue (hm1 : 1 < m) :
    G.isSymmetric_walkEuclidean.eigenvalues hm ⟨1, hm1⟩ ≤ G.secondEigenvalue := by
  have hcard : Fintype.card V = m := by simpa [finrank_euclideanSpace] using hm
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, hm1⟩
  have hi₀₁ : i₀ ≠ i₁ := Fin.ne_of_val_ne (by decide : (0 : ℕ) ≠ 1)
  let b := G.isSymmetric_walkEuclidean.eigenvectorBasis hm
  let a : ℝ := 𝔼 v, (b i₁).ofLp v
  let c : ℝ := 𝔼 v, (b i₀).ofLp v
  rcases eq_or_ne a 0 with ha | ha
  · refine G.le_secondEigenvalue_of_mul_norm_sq_le_inner (u := b i₁) (b.toBasis.ne_zero i₁) ha ?_
    rw [G.isSymmetric_walkEuclidean.apply_eigenvectorBasis hm i₁, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    exact le_rfl
  · let u : EuclideanSpace ℝ V := a • b i₀ - c • b i₁
    have hu_exp : 𝔼 v, u.ofLp v = 0 := by
      simp only [u, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, expect_sub_distrib, ← mul_expect]
      ring
    have hu_repr (i : Fin m) : (b.repr u).ofLp i = a * ⟪b i, b i₀⟫ - c * ⟪b i, b i₁⟫ := by
      rw [map_sub, map_smul, map_smul, WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_smul,
        Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        b.repr_apply_apply, b.repr_apply_apply]
    have hu_i₀ : (b.repr u).ofLp i₀ = a := by
      rw [hu_repr, real_inner_self_eq_norm_sq, b.orthonormal.1 i₀, b.orthonormal.2 hi₀₁]
      ring
    have hu_ne : u ≠ 0 := fun h0 ↦ ha (by simpa [h0] using hu_i₀.symm)
    refine G.le_secondEigenvalue_of_mul_norm_sq_le_inner hu_ne hu_exp ?_
    rw [inner_self_eq_sum_eigenvalues G.isSymmetric_walkEuclidean hm u,
      norm_sq_eq_sum_eigenvectorBasis_repr G.isSymmetric_walkEuclidean hm u, mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    rcases eq_or_ne i i₀ with rfl | hi0
    · exact mul_le_mul_of_nonneg_right
        (G.isSymmetric_walkEuclidean.eigenvalues_antitone hm (show i₀ ≤ i₁ from Nat.zero_le _))
        (sq_nonneg _)
    rcases eq_or_ne i i₁ with rfl | hi1
    · exact le_rfl
    · rw [hu_repr i, b.orthonormal.2 hi0, b.orthonormal.2 hi1]
      simp

/-- On at least two vertices and positive degree, the second largest eigenvalue of
`G.walkEuclidean` counted with multiplicity is `G.secondEigenvalue`. -/
theorem secondEigenvalue_eq_walkEuclidean_eigenvalues_one [Nonempty D] (hm1 : 1 < m) :
    G.secondEigenvalue = G.isSymmetric_walkEuclidean.eigenvalues hm ⟨1, hm1⟩ :=
  le_antisymm (G.secondEigenvalue_le_walkEuclidean_eigenvalues_one hm hm1)
    (G.walkEuclidean_eigenvalues_one_le_secondEigenvalue hm hm1)

end FullSpectrum

end Cslib.RotationMap
