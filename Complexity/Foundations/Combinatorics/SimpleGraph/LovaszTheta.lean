/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/LovaszTheta.lean`)

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.SimpleGraph.ShannonCapacity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Complexity.Foundations.Combinatorics.SimpleGraph.CliqueCover

/-!
# The Lovász theta function

An *orthonormal representation* of a simple graph `G` on `V` is a family of unit vectors `u v`
in a real inner product space such that `u v ⟂ u w` whenever `v ≠ w` are nonadjacent. Lovász's
theta function is
`ϑ(G) = min_{u, c} max_v 1 / ⟪c, u v⟫²`,
over orthonormal representations `u` and unit vectors `c` (the *handle*) [Lovasz1979Shannon]; this
is the unweighted case of `ϑ₁` in Knuth's notes [Knuth1994, §5, (5.2)], whose *orthogonal labelings*
are orthonormal representations in this sense [Knuth1994, §1]. We define `ϑ(G)` as the infimum of
all `t > 0` such that `1 ≤ t ⟪c, u v⟫²` for every vertex `v`, for some orthonormal representation in
some `ℝᵈ` and a unit vector `c`; for each `(u, c)` these are exactly the `t ≥ max_v 1 / ⟪c, u v⟫²`.
So `lovaszTheta` is the infimum of the source's objective; that the infimum is attained (the
source's `min`) is not needed here and is not formalized. Representations in an arbitrary real
inner product space give the same bound (`SimpleGraph.lovaszTheta_le_of_rep`), by restricting to
the span of the finitely many vectors.

* **Lower bound** (`SimpleGraph.indepNum_le_lovaszTheta`): `α(G) ≤ ϑ(G)`. The vectors of an
  independent set are orthonormal, so Bessel's inequality bounds `∑ ⟪c, u v⟫²` over the set by
  `‖c‖² = 1` [Knuth1994, §1, Lemma].
* **Upper bound** (`SimpleGraph.lovaszTheta_le_of_colorable_compl`): if `Gᶜ` has a proper
  `k`-colouring, then `ϑ(G) ≤ k`. Map each vertex to the standard basis vector of its colour and
  take the handle `c = (1, …, 1) / √k`. Together with the lower bound this is the
  *sandwich theorem* `α(G) ≤ ϑ(G) ≤ χ(Gᶜ)` [Knuth1994, §4, (4.9)].
* **Strong products** (`SimpleGraph.lovaszTheta_strongProd_le`): `ϑ(G ⊠ H) ≤ ϑ(G) ϑ(H)`. The
  tensor products `u v ⊗ w v'` form an orthonormal representation of `G ⊠ H` with handle
  `c ⊗ c'` [Lovasz1979Shannon], [Knuth1994, §20, Lemma].
* **Shannon capacity** (`SimpleGraph.shannonCapacity_le_lovaszTheta`): `Θ(G) ≤ ϑ(G)`, since
  `α(Gᵏ) ≤ ϑ(Gᵏ) ≤ ϑ(G)ᵏ` [Lovasz1979Shannon].

The theta function can be computed to any precision in polynomial time by semidefinite
programming or the ellipsoid method [Knuth1994]; that algorithmic statement is not formalized here.

## Main definitions

* `SimpleGraph.IsOrthonormalRepresentation`: unit vectors, orthogonal on nonadjacent pairs.
* `SimpleGraph.lovaszTheta`: the Lovász theta function `ϑ(G)`.

## Main results

* `SimpleGraph.indepNum_le_lovaszTheta`, `SimpleGraph.lovaszTheta_le_chromaticNumber_compl`: the
  sandwich theorem; `SimpleGraph.lovaszTheta_le_of_cliqueCover` states the upper half for a
  cover by cliques, as in [Knuth1994, §4, (4.9)].
* `SimpleGraph.lovaszTheta_strongProd_le`, `SimpleGraph.lovaszTheta_strongPow_le`:
  submultiplicativity.
* `SimpleGraph.shannonCapacity_le_lovaszTheta`: Lovász's bound `Θ(G) ≤ ϑ(G)`.

## References

* [D. E. Knuth, *The sandwich theorem*][Knuth1994]
* [L. Lovász, *On the Shannon capacity of a graph*][Lovasz1979Shannon]
-/

public section

open scoped RealInnerProductSpace TensorProduct

namespace SimpleGraph

variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- An **orthonormal representation** of `G`: unit vectors `u v` with `u v ⟂ u w` whenever
`v ≠ w` are not adjacent in `G`. -/
structure IsOrthonormalRepresentation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : SimpleGraph V) (u : V → E) : Prop where
  norm_eq_one : ∀ v, ‖u v‖ = 1
  inner_eq_zero : ∀ ⦃v w⦄, v ≠ w → ¬G.Adj v w → ⟪u v, u w⟫ = 0

/-- The **Lovász theta function** `ϑ(G)`: the infimum of the `t > 0` for which some orthonormal
representation `u` of `G` in some `ℝᵈ` and some unit vector `c` satisfy `1 ≤ t ⟪c, u v⟫²` for
every vertex `v`, that is, `ϑ(G) = inf_{u, c} max_v 1 / ⟪c, u v⟫²`. -/
noncomputable def lovaszTheta (G : SimpleGraph V) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : V → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)),
    G.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2}

theorem lovaszTheta_nonneg : 0 ≤ G.lovaszTheta :=
  Real.sInf_nonneg fun _ ht => ht.1.le

private theorem bddBelow_feasible :
    BddBelow {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : V → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      G.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2} :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- Restricting an orthonormal representation of `G` along an embedding `G' ↪g G`. -/
theorem IsOrthonormalRepresentation.comp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : V → E} (hu : G.IsOrthonormalRepresentation u)
    {G' : SimpleGraph X} (f : G' ↪g G) : G'.IsOrthonormalRepresentation (u ∘ f) where
  norm_eq_one v := hu.norm_eq_one (f v)
  inner_eq_zero _ _ hvw hadj :=
    hu.inner_eq_zero (fun h => hvw (f.injective h)) fun h => hadj (f.map_adj_iff.1 h)

theorem IsOrthonormalRepresentation.map {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {u : V → E}
    (hu : G.IsOrthonormalRepresentation u) (L : E →ₗᵢ[ℝ] F) :
    G.IsOrthonormalRepresentation (L ∘ u) where
  norm_eq_one v := by simp [hu.norm_eq_one v]
  inner_eq_zero _ _ hvw hadj := by simp [hu.inner_eq_zero hvw hadj]

/-- Tensor products of orthonormal representations of `G` and `H` represent `G ⊠ H`. -/
theorem IsOrthonormalRepresentation.tmul {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {u : V → E}
    {w : W → F} (hu : G.IsOrthonormalRepresentation u) (hw : H.IsOrthonormalRepresentation w) :
    (G ⊠ H).IsOrthonormalRepresentation (fun x => u x.1 ⊗ₜ[ℝ] w x.2) where
  norm_eq_one x := by rw [TensorProduct.norm_tmul, hu.norm_eq_one, hw.norm_eq_one, one_mul]
  inner_eq_zero x y hxy hadj := by
    rw [TensorProduct.inner_tmul]
    simp only [strongProd_adj, hxy, ne_eq, not_false_eq_true, true_and, not_and_or,
      not_or] at hadj
    rcases hadj with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [hu.inner_eq_zero h₁ h₂, zero_mul]
    · rw [hw.inner_eq_zero h₁ h₂, mul_zero]

/-- Any orthonormal representation `u` of a finite graph, in any real inner product space, with
a unit handle `c` and `1 ≤ t ⟪c, u v⟫²` for all `v`, bounds `ϑ(G) ≤ t`. -/
theorem lovaszTheta_le_of_rep [Finite V] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : V → E} (hu : G.IsOrthonormalRepresentation u) {c : E}
    (hc : ‖c‖ = 1) {t : ℝ} (ht : 0 < t) (h : ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2) :
    G.lovaszTheta ≤ t := by
  refine csInf_le bddBelow_feasible ⟨ht, ?_⟩
  let S : Submodule ℝ E := Submodule.span ℝ (insert c (Set.range u))
  have : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range u).insert c)
  have huS (v : V) : u v ∈ S := Submodule.subset_span (Set.mem_insert_of_mem _ ⟨v, rfl⟩)
  let b := stdOrthonormalBasis ℝ S
  let u' : V → S := fun v => ⟨u v, huS v⟩
  let c' : S := ⟨c, Submodule.subset_span (Set.mem_insert _ _)⟩
  have hu' : G.IsOrthonormalRepresentation u' :=
    ⟨fun v => hu.norm_eq_one v, fun _ _ hvw hadj => hu.inner_eq_zero hvw hadj⟩
  refine ⟨_, b.repr ∘ u', b.repr c', hu'.map b.repr.toLinearIsometry, ?_, fun v => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact hc
  · rw [Function.comp_apply, LinearIsometryEquiv.inner_map_map]
    exact h v

/-- Bessel's inequality bound: an orthonormal representation with handle `c` and
`1 ≤ t ⟪c, u v⟫²` for all `v` bounds `α(G) ≤ t`. -/
theorem indepNum_le_of_rep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : V → E} (hu : G.IsOrthonormalRepresentation u) {c : E} (hc : ‖c‖ = 1) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2) : (G.indepNum : ℝ) ≤ t := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have horth : Orthonormal ℝ (fun v : s => u v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, hv⟩ ⟨w, hw⟩
    by_cases hvw : v = w
    · subst hvw
      simp only [↓reduceIte, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · have hne : (⟨v, hv⟩ : s) ≠ ⟨w, hw⟩ := fun h => hvw (congrArg Subtype.val h)
      simp only [hne, ↓reduceIte]
      exact hu.inner_eq_zero hvw (hs.isIndepSet hv hw hvw)
  have hB := horth.sum_inner_products_le (s := Finset.univ) c
  simp only [Real.norm_eq_abs, sq_abs, hc, one_pow] at hB
  rw [← hs.card_eq]
  calc (s.card : ℝ) = ∑ v : s, (1 : ℝ) := by simp
    _ ≤ ∑ v : s, t * ⟪u v, c⟫ ^ 2 := by
      gcongr with v
      rw [real_inner_comm]
      exact h v
    _ = t * ∑ v : s, ⟪u v, c⟫ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ t * 1 := by gcongr
    _ = t := mul_one t

/-- A proper `k`-colouring of `Gᶜ` (`k > 0`) gives a feasible point `k`: colour classes are
cliques of `G`, and the standard basis vector of each colour with the handle `(1, …, 1) / √k` is an
orthonormal representation with `⟪c, u v⟫² = 1 / k`. -/
private theorem mem_feasible_of_colorable_compl {k : ℕ} (hk : 0 < k) (hc : Gᶜ.Colorable k) :
    (k : ℝ) ∈ {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : V → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      G.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2} := by
  obtain ⟨C⟩ := hc
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨hk', k, fun v => EuclideanSpace.single (C v) 1,
    WithLp.toLp 2 fun _ => (√(k : ℝ))⁻¹, ⟨fun v => by simp, fun v w hvw hadj => ?_⟩, ?_,
    fun v => ?_⟩
  · have hne : C v ≠ C w := C.valid (by simp [compl_adj, hvw, hadj])
    rw [EuclideanSpace.inner_single_left]
    simp [hne.symm]
  · rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hk'.le, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ hk'.ne', Real.sqrt_one]
  · rw [EuclideanSpace.inner_single_right]
    simp [mul_inv_cancel₀ hk'.ne']

private theorem nonempty_feasible [Finite V] :
    {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : V → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      G.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2}.Nonempty := by
  have := Fintype.ofFinite V
  exact ⟨_, mem_feasible_of_colorable_compl (Nat.succ_pos (Fintype.card V))
    (Gᶜ.colorable_of_fintype.mono (Nat.le_succ _))⟩

theorem lovaszTheta_eq_zero_of_isEmpty [IsEmpty V] : G.lovaszTheta = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) lovaszTheta_nonneg
  rw [zero_add]
  exact csInf_le bddBelow_feasible ⟨hε, 1, isEmptyElim, EuclideanSpace.single 0 1,
    ⟨isEmptyElim, fun v => isEmptyElim v⟩, by simp, isEmptyElim⟩

/-- **Sandwich theorem, upper half**: a proper `k`-colouring of the complement bounds
`ϑ(G) ≤ k`. -/
theorem lovaszTheta_le_of_colorable_compl {k : ℕ} (hc : Gᶜ.Colorable k) : G.lovaszTheta ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := colorable_zero_iff.1 hc
    rw [lovaszTheta_eq_zero_of_isEmpty, Nat.cast_zero]
  · exact csInf_le bddBelow_feasible (mem_feasible_of_colorable_compl hk hc)

/-- **Sandwich theorem, upper half**: `ϑ(G) ≤ χ(Gᶜ)`. -/
theorem lovaszTheta_le_chromaticNumber_compl [Finite V] :
    G.lovaszTheta ≤ (Gᶜ.chromaticNumber.toNat : ℝ) :=
  lovaszTheta_le_of_colorable_compl Gᶜ.colorable_chromaticNumber_of_fintype

/-- **Sandwich theorem, upper half, clique-cover form**: if the vertices are covered by the cliques
of `G` in `S`, then `ϑ(G) ≤ #S`. The colour classes of a colouring of `Gᶜ` are such cliques
(`SimpleGraph.exists_cliqueCover_iff_colorable_compl`). -/
theorem lovaszTheta_le_of_cliqueCover [Finite V] {S : Finset (Finset V)}
    (hS : ∀ s ∈ S, G.IsClique (s : Set V)) (hcover : ∀ v, ∃ s ∈ S, v ∈ s) :
    G.lovaszTheta ≤ S.card :=
  lovaszTheta_le_of_colorable_compl
    (exists_cliqueCover_iff_colorable_compl.1 ⟨S, le_rfl, hS, hcover⟩)

theorem lovaszTheta_le_natCard [Finite V] : G.lovaszTheta ≤ Nat.card V := by
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  exact lovaszTheta_le_of_colorable_compl Gᶜ.colorable_of_fintype

/-- **Sandwich theorem, lower half**: `α(G) ≤ ϑ(G)`. -/
theorem indepNum_le_lovaszTheta [Finite V] : (G.indepNum : ℝ) ≤ G.lovaszTheta := by
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [indepNum_eq_zero_of_isEmpty, Nat.cast_zero]
    exact lovaszTheta_nonneg
  · refine le_csInf nonempty_feasible ?_
    rintro t ⟨ht, d, u, c, hu, hc, h⟩
    exact indepNum_le_of_rep hu hc ht.le h

theorem lovaszTheta_pos [Finite V] [Nonempty V] : 0 < G.lovaszTheta :=
  lt_of_lt_of_le (by exact_mod_cast one_le_indepNum) indepNum_le_lovaszTheta

/-- The theta function is monotone under graph embeddings. -/
theorem Embedding.lovaszTheta_le [Finite V] {G' : SimpleGraph X} (f : G' ↪g G) :
    G'.lovaszTheta ≤ G.lovaszTheta := by
  have : Finite X := Finite.of_injective f f.injective
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [lovaszTheta_eq_zero_of_isEmpty]
    exact lovaszTheta_nonneg
  refine le_csInf nonempty_feasible ?_
  rintro t ⟨ht, d, u, c, hu, hc, h⟩
  exact lovaszTheta_le_of_rep (hu.comp f) hc ht fun v => h (f v)

/-- The theta function is invariant under graph isomorphisms. -/
theorem Iso.lovaszTheta_eq [Finite V] [Finite W] (e : G ≃g H) : G.lovaszTheta = H.lovaszTheta :=
  le_antisymm e.toEmbedding.lovaszTheta_le e.symm.toEmbedding.lovaszTheta_le

/-- **Submultiplicativity** of the theta function under the strong product:
`ϑ(G ⊠ H) ≤ ϑ(G) ϑ(H)`. -/
theorem lovaszTheta_strongProd_le [Finite V] [Finite W] :
    (G ⊠ H).lovaszTheta ≤ G.lovaszTheta * H.lovaszTheta := by
  rcases isEmpty_or_nonempty V with hV | hV
  · rw [lovaszTheta_eq_zero_of_isEmpty, lovaszTheta_eq_zero_of_isEmpty, zero_mul]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [lovaszTheta_eq_zero_of_isEmpty, lovaszTheta_eq_zero_of_isEmpty (G := H), mul_zero]
  -- feasible points multiply, via tensor products of representations and handles
  have key : ∀ t t', t ∈ {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : V → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      G.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2} →
      t' ∈ {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : W → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      H.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2} →
      (G ⊠ H).lovaszTheta ≤ t * t' := by
    rintro t t' ⟨ht, d, u, c, hu, hc, h⟩ ⟨ht', d', w, c', hw, hc', h'⟩
    refine lovaszTheta_le_of_rep (hu.tmul hw) (c := c ⊗ₜ[ℝ] c')
      (by rw [TensorProduct.norm_tmul, hc, hc', one_mul]) (mul_pos ht ht') fun x => ?_
    rw [TensorProduct.inner_tmul, mul_pow]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ (t * ⟪c, u x.1⟫ ^ 2) * (t' * ⟪c', w x.2⟫ ^ 2) :=
          mul_le_mul (h x.1) (h' x.2) zero_le_one (zero_le_one.trans (h x.1))
      _ = t * t' * (⟪c, u x.1⟫ ^ 2 * ⟪c', w x.2⟫ ^ 2) := by ring
  have hG := G.lovaszTheta_pos
  have h₁ : ∀ t', t' ∈ {t : ℝ | 0 < t ∧ ∃ (d : ℕ) (u : W → EuclideanSpace ℝ (Fin d))
      (c : EuclideanSpace ℝ (Fin d)),
      H.IsOrthonormalRepresentation u ∧ ‖c‖ = 1 ∧ ∀ v, 1 ≤ t * ⟪c, u v⟫ ^ 2} →
      (G ⊠ H).lovaszTheta ≤ G.lovaszTheta * t' := by
    intro t' ht'
    have : (G ⊠ H).lovaszTheta / t' ≤ G.lovaszTheta := by
      refine le_csInf nonempty_feasible fun t ht => ?_
      rw [div_le_iff₀ ht'.1]
      exact key t t' ht ht'
    rwa [div_le_iff₀ ht'.1] at this
  have : (G ⊠ H).lovaszTheta / G.lovaszTheta ≤ H.lovaszTheta := by
    refine le_csInf nonempty_feasible fun t' ht' => ?_
    rw [div_le_iff₀ hG, mul_comm]
    exact h₁ t' ht'
  rwa [div_le_iff₀ hG, mul_comm] at this

theorem lovaszTheta_strongPow_zero_le : (G.strongPow 0).lovaszTheta ≤ 1 :=
  lovaszTheta_le_of_rep (u := fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    ⟨fun _ => by simp, fun x y hxy => absurd (Subsingleton.elim x y) hxy⟩
    (c := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (by simp) one_pos fun _ => by simp

/-- `ϑ(Gᵏ) ≤ ϑ(G)ᵏ` for the strong powers. -/
theorem lovaszTheta_strongPow_le [Finite V] (k : ℕ) :
    (G.strongPow k).lovaszTheta ≤ G.lovaszTheta ^ k := by
  induction k with
  | zero => simpa using lovaszTheta_strongPow_zero_le
  | succ k ih =>
    rw [(G.strongPowAddIso k 1).lovaszTheta_eq, pow_succ]
    calc (G.strongPow k ⊠ G.strongPow 1).lovaszTheta
        ≤ (G.strongPow k).lovaszTheta * (G.strongPow 1).lovaszTheta := lovaszTheta_strongProd_le
      _ ≤ G.lovaszTheta ^ k * G.lovaszTheta := by
        rw [G.strongPowOneIso.lovaszTheta_eq]
        exact mul_le_mul_of_nonneg_right ih lovaszTheta_nonneg

/-- **Lovász's bound on the Shannon capacity**: `Θ(G) ≤ ϑ(G)`. -/
theorem shannonCapacity_le_lovaszTheta [Finite V] : G.shannonCapacity ≤ G.lovaszTheta :=
  shannonCapacity_le fun k =>
    (indepNum_le_lovaszTheta (G := G.strongPow (k + 1))).trans (lovaszTheta_strongPow_le _)

end SimpleGraph
