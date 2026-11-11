/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/PiecewiseQuadratic.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.Polyhedra.PiecewiseLinear
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Piecewise-quadratic functions on compact polyhedra

This file develops real-valued quadratic functions on subsets of real vector spaces and
piecewise-quadratic (PQ) functions on compact polyhedra in the style of [RourkeSanderson1982].

## Main definitions

* `Cslib.Polyhedra.IsQuadraticOn`: `f : E → ℝ` agrees on `S` with a finite sum of products of
  pairs of real-valued affine maps.
* `Cslib.Polyhedra.IsPQOn`: `f : E → ℝ` is piecewise-quadratic on a compact polyhedron `P` if `P`
  is the space of a finite polytopal complex on every cell of which `f` is quadratic.

## Main results

* `Cslib.Polyhedra.isQuadraticOn_iff_quadraticMap_add_affineMap`: on finite-dimensional spaces,
  `IsQuadraticOn` agrees with `QuadraticMap + AffineMap`.
* `Cslib.Polyhedra.isQuadraticOn_iff_mvPolynomial_basis`: with respect to a finite basis,
  `IsQuadraticOn` is equivalent to agreement with an `MvPolynomial` of `totalDegree ≤ 2`.
* Closure of `IsPQOn` under restriction, finite closed covers, piecewise union, real linear
  combinations, products of PL functions (`IsPQOn.mul_of_isPLOn`), and precomposition with PL
  maps (`IsPQOn.comp_isPLOn`).
* `Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial`,
  `Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial_pi`, and
  `Cslib.Polyhedra.IsPQOn.exists_triangulation_mvPolynomial_basis`: finite cell lists and
  triangulations on whose cells a PQ function equals an `MvPolynomial` of `totalDegree ≤ 2`.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
* Issue #4325 notes (`STOC 1056 Lemma 3.1` label; unverified against the primary manuscript).
-/

public section

open scoped BigOperators
open Set

namespace Cslib.Polyhedra

section BasicQuadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `f : E → ℝ` is **quadratic on `S`** (meaning a polynomial of total degree at most
`2`) if it agrees on `S` with a finite sum of products of pairs of real-valued affine maps. -/
@[expose] def IsQuadraticOn (f : E → ℝ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → E →ᵃ[ℝ] ℝ),
    Set.EqOn f (fun x => ∑ i, a i x * b i x) S

theorem IsQuadraticOn.congr {f f' : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S)
    (heq : Set.EqOn f' f S) : IsQuadraticOn f' S := by
  rcases hf with ⟨n, a, b, h⟩
  exact ⟨n, a, b, heq.trans h⟩

theorem IsQuadraticOn.mono {f : E → ℝ} {S T : Set E} (hf : IsQuadraticOn f S)
    (hTS : T ⊆ S) : IsQuadraticOn f T := by
  rcases hf with ⟨n, a, b, h⟩
  exact ⟨n, a, b, h.mono hTS⟩

theorem IsQuadraticOn.of_isAffineOn {f : E → ℝ} {S : Set E} (hf : IsAffineOn f S) :
    IsQuadraticOn f S := by
  rcases hf with ⟨g, hg⟩
  refine ⟨1, fun _ => g, fun _ => AffineMap.const ℝ E 1, fun x hx => ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    AffineMap.const_apply, mul_one]
  exact hg hx

theorem IsQuadraticOn.affineMap (g : E →ᵃ[ℝ] ℝ) (S : Set E) : IsQuadraticOn g S :=
  IsQuadraticOn.of_isAffineOn (IsAffineOn.affineMap g S)

theorem IsQuadraticOn.const (S : Set E) (c : ℝ) : IsQuadraticOn (fun _ => c) S :=
  IsQuadraticOn.of_isAffineOn (IsAffineOn.const S c)

theorem IsQuadraticOn.add {f g : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) (hg : IsQuadraticOn g S) :
    IsQuadraticOn (fun x => f x + g x) S := by
  rcases hf with ⟨n₁, a₁, b₁, hf'⟩
  rcases hg with ⟨n₂, a₂, b₂, hg'⟩
  refine ⟨n₁ + n₂, Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, fun x hx => ?_⟩
  dsimp only
  rw [hf' hx, hg' hx, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]

theorem IsQuadraticOn.neg {f : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S) :
    IsQuadraticOn (fun x => -f x) S := by
  rcases hf with ⟨n, a, b, hf'⟩
  refine ⟨n, fun i => -(a i), b, fun x hx => ?_⟩
  simp only [hf' hx, AffineMap.coe_neg, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem IsQuadraticOn.sub {f g : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) (hg : IsQuadraticOn g S) :
    IsQuadraticOn (fun x => f x - g x) S :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsQuadraticOn.smul (c : ℝ) {f : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S) :
    IsQuadraticOn (fun x => c * f x) S := by
  rcases hf with ⟨n, a, b, hf'⟩
  refine ⟨n, fun i => c • a i, b, fun x hx => ?_⟩
  simp only [hf' hx, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem IsQuadraticOn.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {S : Set E}
    (hf : ∀ i ∈ s, IsQuadraticOn (f i) S) :
    IsQuadraticOn (fun x => ∑ i ∈ s, f i x) S := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact (IsQuadraticOn.const S 0).congr fun _ _ => Finset.sum_empty
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr fun _ _ => Finset.sum_insert ha

theorem IsQuadraticOn.mul_of_isAffineOn {f g : E → ℝ} {S : Set E}
    (hf : IsAffineOn f S) (hg : IsAffineOn g S) :
    IsQuadraticOn (fun x => f x * g x) S := by
  rcases hf with ⟨af, haf⟩
  rcases hg with ⟨ag, hag⟩
  refine ⟨1, fun _ => af, fun _ => ag, fun x hx => ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    haf hx, hag hx]

theorem IsQuadraticOn.comp_affineMap {g : F → ℝ} {T : Set F}
    (hg : IsQuadraticOn g T) (a : E →ᵃ[ℝ] F) {S : Set E} (hmaps : MapsTo a S T) :
    IsQuadraticOn (g ∘ a) S := by
  rcases hg with ⟨n, u, v, hu⟩
  refine ⟨n, fun i => (u i).comp a, fun i => (v i).comp a, fun x hx => ?_⟩
  simp only [Function.comp_apply, AffineMap.coe_comp]
  exact hu (hmaps hx)

end BasicQuadratic

section PolynomialAndQuadraticMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsQuadraticOn.continuousOn [FiniteDimensional ℝ E] {f : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) : ContinuousOn f S := by
  rcases hf with ⟨n, a, b, h⟩
  have hcont : ContinuousOn (fun x => ∑ i : Fin n, a i x * b i x) S :=
    continuousOn_finsetSum Finset.univ fun i _ =>
      ((a i).continuous_of_finiteDimensional.mul
        (b i).continuous_of_finiteDimensional).continuousOn
  exact hcont.congr h

private lemma isQuadraticOn_of_quadraticMap [FiniteDimensional ℝ E]
    (Q : QuadraticMap ℝ E ℝ) (S : Set E) : IsQuadraticOn Q S := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hQB : ∀ x, Q x = (1 / 2 : ℝ) * B x x := fun x => by
    have h1 := hB x x
    have h2 : Q (x + x) = (4 : ℝ) * Q x := by
      have hx2 : x + x = (2 : ℝ) • x := (two_smul ℝ x).symm
      rw [hx2, Q.map_smul, smul_eq_mul]
      ring
    linarith
  let b := Module.finBasis ℝ E
  refine IsQuadraticOn.congr (IsQuadraticOn.sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (f := fun i x => ∑ j : Fin (Module.finrank ℝ E),
      (((1 / 2 : ℝ) * B (b j) (b i)) • (b.coord i).toAffineMap) x * (b.coord j).toAffineMap x)
    fun i _ => IsQuadraticOn.sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (f := fun j x =>
        (((1 / 2 : ℝ) * B (b j) (b i)) • (b.coord i).toAffineMap) x * (b.coord j).toAffineMap x)
      fun j _ => IsQuadraticOn.mul_of_isAffineOn
        (IsAffineOn.affineMap (((1 / 2 : ℝ) * B (b j) (b i)) • (b.coord i).toAffineMap) S)
        (IsAffineOn.affineMap (b.coord j).toAffineMap S)) ?_
  intro x _
  rw [hQB x]
  have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    AffineMap.coe_smul, LinearMap.coe_toAffineMap, Module.Basis.coord_apply,
    Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- On a finite-dimensional real normed space, `IsQuadraticOn f S` holds if and only if `f` agrees
on `S` with the sum of a `QuadraticMap` and an `AffineMap`. -/
theorem isQuadraticOn_iff_quadraticMap_add_affineMap [FiniteDimensional ℝ E]
    {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔
      ∃ (Q : QuadraticMap ℝ E ℝ) (L : E →ᵃ[ℝ] ℝ), Set.EqOn f (fun x => Q x + L x) S := by
  constructor
  · rintro ⟨n, a, b, hf⟩
    let B : LinearMap.BilinMap ℝ E ℝ :=
      { toFun := fun x =>
          { toFun := fun y => ∑ i : Fin n, (a i).linear x * (b i).linear y
            map_add' := fun y₁ y₂ => by
              simp only [map_add, mul_add, Finset.sum_add_distrib]
            map_smul' := fun c y => by
              simp only [map_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring }
        map_add' := fun x₁ x₂ => by
          ext y
          simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, add_mul, Finset.sum_add_distrib,
            LinearMap.add_apply]
        map_smul' := fun c x => by
          ext y
          simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, smul_eq_mul, RingHom.id_apply,
            LinearMap.smul_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring }
    let Llin : E →ₗ[ℝ] ℝ :=
      ∑ i : Fin n, (b i 0 • (a i).linear + a i 0 • (b i).linear)
    let L : E →ᵃ[ℝ] ℝ := Llin.toAffineMap + AffineMap.const ℝ E (∑ i : Fin n, a i 0 * b i 0)
    refine ⟨B.toQuadraticMap, L, fun x hx => ?_⟩
    rw [hf hx]
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, AffineMap.const_apply, B, L, Llin]
    rw [← add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun (AffineMap.decomp (a i)) x, congrFun (AffineMap.decomp (b i)) x]
    simp only [Pi.add_apply]
    ring
  · rintro ⟨Q, L, hQL⟩
    exact ((isQuadraticOn_of_quadraticMap Q S).add (IsQuadraticOn.affineMap L S)).congr hQL

private lemma finsupp_peel_one {ι : Type*} {m : ι →₀ ℕ} (hm0 : m ≠ 0) :
    ∃ i, Finsupp.single i 1 ≤ m ∧
      m = Finsupp.single i 1 + (m - Finsupp.single i 1) ∧
      m.sum (fun _ k => k) = 1 + (m - Finsupp.single i 1).sum (fun _ k => k) := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hm0
  have him : 1 ≤ m i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi))
  have hle : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.2 him
  have hadd : Finsupp.single i 1 + (m - Finsupp.single i 1) = m := by
    ext k
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    exact Nat.add_sub_of_le (hle k)
  have hsum : m.sum (fun _ k => k) = 1 + (m - Finsupp.single i 1).sum (fun _ k => k) := by
    have hsub := congr_arg (fun f : ι →₀ ℕ => f.sum fun _ k => k) hadd.symm
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      at hsub
    exact hsub
  exact ⟨i, hle, hadd.symm, hsum⟩

private lemma finsupp_sum_le_two {ι : Type*} {m : ι →₀ ℕ}
    (hm : m.sum (fun _ k => k) ≤ 2) :
    m = 0 ∨ (∃ i, m = Finsupp.single i 1) ∨
      (∃ i j, m = Finsupp.single i 1 + Finsupp.single j 1) := by
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · obtain ⟨i, _, hm_eq, hsum1⟩ := finsupp_peel_one hm0
    set m' := m - Finsupp.single i 1
    have hm'le : m'.sum (fun _ k => k) ≤ 1 := by linarith
    by_cases hm'0 : m' = 0
    · exact Or.inr (Or.inl ⟨i, by rw [hm_eq, hm'0, add_zero]⟩)
    · obtain ⟨j, _, hm'_eq, hsum2⟩ := finsupp_peel_one hm'0
      set m'' := m' - Finsupp.single j 1
      have hm''0 : m'' = 0 := by
        ext k
        by_contra hk
        have hpos : 0 < m'' k := Nat.pos_of_ne_zero hk
        have hle : m'' k ≤ m''.sum fun _ r => r :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.2 hk)
        linarith
      exact Or.inr (Or.inr ⟨i, j, by rw [hm_eq, hm'_eq, hm''0, add_zero]⟩)

private lemma affineMap_eq_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) (a : E →ᵃ[ℝ] ℝ) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 1 ∧
      ∀ x, MvPolynomial.eval (e.equivFun x) p = a x := by
  classical
  let := Fintype.ofFinite ι
  let p : MvPolynomial ι ℝ :=
    (∑ i : ι, MvPolynomial.C (a.linear (e i)) * MvPolynomial.X i) + MvPolynomial.C (a 0)
  refine ⟨p, ?_, fun x => ?_⟩
  · refine (MvPolynomial.totalDegree_add _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, Nat.max_zero]
    refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  · simp only [p, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Module.Basis.equivFun_apply]
    have hx : x = ∑ i, e.repr x i • e i := (e.sum_repr x).symm
    conv_rhs => rw [congrFun (AffineMap.decomp a) x, hx]
    simp only [Pi.add_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- On a finite-dimensional real normed space equipped with a finite basis `e`, `f` is quadratic on
`S` if and only if it agrees on `S` with a multivariate polynomial of `totalDegree ≤ 2` in the
`e`-coordinates. -/
theorem isQuadraticOn_iff_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) p) S := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨n, a, b, hf⟩
    choose pa hpa hpa_eq using fun i => affineMap_eq_mvPolynomial_basis e (a i)
    choose pb hpb hpb_eq using fun i => affineMap_eq_mvPolynomial_basis e (b i)
    refine ⟨∑ i : Fin n, pa i * pb i, ?_, fun x hx => ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hpa i) (hpb i))
    · rw [hf hx]
      simp only [map_sum, map_mul, hpa_eq, hpb_eq]
  · rintro ⟨p, hp, hpf⟩
    refine IsQuadraticOn.congr (IsQuadraticOn.sum p.support
      (f := fun m x => MvPolynomial.eval (e.equivFun x) (MvPolynomial.monomial m (p.coeff m)))
      fun m hm => ?_) ?_
    · have hmdeg : m.sum (fun _ k => k) ≤ 2 :=
        (Finset.le_sup (f := fun s : ι →₀ ℕ => s.sum fun _ k => k) hm).trans hp
      rcases finsupp_sum_le_two hmdeg with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
      · refine (IsQuadraticOn.const S (p.coeff 0)).congr fun x _ => ?_
        rw [← MvPolynomial.C_apply, MvPolynomial.eval_C]
      · refine (IsQuadraticOn.affineMap
          (p.coeff (Finsupp.single i 1) • (e.coord i).toAffineMap) S).congr fun x _ => ?_
        have hmon : MvPolynomial.monomial (Finsupp.single i 1) (p.coeff (Finsupp.single i 1)) =
            MvPolynomial.C (p.coeff (Finsupp.single i 1)) * MvPolynomial.X i := by
          rw [MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one]
        rw [hmon, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
        simp only [AffineMap.coe_smul, Pi.smul_apply, LinearMap.coe_toAffineMap,
          Module.Basis.coord_apply, smul_eq_mul, Module.Basis.equivFun_apply]
      · refine (IsQuadraticOn.mul_of_isAffineOn
          (IsAffineOn.affineMap
            (p.coeff (Finsupp.single i 1 + Finsupp.single j 1) • (e.coord i).toAffineMap) S)
          (IsAffineOn.affineMap (e.coord j).toAffineMap S)).congr fun x _ => ?_
        have hmon :
            MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1)
                (p.coeff (Finsupp.single i 1 + Finsupp.single j 1)) =
              MvPolynomial.C (p.coeff (Finsupp.single i 1 + Finsupp.single j 1)) *
                MvPolynomial.X i * MvPolynomial.X j := by
          rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one,
            MvPolynomial.monomial_mul_monomial, mul_one]
        rw [hmon, map_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_X]
        simp only [AffineMap.coe_smul, Pi.smul_apply, LinearMap.coe_toAffineMap,
          Module.Basis.coord_apply, smul_eq_mul, Module.Basis.equivFun_apply]
    · intro x hx
      rw [hpf hx]
      conv_lhs => rw [p.as_sum]
      simp only [map_sum]

/-- Variant of `isQuadraticOn_iff_mvPolynomial_basis` using `Module.finBasis ℝ E`. -/
theorem isQuadraticOn_iff_mvPolynomial [FiniteDimensional ℝ E] {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval ((Module.finBasis ℝ E).equivFun x) p) S :=
  isQuadraticOn_iff_mvPolynomial_basis (Module.finBasis ℝ E)

/-- On `Fin d → ℝ`, `IsQuadraticOn f S` is equivalent to agreeing on `S` with an
`MvPolynomial (Fin d) ℝ` of `totalDegree ≤ 2`. -/
theorem isQuadraticOn_iff_mvPolynomial_pi {d : ℕ} {f : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval x p) S :=
  isQuadraticOn_iff_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

end PolynomialAndQuadraticMap

section GeneralPQ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function `f : E → ℝ` is **piecewise-quadratic on `P`** (`IsPQOn P f`) if `P` is a compact
polyhedron admitted as the space of a finite polytopal complex on every cell of which `f` agrees
with a polynomial of degree at most `2`. -/
@[expose] def IsPQOn (P : Set E) (f : E → ℝ) : Prop :=
  IsPiecewiseOn IsQuadraticOn P f

theorem IsPQOn.congr {P : Set E} {f f' : E → ℝ} (hf : IsPQOn P f) (heq : Set.EqOn f' f P) :
    IsPQOn P f' :=
  isPiecewiseOn_congr (fun heq hq => hq.congr heq) hf heq

theorem IsPQOn.of_isPLOn {P : Set E} {f : E → ℝ} (hf : IsPLOn P f) : IsPQOn P f := by
  rcases hf with ⟨C, hC, haff⟩
  exact ⟨C, hC, fun Q hQ => IsQuadraticOn.of_isAffineOn (haff Q hQ)⟩

theorem IsPQOn.neg {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : IsPQOn P (fun x => -f x) := by
  rcases hf with ⟨C, hC, hquad⟩
  exact ⟨C, hC, fun Q hQ => (hquad Q hQ).neg⟩

theorem IsPQOn.smul (c : ℝ) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    IsPQOn P (fun x => c * f x) := by
  rcases hf with ⟨C, hC, hquad⟩
  exact ⟨C, hC, fun Q hQ => (hquad Q hQ).smul c⟩

theorem isPQOn_empty (f : E → ℝ) : IsPQOn (∅ : Set E) f :=
  isPiecewiseOn_empty IsQuadraticOn f

end GeneralPQ

section FiniteDimPQ

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPQOn.isPolyhedron {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : IsPolyhedron P :=
  let ⟨C, hC, _⟩ := hf
  isPolyhedron_iff_exists_polytopalComplex.2 ⟨C, hC⟩

theorem isPQOn_iff_simplicialComplex {P : Set E} {f : E → ℝ} :
    IsPQOn P f ↔ ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ s ∈ K.faces, IsQuadraticOn f (convexHull ℝ (s : Set E)) :=
  isPiecewiseOn_iff_simplicialComplex (fun hsub hq => hq.mono hsub)

theorem isPQOn_iff_finite_polytope_cover {P : Set E} {f : E → ℝ} :
    IsPQOn P f ↔ ∃ ℱ : Set (Set E), ℱ.Finite ∧
      (∀ Q ∈ ℱ, IsPolytope Q ∧ IsQuadraticOn f Q) ∧ P = ⋃ Q ∈ ℱ, Q :=
  isPiecewiseOn_iff_finite_polytope_cover (fun hsub hq => hq.mono hsub)

theorem IsPQOn.affineMap {P : Set E} (hP : IsPolyhedron P) (g : E →ᵃ[ℝ] ℝ) : IsPQOn P g :=
  IsPQOn.of_isPLOn (IsPLOn.affineMap hP g)

theorem IsPQOn.const {P : Set E} (hP : IsPolyhedron P) (c : ℝ) : IsPQOn P (fun _ => c) :=
  IsPQOn.of_isPLOn (IsPLOn.const hP c)

theorem IsPQOn.quadraticMap {P : Set E} (hP : IsPolyhedron P) (Q : QuadraticMap ℝ E ℝ) :
    IsPQOn P Q := by
  obtain ⟨C, hC⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  exact ⟨C, hC, fun R _ => isQuadraticOn_of_quadraticMap Q R⟩

theorem IsPQOn.continuousOn {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : ContinuousOn f P :=
  isPiecewiseOn_continuousOn (fun h => h.continuousOn) hf

theorem IsPQOn.of_finiteCover {ι : Type*} [Finite ι] {P : Set E} {Q : ι → Set E}
    {f : E → ℝ} (hcov : (⋃ i, Q i) = P) (hf : ∀ i, IsPQOn (Q i) f) : IsPQOn P f :=
  isPiecewiseOn_of_finiteCover (fun hsub hq => hq.mono hsub) hcov hf

open Classical in
theorem IsPQOn.piecewise_union {P Q : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn Q g)
    (hagree : ∀ x ∈ P ∩ Q, f x = g x) :
    IsPQOn (P ∪ Q) (fun x => if x ∈ P then f x else g x) :=
  isPiecewiseOn_piecewise_union (fun hsub hq => hq.mono hsub)
    (fun heq hq => hq.congr heq) hf hg hagree

theorem IsPQOn.restrict {P Q : Set E} {f : E → ℝ} (hf : IsPQOn P f)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) : IsPQOn Q f :=
  isPiecewiseOn_restrict (fun hsub hq => hq.mono hsub) hf hQ hQP

theorem IsPQOn.exists_common_complex {P : Set E} {f g : E → ℝ}
    (hf : IsPQOn P f) (hg : IsPQOn P g) :
    ∃ C : PolytopalComplex E, C.space = P ∧
      (∀ Q ∈ C.cells, IsQuadraticOn f Q) ∧ (∀ Q ∈ C.cells, IsQuadraticOn g Q) :=
  isPiecewiseOn_exists_common_complex (fun hsub hu => hu.mono hsub)
    (fun hsub hv => hv.mono hsub) hf hg

theorem IsPQOn.add {P : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn P g) :
    IsPQOn P (fun x => f x + g x) := by
  obtain ⟨C, hC, hqf, hqg⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ => (hqf Q hQ).add (hqg Q hQ)⟩

theorem IsPQOn.sub {P : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn P g) :
    IsPQOn P (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsPQOn.sum {ι : Type*} (s : Finset ι) {P : Set E} (hP : IsPolyhedron P)
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPQOn P (f i)) :
    IsPQOn P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => exact (IsPQOn.const hP 0).congr fun _ _ => Finset.sum_empty
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr fun _ _ => Finset.sum_insert ha

/-- The pointwise product of two real-valued PL functions on `P` is PQ on `P` (cited in issue #4325
notes as `STOC 1056 Lemma 3.1`, unverified against the primary manuscript). -/
theorem IsPQOn.mul_of_isPLOn {P : Set E} {f g : E → ℝ}
    (hf : IsPLOn P f) (hg : IsPLOn P g) : IsPQOn P (fun x => f x * g x) := by
  obtain ⟨C, hC, haff_f, haff_g⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ =>
    IsQuadraticOn.mul_of_isAffineOn (haff_f Q hQ) (haff_g Q hQ)⟩

/-- Any finite sum of pairwise products of real-valued PL functions on `P` is PQ on `P`. -/
theorem IsPQOn.sum_mul_of_isPLOn {ι : Type*} (s : Finset ι) {P : Set E} (hP : IsPolyhedron P)
    {f g : ι → E → ℝ} (hf : ∀ i ∈ s, IsPLOn P (f i)) (hg : ∀ i ∈ s, IsPLOn P (g i)) :
    IsPQOn P (fun x => ∑ i ∈ s, f i x * g i x) :=
  IsPQOn.sum s hP fun i hi => IsPQOn.mul_of_isPLOn (hf i hi) (hg i hi)

/-- Precomposing a PQ map with a PL map preserves piecewise-quadraticity. -/
theorem IsPQOn.comp_isPLOn [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {T : Set F} {f : E → F} {g : F → ℝ}
    (hf : IsPLOn P f) (hg : IsPQOn T g) (hmaps : MapsTo f P T) :
    IsPQOn P (g ∘ f) := by
  rcases hg with ⟨CT, hCT, hq_g⟩
  obtain ⟨D, hDsp, hDcell⟩ := hf.exists_preimage_complex CT
  have hsp : D.space = P := by
    rw [hDsp, hCT]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hmaps hx⟩⟩
  refine ⟨D, hsp, fun S hS => ?_⟩
  obtain ⟨⟨a, ha⟩, R, hR, hsubR⟩ := hDcell S hS
  have hcomp : IsQuadraticOn (g ∘ a) S :=
    (hq_g R hR).comp_affineMap a fun x hx => hsubR ⟨x, hx, ha hx⟩
  exact hcomp.congr fun x hx => by simp only [Function.comp_apply, ha hx]

/-- Every PQ function admits a finite triangulation on each simplex of which it agrees with an
`MvPolynomial` of `totalDegree ≤ 2` in the coordinates of a given basis `e`. -/
theorem IsPQOn.exists_triangulation_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∃ p : Finset E → MvPolynomial ι ℝ,
        ∀ s ∈ K.faces, (p s).totalDegree ≤ 2 ∧
          Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) (p s))
            (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨K, hfin, hsp, hquad⟩ := isPQOn_iff_simplicialComplex.1 hf
  have hpoly : ∀ s : Finset E, ∃ p : MvPolynomial ι ℝ,
      s ∈ K.faces → p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) p) (convexHull ℝ (s : Set E)) := by
    intro s
    by_cases hs : s ∈ K.faces
    · obtain ⟨p, hp, heq⟩ := (isQuadraticOn_iff_mvPolynomial_basis e).1 (hquad s hs)
      exact ⟨p, fun _ => ⟨hp, heq⟩⟩
    · exact ⟨0, fun h => False.elim (hs h)⟩
  choose p hp using hpoly
  exact ⟨K, hfin, hsp, p, fun s hs => hp s hs⟩

/-- Specialization of `IsPQOn.exists_triangulation_mvPolynomial_basis` to `Fin d → ℝ`. -/
theorem IsPQOn.exists_triangulation_mvPolynomial_pi {d : ℕ} {P : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hf : IsPQOn P f) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin d → ℝ), K.faces.Finite ∧ K.space = P ∧
      ∃ p : Finset (Fin d → ℝ) → MvPolynomial (Fin d) ℝ,
        ∀ s ∈ K.faces, (p s).totalDegree ≤ 2 ∧
          Set.EqOn f (fun x => MvPolynomial.eval x (p s))
            (convexHull ℝ (s : Set (Fin d → ℝ))) :=
  hf.exists_triangulation_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

/-- Every PQ function on `P` can be presented as a finite list of convex polytope cells covering
`P` together with a multivariate polynomial of `totalDegree ≤ 2` (in coordinates of basis `e`)
matching `f` on each cell. -/
theorem IsPQOn.exists_cell_list_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × MvPolynomial ι ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P := by
  classical
  obtain ⟨K, hfin, hsp, p, hp⟩ := hf.exists_triangulation_mvPolynomial_basis e
  refine ⟨hfin.toFinset.toList.map (fun s : Finset E => (convexHull ℝ (s : Set E), p s)), ?_, ?_⟩
  · intro S q hSq
    rw [List.mem_map] at hSq
    rcases hSq with ⟨s, hs, hpair⟩
    have hmem : s ∈ K.faces := hfin.mem_toFinset.1 (Finset.mem_toList.1 hs)
    rcases Prod.ext_iff.1 hpair with ⟨rfl, rfl⟩
    exact ⟨isPolytope_convexHull s.finite_toSet, (hp s hmem).1, (hp s hmem).2⟩
  · rw [← hsp]
    ext x
    simp only [Geometry.SimplicialComplex.space, Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨S, ⟨⟨S', q'⟩, hmem, rfl⟩, hx⟩
      rcases hmem with ⟨s, hs, hpair⟩
      have hmem' : s ∈ K.faces := hfin.mem_toFinset.1 (Finset.mem_toList.1 hs)
      rcases Prod.ext_iff.1 hpair with ⟨rfl, _⟩
      exact ⟨s, hmem', hx⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨convexHull ℝ (s : Set E),
        ⟨(convexHull ℝ (s : Set E), p s), ⟨s, Finset.mem_toList.2 (hfin.mem_toFinset.2 hs), rfl⟩,
          rfl⟩, hx⟩

/-- Specialization of `IsPQOn.exists_cell_list_mvPolynomial_basis` to `Module.finBasis ℝ E`. -/
theorem IsPQOn.exists_cell_list_mvPolynomial {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × MvPolynomial (Fin (Module.finrank ℝ E)) ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval ((Module.finBasis ℝ E).equivFun x) p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P :=
  hf.exists_cell_list_mvPolynomial_basis (Module.finBasis ℝ E)

/-- On `Fin d → ℝ`, every PQ function on `P` admits a finite list of convex polytope cells
covering `P` on each of which `f` agrees with an `MvPolynomial (Fin d) ℝ` of `totalDegree ≤ 2`. -/
theorem IsPQOn.exists_cell_list_mvPolynomial_pi {d : ℕ} {P : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set (Fin d → ℝ) × MvPolynomial (Fin d) ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval x p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P :=
  hf.exists_cell_list_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

/-- Coordinate-free finite cell list for a PQ function: a finite list of polytopes covering `P`
together with pairs `(Q, L)` of a `QuadraticMap` and an `AffineMap` agreeing with `f` on each
cell. -/
theorem IsPQOn.exists_cell_list_quadraticMap {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × QuadraticMap ℝ E ℝ × (E →ᵃ[ℝ] ℝ)),
      (∀ S Q L', (S, Q, L') ∈ L → IsPolytope S ∧ Set.EqOn f (fun x => Q x + L' x) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P := by
  classical
  rcases hf with ⟨C, hC, hquad⟩
  have hcell : ∀ S : Set E, ∃ QL : QuadraticMap ℝ E ℝ × (E →ᵃ[ℝ] ℝ),
      S ∈ C.cells → Set.EqOn f (fun x => QL.1 x + QL.2 x) S := by
    intro S
    by_cases hS : S ∈ C.cells
    · obtain ⟨Q, L', hQL⟩ := isQuadraticOn_iff_quadraticMap_add_affineMap.1 (hquad S hS)
      exact ⟨(Q, L'), fun _ => hQL⟩
    · exact ⟨((0 : QuadraticMap ℝ E ℝ), AffineMap.const ℝ E (0 : ℝ)), fun h => False.elim (hS h)⟩
  choose ql hql using hcell
  refine ⟨C.finite_cells.toFinset.toList.map (fun S : Set E => (S, ql S)), ?_, ?_⟩
  · intro S Q L' hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨S₀, hS₀, hpair⟩
    have hSC : S₀ ∈ C.cells := C.finite_cells.mem_toFinset.1 (Finset.mem_toList.1 hS₀)
    rcases Prod.ext_iff.1 hpair with ⟨rfl, hQL'⟩
    have hQ : Q = (ql S₀).1 := congr_arg Prod.fst hQL'.symm
    have hL' : L' = (ql S₀).2 := congr_arg Prod.snd hQL'.symm
    subst hQ; subst hL'
    exact ⟨C.isPolytope_of_mem hSC, hql S₀ hSC⟩
  · rw [← hC]
    ext x
    simp only [PolytopalComplex.mem_space_iff, Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨S, ⟨⟨S', ql'⟩, hmem, rfl⟩, hx⟩
      rcases hmem with ⟨S₀, hS₀, hpair⟩
      have hSC : S₀ ∈ C.cells := C.finite_cells.mem_toFinset.1 (Finset.mem_toList.1 hS₀)
      rcases Prod.ext_iff.1 hpair with ⟨rfl, _⟩
      exact ⟨S₀, hSC, hx⟩
    · rintro ⟨S₀, hS₀, hx⟩
      exact ⟨S₀,
        ⟨(S₀, ql S₀), ⟨S₀, Finset.mem_toList.2 (C.finite_cells.mem_toFinset.2 hS₀), rfl⟩, rfl⟩,
        hx⟩

end FiniteDimPQ

end Cslib.Polyhedra
