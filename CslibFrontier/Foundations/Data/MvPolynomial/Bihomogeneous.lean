/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, bihomogeneous polynomials)

public import CslibFrontier.Foundations.Data.MvPolynomial.MixedOperator
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Bihomogeneous polynomials

Fix a set `s` of variables. The bidegree of a monomial is the pair of its degree in the variables
in `s` and its degree in the other variables. It is the weighted degree for the weight
`MvPolynomial.bidegWeight s` with values in `ℕ × ℕ`, so the polynomials of bidegree `(a, b)` are
the Mathlib submodule `weightedHomogeneousSubmodule R (bidegWeight s) (a, b)`. This is the space
`H_V(a) ⊗ H_U(b)` of [OpenAI, §2][OpenAI2026DepthFive], without a tensor product.

The slice of bidegree `(a, b)` has the monomials of that bidegree as a basis, so its dimension is
a product of two multiset coefficients. The operator `MvPolynomial.mixedOp s Q` of a polynomial
`Q` of bidegree `(i, j)` differentiates `i` times in `s` and multiplies by degree `j` outside
`s`, so it maps bidegree `(a + i, b)` to bidegree `(a, b + j)`. A homogeneous polynomial of
degree `e` is the sum of its components of bidegree `(i, e - i)`.

## Main definitions

* `MvPolynomial.bidegWeight`: the weight whose weighted degree is the bidegree.

## Main results

* `MvPolynomial.finrank_weightedHomogeneousSubmodule`: a weighted homogeneous slice has as
  many dimensions as there are monomials of that weight.
* `MvPolynomial.finrank_bihomogeneous`: the dimension of the slice of bidegree `(a, b)`.
* `MvPolynomial.mixedOp_mem_bihomogeneous`: the action of `mixedOp` on bidegrees.
* `MvPolynomial.IsHomogeneous.eq_sum_bidegree_component`: a homogeneous polynomial is the sum
  of its bihomogeneous components.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §2 (unrefereed preprint)
-/

@[expose] public section

open Finsupp

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

section Slice

variable {M : Type*} [AddCommMonoid M] (w : σ → M) (m : M)

/-- A weighted homogeneous slice has as many dimensions as there are monomials of that weight:
it is the span of these monomials, with Mathlib's basis `basisRestrictSupport`. -/
theorem finrank_weightedHomogeneousSubmodule [StrongRankCondition R] :
    Module.finrank R (weightedHomogeneousSubmodule R w m) =
      Nat.card {d : σ →₀ ℕ // weight w d = m} := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport R {d | weight w d = m})

end Slice

/-- Taking a weighted homogeneous component commutes with a change of coefficient ring. -/
theorem weightedHomogeneousComponent_map {S M : Type*} [CommSemiring S] [AddCommMonoid M]
    (w : σ → M) (m : M) (f : R →+* S) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w m (map f p) = map f (weightedHomogeneousComponent w m p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent, apply_ite f, map_zero]

variable (s : σ → Prop) [DecidablePred s]

/-- The weight whose weighted degree is the bidegree: the variables in `s` have weight `(1, 0)`
and the other variables have weight `(0, 1)`. -/
def bidegWeight (i : σ) : ℕ × ℕ := if s i then (1, 0) else (0, 1)

/-- The two components of the bidegree add up to the degree. -/
theorem weight_bidegWeight_fst_add_snd (d : σ →₀ ℕ) :
    (weight (bidegWeight s) d).1 + (weight (bidegWeight s) d).2 = d.degree := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, ← hf, ← hg]; simp only [Prod.fst_add, Prod.snd_add]; ring
  | single i n => by_cases h : s i <;> simp [weight_single, bidegWeight, h]

theorem weight_bidegWeight [Fintype σ] (d : σ →₀ ℕ) :
    weight (bidegWeight s) d =
      (∑ i with s i, d i, ∑ i with ¬ s i, d i) := by
  rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  ext
  · simp [Prod.fst_sum, bidegWeight, Finset.sum_filter, apply_ite]
  · simp [Prod.snd_sum, bidegWeight, Finset.sum_filter, apply_ite]

/-- The monomials of bidegree `(a, b)` are the pairs of a monomial of degree `a` in the variables
in `s` and a monomial of degree `b` in the other variables. -/
noncomputable def bidegreeEquiv [Fintype σ] [DecidableEq σ] (a b : ℕ) :
    {d : σ →₀ ℕ // weight (bidegWeight s) d = (a, b)} ≃
      (Finset.univ.filter s).finsuppAntidiag a ×
        (Finset.univ.filter (¬ s ·)).finsuppAntidiag b where
  toFun d :=
    (⟨d.1.filter s, Finset.mem_finsuppAntidiag.2
        ⟨(Finset.sum_congr rfl fun i hi => by
            simp [(Finset.mem_filter.1 hi).2]).trans
          (congrArg Prod.fst ((weight_bidegWeight s d.1).symm.trans d.2)),
        fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩⟩⟩,
      ⟨d.1.filter (¬ s ·), Finset.mem_finsuppAntidiag.2
        ⟨(Finset.sum_congr rfl fun i hi => by
            simp [(Finset.mem_filter.1 hi).2]).trans
          (congrArg Prod.snd ((weight_bidegWeight s d.1).symm.trans d.2)),
        fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩⟩⟩)
  invFun := fun (f, g) => ⟨f.1 + g.1, by
    have hf := Finset.mem_finsuppAntidiag.1 f.2
    have hg := Finset.mem_finsuppAntidiag.1 g.2
    have hf0 : ∀ i, ¬ s i → f.1 i = 0 := fun i hi => Classical.byContradiction fun h =>
      hi (Finset.mem_filter.1 (hf.2 (Finsupp.mem_support_iff.2 h))).2
    have hg0 : ∀ i, s i → g.1 i = 0 := fun i hi => Classical.byContradiction fun h =>
      (Finset.mem_filter.1 (hg.2 (Finsupp.mem_support_iff.2 h))).2 hi
    rw [weight_bidegWeight]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    rw [hf.1, hg.1, Finset.sum_eq_zero fun i hi => hg0 i (Finset.mem_filter.1 hi).2,
      Finset.sum_eq_zero fun i hi => hf0 i (Finset.mem_filter.1 hi).2, add_zero, zero_add]⟩
  left_inv d := Subtype.ext (Finsupp.filter_add_filter_not d.1 s)
  right_inv := fun (f, g) => by
    have hf := (Finset.mem_finsuppAntidiag.1 f.2).2
    have hg := (Finset.mem_finsuppAntidiag.1 g.2).2
    have hf' : f.1.filter s = f.1 := (Finsupp.filter_eq_self_iff _ _).2 fun i hi =>
      (Finset.mem_filter.1 (hf (Finsupp.mem_support_iff.2 hi))).2
    have hg' : g.1.filter (¬ s ·) = g.1 := (Finsupp.filter_eq_self_iff _ _).2 fun i hi =>
      (Finset.mem_filter.1 (hg (Finsupp.mem_support_iff.2 hi))).2
    have hf0 : f.1.filter (¬ s ·) = 0 := (Finsupp.filter_eq_zero_iff _ _).2 fun i hi =>
      Classical.byContradiction fun h =>
        hi (Finset.mem_filter.1 (hf (Finsupp.mem_support_iff.2 h))).2
    have hg0 : g.1.filter s = 0 := (Finsupp.filter_eq_zero_iff _ _).2 fun i hi =>
      Classical.byContradiction fun h =>
        (Finset.mem_filter.1 (hg (Finsupp.mem_support_iff.2 h))).2 hi
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
      simp [Finsupp.filter_add, hf', hg', hf0, hg0]

/-- In finitely many variables there are finitely many monomials of a given bidegree. -/
instance finite_bidegree [Finite σ] (ab : ℕ × ℕ) :
    Finite {d : σ →₀ ℕ // weight (bidegWeight s) d = ab} := by
  classical
  have := Fintype.ofFinite σ
  exact Finite.of_equiv _ (bidegreeEquiv s ab.1 ab.2).symm

/-- The dimension of the slice of bidegree `(a, b)`: the number of monomials of degree `a` in the
variables in `s`, times the number of monomials of degree `b` in the other variables. -/
theorem finrank_bihomogeneous [StrongRankCondition R] [Fintype σ] (a b : ℕ) :
    Module.finrank R (weightedHomogeneousSubmodule R (bidegWeight s) (a, b)) =
      Nat.multichoose (Fintype.card {i // s i}) a *
        Nat.multichoose (Fintype.card {i // ¬ s i}) b := by
  classical
  rw [finrank_weightedHomogeneousSubmodule, Nat.card_congr (bidegreeEquiv s a b), Nat.card_prod,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_finsuppAntidiag_nat_eq_multichoose,
    Fintype.card_subtype, Fintype.card_subtype]

/-- In finitely many variables the slice of bidegree `(a, b)` is finite-dimensional. -/
instance finite_bihomogeneous [Finite σ] (a b : ℕ) :
    Module.Finite R (weightedHomogeneousSubmodule R (bidegWeight s) (a, b)) := by
  classical
  have := Fintype.ofFinite σ
  have : Finite {d : σ →₀ ℕ // weight (bidegWeight s) d = (a, b)} :=
    Finite.of_equiv _ (bidegreeEquiv s a b).symm
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.of_basis (basisRestrictSupport R {d | weight (bidegWeight s) d = (a, b)})

variable {s}

private theorem mixedOp_monomial_mem (d : σ →₀ ℕ) : ∀ (a b : ℕ) (p : MvPolynomial σ R),
    p ∈ weightedHomogeneousSubmodule R (bidegWeight s)
      (a + (weight (bidegWeight s) d).1, b) →
    mixedOp s (monomial d 1) p ∈ weightedHomogeneousSubmodule R (bidegWeight s)
      (a, b + (weight (bidegWeight s) d).2) := by
  induction d using Finsupp.induction_linear with
  | zero => intro a b p hp; simpa using hp
  | add f g hf hg =>
    intro a b p hp
    have h : (monomial (f + g) 1 : MvPolynomial σ R) = monomial f 1 * monomial g 1 := by
      simp
    rw [h, map_mul, Module.End.mul_apply]
    rw [map_add, Prod.fst_add, ← add_assoc] at hp
    rw [map_add, Prod.snd_add, add_comm _ (weight (bidegWeight s) g).2, ← add_assoc]
    exact hf _ _ _ (hg _ _ _ hp)
  | single i n =>
    induction n with
    | zero => intro a b p hp; simpa using hp
    | succ n ih =>
      intro a b p hp
      have h : (monomial (single i (n + 1)) 1 : MvPolynomial σ R) =
          monomial (single i n) 1 * X i := by
        simp [X, ← single_add]
      rw [h, map_mul, Module.End.mul_apply]
      by_cases hi : s i
      · have hw : weight (bidegWeight s) (single i (n + 1)) = (n + 1, 0) := by
          simp [weight_single, bidegWeight, hi]
        have hw' : weight (bidegWeight s) (single i n) = (n, 0) := by
          simp [weight_single, bidegWeight, hi]
        rw [hw] at hp ⊢
        rw [mixedOp_X_of_pos hi]
        have := ih a b (pderiv i p) (by
          rw [hw']
          refine IsWeightedHomogeneous.pderiv hp ?_
          simp [bidegWeight, hi, add_assoc])
        rwa [hw'] at this
      · have hw : weight (bidegWeight s) (single i (n + 1)) = (0, n + 1) := by
          simp [weight_single, bidegWeight, hi]
        have hw' : weight (bidegWeight s) (single i n) = (0, n) := by
          simp [weight_single, bidegWeight, hi]
        rw [hw] at hp ⊢
        rw [mixedOp_X_of_neg hi]
        have := ih a (b + 1) (X i * p) (by
          rw [hw']
          have hX := (isWeightedHomogeneous_X (R := R) (bidegWeight s) i).mul hp
          simpa [bidegWeight, hi, add_comm] using hX)
        rwa [hw', add_assoc, add_comm 1 n] at this

/-- The operator of a polynomial of bidegree `(i, j)` maps bidegree `(a + i, b)` to bidegree
`(a, b + j)`: it differentiates `i` times in `s` and multiplies by degree `j` outside `s`. -/
theorem mixedOp_mem_bihomogeneous {Q p : MvPolynomial σ R} {i j a b : ℕ}
    (hQ : Q.IsWeightedHomogeneous (bidegWeight s) (i, j))
    (hp : p ∈ weightedHomogeneousSubmodule R (bidegWeight s) (a + i, b)) :
    mixedOp s Q p ∈ weightedHomogeneousSubmodule R (bidegWeight s) (a, b + j) := by
  rw [Q.as_sum, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd' := hQ (mem_support_iff.1 hd)
  rw [← mul_one (Q.coeff d), ← smul_eq_mul, ← smul_monomial, map_smul, LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := mixedOp_monomial_mem (s := s) d a b p (by rwa [hd'])
  rwa [hd'] at this

/-- A homogeneous polynomial of degree `e` is the sum of its components of bidegree
`(i, e - i)`. -/
theorem IsHomogeneous.eq_sum_bidegree_component {Q : MvPolynomial σ R} {e : ℕ}
    (hQ : Q.IsHomogeneous e) :
    Q = ∑ i ∈ Finset.range (e + 1),
      weightedHomogeneousComponent (bidegWeight s) (i, e - i) Q := by
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hd : Q.coeff d = 0
  · simp [hd]
  have he : (weight (bidegWeight s) d).1 + (weight (bidegWeight s) d).2 = e := by
    rw [weight_bidegWeight_fst_add_snd, ← hQ hd, degree_eq_weight_one]; rfl
  rw [Finset.sum_eq_single (weight (bidegWeight s) d).1]
  · have h : weight (bidegWeight s) d =
        ((weight (bidegWeight s) d).1, e - (weight (bidegWeight s) d).1) :=
      Prod.ext rfl (by change _ = e - _; omega)
    exact (ite_eq_left h).symm
  · intro i _ hi
    exact ite_eq_right fun h => hi (congrArg Prod.fst h).symm
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end MvPolynomial
