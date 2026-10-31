/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, iterated partial derivatives and their span)

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Spaces of partial derivatives

`MvPolynomial.iteratedPDeriv α` differentiates along each variable of the tuple `α` in turn, and
`MvPolynomial.partialDerivatives k p` sends a coefficient vector `c` to `∑ α, c α • ∂_α p`, the sum
running over all `k`-tuples of variables. Its range is the span of the `k`-th order partial
derivatives of `p` (`MvPolynomial.range_partialDerivatives`), so its rank is their dimension.
This is the order-`k` measure `Γ_k` of [Kayal and Saptharishi, §5.2][KayalSaptharishi2014]. It
refines the measure of Nisan and Wigderson, the dimension of the span of the partial derivatives
of all orders [Nisan and Wigderson, §3][NisanWigderson1996]. The map is linear in `p`, so the
measure is subadditive, and renaming the variables along an injection does not decrease it.

Every partial derivative of a product of affine forms is a combination of products of fewer of
the same forms: differentiating once removes one factor and leaves its coefficient. So the
`k`-th order partial derivatives of a product of `d` affine forms lie in the span of the
`choose d k` products omitting `k` of the factors. This is the order-`k` form of
[Nisan and Wigderson, Lemma 3][NisanWigderson1996], which bounds the all-orders measure of such a
product by `2 ^ d`, and it is a claim in the chapter "Lower bounds for depth-3 circuits" of
[Saptharishi's survey][Saptharishi2026Survey]. It holds in every characteristic.

## Main definitions

* `MvPolynomial.iteratedPDeriv`: the iterated partial derivative along a tuple of variables.
* `MvPolynomial.partialDerivatives`: the `k`-th order partial derivatives as a linear map.

## Main results

* `MvPolynomial.range_partialDerivatives`: the range is the span of the partial derivatives.
* `MvPolynomial.rank_partialDerivatives_le_rename`: renaming variables injectively does not
  decrease the measure.
* `MvPolynomial.rank_partialDerivatives_prod_le`: for a product of `d` affine forms, the
  `k`-th order partial derivatives span at most `choose d k` dimensions.

## References

* [N. Nisan, A. Wigderson, *Lower bounds on arithmetic circuits via partial
  derivatives*][NisanWigderson1996], §3 and Lemma 3
* [N. Kayal, R. Saptharishi, *A selection of lower bounds for arithmetic
  circuits*][KayalSaptharishi2014], §5.2
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey]
-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {R : Type u} {σ : Type v} [CommSemiring R]

/-- The iterated partial derivative `∂_{α 0} ∘ ⋯ ∘ ∂_{α (k - 1)}`. -/
noncomputable def iteratedPDeriv : {k : ℕ} → (Fin k → σ) → Module.End R (MvPolynomial σ R)
  | 0, _ => 1
  | _ + 1, α => (pderiv (α 0)).toLinearMap * iteratedPDeriv (Fin.tail α)

@[simp] theorem iteratedPDeriv_zero (α : Fin 0 → σ) : iteratedPDeriv (R := R) α = 1 := rfl

theorem iteratedPDeriv_succ_apply {k : ℕ} (α : Fin (k + 1) → σ) (p : MvPolynomial σ R) :
    iteratedPDeriv α p = pderiv (α 0) (iteratedPDeriv (Fin.tail α) p) := rfl

section

variable {K : Type*} [Field K]

/-- The partial derivative of a product of polynomials with constant partial derivatives is a
combination of the products omitting one factor. -/
private theorem pderiv_prod_mem_span {d : ℕ} (ℓ : Fin d → MvPolynomial σ K)
    (hℓ : ∀ i v, ∃ c, pderiv v (ℓ i) = C c) (v : σ) (S : Finset (Fin d)) :
    pderiv v (∏ i ∈ S, ℓ i) ∈
      Submodule.span K ((fun j => ∏ i ∈ S.erase j, ℓ i) '' (S : Set (Fin d))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    obtain ⟨c, hc⟩ := hℓ a v
    rw [Finset.prod_insert ha, Derivation.leibniz, hc, smul_eq_mul, smul_eq_mul,
      mul_comm _ (C c), ← smul_eq_C_mul]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨a, by simp, by simp [Finset.erase_insert ha]⟩))
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.mulLeft K (ℓ a)) ih
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have hja : j ≠ a := fun h => ha (h ▸ hj)
    refine ⟨j, by simp [hj], ?_⟩
    dsimp only [LinearMap.mulLeft_apply]
    rw [Finset.erase_insert_of_ne hja.symm,
      Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h)]

/-- The `j`-th order partial derivatives of the product over `Tᶜ` lie in the span of the
products over the complements of `(#T + j)`-sets. -/
private theorem iteratedPDeriv_prod_mem_span {d : ℕ} (ℓ : Fin d → MvPolynomial σ K)
    (hℓ : ∀ i v, ∃ c, pderiv v (ℓ i) = C c) (j : ℕ) (β : Fin j → σ) (T : Finset (Fin d)) :
    iteratedPDeriv β (∏ i ∈ Finset.univ \ T, ℓ i) ∈ Submodule.span K
      ((fun T' => ∏ i ∈ Finset.univ \ T', ℓ i) ''
        ((Finset.powersetCard (T.card + j) Finset.univ : Finset (Finset (Fin d))) :
          Set (Finset (Fin d)))) := by
  classical
  induction j with
  | zero => exact Submodule.subset_span ⟨T, by simp, rfl⟩
  | succ j ih =>
    rw [iteratedPDeriv_succ_apply]
    have hmap := Submodule.mem_map_of_mem (f := (pderiv (β 0)).toLinearMap) (ih (Fin.tail β))
    rw [Submodule.map_span] at hmap
    refine (Submodule.span_le.mpr ?_) hmap
    rintro _ ⟨_, ⟨T', hT', rfl⟩, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hT'
    refine Submodule.span_mono ?_ (pderiv_prod_mem_span ℓ hℓ (β 0) (Finset.univ \ T'))
    rintro _ ⟨i, hi, rfl⟩
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi
    refine ⟨insert i T', ?_, by dsimp only; rw [Finset.sdiff_insert]⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard, Finset.card_insert_of_notMem hi.2, hT'.2]
    exact ⟨Finset.subset_univ _, by omega⟩

private theorem iteratedPDeriv_rename {τ : Type v} {f : σ → τ} (hf : Function.Injective f) {k : ℕ}
    (α : Fin k → σ) (p : MvPolynomial σ K) :
    iteratedPDeriv (f ∘ α) (rename f p) = rename f (iteratedPDeriv α p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedPDeriv_succ_apply, iteratedPDeriv_succ_apply]
    exact (congrArg (pderiv (f (α 0))) (ih (Fin.tail α))).trans (pderiv_rename hf _ _)

end

variable [Fintype σ]

/-- The `k`-th order partial derivatives of `p`, combined linearly: `c ↦ ∑ α, c α • ∂_α p`. Its
range is their span (`MvPolynomial.range_partialDerivatives`), and its rank their dimension. -/
noncomputable def partialDerivatives (k : ℕ) :
    MvPolynomial σ R →ₗ[R] ((Fin k → σ) → R) →ₗ[R] MvPolynomial σ R where
  toFun p := Fintype.linearCombination R fun α => iteratedPDeriv α p
  map_add' p q := LinearMap.ext fun c => by
    simp [Fintype.linearCombination_apply, Finset.sum_add_distrib]
  map_smul' r p := LinearMap.ext fun c => by
    simp [Fintype.linearCombination_apply, Finset.smul_sum, smul_comm r]

theorem partialDerivatives_apply (k : ℕ) (p : MvPolynomial σ R) :
    partialDerivatives k p = Fintype.linearCombination R fun α => iteratedPDeriv α p := rfl

/-- The range of `partialDerivatives k p` is the span of the `k`-th order partial derivatives. -/
theorem range_partialDerivatives (k : ℕ) (p : MvPolynomial σ R) :
    LinearMap.range (partialDerivatives k p) =
      Submodule.span R (Set.range fun α : Fin k → σ => iteratedPDeriv α p) :=
  Fintype.range_linearCombination R _

variable {K : Type*} [Field K]

/-- Renaming the variables along an injection does not decrease the partial-derivative
measure. -/
theorem rank_partialDerivatives_le_rename {τ : Type v} [Fintype τ] {f : σ → τ}
    (hf : Function.Injective f) (k : ℕ) (p : MvPolynomial σ K) :
    (partialDerivatives k p).rank ≤ (partialDerivatives k (rename f p)).rank := by
  rw [LinearMap.rank, LinearMap.rank, ← rank_map_eq (f := (rename f).toLinearMap)
    (rename_injective f hf)]
  refine Submodule.rank_mono ?_
  rw [range_partialDerivatives, range_partialDerivatives, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨α, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨f ∘ α, iteratedPDeriv_rename hf α p⟩

/-- The `k`-th order partial derivatives of a product of `d` affine forms span at most
`choose d k` dimensions: the order-`k` form of
[Nisan and Wigderson, Lemma 3][NisanWigderson1996]. -/
theorem rank_partialDerivatives_prod_le {d : ℕ} (a : Fin d → σ → K) (b : Fin d → K) (k : ℕ) :
    (partialDerivatives k (∏ i, (∑ v, a i v • X v + C (b i)))).rank ≤ d.choose k := by
  classical
  set ℓ : Fin d → MvPolynomial σ K := fun i => ∑ v, a i v • X v + C (b i)
  have hℓ : ∀ i v, ∃ c, pderiv v (ℓ i) = C c := fun i v =>
    ⟨a i v, by simp [ℓ, pderiv_X, Pi.single_apply, smul_eq_C_mul]⟩
  set s := (Finset.powersetCard k Finset.univ).image fun T => ∏ i ∈ Finset.univ \ T, ℓ i
  have hrange : LinearMap.range (partialDerivatives k (∏ i, ℓ i)) ≤
      Submodule.span K (s : Set (MvPolynomial σ K)) := by
    rw [range_partialDerivatives, Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    simpa [s] using iteratedPDeriv_prod_mem_span ℓ hℓ k α ∅
  calc (partialDerivatives k (∏ i, ℓ i)).rank
      ≤ Module.rank K (Submodule.span K (s : Set (MvPolynomial σ K))) :=
        Submodule.rank_mono hrange
    _ ≤ s.card := rank_span_finset_le s
    _ ≤ d.choose k := by
        exact_mod_cast Finset.card_image_le.trans (by simp)

end MvPolynomial
