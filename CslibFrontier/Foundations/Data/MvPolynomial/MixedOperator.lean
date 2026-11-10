/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, polynomials acting by differentiation and multiplication)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# Polynomials acting by differentiation and multiplication

Fix a set `s` of variables. A polynomial `Q` acts on polynomials by substituting the partial
derivative `∂ᵢ` for each variable `i` in `s` and multiplication by `X j` for each variable `j`
outside `s`. These operators commute, since `∂ᵢ (X j * p) = X j * ∂ᵢ p` for `i ≠ j`, so the
substitution is an algebra homomorphism `MvPolynomial.mixedOp s` into the endomorphisms of the
polynomial ring. In particular the operator of a product is the composition of the operators of
its factors.

For `s` empty this is multiplication by `Q`, and for `s` everything it is the differential
operator `Q(∂)` of apolarity. The mixed form is the operator `g(∂_V, U)` of
[OpenAI, §2][OpenAI2026DepthFive], whose rank on a slice of the polynomial ring is a complexity
measure for homogeneous depth-five circuits.

## Main definitions

* `MvPolynomial.mixedGen`: the operator of a single variable.
* `MvPolynomial.mixedOp`: the algebra homomorphism `Q ↦ Q(∂_s, X_{sᶜ})`.

## Main results

* `MvPolynomial.commute_mixedGen`: the operators of two variables commute.
* `MvPolynomial.mixedOp_map`: the action commutes with a change of coefficient ring.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §2 (unrefereed preprint)
-/

@[expose] public section

namespace MvPolynomial

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] (s : σ → Prop) [DecidablePred s]

/-- The operator of the variable `i`: the partial derivative `∂ᵢ` if `i` is in `s`, and
multiplication by `X i` otherwise. -/
noncomputable def mixedGen (i : σ) : Module.End R (MvPolynomial σ R) :=
  if s i then (pderiv i).toLinearMap else LinearMap.mulLeft R (X i)

variable {s} in
theorem mixedGen_of_pos {i : σ} (h : s i) (p : MvPolynomial σ R) :
    mixedGen s i p = pderiv i p := by
  simp [mixedGen, h]

variable {s} in
theorem mixedGen_of_neg {i : σ} (h : ¬ s i) (p : MvPolynomial σ R) :
    mixedGen s i p = X i * p := by
  simp [mixedGen, h]

/-- The operators of two variables commute. -/
theorem commute_mixedGen (i j : σ) : Commute (mixedGen (R := R) s i) (mixedGen s j) := by
  refine LinearMap.ext fun p => ?_
  by_cases hi : s i <;> by_cases hj : s j
  · simpa [mixedGen, hi, hj] using commute_pderiv (R := R) i j p
  · have hij : j ≠ i := fun h => hj (h ▸ hi)
    simp [mixedGen, hi, hj, pderiv_X_of_ne hij]
  · have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp [mixedGen, hi, hj, pderiv_X_of_ne hij]
  · simp [mixedGen, hi, hj, mul_left_comm]

/-- A commutative subalgebra containing the operators of all variables: the double centralizer
of the set of these operators. -/
noncomputable def mixedSubalgebra : Subalgebra R (Module.End R (MvPolynomial σ R)) :=
  Subalgebra.centralizer R (Subalgebra.centralizer R (Set.range (mixedGen (R := R) s)) : Set _)

theorem mixedGen_mem (i : σ) : mixedGen (R := R) s i ∈ mixedSubalgebra (R := R) s :=
  fun _ hx => (hx _ ⟨i, rfl⟩).symm

theorem mixedSubalgebra_le :
    mixedSubalgebra (R := R) s ≤ Subalgebra.centralizer R (Set.range (mixedGen (R := R) s)) := by
  refine Subalgebra.centralizer_le R _ _ ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact commute_mixedGen s j i

noncomputable instance : CommSemiring (mixedSubalgebra (R := R) s) where
  mul_comm a b := Subtype.ext (b.2 a (mixedSubalgebra_le s a.2))

/-- The action of a polynomial `Q` on polynomials, with `∂ᵢ` substituted for the variables `i`
in `s` and multiplication by `X j` for the variables `j` outside `s`. -/
noncomputable def mixedOp : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  (mixedSubalgebra s).val.comp (aeval fun i => ⟨mixedGen s i, mixedGen_mem s i⟩)

@[simp]
theorem mixedOp_X (i : σ) : mixedOp (R := R) s (X i) = mixedGen s i := by
  simp [mixedOp]

variable {s} in
theorem mixedOp_X_of_pos {i : σ} (h : s i) (p : MvPolynomial σ R) :
    mixedOp s (X i) p = pderiv i p := by
  rw [mixedOp_X, mixedGen_of_pos h]

variable {s} in
theorem mixedOp_X_of_neg {i : σ} (h : ¬ s i) (p : MvPolynomial σ R) :
    mixedOp s (X i) p = X i * p := by
  rw [mixedOp_X, mixedGen_of_neg h]

@[simp]
theorem mixedOp_C (c : R) (p : MvPolynomial σ R) : mixedOp s (C c) p = c • p := by
  rw [← algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The action commutes with a change of coefficient ring. -/
theorem mixedOp_map (f : R →+* S) (Q p : MvPolynomial σ R) :
    map f (mixedOp s Q p) = mixedOp s (map f Q) (map f p) := by
  induction Q using MvPolynomial.induction_on generalizing p with
  | C a => simp [smul_eq_C_mul]
  | add Q₁ Q₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X Q i h =>
    simp only [map_mul, Module.End.mul_apply, map_X, h]
    by_cases hi : s i
    · rw [mixedOp_X_of_pos hi, mixedOp_X_of_pos hi, pderiv_map]
    · rw [mixedOp_X_of_neg hi, mixedOp_X_of_neg hi, map_mul, map_X]

end MvPolynomial
