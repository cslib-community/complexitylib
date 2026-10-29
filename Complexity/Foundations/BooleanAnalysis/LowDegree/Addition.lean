/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Foundations.LinearAlgebra.ImageSparsification
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Pulling low-degree functions back along XOR

Over a field of characteristic two, a monomial at `x + y` expands over partitions of its
coordinates between `x` and `y`. If its degree is at most `p + q + 1`, every term has degree at
most `p` in the first input or at most `q` in the second. Thus the pullback lies in a sum of two
slice spaces. The statement uses the existing function-space definition of low degree and the
general image-sparsification API; it does not restrict the degree of the Boolean predicates whose
accepting sets will later be sparsified.

## Main results

* `Cslib.BitString.bitVal_xor_of_char_two`: XOR becomes addition in characteristic two.
* `Cslib.BitString.monomial_add`: the squarefree expansion of a monomial at a sum.
* `Cslib.BitString.hasSliceDecomposition_add`: low-degree spaces satisfy the general pullback
  criterion for image sparsification.

## References

* The degree split is the polynomial-method step in [J. S. Ellenberg, *Sumsets as unions of
  sumsets of subsets*, proof of Theorem 1, pp. 2–3][Ellenberg2017Sumsets]. Here it is expressed
  as containment in fixed slice spaces, rather than only as a bound on each matrix's rank.
-/

public section

namespace Cslib.BitString

open Finset ImageSparsification

variable {K ι : Type*}

section CommRing

variable [CommRing K] [CharP K 2]

/-- Reading bits in characteristic two takes XOR to addition. -/
theorem bitVal_xor_of_char_two (a b : Bool) :
    bitVal K (a ^^ b) = bitVal K a + bitVal K b := by
  cases a <;> cases b <;> simp [CharTwo.add_self_eq_zero]

/-- Expanding a squarefree monomial at a sum partitions its coordinates between the inputs. -/
theorem monomial_add [DecidableEq ι] (S : Finset ι) (x y : ι → Bool) :
    monomial K S (x + y) =
      ∑ T ∈ S.powerset, monomial K T x * monomial K (S \ T) y := by
  simp only [monomial, Pi.add_apply, Bool.add_eq_xor, bitVal_xor_of_char_two]
  exact Finset.prod_add _ _ S

end CommRing

variable [Field K] [CharP K 2]

/-- A polynomial of degree at most `p + q + 1` at `x + y` is a sum of slices with first-input
degree at most `p` or second-input degree at most `q`. -/
theorem hasSliceDecomposition_add (p q : ℕ) :
    HasSliceDecomposition (fun x y : ι → Bool => x + y)
      (lowDegree K ι p) (lowDegree K ι q) (lowDegree K ι (p + q + 1)) := by
  classical
  have hrange : Set.range (fun S : {S : Finset ι // #S ≤ p + q + 1} => monomial K S.1) =
      monomial K '' {S | #S ≤ p + q + 1} := by
    ext f
    simp
  change HasSliceDecomposition _ _ _ (Submodule.span K (monomial K '' {S | #S ≤ p + q + 1}))
  rw [← hrange]
  apply hasSliceDecomposition_span
  intro S
  have hexpand : (fun x y : ι → Bool => monomial K S.1 (x + y)) =
      ∑ T ∈ S.1.powerset, (fun x y => monomial K T x * monomial K (S.1 \ T) y) := by
    funext x y
    simp only [Finset.sum_apply, monomial_add]
  rw [hexpand]
  apply (sliceSpace (lowDegree K ι p) (lowDegree K ι q)).sum_mem
  intro T hT
  by_cases hsmall : #T ≤ p
  · exact mul_mem_sliceSpace_left _ (monomial_mem_lowDegree hsmall) _
  · have hsub : T ⊆ S.1 := mem_powerset.mp hT
    have hcard := card_sdiff_add_card_eq_card hsub
    have hdegree := S.2
    exact mul_mem_sliceSpace_right _ _ (monomial_mem_lowDegree (by omega))

end Cslib.BitString
