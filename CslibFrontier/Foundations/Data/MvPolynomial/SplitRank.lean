/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# The rank of a polynomial across a split of its variables

For a set `U` of variables, a polynomial `f` has *split rank at most `w` across `U`*
(`MvPolynomial.SplitRankLE U w f`) if it is a sum of `w` products `p * q` with `p` a polynomial in
the variables of `U` and `q` a polynomial in the other variables. Over a field this says that the
matrix of coefficients of `f`, with rows indexed by the monomials in `U` and columns by the
monomials in the complement, has rank at most `w`; by Nisan's characterisation a
polynomial computed by a read-once oblivious branching program of width `w` in an order that reads
`U` first has this property. The decomposition form is the one used here: it is preserved by every
substitution that keeps the two sets of variables apart, with no matrix in sight.

## Main definitions

* `MvPolynomial.SplitRankLE`: a decomposition into `w` products across a split of the variables.

## Main results

* `MvPolynomial.aeval_congr_of_mem_supported`: a substitution into a polynomial in the variables
  of `s` depends only on the values on `s`.
* `MvPolynomial.SplitRankLE.shift`: shifting the variables preserves the split rank.
* `MvPolynomial.aeval_mem_of_mem_supported`: such a substitution lands in a subalgebra that
  contains the values on `s`.
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- `f` is a sum of `w` products of a polynomial in the variables of `U` and a polynomial in the
other variables. -/
def SplitRankLE (U : Set σ) (w : ℕ) (f : MvPolynomial σ R) : Prop :=
  ∃ p q : Fin w → MvPolynomial σ R,
    (∀ i, p i ∈ supported R U) ∧ (∀ i, q i ∈ supported R Uᶜ) ∧ f = ∑ i, p i * q i

section Supported

variable {A : Type*} [CommSemiring A] [Algebra R A] {s : Set σ} {p : MvPolynomial σ R}

/-- A substitution into a polynomial in the variables of `s` depends only on the values of the
substitution on `s`. -/
theorem aeval_congr_of_mem_supported (hp : p ∈ supported R s) {g₁ g₂ : σ → A}
    (h : ∀ i ∈ s, g₁ i = g₂ i) : aeval g₁ p = aeval g₂ p :=
  eval₂Hom_congr' rfl (fun i hi _ => h i ((mem_supported.1 hp) (Finset.mem_coe.2 hi))) rfl

/-- A substitution into a polynomial in the variables of `s` lands in every subalgebra that
contains the values of the substitution on `s`. -/
theorem aeval_mem_of_mem_supported (hp : p ∈ supported R s) (S : Subalgebra R A) {g : σ → A}
    (hg : ∀ i ∈ s, g i ∈ S) : aeval g p ∈ S := by
  rw [supported_eq_range_rename] at hp
  obtain ⟨p', rfl⟩ := hp
  change aeval g (rename Subtype.val p') ∈ S
  rw [aeval_rename]
  induction p' using MvPolynomial.induction_on with
  | C r => rw [aeval_C]; exact S.algebraMap_mem r
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact S.mul_mem hp (hg _ i.2)

end Supported

/-- Shifting the variables preserves the split rank. -/
theorem SplitRankLE.shift {U : Set σ} {w : ℕ} {f : MvPolynomial σ R} (h : SplitRankLE U w f)
    (a : σ → R) : SplitRankLE U w (shift a f) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  have hmem : ∀ (s : Set σ), ∀ i ∈ s, (X i + C (a i) : MvPolynomial σ R) ∈ supported R s :=
    fun s i hi => add_mem (Algebra.subset_adjoin ⟨i, hi, rfl⟩) ((supported R s).algebraMap_mem _)
  exact ⟨fun i => MvPolynomial.shift a (p i), fun i => MvPolynomial.shift a (q i),
    fun i => aeval_mem_of_mem_supported (hp i) _ (hmem U),
    fun i => aeval_mem_of_mem_supported (hq i) _ (hmem Uᶜ), by simp only [map_sum, map_mul]⟩

end MvPolynomial
