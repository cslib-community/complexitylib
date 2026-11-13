/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.PartialDerivatives
public import CslibFrontier.Foundations.Data.MvPolynomial.Shift
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
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
* `MvPolynomial.iteratedPDeriv_mul_of_mem_supported`: partial derivatives along variables outside
  `s` pass a factor in the variables of `s`.
* `MvPolynomial.coeff_aeval_ite_mem_X_zero`: the coefficients after setting the variables outside
  `s` to zero.
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

/-- A partial derivative of a polynomial in the variables of `s` is a polynomial in the variables
of `s`. -/
theorem pderiv_mem_supported (hp : p ∈ supported R s) (i : σ) : pderiv i p ∈ supported R s := by
  classical
  rw [mem_supported] at hp ⊢
  refine subset_trans (fun j hj => ?_) hp
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨d, hd, hjd⟩ := hj
  rw [mem_support_iff, coeff_pderiv] at hd
  refine ⟨d + Finsupp.single i 1, mem_support_iff.2 (left_ne_zero_of_mul hd), ?_⟩
  rw [Finsupp.mem_support_iff] at hjd ⊢
  rw [Finsupp.add_apply]
  omega

/-- An iterated partial derivative of a polynomial in the variables of `s` is a polynomial in the
variables of `s`. -/
theorem iteratedPDeriv_mem_supported (hp : p ∈ supported R s) {k : ℕ} (α : Fin k → σ) :
    iteratedPDeriv α p ∈ supported R s := by
  induction k with
  | zero => exact hp
  | succ k ih => exact pderiv_mem_supported (ih (Fin.tail α)) _

/-- Partial derivatives along variables outside `s` pass a factor in the variables of `s`. -/
theorem iteratedPDeriv_mul_of_mem_supported (hp : p ∈ supported R s) (q : MvPolynomial σ R)
    {k : ℕ} {α : Fin k → σ} (hα : ∀ i, α i ∉ s) :
    iteratedPDeriv α (p * q) = p * iteratedPDeriv α q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedPDeriv_succ_apply, ih (α := Fin.tail α) fun i => hα i.succ, Derivation.leibniz,
      iteratedPDeriv_succ_apply, pderiv_eq_zero_of_notMem_vars fun h =>
        hα 0 (mem_supported.1 hp (Finset.mem_coe.2 h)), smul_zero, add_zero, smul_eq_mul]

/-- A shift of a polynomial in the variables of `s` is a polynomial in the variables of `s`. -/
theorem shift_mem_supported (hp : p ∈ supported R s) (a : σ → A) :
    shift a p ∈ supported A s :=
  aeval_mem_of_mem_supported hp ((supported A s).restrictScalars R) fun i hi =>
    add_mem (Algebra.subset_adjoin ⟨i, hi, rfl⟩) ((supported A s).algebraMap_mem _)

/-- Setting the variables outside `s` to zero keeps the monomials in the variables of `s`, with
their coefficients, and removes the other monomials. -/
theorem coeff_aeval_ite_mem_X_zero (s : Set σ) [DecidablePred (· ∈ s)] (p : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    (aeval (fun i => if i ∈ s then X i else 0 : σ → MvPolynomial σ R) p).coeff m =
      if ∀ i ∈ m.support, i ∈ s then p.coeff m else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    by_cases hd : ∀ i ∈ d.support, i ∈ s
    · rw [Finset.prod_congr rfl fun i hi => show (if i ∈ s then X i else 0) ^ d i = X i ^ d i by
        simp only [hd i hi, ↓reduceIte], ← Finsupp.prod, ← monomial_eq, coeff_monomial]
      by_cases hdm : d = m
      · subst hdm
        rw [ite_eq_left hd]
      · simp only [hdm, ↓reduceIte, ite_self]
    · have hd' := hd
      push Not at hd'
      obtain ⟨i, hi, his⟩ := hd'
      rw [Finset.prod_eq_zero hi (by
        simp only [his, ↓reduceIte]
        exact zero_pow (Finsupp.mem_support_iff.1 hi)), mul_zero, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply, coeff_monomial]
      split_ifs with hm hdm
      exacts [absurd (hdm ▸ hm) hd, rfl, rfl]
  | add p q hp hq =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp

end Supported

/-- Shifting the variables preserves the split rank. -/
theorem SplitRankLE.shift {U : Set σ} {w : ℕ} {f : MvPolynomial σ R} (h : SplitRankLE U w f)
    (a : σ → R) : SplitRankLE U w (shift a f) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := h
  exact ⟨fun i => MvPolynomial.shift a (p i), fun i => MvPolynomial.shift a (q i),
    fun i => shift_mem_supported (hp i) a, fun i => shift_mem_supported (hq i) a,
    by simp only [map_sum, map_mul]⟩

end MvPolynomial
