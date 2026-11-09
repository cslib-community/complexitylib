/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Fixed-sample unbiased estimation

[Kong2027], Proposition 2.4 (PDF p. 7). Statistics are arbitrary real-valued
functions on a fixed finite vector of independent samples. No positivity is
required of a statistic. Equality of its expectation to a polynomial is required
on the whole probability simplex, including its boundary.
-/

public section
noncomputable section
open scoped BigOperators

namespace Cslib.FiniteSampleInformation.Estimation

variable {α : Type*} [Fintype α]

/-- A probability mass vector, with null outcomes permitted. -/
@[expose] def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Expectation under independent samples with the same mass vector. -/
@[expose] def expectation (p : α → ℝ) :
    (d : ℕ) → ((Fin d → α) → ℝ) → ℝ
  | 0, g => g Fin.elim0
  | d + 1, g => ∑ a, p a * expectation p d (fun v => g (Fin.cons a v))

/-- The recursive expectation is exactly the product-law finite expectation. -/
theorem expectation_eq_sum (p : α → ℝ) (d : ℕ) (g : (Fin d → α) → ℝ) :
    expectation p d g = ∑ v : Fin d → α, g v * ∏ t, p (v t) := by
  induction d with
  | zero =>
    simp only [expectation, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    exact congrArg g (Subsingleton.elim _ _)
  | succ d ih =>
    calc
      expectation p (d + 1) g =
          ∑ a, ∑ v : Fin d → α, g (Fin.cons a v) *
            (p a * ∏ t, p (v t)) := by
        simp only [expectation, ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ w : α × (Fin d → α), g (Fin.cons w.1 w.2) *
          (p w.1 * ∏ t, p (w.2 t)) := by rw [Fintype.sum_prod_type]
      _ = _ := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => α))
        intro w
        simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- Renaming the outcome alphabet transports the actual product-law expectation. -/
theorem expectation_comp_equiv {β : Type*} [Fintype β] (e : α ≃ β)
    (p : β → ℝ) (d : ℕ) (g : (Fin d → β) → ℝ) :
    expectation (p ∘ e) d (fun v => g (e ∘ v)) = expectation p d g := by
  induction d with
  | zero =>
    change g (e ∘ Fin.elim0) = g Fin.elim0
    exact congrArg g (Subsingleton.elim _ _)
  | succ d ih =>
    simp only [expectation]
    apply Fintype.sum_equiv e
    intro a
    congr 1
    have hcons (v : Fin d → α) : e ∘ Fin.cons a v = Fin.cons (e a) (e ∘ v) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    simp only [hcons]
    exact ih (fun v => g (Fin.cons (e a) v))

/-- Independent taskwise channel randomization gives the product law of the
processed one-sample distribution. This is an algebraic identity, so it also
applies before imposing positivity and normalization of the mass/kernel tables. -/
theorem expectation_channel {β : Type*} [Fintype β]
    (p : α → ℝ) (K : α → β → ℝ) (d : ℕ) (g : (Fin d → β) → ℝ) :
    expectation (fun b => ∑ a, p a * K a b) d g =
      ∑ v : Fin d → α, (∏ t, p (v t)) *
        ∑ w : Fin d → β, g w * ∏ t, K (v t) (w t) := by
  rw [expectation_eq_sum]
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.prod_mul_distrib]
  ring

/-- The polynomial whose evaluation is a statistic's expectation. -/
@[expose] def expectationPolynomial :
    (d : ℕ) → ((Fin d → α) → ℝ) → MvPolynomial α ℝ
  | 0, g => MvPolynomial.C (g Fin.elim0)
  | d + 1, g => ∑ a, MvPolynomial.X a *
      expectationPolynomial d (fun v => g (Fin.cons a v))

/-- Evaluation gives the actual i.i.d. expectation, even without normalization. -/
theorem eval_expectationPolynomial (p : α → ℝ) (d : ℕ) (g : (Fin d → α) → ℝ) :
    MvPolynomial.eval p (expectationPolynomial d g) = expectation p d g := by
  induction d with
  | zero => simp [expectationPolynomial, expectation]
  | succ d ih => simp [expectationPolynomial, expectation, ih]

/-- A statistic of `d` samples has polynomial degree at most `d`. -/
theorem expectationPolynomial_totalDegree (d : ℕ) (g : (Fin d → α) → ℝ) :
    (expectationPolynomial d g).totalDegree ≤ d := by
  induction d with
  | zero => simp [expectationPolynomial]
  | succ d ih =>
    change (∑ a, MvPolynomial.X a *
      expectationPolynomial d (fun v => g (Fin.cons a v))).totalDegree ≤ d + 1
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simpa [MvPolynomial.totalDegree_X, Nat.add_comm] using
        Nat.add_le_add_left (ih (fun v => g (Fin.cons a v))) 1)

private theorem expectation_const {p : α → ℝ} (hp : IsProbability p)
    (d : ℕ) (c : ℝ) : expectation p d (fun _ => c) = c := by
  induction d with
  | zero => rfl
  | succ d ih => simp [expectation, ih, ← Finset.sum_mul, hp.2]

private theorem expectation_add (p : α → ℝ) (d : ℕ)
    (g h : (Fin d → α) → ℝ) :
    expectation p d (fun v => g v + h v) = expectation p d g + expectation p d h := by
  induction d with
  | zero => rfl
  | succ d ih => simp [expectation, ih, mul_add, Finset.sum_add_distrib]

private theorem expectation_mul_const (p : α → ℝ) (d : ℕ)
    (g : (Fin d → α) → ℝ) (c : ℝ) :
    expectation p d (fun v => g v * c) = expectation p d g * c := by
  induction d with
  | zero => rfl
  | succ d ih => simp [expectation, ih, mul_assoc, Finset.sum_mul]

/-- The same statistic may ignore an initial sample. -/
private theorem expectation_tail {p : α → ℝ} (hp : IsProbability p)
    (d : ℕ) (g : (Fin d → α) → ℝ) :
    expectation p (d + 1) (fun v => g (Fin.tail v)) = expectation p d g := by
  simp [expectation, ← Finset.sum_mul, hp.2]

/-- Unbiased estimability from a prescribed number of samples. -/
@[expose] def Unbiased (d : ℕ) (F : (α → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin d → α) → ℝ, ∀ p, IsProbability p → expectation p d g = F p

/-- Polynomial representation on the simplex, with a prescribed degree bound. -/
@[expose] def PolynomialOnSimplex (d : ℕ) (F : (α → ℝ) → ℝ) : Prop :=
  ∃ P : MvPolynomial α ℝ, P.totalDegree ≤ d ∧
    ∀ p, IsProbability p → MvPolynomial.eval p P = F p

/-- The necessary direction of the finite-sample characterization. -/
theorem Unbiased.polynomialOnSimplex {d : ℕ} {F : (α → ℝ) → ℝ}
    (h : Unbiased d F) : PolynomialOnSimplex d F := by
  obtain ⟨g, hg⟩ := h
  exact ⟨expectationPolynomial d g, expectationPolynomial_totalDegree d g,
    fun p hp => (eval_expectationPolynomial p d g).trans (hg p hp)⟩

/-- Additional samples can be ignored without changing unbiasedness. -/
theorem Unbiased.mono {d e : ℕ} {F : (α → ℝ) → ℝ}
    (h : Unbiased d F) (hde : d ≤ e) : Unbiased e F := by
  induction e, hde using Nat.le_induction with
  | base => exact h
  | succ e _ ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨fun v => g (Fin.tail v), fun p hp =>
      (expectation_tail hp e g).trans (hg p hp)⟩

/-- Every polynomial has an unbiased estimator using at most its degree samples. -/
theorem polynomial_unbiased (P : MvPolynomial α ℝ) :
    ∀ d, P.totalDegree ≤ d → Unbiased d (fun p => MvPolynomial.eval p P) := by
  classical
  induction P using MvPolynomial.induction_on'' with
  | C c =>
    intro d _
    exact ⟨fun _ => c, fun p hp => by
      simpa using expectation_const hp d c⟩
  | monomial_add a b f ha hb ihf ihm =>
    intro d hd
    change a ∉ f.support at ha
    have hfs : f.support ⊆ (MvPolynomial.monomial a b + f).support := by
      intro v hv
      have hva : v ≠ a := fun h => ha (h ▸ hv)
      simpa [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        MvPolynomial.coeff_monomial, hva.symm] using hv
    have hms : (MvPolynomial.monomial a b : MvPolynomial α ℝ).support ⊆
        (MvPolynomial.monomial a b + f).support := by
      intro v hv
      have hva : v = a := by simpa [MvPolynomial.support_monomial, hb] using hv
      subst v
      have hfzero : f.coeff a = 0 := by simpa [MvPolynomial.mem_support_iff] using ha
      simpa [MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        MvPolynomial.coeff_monomial, hfzero] using hb
    obtain ⟨g, hg⟩ := ihf d ((MvPolynomial.totalDegree_le_of_support_subset hfs).trans hd)
    obtain ⟨h, hh⟩ := ihm d ((MvPolynomial.totalDegree_le_of_support_subset hms).trans hd)
    refine ⟨fun v => h v + g v, fun p hp => ?_⟩
    rw [expectation_add, hh p hp, hg p hp]
    exact MvPolynomial.eval_add.symm
  | mul_X P a ih =>
    intro d hd
    by_cases hP : P = 0
    · subst P
      exact ⟨fun _ => 0, fun p hp => by simp [expectation_const hp]⟩
    · have hdeg : (P * MvPolynomial.X a).totalDegree = P.totalDegree + 1 := by
        rw [MvPolynomial.totalDegree_mul_of_isDomain hP (MvPolynomial.X_ne_zero a),
          MvPolynomial.totalDegree_X]
      cases d with
      | zero => omega
      | succ d =>
        obtain ⟨g, hg⟩ := ih d (by omega)
        refine ⟨fun v => if v 0 = a then g (Fin.tail v) else 0, fun p hp => ?_⟩
        simp only [expectation, Fin.cons_zero, Fin.tail_cons]
        have heq (x : α) : expectation p d (fun v => if x = a then g v else 0) =
            (if x = a then expectation p d g else 0) := by
          split_ifs <;> simp [expectation_const hp]
        simp_rw [heq]
        simp [hg p hp, MvPolynomial.eval_mul, mul_comm]

/-- Proposition 2.4: exact fixed-sample unbiasedness is equivalent to polynomial
representation of no greater degree on the entire closed simplex. -/
theorem unbiased_iff_polynomialOnSimplex (d : ℕ) (F : (α → ℝ) → ℝ) :
    Unbiased d F ↔ PolynomialOnSimplex d F := by
  constructor
  · exact Unbiased.polynomialOnSimplex
  · rintro ⟨P, hd, hP⟩
    obtain ⟨g, hg⟩ := polynomial_unbiased P d hd
    exact ⟨g, fun p hp => (hg p hp).trans (hP p hp)⟩

end Cslib.FiniteSampleInformation.Estimation
