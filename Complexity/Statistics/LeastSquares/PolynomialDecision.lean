/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.EqualityTarget
public import Complexity.Foundations.Algebra.Polynomial.ThresholdIsolation
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-!
# Polynomial constraints for rational-data fractional decisions

The normal equations of [MoitraRohatgi2023], Section 3, PDF p. 6, give an
existential polynomial description with the deletion threshold as a free
variable. `decision_iff` proves the description for all real weights and
coefficients, including singular designs. `fractional_threshold_iff` derives
its equivalence to local inequality stability in the high-mass GP regime.

This is the direct formula with `n+d` quantified variables. It is not the
low-variable elimination of Appendix A, and supplies no quantifier-elimination
program, algebraicity theorem, root-separation bound or output-time bound.
For arbitrary real observations the same equations have real coefficients;
rational polynomial output requires the rational-data restriction used here.
Neither finite exact output nor the literal exact-computation clause of
[XuGaoHu2027], Corollary 3.4(iii), follows just from this encoding.
-/

public section

namespace Cslib.LeastSquares.PolynomialDecision

open Matrix MvPolynomial Set

variable {ι d : Type*} [Fintype ι] [Fintype d]

/-- One free threshold variable, one variable per weight and per coefficient. -/
abbrev Variables (ι d : Type*) := Option (Sum ι d)

/-- The coordinate of the residual normal equation, as a rational polynomial. -/
@[expose] noncomputable def normal (x : ι → d → ℚ) (y : ι → ℚ) (j : d) :
    MvPolynomial (Variables ι d) ℚ :=
  ∑ i, X (some (.inl i)) *
    (C (y i) - ∑ l, C (x i l) * X (some (.inr l))) * C (x i j)

/-- The affine target equality, without inverse matrices or denominators. -/
@[expose] noncomputable def target (e : d → ℚ) (θ : ℚ) : MvPolynomial (Variables ι d) ℚ :=
  (∑ j, C (e j) * X (some (.inr j))) - C θ

/-- Nonnegative exactly when deleted mass is at most the free threshold. -/
@[expose] noncomputable def budget : MvPolynomial (Variables ι d) ℚ :=
  X none - C (Fintype.card ι : ℚ) + ∑ i, X (some (.inl i))

/-- Simultaneous real assignment, leaving the threshold free in the polynomial. -/
@[expose] def assignment (w : ι → ℝ) (b : d → ℝ) (k : ℝ) : Variables ι d → ℝ
  | none => k
  | some (.inl i) => w i
  | some (.inr j) => b j

/-- Evaluation recovers the actual real residual normal equation coordinate. -/
theorem eval_normal (x : ι → d → ℚ) (y : ι → ℚ) (w : ι → ℝ) (b : d → ℝ)
    (k : ℝ) (j : d) :
    eval₂ (algebraMap ℚ ℝ) (assignment w b k) (normal x y j) =
      (∑ i, w i • (((y i : ℝ) - (fun l => (x i l : ℝ)) ⬝ᵥ b) •
        (fun l => (x i l : ℝ)))) j := by
  simp [normal, assignment, dotProduct, Finset.sum_apply, smul_eq_mul, mul_assoc]

omit [Fintype ι] in
/-- Evaluation recovers the arbitrary affine target. -/
theorem eval_target (e : d → ℚ) (θ : ℚ) (w : ι → ℝ) (b : d → ℝ) (k : ℝ) :
    eval₂ (algebraMap ℚ ℝ) (assignment w b k) (target (ι := ι) e θ) =
      (fun j => (e j : ℝ)) ⬝ᵥ b - θ := by
  simp [target, assignment, dotProduct]

omit [Fintype d] in
/-- Evaluation recovers the deletion-budget inequality. -/
theorem eval_budget (w : ι → ℝ) (b : d → ℝ) (k : ℝ) :
    eval₂ (algebraMap ℚ ℝ) (assignment w b k) (budget (ι := ι) (d := d)) =
      k - Fintype.card ι + ∑ i, w i := by
  simp [budget, assignment]

/-- Polynomial encoding with all quantified coordinates explicit. Box tests
are degree one, residual equations have degree at most two, and the free
threshold occurs only in the linear budget constraint. -/
theorem decision_iff (x : ι → d → ℚ) (y : ι → ℚ) (e : d → ℚ) (θ : ℚ) (k : ℝ) :
    EqualityNormalDecision (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
      (fun j => (e j : ℝ)) θ k ↔
    ∃ (w : ι → ℝ) (b : d → ℝ),
      (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧
      (∀ j, eval₂ (algebraMap ℚ ℝ) (assignment w b k) (normal x y j) = 0) ∧
      eval₂ (algebraMap ℚ ℝ) (assignment w b k) (target (ι := ι) e θ) = 0 ∧
      0 ≤ eval₂ (algebraMap ℚ ℝ) (assignment w b k) (budget (ι := ι) (d := d)) := by
  simp only [EqualityNormalDecision, eval_normal, eval_target, eval_budget,
    sub_eq_zero, funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨w, b, hw, hn, ht, hk⟩
    exact ⟨w, b, hw, hn, ht, by linarith⟩
  · rintro ⟨w, b, hw, hn, ht, hk⟩
    exact ⟨w, b, hw, hn, ht, by linarith⟩

/-- The free-variable polynomial formula describes every local fractional
threshold below the singular regime. Attainment and the inequality-to-equality
bridge are proved by `equalityNormalDecision_iff`, not elimination assumptions. -/
theorem fractional_threshold_iff [DecidableEq d] (x : ι → d → ℚ)
    (hgp : GeneralPosition (fun i j => (x i j : ℝ)))
    (y : ι → ℚ) (e : d → ℚ) (θ : ℚ) (w : ι → ℝ)
    (hw : Feasible (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
      (fun j => (e j : ℝ)) θ w)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i)
    (hfull : (θ : ℝ) < (fun j => (e j : ℝ)) ⬝ᵥ
      weightedEstimate 0 0 Finset.univ (fun i j => (x i j : ℝ))
        (fun i => (y i : ℝ)) (fun _ => 1))
    (k : ℝ) (hk : k ≤ Fintype.card ι - Fintype.card d) :
    fractionalStability (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
      (fun j => (e j : ℝ)) θ ≤ k ↔
    ∃ (w : ι → ℝ) (b : d → ℝ),
      (∀ i, w i ∈ Icc (0 : ℝ) 1) ∧
      (∀ j, eval₂ (algebraMap ℚ ℝ) (assignment w b k) (normal x y j) = 0) ∧
      eval₂ (algebraMap ℚ ℝ) (assignment w b k) (target (ι := ι) e θ) = 0 ∧
      0 ≤ eval₂ (algebraMap ℚ ℝ) (assignment w b k) (budget (ι := ι) (d := d)) :=
  (equalityNormalDecision_iff _ hgp _ _ _ w hw hmass hfull k hk).symm.trans
    (decision_iff x y e θ k)

/-- An explicit sign description and root separation suffice for finite exact
output of fractional stability. The sign description is equivalent to normal
feasibility, not to an assumed optimum value. Neither its construction nor the
separation bound is supplied by MR23's Boolean contract. This conditional bridge
does not assert the paper's exact-output runtime or its applicability to arbitrary
real input data. The isolator uses the supplied polynomial product verbatim. -/
theorem isolate_fractional_of_sign_description [DecidableEq d]
    (x : ι → d → ℚ) (hgp : GeneralPosition (fun i j => (x i j : ℝ)))
    (y : ι → ℚ) (e : d → ℚ) (θ : ℚ) (w : ι → ℝ)
    (hw : Feasible (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
      (fun j => (e j : ℝ)) θ w)
    (hmass : (Fintype.card d : ℝ) - 1 < ∑ i, w i)
    (hfull : (θ : ℝ) < (fun j => (e j : ℝ)) ⬝ᵥ
      weightedEstimate 0 0 Finset.univ (fun i j => (x i j : ℝ))
        (fun i => (y i : ℝ)) (fun _ => 1))
    {m : ℕ} (p : Fin m → Polynomial ℚ) (hp : ∀ i, p i ≠ 0)
    (recipe : (Fin m → Bool) → Bool) (l u : ℚ)
    (hl : (l : ℝ) < fractionalStability (fun i j => (x i j : ℝ))
      (fun i => (y i : ℝ)) (fun j => (e j : ℝ)) θ)
    (hu : fractionalStability (fun i j => (x i j : ℝ))
      (fun i => (y i : ℝ)) (fun j => (e j : ℝ)) θ ≤ (u : ℝ))
    (hupper : (u : ℝ) ≤ Fintype.card ι - Fintype.card d)
    (hdesc : ∀ r ∈ Icc (l : ℝ) u,
      recipe (fun i => decide (((p i).map (algebraMap ℚ ℝ)).eval r ≤ 0)) = true ↔
        EqualityNormalDecision (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
          (fun j => (e j : ℝ)) θ r)
    (q : ℚ → Algorithms.Lean.TimeM ℕ Bool)
    (hq : ∀ r ∈ Icc l u, (q r).ret = true ↔
      EqualityNormalDecision (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
        (fun j => (e j : ℝ)) θ r)
    (δ : ℝ)
    (hsep : ∀ a b : ℝ, ((∏ i, p i).map (algebraMap ℚ ℝ)).IsRoot a →
      ((∏ i, p i).map (algebraMap ℚ ℝ)).IsRoot b → a ≠ b → δ ≤ |a - b|)
    (t : ℕ) (hwidth : ((u - l : ℚ) : ℝ) / 2 ^ t < δ) :
    (Cslib.Polynomial.ThresholdIsolation.isolate (∏ i, p i) q t l u).ret.Represents
      (fractionalStability (fun i j => (x i j : ℝ)) (fun i => (y i : ℝ))
        (fun j => (e j : ℝ)) θ) := by
  have hroot := Cslib.Polynomial.ThresholdIsolation.boundary_product_root p recipe _ _ _ hl hu
    (fun r hr => (hdesc r hr).trans
      (equalityNormalDecision_iff _ hgp _ _ _ w hw hmass hfull r (hr.2.trans hupper)))
  exact Cslib.Polynomial.ThresholdIsolation.isolate_represents _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) q _ δ hroot hsep t l u
    (fun r hr => (hq r hr).trans
      (equalityNormalDecision_iff _ hgp _ _ _ w hw hmass hfull r
        ((show (r : ℝ) ≤ u by exact_mod_cast hr.2).trans hupper))) hl.le hu hwidth

end Cslib.LeastSquares.PolynomialDecision
