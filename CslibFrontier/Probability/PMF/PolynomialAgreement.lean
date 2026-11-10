/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Polynomial.Roots

/-!
# Agreement of polynomials at a uniform point

The univariate Schwartz–Zippel lemma in probability form: two distinct polynomials of degree at
most `d` over a finite integral domain `R` agree at a uniformly random point with probability at
most `d / |R|`. The counting core is Mathlib's
`Polynomial.eq_of_natDegree_lt_card_of_eval_eq'`; this module turns it into the outer-measure bound
used by the soundness proofs of the sum-check and GKR protocols.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_eval_eq`: a set of points at which
  two distinct polynomials of degree at most `d` agree has uniform probability at most `d / |R|`.
-/

public section

namespace Cslib.Probability.PMF

open Polynomial
open scoped ENNReal

/-- **Univariate Schwartz–Zippel, probability form.** Two distinct polynomials `p` and `q` of
degree at most `d` over a finite integral domain agree on at most `d` points, so a uniformly random
point lies in a set `S` of agreement points with probability at most `d / |R|`. -/
theorem toOuterMeasure_uniformOfFintype_le_of_eval_eq {R : Type*} [CommRing R] [IsDomain R]
    [Fintype R] {p q : R[X]} {d : ℕ} (hne : p ≠ q) (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    {S : Set R} (hS : ∀ t ∈ S, p.eval t = q.eval t) :
    (PMF.uniformOfFintype R).toOuterMeasure S ≤ (d : ℝ≥0∞) / Fintype.card R := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
  gcongr
  have hcard : (Finset.univ.filter (· ∈ S)).card ≤ max p.natDegree q.natDegree :=
    not_lt.mp fun hlt => hne <| eq_of_natDegree_lt_card_of_eval_eq' p q _
      (fun t ht => hS t (Finset.mem_filter.mp ht).2) hlt
  exact_mod_cast hcard.trans (max_le hp hq)

end Cslib.Probability.PMF
