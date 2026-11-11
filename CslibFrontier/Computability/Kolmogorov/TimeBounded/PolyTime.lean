/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.TimeBounded
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Polynomial
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# `K^t` of the outputs of polynomial-time functions

A function computed in polynomial time has outputs of small time-bounded Kolmogorov complexity:
the universal machine simulates its machine on the encoded input, so `K^t(G a)` is at most the
length of the encoding of `a` plus a constant once `t` dominates a polynomial in that length
([Liu and Pass, Proof of Theorem 5.2, Equation (3), §5.2, pp. 11–12 of
arXiv:2009.11514v1][LiuPass2020]).

## Main results

* `Cslib.Kolmogorov.exists_timeBounded_of_computableInPolyTime`: for `G` computable in polynomial
  time with respect to an encoding `enc`, there are a monotone polynomial `pG` and a constant `c`
  with `K^t(G a) ≤ |enc a| + c` whenever `pG(|enc a|) ≤ t(|G a|)`.

## References

* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 5.2).
-/

public section

namespace Cslib.Kolmogorov

open Turing.MultiTapeTM

/-- General polynomial-time $K^t$ upper bound for any encoded input type $\alpha$: if
`G : α → List Bool` is computable in polynomial time with respect to `enc : α ↪ List Bool` and
`encBits`, there exist a monotone polynomial `pG` (with `n + 1 ≤ pG.eval n`) and a constant `c`
such that whenever `pG.eval (enc a).length ≤ t (G a).length`, we have
`timeBounded t (G a) ≤ ((enc a).length + c : ℕ)`. -/
theorem exists_timeBounded_of_computableInPolyTime {α : Type*} {enc : α ↪ List Bool}
    {G : α → List Bool} (hG : ComputableInPolyTime G enc encBits) :
    ∃ (pG : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ pG.eval n) ∧
      Monotone pG.eval ∧
      ∀ {t : ℕ → ℕ} (a : α), pG.eval (enc a).length ≤ t (G a).length →
        timeBounded t (G a) ≤ ((enc a).length + c : ℕ) := by
  obtain ⟨tG, sG, htG, _, k, State, hfin, tm, htm⟩ := hG
  obtain ⟨pG, hpG⟩ := htG.exists_polynomial_le
  obtain ⟨c_sim, hsim⟩ :=
    DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM tm
  refine ⟨pG, c_sim, fun n => (hpG n).1, pG.monotone_eval, fun {t} a hstep' => ?_⟩
  have hcomp := htm a
  have hstep : tG (enc a).length ≤ t (G a).length := (hpG _).2.trans hstep'
  have htm_le :
      (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG (enc a).length) (G a) ≤
        ((enc a).length : ℕ∞) :=
    DescriptionMethod.etimeBoundedComplexity_ofMultiTapeTM_le hcomp.2.1 hcomp.1
  calc
    timeBounded t (G a) = timeBoundedAt (t (G a).length) (G a) := rfl
    _ ≤ timeBoundedAt (tG (enc a).length) (G a) := timeBoundedAt_anti hstep
    _ ≤ (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG (enc a).length) (G a) +
        c_sim := hsim (tG (enc a).length) (G a)
    _ ≤ ((enc a).length : ℕ∞) + c_sim := add_le_add_left htm_le _
    _ = ((enc a).length + c_sim : ℕ) := by rw [Nat.cast_add]

end Cslib.Kolmogorov
