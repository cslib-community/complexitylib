/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

/-!
# Zero-error average-case devices for MCSP

A zero-error average-case device for `MCSP[s]` on truth tables of `n`-input functions maps each
truth table of length `N = 2 ^ n` to `some b`, an answer, or to `none`, the answer "?"
[OliveiraSanthanam2018, Section 1.2, p. 8]. It is never incorrect: an answer `some b` means that
`b = true` exactly when the truth table has circuit complexity at most `s n`. It is also
correct on most inputs: the fraction of truth tables on which it answers "?" is bounded.

This module records the per-length condition and its asymptotic form. The fraction of "?"
answers is stated as an exact natural-number count: for a parameter `k`, at most a `1 / k`
fraction of the `2 ^ (2 ^ n)` truth tables receive "?". Taking `k = 2` gives the bound
`Pr_x[A(x) ≠ "?"] ≥ 1 / 2` of [OliveiraSanthanam2018, Section 1.2, p. 8]; taking `k n = n`
with correctness for every large enough `n` gives
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34]. The device is an arbitrary function,
so these predicates can be applied to formulas, circuits or any other model by composing with its
semantics.

## Main definitions

* `Cslib.MCSP.IsZeroErrorDecider`: a zero-error device for `MCSP[s]` on `n`-input truth tables
  that answers "?" on at most a `1 / k` fraction of them.
* `Cslib.MCSP.SolvesOnAverage`: a family of devices, one for each `n`, that is eventually a
  zero-error decider at unknown fraction `1 / k n`.

## Main results

* `Cslib.MCSP.IsZeroErrorDecider.mono`, `Cslib.MCSP.SolvesOnAverage.mono`: a smaller parameter
  `k` is a weaker requirement.
* `Cslib.MCSP.isZeroErrorDecider_decide`: the exact decider, which never answers "?".

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.MCSP

open Filter

/-- `D` is a zero-error device for `MCSP[s]` on truth tables of `n`-input functions that answers
"?" (`none`) on at most a `1 / k` fraction of its `2 ^ (2 ^ n)` inputs. An answer `some b` is
always correct: `b = true` exactly when the truth table lies in `GapMCSP.yesSet s`, that is, when
its function has circuit complexity at most `s n`. This is the per-length condition of
[OliveiraSanthanam2018, Section 1.2, p. 8; Appendix A, Definition 43, p. 34]. -/
structure IsZeroErrorDecider (s : ℕ → ℕ) (n k : ℕ) (D : BitString (2 ^ n) → Option Bool) :
    Prop where
  /-- The device is never incorrect. -/
  correct : ∀ (T : BitString (2 ^ n)) (b : Bool), D T = some b →
    (b = true ↔ List.ofFn T ∈ GapMCSP.yesSet s)
  /-- At most a `1 / k` fraction of truth tables receive the answer "?". -/
  card_unknown_le : k * (Finset.univ.filter fun T : BitString (2 ^ n) => D T = none).card ≤
    2 ^ 2 ^ n

/-- The family `D` solves `MCSP[s]` on average with zero error and unknown fraction `1 / k n`:
for every large enough `n`, the device `D n` is never incorrect on `n`-input truth tables and
answers "?" on at most a `1 / k n` fraction of them. With `k n = n` this is
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34], for an arbitrary nonuniform device
family. -/
def SolvesOnAverage (s k : ℕ → ℕ) (D : ∀ n, BitString (2 ^ n) → Option Bool) : Prop :=
  ∀ᶠ n in atTop, IsZeroErrorDecider s n (k n) (D n)

variable {s : ℕ → ℕ} {n : ℕ}

theorem solvesOnAverage_iff {k : ℕ → ℕ} {D : ∀ n, BitString (2 ^ n) → Option Bool} :
    SolvesOnAverage s k D ↔ ∀ᶠ n in atTop, IsZeroErrorDecider s n (k n) (D n) :=
  Iff.rfl

/-- A zero-error decider at unknown fraction `1 / k` is one at every larger fraction `1 / k'`. -/
theorem IsZeroErrorDecider.mono {k₁ k₂ : ℕ} {D : BitString (2 ^ n) → Option Bool}
    (hD : IsZeroErrorDecider s n k₂ D) (hk : k₁ ≤ k₂) : IsZeroErrorDecider s n k₁ D where
  correct := hD.correct
  card_unknown_le := (Nat.mul_le_mul_right _ hk).trans hD.card_unknown_le

/-- Solving on average at unknown fractions `1 / k n` implies solving on average at eventually
larger fractions `1 / k' n`. -/
theorem SolvesOnAverage.mono {k k' : ℕ → ℕ} {D : ∀ n, BitString (2 ^ n) → Option Bool}
    (hD : SolvesOnAverage s k D) (hk : ∀ᶠ n in atTop, k' n ≤ k n) : SolvesOnAverage s k' D := by
  filter_upwards [hD, hk] with n hn hkn
  exact hn.mono hkn

open Classical in
/-- The exact decider for `MCSP[s]` never answers "?", so it is a zero-error decider for every
unknown fraction. -/
theorem isZeroErrorDecider_decide (k : ℕ) :
    IsZeroErrorDecider s n k fun T => some (decide (List.ofFn T ∈ GapMCSP.yesSet s)) where
  correct T b h := by
    cases Option.some.inj h
    exact decide_eq_true_iff
  card_unknown_le := by simp

end Cslib.MCSP
