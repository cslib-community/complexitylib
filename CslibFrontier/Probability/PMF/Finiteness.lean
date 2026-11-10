/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib for `ENNReal.Finiteness.sum_ne_top` and the `PMF.apply_ne_top`
-- tag; addition to `Cslib/Probability/PMF.lean` for the `toOuterMeasure_ne_top` tag)

public import CslibFrontier.Probability.PMF.Event
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Tactic.Finiteness

/-!
# `finiteness` rules for discrete distributions

Mathlib's `finiteness` proves goals `x ≠ ∞` in `ℝ≥0∞` from the syntax of `x`, with rules for
sums, products, powers, quotients, inverses and casts. This module adds the rules that bounds on
discrete distributions need: the mass `p a` of an outcome and the probability
`p.toOuterMeasure s` of an event are finite, and so is a finite sum of finite terms. With them
the side conditions of `ENNReal.toReal_add`, `ENNReal.toReal_mono` and `ENNReal.toNNReal_mono`
in probability bounds are `by finiteness`, whatever the shape of the bound. It also proves `x ≠ ∞`
from a hypothesis `x < _`, and applies hypotheses such as `∀ i, f i ≠ ∞`.

## Main results

* `ENNReal.Finiteness.sum_ne_top`: a finite sum of finite terms is finite, as a `finiteness` rule.
* `PMF.apply_ne_top`, `Cslib.Probability.PMF.toOuterMeasure_ne_top`: registered as `finiteness`
  rules.

## Implementation notes

The rules have penalty `-10`, so Aesop tries them before Mathlib's default-penalty rules. One of
those, `ENNReal.ofNat_ne_top`, concludes `OfNat.ofNat ?n ≠ ∞` and is tried on every goal; its
failed unification with `∑ s : Fin m, f s ≠ ∞` unfolds the sum to `List.foldr`, which made it
most of the cost of `finiteness` on sums.

A safe rule is never undone, so the sum rule would commit `∑ a ∈ s, f a ≠ ∞` to the termwise
goal even when the context proves the sum finite as a whole, by `h : ∑ a ∈ s, f a < ∞`, which
Mathlib's `ne_top_of_lt` (unsafe) uses. The rule `x ≠ ⊤` from a hypothesis `x < _`, with penalty
`-20`, keeps that proof. It matches the hypothesis up to reducible unfolding: at default
transparency, the failed matches against the other hypotheses cost more than the sum rule saves.
Hypotheses are also applied, as an unsafe rule, so that `h : ∀ i, f i ≠ ∞` gives the terms of a
sum.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- A finite sum of finite terms is finite: the forward direction of `ENNReal.sum_ne_top`, as a
`finiteness` rule. -/
@[aesop (rule_sets := [finiteness]) safe -10 apply]
protected theorem Finiteness.sum_ne_top {α : Type*} {s : Finset α} {f : α → ℝ≥0∞}
    (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a ∈ s, f a ≠ ∞ :=
  ENNReal.sum_ne_top.mpr h

end ENNReal

attribute [aesop (rule_sets := [finiteness]) safe -10 apply] PMF.apply_ne_top
  Cslib.Probability.PMF.toOuterMeasure_ne_top

end

public meta section

/- `x ≠ ⊤` from a hypothesis `x < _`, before the sum rule commits to the terms. -/
add_aesop_rules safe -20 tactic (rule_sets := [finiteness])
  (by apply ne_top_of_lt; with_reducible assumption)

/- Apply hypotheses such as `h : ∀ i, f i ≠ ∞`; `assumption` uses only exact matches. -/
attribute [aesop (rule_sets := [finiteness]) unsafe 50%] Aesop.BuiltinRules.applyHyps

end
