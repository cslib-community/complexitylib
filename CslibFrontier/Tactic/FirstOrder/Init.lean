/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Aesop

/-!
# Rule sets for first-order formulas and interpretations

Attributes for the automation of `CslibFrontier.Tactic.FirstOrder`, declared in a file of their own
because an attribute cannot be used in the file declaring it. Lemmas are tagged where they are
proved.

* The Aesop rule set `FirstOrder` proves the syntactic side conditions of first-order reductions:
  quantifier-freeness of formulas, interpretations, projection formulas and projections, and
  closure of classes of structures under isomorphism.
* The simp set `fo_realize` unfolds the realization of formulas built from the combinators of
  `CslibFrontier.Logics.FirstOrder.Basic`, of projection formulas and of the relations of
  interpreted structures, down to propositions about the input structure.

## Main definitions

* `FirstOrder`: the Aesop rule set used by `fo_qf` and `fo_reduction`.
* `fo_realize`: the simp set used by `fo_simp` and `fo_reduction`.
-/

public section

declare_aesop_rule_sets [FirstOrder]

end

public meta section

/-- The simp set `fo_realize` unfolds the realization of first-order formulas, projection formulas
and interpreted relations to plain propositions about the structure they are evaluated in. -/
register_simp_attr fo_realize

end
