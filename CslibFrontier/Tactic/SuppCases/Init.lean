/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `supp_norm`

Declares the simp set `supp_norm`, in a file of its own because an attribute cannot be used in the
file declaring it. `CslibFrontier.Tactic.SuppCases` tags its lemmas and defines the tactic
`supp_cases` that uses it.

## Main definitions

* `supp_norm`: rewrites a membership in the support of a program or distribution into existentials
  over the supports of its parts and equations for its returned values.
-/

public meta section

/-- The simp set `supp_norm` rewrites a membership in the support of a `PMF`, or in the possible
results of an `OracleComp` program, built with `bind`, `map`, `pure` and `if`, into existentials
over the supports of its parts and equations for its returned values. Uniform draws contribute no
membership condition, and returned pairs are compared componentwise. -/
register_simp_attr supp_norm

end
