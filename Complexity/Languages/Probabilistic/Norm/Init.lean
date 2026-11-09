/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init

/-!
# The simp set `pmf_norm`

Declares the simp set `pmf_norm`, in a file of its own because an attribute cannot be used in the
file declaring it. `Complexity.Languages.Probabilistic.Norm` tags its lemmas.

## Main definitions

* `pmf_norm`: rewrites the law of a closed probabilistic program into a normal form of
  `PMF.bind`, `PMF.pure` and `PMF.map`.
-/

public meta section

/-- The simp set `pmf_norm` rewrites the law of a closed probabilistic program, and monad notation
on `PMF`, into a normal form of `PMF.bind`, `PMF.pure` and `PMF.map`: binds are reassociated to the
right, returned values are substituted, maps are pushed into continuations and composed, and
compositions are unfolded to lambdas. -/
register_simp_attr pmf_norm

end
