/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option
public import Complexity.Tactic.OptionMatch

/-!
# Degree certificates by composition

`degree` proves a goal `ComputableInDegree f encIn encOut d e` from the `fun_prop` rules of the
operations in `f`. It rewrites each `match` on an option to `Option.elim`, then runs `fun_prop`,
which discharges the degree side conditions of its composition rules with `lia`.

Like `fun_prop`, it does not unfold definitions: unfold a definition first, or register a named
certificate for it with `fun_prop`.

## Main definitions

* `degree`: prove a degree certificate by composition.
-/

public section

namespace Turing.MultiTapeTM

/-- Prove `ComputableInDegree f encIn encOut d e` by composing the `fun_prop` rules of the
operations in `f`, after rewriting option matches to `Option.elim`. -/
macro "degree" : tactic =>
  `(tactic| ((try option_match_to_elim); fun_prop (disch := first | apply le_refl | lia)))

end Turing.MultiTapeTM
