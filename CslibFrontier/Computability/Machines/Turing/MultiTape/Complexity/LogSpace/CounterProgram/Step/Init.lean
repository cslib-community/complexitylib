/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set of `cp_step`

The simp set used by `cp_step` in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step`,
declared in a file of its own because an attribute cannot be used in the file declaring it. A simp
set is indexed once, when its lemmas are tagged, so a call that uses it does not elaborate and index
its lemmas again; `cp_step` runs once per instruction of a straight-line proof.

## Main definitions

* `cp_simps`: evaluation of counter-program expressions and of the label a read jumps to.
-/

public meta section

/-- The simp set `cp_simps` evaluates counter-program expressions
(`Turing.CounterProgram.Expr.eval`) and the label a read jumps to
(`Turing.CounterProgram.readLabel`), for `cp_step`. -/
register_simp_attr cp_simps

end
