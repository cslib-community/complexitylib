/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Module
public import Complexity.Languages.Probabilistic.Basic

/-!
# Linking is oracle interpretation

A client of a state-transition specification is an oracle program over the specification's
signature: both are `PFunctor.FreeM` over the operations and their answer types. Linking a client
through methods over a lower interface is interpreting the program in the lower interface's client
monad, answering each call with its method (`link_eq_interpret`). The lemmas about
`OracleComp.interpret` (sequencing, composition of interpretations, interpretation into `PMF`
and state monads) therefore apply to linked clients, and refinement and cost results about `link`
apply to interpreted programs.

This bridge is its own module so that the state-transition layer does not import probability.

## Main results

* `link_eq_interpret`: linking is interpretation by the methods.
-/

@[expose] public section

namespace Cslib.DataStructure

universe u v w

variable {D E : StateTransitionSpec.{u, v, w}} {α : Type w}

/-- Linking a client through methods is interpreting it as an oracle program, answering each
call with its method. -/
theorem link_eq_interpret (methods : Methods D E) (p : D.Client α) :
    link methods p = OracleComp.interpret (spec := D.Result) (m := E.Client) methods p := rfl

end Cslib.DataStructure
