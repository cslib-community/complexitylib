/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.CostHoare
public import Complexity.Tactic.Stateful.Init

/-!
# Proof search for stateful operation contracts

`stateful` uses local contracts and the `Stateful` Aesop rule set. The initial rules cover pure
results and individual calls. Use `StateTransitionSpec.CostHoare.bind` with an intermediate contract
and budgets to expose sequencing obligations, and `StateTransitionSpec.CostHoare.link` to select an
implementation. Neither rule is applied blindly: its intermediate assertions or implementation are
proof inputs.

This tactic proves the stated semantic or operation-cost contract. It does not reinterpret that
contract as total machine time; `polytime` certificates for controllers remain separate.

## Main definitions

* `stateful`: search for a stateful contract using local facts and registered rules.
-/

public section

-- Operation-dependent answer types may reduce through a user-defined specification. Match
-- these four structural rules by unification rather than indexing those dependent arguments.
attribute [aesop safe apply (index := [unindexed]) (rule_sets := [Stateful])]
  Cslib.DataStructure.StateTransitionSpec.Hoare.pure
  Cslib.DataStructure.StateTransitionSpec.Hoare.call
  Cslib.DataStructure.StateTransitionSpec.CostHoare.pure
  Cslib.DataStructure.StateTransitionSpec.CostHoare.call

/-- Prove a stateful semantic or operation-cost contract from compositional rules. -/
macro "stateful" : tactic => `(tactic| solve | aesop (rule_sets := [Stateful]))

end
