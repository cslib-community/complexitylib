/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `client_simps`

Declares the simp set `client_simps`, in a file of its own because an attribute cannot be used in
the file declaring it. `CslibFrontier.DataStructure.StateTransition` tags its client laws, and
`CslibFrontier.Computability.WordRAM.Realization.Basic` tags the laws for `memoryCost`.

## Main definitions

* `client_simps`: splits the result, final state, history, cost and admissibility of a sequential
  deterministic client at its binds.
-/

public meta section

/-- The simp set `client_simps` splits the result, final state and history of a deterministic
client (`StateTransitionSpec.clientResult`, `clientState`, `clientHistory`) at `>>=` and `pure`,
and splits the cost and admissibility of a history at an append, so that a sequential client is
reduced to its parts. -/
register_simp_attr client_simps

end
