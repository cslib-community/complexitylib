/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Stack.Memory
public import Complexity.DataStructure.StateTransition.WP

/-!
# Weakest preconditions with cost

The weakest precondition evaluates a client operation by operation. The tests compute the answer,
final state and operation count of a client of the bounded stack by `simp`, and the memory cost
of the array stack's push over the memory oracle, and check `wp_iff` against evaluation.
-/

@[expose] public section

namespace ComplexityTests.StateTransitionWP

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.StateTransitionSpec
  Cslib.DataStructure.Queue

/-- A bounded stack of capacity `2` at word size `8`. -/
abbrev S : StateTransitionSpec := Stack.WordRAM.spec 8 2

/-- Push `1` and `2`, then pop. -/
def client : S.Client (Option ℕ) := do
  S.call (.push 1)
  S.call (.push 2)
  S.call .pop

/-- From the empty stack, the client is admissible, answers `2`, leaves `[1]`, and makes three
operations. -/
example : S.wp (fun _ _ => 1) client (fun a s t => a = some 2 ∧ s = [1] ∧ t = 3) [] := by
  simp [client, wp_bind, Fits]

/-- From a full stack, the first push is not admissible. -/
example : ¬S.wp (fun _ _ => 1) client (fun _ _ _ => True) [7, 8] := by
  simp [client, wp_bind]

/-- The array stack's push over memory: the count cell goes from `0` to `1`, at a memory cost of
three units. -/
example : (Memory.spec 8).wp Memory.charge (Stack.Memory.push ⟨⟨0, 1⟩, ⟨1, 2⟩⟩ 5)
    (fun _ s t => s.mem 0 = 1 ∧ s.mem 1 = 5 ∧ t = 3) ⟨fun _ => 0, 3⟩ :=
  (wp_iff _ _ _).mpr ⟨by decide, by decide⟩

end ComplexityTests.StateTransitionWP
