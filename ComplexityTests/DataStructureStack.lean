/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.DataStructure.Stack.Controller
import Complexity.DataStructure.Stack.Native

/-! The bounded stack: admissibility at the boundary, an adaptive client through the native
stack from the initial state, and the compiled controller on concrete inputs. -/

namespace ComplexityTests.DataStructureStack

open Cslib Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Queue

/-- A full stack rejects another push, while the largest fitting word remains a valid value. -/
example : ¬(Stack.spec 4 2).valid [4, 7] (.push 2) ∧ (Stack.spec 4 2).valid [] (.push 15) := by
  decide

/-- An adaptive client chooses whether to pop from the observed size. -/
def stackClient : (Stack.spec 4 2).Client (Option ℕ × ℕ) :=
  .liftBind (.push 7) fun _ =>
    .liftBind .size fun (n : ℕ) =>
      if n = 1 then
        .liftBind .pop fun v => .liftBind .size fun (m : ℕ) => .pure (v, m)
      else .pure (none, n)

/-- The native stack runs the client from the initial state, one operation at a time: it pops
the pushed value, ends empty, and spends at most the constant `K` on each of its four calls. -/
example : ∃ K, ∃ y traces,
    Executes (Stack.Native.exec 4 2) stackClient (Stack.Native.initial 3 2) (some 7, 0) y traces ∧
      Stack.Native.Rep 4 2 (Stack.Native.initialLayout 3 2) [] y ∧ total id traces ≤ 4 * K := by
  obtain ⟨K, hK⟩ := Stack.Native.run_client
  exact ⟨K, hK stackClient (Stack.Native.initial_rep (by decide)) (by
    change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
    decide)⟩

/-- The compiled controller's memory program returns `max n 1`, here at both branches. -/
example : (Memory.spec 4).clientResult (Realization.inputState [0]) (Stack.Controller.program 0) =
      1 ∧
    (Memory.spec 4).clientResult (Realization.inputState [5]) (Stack.Controller.program 5) = 5 :=
  ⟨(Stack.Controller.program_spec (by decide) (by decide)).1,
    (Stack.Controller.program_spec (by decide) (by decide)).1⟩

end ComplexityTests.DataStructureStack
