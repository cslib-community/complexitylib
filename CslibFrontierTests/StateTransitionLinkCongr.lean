/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (complete linked-run transport regressions)

public import CslibFrontier.DataStructure.Memory.Spec
public import CslibFrontier.DataStructure.StateTransition.LinkCongr

/-! Complete method runs preserve adaptive replies, changed memory and the selected history.
An extra read has the same result and final state but a different charged history. -/

public section

namespace Cslib.DataStructure.Tests.LinkCongr

/-- Replacing every method by a result-staging wrapper preserves the complete adaptive run. -/
theorem linked_write_read (w : ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s
      (link (D := Memory.spec w) (E := Memory.spec w)
        (fun o => do let a ← PFunctor.FreeM.lift o; pure a)
        (do let v ← Memory.read 1; Memory.write 2 (v + 1); Memory.read 2)) =
      (s.mem 1 + 1, ⟨Function.update s.mem 2 (s.mem 1 + 1), s.frontier⟩,
        [Memory.Op.read 1, Memory.Op.write 2 (s.mem 1 + 1), Memory.Op.read 2]) := by
  have hmethods : ∀ t (o : Memory.Op),
      (Memory.spec w).runClient t (PFunctor.FreeM.lift o) =
        (Memory.spec w).runClient t (do let a ← PFunctor.FreeM.lift o; pure a) := by
    intro t o
    change (Memory.spec w).runClient t (PFunctor.FreeM.lift o) =
      (Memory.spec w).runClient t ((PFunctor.FreeM.lift o).bind fun a => .pure a)
    rw [StateTransitionSpec.runClient_bind]
    rfl
  rw [← StateTransitionSpec.runClient_link_congr _ _ hmethods]
  rfl

-- Keeping the answer and final state alone is insufficient: the lower history differs.
example (w : ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s (Memory.read 1) ≠
      (Memory.spec w).runClient s (do let _ ← Memory.read 1; Memory.read 1) := by
  intro h
  have hlength := congrArg (fun r : ℕ × Memory.State × List Memory.Op => r.2.2.length) h
  change 1 = 2 at hlength
  omega

end Cslib.DataStructure.Tests.LinkCongr
