/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regressions for the client_simps simp set)

public import CslibFrontier.Computability.WordRAM.Realization.Basic

/-! `simp only [client_simps]` splits the result, final state, history, cost and admissibility of
a sequential client at its binds: for an arbitrary deterministic specification, for `do` blocks
and `PFunctor.FreeM.bind`, and for `Memory.spec w`, whose operation type reduces. -/

public section

namespace Cslib.DataStructure.Tests.ClientSimps

open StateTransitionSpec WordRAM.Realization

section Generic

variable {D : StateTransitionSpec} {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn f]

example (p : D.Client ℕ) (k : ℕ → D.Client Bool) (s : D.State) :
    D.clientState s (p >>= k) = D.clientState (D.clientState s p) (k (D.clientResult s p)) := by
  simp only [client_simps]

example (p : D.Client ℕ) (s : D.State) :
    D.clientResult s (do let x ← p; pure (x + 1)) = D.clientResult s p + 1 := by
  simp only [client_simps]

example (p : D.Client ℕ) (s : D.State) :
    D.clientState s (do let _ ← p; pure 0) = D.clientState s p := by
  simp only [client_simps]

example (p : D.Client ℕ) (s : D.State) :
    D.clientHistory s (do let _ ← p; pure 0) = D.clientHistory s p := by
  simp only [client_simps, List.append_nil]

-- The cost and admissibility of the history split at the state where `p` stops.
example (p : D.Client ℕ) (k : ℕ → D.Client ℕ) (s : D.State) (c : D.State → D.Op → ℕ) :
    D.totalCost c s (D.clientHistory s (p >>= k)) =
      D.totalCost c s (D.clientHistory s p) +
        D.totalCost c (D.clientState s p) (D.clientHistory (D.clientState s p)
          (k (D.clientResult s p))) := by
  simp only [client_simps]

example (p : D.Client ℕ) (k : ℕ → D.Client ℕ) (s : D.State) :
    D.ValidHistory s (D.clientHistory s (p >>= k)) ↔
      D.ValidHistory s (D.clientHistory s p) ∧
        D.ValidHistory (D.clientState s p)
          (D.clientHistory (D.clientState s p) (k (D.clientResult s p))) := by
  simp only [client_simps]

end Generic

section Memory

-- `(Memory.spec w).Op` reduces to `Memory.Op`; the history lemmas still apply.
example (w : ℕ) (p : Memory.Prog Unit) (k : Unit → Memory.Prog ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= k)) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
        (Memory.spec w).ValidHistory ((Memory.spec w).clientState s p)
          ((Memory.spec w).clientHistory ((Memory.spec w).clientState s p) (k ())) := by
  simp only [client_simps]

example (w : ℕ) (p : Memory.Prog Unit) (k : Unit → Memory.Prog ℕ) (s : Memory.State) :
    (Memory.spec w).totalCost Memory.charge s ((Memory.spec w).clientHistory s (p >>= k)) =
      (Memory.spec w).totalCost Memory.charge s ((Memory.spec w).clientHistory s p) +
        (Memory.spec w).totalCost Memory.charge ((Memory.spec w).clientState s p)
          ((Memory.spec w).clientHistory ((Memory.spec w).clientState s p) (k ())) := by
  simp only [client_simps]

-- `PFunctor.FreeM.bind` is rewritten to `>>=` first.
example (w : ℕ) (p : Memory.Prog Unit) (k : Unit → Memory.Prog ℕ) (s : Memory.State) :
    (Memory.spec w).clientState s (p.bind k) =
      (Memory.spec w).clientState ((Memory.spec w).clientState s p) (k ()) := by
  simp only [client_simps]

example (w : ℕ) (p : Memory.Prog Unit) (s : Memory.State) :
    (Memory.spec w).clientResult s (do p; pure 0) = 0 := by
  simp only [client_simps]

-- Memory charges split the same way.
example (p : Memory.Prog Unit) (k : Unit → Memory.Prog ℕ) (s : Memory.State) :
    memoryCost (p >>= k) s =
      memoryCost p s + memoryCost (k ()) ((Memory.spec 0).clientState s p) := by
  simp only [client_simps]

example (p : Memory.Prog Unit) (s : Memory.State) :
    memoryCost (do p; pure 0) s = memoryCost p s := by
  simp only [client_simps, Nat.add_zero]

end Memory

end Cslib.DataStructure.Tests.ClientSimps
