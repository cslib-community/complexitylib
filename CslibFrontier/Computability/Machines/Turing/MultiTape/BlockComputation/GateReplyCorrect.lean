/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.GateReply
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitNodeCorrect

/-!
# Native gate replies for the existing encoded tree

Typed paths are routed to the existing descending tree's interval gate, including constant
source padding (`nodeAt_eq_gate`), and the active branch runs the native gate-vector machine
clock for clock (`runFrom_inr`). `GateReplyBounds` combines these routing facts with the bounded
gate-vector computation into the end-to-end reply theorems.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed Cslib.BitString

private theorem resolve_eq_walk {k q : ℕ} (σ : ℕ)
    (path : List (Fin (k * 3 + 1))) :
    Descending.resolve (BlockComputation.child (scheduleOfNat k q σ)) q path =
      ImplicitPath.walk k (σ, q, path.map Fin.val) := by
  have hnext : Descending.next (BlockComputation.child (scheduleOfNat k q σ)) =
      BlockComputation.child (scheduleOfNat k q σ) := by
    funext n j
    cases n with
    | zero => rfl
    | succ n => simp [Descending.next]
  rw [Descending.resolve, hnext, ImplicitPath.walk_eq]

/-- At an internal typed path, lookup uses exactly the interval reached by native navigation. -/
theorem nodeAt_eq_gate {k q s : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (σ : ℕ) (path : List (Fin (k * 3 + 1)))
    (hdepth : path.length < q) :
    (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e).nodeAt path =
      .gate (codeGate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ)
        (Encoding.encode e) (Encoding.decode e)
        (ImplicitPath.walk k (σ, q, path.map Fin.val))) := by
  rw [encodedTree, tree, Descending.nodeAt_tree]
  simp only [Descending.lookup, hdepth, ↓reduceIte, resolve_eq_walk]
  congr 1
  unfold Descending.paddedGate
  split_ifs with hz
  · rw [hz]
    rfl
  · rfl

/-- The active branch preserves every physical clock of the vector subroutine. -/
theorem runFrom_inr {k s : ℕ} {Q : Type} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (state : GateVector.State k Q) (t : ℕ) :
    (machine M e).runFrom w (.inr state) t =
      .inr ((GateVector.machine M e).runFrom w state t) := by
  have hstep (q : GateVector.State k Q) :
      (machine M e).step w (.inr q) = .inr ((GateVector.machine M e).step w q) := by
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inr]
    by_cases h : (GateVector.machine M e).halted q = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih, hstep, QueryMachine.runFrom_succ]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply
