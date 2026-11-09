/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Client
public import CslibFrontier.Computability.WordRAM.Realization.While

/-!
# Bounded-while views of the linked Dijkstra client

The edge scan and main loop use the existing `boundedWhile` source representation. Their
equalities hold for every memory method table, without assuming correctness or admissibility
of its implementation. They retain the complete free-monad program, hence every reached
memory and query history. In particular, extracting an empty queue exits immediately.

These source equalities do not provide native code or bound its instructions. The native
realization must separately charge arithmetic, argument delivery and control, establish each
callee's reached-state domain, and exclude cutoff truncation.

## Main definitions

* `scanView`: scan exactly the returned degree with an increasing edge index.
* `loopStep`: extract and scan once, or set the remaining rounds to zero on an empty queue.
* `loopView`: extract and scan until the queue is empty, with the original round cutoff.
* `clientView`: initialize the source and execute the loop.

## Main results

* `scanView_eq`, `loopView_eq`, `clientView_eq`: equality with the original linked source.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.DataStructure Cslib.WordRAM.Realization

variable {n K V w : ℕ}

private theorem range'_forM_eq (f : ℕ → Memory.Prog Unit) (b k i : ℕ)
    (h : i + k = b) :
    (List.range' i k).forM f = (do
      let _ ← boundedWhile (fun (b i : ℕ) => i < b)
        (fun x => do f x.2; pure (x.2 + 1)) b k i
      pure ()) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    have hg : i < b := by omega
    rw [List.range'_succ]
    change (f i >>= fun _ => (List.range' (i + 1) k).forM f) = _
    rw [boundedWhile, ite_eq_left hg]
    simp only [bind_assoc, pure_bind]
    exact congrArg (fun p => f i >>= fun _ => p) (ih (i + 1) (by omega))

private theorem link_forM (M : Methods (spec n K V) (Memory.spec w))
    (xs : List ℕ) (f : ℕ → (spec n K V).Client Unit) :
    link M (xs.forM f) = xs.forM (fun i => link M (f i)) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    change ((f i >>= fun _ => is.forM f).liftM M) = _
    rw [PFunctor.FreeM.liftM_bind]
    exact congrArg (fun p => (f i).liftM M >>= fun _ => p) ih

/-- Query the degree, then scan its edge indices in their original order. -/
def scanView (M : Methods (spec n K V) (Memory.spec w)) (u : Fin n) (du : ℕ) :
    Memory.Prog Unit := do
  let d ← M (.inr (.inr (.degree u)))
  let _ ← boundedWhile (fun (b i : ℕ) => i < b)
    (fun x => do
      link M (relaxEdge u du x.2)
      pure (x.2 + 1)) d d 0
  pure ()

/-- The scan view retains the complete linked program, including repeated offset queries. -/
theorem scanView_eq (M : Methods (spec n K V) (Memory.spec w)) (u : Fin n) (du : ℕ) :
    scanView M u du = link M (scan u du) := by
  calc
    scanView M u du = (M (.inr (.inr (.degree u))) >>= fun d : ℕ =>
        link M ((List.range d).forM (relaxEdge u du))) := by
      unfold scanView
      congr 1 with d : 1
      change ℕ at d
      rw [link_forM, List.range_eq_range']
      exact (range'_forM_eq (fun i => link M (relaxEdge u du i)) d d 0 (by omega)).symm
    _ = link M (scan u du) := by
      have hd : (degree (K := K) (V := V) u).liftM M =
          M (.inr (.inr (.degree u))) :=
        PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inr (.inr (.degree u)))
      exact (congrArg (fun p : Memory.Prog ℕ =>
        p >>= fun d => link M ((List.range d).forM (relaxEdge u du))) hd.symm).trans
          (PFunctor.FreeM.liftM_bind M (degree u)
            (fun d => (List.range d).forM (relaxEdge u du))).symm

/-- One extraction and scan, setting the counter to zero when the queue is empty. -/
def loopStep (M : Methods (spec n K V) (Memory.spec w)) (x : Unit × ℕ) :
    Memory.Prog ℕ := do
  match ← M (.inl .extractMin) with
  | none => pure 0
  | some (u, du) =>
    scanView M u du
    pure (x.2 - 1)

/-- The original round cutoff with genuine early exit when extraction returns `none`. -/
def loopView (M : Methods (spec n K V) (Memory.spec w)) (k : ℕ) : Memory.Prog Unit := do
  let _ ← boundedWhile (fun (_ : Unit) (a : ℕ) => a ≠ 0) (loopStep M) () k k
  pure ()

/-- The main-loop view retains all source behavior, including the empty-queue exit. -/
theorem loopView_eq (M : Methods (spec n K V) (Memory.spec w)) (k : ℕ) :
    loopView M k = link M (loop (n := n) (K := K) (V := V) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hg : k + 1 ≠ 0 := by omega
    unfold loopView
    rw [boundedWhile, ite_eq_left hg]
    simp only [loopStep, bind_assoc, Nat.add_sub_cancel]
    change (M (.inl .extractMin) >>= _) = _
    unfold loop link queue
    congr 1 with e : 1
    cases e with
    | none =>
      simp only [pure_bind, boundedWhile_of_not (fun (_ : Unit) (a : ℕ) => a ≠ 0)
        (loopStep M) () k 0 (by simp)]
      rfl
    | some e =>
      rcases e with ⟨u, du⟩
      dsimp only
      rw [scanView_eq]
      simp only [bind_assoc, pure_bind]
      change (link M (scan (K := K) (V := V) u du) >>= fun _ => loopView M k) =
        ((scan (K := K) (V := V) u du >>= fun _ => loop k).liftM M)
      rw [PFunctor.FreeM.liftM_bind]
      exact congrArg (fun q => link M (scan (K := K) (V := V) u du) >>= fun _ => q) ih

/-- Initialize the source distance and queue, then execute the original early-exit loop. -/
def clientView (M : Methods (spec n K V) (Memory.spec w)) (src : Fin n) : Memory.Prog Unit := do
  M (.inr (.inl (.insert src 0)))
  M (.inl (.insert src 0))
  loopView M n

/-- The bounded-while client is exactly the linked original Dijkstra program. -/
theorem clientView_eq (M : Methods (spec n K V) (Memory.spec w)) (src : Fin n) :
    clientView M src = link M (dijkstra src) := by
  unfold clientView dijkstra
  rw [loopView_eq]
  rfl

end Cslib.Algorithms.Lean.Dijkstra.Native
