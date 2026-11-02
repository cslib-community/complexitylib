/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Loop
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Memory

/-!
# Iteration forms of the Fibonacci heap's memory programs

These source equations expose the existing record programs to the realization rules. They
preserve the entire memory-oracle program, rather than only its result on valid heaps. No
instruction or amortized bound is claimed here; those require the method certificates and
their reached-state domains.

## Main definitions

* `gatherStep`: one consolidation-table slot scan, returning the next degree.
* `scatterListStep`: one root-list step, retaining the next root and largest placed degree.
* `cascadeStep`, `scatterStep`: the original stopping/continuing branches of the fuel recursions.

## Main results

* `link_gather_eq_iterate`: the existing gather program is the shared fixed-iteration source.
* `link_scatterList_eq_iterate`: the existing root-list traversal has the same iteration form.
* `link_cascade_succ_eq_step`, `link_scatter_succ_eq_step`: memory-level step equations for the
  early-exit recursions, without changing their cutoff behavior.
* `gather_iterations_le_memoryCost`, `scatterList_iterations_le_memoryCost`: each fixed iteration
  issues a real query, so the iteration count can pay control work through the memory charge.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.DataStructure Cslib.WordRAM

/-- Scan one consolidation-table slot and return the next degree. The record operations are
exactly those in `gather`; its continuation is exposed for the shared iteration rule. -/
@[expose] def gatherStep (d : ℕ) : Prog ℕ := do
  let c ← rd (.cons d)
  if c ≠ 0 then
    wr (.cons d) 0
    addRoot (c - 1)
  pure (d + 1)

private theorem gather_succ (k d : ℕ) :
    gather (k + 1) d = (do let d' ← gatherStep d; gather k d') := by
  simp only [gather, gatherStep, bind_assoc]
  congr 1
  funext c
  by_cases h : c = 0 <;> simp [h]

/-- Linking the existing gather program into memory is exactly a fixed number of applications
of `gatherStep`. The returned degree is discarded, as in the original unit-valued program. -/
theorem link_gather_eq_iterate {n : ℕ} (L : Record.Layout (Cell.ok n)) (w k d : ℕ) :
    DataStructure.link (L.methods w) (gather k d) = (do
      let _ ← Realization.iterate
        (fun q : Unit × ℕ => DataStructure.link (L.methods w) (gatherStep q.2)) () k d
      pure ()) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [gather_succ]
    simp only [Realization.iterate, DataStructure.link, PFunctor.FreeM.liftM_bind, bind_assoc]
    congr 1
    funext d'
    exact ih d'

/-- Scatter one root and retain the next root and largest placed degree. Preparation performs
the original parent/mark writes before scattering; the inner scatter keeps its original fuel. -/
@[expose] def scatterListStep (fuel : ℕ) (prep : Bool) (a : ℕ × ℕ) : Prog (ℕ × ℕ) := do
  let nxt ← rd (.right a.1)
  if prep then
    wr (.par a.1) 0
    let mk ← rd (.mark a.1)
    wr (.mark a.1) 0
    let c ← rd .numMarked
    wr .numMarked (c - mk)
  let md' ← scatter fuel a.1 a.2
  pure (nxt, md')

private theorem scatterList_succ (fuel : ℕ) (prep : Bool) (k x md : ℕ) :
    scatterList fuel prep (k + 1) x md = (do
      let a ← scatterListStep fuel prep (x, md)
      scatterList fuel prep k a.1 a.2) := by
  simp only [scatterList, scatterListStep, bind_assoc]
  cases prep <;> simp [bind_assoc]

/-- Linking the root-list traversal into memory is the shared fixed-iteration source, with
the root pointer and maximum degree as its state. This preserves nested scatter calls too. -/
theorem link_scatterList_eq_iterate {n : ℕ} (L : Record.Layout (Cell.ok n))
    (w fuel : ℕ) (prep : Bool) (k x md : ℕ) :
    DataStructure.link (L.methods w) (scatterList fuel prep k x md) = (do
      let a ← Realization.iterate
        (fun q : (ℕ × Bool) × (ℕ × ℕ) =>
          DataStructure.link (L.methods w) (scatterListStep q.1.1 q.1.2 q.2))
        (fuel, prep) k (x, md)
      pure a.2) := by
  induction k generalizing x md with
  | zero => rfl
  | succ k ih =>
    rw [scatterList_succ]
    simp only [Realization.iterate, DataStructure.link, PFunctor.FreeM.liftM_bind, bind_assoc]
    congr 1
    funext a
    exact ih a.1 a.2

/-- One cascading-cut step. `none` records the original stop at a root or after marking;
`some p` records the original cut and continuation at its parent. -/
@[expose] def cascadeStep (z : ℕ) : Prog (Option ℕ) := do
  let pz ← rd (.par z)
  if pz = 0 then pure none
  else
    let mk ← rd (.mark z)
    if mk = 0 then
      wr (.mark z) 1
      let c ← rd .numMarked
      wr .numMarked (c + 1)
      pure none
    else
      cut z (pz - 1)
      pure (some (pz - 1))

private theorem cascade_succ (fuel z : ℕ) :
    cascade (fuel + 1) z = (do
      let next ← cascadeStep z
      match next with
      | none => pure ()
      | some p => cascade fuel p) := by
  simp only [cascade, cascadeStep, bind_assoc]
  congr 1
  funext pz
  by_cases hp : pz = 0
  · simp [hp]
  · simp only [hp, ite_false, bind_assoc]
    congr 1
    funext mk
    by_cases hm : mk = 0 <;> simp [hm, bind_assoc]

/-- One source cascade step preserves both stopping branches and the recursive parent exactly.
This equation makes no assertion that the original fuel cannot run out. -/
theorem link_cascade_succ_eq_step {n : ℕ} (L : Record.Layout (Cell.ok n)) (w fuel z : ℕ) :
    DataStructure.link (L.methods w) (cascade (fuel + 1) z) = (do
      let next ← DataStructure.link (L.methods w) (cascadeStep z)
      match next with
      | none => pure ()
      | some p => DataStructure.link (L.methods w) (cascade fuel p)) := by
  rw [cascade_succ]
  simp only [DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1
  funext next
  cases next <;> rfl

/-- One consolidation step. An empty slot stops with the updated maximum degree; a collision
keeps the old maximum and continues with exactly the root returned by `link`. -/
@[expose] def scatterStep (a : ℕ × ℕ) : Prog (Option ℕ × ℕ) := do
  let d ← rd (.deg a.1)
  let c ← rd (.cons d)
  if c = 0 then
    wr (.cons d) (a.1 + 1)
    pure (none, max a.2 d)
  else
    wr (.cons d) 0
    let u' ← link a.1 (c - 1)
    pure (some u', a.2)

private theorem scatter_succ (fuel u md : ℕ) :
    scatter (fuel + 1) u md = (do
      let a ← scatterStep (u, md)
      match a.1 with
      | none => pure a.2
      | some u' => scatter fuel u' a.2) := by
  simp only [scatter, scatterStep, bind_assoc]
  congr 1
  funext d
  congr 1
  funext c
  by_cases hc : c = 0 <;> simp [hc, bind_assoc]

/-- The linked consolidation recursion has exactly the original stop/continue memory effect
and carries the original maximum degree, including when the cutoff truncates a collision chain. -/
theorem link_scatter_succ_eq_step {n : ℕ} (L : Record.Layout (Cell.ok n)) (w fuel u md : ℕ) :
    DataStructure.link (L.methods w) (scatter (fuel + 1) u md) = (do
      let a ← DataStructure.link (L.methods w) (scatterStep (u, md))
      match a.1 with
      | none => pure a.2
      | some u' => DataStructure.link (L.methods w) (scatter fuel u' a.2)) := by
  rw [scatter_succ]
  simp only [DataStructure.link, PFunctor.FreeM.liftM_bind]
  congr 1
  funext a
  rcases a with ⟨next, md'⟩
  cases next <;> rfl

/-- Every consolidation-table scan reads its slot, even when that slot is empty. This is a
lower bound on the oracle charge, not an instruction bound or an admissibility assertion. -/
theorem gather_iterations_le_memoryCost {n : ℕ} (L : Record.Layout (Cell.ok n))
    (w k d : ℕ) (s : Memory.State) :
    k ≤ Realization.memoryCost (DataStructure.link (L.methods w) (gather k d)) s := by
  induction k generalizing d s with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [gather_succ]
    simp only [DataStructure.link, PFunctor.FreeM.liftM_bind]
    simp only [← PFunctor.FreeM.bind_eq_bind, Realization.memoryCost_bind]
    have ht := ih ((Memory.spec 0).clientResult s
      (DataStructure.link (L.methods w) (gatherStep d)))
      ((Memory.spec 0).clientState s (DataStructure.link (L.methods w) (gatherStep d)))
    have hs : 1 ≤ Realization.memoryCost (DataStructure.link (L.methods w) (gatherStep d)) s := by
      simp only [gatherStep, DataStructure.link, PFunctor.FreeM.liftM_bind]
      simp only [← PFunctor.FreeM.bind_eq_bind, Realization.memoryCost_bind]
      change 1 ≤ 1 + _
      omega
    dsimp only [DataStructure.link] at ht hs
    omega

/-- Every root-list step reads its successor before preparation and the inner scatter. Thus
even zero inner fuel cannot turn a fixed iteration into free native control work. -/
theorem scatterList_iterations_le_memoryCost {n : ℕ} (L : Record.Layout (Cell.ok n))
    (w fuel : ℕ) (prep : Bool) (k x md : ℕ) (s : Memory.State) :
    k ≤ Realization.memoryCost
      (DataStructure.link (L.methods w) (scatterList fuel prep k x md)) s := by
  induction k generalizing x md s with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [scatterList_succ]
    simp only [DataStructure.link, PFunctor.FreeM.liftM_bind]
    simp only [← PFunctor.FreeM.bind_eq_bind, Realization.memoryCost_bind]
    let a := (Memory.spec 0).clientResult s
      (DataStructure.link (L.methods w) (scatterListStep fuel prep (x, md)))
    have ht := ih a.1 a.2 ((Memory.spec 0).clientState s
      (DataStructure.link (L.methods w) (scatterListStep fuel prep (x, md))))
    have hs : 1 ≤ Realization.memoryCost
        (DataStructure.link (L.methods w) (scatterListStep fuel prep (x, md))) s := by
      simp only [scatterListStep, DataStructure.link, PFunctor.FreeM.liftM_bind]
      simp only [← PFunctor.FreeM.bind_eq_bind, Realization.memoryCost_bind]
      change 1 ≤ 1 + _
      omega
    dsimp only [a, DataStructure.link] at ht
    dsimp only [DataStructure.link] at hs
    omega

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
