/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Walk

/-!
# Finite-buffer arbitrary-comparison lifting

Implement the first-connector, shortest-exit and actual-arm scans of the existing whole-instance
lifting construction. The comparison may change every surviving outside row. The actual native
two-phase augmentation routine supplies its walk; all subsequent scans use original incidence
records, binary global positions and list-funded prefix lengths.

The mathematical source is Lemmas 31 and 44 of [KazdaKolmogorovRolinek2018],
arXiv:1602.03124v6, printed pp. 14 and 20–22. Finite representation bookkeeping is original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeLifting

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (WalkCode Record)

/-- Scope of one original positional record, with a bounded list default. -/
@[expose] def scope (F : CSP Table ℕ) (o : Record) : List ℕ :=
  (F.getD o.1 (⟨0, []⟩, [])).2

/-- Record of a surviving original port in the actual contracted body. Its constraint position
and original binary name are retained; its argument position is its outside-list rank. -/
@[expose] def oldRecord (F : CSP Table ℕ) (vs : List ℕ) (o : Record) : Record :=
  let os := Table.outsidePositions (scope F o).length (Blossom.positions vs (scope F o))
  (o.1, os.idxOf o.2.1, o.2.2)

/-- Invert surviving ports by the original finite incidence scan, preserving source tie order.
The fallback is an actual cycle port on certified inputs; malformed raw positions remain total. -/
@[expose] def restore (input : EdgeForest.Input) (vs : List ℕ)
    (fallback index : ℕ) : ℕ :=
  let target := EdgeAugmenting.recordAt (Contraction.contract input vs) index
  let records := CSP.occurrences input.body
  ((records.find? fun o => !vs.contains o.2.2 && oldRecord input.body vs o == target).map
    fun o => records.idxOf o).getD fallback

/-- Restore the actual outside prefix, retaining its original start and step order. -/
@[expose] def restoreWalk (input : EdgeForest.Input) (vs : List ℕ)
    (fallback : ℕ) (p : WalkCode) : WalkCode :=
  ⟨p.start, p.steps.map fun (a, b) =>
    (restore input vs fallback a, restore input vs fallback b)⟩

/-- Actual feasible original exits from one prefix, in source scan order. The original outside
port must be unused; pair feasibility is tested on the prefix's current finite buffer. -/
@[expose] def exitsAt (input : EdgeForest.Input) (w r : WalkCode) (n : ℕ) : List (ℕ × ℕ) :=
  let front := NativeWalk.take r n
  let used := NativeWalk.edges front
  let current := NativeWalk.flip input.labels used
  let records := CSP.occurrences input.body
  records.flatMap fun o =>
    ((NativeWalk.edges w).filter fun e =>
      let index := records.idxOf o
      o.2.2 == EdgeAugmenting.finish ⟨input.body, [], [], 0⟩ front &&
        o.1 == (EdgeAugmenting.recordAt input.body e).1 && !used.contains index &&
        EdgeAugmenting.valid input.body
          (NativeWalk.flip (NativeWalk.flip current [index]) [e])).map
      fun e => (records.idxOf o, e)

/-- First feasible exit, with a unary number of whole prefix steps and binary port positions. -/
structure ExitCode where
  /-- Actual prefix length; this clock is funded by the supplied walk's step list. -/
  length : ℕ
  /-- Original outside port's binary global position. -/
  input : ℕ
  /-- Original cycle port's binary global position. -/
  output : ℕ

/-- Unary prefix length is framed, then the binary outside position is framed, then the
binary cycle position. -/
enc_structure encExitCode : ExitCode where
  length : encUnary, input : encNat, output : encNat

/-- Find the earliest whole prefix with a feasible original exit, then its first actual pair. -/
@[expose] def firstExit (input : EdgeForest.Input) (w r : WalkCode) : Option ExitCode :=
  let n := (List.range (r.steps.length + 1)).findIdx fun n => !(exitsAt input w r n).isEmpty
  if n < r.steps.length + 1 then
    ((exitsAt input w r n).head?).map fun pair => ⟨n, pair.1, pair.2⟩
  else none

/-- Two actual arms at every matching original constraint, in original cycle-step order.
Repeated original constraints are retained as separate copied steps. -/
@[expose] def armCandidates (F : CSP Table ℕ) (w : WalkCode) (outside : ℕ) : List WalkCode :=
  w.steps.zipIdx.flatMap fun ((a, b), j) =>
    if (EdgeAugmenting.recordAt F a).1 = (EdgeAugmenting.recordAt F outside).1 then
      [NativeWalk.inputArm w j a outside, NativeWalk.outputArm F w j b outside]
    else []

/-- Choose the first actual valid arm against the already changed outside prefix. -/
@[expose] def attachment (input : EdgeForest.Input) (w : WalkCode) (outside : ℕ) :
    Option WalkCode :=
  (armCandidates input.body w outside).find? fun arm =>
    EdgeAugmenting.valid input.body (NativeWalk.flip input.labels (NativeWalk.edges arm))

/-- Perform the first feasible outside prefix and the first feasible actual original arm. -/
@[expose] def liftPrefix (input : EdgeForest.Input) (w r : WalkCode) : Option (List Bool) :=
  (firstExit input w r).elim none fun exit =>
    let current := NativeWalk.flip input.labels (NativeWalk.edges (NativeWalk.take r exit.length))
    (attachment ⟨input.body, current⟩ w exit.input).map fun arm =>
      NativeWalk.flip current (NativeWalk.edges arm)

/-- Restore a connector-free augmentation directly, or restore the prefix before its first
connector and execute the actual original exit/arm construction. -/
@[expose] def liftWalk (input : EdgeForest.Input) (w p : WalkCode) : Option (List Bool) :=
  w.steps.head?.elim none fun (fallback, _) =>
    let vs := NativeWalk.internal input.body w
    let connectors := Contraction.connectors input.body vs
    if (NativeWalk.edges p).all fun i => !connectors.contains
        (EdgeAugmenting.recordAt (Contraction.contract input vs) i).2.2 then
      some (NativeWalk.flip input.labels
        (NativeWalk.edges (restoreWalk input vs fallback p)))
    else
      let n := p.steps.findIdx fun pair => connectors.contains
        (EdgeAugmenting.recordAt (Contraction.contract input vs) pair.2).2.2
      liftPrefix input w (restoreWalk input vs fallback (NativeWalk.take p n))

/-- Actual native comparison augmentation followed by whole-instance lifting. Every width
check is supplied internally by the native augmentation routine. -/
@[expose] def liftComparison (input : EdgeForest.Input) (w : WalkCode)
    (comparison : List Bool) : Option (List Bool) :=
  let vs := NativeWalk.internal input.body w
  let connectors := Contraction.connectors input.body vs
  if connectors.isEmpty then none else
    (EdgeAugmenting.run
      ⟨Contraction.contract input vs, (Contraction.referenceRows input vs).flatten,
        comparison, connectors.headD 0⟩).elim none fun p => liftWalk input w p

end Cslib.Complexity.CSP.EdgeSolver.NativeLifting
