/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Branching
public import CslibFrontier.Algorithms.Lean.Arborescence.Table
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.List.ArgMin
import CslibFrontier.Foundations.Data.Nat.BinarySize
import CslibFrontier.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# Polynomial-time Chu–Liu/Edmonds arborescence and branching solvers (`P`)

This file implements plain `ComputableInPolyTime` list-table versions of the Chu–Liu/Edmonds
minimum-cost rooted arborescence algorithm and Edmonds's Theorem 1 maximum-weight branching solver
[Edmonds1967Branchings], proving that the corresponding decision problems lie in `P` with binary
integer arc weights (`encIntBin`).

Contraction modifies arc costs solely via `otherCycleCost` additions (no integer subtraction), so
after `i` contraction rounds every intermediate table entry satisfies
`|cᵢ[u, w]| ≤ (n + 1) ^ i · M₀` and has binary bit length `O(L²)` in the input length `L`, keeping
the contraction stack and all reachable `ContractState`s bounded by a polynomial in `L`.

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.ArborescenceInstance`, `.ArborescenceDecInstance`,
  `.BranchingInstance`, `.BranchingDecInstance`: structured inputs and decision instances encoded
  with `enc_structure`.
* `Cslib.Algorithms.Lean.Arborescence.ContractLevel`, `.ContractState`: structured contraction
  frames and forward-pass state for `iterateWith` and `foldl'`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsList`, `.edmondsOutList`, `.optimumBranchingList`:
  list-table solvers for minimum-cost spanning in-arborescences, out-arborescences, and
  maximum-weight branchings.
* `Cslib.Algorithms.Lean.Arborescence.minArborescenceDec`, `.minOutArborescenceDec`,
  `.maxBranchingDec`: decision languages for bounded-cost spanning in/out-arborescences and
  bounded-weight branchings.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsList`,
  `.computableInPolyTime_edmondsOutList`, `.computableInPolyTime_optimumBranchingList`:
  all three solvers are `ComputableInPolyTime` on binary integer weights.
* `Cslib.Algorithms.Lean.Arborescence.minArborescenceDec_mem_P`,
  `.minOutArborescenceDec_mem_P`, `.maxBranchingDec_mem_P`: all three decision problems belong to
  `Cslib.Complexity.P`.

## References

* [J. Edmonds, *Optimum branchings*][Edmonds1967Branchings], Sections 1–4 (Theorem 1)
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Problem instances and contraction state structures -/

/-- Row-major Boolean adjacency matrix encoding. -/
abbrev encAdjTable : List (List Bool) ↪ List Bool :=
  encList (encList encBool)

/-- Row-major binary integer weight or cost matrix encoding. -/
abbrev encIntTable : List (List ℤ) ↪ List Bool :=
  encList (encList encIntBin)

/-- Encoding of an optional list of unary vertex indices (`Option (List ℕ)`). -/
abbrev encParentOption : Option (List ℕ) ↪ List Bool :=
  encOption (encList encUnary)

/-- Instance of the minimum-cost spanning arborescence problem on vertices `0, …, n - 1` (`n =
adj.length`), given by a Boolean adjacency table, a binary integer cost table, and a binary root
vertex index. -/
structure ArborescenceInstance where
  /-- `n × n` Boolean adjacency matrix (`adj[u][v] = true` for arc `u → v`). -/
  adj : List (List Bool)
  /-- `n × n` binary integer arc-cost matrix. -/
  cost : List (List ℤ)
  /-- Designated root vertex index (`root < adj.length`). -/
  root : ℕ

/-- Encoding of `ArborescenceInstance` with Boolean adjacency table, `encIntBin` cost matrix, and
binary root index `encNat`. -/
enc_structure encArborescenceInstance : ArborescenceInstance where
  adj : encAdjTable, cost : encIntTable, root : encNat

/-- Decision instance for minimum-cost spanning arborescence (`arcCost ≤ threshold`). -/
structure ArborescenceDecInstance where
  /-- Underlying weighted digraph and root instance. -/
  inst : ArborescenceInstance
  /-- Binary integer cost upper bound. -/
  threshold : ℤ

/-- Encoding of `ArborescenceDecInstance` as instance plus binary `encIntBin` threshold. -/
enc_structure encArborescenceDecInstance : ArborescenceDecInstance where
  inst : encArborescenceInstance, threshold : encIntBin

/-- Instance of the maximum-weight branching problem on vertices `0, …, n - 1`. -/
structure BranchingInstance where
  /-- `n × n` Boolean adjacency matrix. -/
  adj : List (List Bool)
  /-- `n × n` binary integer arc-weight matrix. -/
  weight : List (List ℤ)

/-- Encoding of `BranchingInstance` with Boolean adjacency table and `encIntBin` weights. -/
enc_structure encBranchingInstance : BranchingInstance where
  adj : encAdjTable, weight : encIntTable

/-- Decision instance for maximum-weight branching (`threshold ≤ arcCost`). -/
structure BranchingDecInstance where
  /-- Underlying weighted digraph instance. -/
  inst : BranchingInstance
  /-- Binary integer weight lower bound. -/
  threshold : ℤ

/-- Encoding of `BranchingDecInstance` as instance plus binary `encIntBin` threshold. -/
enc_structure encBranchingDecInstance : BranchingDecInstance where
  inst : encBranchingInstance, threshold : encIntBin

/-- One contraction level recorded by the forward pass of `edmondsTableAuxList` for bottom-up
expansion of parent pointers. -/
structure ContractLevel where
  /-- Selected parent table `f[v]` before contraction (`v < n`). -/
  parent : List ℕ
  /-- Cycle indicator mask `inCycle[v]` for the contracted directed cycle `C`. -/
  inCycle : List Bool
  /-- Best incoming vertex index into `C` from each `u ∉ C`, if any. -/
  bestEntry : List (Option ℕ)
  /-- Best outgoing vertex `x ∈ C` to each `w ∉ C`, if any. -/
  bestExit : List (Option ℕ)
  /-- Representative vertex `x₀ ∈ C` of the contracted cycle. -/
  rep : ℕ

/-- Encoding of `ContractLevel` with unary vertex indices bounded by `n`. -/
enc_structure encContractLevel : ContractLevel where
  parent : (encList encUnary), inCycle : (encList encBool),
  bestEntry : (encList (encOption encUnary)), bestExit : (encList (encOption encUnary)),
  rep : encUnary

/-- Forward contraction state of the list-based Chu–Liu/Edmonds solver. -/
structure ContractState where
  /-- Current contracted adjacency matrix. -/
  adj : List (List Bool)
  /-- Current contracted integer cost matrix. -/
  cost : List (List ℤ)
  /-- Root vertex index (`encUnary` during table contraction). -/
  root : ℕ
  /-- Whether contraction has terminated (acyclic solution found or infeasible). -/
  done : Bool
  /-- Base acyclic parent map when terminated cleanly, or `none`. -/
  result : Option (List ℕ)
  /-- Contraction frames pushed innermost-first for backward `foldl` expansion. -/
  stack : List ContractLevel

/-- Encoding of `ContractState` for `iterateWith`. -/
enc_structure encContractState : ContractState where
  adj : encAdjTable, cost : encIntTable,
  root : encUnary, done : encBool, result : encParentOption,
  stack : (encList encContractLevel)

/-- Input bundle for parameterized `edmondsTableAuxList`. -/
structure TableAuxInput where
  /-- Iteration bound (fuel) in unary. -/
  fuel : ℕ
  /-- Root vertex index in unary. -/
  root : ℕ
  /-- Boolean adjacency table. -/
  adj : List (List Bool)
  /-- Integer arc-cost table. -/
  cost : List (List ℤ)

/-- Encoding of `TableAuxInput` with unary fuel and root and binary integer costs. -/
enc_structure encTableAuxInput : TableAuxInput where
  fuel : encUnary, root : encUnary, adj : encAdjTable,
  cost : encIntTable

/-- Intermediate workspace record for one contraction round (`contractFromParent`). -/
structure ContractWork where
  /-- Current contraction state before the step. -/
  state : ContractState
  /-- Selected parent table `f`. -/
  parent : List ℕ
  /-- Representative vertex `x₀` of the detected cycle. -/
  rep : ℕ
  /-- Cycle indicator mask `inCycle`. -/
  inCycle : List Bool
  /-- Other-cycle-cost sum vector `otherCycleCost`. -/
  other : List ℤ
  /-- Best entry vector `bestEntry`. -/
  bestEntry : List (Option ℕ)
  /-- Best exit vector `bestExit`. -/
  bestExit : List (Option ℕ)

/-- Encoding of `ContractWork` for assembling step certificates without nested pair projections. -/
enc_structure encContractWork : ContractWork where
  state : encContractState, parent : (encList encUnary), rep : encUnary,
  inCycle : (encList encBool), other : (encList encIntBin),
  bestEntry : (encList (encOption encUnary)), bestExit : (encList (encOption encUnary))

/-! ### Table semantics and decision problems -/

/-- Read entry `(u, w)` of a Boolean adjacency table, defaulting out-of-bounds to `false`. -/
@[expose] def adjAt (a : List (List Bool)) (u w : ℕ) : Bool :=
  (a.getD u []).getD w false

/-- Read `(u, w)` entry of an integer cost table, defaulting out-of-bounds entries to `0`. -/
@[expose] def costAt (c : List (List ℤ)) (u w : ℕ) : ℤ :=
  (c.getD u []).getD w 0

/-- Digraph on `Fin a.length` defined by `adjAt a`. -/
@[expose] def tableDigraph (a : List (List Bool)) : Digraph (Fin a.length) where
  Adj u w := adjAt a u.1 w.1 = true

instance instDecidableRelTableDigraphAdj (a : List (List Bool)) :
    DecidableRel (tableDigraph a).Adj :=
  fun u w => inferInstanceAs (Decidable (adjAt a u.1 w.1 = true))

/-- Integer arc-cost function on `Fin n` extracted from `costAt c`. -/
@[expose] def tableCost (c : List (List ℤ)) {n : ℕ} (u w : Fin n) : ℤ :=
  costAt c u.1 w.1

/-- Decision language for minimum-cost spanning in-arborescence (`arcCost T ≤ threshold`). -/
@[expose] def minArborescenceDec : Set ArborescenceDecInstance :=
  {d | ∃ h : d.inst.root < d.inst.adj.length,
    ∃ T : Digraph (Fin d.inst.adj.length),
      T.IsInArborescence ⟨d.inst.root, h⟩ ∧ T ≤ tableDigraph d.inst.adj ∧
        let _ := Classical.decRel T.Adj
        arcCost T (tableCost d.inst.cost) ≤ d.threshold}

/-- Decision language for minimum-cost spanning out-arborescence (`arcCost T ≤ threshold`). -/
@[expose] def minOutArborescenceDec : Set ArborescenceDecInstance :=
  {d | ∃ h : d.inst.root < d.inst.adj.length,
    ∃ T : Digraph (Fin d.inst.adj.length),
      T.IsOutArborescence ⟨d.inst.root, h⟩ ∧ T ≤ tableDigraph d.inst.adj ∧
        let _ := Classical.decRel T.Adj
        arcCost T (tableCost d.inst.cost) ≤ d.threshold}

/-- Decision language for maximum-weight branching (`threshold ≤ arcCost B`). -/
@[expose] def maxBranchingDec : Set BranchingDecInstance :=
  {d | ∃ B : Digraph (Fin d.inst.adj.length),
    B.IsBranching ∧ B ≤ tableDigraph d.inst.adj ∧
      let _ := Classical.decRel B.Adj
      d.threshold ≤ arcCost B (tableCost d.inst.weight)}

/-! ### List-based Chu–Liu/Edmonds operations -/

/-- Single step in scanning `List.range n` for the first index satisfying `pred` with minimum
`key`. -/
@[expose] def argMinStep (pred : ℕ → Bool) (key : ℕ → ℤ) (acc : Option ℕ) (j : ℕ) :
    Option ℕ :=
  if pred j then
    acc.elim (some j) fun cur => if decide (key j < key cur) then some j else some cur
  else acc

/-- First index in `List.range n` satisfying `pred` with minimum `key`. -/
@[expose] def argMinRange (n : ℕ) (pred : ℕ → Bool) (key : ℕ → ℤ) : Option ℕ :=
  (List.range n).foldl (argMinStep pred key) none

/-- Select cheapest valid incoming parent for each `v ≠ r` (`some r` at `v = r`), returning `none`
when some `v ≠ r` has no valid candidate arc. -/
@[expose] def selectParentsList (a : List (List Bool)) (c : List (List ℤ)) (r : ℕ) :
    Option (List ℕ) :=
  let n := a.length
  let opts := (List.range n).map fun v =>
    if v == r then some r
    else argMinRange n (fun w => adjAt a v w && (w != v)) (fun w => costAt c v w)
  if opts.all Option.isSome then some (opts.map fun o => o.getD 0) else none

/-- Follow parent table `f` from `x`, defaulting out-of-bounds lookups to `0`. -/
@[expose] def followParent (f : List ℕ) (x : ℕ) : ℕ :=
  f.getD x 0

/-- Test whether `x` reaches itself within `n` steps of `followParent f` (in `1 .. n` steps). -/
@[expose] def hasCycleFromList (n : ℕ) (f : List ℕ) (x : ℕ) : Bool :=
  (List.range n).any fun k => (followParent f)^[k + 1] x == x

/-- Find the first vertex `x < n` with `x ≠ r` lying on a cycle of `followParent f`. -/
@[expose] def findCycleList (n r : ℕ) (f : List ℕ) : Option ℕ :=
  (List.range n).find? fun x => (x != r) && hasCycleFromList n f x

/-- Boolean mask of vertices `y < n` in the `n`-step orbit of `x0` under `followParent f`. -/
@[expose] def cycleMaskList (n : ℕ) (f : List ℕ) (x0 : ℕ) : List Bool :=
  (List.range n).map fun y =>
    (List.range n).any fun k => (followParent f)^[k] x0 == y

/-- Subtraction-free sum `∑ y ∈ C \ {x}, c[y, f[y]]` for `x ∈ C`, and `0` outside `C`. -/
@[expose] def otherCycleCostList (n : ℕ) (c : List (List ℤ)) (f : List ℕ)
    (inCycle : List Bool) : List ℤ :=
  (List.range n).map fun x =>
    if inCycle.getD x false then
      (((List.range n).filter fun y => inCycle.getD y false && (y != x)).map fun y =>
        costAt c y (f.getD y 0)).sum
    else 0

/-- Best cycle vertex `y ∈ C` maximizing cheapness of `u → y` for each `u < n`. -/
@[expose] def bestEntryList (n : ℕ) (a : List (List Bool)) (c : List (List ℤ))
    (inCycle : List Bool) : List (Option ℕ) :=
  (List.range n).map fun u =>
    argMinRange n (fun y => inCycle.getD y false && adjAt a u y) (fun y => costAt c u y)

/-- Best exit vertex `x ∈ C` minimizing `c[x, w] + otherCycleCost[x]` for each `w < n`. -/
@[expose] def bestExitList (n : ℕ) (a : List (List Bool)) (c : List (List ℤ))
    (inCycle : List Bool) (other : List ℤ) : List (Option ℕ) :=
  (List.range n).map fun w =>
    argMinRange n (fun x => inCycle.getD x false && adjAt a x w)
      (fun x => costAt c x w + other.getD x 0)

/-- Contracted `n × n` adjacency table. -/
@[expose] def contractAdjList (n : ℕ) (inCycle : List Bool) (a : List (List Bool))
    (bEntry bExit : List (Option ℕ)) (x0 r : ℕ) : List (List Bool) :=
  (List.range n).map fun u =>
    (List.range n).map fun w =>
      if inCycle.getD u false then
        if u == x0 then !(inCycle.getD w false) && (bExit.getD w none).isSome
        else w == r
      else
        if inCycle.getD w false then (w == x0) && (bEntry.getD u none).isSome
        else adjAt a u w

/-- Contracted `n × n` subtraction-free integer cost table. -/
@[expose] def contractCostList (n : ℕ) (inCycle : List Bool) (c : List (List ℤ))
    (other : List ℤ) (bEntry bExit : List (Option ℕ)) (x0 : ℕ) : List (List ℤ) :=
  (List.range n).map fun u =>
    (List.range n).map fun w =>
      if inCycle.getD u false then
        if u == x0 then
          (bExit.getD w none).elim (costAt c u w) fun x => costAt c x w + other.getD x 0
        else 0
      else
        if w == x0 then
          (bEntry.getD u none).elim (costAt c u w) fun y => costAt c u y
        else costAt c u w

/-- Expand a contracted parent list `q` using one saved `ContractLevel`. -/
@[expose] def expandLevelList (lvl : ContractLevel) (q : List ℕ) : List ℕ :=
  let n := lvl.inCycle.length
  let qx0 := q.getD lvl.rep 0
  let bx := lvl.bestExit.getD qx0 none
  (List.range n).map fun v =>
    if lvl.inCycle.getD v false then
      bx.elim (lvl.parent.getD v 0) fun x => if v == x then qx0 else lvl.parent.getD v 0
    else if q.getD v 0 == lvl.rep then (lvl.bestEntry.getD v none).getD v
    else q.getD v 0

/-- Perform one cycle-contraction step given selected parent table `f` and cycle witness `x0`. -/
@[expose] def contractFromParent (s : ContractState) (f : List ℕ) (x0 : ℕ) : ContractState :=
  let n := s.adj.length
  let inCycle := cycleMaskList n f x0
  let other := otherCycleCostList n s.cost f inCycle
  let bEntry := bestEntryList n s.adj s.cost inCycle
  let bExit := bestExitList n s.adj s.cost inCycle other
  let a' := contractAdjList n inCycle s.adj bEntry bExit x0 s.root
  let c' := contractCostList n inCycle s.cost other bEntry bExit x0
  let lvl : ContractLevel := ⟨f, inCycle, bEntry, bExit, x0⟩
  ⟨a', c', s.root, false, none, lvl :: s.stack⟩

/-- Perform one step of the iterative forward contraction pass. -/
@[expose] def contractStep (s : ContractState) : ContractState :=
  if s.done then s
  else
    (selectParentsList s.adj s.cost s.root).elim
      ⟨s.adj, s.cost, s.root, true, none, s.stack⟩
      fun f =>
        (findCycleList s.adj.length s.root f).elim
          ⟨s.adj, s.cost, s.root, true, some f, s.stack⟩
          fun x0 => contractFromParent s f x0

/-- Iterative list-table Chu–Liu/Edmonds solver running `fuel` forward steps followed by stack
expansion. -/
@[expose] def edmondsTableAuxList (fuel r : ℕ) (a : List (List Bool)) (c : List (List ℤ)) :
    Option (List ℕ) :=
  let init : ContractState := ⟨a, c, r, false, none, []⟩
  let final := contractStep^[fuel] init
  final.result.map fun base => final.stack.foldl (fun q lvl => expandLevelList lvl q) base

/-- Normalize `inst.root` to a unary-bounded index (`0` when out of bounds). -/
@[expose] def clampedRoot (inst : ArborescenceInstance) : ℕ :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then inst.root else 0

/-- Solve minimum-cost spanning in-arborescence for `inst`, returning `none` if `root ≥ n` or no
spanning in-arborescence exists. -/
@[expose] def edmondsList (inst : ArborescenceInstance) : Option (List ℕ) :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then
    edmondsTableAuxList inst.adj.length (clampedRoot inst) inst.adj inst.cost
  else none

/-- Transpose an `n × n` Boolean matrix (`n = a.length`). -/
@[expose] def transposeBoolTable (a : List (List Bool)) : List (List Bool) :=
  let n := a.length
  (List.range n).map fun u => (List.range n).map fun w => adjAt a w u

/-- Transpose an `n × n` integer matrix (`c[w, u]` for `u, w < n`). -/
@[expose] def transposeIntTable (n : ℕ) (c : List (List ℤ)) : List (List ℤ) :=
  (List.range n).map fun u => (List.range n).map fun w => costAt c w u

/-- Solve minimum-cost spanning out-arborescence by reversing all arcs and costs. -/
@[expose] def edmondsOutList (inst : ArborescenceInstance) : Option (List ℕ) :=
  if decide ((inst.root : ℤ) < (inst.adj.length : ℤ)) then
    edmondsTableAuxList inst.adj.length (clampedRoot inst)
      (transposeBoolTable inst.adj) (transposeIntTable inst.adj.length inst.cost)
  else none

/-- Decision procedure for `minArborescenceDec`. -/
@[expose] def minArborescenceDecide (d : ArborescenceDecInstance) : Bool :=
  (edmondsList d.inst).elim false fun p =>
    let r := clampedRoot d.inst
    let n := d.inst.adj.length
    let total := (((List.range n).filter fun v => v != r).map fun v =>
      costAt d.inst.cost v (p.getD v 0)).sum
    decide (total ≤ d.threshold)

/-- Decision procedure for `minOutArborescenceDec`. -/
@[expose] def minOutArborescenceDecide (d : ArborescenceDecInstance) : Bool :=
  (edmondsOutList d.inst).elim false fun p =>
    let r := clampedRoot d.inst
    let n := d.inst.adj.length
    let total := (((List.range n).filter fun v => v != r).map fun v =>
      costAt d.inst.cost (p.getD v 0) v).sum
    decide (total ≤ d.threshold)

/-- `(n + 1) × (n + 1)` super-root adjacency matrix with reversed real arcs (`v < n, u < n`:
`adj[u, v]`) and fallback arcs `v → n` (`v < n`). -/
@[expose] def superRootAdjList (a : List (List Bool)) : List (List Bool) :=
  let n := a.length
  (List.range (n + 1)).map fun u =>
    (List.range (n + 1)).map fun w =>
      if u == n then false
      else if w == n then true
      else adjAt a w u

/-- `(n + 1) × (n + 1)` super-root cost matrix with negated reversed weights `-wt[w, u]` and `0`
on fallback arcs incident to vertex `n`. -/
@[expose] def superRootWeightList (n : ℕ) (wt : List (List ℤ)) : List (List ℤ) :=
  (List.range (n + 1)).map fun u =>
    (List.range (n + 1)).map fun w =>
      if u == n then 0
      else if w == n then 0
      else -costAt wt w u

/-- Optimum branching parent map on `0, …, n - 1` computed via Edmonds's super-root reduction
(`p[v] = v` denotes a root of a component tree). -/
@[expose] def optimumBranchingList (B : BranchingInstance) : List ℕ :=
  let n := B.adj.length
  let adj' := superRootAdjList B.adj
  let wt' := superRootWeightList n B.weight
  (edmondsTableAuxList (n + 1) n adj' wt').elim [] fun p =>
    (List.range n).map fun v =>
      let pv := p.getD v 0
      if pv == n then v else pv

/-- Decision procedure for `maxBranchingDec`. -/
@[expose] def maxBranchingDecide (d : BranchingDecInstance) : Bool :=
  let n := d.inst.adj.length
  let p := optimumBranchingList d.inst
  let total := (((List.range n).filter fun v => p.getD v 0 != v).map fun v =>
    costAt d.inst.weight (p.getD v 0) v).sum
  decide (d.threshold ≤ total)

/-! ### Polynomial-time certificates for list operations -/

private theorem length_encOption_unary_le {o : Option ℕ} {n : ℕ}
    (ho : ∀ x, o = some x → x ≤ n) :
    (encOption encUnary o).length ≤ n + 1 := by
  cases o with
  | none => simp
  | some x =>
    have hx := ho x rfl
    simp [encOption_some, encUnary_apply]
    omega

private theorem foldl_argMinStep_lt (pred : ℕ → Bool) (key : ℕ → ℤ) (n : ℕ) :
    ∀ (l : List ℕ), (∀ j ∈ l, j < n) →
      ∀ (acc : Option ℕ), (∀ cur, acc = some cur → cur < n) →
        ∀ res, l.foldl (argMinStep pred key) acc = some res → res < n
  | [], _, acc, hacc, res, hres => hacc res hres
  | j :: l, hl, acc, hacc, res, hres => by
    simp only [List.foldl_cons] at hres
    refine foldl_argMinStep_lt pred key n l (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      (argMinStep pred key acc j) (fun cur hcur => ?_) res hres
    have hj : j < n := hl j List.mem_cons_self
    unfold argMinStep at hcur
    split_ifs at hcur with hpred
    · cases acc with
      | none =>
        simp only [Option.elim_none, Option.some.injEq] at hcur
        exact hcur ▸ hj
      | some c =>
        simp only [Option.elim_some] at hcur
        split_ifs at hcur <;> simp only [Option.some.injEq] at hcur
        · exact hcur ▸ hj
        · exact hcur ▸ hacc c rfl
    · exact hacc cur hcur

private theorem computableInPolyTime_argMinRange {γ π : Type}
    {encIn : γ ↪ List Bool} {encPar : π ↪ List Bool}
    {par : γ → π} {bound : γ → ℕ} {pred : π → ℕ → Bool} {key : π → ℕ → ℤ}
    (hpar : ComputableInPolyTime par encIn encPar)
    (hbound : ComputableInPolyTime bound encIn encUnary)
    (hpred : ComputableInPolyTime (fun p : π × ℕ => pred p.1 p.2)
      (encPair encPar encUnary) encBool)
    (hkey : ComputableInPolyTime (fun p : π × ℕ => key p.1 p.2)
      (encPair encPar encUnary) encIntBin) :
    ComputableInPolyTime (fun x => argMinRange (bound x) (pred (par x)) (key (par x)))
      encIn (encOption encUnary) := by
  have hstep : ComputableInPolyTime
      (fun q : (π × Option ℕ) × ℕ =>
        let st := q.1
        argMinStep (pred st.1) (key st.1) st.2 q.2)
      (encPair (encPair encPar (encOption encUnary)) encUnary) (encOption encUnary) := by
    let Q := encPair (encPair encPar (encOption encUnary)) encUnary
    have hparq : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.1.1) Q encPar := by polytime
    have hacc : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.1.2) Q
        (encOption encUnary) := by
      polytime
    have hj : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => q.2) Q encUnary := by polytime
    have hcond : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => pred q.1.1 q.2) Q encBool :=
      hpred.comp (hparq.prod hj)
    have hsomej : ComputableInPolyTime (fun q : (π × Option ℕ) × ℕ => some q.2) Q
        (encOption encUnary) :=
      (optionSome encUnary).comp hj
    have hbody : ComputableInPolyTime
        (fun r : ((π × Option ℕ) × ℕ) × ℕ =>
          let q := r.1
          let st := q.1
          if decide (key st.1 q.2 < key st.1 r.2) then some q.2 else some r.2)
        (encPair Q encUnary) (encOption encUnary) := by
      have hrpar : ComputableInPolyTime
          (fun r : ((π × Option ℕ) × ℕ) × ℕ => r.1.1.1) (encPair Q encUnary) encPar :=
        hparq.comp (fst _ _)
      have hrj : ComputableInPolyTime
          (fun r : ((π × Option ℕ) × ℕ) × ℕ => r.1.2) (encPair Q encUnary) encUnary :=
        hj.comp (fst _ _)
      have hrcur : ComputableInPolyTime
          (fun r : ((π × Option ℕ) × ℕ) × ℕ => r.2) (encPair Q encUnary) encUnary :=
        snd _ _
      have hk1 : ComputableInPolyTime
          (fun r : ((π × Option ℕ) × ℕ) × ℕ => key r.1.1.1 r.1.2) (encPair Q encUnary) encIntBin :=
        hkey.comp (hrpar.prod hrj)
      have hk2 : ComputableInPolyTime
          (fun r : ((π × Option ℕ) × ℕ) × ℕ => key r.1.1.1 r.2) (encPair Q encUnary) encIntBin :=
        hkey.comp (hrpar.prod hrcur)
      exact ite (intBin_lt.comp (hk1.prod hk2)) ((optionSome encUnary).comp hrj)
        ((optionSome encUnary).comp hrcur)
    simpa only [argMinStep] using ite hcond (optionElimWithInput hacc hsomej hbody) hacc
  have hB : PolyBounded (fun x => (encIn x).length) (fun x => bound x + 1) := by
    obtain ⟨c, d, hcd⟩ := hbound.polyBounded.exists_le
    refine PolyBounded.of_forall_le (c + 1) d fun x => ?_
    have h1 := hcd x
    have hpow : 1 ≤ ((encIn x).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    nlinarith
  refine ComputableInPolyTime.foldlWith (encA := encUnary) (encB := encOption encUnary)
    (encL := encList encUnary) (encP := encPar)
    (par := par) (list := fun x => List.range (bound x)) (init := fun _ => none)
    (step := fun p acc j => argMinStep (pred p) (key p) acc j)
    hpar (by fun_prop) (const none) hstep hB (fun x i _ => ?_)
  refine length_encOption_unary_le fun res hres => Nat.le_of_lt ?_
  refine foldl_argMinStep_lt (pred (par x)) (key (par x)) (bound x)
    ((List.range (bound x)).take i) (fun j hj => ?_) none (fun _ h => by simp at h) res hres
  exact List.mem_range.mp (List.mem_of_mem_take hj)

private theorem computableInPolyTime_adjAt' {γ : Type} {encIn : γ ↪ List Bool}
    {a : γ → List (List Bool)} {u w : γ → ℕ}
    (ha : ComputableInPolyTime a encIn (encList (encList encBool)))
    (hu : ComputableInPolyTime u encIn encUnary)
    (hw : ComputableInPolyTime w encIn encUnary) :
    ComputableInPolyTime (fun x => adjAt (a x) (u x) (w x)) encIn encBool := by
  unfold adjAt
  exact listGetDWithInput (listGetDWithInput ha hu []) hw false

private theorem computableInPolyTime_costAt' {γ : Type} {encIn : γ ↪ List Bool}
    {c : γ → List (List ℤ)} {u w : γ → ℕ}
    (hc : ComputableInPolyTime c encIn (encList (encList encIntBin)))
    (hu : ComputableInPolyTime u encIn encUnary)
    (hw : ComputableInPolyTime w encIn encUnary) :
    ComputableInPolyTime (fun x => costAt (c x) (u x) (w x)) encIn encIntBin := by
  unfold costAt
  exact listGetDWithInput (listGetDWithInput hc hu []) hw 0

attribute [local fun_prop] computableInPolyTime_adjAt' computableInPolyTime_costAt'

private theorem computableInPolyTime_selectParentsState :
    ComputableInPolyTime
      (fun s : ContractState => selectParentsList s.adj s.cost s.root)
      encContractState (encOption (encList encUnary)) := by
  have harg : ComputableInPolyTime
      (fun q : ContractState × ℕ =>
        argMinRange q.1.adj.length (fun w => adjAt q.1.adj q.2 w && (w != q.2))
          (fun w => costAt q.1.cost q.2 w))
      (encPair encContractState encUnary) (encOption encUnary) := by
    exact computableInPolyTime_argMinRange (encPar := encPair encContractState encUnary)
      (par := fun q => q) (bound := fun q => q.1.adj.length)
      (pred := fun par w => adjAt par.1.adj par.2 w && (w != par.2))
      (key := fun par w => costAt par.1.cost par.2 w)
      (id' (encIn := encPair encContractState encUnary)) (by fun_prop) (by fun_prop)
      (by fun_prop)
  have hslen : ComputableInPolyTime (fun s : ContractState => s.adj.length)
      encContractState encUnary := by fun_prop
  have hopts : ComputableInPolyTime
      (fun s : ContractState =>
        (List.range s.adj.length).map fun v =>
          if v == s.root then some s.root
          else argMinRange s.adj.length (fun w => adjAt s.adj v w && (w != v))
            (fun w => costAt s.cost v w))
      encContractState (encList (encOption encUnary)) := by
    refine mapWithInput (range.comp hslen) ?_
    have hcond : ComputableInPolyTime (fun q : ContractState × ℕ => q.2 == q.1.root)
        (encPair encContractState encUnary) encBool := by fun_prop
    have hroot : ComputableInPolyTime (fun q : ContractState × ℕ => some q.1.root)
        (encPair encContractState encUnary) (encOption encUnary) := by fun_prop
    exact ite hcond hroot harg
  have hall : ComputableInPolyTime
      (fun s : ContractState =>
        ((List.range s.adj.length).map fun v =>
          if v == s.root then some s.root
          else argMinRange s.adj.length (fun w => adjAt s.adj v w && (w != v))
            (fun w => costAt s.cost v w)).all Option.isSome)
      encContractState encBool := by
    refine allWithInput hopts ?_
    exact optionIsSome (encB := encUnary) (snd _ _)
  have hmap : ComputableInPolyTime
      (fun s : ContractState =>
        some (((List.range s.adj.length).map fun v =>
          if v == s.root then some s.root
          else argMinRange s.adj.length (fun w => adjAt s.adj v w && (w != v))
            (fun w => costAt s.cost v w)).map fun o => o.getD 0))
      encContractState (encOption (encList encUnary)) := by
    refine (optionSome (encList encUnary)).comp (mapWithInput hopts ?_)
    exact optionGetDWithInput (snd encContractState (encOption encUnary)) (const 0)
  simpa only [selectParentsList] using ite hall hmap (const none)

private theorem followParent_iterate_le (f : List ℕ) (x : ℕ) :
    ∀ k, (followParent f)^[k] x ≤ max x (encList encUnary f).length
  | 0 => le_max_left _ _
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    set cur := (followParent f)^[k] x
    unfold followParent
    by_cases hlt : cur < f.length
    · rw [List.getD_eq_getElem _ _ hlt]
      have hlen : (encUnary f[cur]).length ≤ (encList encUnary f).length :=
        SizedListEncoding.length_elem_le f f[cur] (List.getElem_mem hlt)
      simp only [encUnary_apply, List.length_replicate] at hlen
      exact hlen.trans (le_max_right _ _)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]
      exact Nat.zero_le _

private theorem computableInPolyTime_followParent_iterate :
    ComputableInPolyTime
      (fun p : (List ℕ × ℕ) × ℕ => (followParent p.1.1)^[p.2] p.1.2)
      (encPair (encPair (encList encUnary) encUnary) encUnary) encUnary := by
  let E := encPair (encPair (encList encUnary) encUnary) encUnary
  have hstep : ComputableInPolyTime (fun q : List ℕ × ℕ => followParent q.1 q.2)
      (encPair (encList encUnary) encUnary) encUnary := by
    unfold followParent
    exact listGetDWithInput (fst (encList encUnary) encUnary) (snd (encList encUnary) encUnary) 0
  have hB : PolyBounded (fun p => (E p).length)
      (fun p => p.1.2 + (encList encUnary p.1.1).length) := by
    refine PolyBounded.of_forall_le 2 1 fun p => ?_
    have hxle : p.1.2 ≤ (E p).length := by
      have h := (length_le_encPair_right (encList encUnary) encUnary p.1).trans
        (length_le_encPair_left (encPair (encList encUnary) encUnary) encUnary p)
      simpa only [E, encUnary_apply, List.length_replicate] using h
    have hfle : (encList encUnary p.1.1).length ≤ (E p).length :=
      (length_le_encPair_left (encList encUnary) encUnary p.1).trans
        (length_le_encPair_left (encPair (encList encUnary) encUnary) encUnary p)
    have hpow : ((E p).length + 1) ^ 1 = (E p).length + 1 := pow_one _
    omega
  refine ComputableInPolyTime.iterateWith (by fun_prop) (by fun_prop) (by fun_prop) hstep hB
    (fun p i _ => ?_)
  simp only [encUnary_apply, List.length_replicate]
  exact (followParent_iterate_le p.1.1 p.1.2 i).trans (max_le (Nat.le_add_right _ _)
    (Nat.le_add_left _ _))

private theorem computableInPolyTime_hasCycleFromList :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => hasCycleFromList p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary) encBool := by
  unfold hasCycleFromList
  have hbound : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.1)
      (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary := by fun_prop
  refine anyWithInput (range.comp hbound) ?_
  have hqargs : ComputableInPolyTime
      (fun q : ((ℕ × List ℕ) × ℕ) × ℕ => ((q.1.1.2, q.1.2), q.2 + 1))
      (encPair (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary)
      (encPair (encPair (encList encUnary) encUnary) encUnary) := by fun_prop
  have hfn : ComputableInPolyTime
      (fun q : ((ℕ × List ℕ) × ℕ) × ℕ => (followParent q.1.1.2)^[q.2 + 1] q.1.2)
      (encPair (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary) encUnary :=
    computableInPolyTime_followParent_iterate.comp hqargs
  exact unary_beq' hfn (by fun_prop)

private theorem computableInPolyTime_findCycleList :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List ℕ => findCycleList p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) (encList encUnary)) (encOption encUnary) := by
  unfold findCycleList
  have hbound : ComputableInPolyTime (fun p : (ℕ × ℕ) × List ℕ => p.1.1)
      (encPair (encPair encUnary encUnary) (encList encUnary)) encUnary := by fun_prop
  refine findWithInput (range.comp hbound) ?_
  have hcargs : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
      (encPair (encPair (encPair encUnary encUnary) (encList encUnary)) encUnary)
      (encPair (encPair encUnary (encList encUnary)) encUnary) := by fun_prop
  exact bool_and' (by fun_prop) (computableInPolyTime_hasCycleFromList.comp hcargs)

private theorem computableInPolyTime_cycleMaskWork :
    ComputableInPolyTime
      (fun w : ContractWork => cycleMaskList w.state.adj.length w.parent w.rep)
      encContractWork (encList encBool) := by
  unfold cycleMaskList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  have hlen2 : ComputableInPolyTime (fun q : ContractWork × ℕ => q.1.state.adj.length)
      (encPair encContractWork encUnary) encUnary := by fun_prop
  refine anyWithInput (range.comp hlen2) ?_
  have hrargs : ComputableInPolyTime
      (fun r : (ContractWork × ℕ) × ℕ => ((r.1.1.parent, r.1.1.rep), r.2))
      (encPair (encPair encContractWork encUnary) encUnary)
      (encPair (encPair (encList encUnary) encUnary) encUnary) := by fun_prop
  have hfn : ComputableInPolyTime
      (fun r : (ContractWork × ℕ) × ℕ => (followParent r.1.1.parent)^[r.2] r.1.1.rep)
      (encPair (encPair encContractWork encUnary) encUnary) encUnary :=
    computableInPolyTime_followParent_iterate.comp hrargs
  exact unary_beq' hfn (by fun_prop)

private theorem computableInPolyTime_otherCycleCostWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        otherCycleCostList w.state.adj.length w.state.cost w.parent w.inCycle)
      encContractWork (encList encIntBin) := by
  unfold otherCycleCostList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  have hcond : ComputableInPolyTime
      (fun q : ContractWork × ℕ => q.1.inCycle.getD q.2 false)
      (encPair encContractWork encUnary) encBool := by fun_prop
  have hsum : ComputableInPolyTime
      (fun q : ContractWork × ℕ =>
        (((List.range q.1.state.adj.length).filter fun y =>
          q.1.inCycle.getD y false && (y != q.2)).map fun y =>
          costAt q.1.state.cost y (q.1.parent.getD y 0)).sum)
      (encPair encContractWork encUnary) encIntBin := by
    refine intBin_sum.comp ?_
    exact mapWithInput (filterWithInput (range.comp (by fun_prop)) (by fun_prop)) (by fun_prop)
  exact ite hcond hsum (const 0)

private theorem computableInPolyTime_bestEntryWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        bestEntryList w.state.adj.length w.state.adj w.state.cost w.inCycle)
      encContractWork (encList (encOption encUnary)) := by
  unfold bestEntryList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine computableInPolyTime_argMinRange (encPar := encPair encContractWork encUnary)
    (par := fun q => q) (bound := fun q => q.1.state.adj.length)
    (pred := fun par y => par.1.inCycle.getD y false && adjAt par.1.state.adj par.2 y)
    (key := fun par y => costAt par.1.state.cost par.2 y)
    (id' (encIn := encPair encContractWork encUnary)) (by fun_prop) (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_bestExitWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        bestExitList w.state.adj.length w.state.adj w.state.cost w.inCycle w.other)
      encContractWork (encList (encOption encUnary)) := by
  unfold bestExitList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine computableInPolyTime_argMinRange (encPar := encPair encContractWork encUnary)
    (par := fun q => q) (bound := fun q => q.1.state.adj.length)
    (pred := fun par x => par.1.inCycle.getD x false && adjAt par.1.state.adj x par.2)
    (key := fun par x => costAt par.1.state.cost x par.2 + par.1.other.getD x 0)
    (id' (encIn := encPair encContractWork encUnary)) (by fun_prop) (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_contractAdjWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        contractAdjList w.state.adj.length w.inCycle w.state.adj w.bestEntry w.bestExit
          w.rep w.state.root)
      encContractWork (encList (encList encBool)) := by
  unfold contractAdjList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  fun_prop

private theorem computableInPolyTime_contractCostWork :
    ComputableInPolyTime
      (fun w : ContractWork =>
        contractCostList w.state.adj.length w.inCycle w.state.cost w.other w.bestEntry
          w.bestExit w.rep)
      encContractWork (encList (encList encIntBin)) := by
  unfold contractCostList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  fun_prop

private theorem computableInPolyTime_contractFromParent :
    ComputableInPolyTime
      (fun p : (ContractState × List ℕ) × ℕ => contractFromParent p.1.1 p.1.2 p.2)
      (encPair (encPair encContractState (encList encUnary)) encUnary) encContractState := by
  have hw0 : ComputableInPolyTime
      (fun p : (ContractState × List ℕ) × ℕ => ContractWork.mk p.1.1 p.1.2 p.2 [] [] [] [])
      (encPair (encPair encContractState (encList encUnary)) encUnary) encContractWork := by
    polytime
  have hw1 : ComputableInPolyTime
      (fun w : ContractWork =>
        ContractWork.mk w.state w.parent w.rep
          (cycleMaskList w.state.adj.length w.parent w.rep) [] [] [])
      encContractWork encContractWork := by
    have hc := computableInPolyTime_cycleMaskWork
    polytime
  have hw2 : ComputableInPolyTime
      (fun w : ContractWork =>
        ContractWork.mk w.state w.parent w.rep w.inCycle
          (otherCycleCostList w.state.adj.length w.state.cost w.parent w.inCycle) [] [])
      encContractWork encContractWork := by
    have hc := computableInPolyTime_otherCycleCostWork
    polytime
  have hw3 : ComputableInPolyTime
      (fun w : ContractWork =>
        ContractWork.mk w.state w.parent w.rep w.inCycle w.other
          (bestEntryList w.state.adj.length w.state.adj w.state.cost w.inCycle) [])
      encContractWork encContractWork := by
    have hc := computableInPolyTime_bestEntryWork
    polytime
  have hw4 : ComputableInPolyTime
      (fun w : ContractWork =>
        ContractWork.mk w.state w.parent w.rep w.inCycle w.other w.bestEntry
          (bestExitList w.state.adj.length w.state.adj w.state.cost w.inCycle w.other))
      encContractWork encContractWork := by
    have hc := computableInPolyTime_bestExitWork
    polytime
  have hfin : ComputableInPolyTime
      (fun w : ContractWork =>
        let a' := contractAdjList w.state.adj.length w.inCycle w.state.adj w.bestEntry w.bestExit
          w.rep w.state.root
        let c' := contractCostList w.state.adj.length w.inCycle w.state.cost w.other w.bestEntry
          w.bestExit w.rep
        let lvl : ContractLevel := ⟨w.parent, w.inCycle, w.bestEntry, w.bestExit, w.rep⟩
        ContractState.mk a' c' w.state.root false none (lvl :: w.state.stack))
      encContractWork encContractState := by
    have ha' := computableInPolyTime_contractAdjWork
    have hc' := computableInPolyTime_contractCostWork
    polytime
  have hcomp := hfin.comp (hw4.comp (hw3.comp (hw2.comp (hw1.comp hw0))))
  simpa only [Function.comp_def, contractFromParent] using hcomp

private theorem computableInPolyTime_contractStep :
    ComputableInPolyTime contractStep encContractState encContractState := by
  have hsel := computableInPolyTime_selectParentsState
  have hstep : ComputableInPolyTime
      (fun s : ContractState =>
        if s.done then s
        else
          (selectParentsList s.adj s.cost s.root).elim
            ⟨s.adj, s.cost, s.root, true, none, s.stack⟩
            fun f =>
              (findCycleList s.adj.length s.root f).elim
                ⟨s.adj, s.cost, s.root, true, some f, s.stack⟩
                fun x0 => contractFromParent s f x0)
      encContractState encContractState := by
    have hdone : ComputableInPolyTime (fun s : ContractState => s.done)
        encContractState encBool := by fun_prop
    refine ite hdone (id' (encIn := encContractState)) ?_
    have helse1 : ComputableInPolyTime
        (fun s : ContractState => ContractState.mk s.adj s.cost s.root true none s.stack)
        encContractState encContractState := by fun_prop
    refine optionElimWithInput hsel helse1 ?_
    have hfcargs : ComputableInPolyTime
        (fun q : ContractState × List ℕ => ((q.1.adj.length, q.1.root), q.2))
        (encPair encContractState (encList encUnary))
        (encPair (encPair encUnary encUnary) (encList encUnary)) := by fun_prop
    have hcyc : ComputableInPolyTime
        (fun q : ContractState × List ℕ => findCycleList q.1.adj.length q.1.root q.2)
        (encPair encContractState (encList encUnary)) (encOption encUnary) :=
      computableInPolyTime_findCycleList.comp hfcargs
    have helse2 : ComputableInPolyTime
        (fun q : ContractState × List ℕ =>
          ContractState.mk q.1.adj q.1.cost q.1.root true (some q.2) q.1.stack)
        (encPair encContractState (encList encUnary)) encContractState := by fun_prop
    have hcfrom := computableInPolyTime_contractFromParent
    refine optionElimWithInput hcyc helse2 ?_
    exact hcfrom
  exact hstep.of_enc_eq fun s => by unfold contractStep; rfl

private theorem computableInPolyTime_expandLevelList :
    ComputableInPolyTime (fun p : List ℕ × ContractLevel => expandLevelList p.2 p.1)
      (encPair (encList encUnary) encContractLevel) (encList encUnary) := by
  unfold expandLevelList
  let E := encPair (encList encUnary) encContractLevel
  have hqx0 : ComputableInPolyTime (fun p : List ℕ × ContractLevel => p.1.getD p.2.rep 0)
      E encUnary := by fun_prop
  have hbx : ComputableInPolyTime
      (fun p : List ℕ × ContractLevel => p.2.bestExit.getD (p.1.getD p.2.rep 0) none)
      E (encOption encUnary) := by fun_prop
  have hlen : ComputableInPolyTime (fun p : List ℕ × ContractLevel => p.2.inCycle.length)
      E encUnary := by fun_prop
  refine mapWithInput (range.comp hlen) ?_
  have hcond1 : ComputableInPolyTime
      (fun q : (List ℕ × ContractLevel) × ℕ => q.1.2.inCycle.getD q.2 false)
      (encPair E encUnary) encBool := by fun_prop
  have hthen : ComputableInPolyTime
      (fun q : (List ℕ × ContractLevel) × ℕ =>
        (q.1.2.bestExit.getD (q.1.1.getD q.1.2.rep 0) none).elim (q.1.2.parent.getD q.2 0)
          fun x => if q.2 == x then q.1.1.getD q.1.2.rep 0 else q.1.2.parent.getD q.2 0)
      (encPair E encUnary) encUnary := by
    have hfb : ComputableInPolyTime
        (fun q : (List ℕ × ContractLevel) × ℕ => q.1.2.parent.getD q.2 0)
        (encPair E encUnary) encUnary := by fun_prop
    refine optionElimWithInput (hbx.comp (fst _ _)) hfb ?_
    have hbeq : ComputableInPolyTime
        (fun r : ((List ℕ × ContractLevel) × ℕ) × ℕ => r.1.2 == r.2)
        (encPair (encPair E encUnary) encUnary) encBool := by fun_prop
    have hr1 : ComputableInPolyTime
        (fun r : ((List ℕ × ContractLevel) × ℕ) × ℕ => r.1.1.1.getD r.1.1.2.rep 0)
        (encPair (encPair E encUnary) encUnary) encUnary := by fun_prop
    have hr2 : ComputableInPolyTime
        (fun r : ((List ℕ × ContractLevel) × ℕ) × ℕ => r.1.1.2.parent.getD r.1.2 0)
        (encPair (encPair E encUnary) encUnary) encUnary := by fun_prop
    exact ite hbeq hr1 hr2
  have helse : ComputableInPolyTime
      (fun q : (List ℕ × ContractLevel) × ℕ =>
        if q.1.1.getD q.2 0 == q.1.2.rep then (q.1.2.bestEntry.getD q.2 none).getD q.2
        else q.1.1.getD q.2 0)
      (encPair E encUnary) encUnary := by
    have hcond2 : ComputableInPolyTime
        (fun q : (List ℕ × ContractLevel) × ℕ => q.1.1.getD q.2 0 == q.1.2.rep)
        (encPair E encUnary) encBool := by fun_prop
    have hopt : ComputableInPolyTime
        (fun q : (List ℕ × ContractLevel) × ℕ => q.1.2.bestEntry.getD q.2 none)
        (encPair E encUnary) (encOption encUnary) := by fun_prop
    have hdef : ComputableInPolyTime (fun q : (List ℕ × ContractLevel) × ℕ => q.2)
        (encPair E encUnary) encUnary := by fun_prop
    have hbe : ComputableInPolyTime
        (fun q : (List ℕ × ContractLevel) × ℕ => (q.1.2.bestEntry.getD q.2 none).getD q.2)
        (encPair E encUnary) encUnary :=
      optionGetDWithInput hopt hdef
    have hfb : ComputableInPolyTime
        (fun q : (List ℕ × ContractLevel) × ℕ => q.1.1.getD q.2 0)
        (encPair E encUnary) encUnary := by fun_prop
    exact ite hcond2 hbe hfb
  exact ite hcond1 hthen helse

/-! ### Bit-length invariant and polynomial-time certificate for `edmondsTableAuxList` -/

private theorem maxNatAbsRow_le (row : List ℤ) :
    ∀ acc z, z ∈ row → z.natAbs ≤ row.foldl (fun m (x : ℤ) => max m x.natAbs) acc := by
  induction row with
  | nil => intro _ _ h; simp at h
  | cons a t ih =>
    intro acc z hz
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hz with rfl | ht
    · have hmono : ∀ (l : List ℤ) u,
          u ≤ l.foldl (fun m (x : ℤ) => max m x.natAbs) u := by
        intro l
        induction l with
        | nil => intro u; exact le_rfl
        | cons y ys ih2 =>
          intro u
          exact (le_max_left _ _).trans (ih2 _)
      exact (le_max_right _ _).trans (hmono t _)
    · exact ih _ _ ht

private theorem maxNatAbsTable_le (c : List (List ℤ)) :
    ∀ acc row z, row ∈ c → z ∈ row →
      z.natAbs ≤ c.foldl (fun m r => r.foldl (fun k (x : ℤ) => max k x.natAbs) m) acc := by
  induction c with
  | nil => intro _ _ _ h; simp at h
  | cons r rs ih =>
    intro acc row z hrow hz
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hrow with rfl | hrs
    · have hmono : ∀ (l : List (List ℤ)) u,
          u ≤ l.foldl (fun m r => r.foldl (fun k (x : ℤ) => max k x.natAbs) m) u := by
        intro l
        induction l with
        | nil => intro u; exact le_rfl
        | cons y ys ih2 =>
          intro u
          have h1 : u ≤ y.foldl (fun k (x : ℤ) => max k x.natAbs) u := by
            clear ih2
            induction y generalizing u with
            | nil => exact le_rfl
            | cons a as ihy => exact (le_max_left _ _).trans (ihy _)
          exact h1.trans (ih2 _)
      exact (maxNatAbsRow_le row acc z hz).trans (hmono rs _)
    · exact ih _ row z hrs hz

private theorem maxNatAbsRow_size_le (B : ℕ) :
    ∀ (r : List ℤ), (∀ z ∈ r, z.natAbs.size ≤ B) →
      ∀ (acc : ℕ), acc.size ≤ B →
        (r.foldl (fun k (x : ℤ) => max k x.natAbs) acc).size ≤ B
  | [], _, acc, hacc => hacc
  | a :: t, hrow, acc, hacc => by
    simp only [List.foldl_cons]
    refine maxNatAbsRow_size_le B t (fun z hz => hrow z (List.mem_cons_of_mem _ hz)) _ ?_
    have ha : a.natAbs.size ≤ B := hrow a List.mem_cons_self
    rcases le_total acc a.natAbs with h | h
    · rw [max_eq_right h]; exact ha
    · rw [max_eq_left h]; exact hacc

private theorem maxNatAbsTable_size_le (c : List (List ℤ)) (B : ℕ)
    (hB : ∀ row ∈ c, ∀ z ∈ row, z.natAbs.size ≤ B) :
    ∀ (acc : ℕ), acc.size ≤ B →
      (c.foldl (fun m r => r.foldl (fun k (x : ℤ) => max k x.natAbs) m) acc).size ≤ B := by
  induction c with
  | nil => intro acc h; exact h
  | cons r rs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    refine ih (fun row hr z hz => hB row (List.mem_cons_of_mem _ hr) z hz) _ ?_
    exact maxNatAbsRow_size_le B r (hB r List.mem_cons_self) acc hacc

private theorem costAt_natAbs_le {c : List (List ℤ)} {M : ℕ}
    (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (u w : ℕ) : (costAt c u w).natAbs ≤ M := by
  unfold costAt
  by_cases hu : u < c.length
  · rw [List.getD_eq_getElem _ _ hu]
    have hrow := List.getElem_mem hu
    by_cases hw : w < c[u].length
    · rw [List.getD_eq_getElem _ _ hw]
      exact hc c[u] hrow c[u][w] (List.getElem_mem hw)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hw)]
      exact Nat.zero_le _
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hu), List.getD_nil]
    exact Nat.zero_le _

private theorem list_sum_natAbs_le {M : ℕ} :
    ∀ l : List ℤ, (∀ z ∈ l, z.natAbs ≤ M) → l.sum.natAbs ≤ l.length * M
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have ha := h a List.mem_cons_self
    have hl := list_sum_natAbs_le l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact (Int.natAbs_add_le _ _).trans ((Nat.add_le_add ha hl).trans_eq (Nat.add_comm _ _))

private theorem otherCycleCostList_natAbs_le {n : ℕ} {c : List (List ℤ)} {f : List ℕ}
    {inCycle : List Bool} {M : ℕ} (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (x : ℕ) :
    ((otherCycleCostList n c f inCycle).getD x 0).natAbs ≤ n * M := by
  have hlen : (otherCycleCostList n c f inCycle).length = n := by
    simp [otherCycleCostList]
  by_cases hx : x < n
  · rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hx)]
    unfold otherCycleCostList
    rw [List.getElem_map, List.getElem_range]
    split_ifs
    · have hs := list_sum_natAbs_le
          (((List.range n).filter fun z => inCycle.getD z false && (z != x)).map fun z =>
            costAt c z (f.getD z 0)) (fun v hv => by
        obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
        exact costAt_natAbs_le hc z _)
      rw [List.length_map] at hs
      have hfl : ((List.range n).filter fun z => inCycle.getD z false && (z != x)).length ≤ n :=
        (List.length_filter_le _ _).trans (by simp)
      exact hs.trans (Nat.mul_le_mul_right M hfl)
    · exact Nat.zero_le _
  · rw [List.getD_eq_default _ _ (by rw [hlen]; exact Nat.le_of_not_lt hx)]
    exact Nat.zero_le _

private theorem contractCostList_natAbs_le {n : ℕ} {inCycle : List Bool} {c : List (List ℤ)}
    {other : List ℤ} {bEntry bExit : List (Option ℕ)} {x0 M : ℕ}
    (hc : ∀ row ∈ c, ∀ z ∈ row, z.natAbs ≤ M) (ho : ∀ x, (other.getD x 0).natAbs ≤ n * M) :
    ∀ row ∈ contractCostList n inCycle c other bEntry bExit x0,
      ∀ z ∈ row, z.natAbs ≤ (n + 1) * M := by
  intro row hrow z hz
  unfold contractCostList at hrow
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz
  split_ifs
  · cases bExit.getD w none with
    | none => exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
    | some x =>
      exact (Int.natAbs_add_le _ _).trans
        (by simpa [Nat.succ_mul, Nat.add_comm] using
          Nat.add_le_add (costAt_natAbs_le hc x w) (ho x))
  · exact Nat.zero_le _
  · cases bEntry.getD u none with
    | none => exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
    | some y => exact (costAt_natAbs_le hc u y).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
  · exact (costAt_natAbs_le hc u w).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))

private theorem encListBool_table_le (a : List (List Bool)) (n : ℕ)
    (h1 : a.length ≤ n) (h2 : ∀ r ∈ a, r.length ≤ n) :
    (encList (encList encBool) a).length ≤ n * (6 * n + 1) := by
  have hle := length_encList_le (encList encBool) a (b := 3 * n) fun r hr => by
    have hr1 := length_encList_le encBool r (b := 1) fun b _ => by simp [encBool_apply]
    have hr2 := h2 r hr
    nlinarith
  nlinarith

private theorem encListUnary_le (l : List ℕ) (n B : ℕ)
    (h1 : l.length ≤ n) (h2 : ∀ x ∈ l, x ≤ B) :
    (encList encUnary l).length ≤ n * (2 * B + 1) := by
  refine (length_encList_le encUnary l (b := B) fun x hx => ?_).trans
    (Nat.mul_le_mul_right _ h1)
  simpa [encUnary_apply] using h2 x hx

private theorem encListOptUnary_le (l : List (Option ℕ)) (n B : ℕ)
    (h1 : l.length ≤ n) (h2 : ∀ o ∈ l, ∀ x, o = some x → x ≤ B) :
    (encList (encOption encUnary) l).length ≤ n * (2 * (B + 1) + 1) :=
  (length_encList_le (encOption encUnary) l (b := B + 1) fun o ho =>
    length_encOption_unary_le (h2 o ho)).trans (Nat.mul_le_mul_right _ h1)

private structure StateBoundInv (x : TableAuxInput) (M₀ i : ℕ) (s : ContractState) : Prop where
  adj_len : s.adj.length = x.adj.length
  root_eq : s.root = x.root
  adj_code : (encList (encList encBool) s.adj).length ≤
    (encList (encList encBool) x.adj).length + x.adj.length * (6 * x.adj.length + 1)
  cost_abs : ∀ row ∈ s.cost, ∀ z ∈ row, z.natAbs ≤ (x.adj.length + 1) ^ i * M₀
  cost_rows : s.cost = x.cost ∨
    (s.cost.length = x.adj.length ∧ ∀ row ∈ s.cost, row.length = x.adj.length)
  result_bound : ∀ f, s.result = some f →
    f.length ≤ x.adj.length ∧ ∀ v ∈ f, v ≤ max x.root x.adj.length
  stack_len : s.stack.length ≤ i
  stack_bound : ∀ lvl ∈ s.stack,
    lvl.parent.length ≤ x.adj.length ∧ (∀ v ∈ lvl.parent, v ≤ max x.root x.adj.length) ∧
    lvl.inCycle.length ≤ x.adj.length ∧
    lvl.bestEntry.length ≤ x.adj.length ∧
    (∀ o ∈ lvl.bestEntry, ∀ v, o = some v → v ≤ x.adj.length) ∧
    lvl.bestExit.length ≤ x.adj.length ∧ (∀ o ∈ lvl.bestExit, ∀ v, o = some v → v ≤ x.adj.length) ∧
    lvl.rep ≤ x.adj.length

private theorem selectParentsList_bound (a : List (List Bool)) (c : List (List ℤ)) (r : ℕ)
    (f : List ℕ) (hf : selectParentsList a c r = some f) :
    f.length = a.length ∧ ∀ v ∈ f, v ≤ max r a.length := by
  unfold selectParentsList at hf
  dsimp only at hf
  split_ifs at hf with hall
  · obtain rfl := Option.some_injective _ hf
    simp only [List.length_map, List.length_range, true_and]
    intro v hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp ho
    rw [List.mem_range] at hidx
    split_ifs
    · simp
    · cases harg : argMinRange a.length (fun w => adjAt a idx w && (w != idx))
          (fun w => costAt c idx w) with
      | none => simp
      | some w =>
        have hlt := foldl_argMinStep_lt (fun w => adjAt a idx w && (w != idx))
          (fun w => costAt c idx w) a.length (List.range a.length)
          (fun j hj => List.mem_range.mp hj) none (fun _ h => by simp at h) w harg
        exact (Nat.le_of_lt hlt).trans (le_max_right _ _)

private theorem findCycleList_lt (n r : ℕ) (f : List ℕ) (x0 : ℕ)
    (h : findCycleList n r f = some x0) : x0 < n := by
  have hmem := List.mem_of_find?_eq_some h
  exact List.mem_range.mp hmem

/-- Shared bound for `bestEntryList` and `bestExitList`: a row of `n` arg-min lookups over
`List.range n` has length `n` and entries at most `n`. -/
private theorem argMinRangeList_bound (n : ℕ) (pred : ℕ → ℕ → Bool) (key : ℕ → ℕ → ℤ) :
    ((List.range n).map fun u => argMinRange n (pred u) (key u)).length = n ∧
      ∀ o ∈ (List.range n).map (fun u => argMinRange n (pred u) (key u)), ∀ v, o = some v →
        v ≤ n := by
  refine ⟨by simp, fun o ho v hv => ?_⟩
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp ho
  exact Nat.le_of_lt (foldl_argMinStep_lt _ _ n (List.range n)
    (fun j hj => List.mem_range.mp hj) none (fun _ h => by simp at h) v hv)

private theorem stateBoundInv_step (x : TableAuxInput) (M₀ i : ℕ) {s : ContractState}
    (hs : StateBoundInv x M₀ i s) :
    StateBoundInv x M₀ (i + 1) (contractStep s) := by
  have hmono_cost : ∀ row ∈ s.cost, ∀ z ∈ row, z.natAbs ≤ (x.adj.length + 1) ^ (i + 1) * M₀ :=
    fun row hr z hz => (hs.cost_abs row hr z hz).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ i)))
  unfold contractStep
  split_ifs with hdone
  · exact ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono_cost, hs.cost_rows, hs.result_bound,
      hs.stack_len.trans (Nat.le_succ i), hs.stack_bound⟩
  · cases hsel : selectParentsList s.adj s.cost s.root with
    | none =>
      simp only [Option.elim_none]
      exact ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono_cost, hs.cost_rows, fun _ h => by simp at h,
        hs.stack_len.trans (Nat.le_succ i), hs.stack_bound⟩
    | some f =>
      have hf := selectParentsList_bound s.adj s.cost s.root f hsel
      rw [hs.adj_len, hs.root_eq] at hf
      cases hcyc : findCycleList s.adj.length s.root f with
      | none =>
        simp only [Option.elim_some, hcyc, Option.elim_none]
        refine ⟨hs.adj_len, hs.root_eq, hs.adj_code, hmono_cost, hs.cost_rows, fun g hg => ?_,
          hs.stack_len.trans (Nat.le_succ i), hs.stack_bound⟩
        obtain rfl := Option.some_injective _ hg
        exact ⟨hf.1.le, hf.2⟩
      | some x0 =>
        simp only [Option.elim_some, hcyc]
        have hx0 : x0 ≤ x.adj.length := Nat.le_of_lt (hs.adj_len ▸ findCycleList_lt _ _ _ _ hcyc)
        dsimp only [contractFromParent]
        set n := s.adj.length
        have hn : n = x.adj.length := hs.adj_len
        set inCycle := cycleMaskList n f x0
        set other := otherCycleCostList n s.cost f inCycle
        set bEntry := bestEntryList n s.adj s.cost inCycle
        set bExit := bestExitList n s.adj s.cost inCycle other
        set a' := contractAdjList n inCycle s.adj bEntry bExit x0 s.root
        set c' := contractCostList n inCycle s.cost other bEntry bExit x0
        have ha'_len : a'.length = x.adj.length := by simp [a', contractAdjList, hn]
        have ha'_code : (encList (encList encBool) a').length ≤
            (encList (encList encBool) x.adj).length + x.adj.length * (6 * x.adj.length + 1) := by
          refine (encListBool_table_le a' x.adj.length ha'_len.le fun r hr => ?_).trans
            (Nat.le_add_left _ _)
          obtain ⟨u, -, rfl⟩ := List.mem_map.mp hr
          simp [hn]
        have hc'_abs : ∀ row ∈ c', ∀ z ∈ row,
            z.natAbs ≤ (x.adj.length + 1) ^ (i + 1) * M₀ := by
          intro row hrow z hz
          have hcb := contractCostList_natAbs_le (n := n) (inCycle := inCycle)
            (other := other) (bEntry := bEntry) (bExit := bExit) (x0 := x0)
            hs.cost_abs (otherCycleCostList_natAbs_le hs.cost_abs) row hrow z hz
          rw [hn] at hcb
          simpa [pow_succ', Nat.mul_assoc] using hcb
        have hc'_rows : c'.length = x.adj.length ∧ ∀ row ∈ c', row.length = x.adj.length := by
          refine ⟨by simp [c', contractCostList, hn], fun row hr => ?_⟩
          obtain ⟨u, -, rfl⟩ := List.mem_map.mp hr
          simp [hn]
        have hbe := argMinRangeList_bound n (pred := fun u y => inCycle.getD y false &&
          adjAt s.adj u y) (key := fun u y => costAt s.cost u y)
        have hbx := argMinRangeList_bound n (pred := fun w x => inCycle.getD x false &&
          adjAt s.adj x w) (key := fun w x => costAt s.cost x w + other.getD x 0)
        refine ⟨ha'_len, hs.root_eq, ha'_code, hc'_abs, Or.inr hc'_rows,
          fun _ h => by simp at h, Nat.succ_le_succ hs.stack_len, fun lvl hlvl => ?_⟩
        rcases List.mem_cons.mp hlvl with rfl | hlvl'
        · refine ⟨hf.1.le, hf.2, by simp [inCycle, cycleMaskList, hn],
            hn ▸ hbe.1.le, fun o ho v hv => (hn ▸ hbe.2 o ho v hv),
            hn ▸ hbx.1.le, fun o ho v hv => (hn ▸ hbx.2 o ho v hv), hx0⟩
        · exact hs.stack_bound lvl hlvl'

private theorem stateBoundInv_iterate (x : TableAuxInput) :
    let M₀ := x.cost.foldl (fun m r => r.foldl (fun k (z : ℤ) => max k z.natAbs) m) 0
    ∀ i, StateBoundInv x M₀ i (contractStep^[i] ⟨x.adj, x.cost, x.root, false, none, []⟩)
  | 0 => by
    refine ⟨rfl, rfl, Nat.le_add_right _ _, fun row hr z hz => ?_, Or.inl rfl,
      fun _ h => by simp at h, le_rfl, fun _ h => by simp at h⟩
    simpa only [pow_zero, one_mul] using maxNatAbsTable_le x.cost 0 row z hr hz
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact stateBoundInv_step x _ i (stateBoundInv_iterate x i)

theorem computableInPolyTime_edmondsTableAuxList :
    ComputableInPolyTime
      (fun x : TableAuxInput => edmondsTableAuxList x.fuel x.root x.adj x.cost)
      encTableAuxInput encParentOption := by
  let polyB : TableAuxInput → ℕ := fun x =>
    let L := (encTableAuxInput x).length
    let sAdj := L + L * (6 * L + 1)
    let sCost := L + L * (2 * (L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) + 1)
    let sRes := 1 + L * (2 * L + 1)
    let sLvl := 2 * (L * (2 * L + 1)) + 1 + (2 * (3 * L) + 1 +
      (2 * (L * (2 * (L + 1) + 1)) + 1 + (2 * (L * (2 * (L + 1) + 1)) + 1 + L)))
    let sStack := L * (2 * sLvl + 1)
    2 * sAdj + 1 + (2 * sCost + 1 + (2 * L + 1 + (2 * 1 + 1 + (2 * sRes + 1 + sStack))))
  have hpoly : PolyBounded (fun x => (encTableAuxInput x).length) polyB := by
    dsimp only [polyB]
    refine PolyBounded.of_forall_le 1000 4 fun x => ?_
    set L := (encTableAuxInput x).length
    rw [show 1000 * (L + 1) ^ 4 =
        1000 + 4000 * L + 6000 * L ^ 2 + 4000 * L ^ 3 + 1000 * L ^ 4 by ring]
    ring_nf
    omega
  have hiter : ComputableInPolyTime
      (fun x : TableAuxInput => contractStep^[x.fuel] ⟨x.adj, x.cost, x.root, false, none, []⟩)
      encTableAuxInput encContractState := by
    refine ComputableInPolyTime.iterate (by polytime) (by polytime)
      computableInPolyTime_contractStep hpoly (fun x i hi => ?_)
    set L := (encTableAuxInput x).length
    set M₀ := x.cost.foldl (fun m r => r.foldl (fun k (z : ℤ) => max k z.natAbs) m) 0
    have hinv := stateBoundInv_iterate x i
    have hlen_in : L = 2 * x.fuel + 1 + (2 * x.root + 1 +
        (2 * (encList (encList encBool) x.adj).length + 1 +
          (encList (encList encIntBin) x.cost).length)) := by
      dsimp only [L]
      rw [encTableAuxInput_apply, length_encPair, length_encPair, length_encPair]
      simp [encUnary_apply]
    have hfuel : x.fuel ≤ L := by omega
    have hroot : x.root ≤ L := by omega
    have hadj_in : (encList (encList encBool) x.adj).length ≤ L := by omega
    have hcost_in : (encList (encList encIntBin) x.cost).length ≤ L := by omega
    have hn : x.adj.length ≤ L :=
      (SizedListEncoding.length_le (encA := encList encBool)
        (encL := encList (encList encBool)) x.adj).trans hadj_in
    have hM0_size : M₀.size ≤ L := by
      refine maxNatAbsTable_size_le x.cost L (fun row hrow z hz => ?_) 0 (by simp)
      have h1 : (encIntBin z).length ≤ (encList encIntBin row).length :=
        SizedListEncoding.length_elem_le row z hz
      have h2 : (encList encIntBin row).length ≤ (encList (encList encIntBin) x.cost).length :=
        SizedListEncoding.length_elem_le x.cost row hrow
      rw [length_encIntBin] at h1
      omega
    set s := contractStep^[i] ⟨x.adj, x.cost, x.root, false, none, []⟩
    have hadj_code : (encList (encList encBool) s.adj).length ≤ L + L * (6 * L + 1) := by
      refine hinv.adj_code.trans (Nat.add_le_add hadj_in ?_)
      exact Nat.mul_le_mul hn (by omega)
    have hcost_code : (encList (encList encIntBin) s.cost).length ≤
        L + L * (2 * (L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) + 1) := by
      rcases hinv.cost_rows with heq_cost | ⟨hrows_len, hrows_each⟩
      · rw [heq_cost]
        exact hcost_in.trans (Nat.le_add_right _ _)
      · have hc_rows : (encList (encList encIntBin) s.cost).length ≤
            L * (2 * (L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) + 1) := by
          refine (length_encList_le (encList encIntBin) s.cost
              (b := L * (2 * (L * (L + 1) + 1 + L + 1) + 1)) fun row hrow => ?_).trans
            (Nat.mul_le_mul_right _ (hrows_len ▸ hn))
          refine (length_encList_le encIntBin row
              (b := L * (L + 1) + 1 + L + 1) fun z hz => ?_).trans
            (Nat.mul_le_mul_right _ (hrows_each row hrow ▸ hn))
          rw [length_encIntBin]
          have habs := hinv.cost_abs row hrow z hz
          have hs1 : z.natAbs.size ≤ ((x.adj.length + 1) ^ i * M₀).size := Nat.size_le_size habs
          have hs2 : ((x.adj.length + 1) ^ i * M₀).size ≤
              ((x.adj.length + 1) ^ i).size + M₀.size := Nat.size_mul_le _ _
          have hs3 : ((x.adj.length + 1) ^ i).size ≤ i * (x.adj.length + 1).size + 1 :=
            Nat.size_pow_le _ _
          have hs4 : (x.adj.length + 1).size ≤ L + 1 := (Nat.size_le_self _).trans (by omega)
          have hmul : i * (x.adj.length + 1).size ≤ L * (L + 1) :=
            Nat.mul_le_mul (hi.trans hfuel) hs4
          omega
        exact hc_rows.trans (Nat.le_add_left _ _)
    have hroot_code : (encUnary s.root).length ≤ L := by
      simpa [encUnary_apply, hinv.root_eq] using hroot
    have hdone_code : (encBool s.done).length = 1 := by simp [encBool_apply]
    have hres_code : (encOption (encList encUnary) s.result).length ≤ 1 + L * (2 * L + 1) := by
      cases hr : s.result with
      | none => simp
      | some f =>
        simp only [encOption_some, List.length_cons]
        have hf := hinv.result_bound f hr
        have hlen := encListUnary_le f L L (hf.1.trans hn) fun v hv =>
          (hf.2 v hv).trans (max_le hroot hn)
        omega
    have hstack_code : (encList encContractLevel s.stack).length ≤
        L * (2 * (2 * (L * (2 * L + 1)) + 1 + (2 * (3 * L) + 1 +
          (2 * (L * (2 * (L + 1) + 1)) + 1 +
          (2 * (L * (2 * (L + 1) + 1)) + 1 + L)))) + 1) := by
      refine (length_encList_le encContractLevel s.stack fun lvl hlvl => ?_).trans
        (Nat.mul_le_mul_right _ (hinv.stack_len.trans (hi.trans hfuel)))
      obtain ⟨hp1, hp2, hic, hbe1, hbe2, hbx1, hbx2, hrep⟩ := hinv.stack_bound lvl hlvl
      rw [encContractLevel_apply, length_encPair, length_encPair, length_encPair, length_encPair]
      dsimp only
      have c1 := encListUnary_le lvl.parent L L (hp1.trans hn) fun v hv =>
        (hp2 v hv).trans (max_le hroot hn)
      have c2 : (encList encBool lvl.inCycle).length ≤ 3 * L := by
        refine (length_encList_le encBool lvl.inCycle (b := 1) fun _ _ =>
          by simp [encBool_apply]).trans ?_
        have := hic.trans hn
        omega
      have c3 := encListOptUnary_le lvl.bestEntry L L (hbe1.trans hn) fun o ho v hv =>
        (hbe2 o ho v hv).trans hn
      have c4 := encListOptUnary_le lvl.bestExit L L (hbx1.trans hn) fun o ho v hv =>
        (hbx2 o ho v hv).trans hn
      have c5 : (encUnary lvl.rep).length ≤ L := by
        simpa [encUnary_apply] using hrep.trans hn
      omega
    rw [encContractState_apply, length_encPair, length_encPair, length_encPair, length_encPair,
      length_encPair]
    dsimp only
    dsimp only [L] at hadj_code hcost_code hroot_code hres_code hstack_code
    dsimp only [polyB, encAdjTable, encIntTable, encParentOption]
    omega
  have hfin : ComputableInPolyTime
      (fun x : TableAuxInput =>
        let final := contractStep^[x.fuel] ⟨x.adj, x.cost, x.root, false, none, []⟩
        final.result.map fun base => final.stack.foldl (fun q lvl => expandLevelList lvl q) base)
      encTableAuxInput (encOption (encList encUnary)) := by
    refine optionMapWithInput (by polytime) ?_
    have hfold : ComputableInPolyTime
        (fun p : TableAuxInput × List ℕ =>
          let final := contractStep^[p.1.fuel] ⟨p.1.adj, p.1.cost, p.1.root, false, none, []⟩
          final.stack.foldl (fun q lvl => expandLevelList lvl q) p.2)
        (encPair encTableAuxInput (encList encUnary)) (encList encUnary) := by
      have hstep_fold : ComputableInPolyTime
          (fun q : List ℕ × ContractLevel => expandLevelList q.2 q.1)
          (encPair (encList encUnary) encContractLevel) (encList encUnary) :=
        computableInPolyTime_expandLevelList
      have hlist_f : ComputableInPolyTime
          (fun p : TableAuxInput × List ℕ =>
            (contractStep^[p.1.fuel] ⟨p.1.adj, p.1.cost, p.1.root, false, none, []⟩).stack)
          (encPair encTableAuxInput (encList encUnary)) (encList encContractLevel) := by
        have := hiter.comp (fst encTableAuxInput (encList encUnary))
        polytime
      have hB : PolyBounded (fun p : TableAuxInput × List ℕ =>
          (encPair encTableAuxInput (encList encUnary) p).length)
          (fun p => let L := (encTableAuxInput p.1).length
            let M := (encList encUnary p.2).length
            max M (L * (2 * (M + L) + 1))) := by
        refine PolyBounded.of_forall_le 4 2 fun p => ?_
        rw [length_encPair]
        set L := (encTableAuxInput p.1).length
        set M := (encList encUnary p.2).length
        have _ : 1 ≤ (2 * L + 1 + M + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
        rcases le_total M (L * (2 * (M + L) + 1)) with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
      refine ComputableInPolyTime.foldl' (encA := encContractLevel) (encB := encList encUnary)
        (encL := encList encContractLevel)
        hlist_f (snd _ _) hstep_fold hB (fun p k hk => ?_)
      set x := p.1
      set base := p.2
      have hinv := stateBoundInv_iterate x x.fuel
      set final := contractStep^[x.fuel] ⟨x.adj, x.cost, x.root, false, none, []⟩
      have hlen_in : (encTableAuxInput x).length = 2 * x.fuel + 1 + (2 * x.root + 1 +
          (2 * (encList (encList encBool) x.adj).length + 1 +
            (encList (encList encIntBin) x.cost).length)) := by
        rw [encTableAuxInput_apply, length_encPair, length_encPair, length_encPair]
        simp [encUnary_apply]
      have hL_adj : x.adj.length ≤ (encTableAuxInput x).length := by
        have h1 := SizedListEncoding.length_le (encA := encList encBool)
          (encL := encList (encList encBool)) x.adj
        omega
      have hL_root : x.root ≤ (encTableAuxInput x).length := by omega
      have hbase_len : base.length ≤ (encList encUnary base).length :=
        SizedListEncoding.length_le (encA := encUnary) (encL := encList encUnary) base
      have hbase_elem : ∀ v ∈ base, v ≤ (encList encUnary base).length := fun v hv => by
        have h := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
          base v hv
        simpa [encUnary_apply] using h
      set B_val := (encList encUnary base).length + (encTableAuxInput x).length
      have hexp_inv : ∀ (l : List ContractLevel), (∀ lvl ∈ l, lvl ∈ final.stack) →
          ∀ q : List ℕ, (l = [] → (encList encUnary q).length ≤ (encList encUnary base).length) →
            (∀ v ∈ q, v ≤ B_val) →
            l = [] ∨
              ((l.foldl (fun acc lvl => expandLevelList lvl acc) q).length ≤ x.adj.length ∧
                ∀ v ∈ l.foldl (fun acc lvl => expandLevelList lvl acc) q, v ≤ B_val) := by
        intro l hl q hq0 hq
        induction l generalizing q with
        | nil => exact Or.inl rfl
        | cons lvl ls ih =>
          simp only [List.foldl_cons]
          obtain ⟨hp1, hp2, hic, hbe1, hbe2, -, -, -⟩ :=
            hinv.stack_bound lvl (hl lvl List.mem_cons_self)
          have hstep_len : (expandLevelList lvl q).length ≤ x.adj.length := by
            simp [expandLevelList, hic]
          have hstep_elem : ∀ v ∈ expandLevelList lvl q, v ≤ B_val := fun v hv => by
            unfold expandLevelList at hv
            obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hv
            split_ifs
            · cases hbx : lvl.bestExit.getD (q.getD lvl.rep 0) none with
              | none =>
                simp only [Option.elim_none]
                by_cases hlt : idx < lvl.parent.length
                · rw [List.getD_eq_getElem _ _ hlt]
                  exact (hp2 _ (List.getElem_mem hlt)).trans (max_le (by omega) (by omega))
                · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; exact Nat.zero_le _
              | some x =>
                simp only [Option.elim_some]
                split_ifs
                · by_cases hlt : lvl.rep < q.length
                  · rw [List.getD_eq_getElem _ _ hlt]; exact hq _ (List.getElem_mem hlt)
                  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; exact Nat.zero_le _
                · by_cases hlt : idx < lvl.parent.length
                  · rw [List.getD_eq_getElem _ _ hlt]
                    exact (hp2 _ (List.getElem_mem hlt)).trans (max_le (by omega) (by omega))
                  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; exact Nat.zero_le _
            · cases hbe : lvl.bestEntry.getD idx none with
              | none =>
                exact (Nat.le_of_lt (lt_of_lt_of_le (List.mem_range.mp hidx) hic)).trans (by omega)
              | some y =>
                by_cases hlt : idx < lvl.bestEntry.length
                · rw [List.getD_eq_getElem _ _ hlt] at hbe
                  exact (hbe2 _ (List.getElem_mem hlt) y hbe).trans (by omega)
                · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)] at hbe; simp at hbe
            · by_cases hlt : idx < q.length
              · rw [List.getD_eq_getElem _ _ hlt]; exact hq _ (List.getElem_mem hlt)
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]; exact Nat.zero_le _
          rcases ls with _ | ⟨lvl2, ls2⟩
          · exact Or.inr ⟨hstep_len, hstep_elem⟩
          · have hrec := ih (fun m hm => hl m (List.mem_cons_of_mem _ hm)) (expandLevelList lvl q)
              (fun h => by simp at h) hstep_elem
            rcases hrec with hcons | hres
            · simp at hcons
            · exact Or.inr hres
      rcases hexp_inv (final.stack.take k) (fun lvl hl => List.mem_of_mem_take hl) base
          (fun _ => le_rfl) (fun v hv => (hbase_elem v hv).trans (Nat.le_add_right _ _))
        with hnil | ⟨hlen, helem⟩
      · rw [hnil, List.foldl_nil]
        exact le_max_left _ _
      · exact (encListUnary_le _ (encTableAuxInput x).length B_val (hlen.trans hL_adj) helem).trans
          (le_max_right _ _)
    exact hfold
  exact hfin

/-! ### Polynomial-time certificates for solvers and deciders -/

private theorem computableInPolyTime_rootInBounds :
    ComputableInPolyTime
      (fun inst : ArborescenceInstance => decide ((inst.root : ℤ) < (inst.adj.length : ℤ)))
      encArborescenceInstance encBool := by
  have hrNat : ComputableInPolyTime ArborescenceInstance.root encArborescenceInstance encNat := by
    fun_prop
  have hr : ComputableInPolyTime (fun inst : ArborescenceInstance => (inst.root : ℤ))
      encArborescenceInstance encIntBin :=
    intBin_natCast.comp hrNat
  have hlenNat : ComputableInPolyTime (fun inst : ArborescenceInstance => inst.adj.length)
      encArborescenceInstance encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hlen : ComputableInPolyTime (fun inst : ArborescenceInstance => (inst.adj.length : ℤ))
      encArborescenceInstance encIntBin :=
    intBin_natCast.comp hlenNat
  exact intBin_lt' hr hlen

private theorem computableInPolyTime_clampedRoot :
    ComputableInPolyTime clampedRoot encArborescenceInstance encUnary := by
  have hnat : ComputableInPolyTime clampedRoot encArborescenceInstance encNat := by
    unfold clampedRoot
    exact ite computableInPolyTime_rootInBounds (by fun_prop) (const 0)
  have hle : ∀ inst : ArborescenceInstance, clampedRoot inst ≤ inst.adj.length := by
    intro inst
    unfold clampedRoot
    split_ifs with h
    · exact Nat.le_of_lt (Int.ofNat_lt.mp (of_decide_eq_true h))
    · exact Nat.zero_le _
  exact binary_to_unary_bounded hnat (by fun_prop) hle

theorem computableInPolyTime_edmondsList :
    ComputableInPolyTime edmondsList encArborescenceInstance encParentOption := by
  have hcr := computableInPolyTime_clampedRoot
  have hin : ComputableInPolyTime
      (fun inst : ArborescenceInstance =>
        TableAuxInput.mk inst.adj.length (clampedRoot inst) inst.adj inst.cost)
      encArborescenceInstance encTableAuxInput := by fun_prop
  have hrun := computableInPolyTime_edmondsTableAuxList.comp hin
  unfold edmondsList
  exact ite computableInPolyTime_rootInBounds hrun (const none)

private theorem computableInPolyTime_transposeBoolTable :
    ComputableInPolyTime transposeBoolTable
      (encList (encList encBool)) (encList (encList encBool)) := by
  unfold transposeBoolTable
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  exact computableInPolyTime_adjAt' (by fun_prop) (by fun_prop) (by fun_prop)

private theorem computableInPolyTime_transposeIntTable :
    ComputableInPolyTime
      (fun p : ℕ × List (List ℤ) => transposeIntTable p.1 p.2)
      (encPair encUnary (encList (encList encIntBin))) (encList (encList encIntBin)) := by
  unfold transposeIntTable
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  exact computableInPolyTime_costAt' (by fun_prop) (by fun_prop) (by fun_prop)

theorem computableInPolyTime_edmondsOutList :
    ComputableInPolyTime edmondsOutList encArborescenceInstance encParentOption := by
  have hcr := computableInPolyTime_clampedRoot
  have htb : ComputableInPolyTime (fun inst : ArborescenceInstance => transposeBoolTable inst.adj)
      encArborescenceInstance (encList (encList encBool)) :=
    computableInPolyTime_transposeBoolTable.comp (by fun_prop)
  have hlen : ComputableInPolyTime (fun inst : ArborescenceInstance => inst.adj.length)
      encArborescenceInstance encUnary := by fun_prop
  have hcost : ComputableInPolyTime (fun inst : ArborescenceInstance => inst.cost)
      encArborescenceInstance (encList (encList encIntBin)) := by fun_prop
  have hti : ComputableInPolyTime
      (fun inst : ArborescenceInstance => transposeIntTable inst.adj.length inst.cost)
      encArborescenceInstance (encList (encList encIntBin)) :=
    computableInPolyTime_transposeIntTable.comp (hlen.prod hcost)
  have hin : ComputableInPolyTime
      (fun inst : ArborescenceInstance =>
        TableAuxInput.mk inst.adj.length (clampedRoot inst)
          (transposeBoolTable inst.adj) (transposeIntTable inst.adj.length inst.cost))
      encArborescenceInstance encTableAuxInput := by fun_prop
  have hrun := computableInPolyTime_edmondsTableAuxList.comp hin
  unfold edmondsOutList
  exact ite computableInPolyTime_rootInBounds hrun (const none)

private theorem computableInPolyTime_nonRootFilter
    (hcr : ComputableInPolyTime (fun d : ArborescenceDecInstance => clampedRoot d.inst)
      encArborescenceDecInstance encUnary) :
    ComputableInPolyTime
      (fun q : ArborescenceDecInstance × List ℕ =>
        (List.range q.1.inst.adj.length).filter fun v => v != clampedRoot q.1.inst)
      (encPair encArborescenceDecInstance (encList encUnary)) (encList encUnary) := by
  refine filterWithInput (range.comp (by fun_prop)) ?_
  have hcr' : ComputableInPolyTime
      (fun r : (ArborescenceDecInstance × List ℕ) × ℕ => clampedRoot r.1.1.inst)
      (encPair (encPair encArborescenceDecInstance (encList encUnary)) encUnary)
      encUnary :=
    hcr.comp ((fst _ _).comp (fst _ _))
  have hv : ComputableInPolyTime
      (fun r : (ArborescenceDecInstance × List ℕ) × ℕ => r.2)
      (encPair (encPair encArborescenceDecInstance (encList encUnary)) encUnary)
      encUnary := by fun_prop
  exact bool_not.comp (unary_beq' hv hcr')

theorem computableInPolyTime_minArborescenceDecide :
    ComputableInPolyTime minArborescenceDecide encArborescenceDecInstance encBool := by
  have hed : ComputableInPolyTime (fun d : ArborescenceDecInstance => edmondsList d.inst)
      encArborescenceDecInstance (encOption (encList encUnary)) :=
    computableInPolyTime_edmondsList.comp (by fun_prop)
  have hcr : ComputableInPolyTime (fun d : ArborescenceDecInstance => clampedRoot d.inst)
      encArborescenceDecInstance encUnary :=
    computableInPolyTime_clampedRoot.comp (by fun_prop)
  unfold minArborescenceDecide
  refine optionElimWithInput hed (const false) ?_
  exact intBin_le' (intBin_sum.comp
    (mapWithInput (computableInPolyTime_nonRootFilter hcr) (by fun_prop))) (by fun_prop)

theorem computableInPolyTime_minOutArborescenceDecide :
    ComputableInPolyTime minOutArborescenceDecide encArborescenceDecInstance encBool := by
  have hed : ComputableInPolyTime (fun d : ArborescenceDecInstance => edmondsOutList d.inst)
      encArborescenceDecInstance (encOption (encList encUnary)) :=
    computableInPolyTime_edmondsOutList.comp (by fun_prop)
  have hcr : ComputableInPolyTime (fun d : ArborescenceDecInstance => clampedRoot d.inst)
      encArborescenceDecInstance encUnary :=
    computableInPolyTime_clampedRoot.comp (by fun_prop)
  unfold minOutArborescenceDecide
  refine optionElimWithInput hed (const false) ?_
  exact intBin_le' (intBin_sum.comp
    (mapWithInput (computableInPolyTime_nonRootFilter hcr) (by fun_prop))) (by fun_prop)

private theorem computableInPolyTime_superRootAdjList :
    ComputableInPolyTime superRootAdjList
      (encList (encList encBool)) (encList (encList encBool)) := by
  unfold superRootAdjList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  fun_prop

private theorem computableInPolyTime_superRootWeightList :
    ComputableInPolyTime
      (fun p : ℕ × List (List ℤ) => superRootWeightList p.1 p.2)
      (encPair encUnary (encList (encList encIntBin))) (encList (encList encIntBin)) := by
  unfold superRootWeightList
  refine mapWithInput (range.comp (by fun_prop)) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  fun_prop

theorem computableInPolyTime_optimumBranchingList :
    ComputableInPolyTime optimumBranchingList encBranchingInstance (encList encUnary) := by
  have hsa : ComputableInPolyTime (fun B : BranchingInstance => superRootAdjList B.adj)
      encBranchingInstance (encList (encList encBool)) :=
    computableInPolyTime_superRootAdjList.comp (by fun_prop)
  have hlen : ComputableInPolyTime (fun B : BranchingInstance => B.adj.length)
      encBranchingInstance encUnary := by fun_prop
  have hwt : ComputableInPolyTime (fun B : BranchingInstance => B.weight)
      encBranchingInstance (encList (encList encIntBin)) := by fun_prop
  have hsw : ComputableInPolyTime
      (fun B : BranchingInstance => superRootWeightList B.adj.length B.weight)
      encBranchingInstance (encList (encList encIntBin)) :=
    computableInPolyTime_superRootWeightList.comp (hlen.prod hwt)
  have hin : ComputableInPolyTime
      (fun B : BranchingInstance =>
        TableAuxInput.mk (B.adj.length + 1) B.adj.length
          (superRootAdjList B.adj) (superRootWeightList B.adj.length B.weight))
      encBranchingInstance encTableAuxInput := by fun_prop
  have hrun := computableInPolyTime_edmondsTableAuxList.comp hin
  unfold optimumBranchingList
  refine optionElimWithInput hrun (const []) ?_
  refine mapWithInput (range.comp (by fun_prop)) ?_
  have hcond : ComputableInPolyTime
      (fun r : (BranchingInstance × List ℕ) × ℕ =>
        r.1.2.getD r.2 0 == r.1.1.adj.length)
      (encPair (encPair encBranchingInstance (encList encUnary)) encUnary) encBool := by fun_prop
  exact ite hcond (by fun_prop) (by fun_prop)

theorem computableInPolyTime_maxBranchingDecide :
    ComputableInPolyTime maxBranchingDecide encBranchingDecInstance encBool := by
  have hopt : ComputableInPolyTime (fun d : BranchingDecInstance => optimumBranchingList d.inst)
      encBranchingDecInstance (encList encUnary) :=
    computableInPolyTime_optimumBranchingList.comp (by fun_prop)
  unfold maxBranchingDecide
  have htotal : ComputableInPolyTime
      (fun d : BranchingDecInstance =>
        (((List.range d.inst.adj.length).filter fun v =>
          (optimumBranchingList d.inst).getD v 0 != v).map fun v =>
          costAt d.inst.weight ((optimumBranchingList d.inst).getD v 0) v).sum)
      encBranchingDecInstance encIntBin := by
    have hp : ComputableInPolyTime
        (fun q : BranchingDecInstance × ℕ => (optimumBranchingList q.1.inst).getD q.2 0)
        (encPair encBranchingDecInstance encUnary) encUnary :=
      listGetDWithInput (hopt.comp (fst _ _)) (snd _ _) 0
    exact intBin_sum.comp (mapWithInput (filterWithInput (range.comp (by fun_prop))
      (bool_not.comp (unary_beq' hp (snd _ _))))
      (computableInPolyTime_costAt' (by fun_prop) hp (snd _ _)))
  exact intBin_le' (by fun_prop) htotal

/-! ### Correctness equivalence and `P` membership -/

private def runListAux (r : ℕ) : ℕ → List (List Bool) → List (List ℤ) → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, a, c =>
    match selectParentsList a c r with
    | none => none
    | some f =>
      match findCycleList a.length r f with
      | none => some f
      | some x0 =>
        let n := a.length
        let inCycle := cycleMaskList n f x0
        let other := otherCycleCostList n c f inCycle
        let bEntry := bestEntryList n a c inCycle
        let bExit := bestExitList n a c inCycle other
        let a' := contractAdjList n inCycle a bEntry bExit x0 r
        let c' := contractCostList n inCycle c other bEntry bExit x0
        let lvl : ContractLevel := ⟨f, inCycle, bEntry, bExit, x0⟩
        (runListAux r fuel a' c').map (expandLevelList lvl)

private theorem contractStep_of_done {s : ContractState} (h : s.done = true) :
    ∀ k, contractStep^[k] s = s
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply, show contractStep s = s by simp [contractStep, h]]
    exact contractStep_of_done h k

private theorem evalContractState_iterate (r : ℕ) :
    ∀ (fuel : ℕ) (a : List (List Bool)) (c : List (List ℤ)) (st : List ContractLevel),
      let final := contractStep^[fuel] ⟨a, c, r, false, none, st⟩
      final.result.map (fun base => final.stack.foldl (fun q lvl => expandLevelList lvl q) base) =
        (runListAux r fuel a c).map fun base => st.foldl (fun q lvl => expandLevelList lvl q) base
  | 0, _, _, _ => rfl
  | fuel + 1, a, c, st => by
    dsimp only
    rw [Function.iterate_succ_apply]
    cases hsel : selectParentsList a c r with
    | none =>
      have hs : contractStep ⟨a, c, r, false, none, st⟩ = ⟨a, c, r, true, none, st⟩ := by
        simp [contractStep, hsel]
      rw [hs, contractStep_of_done rfl fuel]
      simp [runListAux, hsel]
    | some f =>
      cases hcyc : findCycleList a.length r f with
      | none =>
        have hs : contractStep ⟨a, c, r, false, none, st⟩ =
            ⟨a, c, r, true, some f, st⟩ := by
          simp [contractStep, hsel, hcyc]
        rw [hs, contractStep_of_done rfl fuel]
        simp [runListAux, hsel, hcyc]
      | some x0 =>
        have hs : contractStep ⟨a, c, r, false, none, st⟩ =
            contractFromParent ⟨a, c, r, false, none, st⟩ f x0 := by
          simp [contractStep, hsel, hcyc]
        rw [hs]
        dsimp only [contractFromParent]
        have ih := evalContractState_iterate r fuel
          (contractAdjList a.length (cycleMaskList a.length f x0) a
            (bestEntryList a.length a c (cycleMaskList a.length f x0))
            (bestExitList a.length a c (cycleMaskList a.length f x0)
              (otherCycleCostList a.length c f (cycleMaskList a.length f x0))) x0 r)
          (contractCostList a.length (cycleMaskList a.length f x0) c
            (otherCycleCostList a.length c f (cycleMaskList a.length f x0))
            (bestEntryList a.length a c (cycleMaskList a.length f x0))
            (bestExitList a.length a c (cycleMaskList a.length f x0)
              (otherCycleCostList a.length c f (cycleMaskList a.length f x0))) x0)
          (⟨f, cycleMaskList a.length f x0,
            bestEntryList a.length a c (cycleMaskList a.length f x0),
            bestExitList a.length a c (cycleMaskList a.length f x0)
              (otherCycleCostList a.length c f (cycleMaskList a.length f x0)), x0⟩ :: st)
        simpa [runListAux, hsel, hcyc, Option.map_map, Function.comp_def, List.foldl_cons] using ih

private theorem edmondsTableAuxList_eq_runListAux (fuel r : ℕ) (a : List (List Bool))
    (c : List (List ℤ)) :
    edmondsTableAuxList fuel r a c = runListAux r fuel a c := by
  have h := evalContractState_iterate r fuel a c []
  simpa [edmondsTableAuxList] using h

@[instance_reducible] private def localFinEnum (n : ℕ) : FinEnum (Fin n) :=
  ⟨n, Equiv.refl (Fin n)⟩

private theorem localFinEnum_toList (n : ℕ) :
    @FinEnum.toList (Fin n) (localFinEnum n) = List.finRange n := by
  change List.map (⇑(Equiv.refl (Fin n)).symm) (List.finRange n) = List.finRange n
  simp

private theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

private theorem foldl_argMinStep_fin {n : ℕ} (pred : Fin n → Bool) (key : Fin n → ℤ)
    (predN : ℕ → Bool) (keyN : ℕ → ℤ)
    (hpred : ∀ w : Fin n, pred w = predN w.1)
    (hkey : ∀ w : Fin n, pred w = true → key w = keyN w.1) :
    ∀ (l : List (Fin n)) (acc : Option (Fin n)), (∀ a, acc = some a → pred a = true) →
      ((l.filter pred).foldl (List.argAux fun a b => key a < key b) acc).map Fin.val =
        (l.map Fin.val).foldl (argMinStep predN keyN) (acc.map Fin.val)
  | [], _, _ => rfl
  | x :: xs, acc, hacc => by
    simp only [List.map_cons, List.foldl_cons, argMinStep]
    by_cases hx : pred x = true
    · have hxn : predN x.1 = true := (hpred x).symm.trans hx
      rw [List.filter_cons_of_pos (by simp [hx])]
      simp only [List.foldl_cons, hxn, ↓reduceIte]
      have hstep : (List.argAux (fun a b => key a < key b) acc x).map Fin.val =
          (acc.map Fin.val).elim (some x.1)
            (fun cur => if decide (keyN x.1 < keyN cur) then some x.1 else some cur) := by
        cases acc with
        | none => rfl
        | some a =>
          have ha := hacc a rfl
          simp only [List.argAux, Option.map_some, Option.elim_some, hkey x hx, hkey a ha]
          by_cases hlt : keyN x.1 < keyN a.1 <;> simp [hlt]
      have hacc' : ∀ b, List.argAux (fun a b => key a < key b) acc x = some b → pred b = true := by
        intro b hb
        cases acc with
        | none =>
          simp only [List.argAux, Option.some.injEq] at hb
          exact hb ▸ hx
        | some a =>
          simp only [List.argAux] at hb
          split_ifs at hb <;> simp only [Option.some.injEq] at hb
          · exact hb ▸ hx
          · exact hb ▸ hacc a rfl
      rw [foldl_argMinStep_fin pred key predN keyN hpred hkey xs _ hacc', hstep]
    · have hxf : pred x = false := Bool.eq_false_iff.mpr hx
      have hxn : predN x.1 = false := (hpred x).symm.trans hxf
      rw [List.filter_cons_of_neg (by simp [hxf])]
      simp only [hxn, Bool.false_eq_true, ↓reduceIte]
      exact foldl_argMinStep_fin pred key predN keyN hpred hkey xs acc hacc

private theorem argMinRange_fin {n : ℕ} (pred : Fin n → Bool) (key : Fin n → ℤ)
    (predN : ℕ → Bool) (keyN : ℕ → ℤ)
    (hpred : ∀ w : Fin n, pred w = predN w.1)
    (hkey : ∀ w : Fin n, pred w = true → key w = keyN w.1) :
    (((List.finRange n).filter pred).argmin key).map Fin.val = argMinRange n predN keyN := by
  have h := foldl_argMinStep_fin pred key predN keyN hpred hkey (List.finRange n) none
    fun _ h => by simp at h
  simpa [List.argmin, argMinRange, map_val_finRange] using h

/-- Boolean adjacency relation on `Fin n × Fin n` read from row-major table `a`. -/
private def tableAdj (n : ℕ) (a : List (List Bool)) (u w : Fin n) : Bool :=
  adjAt a u.1 w.1

private theorem decide_congr_inst {p : Prop} (d₁ d₂ : Decidable p) :
    @decide p d₁ = @decide p d₂ := by
  cases Subsingleton.elim d₁ d₂
  rfl

private theorem selectParentsList_eq {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    {a : List (List Bool)} (ha : a.length = n) (c : List (List ℤ)) (r : Fin n) :
    match selectParentsList a c r.1 with
    | none => ¬ ∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ []
    | some f =>
      (∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ []) ∧
        f.length = n ∧ (∀ i < n, f.getD i 0 < n) ∧
        ∀ v : Fin n, f.getD v.1 0 = (cheapestParent (tableAdj n a) (tableCost c) r v).1 := by
  have hcand_eq (v : Fin n) :
      ((List.finRange n).filter fun w : Fin n => adjAt a v.1 w.1 && (w != v)) =
        candidates (tableAdj n a) v := by
    unfold candidates
    rw [htl]
    refine List.filter_congr fun w _ => ?_
    simp only [tableAdj, _root_.bne, BEq.beq]
    exact congrArg (adjAt a v.1 w.1 && ·) (congrArg not (decide_congr_inst _ _))
  have harg (v : Fin n) :
      ((candidates (tableAdj n a) v).argmin (tableCost c v)).map Fin.val =
        argMinRange n (fun w => adjAt a v.1 w && (w != v.1)) (fun w => costAt c v.1 w) := by
    rw [← hcand_eq v]
    refine argMinRange_fin _ _ _ _ (fun w => ?_) (fun _ _ => rfl)
    by_cases hwv : w = v
    · subst hwv; simp [_root_.bne, BEq.beq]
    · simp only [_root_.bne, BEq.beq]
      rw [decide_eq_false hwv, decide_eq_false (Fin.val_ne_of_ne hwv)]
  unfold selectParentsList
  dsimp only
  rw [ha]
  set opts := (List.range n).map fun v =>
    if v == r.1 then some r.1
    else argMinRange n (fun w => adjAt a v w && (w != v)) (fun w => costAt c v w)
  have hopts_len : opts.length = n := by simp [opts]
  have hopts_get (v : Fin n) :
      opts.getD v.1 none =
        if v = r then some r.1
        else ((candidates (tableAdj n a) v).argmin (tableCost c v)).map Fin.val := by
    rw [List.getD_eq_getElem opts none (by rw [hopts_len]; exact v.2)]
    simp only [opts, List.getElem_map, List.getElem_range, ← harg v]
    by_cases hvr : v = r
    · simp [hvr]
    · have hvrn : (v.1 == r.1) = false := by simp [Fin.ext_iff] at hvr; simp [hvr]
      simp [hvr, hvrn]
  have hall_iff : opts.all Option.isSome = true ↔
      ∀ v : Fin n, v ≠ r → candidates (tableAdj n a) v ≠ [] := by
    constructor
    · intro hall v hvr
      have hv_lt : v.1 < opts.length := by rw [hopts_len]; exact v.2
      have hmem : opts[v.1]'hv_lt ∈ opts := List.getElem_mem _
      have his := (List.all_eq_true.mp hall) _ hmem
      have hget : opts.getD v.1 none = opts[v.1]'hv_lt := List.getD_eq_getElem opts none hv_lt
      rw [← hget, hopts_get v, ite_eq_right (fun h => hvr h)] at his
      intro hnil
      simp [hnil] at his
    · intro hall
      rw [List.all_eq_true]
      intro o ho
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ho
      rw [List.mem_range] at hk
      set v : Fin n := ⟨k, hk⟩
      have hv_lt : v.1 < opts.length := by rw [hopts_len]; exact v.2
      have hget : (if k == r.1 then some r.1 else
          argMinRange n (fun w => adjAt a k w && (w != k)) (fun w => costAt c k w)) =
            opts.getD v.1 none := by
        rw [List.getD_eq_getElem opts none hv_lt]
        simp [opts, v]
      rw [hget, hopts_get v]
      by_cases hvr : v = r
      · simp [hvr]
      · obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := tableCost c v) (hall v hvr)
        simp [hvr, hm]
  split_ifs with hall
  · have hcond := hall_iff.mp hall
    refine ⟨hcond, by simp [opts], fun i hi => ?_, fun v => ?_⟩
    · have hi_opt : i < opts.length := by rw [hopts_len]; exact hi
      rw [List.getD_eq_getElem _ _ (by simp only [opts, List.length_map, List.length_range, hi]),
        List.getElem_map]
      have h1 : opts[i]'hi_opt = opts.getD (⟨i, hi⟩ : Fin n).1 none :=
        (List.getD_eq_getElem opts none hi_opt).symm
      rw [h1, hopts_get ⟨i, hi⟩]
      by_cases hir : (⟨i, hi⟩ : Fin n) = r
      · simp [hir, r.isLt]
      · obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := tableCost c ⟨i, hi⟩)
          (hcond ⟨i, hi⟩ hir)
        simp [hir, hm, m.isLt]
    · have hv_opt : v.1 < opts.length := by rw [hopts_len]; exact v.2
      rw [List.getD_eq_getElem _ _ (by simp [opts]), List.getElem_map]
      have h1 : opts[v.1]'hv_opt = opts.getD v.1 none :=
        (List.getD_eq_getElem opts none hv_opt).symm
      rw [h1, hopts_get v]
      unfold cheapestParent
      by_cases hvr : v = r
      · simp [hvr]
      · obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := tableCost c v) (hcond v hvr)
        simp [hvr, hm]
  · exact fun h => hall (hall_iff.mpr h)

private theorem followParent_iterate_eq {n : ℕ} (f : List ℕ) (fV : Fin n → Fin n)
    (hf : ∀ v : Fin n, f.getD v.1 0 = (fV v).1) (v : Fin n) :
    ∀ k, (followParent f)^[k] v.1 = (fV^[k] v).1
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      followParent_iterate_eq f fV hf v k, followParent, hf]

private theorem findCycleList_eq {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    (hcard : FinEnum.card (Fin n) = n)
    (f : List ℕ) (fV : Fin n → Fin n) (hf : ∀ v : Fin n, f.getD v.1 0 = (fV v).1) (r : Fin n) :
    findCycleList n r.1 f = (findCycle r fV).map Fin.val := by
  unfold findCycleList findCycle
  rw [htl, ← map_val_finRange n, List.find?_map]
  have hpred : (fun x => (x != r.1) && hasCycleFromList n f x) ∘ Fin.val =
      fun x : Fin n => x != r &&
        (List.range (FinEnum.card (Fin n))).any fun k => fV^[k + 1] x == x := by
    funext x
    simp only [Function.comp_apply, hasCycleFromList, hcard]
    have hne : (x.1 != r.1) = (x != r) := by
      by_cases hxr : x = r
      · subst hxr; simp [_root_.bne]
      · simp [hxr, Fin.val_ne_of_ne hxr, _root_.bne]
    rw [hne]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨k, hk, hper⟩
      exact ⟨k, hk, Fin.ext ((followParent_iterate_eq f fV hf x (k + 1)).symm.trans hper)⟩
    · rintro ⟨k, hk, hper⟩
      exact ⟨k, hk, (followParent_iterate_eq f fV hf x (k + 1)).trans (congrArg Fin.val hper)⟩
  rw [hpred]
  refine congrArg (Option.map Fin.val) (congrArg (fun p => (List.finRange n).find? p) ?_)
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, bne_iff_ne, List.any_eq_true, List.mem_range, beq_iff_eq, hcard]

private theorem list_getD_map_range {α : Type*} (f : ℕ → α) (n i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range]

private theorem finset_erase_eq_of_dec {α : Type*} (d₁ d₂ : DecidableEq α) (s : Finset α)
    (a : α) : @Finset.erase α d₁ s a = @Finset.erase α d₂ s a := by
  cases Subsingleton.elim d₁ d₂; rfl

private theorem cycleMaskList_eq {n : ℕ} [FinEnum (Fin n)]
    (hcard : FinEnum.card (Fin n) = n)
    (f : List ℕ) (fV : Fin n → Fin n) (hf : ∀ v : Fin n, f.getD v.1 0 = (fV v).1) (x0 y : Fin n) :
    (cycleMaskList n f x0.1).getD y.1 false = true ↔ y ∈ cycleOf fV x0 := by
  unfold cycleMaskList
  rw [List.getD_eq_getElem _ _ (by simp [y.2]), List.getElem_map, List.getElem_range,
    List.any_eq_true, mem_cycleOf]
  simp only [List.mem_range, beq_iff_eq, hcard]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, Fin.ext ((followParent_iterate_eq f fV hf x0 k).symm.trans heq)⟩
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (followParent_iterate_eq f fV hf x0 k).trans (congrArg Fin.val heq)⟩

private theorem otherCycleCostList_eq {n : ℕ} (c : List (List ℤ)) (f : List ℕ) (fV : Fin n → Fin n)
    (inCycle : List Bool) (C : Finset (Fin n))
    (hf : ∀ v : Fin n, f.getD v.1 0 = (fV v).1)
    (hmask : ∀ y : Fin n, inCycle.getD y.1 false = true ↔ y ∈ C)
    {x : Fin n} (hx : x ∈ C) :
    (otherCycleCostList n c f inCycle).getD x.1 0 = ∑ y ∈ C.erase x, tableCost c y (fV y) := by
  unfold otherCycleCostList
  rw [List.getD_eq_getElem _ _ (by simp [x.2]), List.getElem_map, List.getElem_range]
  have hxin : inCycle.getD x.1 false = true := (hmask x).mpr hx
  simp only [hxin, ↓reduceIte]
  rw [← map_val_finRange n, List.filter_map, List.map_map]
  have hcongr : List.map ((fun y => costAt c y (f.getD y 0)) ∘ Fin.val)
      ((List.finRange n).filter
        ((fun y => inCycle.getD y false && (y != x.1)) ∘ Fin.val)) =
      ((List.finRange n).filter (fun z : Fin n => decide (z ∈ C) && (z != x))).map
        (fun z : Fin n => tableCost c z (fV z)) := by
    have hf1 : (List.finRange n).filter
          ((fun y => inCycle.getD y false && (y != x.1)) ∘ Fin.val) =
        (List.finRange n).filter (fun z : Fin n => decide (z ∈ C) && (z != x)) := by
      refine List.filter_congr fun z _ => ?_
      have h1 : inCycle.getD z.1 false = decide (z ∈ C) :=
        Bool.eq_iff_iff.mpr (by simpa using hmask z)
      have h2 : (z.1 != x.1) = (z != x) := by
        by_cases hzx : z = x
        · subst hzx; simp [_root_.bne]
        · simp [hzx, Fin.val_ne_of_ne hzx, _root_.bne]
      simp only [Function.comp_apply, h1, h2]
    rw [hf1]
    refine List.map_congr_left fun z _ => ?_
    dsimp only [Function.comp_apply, tableCost]
    rw [hf z]
  rw [hcongr]
  have hnd : ((List.finRange n).filter (fun z : Fin n => decide (z ∈ C) && (z != x))).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.sum_toFinset _ hnd]
  congr 1
  ext z
  simp [and_comm]

private theorem runListAux_eq_edmondsAux {n : ℕ} [FinEnum (Fin n)]
    (htl : FinEnum.toList (Fin n) = List.finRange n)
    (hcard : FinEnum.card (Fin n) = n) (r : Fin n) :
    ∀ (fuel : ℕ) (a : List (List Bool)) (c : List (List ℤ)), a.length = n →
      match runListAux r.1 fuel a c,
          edmondsAux r fuel (tableAdj n a) (tableCost c) with
      | none, none => True
      | some pL, some pV =>
        pL.length = n ∧ ∀ v : Fin n, pL.getD v.1 0 = (pV v).1
      | _, _ => False
  | 0, _, _, _ => trivial
  | fuel + 1, a, c, ha_len => by
    have hsel := selectParentsList_eq htl ha_len c r
    unfold runListAux edmondsAux
    cases hselL : selectParentsList a c r.1 with
    | none =>
      rw [hselL] at hsel
      dsimp only at hsel
      simp only [hsel, ↓reduceIte]
    | some f =>
      rw [hselL] at hsel
      dsimp only at hsel
      obtain ⟨hcond, hf_len, hf_lt, hf_eq⟩ := hsel
      set fV := cheapestParent (tableAdj n a) (tableCost c) r
      split_ifs
      simp only [ha_len]
      have hcyc := findCycleList_eq htl hcard f fV hf_eq r
      cases hcycL : findCycleList n r.1 f with
      | none =>
        rw [hcycL] at hcyc
        have hcycV : findCycle r fV = none := by
          cases h : findCycle r fV <;> simp_all
        rw [hcycV]
        exact ⟨hf_len, hf_eq⟩
      | some x0N =>
        rw [hcycL] at hcyc
        obtain ⟨x0, hx0V, hx0N⟩ : ∃ x0 : Fin n, findCycle r fV = some x0 ∧ x0.1 = x0N := by
          cases h : findCycle r fV <;> simp_all
        rw [hx0V]
        dsimp only
        subst hx0N
        set C := cycleOf fV x0
        set inCycle := cycleMaskList n f x0.1
        set other := otherCycleCostList n c f inCycle
        set bEntry := bestEntryList n a c inCycle
        set bExit := bestExitList n a c inCycle other
        set a' := contractAdjList n inCycle a bEntry bExit x0.1 r.1
        set c' := contractCostList n inCycle c other bEntry bExit x0.1
        have hmask (y : Fin n) : inCycle.getD y.1 false = true ↔ y ∈ C :=
          cycleMaskList_eq hcard f fV hf_eq x0 y
        have hin (y : Fin n) : inCycle.getD y.1 false = decide (y ∈ C) :=
          Bool.eq_iff_iff.mpr (by simpa using hmask y)
        have hother {x : Fin n} (hx : x ∈ C) :
            other.getD x.1 0 = ∑ y ∈ C.erase x, tableCost c y (fV y) :=
          otherCycleCostList_eq c f fV inCycle C hf_eq hmask hx
        have hbe (u : Fin n) :
            bEntry.getD u.1 none =
              ((bestEntry (tableAdj n a) (tableCost c) C u)).map Fin.val := by
          dsimp only [bEntry]
          unfold bestEntryList bestEntry
          rw [List.getD_eq_getElem _ _ (by simp [u.2]), List.getElem_map, List.getElem_range, htl]
          symm
          exact argMinRange_fin _ _ _ _ (fun y => by
            rw [tableAdj, hin]; exact congrArg (· && _) (decide_congr_inst _ _)) (fun _ _ => rfl)
        have hbe_some (u : Fin n) : (bEntry.getD u.1 none).isSome =
            (List.finRange n).any fun y => decide (y ∈ C) && tableAdj n a u y := by
          rw [hbe u, Option.isSome_map, bestEntry, htl, List.isSome_argmin_filter]
          exact congrArg _ (funext fun y => congrArg (· && _) (decide_congr_inst _ _))
        have hbx (w : Fin n) :
            bExit.getD w.1 none =
              ((bestExit (tableAdj n a) (tableCost c) fV C w)).map Fin.val := by
          dsimp only [bExit]
          unfold bestExitList bestExit
          rw [List.getD_eq_getElem _ _ (by simp [w.2]), List.getElem_map, List.getElem_range, htl]
          symm
          refine argMinRange_fin _ _ _ _ (fun x => by
            rw [tableAdj, hin]; exact congrArg (· && _) (decide_congr_inst _ _)) (fun x hx => ?_)
          have hxC : x ∈ C := by
            have h := (Bool.and_eq_true _ _ |>.mp hx).1
            rw [decide_congr_inst _ inferInstance] at h
            exact of_decide_eq_true h
          dsimp only [exitCost, tableCost]
          rw [hother hxC, finset_erase_eq_of_dec _ (instDecidableEqFin n) C x]
          rfl
        have hbx_some (w : Fin n) : (bExit.getD w.1 none).isSome =
            (List.finRange n).any fun x => decide (x ∈ C) && tableAdj n a x w := by
          rw [hbx w, Option.isSome_map, bestExit, htl, List.isSome_argmin_filter]
          exact congrArg _ (funext fun x => congrArg (· && _) (decide_congr_inst _ _))
        have ha'_len : a'.length = n := by simp [a', contractAdjList]
        have ha'_eq : tableAdj n a' = contractAdj (tableAdj n a) C x0 r := by
          funext u w
          have hget : adjAt a' u.1 w.1 =
              if inCycle.getD u.1 false then
                if u.1 == x0.1 then !(inCycle.getD w.1 false) && (bExit.getD w.1 none).isSome
                else w.1 == r.1
              else
                if inCycle.getD w.1 false then (w.1 == x0.1) && (bEntry.getD u.1 none).isSome
                else adjAt a u.1 w.1 := by
            dsimp only [a']
            unfold adjAt contractAdjList
            rw [list_getD_map_range _ _ _ _ u.2, list_getD_map_range _ _ _ _ w.2]
            rfl
          change adjAt a' u.1 w.1 = contractAdj (tableAdj n a) C x0 r u w
          rw [hget]
          unfold contractAdj
          rw [htl, hbx_some w, hbe_some u]
          have hb_iff (y : Fin n) : (y ∈ C → inCycle.getD y.1 false = true) ∧
              (y ∉ C → inCycle.getD y.1 false = false) :=
            ⟨(hmask y).mpr, fun hy => Bool.eq_false_iff.mpr fun h => hy ((hmask y).mp h)⟩
          dsimp only [tableAdj]
          by_cases huC : u ∈ C
          · simp only [(hb_iff u).1 huC, huC, ↓reduceIte]
            by_cases hux' : u = x0
            · have hux1 : (u.1 == x0.1) = true := beq_iff_eq.mpr (congrArg Fin.val hux')
              rw [hux1]
              simp only [hux', ↓reduceIte]
              congr 1
              · by_cases hwC : w ∈ C
                · have hwT := (hb_iff w).1 hwC
                  rw [hwT]
                  simp [hwC]
                · have hwF := (hb_iff w).2 hwC
                  rw [hwF]
                  simp [hwC]
              · refine congrArg (List.any (List.finRange n)) (funext fun x => ?_)
                exact congrArg (· && adjAt a x.1 w.1) (decide_congr_inst _ _)
            · have hux1 : (u.1 == x0.1) = false := beq_false_of_ne (Fin.val_ne_of_ne hux')
              rw [hux1]
              simp only [Bool.false_eq_true, ↓reduceIte, hux']
              by_cases hwr' : w = r
              · simp [hwr']
              · simp [hwr', Fin.val_ne_of_ne hwr']
          · simp only [(hb_iff u).2 huC, Bool.false_eq_true, huC, ↓reduceIte]
            by_cases hwC : w ∈ C
            · simp only [(hb_iff w).1 hwC, hwC, ↓reduceIte]
              refine congrArg₂ Bool.and ?_ ?_
              · by_cases hwx' : w = x0
                · simp [hwx']
                · simp [hwx', Fin.val_ne_of_ne hwx']
              · refine congrArg (List.any (List.finRange n)) (funext fun y => ?_)
                exact congrArg (· && adjAt a u.1 y.1) (decide_congr_inst _ _)
            · simp only [(hb_iff w).2 hwC, Bool.false_eq_true, hwC, ↓reduceIte]
        have hc'_eq : tableCost c' = contractCost (tableAdj n a) (tableCost c) fV C x0 := by
          funext u w
          have hget : costAt c' u.1 w.1 =
              if inCycle.getD u.1 false then
                if u.1 == x0.1 then
                  (bExit.getD w.1 none).elim (costAt c u.1 w.1)
                    fun x => costAt c x w.1 + other.getD x 0
                else 0
              else
                if w.1 == x0.1 then
                  (bEntry.getD u.1 none).elim (costAt c u.1 w.1) fun y => costAt c u.1 y
                else costAt c u.1 w.1 := by
            dsimp only [c']
            unfold costAt contractCostList
            rw [list_getD_map_range _ _ _ _ u.2, list_getD_map_range _ _ _ _ w.2]
            rfl
          change costAt c' u.1 w.1 = contractCost (tableAdj n a) (tableCost c) fV C x0 u w
          rw [hget]
          unfold contractCost
          by_cases huC : u ∈ C
          · have huT : inCycle.getD u.1 false = true := (hmask u).mpr huC
            simp only [huT, ↓reduceIte, huC]
            by_cases hux' : u = x0
            · have hux1 : (u.1 == x0.1) = true := beq_iff_eq.mpr (congrArg Fin.val hux')
              rw [hux1]
              simp only [↓reduceIte, hux']
              cases hbo : bestExit (tableAdj n a) (tableCost c) fV C w with
              | none => rw [hbx, hbo]; rfl
              | some x =>
                have hmem : x ∈ C := by
                  unfold bestExit at hbo
                  have hm := (List.mem_filter.mp (List.argmin_mem hbo)).2
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
                  exact hm.1
                rw [hbx, hbo, Option.map_some, Option.elim_some]
                dsimp only [exitCost, tableCost]
                rw [hother hmem,
                  finset_erase_eq_of_dec (instDecidableEqFin n) (fun a b => FinEnum.decEq a b) C x]
                rfl
            · have hux1 : (u.1 == x0.1) = false := beq_false_of_ne (Fin.val_ne_of_ne hux')
              rw [hux1]
              simp only [Bool.false_eq_true, ↓reduceIte, hux']
          · have huF : inCycle.getD u.1 false = false :=
              Bool.eq_false_iff.mpr fun h => huC ((hmask u).mp h)
            simp only [huF, Bool.false_eq_true, ↓reduceIte, huC]
            by_cases hwx' : w = x0
            · have hwx1 : (w.1 == x0.1) = true := beq_iff_eq.mpr (congrArg Fin.val hwx')
              rw [hwx1]
              simp only [↓reduceIte, hwx']
              cases hbi : bestEntry (tableAdj n a) (tableCost c) C u with
              | none => rw [hbe, hbi]; rfl
              | some y => rw [hbe, hbi]; rfl
            · have hwx1 : (w.1 == x0.1) = false := beq_false_of_ne (Fin.val_ne_of_ne hwx')
              rw [hwx1]
              simp only [Bool.false_eq_true, ↓reduceIte, hwx']
              rfl
        have hih := runListAux_eq_edmondsAux htl hcard r fuel a' c' ha'_len
        rw [ha'_eq, hc'_eq] at hih
        cases hrL : runListAux r.1 fuel a' c' with
        | none =>
          cases hrV : edmondsAux r fuel (contractAdj (tableAdj n a) C x0 r)
              (contractCost (tableAdj n a) (tableCost c) fV C x0) with
          | none => simp only [Option.map_none]
          | some qV =>
            simp only [hrL, hrV] at hih
        | some qL =>
          cases hrV : edmondsAux r fuel (contractAdj (tableAdj n a) C x0 r)
              (contractCost (tableAdj n a) (tableCost c) fV C x0) with
          | none =>
            simp only [hrL, hrV] at hih
          | some qV =>
            simp only [hrL, hrV] at hih
            obtain ⟨hq_len, hq_eq⟩ := hih
            simp only [Option.map_some]
            refine ⟨by simp [expandLevelList, inCycle, cycleMaskList], fun v => ?_⟩
            set lvl : ContractLevel := ⟨f, inCycle, bEntry, bExit, x0.1⟩
            have hic_len : lvl.inCycle.length = n := by simp [lvl, inCycle, cycleMaskList]
            have hget_exp : (expandLevelList lvl qL).getD v.1 0 =
                if lvl.inCycle.getD v.1 false then
                  (lvl.bestExit.getD (qL.getD lvl.rep 0) none).elim (lvl.parent.getD v.1 0) fun x =>
                    if v.1 == x then qL.getD lvl.rep 0 else lvl.parent.getD v.1 0
                else if qL.getD v.1 0 == lvl.rep then (lvl.bestEntry.getD v.1 none).getD v.1
                else qL.getD v.1 0 := by
              unfold expandLevelList
              exact list_getD_map_range _ _ _ _ (by simp [hic_len])
            rw [hget_exp]
            unfold expandParent
            have hqx0 : qL.getD x0.1 0 = (qV x0).1 := hq_eq x0
            by_cases hvC : v ∈ C
            · have hvT : lvl.inCycle.getD v.1 false = true := (hmask v).mpr hvC
              simp only [lvl, hvT, ↓reduceIte, hvC, hqx0]
              cases hbo : bestExit (tableAdj n a) (tableCost c) fV C (qV x0) with
              | none => rw [hbx, hbo]; exact hf_eq v
              | some x =>
                rw [hbx, hbo, Option.map_some, Option.elim_some]
                by_cases hvx : v = x
                · have hvx1 : (v.1 == x.1) = true := beq_iff_eq.mpr (congrArg Fin.val hvx)
                  rw [hvx1]
                  simp only [↓reduceIte, hvx]
                · have hvx1 : (v.1 == x.1) = false := beq_false_of_ne (Fin.val_ne_of_ne hvx)
                  rw [hvx1]
                  simp only [Bool.false_eq_true, ↓reduceIte, hvx]
                  exact hf_eq v
            · have hvF : lvl.inCycle.getD v.1 false = false :=
                Bool.eq_false_iff.mpr fun h => hvC ((hmask v).mp h)
              simp only [lvl, hvF, Bool.false_eq_true, ↓reduceIte, hvC]
              by_cases hqvx : qV v = x0
              · have h1 : (qL.getD v.1 0 == x0.1) = true := by
                  rw [hq_eq v]; exact beq_iff_eq.mpr (congrArg Fin.val hqvx)
                rw [h1]
                simp only [↓reduceIte, hqvx]
                cases hbi : bestEntry (tableAdj n a) (tableCost c) C v with
                | none => rw [hbe, hbi]; rfl
                | some y => rw [hbe, hbi]; rfl
              · have h1 : (qL.getD v.1 0 == x0.1) = false := by
                  rw [hq_eq v]; exact beq_false_of_ne (Fin.val_ne_of_ne hqvx)
                rw [h1]
                simp only [Bool.false_eq_true, ↓reduceIte, hqvx]
                exact hq_eq v

private theorem arcCost_parentDigraph_eq_sum_range {n : ℕ} {c : Fin n → Fin n → ℤ}
    {cL : ℕ → ℕ → ℤ} (hc : ∀ u w : Fin n, c u w = cL u.1 w.1)
    (r : Fin n) (p : Fin n → Fin n) (pL : List ℕ)
    (hp : ∀ v : Fin n, pL.getD v.1 0 = (p v).1) :
    arcCost (Digraph.parentDigraph r p) c =
      (((List.range n).filter fun v => v != r.1).map fun v => cL v (pL.getD v 0)).sum := by
  rw [arcCost_parentDigraph]
  unfold parentCost
  have hnd : ((List.finRange n).filter fun v : Fin n => v != r).Nodup :=
    (List.nodup_finRange n).filter _
  have hset : ((List.finRange n).filter fun v : Fin n => v != r).toFinset =
      Finset.univ.erase r := by
    ext v
    simp
  rw [← hset, List.sum_toFinset _ hnd]
  rw [← map_val_finRange n, List.filter_map]
  have hf : (List.finRange n).filter (fun v : Fin n => v != r) =
      (List.finRange n).filter (fun v : Fin n => (v.1 != r.1)) := by
    refine List.filter_congr fun v _ => ?_
    by_cases hvr : v = r
    · subst hvr; simp [_root_.bne]
    · simp [hvr, Fin.val_ne_of_ne hvr, _root_.bne]
  change (List.map (fun v => c v (p v))
      ((List.finRange n).filter fun v : Fin n => v != r)).sum = _
  rw [hf]
  have hf' : (List.finRange n).filter (fun v : Fin n => v.1 != r.1) =
      (List.finRange n).filter ((fun v => v != r.1) ∘ Fin.val) := rfl
  rw [hf', List.map_map]
  refine congrArg List.sum (List.map_congr_left fun v _ => ?_)
  dsimp only [Function.comp_apply]
  rw [hc, hp v]

/-- Shared core of the bounded-cost decision procedures: a list run `o` that matches a solver
output `oV` satisfying the Chu–Liu/Edmonds specification on `G` decides whether `G` has a
spanning in-arborescence rooted at `r` of cost at most `θ`. -/
private theorem elim_decide_iff_of_spec {n : ℕ} {fi : Fintype (Fin n)}
    {de : DecidableEq (Fin n)} {G : Digraph (Fin n)}
    {c : Fin n → Fin n → ℤ} {r : Fin n} {cL : ℕ → ℕ → ℤ}
    (hc : ∀ u w : Fin n, c u w = cL u.1 w.1) {o : Option (List ℕ)}
    {oV : Option (Fin n → Fin n)}
    (ho : match o, oV with
      | none, none => True
      | some pL, some pV => pL.length = n ∧ ∀ v : Fin n, pL.getD v.1 0 = (pV v).1
      | _, _ => False)
    (hspec : (∀ p, oV = some p → IsInArborescenceParent G.Adj r p ∧
        ∀ t, IsInArborescenceParent G.Adj r t →
          @parentCost _ _ fi de _ c r p ≤ @parentCost _ _ fi de _ c r t) ∧
      (oV = none → ∀ t, ¬ IsInArborescenceParent G.Adj r t)) (θ : ℤ) :
    o.elim false (fun pL => decide ((((List.range n).filter fun v => v != r.1).map fun v =>
        cL v (pL.getD v 0)).sum ≤ θ)) = true ↔
      ∃ T : Digraph (Fin n), T.IsInArborescence r ∧ T ≤ G ∧
        @arcCost (Fin n) ℤ (Fin.fintype n) _ T (Classical.decRel _) c ≤ θ := by
  have hcost (t : Fin n → Fin n) : @parentCost _ _ fi de _ c r t =
      @arcCost (Fin n) ℤ (Fin.fintype n) _ (Digraph.parentDigraph r t) (Classical.decRel _) c :=
    (@arcCost_parentDigraph _ _ fi de _ r t c).symm.trans (arcCost_congr _ _ _ _ rfl c)
  cases o <;> cases oV <;> simp only at ho
  · simp only [Option.elim_none, Bool.false_eq_true, false_iff, not_exists]
    rintro T ⟨hT, hTG, -⟩
    obtain ⟨t, htr, rfl⟩ := hT.exists_parentDigraph_eq
    exact hspec.2 rfl t ((isInArborescenceParent_iff htr).mpr ⟨hT, hTG⟩)
  · rename_i pL p
    obtain ⟨hp, hmin⟩ := hspec.1 p rfl
    rw [Option.elim_some, decide_eq_true_eq, ← arcCost_parentDigraph_eq_sum_range hc r p pL ho.2,
      arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl c]
    obtain ⟨hT, hTG⟩ := (isInArborescenceParent_iff hp.root).mp hp
    refine ⟨fun hle => ⟨_, hT, hTG, hle⟩, fun ⟨T, hT', hTG', hle⟩ => ?_⟩
    obtain ⟨t, htr, rfl⟩ := hT'.exists_parentDigraph_eq
    have h := hmin t ((isInArborescenceParent_iff htr).mpr ⟨hT', hTG'⟩)
    rw [hcost, hcost] at h
    exact h.trans hle

/-- `adjAt a` as the Boolean form of a relation `R` that it decides. -/
private theorem tableAdj_eq_decide {n : ℕ} {a : List (List Bool)} {R : Fin n → Fin n → Prop}
    [DecidableRel R] (h : ∀ u w, R u w ↔ adjAt a u.1 w.1 = true) :
    tableAdj n a = fun u w => decide (R u w) := by
  funext u w
  simp [tableAdj, h]

theorem minArborescenceDecide_eq_true_iff (d : ArborescenceDecInstance) :
    minArborescenceDecide d = true ↔ d ∈ minArborescenceDec := by
  unfold minArborescenceDecide minArborescenceDec edmondsList clampedRoot
  by_cases hr : d.inst.root < d.inst.adj.length
  · let _ := localFinEnum d.inst.adj.length
    have h := runListAux_eq_edmondsAux (localFinEnum_toList _) rfl ⟨d.inst.root, hr⟩
      d.inst.adj.length d.inst.adj d.inst.cost rfl
    rw [tableAdj_eq_decide (R := (tableDigraph d.inst.adj).Adj) fun _ _ => Iff.rfl] at h
    simp only [show ((d.inst.root : ℤ) < d.inst.adj.length) by omega, decide_true, ↓reduceIte,
      edmondsTableAuxList_eq_runListAux, Set.mem_ofPred_eq, exists_prop_of_true hr]
    exact elim_decide_iff_of_spec (c := tableCost d.inst.cost) (cL := costAt d.inst.cost)
      (fun _ _ => rfl) h (edmonds_spec (r := (⟨d.inst.root, hr⟩ : Fin d.inst.adj.length))) _
  · simp [hr]

theorem minArborescenceDec_mem_P :
    minArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  ⟨minArborescenceDecide, computableInPolyTime_minArborescenceDecide,
    fun d => (minArborescenceDecide_eq_true_iff d).symm⟩

private theorem transposeBoolTable_adj {a : List (List Bool)} {n : ℕ} (ha : a.length = n)
    (u w : Fin n) : tableAdj n (transposeBoolTable a) u w = tableAdj n a w u := by
  have hu : u.1 < a.length := ha.symm ▸ u.2
  have hw : w.1 < a.length := ha.symm ▸ w.2
  unfold tableAdj adjAt transposeBoolTable
  rw [list_getD_map_range _ _ _ _ hu, list_getD_map_range _ _ _ _ hw]
  rfl

private theorem transposeIntTable_cost {n : ℕ} (c : List (List ℤ)) (u w : Fin n) :
    tableCost (transposeIntTable n c) u w = tableCost c w u := by
  unfold tableCost costAt transposeIntTable
  rw [list_getD_map_range _ _ _ _ u.2, list_getD_map_range _ _ _ _ w.2]
  rfl

private theorem arcCost_reverse {V β : Type*} [Fintype V] [AddCommMonoid β]
    (T : Digraph V) [DecidableRel T.Adj] [DecidableRel T.reverse.Adj] (c : V → V → β) :
    arcCost T.reverse (fun u w => c w u) = arcCost T c := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => by
    simp [Digraph.reverse_adj]

theorem minOutArborescenceDecide_eq_true_iff (d : ArborescenceDecInstance) :
    minOutArborescenceDecide d = true ↔ d ∈ minOutArborescenceDec := by
  unfold minOutArborescenceDecide minOutArborescenceDec edmondsOutList clampedRoot
  by_cases hr : d.inst.root < d.inst.adj.length
  · let _ := localFinEnum d.inst.adj.length
    have h := runListAux_eq_edmondsAux (localFinEnum_toList _) rfl ⟨d.inst.root, hr⟩
      d.inst.adj.length (transposeBoolTable d.inst.adj)
      (transposeIntTable d.inst.adj.length d.inst.cost) (by simp [transposeBoolTable])
    rw [tableAdj_eq_decide (R := (tableDigraph d.inst.adj).reverse.Adj) fun u w => by
        change _ ↔ tableAdj _ _ u w = true; rw [transposeBoolTable_adj rfl]; rfl,
      show tableCost (transposeIntTable _ d.inst.cost) = fun u w => tableCost d.inst.cost w u
        from funext₂ (transposeIntTable_cost d.inst.cost)] at h
    simp only [show ((d.inst.root : ℤ) < d.inst.adj.length) by omega, decide_true, ↓reduceIte,
      edmondsTableAuxList_eq_runListAux, Set.mem_ofPred_eq, exists_prop_of_true hr]
    refine (elim_decide_iff_of_spec (G := (tableDigraph d.inst.adj).reverse)
      (c := fun u w => tableCost d.inst.cost w u) (cL := fun u w => costAt d.inst.cost w u)
      (r := ⟨d.inst.root, hr⟩) (fun _ _ => rfl) h
      (edmondsOut_spec (G := tableDigraph d.inst.adj) (c := tableCost d.inst.cost)) _).trans
      ⟨fun ⟨T, hT, hTG, hle⟩ => ⟨T.reverse, hT, fun _ _ h => hTG h, ?_⟩,
        fun ⟨T, hT, hTG, hle⟩ => ⟨T.reverse, hT, fun _ _ h => hTG h, ?_⟩⟩
    · exact (@arcCost_reverse _ _ _ _ T.reverse (Classical.decRel _) (Classical.decRel _)
        _).symm.trans_le hle
    · exact (@arcCost_reverse _ _ _ _ T (Classical.decRel _) (Classical.decRel _) _).trans_le hle
  · simp [hr]

theorem minOutArborescenceDec_mem_P :
    minOutArborescenceDec ∈ Cslib.Complexity.P encArborescenceDecInstance :=
  ⟨minOutArborescenceDecide, computableInPolyTime_minOutArborescenceDecide,
    fun d => (minOutArborescenceDecide_eq_true_iff d).symm⟩

private def mapDigraph {α β : Type*} (φ : α ≃ β) (G : Digraph α) : Digraph β where
  Adj x y := G.Adj (φ.symm x) (φ.symm y)

private instance instDecidableRelMapDigraph {α β : Type*} (φ : α ≃ β) (G : Digraph α)
    [DecidableRel G.Adj] : DecidableRel (mapDigraph φ G).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj (φ.symm x) (φ.symm y)))

private theorem isInArborescence_mapDigraph {α β : Type*} (φ : α ≃ β) {G : Digraph α} {r : α} :
    (mapDigraph φ G).IsInArborescence (φ r) ↔ G.IsInArborescence r := by
  have hwalk : ∀ x y : α, Relation.ReflTransGen (mapDigraph φ G).Adj (φ x) (φ y) ↔
      Relation.ReflTransGen G.Adj x y := by
    intro x y
    constructor
    · intro h
      have : ∀ a b, Relation.ReflTransGen (mapDigraph φ G).Adj a b →
          Relation.ReflTransGen G.Adj (φ.symm a) (φ.symm b) := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep ih => exact ih.tail hstep
      simpa using this (φ x) (φ y) h
    · intro h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih => exact ih.tail (by simpa [mapDigraph] using hstep)
  constructor
  · intro h
    refine ⟨fun y hy => h.not_adj_root (φ y) (by simpa [mapDigraph] using hy), ?_, ?_⟩
    · intro v hv
      obtain ⟨w, hw, hu⟩ := h.existsUnique_adj (φ v) (fun h => hv (φ.injective h))
      refine ⟨φ.symm w, by simpa [mapDigraph] using hw, fun u hu' => ?_⟩
      exact Eq.symm (φ.symm_apply_eq.mpr (hu (φ u) (by simpa [mapDigraph] using hu')).symm)
    · exact fun v => (hwalk v r).mp (h.reachable (φ v))
  · intro h
    refine ⟨fun y hy => h.not_adj_root (φ.symm y) (by simpa [mapDigraph] using hy),
      fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨w, hw, hu⟩ := h.existsUnique_adj (φ.symm v) (fun h => hv (φ.symm_apply_eq.mp h))
      refine ⟨φ w, by simpa [mapDigraph] using hw, fun u hu' => ?_⟩
      exact φ.symm_apply_eq.mp (hu (φ.symm u) (by simpa [mapDigraph] using hu'))
    · simpa using (hwalk (φ.symm v) r).mpr (h.reachable (φ.symm v))

private theorem arcCost_mapDigraph {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (φ : α ≃ β) (G : Digraph α) [DecidableRel G.Adj] [DecidableRel (mapDigraph φ G).Adj]
    (c : β → β → γ) :
    arcCost (mapDigraph φ G) c = arcCost G (fun u w => c (φ u) (φ w)) := by
  unfold arcCost
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (φ.prodCongr φ) _ _ fun e => ?_).symm
  simp [mapDigraph]

private theorem superRootAdjList_getD (a : List (List Bool)) {u w : ℕ}
    (hu : u < a.length + 1) (hw : w < a.length + 1) :
    adjAt (superRootAdjList a) u w =
      if u == a.length then false else if w == a.length then true else adjAt a w u := by
  unfold adjAt superRootAdjList
  rw [list_getD_map_range _ _ _ _ hu, list_getD_map_range _ _ _ _ hw]
  rfl

private theorem superRootWeightList_getD (n : ℕ) (wt : List (List ℤ)) {u w : ℕ}
    (hu : u < n + 1) (hw : w < n + 1) :
    costAt (superRootWeightList n wt) u w =
      if u == n then 0 else if w == n then 0 else -costAt wt w u := by
  unfold costAt superRootWeightList
  rw [list_getD_map_range _ _ _ _ hu, list_getD_map_range _ _ _ _ hw]
  rfl

theorem maxBranchingDecide_eq_true_iff (d : BranchingDecInstance) :
    maxBranchingDecide d = true ↔ d ∈ maxBranchingDec := by
  let _ := localFinEnum d.inst.adj.length
  set n := d.inst.adj.length
  set adj' := superRootAdjList d.inst.adj
  set wt' := superRootWeightList n d.inst.weight
  set r : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  let G' : Digraph (Fin (n + 1)) := ⟨fun u w => tableAdj (n + 1) adj' u w = true⟩
  let _ : DecidableRel G'.Adj :=
    fun u w => inferInstanceAs (Decidable (tableAdj (n + 1) adj' u w = true))
  let e : Fin (n + 1) ≃ Option (Fin n) :=
    { toFun := fun x => if h : x.1 < n then some ⟨x.1, h⟩ else none
      invFun := fun o => o.elim r fun v => ⟨v.1, Nat.lt_succ_of_lt v.2⟩
      left_inv := fun x => by
        dsimp only
        split_ifs with h
        · rfl
        · ext; exact (Nat.eq_of_le_of_lt_succ (Nat.le_of_not_lt h) x.2).symm
      right_inv := fun o => by
        cases o with
        | none => simp [r]
        | some v => simp [v.2] }
  have he_none : e r = none := by simp [e, r]
  have he_symm_none : e.symm none = r := rfl
  have he_some (v : Fin n) : e ⟨v.1, Nat.lt_succ_of_lt v.2⟩ = some v := by
    simp [e, v.2]
  have he_symm_some (v : Fin n) : e.symm (some v) = ⟨v.1, Nat.lt_succ_of_lt v.2⟩ := rfl
  have ha'_len : adj'.length = n + 1 := by simp [adj', superRootAdjList, n]
  have hcase (u : Fin (n + 1)) : (∃ h : u.1 < n, (u.1 == n) = false ∧ e u = some ⟨u.1, h⟩) ∨
      ((u.1 == n) = true ∧ e u = none) := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ u.2) with hu | hu
    · exact .inl ⟨hu, beq_false_of_ne hu.ne, he_some ⟨u.1, hu⟩⟩
    · exact .inr ⟨beq_iff_eq.mpr hu, by rw [← he_none]; congr 1; exact Fin.ext hu⟩
  have hsuper_adj : ∀ u w : Fin (n + 1),
      G'.Adj u w ↔ (tableDigraph d.inst.adj).superRootDigraph.Adj (e u) (e w) := by
    intro u w
    change adjAt adj' u.1 w.1 = true ↔ _
    rw [superRootAdjList_getD d.inst.adj u.2 w.2]
    rcases hcase u with ⟨_, hu, heu⟩ | ⟨hu, heu⟩ <;>
      rcases hcase w with ⟨_, hw, hew⟩ | ⟨hw, hew⟩ <;>
      dsimp only [n] at hu hw <;>
      simp [hu, hw, heu, hew, Digraph.superRootDigraph, tableDigraph]
  have hsuper_cost : ∀ u w : Fin (n + 1),
      tableCost wt' u w = superRootCost (tableCost d.inst.weight) (e u) (e w) := by
    intro u w
    change costAt wt' u.1 w.1 = _
    rw [superRootWeightList_getD n d.inst.weight u.2 w.2]
    rcases hcase u with ⟨_, hu, heu⟩ | ⟨hu, heu⟩ <;>
      rcases hcase w with ⟨_, hw, hew⟩ | ⟨hw, hew⟩ <;>
      simp [hu, hw, heu, hew, superRootCost, tableCost]
  have hfeas : IsInArborescenceParent (fun u w => G'.Adj u w) r (fun _ => r) := by
    refine ⟨rfl, fun x hx => ?_, fun _ => ⟨1, rfl⟩⟩
    rw [hsuper_adj x r, he_none]
    have hne : e x ≠ none := fun h => hx (e.injective (h.trans he_none.symm))
    rcases Option.ne_none_iff_exists'.mp hne with ⟨v, hv⟩
    rw [hv]
    trivial
  let _ := localFinEnum (n + 1)
  have hrun_eq := @runListAux_eq_edmondsAux (n + 1) (localFinEnum (n + 1))
    (localFinEnum_toList (n + 1)) rfl r (n + 1) adj' wt' ha'_len
  have hed_isSome :
      ∃ pV, @edmonds (Fin (n + 1)) ℤ (localFinEnum (n + 1)) _ _ G' _
        (tableCost wt') r = some pV := by
    by_cases hnone :
        @edmonds (Fin (n + 1)) ℤ (localFinEnum (n + 1)) _ _ G' _
          (tableCost wt') r = none
    · exact absurd hfeas (edmonds_spec.2 hnone _)
    · exact Option.ne_none_iff_exists'.mp hnone
  obtain ⟨pV, hpV⟩ := hed_isSome
  have hG'_adj : (fun u w : Fin (n + 1) => decide (G'.Adj u w)) = tableAdj (n + 1) adj' := by
    funext u w; simp [G', Bool.decide_eq_true]
  have hpV' : @edmondsAux (Fin (n + 1)) ℤ (localFinEnum (n + 1)) _ _ r (n + 1)
      (tableAdj (n + 1) adj') (tableCost wt') = some pV := by
    have h := hpV
    unfold edmonds at h
    rw [← hG'_adj]
    exact h
  rw [hpV'] at hrun_eq
  obtain ⟨pL, hpL_eq, hpL_len, hpL_val⟩ :
      ∃ pL, edmondsTableAuxList (n + 1) n adj' wt' = some pL ∧
        pL.length = n + 1 ∧ ∀ v : Fin (n + 1), pL.getD v.1 0 = (pV v).1 := by
    rw [edmondsTableAuxList_eq_runListAux]
    cases hL : runListAux r.1 (n + 1) adj' wt' with
    | none => simp [hL] at hrun_eq
    | some pL =>
      simp only [hL] at hrun_eq
      exact ⟨pL, rfl, hrun_eq.1, hrun_eq.2⟩
  obtain ⟨hT, hTG, hoptT⟩ := edmonds_optimal hpV
  have hT_map_arb : (mapDigraph e (Digraph.parentDigraph r pV)).IsInArborescence none := by
    rw [← he_none]
    exact (isInArborescence_mapDigraph e).mpr hT
  have hT_map_le :
      mapDigraph e (Digraph.parentDigraph r pV) ≤ (tableDigraph d.inst.adj).superRootDigraph := by
    intro x y hxy
    have hxy' := hTG hxy
    change G'.Adj (e.symm x) (e.symm y) at hxy'
    rw [hsuper_adj] at hxy'
    simpa using hxy'
  obtain ⟨hB_branch, hB_ext, hB_le⟩ := Digraph.restrictOption_spec hT_map_arb
  set Bstar := Digraph.restrictOption (mapDigraph e (Digraph.parentDigraph r pV))
  have hBstar_le : Bstar ≤ tableDigraph d.inst.adj := hB_le _ hT_map_le
  have hBstar_eq_p : Bstar = Digraph.branchingDigraph (fun v : Fin n =>
      let pv := (optimumBranchingList d.inst).getD v.1 0
      if h : pv < n then ⟨pv, h⟩ else v) := by
    ext u v
    simp only [Bstar, Digraph.restrictOption_adj, Digraph.branchingDigraph_adj, mapDigraph,
      Digraph.parentDigraph_adj, he_symm_some]
    have hvn : v.1 < n := v.2
    have hopt_get : (optimumBranchingList d.inst).getD v.1 0 =
        if pL.getD v.1 0 == n then v.1 else pL.getD v.1 0 := by
      unfold optimumBranchingList
      dsimp only
      change ((edmondsTableAuxList (n + 1) n adj' wt').elim []
          (fun p => (List.range n).map fun v =>
            let pv := p.getD v 0; if pv == n then v else pv)).getD v.1 0 = _
      rw [hpL_eq, Option.elim_some, List.getD_eq_getElem _ _ (by simp [hvn]),
        List.getElem_map, List.getElem_range]
    have hpv_lt := hpL_val ⟨v.1, Nat.lt_succ_of_lt v.2⟩
    have hv_ne : (⟨v.1, Nat.lt_succ_of_lt v.2⟩ : Fin (n + 1)) ≠ r := by
      simp [Fin.ext_iff, r, v.2.ne]
    by_cases hpr : pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩ = r
    · have hpn : pL.getD v.1 0 = n := by rw [hpv_lt, hpr]
      rw [hopt_get, hpn]
      simp [hpr, r, Fin.ext_iff, v.2.ne, u.2.ne.symm]
    · have hplt : (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).1 < n := by
        have hlt := (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).2
        have hne : (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).1 ≠ n := fun h => hpr (Fin.ext h)
        omega
      dsimp only at hpv_lt
      have hp_ne : (pL.getD v.1 0 == n) = false := beq_false_of_ne (by omega)
      have hval : (optimumBranchingList d.inst).getD v.1 0 =
          (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).1 := by
        rw [hopt_get, hp_ne]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hpv_lt
      have hP : (let pv := (optimumBranchingList d.inst).getD v.1 0
          if h : pv < n then ⟨pv, h⟩ else v) = ⟨(pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).1, hplt⟩ := by
        dsimp only
        split_ifs with hlt
        · exact Fin.ext hval
        · exact absurd (hval.symm ▸ hplt) hlt
      rw [hP]
      constructor
      · rintro ⟨_, h⟩
        have hval_h : (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).1 = u.1 :=
          congrArg (@Fin.val (n + 1)) h
        refine ⟨fun hvu => ?_, Fin.ext hval_h⟩
        have hself : pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩ = ⟨v.1, Nat.lt_succ_of_lt v.2⟩ :=
          Fin.ext (congrArg (@Fin.val n) hvu)
        have hloop : (Digraph.parentDigraph r pV).Adj
            ⟨v.1, Nat.lt_succ_of_lt v.2⟩ ⟨v.1, Nat.lt_succ_of_lt v.2⟩ := ⟨hv_ne, hself⟩
        have hc := Relation.TransGen.single (show Bstar.Adj v v from by
          simpa [Bstar, mapDigraph, he_symm_some] using hloop)
        exact hB_branch.acyclic hc
      · rintro ⟨_, hpu⟩
        exact ⟨hv_ne, Fin.ext (congrArg (@Fin.val n) hpu)⟩
  have hsum_eq : (((List.range n).filter fun v => (optimumBranchingList d.inst).getD v 0 != v).map
      fun v => costAt d.inst.weight ((optimumBranchingList d.inst).getD v 0) v).sum =
      @arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid Bstar
        (Classical.decRel _) (tableCost d.inst.weight) := by
    let P_fun : Fin n → Fin n := fun v : Fin n =>
      let pv := (optimumBranchingList d.inst).getD v.1 0
      if h : pv < n then ⟨pv, h⟩ else v
    have hopt_lt : ∀ v : Fin n, (optimumBranchingList d.inst).getD v.1 0 < n := by
      intro v
      unfold optimumBranchingList
      dsimp only
      rw [show edmondsTableAuxList (n + 1) n (superRootAdjList d.inst.adj)
          (superRootWeightList n d.inst.weight) = some pL from hpL_eq,
        Option.elim_some, List.getD_eq_getElem _ _ (by dsimp only [n]; simp),
        List.getElem_map, List.getElem_range]
      have hv_val := hpL_val ⟨v.1, Nat.lt_succ_of_lt v.2⟩
      dsimp only at hv_val
      have hpV_lt := (pV ⟨v.1, Nat.lt_succ_of_lt v.2⟩).2
      split_ifs with heq
      · exact v.2
      · have hne' : pL.getD v.1 0 ≠ n := fun h => heq (beq_iff_eq.mpr h)
        omega
    have hPv : ∀ v : Fin n, P_fun v = ⟨(optimumBranchingList d.inst).getD v.1 0, hopt_lt v⟩ := by
      intro v
      dsimp only [P_fun]
      split_ifs with hlt
      · rfl
      · exact absurd (hopt_lt v) hlt
    have hBstar_sub : @arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid Bstar
          (Classical.decRel _) (tableCost d.inst.weight) =
        @arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid
          (Digraph.branchingDigraph P_fun) (Classical.decRel _) (tableCost d.inst.weight) :=
      arcCost_congr (Fin.fintype n) (Fin.fintype n) (Classical.decRel _) (Classical.decRel _)
        hBstar_eq_p (tableCost d.inst.weight)
    rw [hBstar_sub]
    unfold arcCost
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    have hpt : ∀ u : Fin n,
        ∑ v : Fin n, (if (Digraph.branchingDigraph P_fun).Adj u v then
            tableCost d.inst.weight u v else 0) =
          ∑ v : Fin n, if (optimumBranchingList d.inst).getD v.1 0 != v.1 ∧
            (optimumBranchingList d.inst).getD v.1 0 = u.1 then
            costAt d.inst.weight ((optimumBranchingList d.inst).getD v.1 0) v.1 else 0 := by
      intro u
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [Digraph.branchingDigraph_adj, hPv v]
      split_ifs with h1 h2 h2
      · dsimp only [tableCost]
        rw [h2.2]
      · exfalso
        apply h2
        refine ⟨bne_iff_ne.mpr fun heq => h1.1 (Fin.ext heq), congrArg Fin.val h1.2⟩
      · exfalso
        rcases h2 with ⟨hne, hu⟩
        apply h1
        exact ⟨fun h => (bne_iff_ne.mp hne) (congrArg (@Fin.val n) h), Fin.ext hu⟩
      · rfl
    simp_rw [hpt]
    rw [Finset.sum_comm]
    have hinner : ∀ v : Fin n,
        ∑ u : Fin n, (if (optimumBranchingList d.inst).getD v.1 0 != v.1 ∧
            (optimumBranchingList d.inst).getD v.1 0 = u.1 then
            costAt d.inst.weight ((optimumBranchingList d.inst).getD v.1 0) v.1 else 0) =
          if (optimumBranchingList d.inst).getD v.1 0 != v.1 then
            costAt d.inst.weight ((optimumBranchingList d.inst).getD v.1 0) v.1 else 0 := by
      intro v
      by_cases hne : (optimumBranchingList d.inst).getD v.1 0 != v.1
      · simp only [hne, true_and]
        rw [Finset.sum_eq_single ⟨(optimumBranchingList d.inst).getD v.1 0, hopt_lt v⟩]
        · simp
        · intro u _ hu
          rw [ite_eq_right_iff.mpr fun h => absurd (Fin.ext h.symm) hu]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hne_false : ((optimumBranchingList d.inst).getD v.1 0 != v.1) = false :=
          Bool.eq_false_iff.mpr hne
        rw [hne_false]
        simp
    simp_rw [hinner]
    have hnd : ((List.finRange n).filter fun v : Fin n =>
        (optimumBranchingList d.inst).getD v.1 0 != v.1).Nodup :=
      (List.nodup_finRange n).filter _
    have hset : ((List.finRange n).filter fun v : Fin n =>
        (optimumBranchingList d.inst).getD v.1 0 != v.1).toFinset =
        Finset.univ.filter fun v : Fin n =>
          (optimumBranchingList d.inst).getD v.1 0 != v.1 := by
      ext v; simp
    rw [← Finset.sum_filter, ← hset, List.sum_toFinset _ hnd]
    rw [← map_val_finRange n, List.filter_map, List.map_map]
    rfl
  have hBstar_opt : ∀ (B₁ : Digraph (Fin n)) [DecidableRel B₁.Adj],
      B₁.IsBranching → B₁ ≤ tableDigraph d.inst.adj →
      @arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid B₁ (Classical.decRel _)
          (tableCost d.inst.weight) ≤
        @arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid Bstar (Classical.decRel _)
          (tableCost d.inst.weight) := by
    intro B₁ _ hB₁ hB₁G
    classical
    have h1 : (B₁.superRootExtend).IsInArborescence none :=
      Digraph.isBranching_iff_isInArborescence_superRootExtend.mp hB₁
    have h2 : B₁.superRootExtend ≤ (tableDigraph d.inst.adj).superRootDigraph :=
      Digraph.superRootExtend_le_superRootDigraph hB₁G
    let T₁ := mapDigraph e.symm B₁.superRootExtend
    have hT₁_arb : T₁.IsInArborescence r := by
      have := (isInArborescence_mapDigraph e.symm).mpr h1
      simpa [he_symm_none] using this
    have hT₁_le : T₁ ≤ G' := by
      intro x y hxy
      rw [hsuper_adj]
      exact h2 (by simpa [T₁, mapDigraph] using hxy)
    have hcmp := hoptT T₁ hT₁_arb hT₁_le
    have hlhs : @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype Int.instAddCommMonoid
          (Digraph.parentDigraph r pV) (Classical.decRel _) (tableCost wt') =
        -@arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid Bstar (Classical.decRel _)
          (tableCost d.inst.weight) := by
      calc @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype Int.instAddCommMonoid
            (Digraph.parentDigraph r pV) (Classical.decRel _) (tableCost wt')
          = arcCost (Digraph.parentDigraph r pV)
              (fun u w => superRootCost (tableCost d.inst.weight) (e u) (e w)) := by
            unfold arcCost
            refine Finset.sum_congr (by ext p; simp) fun p _ => hsuper_cost p.1 p.2
        _ = arcCost (mapDigraph e (Digraph.parentDigraph r pV))
              (superRootCost (tableCost d.inst.weight)) :=
            (arcCost_mapDigraph e _ _).symm
        _ = @arcCost (Option (Fin n)) ℤ inferInstance _ Bstar.superRootExtend
              (Classical.decRel _) (superRootCost (tableCost d.inst.weight)) :=
            arcCost_congr _ _ _ (Classical.decRel _)
              hB_ext.symm (superRootCost (tableCost d.inst.weight))
        _ = -@arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid Bstar (Classical.decRel _)
              (tableCost d.inst.weight) := by
            rw [arcCost_superRootExtend Bstar (tableCost d.inst.weight),
              arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl
                (tableCost d.inst.weight)]
    have hrhs : @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype Int.instAddCommMonoid
          T₁ (Classical.decRel _) (tableCost wt') =
        -@arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid B₁ (Classical.decRel _)
          (tableCost d.inst.weight) := by
      calc @arcCost (Fin (n + 1)) ℤ FinEnum.instFintype Int.instAddCommMonoid
            T₁ (Classical.decRel _) (tableCost wt')
          = arcCost T₁ (fun u w => superRootCost (tableCost d.inst.weight) (e u) (e w)) := by
            unfold arcCost
            refine Finset.sum_congr (by ext p; simp) fun p _ => hsuper_cost p.1 p.2
        _ = arcCost B₁.superRootExtend (superRootCost (tableCost d.inst.weight)) := by
            have h := arcCost_mapDigraph e.symm B₁.superRootExtend
              (fun u w => superRootCost (tableCost d.inst.weight) (e u) (e w))
            have hc : (fun u w => superRootCost (tableCost d.inst.weight)
                (e (e.symm u)) (e (e.symm w))) = superRootCost (tableCost d.inst.weight) := by
              funext u w; simp only [Equiv.apply_symm_apply]
            dsimp only [T₁]
            rw [arcCost_congr _ _ _ _ rfl _, h, hc]
        _ = -@arcCost (Fin n) ℤ (Fin.fintype n) Int.instAddCommMonoid B₁ (Classical.decRel _)
              (tableCost d.inst.weight) := by
            rw [arcCost_superRootExtend B₁ (tableCost d.inst.weight),
              arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl
                (tableCost d.inst.weight)]
    rw [arcCost_congr (T₁ := Digraph.parentDigraph r pV) _ FinEnum.instFintype _
        (Classical.decRel _) rfl (tableCost wt'),
      arcCost_congr (T₁ := T₁) _ FinEnum.instFintype _
        (Classical.decRel _) rfl (tableCost wt')] at hcmp
    rw [hlhs, hrhs] at hcmp
    exact neg_le_neg_iff.mp hcmp
  unfold maxBranchingDecide maxBranchingDec
  dsimp only
  change decide (d.threshold ≤ (((List.range n).filter fun v =>
      (optimumBranchingList d.inst).getD v 0 != v).map fun v =>
      costAt d.inst.weight ((optimumBranchingList d.inst).getD v 0) v).sum) = true ↔ _
  rw [hsum_eq, decide_eq_true_eq]
  constructor
  · intro hth
    refine ⟨Bstar, hB_branch, hBstar_le, ?_⟩
    rw [arcCost_congr _ (Fin.fintype n) _ (Classical.decRel _) rfl
      (tableCost d.inst.weight)]
    exact hth
  · rintro ⟨B₁, hB₁, hB₁G, hle₁⟩
    classical
    have hc := hBstar_opt B₁ hB₁ hB₁G
    rw [arcCost_congr (T₁ := B₁) _ (Fin.fintype n) _ (Classical.decRel _) rfl
        (tableCost d.inst.weight)] at hle₁
    exact hle₁.trans hc

theorem maxBranchingDec_mem_P :
    maxBranchingDec ∈ Cslib.Complexity.P encBranchingDecInstance :=
  ⟨maxBranchingDecide, computableInPolyTime_maxBranchingDecide,
    fun d => (maxBranchingDecide_eq_true_iff d).symm⟩

end Cslib.Algorithms.Lean.Arborescence
