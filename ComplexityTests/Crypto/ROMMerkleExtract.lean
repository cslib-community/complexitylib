/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MerkleDamgard
import Complexity.Crypto.Computational.MerkleTree.ROMExtract

/-!
# Tests for straight-line Merkle trace extraction in the random-oracle model

Under an injective hash (`idHash`), a trace recording the hash evaluations along all four paths of
a depth-two Merkle tree is collision-free, and `extractTableFromTrace` recovers all four leaves
directly from the trace without rewinding. A partial trace recording only the path for position `2`
recovers leaf `2` while leaving the unqueried sibling subtree as `none`. Under a colliding hash
(`xorHash`), a trace recording both the honest tree and a colliding leaf at position `1` accepts
both openings; because `extractLeafFromTrace` returns the first-recorded leaf `[false, true]`,
`extractTraceCollision` on the conflicting opening `[true, true]` deterministically extracts a hash
collision from the trace. Finally, we check the random-oracle collision probability bound on a
concrete two-query `OracleComp` program.
-/

namespace ComplexityTests.Crypto.ROMMerkleExtract

open Cslib Cslib.Crypto Cslib.Probability OracleComp Turing.MultiTapeTM
open scoped ENNReal

/-- Four leaves in a tree of depth two. -/
abbrev leaves : List (List Bool) := [[true], [false, true], [true, false], [true, true]]

/-- The key at security parameter `2`. -/
abbrev key : List Bool := [false, true]

/-- An injective hash returning its input unchanged. -/
def idHash (_ x : List Bool) : List Bool := x

/-- Record `(q, H k q)` for every hash input along `(leaf, i, path)`. -/
def pathTrace (H : List Bool → List Bool → List Bool) (k : List Bool) (i : ℕ) (leaf : List Bool)
    (path : List (List Bool)) : List (List Bool × List Bool) :=
  (merkleInputs H k leaf i path).map fun q => (q, H k q)

/-- Full trace recording all four openings of `leaves` at depth two. -/
def fullTreeTrace (H : List Bool → List Bool → List Bool) (k : List Bool) :
    List (List Bool × List Bool) :=
  ((List.range 4).flatMap fun i =>
    pathTrace H k i (leaves.getD i []) (merklePath H k leaves i)).eraseDups

/-! ### Straight-line extraction on a collision-free trace -/

abbrev rtId : List Bool := merkleRoot idHash key leaves
abbrev trId : List (List Bool × List Bool) := fullTreeTrace idHash key

example : TraceConsistentWith (idHash key) trId := by decide

example : TraceCollisionFree trId := by decide

example : ∀ i : Fin 4,
    PathQueriedInTrace idHash key trId i (leaves.getD i [])
      (merklePath idHash key leaves i) := by decide

-- Straight-line extraction recovers every leaf and the entire table from the query trace alone.
example : ∀ i : Fin 4,
    extractLeafFromTrace trId 2 rtId i = some (leaves.getD i []) := by decide

example : extractTableFromTrace trId 2 rtId [] = leaves := by decide

-- Applying `extractLeafFromTrace_eq_some_of_merkleVerify` and
-- `getD_extractTableFromTrace_eq_of_merkleVerify` to position `2`.
example : extractLeafFromTrace trId 2 rtId 2 = some [true, false] :=
  extractLeafFromTrace_eq_some_of_merkleVerify (H := idHash) (k := key)
    (path := merklePath idHash key leaves 2) (by decide) (by decide) (by decide)

example : (extractTableFromTrace trId 2 rtId []).getD 2 [] = [true, false] :=
  getD_extractTableFromTrace_eq_of_merkleVerify (H := idHash) (k := key)
    (path := merklePath idHash key leaves 2) (by decide) (by decide) (by decide)

/-! ### Partial trace: only queried paths are extracted -/

abbrev trPartial : List (List Bool × List Bool) :=
  pathTrace idHash key 2 [true, false] (merklePath idHash key leaves 2)

example : TraceCollisionFree trPartial := by decide

-- Position `2` is recovered because its path is in `trPartial`.
example : extractLeafFromTrace trPartial 2 rtId 2 = some [true, false] := by decide

-- Position `0` is in the unqueried left subtree (only its root digest appears as a sibling),
-- so `extractLeafFromTrace` returns `none` and `extractTableFromTrace` falls back to `defaultLeaf`.
example : extractLeafFromTrace trPartial 2 rtId 0 = none := by decide

example : (extractTableFromTrace trPartial 2 rtId [false, false]).getD 0 [false, false] =
    [false, false] := by decide

/-! ### Dual collision extraction under colliding hashes -/

/-- A toy hash that maps `[true, true]` to `[false, true]` and acts as the identity elsewhere,
creating a single leaf collision between `[false, true]` and `[true, true]`. -/
def collideLeavesHash (_ x : List Bool) : List Bool :=
  if x == [true, true] then [false, true] else x

abbrev rtCollide : List Bool := merkleRoot collideLeavesHash key leaves
abbrev pathCollide1 : List (List Bool) := merklePath collideLeavesHash key leaves 1

/-- Trace recording the honest opening of position `1` (`[false, true]`) followed by the colliding
leaf query `[true, true]`. -/
abbrev trCollide : List (List Bool × List Bool) :=
  pathTrace collideLeavesHash key 1 [false, true] pathCollide1 ++
    pathTrace collideLeavesHash key 1 [true, true] pathCollide1

example : TraceConsistentWith (collideLeavesHash key) trCollide := by decide

-- Because `[false, true]` and `[true, true]` both hash to `[false, true]`, the combined trace is
-- not collision-free.
example : ¬ TraceCollisionFree trCollide := by decide

-- Both `[false, true]` and `[true, true]` verify at position `1` with all path queries in
-- `trCollide`.
example : merkleVerify collideLeavesHash key 2 rtCollide 1 [true, true] pathCollide1 = true := by
  decide

example : PathQueriedInTrace collideLeavesHash key trCollide 1 [true, true] pathCollide1 := by
  decide

-- The straight-line extractor returns the first-recorded leaf `[false, true]`, disagreeing with
-- the second valid opening `[true, true]`.
example : extractLeafFromTrace trCollide 2 rtCollide 1 = some [false, true] := by decide

example : extractLeafFromTrace trCollide 2 rtCollide 1 ≠ some [true, true] := by decide

-- `extractTraceCollision` deterministically extracts the colliding pair
-- `([true, true], [false, true])`.
example :
    extractTraceCollision collideLeavesHash key trCollide 1 [true, true] pathCollide1 =
      ([true, true], [false, true]) := by decide

example :
    let col := extractTraceCollision collideLeavesHash key trCollide 1 [true, true] pathCollide1
    (col.1, collideLeavesHash key col.1) ∈ trCollide ∧
      (col.2, collideLeavesHash key col.1) ∈ trCollide ∧
      col.1 ≠ col.2 ∧
      collideLeavesHash key col.1 = collideLeavesHash key col.2 :=
  extractTraceCollision_spec (H := collideLeavesHash) (k := key) (d := 2) (rt := rtCollide)
    (by decide) (by decide) (by decide) (by decide)

/-- A toy keyed hash that XORs the first two `k.length`-bit blocks of its input. -/
def xorHash (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

abbrev rtXor : List Bool := merkleRoot xorHash key leaves
abbrev pathXor1 : List (List Bool) := merklePath xorHash key leaves 1

/-- Trace recording the honest opening of position `1` (`[false, true]`) followed by the colliding
opening `[true, true]` under `xorHash`. -/
abbrev trXor : List (List Bool × List Bool) :=
  pathTrace xorHash key 1 [false, true] pathXor1 ++
    pathTrace xorHash key 1 [true, true] pathXor1

-- `extractTraceCollision` also extracts a valid `xorHash` collision whenever `extractLeafFromTrace`
-- disagrees with an accepted opening in `trXor`.
example :
    let col := extractTraceCollision xorHash key trXor 1 [true, true] pathXor1
    isCollision xorHash (fun _ _ => true) 2 key col.1 col.2 = true :=
  isCollision_extractTraceCollision (H := xorHash) (k := key) (d := 2) (rt := rtXor)
    (by decide) (by decide) (by decide) (by decide) 2

/-! ### Random-oracle collision bound on a query-bounded program -/

/-- A simple two-query ROM program hashing `[false]` and `[true]`. -/
def twoQueryProg : OracleComp (fun _ : List Bool => List Bool) (List Bool × List Bool) := do
  let d₀ ← query [false]
  let d₁ ← query [true]
  return (d₀, d₁)

theorem isQueryBounded_twoQueryProg : IsQueryBounded twoQueryProg 2 :=
  .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

example (m : ℕ) :
    ((OracleComp.interpret (memoize (fun _ : List Bool => BitString.uniformList m))
      twoQueryProg).run []).toOuterMeasure {x | ¬ TraceCollisionFree x.2} ≤
      (2 : ℝ≥0∞) * ((2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m)) :=
  toOuterMeasure_run_memoize_not_traceCollisionFree_le m isQueryBounded_twoQueryProg

end ComplexityTests.Crypto.ROMMerkleExtract
