/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalModel
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalExec
import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalRoot

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

private def fixture : Data 128 where
  regs i := if i = registers Stack.ptr then 20 else if i = registers Stack.len then 0
    else if 64 ≤ i.val ∧ i.val < 71 then i.val - 60 else 79
  mem _ := 79

private def roundTrip : Code .standard 128 := .seq pushFrame popFrame

-- A complete native record round trip restores all seven words, keeps low kernel registers,
-- and preserves memory on both sides of the reserved stack. Old stack contents are nonzero.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 8 16 roundTrip fixture).map (fun (y, _) =>
  (List.ofFn (fun i : Fin 7 => y.regs (slot i)),
    y.regs 0, y.regs (registers Stack.len), y.mem 19, y.mem 27)) =
  some ([4, 5, 6, 7, 8, 9, 10], 79, 0, 79, 79))

-- Address arithmetic really runs in the admitted physical width.
/-- info: true -/
#guard_msgs in
#eval (Code.eval 1 16 pushFrame fixture).isNone

private theorem fixture_rep : Stack.Rep 8 20 7 [] (fixture.comap registers) := by
  refine ⟨?_, ?_, ?_, by decide, fun i => Fin.elim0 i⟩
  · constructor
    · intro i
      change Fits 8 (fixture.regs (registers i))
      dsimp only [fixture]
      split
      · decide
      · split
        · decide
        · split
          · change (registers i).val - 60 < 256
            have := (registers i).isLt
            omega
          · decide
    · intro a
      change Fits 8 79
      decide
  · decide
  · decide

-- The native transfer contracts have a fully admitted client, including old nonzero memory.
example : ∃ y, Exec 8 roundTrip fixture y 163 ∧
    Stack.Rep 8 20 7 [] (y.comap registers) ∧
    (∀ i, y.regs (slot i) = fixture.regs (slot i)) := by
  have hwords (i : Fin 7) : Fits 8 (fixture.regs (slot i)) := by
    dsimp only [fixture]
    split
    · decide
    · split
      · decide
      · split
        · change (slot i).val - 60 < 256
          have := (slot i).isLt
          omega
        · decide
  obtain ⟨z, hz, hrz, _, _⟩ := pushFrame_exec fixture [] (by decide) (by decide)
    fixture_rep hwords (by decide)
  obtain ⟨y, hy, hry, hslots, _, _⟩ := popFrame_exec z []
    (fun i => fixture.regs (slot i)) (by decide) (by decide) hrz
  exact ⟨y, hz.seq hy, hry, hslots⟩

-- Pending entries include zero-fuel calls; capacity bounds are neither empty nor universal.
private def root : Math.Task := ⟨1, fun _ => {0}⟩
example : Math.Bounded 1 [root] ∧ ¬Math.Bounded 0 [root] ∧ Math.work 1 = 4 := by
  norm_num [Math.Bounded, root, Math.work]

-- A zero-fuel call produces no node even with three nonempty sets.
example : (Math.step {2} 1 ⟨0, fun _ => {0}⟩ []).1 = [] ∧
    (Math.step {2} 1 ⟨0, fun _ => {0}⟩ []).2 = none := by
  decide

private def treeInput (f n : ℕ) (z : ℤ) : Data 128 where
  regs i := match i.val with
    | 64 => f
    | 65 => 1
    | 66 => n
    | 67 => 2
    | 68 => n
    | 69 => 3
    | 70 => n
    | 71 => 2
    | 72 => 1
    | 73 => 1
    | 74 => 8
    | 75 => 10
    | 76 => 1
    | 77 => 100
    | 78 => 60
    | 79 => 0
    | 80 => 20
    | 81 => 21
    | _ => 79
  mem a := if a = 1 ∨ a = 2 ∨ a = 3 then Signed.encode z
    else if a = 10 ∨ a = 11 then 0 else if a = 12 then 1 else 79

private def observeTree (f n : ℕ) (z : ℤ) :=
  (Code.eval 16 32 oneRoot (treeInput f n z)).map fun (y, _) =>
    (y.regs outputCount, y.regs heap, y.mem 60, y.regs (registers Stack.len),
      (List.range 32).map (fun i => y.mem (106 + i)))

private def packedSingleton (z : ℤ) : List ℕ :=
  let ν : Cslib.Algorithms.ThreeSum.ChanHe.Node := ⟨{z}, {z}, {z}, 4⟩
  (List.range 32).map fun i => Signed.encode (ν.oneArray 1 i)

-- Zero fuel and empty sets are actually popped and skipped without calling either node kernel.
/-- info: true -/
#guard_msgs in
#eval decide ((observeTree 0 1 0).map (fun r => (r.1, r.2.1, r.2.2.1)) = some (0, 100, 79))

/-- info: true -/
#guard_msgs in
#eval decide ((observeTree 1 0 0).map (fun r => (r.1, r.2.1, r.2.2.1)) = some (0, 100, 79))

-- Actual full controller: both prime searches, all three node counts, all packed stores,
-- three native child pushes, and the three zero-fuel pops. Every packed cell is checked.
/-- info: true -/
#guard_msgs in
#eval decide (observeTree 1 1 0 = some (1, 145, 106, 0, packedSingleton 0))

-- The same complete traversal executes negative signed input and negated-Z placement.
/-- info: true -/
#guard_msgs in
#eval decide (observeTree 1 1 (-1) = some (1, 145, 106, 0, packedSingleton (-1)))

private def branchingInput : Data 128 where
  regs i := if i = slot 2 then 3 else if i = slot 3 then 4 else if i = slot 5 then 5
    else if i = digits then 4 else if i = magnitude then 4
    else if i = stackCapacity then 35 else (treeInput 2 1 0).regs i
  mem a := match a with
    | 1 => Signed.encode 0
    | 2 => Signed.encode 4
    | 3 => Signed.encode 1
    | 4 => Signed.encode 0
    | 5 => Signed.encode (-1)
    | _ => (treeInput 2 1 0).mem a

private def branchingNodes : List Cslib.Algorithms.ThreeSum.ChanHe.Node :=
  let ν₀ : Cslib.Algorithms.ThreeSum.ChanHe.Node := ⟨{0, 4, 1}, {0}, {-1}, 4⟩
  let ν₁ : Cslib.Algorithms.ThreeSum.ChanHe.Node := ⟨{0, 4}, {0}, {-1}, 4⟩
  [ν₀, ν₁]

-- The same two nodes are computed by the existing finite recursion, in the same order.
example : (Math.Task.mk 2 ![{0, 4, 1}, {0}, {-1}]).output {2} 4 = branchingNodes := by
  decide

private def expectedBranching : List (List ℕ) :=
  branchingNodes.map fun ν => (List.range 32).map fun i => Signed.encode (ν.oneArray 4 i)

-- Only the first column has heavy elements. The child changes that descriptor and keeps the
-- other two, then its zero-fuel children and both empty siblings are popped without outputs.
-- The two packed arrays differ, so this also checks their preorder and exact readback.
/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 16 64 oneRoot branchingInput).map (fun (y, _) =>
  (y.regs outputCount, y.regs heap, y.regs (registers Stack.len),
    [y.mem 60, y.mem 61], [108, 156].map fun p => (List.range 32).map fun i => y.mem (p + i))) =
  some (2, 196, 0, [108, 156], expectedBranching))

private theorem treeInput_zero_bounded : (treeInput 0 1 0).Bounded 8 := by
  constructor
  · intro i
    dsimp only [treeInput]
    split <;> decide
  · intro a
    dsimp only [treeInput]
    split
    · decide
    · split
      · decide
      · split <;> decide

-- All premises of the complete-controller theorem are discharged in a concrete native state.
example : ∃ y, Exec 8 oneRoot (treeInput 0 1 0) y 173 ∧
    y.regs outputCount = 0 ∧ y.regs heap = 100 := by
  obtain ⟨y, hy, _, _, hc, hh, _⟩ := oneRoot_zero (capacity := 7) (treeInput 0 1 0)
    treeInput_zero_bounded (by decide) (by decide) (by decide) rfl
  exact ⟨y, hy, hc, hh⟩

/-- info: true -/
#guard_msgs in
#eval decide ((Code.eval 8 16 oneRoot (treeInput 0 1 0)).map Prod.snd = some 173)

private def admittedTree : Data 128 where
  regs i := if i = zero then 0 else if i = one then 1 else (treeInput 1 1 0).regs i
  mem := (treeInput 1 1 0).mem

private def admittedEntry : Entry := ⟨1, ![1, 2, 3], fun _ => [0]⟩

private def admittedArena : Arena where
  n := 1
  m := 2
  Λ := 1
  U := 1
  N := 8
  fuel := 1
  primes := 10
  stack := 20
  capacity := 21
  table := 60
  outputCapacity := 4
  floor := 100
  ceiling := 280
  retained := admittedTree.mem

private theorem admittedTree_bounded : admittedTree.Bounded 66 := by
  constructor
  · intro i
    dsimp only [admittedTree]
    split
    · decide
    · split
      · decide
      · dsimp only [treeInput]
        split <;> decide
  · intro p
    dsimp only [admittedTree, treeInput]
    split
    · decide
    · split
      · decide
      · split <;> decide

-- All premises of the complete live root theorem hold in one concrete native allocation.
-- This includes both searches, real histograms/packing, depth, width and space reservations.
private theorem admittedRoot : RootInput admittedArena 64 admittedEntry [] admittedTree := by
  refine ⟨admittedTree_bounded, by unfold Arena.Controls; decide,
    by unfold Entry.Loaded; decide, by unfold Entry.Stored Block.Realizes; decide,
    ?_, ?_, by unfold Entry.Around; decide,
    by decide, rfl, by decide, by decide, rfl, by decide, storedNodes_nil _ _ _ _,
    fun i => Fin.elim0 i, fun _ _ => rfl⟩
  · refine ⟨by decide, ?_⟩
    refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
      simp [Cslib.Algorithms.ThreeSum.Bdd, admittedEntry]
  · intro q hq
    change q ≤ 2 at hq
    interval_cases q <;> decide

example : ∃ (ns : List (ℕ × Cslib.Algorithms.ThreeSum.ChanHe.Node)) (y : Data 128),
    ExecWithin 66 oneRoot admittedTree y (rootTime 1 1 2 8) ∧
    ns.map Prod.snd = admittedEntry.task.output (Nat.primesLE 2) 1 ∧
    StoredNodes 1 8 60 ns y.mem ∧ y.regs outputCount = ns.length := by
  obtain ⟨ns, y, he, hi, hout, _, _⟩ := root_exec admittedEntry [] admittedTree
    (by unfold Arena.Separated; decide) (by unfold Arena.Ready; decide) admittedRoot
  exact ⟨ns, y, he, by simpa only [List.map_nil, List.nil_append, admittedArena] using hout,
    hi.output, hi.count⟩

-- The common envelope is a real restriction; width 1 cannot admit this live allocation.
example : ¬admittedArena.Ready 1 := by unfold Arena.Ready; decide
