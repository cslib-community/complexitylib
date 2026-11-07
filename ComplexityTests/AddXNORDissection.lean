/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Complexity.Cryptanalysis.AddXNORDissection

/-!
# Streaming Add/XNOR class and dissection clients

The concrete cases check both directions, wraparound, empty/zero-width inputs,
colliding witnesses, misses, both storage orientations and emitted-record order.
The generic clients use unrestricted inputs. Resource units are chain calls and
trie nodes, not native runtime or compiled peak storage.
-/

public section

open Cslib.Cryptanalysis.AddXNOR ClassEnumeration Dissection
open Cslib.DataStructure.BinaryTrie

/-- A bucket retains literal duplicates in their original order. -/
example : bucket (bucketIndex (fun n : ℕ => [decide (n % 2 = 0)]) [2, 3, 2, 4]) [true] =
    [2, 2, 4] := by decide

/-- The emitted full states are recovered only for actual low-bit bucket hits. -/
example : (classRecords [1#3] [2#3] 3#3 0#1).map (fun r => (r.first, r.second, r.state)) =
    [([false], [false], 6#3), ([true], [true], 0#3)] := by decide

/-- Backward queries exchange forward/inverse roles and retain original order. -/
example : (backClassRecords [1#3] [2#3] 0#3 0#1).map (fun r => (r.first, r.second, r.state)) =
    [([false], [true], 4#3), ([true], [false], 0#3)] := by decide

/-- A miss scans the quarters without evaluating every full half witness. -/
example : classRecords [0#8] [0#8] 0#8 1#2 = [] ∧
    chainStepCalls [0#8] [0#8] 0#8 1#2 = 4 := by decide

/-- Sixteen indexed witnesses survive complete state collision at width zero. -/
example : (classRecords [0#0, 0#0] [0#0, 0#0] 0#0 0#0).length = 16 ∧
    chainStepCalls [0#0, 0#0] [0#0, 0#0] 0#0 0#0 = 48 := by decide

/-- Streaming consumption can count without retaining output records. -/
example : foldClass (fun n _ => n + 1) [0#0, 0#0] [0#0, 0#0] 0#0 0#0 0 = 16 := by decide

/-- Either dictionary orientation recovers a real solution. -/
example : searchClass true [1#3] [2#3] [3#3] [4#3] 0#3 2#3 1#1 ≠ none ∧
    searchClass false [1#3] [2#3] [3#3] [4#3] 0#3 2#3 1#1 ≠ none := by decide

/-- Actual counter-directed search accepts modular wraparound. -/
example : search 1 [7#3] [1#3] [] [] 1#3 1#3 ≠ none := by decide

/-- Empty sides do not manufacture witnesses for unequal endpoints. -/
example : search 2 ([] : List (BitVec 3)) [] [] [] 0#3 1#3 = none := by decide

/-- Zero-width input retains unrestricted operator choices. -/
example : search 0 [0#0] [0#0] [0#0] [0#0] 0#0 0#0 ≠ none := by decide

/-- Kernel checking covers every one-bit four-operand input and both targets. -/
example : ∀ (a b c d s t : BitVec 1),
    search 1 [a] [b] [c] [d] s t ≠ none ↔
      ∃ bs : Fin 4 → Bool, eval (steps bs ![a, b, c, d]) s = t := by decide

/-- The main decision client has no distinctness, balance or length hypotheses. -/
example {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m)) (s t : BitVec m) :
    search p a b c d s t ≠ none ↔ Solvable ((a ++ b) ++ (c ++ d)) s t :=
  search_correct hp a b c d s t

/-- A returned pair is the actual unrestricted full-chain witness. -/
example {m p : ℕ} (hp : p ≤ m) (a b c d : List (BitVec m))
    (s t : BitVec m) (xs ys : List Bool) (h : search p a b c d s t = some (xs, ys)) :
    xs.length = (a ++ b).length ∧ ys.length = (c ++ d).length ∧
      eval ((xs ++ ys).zip ((a ++ b) ++ (c ++ d))) s = t :=
  search_sound hp a b c d s t xs ys h

/-- With a much smaller backward class, the counter comparison stores it. -/
example : (storedClass false [0#0, 0#0] [0#0, 0#0] [0#0] [] 0#0 0#0 0#0).length = 2 := by decide

/-- The full dictionary is bounded by the actual finite maximum of the minima. -/
example {m p a b c d : ℕ} (hp : p ≤ m)
    (as : Fin a → BitVec m) (bs : Fin b → BitVec m)
    (cs : Fin c → BitVec m) (ds : Fin d → BitVec m) (s t : BitVec m) (g : BitVec p) :
    let fc := WordTable.classCounters
      ((List.ofFn as ++ List.ofFn bs).map (BitVec.setWidth p)) (s.setWidth p)
    let bc := WordTable.backwardCounters
      ((List.ofFn cs ++ List.ofFn ds).map (BitVec.setWidth p)) (t.setWidth p)
    (recordTrie (storedClass (decide (fc.read g ≤ bc.read g))
      (List.ofFn as) (List.ofFn bs) (List.ofFn cs) (List.ofFn ds) s t g)).nodes ≤
        classBalance p (Fin.append as bs) (Fin.append cs ds) s t * (m + 1) :=
  storedClass_nodes_le_balance hp as bs cs ds s t g

/-- Every operator pair is counted exactly once across the low-bit classes. -/
example : (∑ g : BitVec 2, (classRecords [1#3] [2#3] 0#3 g).length) = 4 := by decide

/-- The unconditional chain-call sum includes setup repeated at every class. -/
example : (∑ g : BitVec 1, (chainStepCalls [1#3] [2#3] 0#3 g +
    backChainStepCalls [3#3] [4#3] 2#3 g)) = 24 := by decide

/-- All quarter-cut remainders, including short inputs and oversized projections. -/
example : ∀ n : Fin 8,
    solve 8 (List.replicate n.val 0#3) 0#3 0#3 ≠ none ∧
      solve 8 (List.replicate n.val 0#3) 0#3 1#3 = none := by decide

/-- One-list callers receive a complete unrestricted decision/witness interface. -/
example {m : ℕ} (p : ℕ) (as : List (BitVec m)) (s t : BitVec m) :
    solve p as s t ≠ none ↔ Solvable as s t := solve_correct p as s t
