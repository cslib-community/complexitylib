/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import all Complexity.Cryptanalysis.AddXNORNativeClassSearch
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics
import all Complexity.Cryptanalysis.AddXNORNativeClassRetain
import all Complexity.Cryptanalysis.AddXNORNativeClassProbe
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeDictionary
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import Mathlib.Tactic.IntervalCases

/-! # Complete original-input full-class decision and termination clients -/

set_option linter.privateModule false

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR
open Cslib.Cryptanalysis.AddXNOR.Native
open Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private def first : List (BitVec 3) := [1#3, 2#3, 4#3]
private def middle : List (BitVec 3) := [1#3]

private def input : Data 32 :=
  { regs := fun _ => 99
    mem := fun a => if a = 5 then 1 else if a = 6 then 2 else if a = 7 then 4
      else if a = 8 then 1 else if a = 10 then 1 else if a = 12 then 1
      else if a < 64 then 17 else 0 }

private def budget (t : BitVec 3) (g : BitVec 2) : ℕ :=
  let fs := fun k : BitVec 2 => Forward.records first 1#3 2 k.toNat
  let rs := inverseRecords middle t 2
  ((10 * 1 + 8) + (10 * 1 + 8)) +
    ((7 + (4 * 4 + 8 * (11 * 3 + 22) + 10) +
      (7 + (4 * 4 + 2 * (18 * 1 + 37) + 10))) +
      (8 + ((5 + classRetainTime middle g fs 0 2) +
        (8 + (2 + (4 + classProbeTime middle g rs 0 2))))))

/-- Every raw premise is supplied for arbitrary targets and classes at these
nontrivial widths. Both middle-quarter words are native loop counters. -/
private theorem checked (t : BitVec 3) (g : BitVec 2) :
    ∃ y, ExecWithin 12
      (searchClass 5 3 8 1 10 1 12 1 16 17 8 4 1 t.toNat g.toNat 20 24 52 56 64)
      input y (budget t g) ∧
      (y.regs operand ≠ 0 ↔ PackedClassSolution first middle middle middle 1#3 t g) ∧
      (y.regs operand = 0 ↔ ¬PackedClassSolution first middle middle middle 1#3 t g) ∧
      (y.regs operand ≠ 0 →
        eval (((decode 3 (y.regs operand - 1)).zip first) ++
          ((decode 1 (y.regs bits)).zip middle) ++
          ((decode 1 (y.regs operators)).zip middle) ++
          ((decode 1 (y.regs firstOperators)).zip middle)) 1#3 = t) ∧
      (y.regs operand ≠ 0 → y.regs operand - 1 < 8 ∧ y.regs bits < 2 ∧
        y.regs operators < 2 ∧ y.regs firstOperators < 2) ∧
      ∃ keys, Dictionary.Valid y.mem 64 (y.regs Dictionary.top) keys ∧
        keys.length ≤ (classEntries middle g
          (fun k : BitVec 2 => Forward.records first 1#3 2 k.toNat) 0 2).length := by
  obtain ⟨y, he, hh, hm, hw, hb, keys, hk, hl, _⟩ := searchClass_exec
    (W := 12) (b := 5) (c := 8) (b₃ := 10) (b₄ := 12) (q₂ := 16) (q₃ := 17)
    (h := 20) (f := 24) (h₄ := 52) (f₄ := 56) (D := 64) (by decide)
    first middle middle middle 1#3 t g input
    (by intro i hi; simp only [first, List.length_cons, List.length_nil] at hi
        interval_cases i <;> decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by intro i hi; have : i = 0 := by change i < 1 at hi; omega
        subst i; decide +revert)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro a ha; simp [input, show ¬a = 5 by omega, show ¬a = 6 by omega,
      show ¬a = 7 by omega, show ¬a = 8 by omega, show ¬a = 10 by omega,
      show ¬a = 12 by omega, show ¬a < 64 by omega]) (by decide)
  exact ⟨y, he, hh, hm, hw, hb, keys, hk, hl⟩

/-- A real class hit has an indexed solution with non-self-inverse additions.
This uses the general completeness theorem, not an assumed hit or native run. -/
example : ∃ y, ExecWithin 12
      (searchClass 5 3 8 1 10 1 12 1 16 17 8 4 1 2 0 20 24 52 56 64) input y (budget 2#3 0#2) ∧
    y.regs operand ≠ 0 := by
  obtain ⟨y, he, hit, _⟩ := checked 2#3 0#2
  refine ⟨y, he, hit.mpr ?_⟩
  refine ⟨4, by decide, 0, by decide, 0, by decide, 0, by decide, ?_, ?_⟩ <;> decide +kernel

/-- This selected class is empty of solutions even though other classes may hit.
The native loop terminates with a zero tag; there is no supplied exhaustion premise. -/
example : ∃ y, ExecWithin 12
      (searchClass 5 3 8 1 10 1 12 1 16 17 8 4 1 2 1 20 24 52 56 64) input y (budget 2#3 1#2) ∧
    y.regs operand = 0 := by
  obtain ⟨y, he, _, miss, _⟩ := checked 2#3 1#2
  refine ⟨y, he, miss.mpr ?_⟩
  rintro ⟨u, hu, v, hv, w, hw, z, hz, hc, hs⟩
  change u < 8 at hu
  change v < 2 at hv
  change w < 2 at hw
  change z < 2 at hz
  interval_cases u <;> interval_cases v <;> interval_cases w <;> interval_cases z <;>
    (revert hc hs; decide +kernel)

/-- Retaining all middle words preserves indexed collisions but replaces a
full state's payload coherently; four class entries occupy one width-zero key. -/
example :
    let es := classEntries [0#0] 0#0
      (fun k : BitVec 0 => Forward.records [0#0] 0#0 0 k.toNat) 0 2
    es.length = 4 ∧ Dictionary.filledMemory 24 es (fun _ => 0) 0 24 = 1 ∧
      Dictionary.filledMemory 24 es (fun _ => 0) 0 25 = 1 := by
  simp only [classEntries, retainQuery, retainedEntries, Forward.records, bucketIndices,
    indexedState, List.length_cons, List.length_nil, Nat.reducePow, Nat.reduceAdd]
  decide +kernel

private def emptyInput : Data 32 :=
  { regs := fun _ => 17, mem := fun a => if a < 24 then 17 else 0 }

/-- Entire native projection, both preparations, both full class loops and early
exit at width zero. Empty quarters still have one admissible packed word. -/
example : ((searchClass 0 0 0 0 0 0 0 0 2 3 1 1 0 0 0 4 8 12 16 24).eval 8 8 emptyInput).map
    (fun r => (r.1.regs operand, r.1.regs bits, r.1.regs operators,
      r.1.regs firstOperators, r.1.regs stop)) = some (1, 0, 0, 0, 0) := by
  decide +kernel

/-- An empty selected class exhausts the computed packed-word bound. -/
example : ((searchClass 0 0 0 0 0 0 0 0 2 3 2 2 0 0 1 4 8 12 16 24).eval 8 8 emptyInput).map
    (fun r => (r.1.regs operand, r.1.regs operators, r.1.regs stop)) = some (0, 1, 1) := by
  decide +kernel

/-- The indexed completeness predicate is the existing dissection meeting notion. -/
example (t : BitVec 3) (g : BitVec 2) : ∃ y, ExecWithin 12
      (searchClass 5 3 8 1 10 1 12 1 16 17 8 4 1 t.toNat g.toNat 20 24 52 56 64)
      input y (budget t g) ∧
    (y.regs operand ≠ 0 ↔ Dissection.Meets first middle middle middle 1#3 t g) := by
  obtain ⟨y, he, hit, _⟩ := checked t g
  exact ⟨y, he, hit.trans (packedClassSolution_iff_meets (by decide) _ _ _ _ _ _ _)⟩
