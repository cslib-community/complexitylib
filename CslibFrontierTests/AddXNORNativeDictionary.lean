/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORNativeRetain
import Mathlib.Tactic.FinCases

/-!
# Native full-state dictionary lifetimes

The symbolic resource client supplies every hypothesis. Kernel executions cover
replacement, absent keys, zero witnesses, reuse, an unread dirty sentinel and a
consecutive original-quarter-to-dictionary pipeline. This is not an all-class
counter-selected dissection certificate.
-/

-- The checked examples and private fixtures export no library API.
set_option linter.privateModule false

public section

open Cslib.WordRAM Cslib.Cryptanalysis.AddXNOR.Native
open Quarter Dictionary

private def entries : List Entry := [⟨6, 0, 0⟩, ⟨6, 1, 2⟩, ⟨1, 3, 0⟩]

private def input : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 3
      else if r = table then 40 else 0
    mem := fun a => if a = 5 ∨ a = 8 then 6 else if a = 9 ∨ a = 11 then 1
      else if a = 10 then 2 else if a = 12 then 3 else if a = 30 then 17 else 0 }

private theorem input_bounded : input.Bounded 8 := by
  constructor
  · intro r
    fin_cases r <;> decide
  · intro a
    simp only [input]
    split_ifs <;> decide

/-- Full instantiation includes the original record cells and unread sentinel.
The release stack, its distinctness and all deletion costs are conclusions. -/
example : ∃ y n ts, n + 1 ≤ 135 ∧ TraceExec 8 cycle input y n ts ∧
    Executes 8 (cycle.program top) ⟨0, input⟩ 0 (n + 1) ∧ y.mem = input.mem ∧
    ∀ k u, Runs 8 (cycle.program top) ⟨0, input⟩ u k → k ≤ n →
      u.data.Bounded 8 ∧ ∃ live : Finset ℕ,
        (∀ a, u.data.mem a ≠ 0 ↔ a ∈ live) ∧
        (live.card + 32) * 8 ≤ 206 * 8 := by
  have h := cycle_resources (D := 40) (b := 5) entries input (Finset.range 40)
    input_bounded ?_ (by decide) (by decide) (by decide) (by decide) (by decide)
    ?_ ?_ (by decide) ?_
  · simpa [entries] using h
  · intro a ha
    simp only [input] at ha
    split_ifs at ha <;> simp only [Finset.mem_range] <;> omega
  · decide
  · intro a ha
    simp [input, show a ≠ 5 by omega, show a ≠ 8 by omega, show a ≠ 9 by omega,
      show a ≠ 11 by omega, show a ≠ 10 by omega, show a ≠ 12 by omega,
      show a ≠ 30 by omega]
  · decide

private def lookupAfterFill : Code .standard 32 :=
  .seq fill (.seq (ram[ state ← #6; one ← #1 ]) get)

/-- State six is replaced, not pushed twice. Its new witnesses are (1,2),
and its predecessor is zero. State one points to state six plus one. -/
example : (lookupAfterFill.eval 8 8 input).map (fun r =>
    (r.1.regs operand, r.1.regs bits, r.1.regs top,
      [r.1.mem 58, r.1.mem 59, r.1.mem 60, r.1.mem 43, r.1.mem 44, r.1.mem 45],
      r.1.mem 30)) = some (2, 2, 2, [2, 2, 0, 4, 0, 7], 17) := by
  decide +kernel

/-- Full-state lookup separates two keys with the same low bit. -/
example : ((.seq fill (.seq (ram[ state ← #4; one ← #1 ]) get) : Code .standard 32).eval
    8 8 input).map (fun r => (r.1.regs operand, r.1.regs bits)) = some (0, 0) := by
  decide +kernel

/-- A class releases all occupied words; a second class uses the same addresses.
Old witness and link cells, including zeros, are restored exactly. -/
example : ((.seq cycle cycle : Code .standard 32).eval 8 8 input).map (fun r =>
    (r.1.regs top, (List.range 80).map r.1.mem)) =
      some (0, (List.range 80).map input.mem) := by decide +kernel

/-- Width overflow faults in the actual native interpreter. -/
example : fill.eval 4 8 input = none := by decide +kernel

/-- The empty class still executes setup, loop exit, release and halt normally. -/
example : (cycle.eval 8 2 (input.set count 0)).map (fun r =>
    (r.1.regs top, r.1.mem 30, r.1.mem 58)) = some (0, 17, 0) := by decide +kernel

private def quarterInput : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 2
      else if r = modulus then 8 else if r = initial then 3
      else if r = keyModulus then 2 else if r = heads then 20
      else if r = frontier then 24 else 0
    mem := fun a => if a = 5 then 1 else if a = 6 then 2
      else if a = 8 then 3 else if a = 9 ∨ a = 10 ∨ a = 11 then 1
      else if 20 ≤ a ∧ a < 22 ∨ 24 ≤ a ∧ a < 36 then 99
      else if a = 100 then 17 else 0 }

private abbrev savedFirst : Fin 32 := 29
private abbrev savedSecond : Fin 32 := 30

private def quarterDictionary : Code .standard 32 :=
  .seq prepare
    (.seq (ram[ base ← #10; modulus ← keyModulus; state ← #0; operators ← #2 ])
      (.seq queryBucket
        (.seq (ram[ base ← #8; modulus ← #8; zero ← #0; one ← #1;
          table ← #1000; top ← #0 ])
          (.seq retainLoop
            (.seq (ram[ state ← #2; one ← #1 ])
              (.seq get (.seq (ram[ savedFirst ← operand; savedSecond ← bits ])
                (.seq release (.seq (ram[ state ← #2; one ← #1 ]) get)))))))))

/-- The input contains original full-width operands, not preinstalled records.
Native preparation, inverse query, full-state recovery, direct dictionary retention, lookup
and release execute consecutively. The match is the packed witness (2,2);
after release the same key is absent and the unread sentinel is preserved.
No intermediate output-record array is allocated. -/
example : (quarterDictionary.eval 11 8 quarterInput).map (fun r =>
    [r.1.regs savedFirst, r.1.regs savedSecond, r.1.regs operand, r.1.regs bits, r.1.regs top,
      r.1.mem 100, r.1.mem 5, r.1.mem 6, r.1.mem 1006, r.1.mem 1007, r.1.mem 1008]) =
      some [3, 2, 0, 0, 0, 17, 1, 2, 0, 0, 0] := by decide +kernel

/-- The fixed programs are deterministic and do not branch on physical width. -/
example : fill.IsRandFree ∧ ¬fill.ReadsWidth ∧ get.IsRandFree ∧ ¬get.ReadsWidth ∧
    release.IsRandFree ∧ ¬release.ReadsWidth ∧ retainLoop.IsRandFree ∧
    ¬retainLoop.ReadsWidth := by decide

private def hitsInput : Data 32 :=
  { regs := fun r => if r = base then 5 else if r = count then 1
      else if r = modulus then 8 else if r = link then 10
      else if r = table then 40 else if r = one then 1 else 0
    mem := fun q => if q = 5 ∨ q = 17 then 1 else if q = 10 then 15
      else if q = 11 then 2 else if q = 16 then 7 else if q = 30 then 17 else 0 }

private theorem hits_bounded : hitsInput.Bounded 8 := by
  constructor
  · intro r
    fin_cases r <;> decide
  · intro q
    simp only [hitsInput]
    split_ifs <;> decide

private theorem hits_linked : Linked hitsInput.mem 20 10 [(2, 0), (7, 1)] := by
  refine .cons (by decide) (by decide) (by decide) (by decide) ?_
  change Linked hitsInput.mem 20 15 [(7, 1)]
  refine .cons (by decide) (by decide) (by decide) (by decide) ?_
  change Linked hitsInput.mem 20 0 []
  exact .nil

/-- Fully instantiated direct-retention lifetime. No output-record array is
supplied, and its physical release stack is derived by the generic theorem. -/
example : ∃ y n ts, n + 1 ≤ 114 ∧ TraceExec 8 retainLifetime hitsInput y n ts ∧
    Executes 8 (retainLifetime.program top) ⟨0, hitsInput⟩ 0 (n + 1) ∧
    y.mem = hitsInput.mem ∧ ∀ k u, Runs 8 (retainLifetime.program top) ⟨0, hitsInput⟩ u k →
      k ≤ n → u.data.Bounded 8 ∧ ∃ live : Finset ℕ,
        (∀ q, u.data.mem q ≠ 0 ↔ q ∈ live) ∧
        (live.card + 32) * 8 ≤ 185 * 8 := by
  have h := retainLifetime_resources (W := 8) (a := 1) (b := 5) (boundary := 20)
    (ptr := 10) (D := 40) (v := 0) [1#3] [(2, 0), (7, 1)] hitsInput (Finset.range 40)
    hits_bounded ?_ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hits_linked (by decide)
    (by decide) (by decide) (by decide) (by decide) ?_ (by decide)
  · simpa using h
  · intro q hq
    simp only [hitsInput] at hq
    split_ifs at hq <;> simp only [Finset.mem_range] <;> omega
  · intro q hq
    simp [hitsInput, show q ≠ 5 by omega, show q ≠ 17 by omega,
      show q ≠ 10 by omega, show q ≠ 11 by omega, show q ≠ 16 by omega,
      show q ≠ 30 by omega]

/-- A recovered full state of zero and a zero second-quarter witness are present
records. Their presence does not depend on either payload being nonzero. -/
example : ((.seq retainLoop (.seq (ram[ state ← #0 ]) get) : Code .standard 32).eval
    8 4 hitsInput).map (fun r => [r.1.regs operand, r.1.regs bits, r.1.regs top]) =
      some [2, 0, 1] := by decide +kernel

/-- A second native lifetime can reuse all the first one's slots. -/
example : ((.seq retainLifetime (.seq (ram[ link ← #10 ]) retainLifetime) :
    Code .standard 32).eval 8 5 hitsInput).map (fun r =>
      (r.1.regs top, (List.range 80).map r.1.mem)) =
        some (0, (List.range 80).map hitsInput.mem) := by decide +kernel
