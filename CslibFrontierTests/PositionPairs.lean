/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PositionPairs

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.PositionPairs Cslib.BitString

/- Empty binary zero leaves the source head in place and preserves the old output. -/
example : machine.runFrom
    ((tapesCfg [true] ![[false, true], [], []] 0 ![0, 0, 0] [true, false]).withState
      (some machine.q₀)) 13 =
    (tapesCfg [true] ![[false, true], [], []] 0 ![0, 0, 0] [true, false]).withState none := by
  simpa only [config, lsbValue, List.length_cons, List.length_nil,
    Bool.toNat_false, Bool.toNat_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.cast_zero, Nat.cast_ofNat, Int.reduceMul] using
    (runsBetween [true] [false, true] [] [true, false]).1

/- A padded zero must erase the complete underflow word without moving the source. -/
example : machine.runFrom
    ((tapesCfg [false] ![[true, false, true], [false, false, false], []]
      0 ![0, 0, 0] [false, true]).withState (some machine.q₀)) 28 =
    (tapesCfg [false] ![[true, false, true], [], []]
      0 ![0, 0, 0] [false, true]).withState none := by
  simpa only [config, lsbValue, List.length_cons, List.length_nil,
    Bool.toNat_false, Bool.toNat_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.cast_zero, Nat.cast_ofNat, Int.reduceMul] using
    (runsBetween [false] [true, false, true] [false, false, false] [false, true]).1

/- Eight crosses a long borrow prefix. Even a shorter source is preserved cell for cell;
the cursor primitive neither interprets nor bounds the source contents. -/
example : machine.runFrom
    ((tapesCfg [true, false] ![[false, true, true, false], [false, false, false, true], []]
      0 ![0, 0, 0] [true]).withState (some machine.q₀)) 121 =
    (tapesCfg [true, false] ![[false, true, true, false], [], []]
      0 ![16, 0, 0] [true]).withState none := by
  simpa only [config, lsbValue, List.length_cons, List.length_nil,
    Bool.toNat_false, Bool.toNat_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.cast_zero, Nat.cast_ofNat, Int.reduceMul] using
    (runsBetween [true, false] [false, true, true, false]
      [false, false, false, true] [true]).1

/- Padding changes the charged cleanup but not the value or cursor displacement. -/
example : RunsBetween machine
    (tapesCfg [] ![[true, false], [true, false, false], []] 0 ![0, 0, 0] [false])
    (tapesCfg [] ![[true, false], [], []] 0 ![2, 0, 0] [false]) 39 120 := by
  simpa only [config, lsbValue, List.length_cons, List.length_nil,
    Bool.toNat_false, Bool.toNat_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Int.reduceMul] using
    runsBetween [] [true, false] [true, false, false] [false]

/- One finite controller handles every binary position; the value is runtime tape data. -/
example : ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM 3 Bool S),
    ∀ (input source out : List Bool) (p : ℕ),
      RunsBetween tm (config input source p.bits [] 0 out)
        (config input source [] [] (2 * (p : ℤ)) out)
        (11 * p + 5 * p.bits.length + 13) (3 * (11 * p + 5 * p.bits.length + 14)) := by
  exact ⟨_, inferInstance, machine, runsBetween_bits⟩
