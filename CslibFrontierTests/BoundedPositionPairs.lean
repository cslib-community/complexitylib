/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BoundedPositionPairs

open Turing Turing.MultiTapeTM Cslib.BitString
open Turing.MultiTapeTM.BoundedPositionPairs

/- The second pair exists: the source remains intact and both auxiliary words are erased. -/
example : RunsBetween machine
    (tapesCfg [true] ![[false, true, true, false], [true], []] 0 ![0, 0, 0] [false])
    (tapesCfg [true] ![[false, true, true, false], [], []] 0 ![2, 0, 0] [false, true])
    30 93 := by
  simpa [PositionPairs.config, lsbValue] using
    runsBetween [true] [false, true, true, false] [true] [false] 2 rfl

/- An index exactly at EOF fails, and the cursor stops at EOF. -/
example : RunsBetween machine
    (tapesCfg [] ![[true, false, false, true], [false, true], []] 0 ![0, 0, 0] [true])
    (tapesCfg [] ![[true, false, false, true], [], []] 0 ![4, 0, 0] [true, false])
    46 141 := by
  simpa [PositionPairs.config, lsbValue] using
    runsBetween [] [true, false, false, true] [false, true] [true] 2 rfl

/- No pair exists in the empty source, even for binary zero. -/
example : RunsBetween machine
    (tapesCfg [] ![[], [], []] 0 ![0, 0, 0] [])
    (tapesCfg [] ![[], [], []] 0 ![0, 0, 0] [false]) 14 45 := by
  simpa [PositionPairs.config, lsbValue] using runsBetween [] [] [] [] 0 rfl

/- A padded zero succeeds without moving the source, but cleanup charges its entire width. -/
example : RunsBetween machine
    (tapesCfg [] ![[true, false], [false, false, false], []] 0 ![0, 0, 0] [])
    (tapesCfg [] ![[true, false], [], []] 0 ![0, 0, 0] [true]) 29 90 := by
  simpa [PositionPairs.config, lsbValue] using
    runsBetween [] [true, false] [false, false, false] [] 1 rfl

/- A 129-bit index representing 2^128 is rejected after two pairs. Its value never appears
in the transition bound: all 129 index bits, including the long initial borrow, are charged. -/
example : RunsBetween machine
    (tapesCfg [] ![[false, true, true, false], List.replicate 128 false ++ [true], []]
      0 ![0, 0, 0] [])
    (tapesCfg [] ![[false, true, true, false], [], []] 0 ![4, 0, 0] [false]) 681 2046 := by
  have h := runsBetween [] [false, true, true, false]
    (List.replicate 128 false ++ [true]) [] 2 rfl
  have hv : lsbValue (List.replicate 128 false ++ [true]) = 2 ^ 128 := by
    rw [lsbValue_append, lsbValue_replicate_false]
    simp only [List.length_replicate, lsbValue_singleton, Bool.toNat_true, mul_one, zero_add]
  have hw : (List.replicate 128 false ++ [true]).length = 129 := by simp
  rw [hv, hw] at h
  norm_num only [PositionPairs.config] at h
  exact h

/- Tape words and indices are runtime data for a single finite controller. -/
example : ∃ (S : Type) (_ : Finite S) (tm : MultiTapeTM 3 Bool S),
    ∀ (input source out : List Bool) (q p : ℕ), source.length = 2 * q →
      RunsBetween tm (PositionPairs.config input source p.bits [] 0 out)
        (PositionPairs.config input source [] [] (2 * (min p q : ℕ) : ℤ)
          (out ++ [decide (p < q)]))
        (11 * min p q + 5 * p.bits.length + 14)
        (3 * (11 * min p q + 5 * p.bits.length + 15)) := by
  exact ⟨_, inferInstance, machine, runsBetween_bits⟩
