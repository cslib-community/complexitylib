/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelZeroSpace
import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw

namespace CslibFrontierTests.WorkTapePredicate

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.WorkTapePredicate

-- Both singleton results execute the virtual-input adapter and restore the host input head.
example (outer : List Bool) (answer : Bool) :
    (machine (tidyCopy Bool)).runFrom
      ((config outer [answer]).withState (some (machine (tidyCopy Bool)).q₀)) 12 =
      (config outer [answer] [answer]).withState none := by
  simpa using (runsBetween (computesTidily_tidyCopy [answer]) outer []).1

-- The marker tape is actually cleared and reset, while the serialized query survives.
example (outer out : List Bool) :
    let tm := machine (tidyCopy Bool)
    let result := tm.runFrom ((config outer [true] out).withState (some tm.q₀)) 12
    result.inputPos = 0 ∧ result.workTapes 0 = tapeOfList [true] ∧
      result.workTapes 1 = tapeOfList [] ∧ result.workTapePos = 0 ∧
      result.output = out ++ [true] := by
  dsimp only
  have hr := (runsBetween (computesTidily_tidyCopy [true]) outer out).1
  norm_num only [List.length_cons, List.length_nil] at hr
  rw [hr]
  simp [config, tapesCfg, Cfg.withState]

-- An empty virtual input also runs the complete ten-transition setup/cleanup protocol.
example (outer : List Bool) :
    (machine (tidyCopy Bool)).runFrom
      ((config outer []).withState (some (machine (tidyCopy Bool)).q₀)) 10 =
      (config outer []).withState none := by
  simpa using (runsBetween (computesTidily_tidyCopy ([] : List Bool)) outer []).1

-- Alternation duplicates actual deterministic transitions; a false returned bit is rejected.
example (outer : List Bool) (answer : Bool) :
    (MultiTapeATM.ofTMs (fun _ => machine (tidyCopy Bool)) (fun _ => false)).AcceptsWithin 12
      ((config outer [answer]).withState (some (machine (tidyCopy Bool)).q₀)) ↔ answer = true := by
  simpa using acceptsWithin (computesTidily_tidyCopy [answer]) outer

private def present : Cslib.CountingLeaf.RawInput :=
  ⟨[true], [false, true, true, false], [false, false, true, false],
    [true, false, true], false, [false, false]⟩

private def padding : Cslib.CountingLeaf.RawInput :=
  ⟨[true], [true, false, true, false], [false, false, true, false],
    [true, false, true], false, [false, false]⟩

private def predicate (p : List Bool × ℕ) : Bool := decide (p.1 = [true])

-- One extracted native predicate runner distinguishes a genuine counting leaf from padding.
-- Its input is the fully serialized query, not a free semantic lookup at the leaf.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (atm : MultiTapeATM (k + 2) Bool S)
    (c d : ℕ), ∀ outer : List Bool,
    atm.AcceptsWithin (c * ((Cslib.CountingLeaf.encRawInput present).length + 1) ^ d)
      ((config outer (Cslib.CountingLeaf.encRawInput present)).withState
        (some atm.toPTM.toNTM.q₀)) ∧
    ¬atm.AcceptsWithin (c * ((Cslib.CountingLeaf.encRawInput padding).length + 1) ^ d)
      ((config outer (Cslib.CountingLeaf.encRawInput padding)).withState
        (some atm.toPTM.toNTM.q₀)) := by
  have hn : ComputableInPolyTime predicate (encPair encBits encNat) encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encBits encNat)
      (ComputableInPolyTime.const [true])
  have hp := Cslib.CountingLeaf.computableInPolyTime_runRaw predicate hn
  obtain ⟨k, S, hS, atm, c, d, h⟩ := exists_alternating_of_polyTime hp
  refine ⟨k, S, hS, atm, c, d, fun outer => ⟨?_, ?_⟩⟩
  · exact ((h present outer).1).mpr (by decide)
  · intro ha
    have hf := ((h padding outer).1).mp ha
    have hn : Cslib.CountingLeaf.runRaw predicate padding = false := by decide
    simp [hn] at hf

end CslibFrontierTests.WorkTapePredicate
