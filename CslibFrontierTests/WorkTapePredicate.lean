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

private theorem copy_run (word : List Bool) :
    RunsBetween (tidyCopy Bool) (tapesCfg word (fun _ => []) 0 0 [])
      (tapesCfg word (fun _ => []) 0 0 word) (2 * word.length + 4) 0 := by
  simpa only [RunsBetween, tapesCfg_zero_withState] using
    computesTidily_iff_runFrom.mp (computesTidily_tidyCopy word)

-- Both singleton results execute the virtual-input adapter and restore the host input head.
example (outer : List Bool) (answer : Bool) :
    (machine (tidyCopy Bool)).runFrom
      ((config outer [answer]).withState (some (machine (tidyCopy Bool)).q₀)) 12 =
      (config outer [answer] [answer]).withState none := by
  simpa using (runsBetween (copy_run [answer]) outer []).1

-- The marker tape is actually cleared and reset, while the serialized query survives.
example (outer out : List Bool) :
    let tm := machine (tidyCopy Bool)
    let result := tm.runFrom ((config outer [true] out).withState (some tm.q₀)) 12
    result.inputPos = 0 ∧ result.workTapes 0 = tapeOfList [true] ∧
      result.workTapes 1 = tapeOfList [] ∧ result.workTapePos = 0 ∧
      result.output = out ++ [true] := by
  dsimp only
  have hr := (runsBetween (copy_run [true]) outer out).1
  norm_num only [List.length_cons, List.length_nil] at hr
  rw [hr]
  simp [config, tapesCfg, Cfg.withState]

-- An empty virtual input also runs the complete ten-transition setup/cleanup protocol.
example (outer : List Bool) :
    (machine (tidyCopy Bool)).runFrom
      ((config outer []).withState (some (machine (tidyCopy Bool)).q₀)) 10 =
      (config outer []).withState none := by
  simpa using (runsBetween (copy_run []) outer []).1

-- Alternation duplicates actual deterministic transitions; a false returned bit is rejected.
example (outer : List Bool) (answer : Bool) :
    (MultiTapeATM.ofTMs (fun _ => machine (tidyCopy Bool)) (fun _ => false)).AcceptsWithin 12
      ((config outer [answer]).withState (some (machine (tidyCopy Bool)).q₀)) ↔ answer = true := by
  simpa using acceptsWithin (copy_run [answer]) outer

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

private theorem boolIdentity_inO :
    ComputableInO (fun b : Bool => b) encBool encBool (fun _ => 0) (fun _ => 0) := by
  refine ⟨6, ⟨0, _, inferInstance, tidyCopy Bool, ?_⟩, ?_⟩
  · intro b
    have h := (computesTidily_tidyCopy [b]).mono (show 2 * [b].length + 4 ≤ 6 by simp)
      (show 0 ≤ 6 by decide)
    simpa only [encBool_apply, Nat.zero_add, Nat.mul_one] using h.computesInTimeAndSpace
  · intro b
    simp

-- A nonconstant predicate with zero nominal budgets still gets a positive common native clock.
-- The same finite runner returns both answers and restores its query, scratch, marker and heads.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (runner : MultiTapeTM (k + 2) Bool S) (c : ℕ), ∀ outer : List Bool,
      let yes := runner.runFrom ((config outer [true]).withState (some runner.q₀)) c
      let no := runner.runFrom ((config outer [false]).withState (some runner.q₀)) c
      yes.output = [true] ∧ no.output = [false] ∧ yes.state = none ∧ no.state = none ∧
        yes.inputPos = 0 ∧ no.inputPos = 0 ∧ yes.workTapePos = 0 ∧ no.workTapePos = 0 ∧
        yes.workTapes (Fin.natAdd k 0) = tapeOfList [true] ∧
        no.workTapes (Fin.natAdd k 0) = tapeOfList [false] ∧
        yes.workTapes (Fin.natAdd k 1) = tapeOfList [] ∧
        no.workTapes (Fin.natAdd k 1) = tapeOfList [] ∧
        (∀ i : Fin k, yes.workTapes (i.castAdd 2) = tapeOfList []) ∧
        (∀ i : Fin k, no.workTapes (i.castAdd 2) = tapeOfList []) := by
  obtain ⟨k, S, hS, runner, c, h⟩ := exists_of_inO boolIdentity_inO
  refine ⟨k, S, hS, runner, c, ?_⟩
  intro outer
  have hy := h true outer
  have hn := h false outer
  simp only [Nat.zero_add, Nat.mul_one, encBool_apply] at hy hn
  dsimp only
  rw [hy, hn]
  simp [config, tapesCfg, Cfg.withState, Fin.castAdd_ne_natAdd]

end CslibFrontierTests.WorkTapePredicate
