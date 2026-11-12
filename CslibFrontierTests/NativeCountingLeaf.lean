/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.CountingLeaf.Native

namespace CslibFrontierTests.NativeCountingLeaf

open Turing Turing.MultiTapeTM Cslib.CountingLeaf Cslib.CountingLeaf.Native

private def present : RawInput :=
  ⟨[true], [false, true, true, false], [false, false, true, false],
    [true, false, true], false, [false, false]⟩

private def padding : RawInput :=
  ⟨[true], [true, false, true, false], [false, false, true, false],
    [true, false, true], false, [false, false]⟩

private def constantRunner (answer : Bool) : MultiTapeTM 2 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, fun _ => (none, 0), some answer, none⟩

-- The full physical serializer runs before a concrete one-step leaf; both output bits work.
example (input : List Bool) (answer : Bool) :
    (machine (constantRunner answer)).runFrom
      ((initial 0 input present).withState (some (machine (constantRunner answer)).q₀)) 72 =
      (final 0 input present [answer]).withState none := by
  have hr : (constantRunner answer).runFrom
      ((WorkTapePredicate.config input (encRawInput present)).withState
        (some (constantRunner answer).q₀)) 1 =
      (WorkTapePredicate.config input (encRawInput present) [answer]).withState none := by
    simp [constantRunner, runFrom, step_of_state, Action.apply, WorkTapePredicate.config,
      tapesCfg, Cfg.withState]
    rfl
  have h := runFrom_machine (constantRunner answer) present input answer 1 hr
  have hl : (encRawInput present).length = 33 := by decide
  simpa only [hl] using h

-- Raw high zeroes and the path survive. The framed query is on a separate rewound tape,
-- the marker is blank, and the host head is restored to its left blank.
example (input : List Bool) (answer : Bool) :
    (final 0 input present [answer]).workTapes ((1 : Fin 6).castAdd 2) =
      tapeOfList [false, true, true, false] ∧
    (final 0 input present [answer]).workTapePos ((3 : Fin 6).castAdd 2) = 3 ∧
    (final 0 input present [answer]).workTapes (Fin.natAdd 6 (0 : Fin 2)) =
      tapeOfList (encRawInput present) ∧
    (final 0 input present [answer]).workTapePos (Fin.natAdd 6 (0 : Fin 2)) = 0 ∧
    (final 0 input present [answer]).workTapes (Fin.natAdd 6 (1 : Fin 2)) = tapeOfList [] ∧
    (final 0 input present [answer]).inputPos = 0 := by
  simp only [final, Fin.append_left, Fin.append_right]
  simp [Serialize.fields, present]

private def predicate (p : List Bool × ℕ) : Bool := decide (p.1 = [true])

-- One finite native machine now starts from the six separate unencoded fields and returns the
-- correct counting bit for both a genuine leaf and a padded address. Serialization is charged.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (6 + (k + 2)) Bool S)
    (c d : ℕ), ∀ input : List Bool,
    tm.runFrom ((initial k input present).withState (some tm.q₀))
      (c * (size present + 1) ^ d) = (final k input present [true]).withState none ∧
    tm.runFrom ((initial k input padding).withState (some tm.q₀))
      (c * (size padding + 1) ^ d) = (final k input padding [false]).withState none := by
  have hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst encBits encNat)
      (ComputableInPolyTime.const [true])
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_counting predicate hp
  refine ⟨k, S, hS, tm, c, d, fun input => ⟨?_, ?_⟩⟩
  · have ht : runRaw predicate present = true := by decide
    simpa only [ht] using h present input
  · have hf : runRaw predicate padding = false := by decide
    simpa only [hf] using h padding input

end CslibFrontierTests.NativeCountingLeaf
