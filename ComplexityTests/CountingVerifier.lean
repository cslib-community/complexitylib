/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SharpP.Characterization

/-! Native guess-and-verify clients: exact framing, retained input, output collisions, zero-length
witnesses, first-halting clock padding, and instantiated finite/nonblocking machine contracts. -/

namespace ComplexityTests.CountingVerifier

open Cslib Turing MultiTapeCTM MultiTapeMachine

-- Reserved tapes can be dirty and have displaced heads; their contents are not read or cleared.
example : MultiTapeCTM.HaltsWithin (guessMachine.extendTapes (Fin.castAddEmb 1)) 3
    (((guessMachine.initialConfig [true, false]).embed (Fin.castAddEmb 1)
      (fun _ _ => some false) (fun _ => -7)).tapes) :=
  HaltsWithin.embed GuessMachine.nonblocking _ _ _ _ _
    (GuessMachine.haltsWithin [true, false])

-- An already present output is unreadable and introduces no additional choices or steps.
example : (guessMachine.runList 3
    ((guessMachine.initialConfig [true, false]).tapes.prependOutput [false, true])).map Cfg.output =
    [[false, true, false, false], [false, true, false, true],
      [false, true, true, false], [false, true, true, true]] := by
  rw [runList_prependOutput]
  decide

-- Write frame [false] = [true, false, false], without moving the real input head.
private def frameOne : MultiTapeTM 0 Bool (Fin 3) :=
  MultiTapeTM.ofTr 0 fun state _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some (state == 0)
      state := if state == 0 then some 1 else if state == 1 then some 2 else none }

private theorem frameOne_ready : frameOne.runFrom (frameOne.initCfg [false]) 3 =
    wordsCfg [false] none (fun _ => []) [true, false, false] := by
  refine Cfg.ext ?_ ?_ (by funext i; exact Fin.elim0 i)
    (by funext i; exact Fin.elim0 i) ?_ <;>
    simp [MultiTapeTM.runFrom, MultiTapeTM.step_of_state, frameOne, Action.apply,
      wordsCfg, Cfg.init]

private noncomputable def framed := (ofDeterministic frameOne).seq guessMachine

private theorem framed_nonblocking : Nonblocking framed :=
  (nonblocking_ofDeterministic frameOne).seq GuessMachine.nonblocking

private theorem framed_halts : MultiTapeCTM.HaltsWithin framed 5
    (framed.initialConfig [false]).tapes :=
  haltsWithin_seq_prependOutput frameOne guessMachine GuessMachine.nonblocking
    [false] [true, false, false] 3 2 frameOne_ready (GuessMachine.haltsWithin [false])

-- The scanner sees the original one-symbol input, so it guesses one bit, not four bits.
example : (runList framed 5 (framed.initialConfig [false]).tapes).map Cfg.output =
    [[true, false, false, false], [true, false, false, true]] := by
  unfold framed
  rw [runList_seq_prependOutput frameOne guessMachine GuessMachine.nonblocking
    [false] [true, false, false] 3 2 frameOne_ready (GuessMachine.haltsWithin [false])]
  decide

-- An actual consumer scans to the right boundary and emits the last symbol it read.
-- The two framed words differ only in the witness bit; this detects reversal or wrong buffering.
private def readLast : MultiTapeTM 0 Bool Bool :=
  MultiTapeTM.ofTr false fun state symbol _ =>
    { inputTape := if symbol.isSome then 1 else 0, workTapes := Fin.elim0
      output := if symbol.isSome then none else some state, state := symbol }

private theorem readLast_halts : ∀ result ∈ runList framed 5 (framed.initialConfig [false]).tapes,
    (ofDeterministic readLast).HaltsWithin 5
      ((ofDeterministic readLast).initialConfig result.output).tapes := by
  intro result hresult
  rw [haltsWithin_ofDeterministic_iff]
  unfold framed at hresult
  rw [runList_seq_prependOutput frameOne guessMachine GuessMachine.nonblocking
    [false] [true, false, false] 3 2 frameOne_ready (GuessMachine.haltsWithin [false])] at hresult
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hresult
  have hout : original.output = [false] ∨ original.output = [true] := by
    have hm := (List.mem_map (f := Cfg.output)).mpr ⟨original, horiginal, rfl⟩
    change original.output ∈ [[false], [true]] at hm
    simpa using hm
  rcases hout with hout | hout <;>
    change (readLast.runFrom
      (readLast.initCfg ([true, false, false] ++ original.output)) 5).Halted <;>
    rw [hout] <;>
    simp [MultiTapeTM.runFrom, MultiTapeTM.step_of_state, readLast, Action.apply,
      Cfg.Halted, Cfg.inputSymbol, moveInputPos]

private noncomputable def compiled := (ofDeterministic readLast).comp framed true

example : compiled.Nonblocking :=
  framed_nonblocking.comp (nonblocking_ofDeterministic readLast) true

private theorem compiled_halts : compiled.HaltsWithin 19 (compiled.initialConfig [false]).tapes :=
  HaltsWithin.comp framed (ofDeterministic readLast) framed_nonblocking
    (nonblocking_ofDeterministic readLast) true [false] 5 5 framed_halts readLast_halts

example : (compiled.runList 19 (compiled.initialConfig [false]).tapes).map Cfg.output =
    [[false], [true]] := by
  unfold compiled
  rw [runList_comp framed (ofDeterministic readLast) framed_nonblocking
    (nonblocking_ofDeterministic readLast) true [false] 5 5 framed_halts readLast_halts]
  simp only [framed, ofDeterministic, frameOne, readLast, MultiTapeTM.tr_ofTr]
  decide

example : compiled.acceptCount 19 (compiled.initialConfig [false]).tapes = 1 := by
  unfold acceptCount compiled
  rw [branchCount_comp framed (ofDeterministic readLast) framed_nonblocking
    (nonblocking_ofDeterministic readLast) true [false] 5 5 framed_halts readLast_halts]
  simp only [framed, ofDeterministic, frameOne, readLast, MultiTapeTM.tr_ofTr]
  decide

example : compiled.rejectCount 19 (compiled.initialConfig [false]).tapes = 1 := by
  unfold rejectCount compiled
  rw [branchCount_comp framed (ofDeterministic readLast) framed_nonblocking
    (nonblocking_ofDeterministic readLast) true [false] 5 5 framed_halts readLast_halts]
  simp only [framed, ofDeterministic, frameOne, readLast, MultiTapeTM.tr_ofTr]
  decide

-- Waiting after the first halt introduces no new accepting or rejecting branches.
example (padding : ℕ) : compiled.acceptCount (19 + padding)
    (compiled.initialConfig [false]).tapes = compiled.acceptCount 19
      (compiled.initialConfig [false]).tapes :=
  compiled_halts.branchCount_eq (by lia) _

-- The full construction is inhabited with no witness bits: one accepting branch, zero rejecting.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
    (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
      machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
      machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) = 1 ∧
      machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 0 := by
  simpa only [MultiTapeTM.encBits_apply, Polynomial.eval_zero, Complexity.acceptCount_true,
    pow_zero, Nat.sub_self] using
    exists_verifier_counting_machine MultiTapeTM.encBits 0 (fun _ => true)
    (.of_tidy (MultiTapeTM.ComputableTidilyInPolyTime.const true))

-- Four distinct witnesses may have the identical Boolean output; all four occurrences count.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
    (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
      machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
      machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) = 4 ∧
      machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 0 := by
  simpa only [MultiTapeTM.encBits_apply, Polynomial.eval_C, Complexity.acceptCount_true,
    Nat.reducePow, Nat.sub_self] using
    exists_verifier_counting_machine MultiTapeTM.encBits (Polynomial.C 2) (fun _ => true)
    (.of_tidy (MultiTapeTM.ComputableTidilyInPolyTime.const true))

-- The all-rejecting empty witness is still a terminal branch, and supplies the zero #P function.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
    (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
      machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
      machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) = 0 ∧
      machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 1 := by
  simpa only [MultiTapeTM.encBits_apply, Polynomial.eval_zero, Complexity.acceptCount_false,
    pow_zero, Nat.sub_zero] using
    exists_verifier_counting_machine MultiTapeTM.encBits 0 (fun _ => false)
    (.of_tidy (MultiTapeTM.ComputableTidilyInPolyTime.const false))

/--
info: 'Turing.MultiTapeCTM.exists_verifier_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.exists_verifier_machine
/--
info: 'Turing.MultiTapeCTM.exists_verifier_counting_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.exists_verifier_counting_machine
/--
info: 'Cslib.Complexity.mem_SharpP_iff_exists_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_SharpP_iff_exists_machine

end ComplexityTests.CountingVerifier
