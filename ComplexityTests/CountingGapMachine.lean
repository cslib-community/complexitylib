/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.GapMachine

/-!
Adversarial clients for signed native counting: the actual one-step source, buffered router and
selector have counts `2/1` and `1/2`, not an even multiple of those gaps. Further clients cover
zero cancellation, different witness lengths, dirty selector tapes and first-halt clock padding.
-/

@[expose] public section

namespace ComplexityTests.CountingGapMachine

open Cslib Turing Turing.MultiTapeTM Turing.MultiTapeMachine Turing.MultiTapeCTM

-- A verifier with no guessed bits emits one result and halts in one native instruction.
def answer (bit : Bool) : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [Action.emptyOracleEquiv.symm (VerdictMachine.halt bit)]

theorem answer_nonblocking (bit : Bool) : (answer bit).Nonblocking := by
  intro state symbol work
  simp [answer]

theorem answer_runList (bit : Bool) (input : List Bool) :
    (answer bit).runList 1 (Cfg.init () input) =
      [(VerdictMachine.halt bit).apply (Cfg.init () input)] := by
  rw [runList_succ _ _ 0 () rfl]
  simp [actions, answer]

theorem answer_halts (bit : Bool) (input : List Bool) :
    (answer bit).HaltsWithin 1 (Cfg.init () input) := by
  apply haltsWithin_of_halted _ (answer_nonblocking bit).actions_ne_nil
  intro final hfinal
  rw [answer_runList] at hfinal
  have heq := List.mem_singleton.mp hfinal
  subst final
  rfl

abbrev RoutedState := Unit ⊕ ((MarkWorkState ⊕ RewindWorkState) ⊕ Unit)

noncomputable def routed (sign bit : Bool) : MultiTapeCTM 2 Bool RoutedState :=
  (verdictMachine sign).comp (answer bit) true

theorem routed_nonblocking (sign bit : Bool) : (routed sign bit).Nonblocking :=
  (answer_nonblocking bit).comp (VerdictMachine.nonblocking sign) true

-- One source step, at most five preparation steps, and the actual one-step router.
theorem routed_halts (sign bit : Bool) (input : List Bool) :
    (routed sign bit).HaltsWithin 7 ((routed sign bit).initialConfig input).tapes :=
  HaltsWithin.comp (answer bit) (verdictMachine sign) (answer_nonblocking bit)
    (VerdictMachine.nonblocking sign) true input 1 1 (answer_halts bit input)
    (fun result _ => VerdictMachine.haltsWithin sign result.output)

theorem routed_count (sign bit verdict : Bool) (input : List Bool) :
    (routed sign bit).branchCount (fun out => (out == [true]) == verdict) 7
        ((routed sign bit).initialConfig input).tapes =
      if sign = verdict then 1 else (!bit).toNat := by
  have hbool : ∀ result ∈ (answer bit).runList 1 (Cfg.init (answer bit).initial input),
      ∃ bit, result.output = encBool bit := by
    intro result hresult
    change result ∈ (answer bit).runList 1 (Cfg.init () input) at hresult
    rw [answer_runList] at hresult
    obtain rfl := List.mem_singleton.mp hresult
    exact ⟨bit, rfl⟩
  have h := VerdictMachine.branchCount_comp (answer bit) (answer_nonblocking bit) input 1
    (answer_halts bit input) hbool sign verdict
  have hr : (answer bit).rejectCount 1 (Cfg.init (answer bit).initial input) = (!bit).toNat := by
    rw [rejectCount, (answer_halts bit input).branchCount_eq_countP (fun out => !(out == [true])),
      answer_runList]
    cases bit <;> simp [VerdictMachine.halt, Turing.Action.apply]
  rw [hr] at h
  have hl : ((answer bit).runList 1 (Cfg.init (answer bit).initial input)).length = 1 := by
    change ((answer bit).runList 1 (Cfg.init () input)).length = 1
    rw [answer_runList]
    rfl
  simpa only [routed, hl] using h

-- The two independently buffered components reserve disjoint pairs of work tapes.
noncomputable def combined (positive negative : Bool) :
    MultiTapeCTM 4 Bool (Option (RoutedState ⊕ RoutedState)) :=
  alternative ((routed true positive).extendTapes (Fin.castAddEmb 2))
    ((routed false negative).extendTapes (Fin.natAddEmb 2))

theorem combined_nonblocking (positive negative : Bool) :
    (combined positive negative).Nonblocking :=
  ((routed_nonblocking true positive).extendTapes _).alternative
    ((routed_nonblocking false negative).extendTapes _)

-- Both seven-step clocks are enlarged to fourteen without creating any additional branches.
theorem combined_halts (positive negative : Bool) (input : List Bool) :
    (combined positive negative).HaltsWithin 15
      ((combined positive negative).initialConfig input).tapes := by
  apply HaltsWithin.alternative
    ((routed_nonblocking true positive).extendTapes _)
    ((routed_nonblocking false negative).extendTapes _) 14 input
  · exact (HaltsWithin.extendTapes (routed_nonblocking true positive) _ input 7
      (routed_halts true positive input)).mono (by decide)
  · exact (HaltsWithin.extendTapes (routed_nonblocking false negative) _ input 7
      (routed_halts false negative input)).mono (by decide)

theorem combined_count (positive negative verdict : Bool) (input : List Bool) :
    (combined positive negative).branchCount (fun out => (out == [true]) == verdict) 15
        ((combined positive negative).initialConfig input).tapes =
      (if true = verdict then 1 else (!positive).toNat) +
        (if false = verdict then 1 else (!negative).toNat) := by
  unfold combined
  change (alternative _ _).branchCount _ (14 + 1) (Cfg.init _ input) = _
  rw [branchCount_alternative]
  have he (sign bit : Bool) (e : Fin 2 ↪ Fin 4) :
      branchCount ((routed sign bit).extendTapes e) (fun out => (out == [true]) == verdict) 14
          (Cfg.init ((routed sign bit).extendTapes e).initial input) =
        if sign = verdict then 1 else (!bit).toNat := by
    have h := branchCount_extendTapes (routed sign bit) e input 14
      (fun out => (out == [true]) == verdict)
    rw [(routed_halts sign bit input).branchCount_eq (by decide) _] at h
    exact h.trans (routed_count sign bit verdict input)
  rw [he, he]

-- No witness bits: true/false gives gap +1, with actual counts 2/1.
example (input : List Bool) :
    (combined true false).acceptCount 15 ((combined true false).initialConfig input).tapes = 2 ∧
    (combined true false).rejectCount 15 ((combined true false).initialConfig input).tapes = 1 := by
  constructor
  · simpa [acceptCount] using combined_count true false true input
  · simpa [rejectCount] using combined_count true false false input

-- Swapping success/failure gives gap -1, with counts 1/2.
example (input : List Bool) :
    (combined false true).acceptCount 15 ((combined false true).initialConfig input).tapes = 1 ∧
    (combined false true).rejectCount 15 ((combined false true).initialConfig input).tapes = 2 := by
  constructor
  · simpa [acceptCount] using combined_count false true true input
  · simpa [rejectCount] using combined_count false true false input

-- Colliding false outputs cancel separately: two accepting and two rejecting occurrences.
example (input : List Bool) :
    (combined false false).acceptCount 15
      ((combined false false).initialConfig input).tapes = 2 ∧
    (combined false false).rejectCount 15
      ((combined false false).initialConfig input).tapes = 2 := by
  constructor
  · simpa [acceptCount] using combined_count false false true input
  · simpa [rejectCount] using combined_count false false false input

example (input : List Bool) :
    (combined true false).acceptCount 100
      ((combined true false).initialConfig input).tapes = 2 := by
  rw [acceptCount, (combined_halts true false input).branchCount_eq (by decide)]
  simpa [acceptCount] using combined_count true false true input

-- A control transfer retains dirty scratch, negative work-head positions and a moved real head.
def dirty : Cfg 1 Bool (Option (Unit ⊕ Unit)) [false, true] :=
  { state := some none, inputPos := 3, workTapes := fun _ _ => some false,
    workTapePos := fun _ => -7, output := [true, false] }

example : (Alternative.jump (some (Sum.inl ()))).apply dirty =
    dirty.withState (some (some (Sum.inl ()))) := by
  simp [Alternative.jump, Turing.Action.apply, dirty, Cfg.withState, moveInputPos]

-- The inner `none` is live selector control, not a terminal configuration.
example : ¬dirty.Halted := by decide

-- Full certified generators retain the empty witness on both sign choices.
example (sign : Bool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
      (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
        machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
        machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) = 1 ∧
        machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 1 := by
  simpa only [encBits_apply, Polynomial.eval_zero, Complexity.acceptCount_false, pow_zero,
    Nat.sub_zero, ite_self] using exists_signed_verifier_machine encBits 0 (fun _ => false)
      (.of_tidy (ComputableTidilyInPolyTime.const false)) sign

-- Independently sized 2-bit and 0-bit successful families have odd difference 4 - 1 = 3.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
    (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
      machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
      (machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) : ℤ) -
        machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 3 := by
  simpa only [encBits_apply, Polynomial.eval_C, Polynomial.eval_zero, Complexity.acceptCount_true,
    Nat.reducePow, pow_zero, Nat.cast_ofNat, Nat.cast_one, Int.reduceSub] using
    exists_verifier_difference_machine encBits (Polynomial.C 2) 0 (fun _ => true) (fun _ => true)
      (.of_tidy (ComputableTidilyInPolyTime.const true))
        (.of_tidy (ComputableTidilyInPolyTime.const true))

-- Unequal all-false families still cancel to zero, without matching their witness lengths.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State)
    (clock : Polynomial ℕ), machine.Nonblocking ∧ ∀ input : List Bool,
      machine.HaltsWithin (clock.eval input.length) (Cfg.init machine.initial input) ∧
      (machine.acceptCount (clock.eval input.length) (Cfg.init machine.initial input) : ℤ) -
        machine.rejectCount (clock.eval input.length) (Cfg.init machine.initial input) = 0 := by
  simpa only [encBits_apply, Polynomial.eval_C, Polynomial.eval_zero, Complexity.acceptCount_false,
    Nat.cast_zero, sub_self] using
    exists_verifier_difference_machine encBits 0 (Polynomial.C 2) (fun _ => false) (fun _ => false)
      (.of_tidy (ComputableTidilyInPolyTime.const false))
        (.of_tidy (ComputableTidilyInPolyTime.const false))

/--
info: 'Turing.MultiTapeCTM.exists_signed_verifier_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.exists_signed_verifier_machine
/--
info: 'Turing.MultiTapeCTM.exists_verifier_difference_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeCTM.exists_verifier_difference_machine
/--
info: 'Cslib.Complexity.mem_GapP_iff_exists_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_GapP_iff_exists_machine

end ComplexityTests.CountingGapMachine
