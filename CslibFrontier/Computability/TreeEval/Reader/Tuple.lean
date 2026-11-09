/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Reader.Encode

/-!
# The Tree Evaluation read machine on tuples

The halting test, the address and the step of `Cslib.TreeEval.Reader.machine`, written on the
tuples of `Cslib.TreeEval.Reader.State.toTuple` as chains of tests on finite tags. In this form
they are built from basic functions, which is how their work space is bounded.

## Main definitions

* `Cslib.TreeEval.Reader.haltT`, `Cslib.TreeEval.Reader.addrT`, `Cslib.TreeEval.Reader.stepT`.

## Main results

* `Cslib.TreeEval.Reader.haltT_toTuple`, `Cslib.TreeEval.Reader.addrT_toTuple`,
  `Cslib.TreeEval.Reader.stepT_toTuple`: they agree with the machine.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Iter

namespace Tuple

variable (x : Tuple)

/-- The value length. -/
abbrev ell : ℕ := x.1.1.1
/-- The height. -/
abbrev height : ℕ := x.1.1.2.1
/-- The prime. -/
abbrev p : ℕ := x.1.1.2.2
/-- The registers. -/
abbrev regs : Regs := x.1.2
/-- The stack. -/
abbrev stack : List Frame := x.2.1.1
/-- The mode. -/
abbrev mode : Mode := x.2.1.2
/-- The tag of the control state. -/
abbrev tag : Fin 7 := x.2.2.1
/-- The first number of the control state. -/
abbrev n₁ : ℕ := x.2.2.2.1
/-- The second number of the control state. -/
abbrev n₂ : ℕ := x.2.2.2.2.1
/-- The list of the control state. -/
abbrev acc : List ℕ := x.2.2.2.2.2

/-- A tuple with a new control state. -/
abbrev withCtl (c : Fin 7 × ℕ × ℕ × List ℕ) : Tuple := (x.1, x.2.1, c)

end Tuple

/-- The control tuple of `run`. -/
abbrev runCtl : Fin 7 × ℕ × ℕ × List ℕ := (3, 0, 0, [])

/-- The offset in the encoding of the node at the path of a stack. -/
def offsetT (x : Tuple) (st : List Frame) : ℕ :=
  x.ell + x.height + 2 + pathOffset x.ell x.height (path st)

/-- The halting test on tuples. -/
def haltT (x : Tuple) : Bool := decide (x.tag = 6)

/-- The address on tuples. -/
def addrT (x : Tuple) : Option ℕ :=
  if x.tag = 0 then some x.n₁
  else if x.tag = 1 then some (x.ell + 1 + x.n₁)
  else if x.tag = 4 then some (offsetT x x.stack + x.n₁)
  else if x.tag = 5 then some (offsetT x x.stack.tail + x.n₁)
  else none

/-- Whether a mode is a call. -/
def _root_.Cslib.TreeEval.Iter.Mode.isCall : Mode → Bool
  | .call _ _ => true
  | .ret => false

/-- The sign of a call. -/
def _root_.Cslib.TreeEval.Iter.Mode.neg : Mode → Bool
  | .call neg _ => neg
  | .ret => false

/-- The target of a call. -/
def _root_.Cslib.TreeEval.Iter.Mode.target : Mode → Fin 3
  | .call _ t => t
  | .ret => 0

/-- The default frame, standing for the top of an empty stack. -/
abbrev dfr : Frame := ⟨0, 0, false, 0⟩

/-- The tuple with new registers, stack, mode and control state. -/
abbrev Tuple.with (x : Tuple) (R : Regs) (st : List Frame) (m : Mode)
    (c : Fin 7 × ℕ × ℕ × List ℕ) : Tuple :=
  (((x.ell, x.height, x.p), R), (st, m), c)

/-- The steps of the iterative procedure on tuples. -/
def runStepT (x : Tuple) : Tuple × List Bool :=
  let fr := x.stack.headD dfr
  let st := x.stack.tail
  let t := x.mode.target
  if x.mode.isCall then
    if x.stack.length = x.height then (x.withCtl (4, 0, 0, []), [])
    else (x.with (x.regs.scale x.p (t + 1) (unitVal 0)) (⟨0, 0, x.mode.neg, t⟩ :: x.stack)
      (.call false (t + 1)) runCtl, [])
  else if x.stack.isEmpty then (x.withCtl (6, 0, 0, []), (x.regs.get 2).map (· == 1))
  else if fr.phase = 0 then
    (x.with (x.regs.scale x.p (fr.target + 2) (unitVal fr.round)) ({ fr with phase := 1 } :: st)
      (.call false (fr.target + 2)) runCtl, [])
  else if fr.phase = 1 then (x.withCtl (5, 0, 0, List.replicate x.ell 0), [])
  else if fr.phase = 2 then
    (x.with (x.regs.scale x.p (fr.target + 1) (unitInv x.p fr.round)) ({ fr with phase := 3 } :: st)
      (.call true (fr.target + 2)) runCtl, [])
  else if fr.round + 1 < x.p - 1 then
    (x.with ((x.regs.scale x.p (fr.target + 2) (unitInv x.p fr.round)).scale x.p (fr.target + 1)
      (unitVal (fr.round + 1))) (⟨fr.round + 1, 0, fr.neg, fr.target⟩ :: st)
      (.call false (fr.target + 1)) runCtl, [])
  else (x.with (x.regs.scale x.p (fr.target + 2) (unitInv x.p fr.round)) st .ret runCtl, [])

/-- The step on tuples, given the bit read. -/
def stepT (y : Tuple × Bool) : Tuple × List Bool :=
  let x := y.1
  let b := y.2
  let fr := x.stack.headD dfr
  if x.tag = 0 then
    if b then (x.withCtl (0, x.n₁ + 1, 0, []), [])
    else ((((x.n₁, x.height, x.p), x.regs), x.2.1, (1, 0, 0, [])), [])
  else if x.tag = 1 then
    if b then (x.withCtl (1, x.n₁ + 1, 0, []), [])
    else ((((x.ell, x.n₁, x.p), x.regs), x.2.1, (2, 2 * x.ell + 2, 2, [])), [])
  else if x.tag = 2 then
    if x.n₂ < x.n₁ then
      if x.n₁ % x.n₂ = 0 then (x.withCtl (2, x.n₁ + 1, 2, []), [])
      else (x.withCtl (2, x.n₁, x.n₂ + 1, []), [])
    else ((((x.ell, x.height, x.n₁),
      (List.replicate x.ell 0, List.replicate x.ell 0, List.replicate x.ell 0)),
      ([], .call false 2), runCtl), [])
  else if x.tag = 3 then runStepT x
  else if x.tag = 4 then
    if x.mode.isCall then
      if x.n₁ < x.ell then
        (x.with (x.regs.set x.mode.target (modifyAt (x.regs.get x.mode.target) x.n₁
          (addMod x.p (if b then sgnVal x.p x.mode.neg else 0)))) x.stack x.mode
          (4, x.n₁ + 1, 0, []), [])
      else (x.with x.regs x.stack .ret runCtl, [])
    else (x, [])
  else if x.tag = 5 then
    if x.stack.isEmpty then (x, [])
    else if x.n₁ < tableLength x.ell then
      if b then
        (x.withCtl (5, x.n₁ + 1, 0, modifyAt x.acc (x.n₁ % x.ell) (addMod x.p
          (weight x.p x.ell (x.n₁ / x.ell) (x.regs.get (fr.target + 1))
            (x.regs.get (fr.target + 2))))), [])
      else (x.withCtl (5, x.n₁ + 1, 0, x.acc), [])
    else (x.with (subtractSums x.p (sgnVal x.p fr.neg) fr.target x.acc x.regs)
      ({ fr with phase := 2 } :: x.stack.tail) (.call true (fr.target + 1)) runCtl, [])
  else (x, [])

/-- On the tuple of a state, `haltT` is the halting test of `machine`. -/
theorem haltT_toTuple (s : State) : haltT s.toTuple = machine.halt s := by
  obtain ⟨_, _, _, _, _, _, c⟩ := s
  cases c <;> rfl

/-- On the tuple of a state, `addrT` is the address `addr` of the state. -/
theorem addrT_toTuple (s : State) : addrT s.toTuple = addr s := by
  obtain ⟨_, _, _, _, _, _, c⟩ := s
  cases c <;> rfl

/-- On the tuple of a state, `stepT` is the step of `machine`: it gives the tuple of the next
state and the same output. -/
theorem stepT_toTuple (s : State) (b : Bool) :
    stepT (s.toTuple, b) = ((machine.step s b).1.toTuple, (machine.step s b).2) := by
  obtain ⟨e, h, p, R, st, m, c⟩ := s
  cases c with
  | hdrLength n => cases b <;> rfl
  | hdrHeight n => cases b <;> rfl
  | prime q d =>
    by_cases h₁ : d < q <;> by_cases h₂ : q % d = 0 <;>
      simp [Tuple.tag, Tuple.n₁, Tuple.n₂, Tuple.ell, Tuple.height, Tuple.withCtl, stepT, machine,
        step, State.toTuple, Ctl.toTuple, h₁, h₂]
  | run =>
    rcases m with ⟨neg, t⟩ | _
    · by_cases h₁ : st.length = h <;>
        simp [Tuple.tag, Tuple.height, Tuple.p, Tuple.regs, Tuple.stack, Tuple.mode,
          Tuple.withCtl, Mode.isCall, Mode.target, Mode.neg, stepT, runStepT, machine, step,
          runStep, State.toTuple, Ctl.toTuple, h₁]
    · rcases st with _ | ⟨⟨j, ph, ng, tg⟩, st⟩
      · rfl
      · fin_cases ph
        · rfl
        · rfl
        · rfl
        · by_cases h₁ : j + 1 < p - 1 <;>
            simp [Tuple.tag, Tuple.p, Tuple.regs, Tuple.stack, Tuple.mode,
              Mode.isCall, stepT, runStepT, machine, step, runStep, State.toTuple, Ctl.toTuple, h₁]
  | leaf i =>
    rcases m with ⟨neg, t⟩ | _
    · by_cases h₁ : i < e <;> cases b <;>
        simp [Tuple.tag, Tuple.n₁, Tuple.ell, Tuple.p, Tuple.regs, Tuple.stack,
          Tuple.mode, Mode.isCall, Mode.target, Mode.neg, stepT, machine, step, State.toTuple,
          Ctl.toTuple, h₁]
    · rfl
  | scan k acc =>
    rcases st with _ | ⟨fr, st⟩
    · rfl
    · by_cases h₁ : k < tableLength e <;> cases b <;>
        simp [Tuple.tag, Tuple.n₁, Tuple.acc, Tuple.ell, Tuple.p, Tuple.regs,
          Tuple.stack, Tuple.withCtl, stepT, machine, step, State.toTuple, Ctl.toTuple, h₁]
  | done => rfl

end Reader

end Cslib.TreeEval
