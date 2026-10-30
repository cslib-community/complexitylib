/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Loops with a stack of frames

A stack loop (`Turing.MultiTapeTM.StackLoop`) keeps a current value and a stack of frames. While
`halt` is false at the current value, a round pops the top frame (`none` on an empty stack),
applies `round` to it and the current value, pushes the returned frames (the first one ends on
top) and continues with the returned value.

The machine keeps the stack on its own work tape, so a round touches only the current value, the
popped frame and the pushed frames: its cost does not depend on the frames deeper in the stack.
This makes recursive algorithms such as divide and conquer computable within the sum of the costs
of their calls, rather than paying for the whole recursion state on every round.

## Main definitions

* `Turing.MultiTapeTM.StackLoop`: the round and the halting test of a stack loop.
* `Turing.MultiTapeTM.StackLoop.step`: one round on a value and a stack.

## Main results

* `Turing.MultiTapeTM.ComputableInO.stackLoop`: if the initial value, the halting test and
  the round are computable, so is the value at which the loop halts with an empty stack,
  within the sum over the rounds of their costs and the lengths of the words they touch.
-/

public section

namespace Turing.MultiTapeTM

/-- A loop with a stack of frames: a halting test on the current value, and a round taking the
popped top frame (`none` on an empty stack) and the current value to the frames to push, the
first one ending on top, and the next value. -/
structure StackLoop (α γ : Type) where
  /-- Whether the loop stops at the current value. -/
  halt : α → Bool
  /-- A round: from the popped frame and the current value, the pushed frames and the next
  value. -/
  round : Option γ × α → List γ × α

namespace StackLoop

variable {α γ : Type}

/-- The input of a round on the value `s.1` and the stack `s.2`, top first: the top frame, if
any, and the value. -/
@[expose] def roundInput (s : α × List γ) : Option γ × α := (s.2.head?, s.1)

/-- One round on a value and a stack, top first: pop the top frame, apply the round, push the
returned frames. -/
@[expose] def step (L : StackLoop α γ) (s : α × List γ) : α × List γ :=
  ((L.round (roundInput s)).2, (L.round (roundInput s)).1 ++ s.2.tail)

end StackLoop

open StackLoop

/-- **Stack loops.** If the initial value, the halting test and the round of a stack loop are
computable, and from the initial value with an empty stack the loop halts after `n x`
rounds with an empty stack, then the halting value is computable. The time and space are
the costs of the initialization, plus, for every round and the final halting test, the costs of
the halting test and of the round together with the lengths of the words they read and write.

The frames are kept on a separate work tape: a round pays for the popped and pushed frames only,
not for the rest of the stack. -/
theorem ComputableInO.stackLoop {δ α γ : Type} {encIn : δ ↪ List Bool}
    {encA : α ↪ List Bool} {encG : γ ↪ List Bool} (L : StackLoop α γ)
    {init : δ → α} {Ti Si : δ → ℕ} {Th Sh : α → ℕ} {Tr Sr : Option γ × α → ℕ} (n : δ → ℕ)
    (hinit : ComputableInO init encIn encA Ti Si)
    (hhalt : ComputableInO L.halt encA encBool Th Sh)
    (hround : ComputableInO L.round (encPair (encOption encG) encA)
      (encPair (encList encG) encA) Tr Sr)
    (hrun : ∀ x, ∀ i < n x, L.halt (L.step^[i] (init x, [])).1 = false)
    (hstop : ∀ x, L.halt (L.step^[n x] (init x, [])).1 = true)
    (hempty : ∀ x, (L.step^[n x] (init x, [])).2 = []) :
    ComputableInO (fun x => (L.step^[n x] (init x, [])).1) encIn encA
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length))
      (fun x => (encIn x).length + Ti x + Si x +
        ∑ i ∈ Finset.range (n x + 1),
          (Th (L.step^[i] (init x, [])).1 + Sh (L.step^[i] (init x, [])).1 +
            (encA (L.step^[i] (init x, [])).1).length) +
        ∑ i ∈ Finset.range (n x),
          (Tr (roundInput (L.step^[i] (init x, []))) + Sr (roundInput (L.step^[i] (init x, []))) +
            (encPair (encOption encG) encA (roundInput (L.step^[i] (init x, [])))).length +
            (encPair (encList encG) encA (L.round (roundInput (L.step^[i] (init x, []))))).length)) :=
  sorry

end Turing.MultiTapeTM
