/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Representation

/-!
# Compiled input movement and output emission

## Main definitions

* `Turing.MultiTapeTM.ToTM2.inputSymbol`: the scratch symbol after compiled input movement.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_moveInput`: compiled movement agrees with the raw input
  zipper, without a validity assumption.
* `Turing.MultiTapeTM.ToTM2.stepAux_finish`: emit an optional bit and restore boundary control.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Input movement retains scratch at the left boundary and otherwise remembers the popped bit. -/
def inputSymbol (d : Data k State) (direction : SignType) (scratch : Option Bool) : Option Bool :=
  if d.input.atLeft then scratch else
    match direction with
    | .zero => scratch
    | .neg => d.input.left.head?
    | .pos => d.input.right.head?

/-- The compiled input movement agrees with the zipper on every raw configuration. -/
theorem stepAux_moveInput (d : Data k State) (direction : SignType)
    (next : Statement k State) (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux (moveInput direction next) (control d scratch busy) (store d) =
      TM2.stepAux next
        (control { d with input := d.input.move direction } (inputSymbol d direction scratch) busy)
        (store { d with input := d.input.move direction }) := by
  classical
  rcases d with ⟨state, ⟨left, right, atLeft⟩, work, output⟩
  cases direction <;> cases atLeft
  all_goals try rfl
  all_goals cases left <;> cases right
  all_goals
    simp only [moveInput, TM2.stepAux, control, store, inputSymbol, Input.move, Input.moveLeft,
      Input.moveRight]
  all_goals simp only [Alphabet, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.isSome_none, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  all_goals
    congr 1 with s : 1
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

/-- Emitting an optional bit and loading the next source state restores a step boundary. -/
theorem stepAux_finish (d : Data k State) (state : Option State) (output : Option Bool)
    (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux
      (output.elim id (fun b => TM2.Stmt.push .reversed (fun _ => b))
        (TM2.Stmt.load (fun v => { v with state := state, symbol := none, busy := false })
          (TM2.Stmt.goto (fun _ => .run))))
      (control d scratch busy) (store d) =
      encode { d with state := state, output := d.output ++ output.toList } := by
  classical
  cases output with
  | none =>
    simp only [Option.elim, encode, Option.toList_none, List.append_nil]
    congr 1
  | some b =>
    simp only [Option.elim, TM2.stepAux, encode, Option.toList_some]
    congr 1 with s : 1
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

end

end Turing.MultiTapeTM.ToTM2
