/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Representation
public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.InputProgram

/-!
# Execution correspondence for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_action`: a compiled action realizes the raw tape update.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private theorem control_write (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with
      head := (Function.update (control d symbol busy).head i
        (w.getD ((control d symbol busy).head i))) }
      = control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i <;> simp [Function.update, control, RawTape.write, h]

private theorem store_write (d : Data k State) (i : Fin k) (w : Option (Option Bool)) :
    store { d with work := Function.update d.work i ((d.work i).write w) } = store d := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i <;> cases side <;> simp [store, RawTape.write, h]
  | _ => rfl

private theorem stepAux_writeWork (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (writeWork i w next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).write w) }) := by
  simp only [writeWork, TM2.stepAux, control_write, store_write]

private theorem control_moveLeft (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i false)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveLeft } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveLeft (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
      (.work i false) (d.work i).left.tail =
      store { d with work := Function.update d.work i (d.work i).moveLeft } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveLeft]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem control_moveRight (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i true)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveRight } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveRight (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
      (.work i true) (d.work i).right.tail =
      store { d with work := Function.update d.work i (d.work i).moveRight } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveRight]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem stepAux_moveWork (d : Data k State) (i : Fin k) (direction : SignType)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (moveWork i direction next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step (none, direction)) }
          symbol busy)
        (store
          { d with work := Function.update d.work i ((d.work i).step (none, direction)) }) := by
  cases direction with
  | zero => simp [moveWork, RawTape.step, RawTape.write, Function.update_eq_self]
  | neg =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i false ≠ Stack.work i true)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i false)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
        (.work i false) (d.work i).left.tail) = _
    rw [control_moveLeft, store_moveLeft]
    rfl
  | pos =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i true ≠ Stack.work i false)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i true)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
        (.work i true) (d.work i).right.tail) = _
    rw [control_moveRight, store_moveRight]
    rfl

private theorem stepAux_workAction (d : Data k State) (i : Fin k)
    (a : Option (Option Bool) × SignType) (next : Statement k State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (workAction i a next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step a) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).step a) }) := by
  rw [workAction, stepAux_writeWork, stepAux_moveWork]
  cases a with | mk w direction =>
    cases direction <;> simp [RawTape.step, RawTape.write, Function.update_idem]

private def applyWorks (d : Data k State)
    (a : Fin k → Option (Option Bool) × SignType) (indices : List (Fin k)) : Data k State :=
  indices.foldl (fun d i => { d with work := Function.update d.work i ((d.work i).step (a i)) }) d

private theorem stepAux_workActions (indices : List (Fin k))
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (indices.foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control (applyWorks d a indices) symbol busy)
        (store (applyWorks d a indices)) := by
  induction indices generalizing d with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldr_cons, stepAux_workAction, ih]
    rfl

private theorem applyWorks_eq (indices : List (Fin k)) (h : indices.Nodup)
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State) :
    applyWorks d a indices =
      { d with work := fun i => if i ∈ indices then (d.work i).step (a i) else d.work i } := by
  induction indices generalizing d with
  | nil => simp [applyWorks]
  | cons i indices ih =>
    rw [List.nodup_cons] at h
    change applyWorks { d with work := Function.update d.work i ((d.work i).step (a i)) }
      a indices = _
    rw [ih h.2]
    apply Data.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst j
      simp [h.1]
    · by_cases hmem : j ∈ indices <;> simp [hj, hmem]

/-- Each work tape is updated once, in a fixed straight-line statement. -/
private theorem stepAux_allWork (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux ((List.finRange k).foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control { d with work := fun i => (d.work i).step (a i) } symbol busy)
        (store { d with work := fun i => (d.work i).step (a i) }) := by
  rw [stepAux_workActions, applyWorks_eq _ (List.nodup_finRange k)]
  simp only [List.mem_finRange, ↓reduceIte]

/-- One complete compiled action realizes the native update on finite tape data. -/
theorem stepAux_action (d : Data k State) (a : Turing.Action k Bool State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (action a) (control d symbol busy) (store d) = encode (d.step a) := by
  rw [action, stepAux_allWork, stepAux_moveInput, stepAux_finish]
  rfl

/-- One live source transition is exactly one Mathlib stack-machine transition. -/
theorem step_encode [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.step (program tm.q₀ tm.tr) (encode d) = some (encode (Data.totalStep tm d)) := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  change some (TM2.stepAux
    (match d.state with
    | none => TM2.Stmt.goto (fun _ => .clean)
    | some q => action (tm.tr q (if d.input.atLeft then none else d.input.right.head?)
        (fun i => (d.work i).head)))
    (control d d.input.right.head? false) (store d)) = _
  rw [hq, stepAux_action, Data.totalStep_of_state tm hq]
  rfl

/-- A halted source starts cleanup on the following target step. -/
theorem step_encode_halt [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.step (program tm.q₀ tm.tr) (encode d) =
      some ⟨some .clean, control d d.input.right.head? false, store d⟩ := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  simp only [control, hq, TM2.stepAux, store]

/-- Native initialization already has the stack layout required by the compiler. -/
theorem encode_init [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool) :
    encode (Data.init tm.q₀ input) = initList (machine tm.q₀ tm.tr) input := by
  apply congrArg (fun s =>
    (⟨some .run, initialControl tm.q₀, s⟩ : TM2.Cfg (Alphabet (k := k)) Label (Control k State)))
  funext s
  cases s with
  | work i b => cases b <;> rfl
  | _ => rfl

end

end Turing.MultiTapeTM.ToTM2
