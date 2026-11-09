/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Configuration
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite stack program for deterministic multi-tape machines

The input uses a pair of binary stacks and a flag for the left boundary. Each two-sided work
tape uses two stacks over `Option Bool`, with its current cell in finite control. Output is
accumulated in reverse order. A separate cleanup phase empties all auxiliary stacks before
reversing the output and resetting the control to Mathlib's canonical `haltList` convention.

## Main definitions

* `Turing.TM2.selectList`, `Turing.TM2.select`: finite case analysis in a TM2 statement.
* `Turing.MultiTapeTM.ToTM2.machine`: the finite-alphabet stack machine.
* `Turing.MultiTapeTM.ToTM2.program`: its running, cleanup and output-reversal phases.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/

public section

namespace Turing.TM2

open Stmt

variable {K : Type} {Γ : K → Type} {Λ State : Type}

/-- Finite case analysis compiles an arbitrary table on finite control to a fixed statement. -/
def selectList [DecidableEq State] (values : List State)
    (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  values.foldr (fun value rest => branch (fun state => decide (state = value)) (table value) rest)
    halt

theorem stepAux_selectList [DecidableEq State] [DecidableEq K]
    (values : List State) (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) (h : state ∈ values) :
    stepAux (selectList values table) state store = stepAux (table state) state store := by
  induction values with
  | nil => simp at h
  | cons value values ih =>
    simp only [selectList, List.foldr_cons, stepAux]
    by_cases heq : state = value
    · subst value
      simp
    · simp only [heq, decide_false, Bool.cond_false]
      exact ih (List.mem_of_ne_of_mem heq h)

open scoped Classical in
/-- A table on a finite type uses only finitely many branches. -/
noncomputable def select [Fintype State] (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  selectList (Finset.univ.toList) table

theorem stepAux_select [Fintype State] [DecidableEq K]
    (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) :
    stepAux (select table) state store = stepAux (table state) state store := by
  classical
  exact stepAux_selectList _ _ _ _ (by simp)

end Turing.TM2

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- The four binary stacks and the two stacks for every work tape. -/
inductive Stack (k : ℕ) where
  | input | before | output | reversed
  | work (tape : Fin k) (right : Bool)
  deriving @[expose] DecidableEq, @[expose] Fintype

/-- Work stacks store blank cells explicitly; the input and output alphabets are binary. -/
abbrev Alphabet : Stack k → Type
  | .work _ _ => Option Bool
  | _ => Bool

instance (s : Stack k) : Fintype (Alphabet s) := by
  cases s <;> unfold Alphabet <;> infer_instance

/-- The three phases have no unbounded counters in their control. -/
inductive Label where
  | run | clean | reverse
  deriving @[expose] DecidableEq

instance : Fintype Label := ⟨{.run, .clean, .reverse}, by intro l; cases l <;> simp⟩

/-- All unbounded data live on stacks. `symbol` and `busy` are scratch registers. -/
@[ext] structure Control (k : ℕ) (State : Type) where
  /-- The source state, or `none` when its final action has executed. -/
  state : Option State
  /-- Whether the bounded input head is at the blank before the word. -/
  atLeft : Bool
  /-- The current cell on each work tape. -/
  head : Fin k → Option Bool
  /-- A scratch register for input movement and output reversal. -/
  symbol : Option Bool
  /-- Whether the current cleanup round found a nonempty auxiliary stack. -/
  busy : Bool
  deriving @[expose] Fintype

/-- Initial finite control, also restored before halting. -/
@[expose] def initialControl (q : State) : Control k State :=
  ⟨some q, false, fun _ => none, none, false⟩

/-- A statement over the compiler's stack alphabets, phases and finite control. -/
abbrev Statement (k : ℕ) (State : Type) :=
  TM2.Stmt (Alphabet (k := k)) Label (Control k State)

open TM2.Stmt

/-- Write the current work cell, retaining the old value when no write is requested. -/
@[expose] def writeWork (i : Fin k) (write : Option (Option Bool)) (next : Statement k State) :
    Statement k State :=
  load (fun v => { v with head := Function.update v.head i (write.getD (v.head i)) }) next

/-- Moving a work head transfers its old current cell to the opposite stack. -/
@[expose] def moveWork (i : Fin k) (direction : SignType) (next : Statement k State) :
    Statement k State :=
  match direction with
  | .zero => next
  | .neg => push (.work i true) (fun v => v.head i)
      (pop (.work i false) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)
  | .pos => push (.work i false) (fun v => v.head i)
      (pop (.work i true) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)

/-- A fixed native work-tape action is a bounded straight-line stack statement. -/
@[expose] def workAction (i : Fin k) (action : Option (Option Bool) × SignType)
    (next : Statement k State) : Statement k State :=
  writeWork i action.1 (moveWork i action.2 next)

/-- Move the bounded read-only input head. Empty stacks detect the two boundaries. -/
@[expose] def moveInput (direction : SignType) (next : Statement k State) : Statement k State :=
  match direction with
  | .zero => next
  | .neg => branch (fun v => v.atLeft) next
      (pop .before (fun v a => { v with symbol := a })
        (branch (fun v => v.symbol.isSome)
          (push .input (fun v => v.symbol.getD false) next)
          (load (fun v => { v with atLeft := true }) next)))
  | .pos => branch (fun v => v.atLeft) (load (fun v => { v with atLeft := false }) next)
      (pop .input (fun v a => { v with symbol := a })
        (branch (fun v => v.symbol.isSome)
          (push .before (fun v => v.symbol.getD false) next) next))

/-- A source step updates every work tape, the input head, output and control. -/
@[expose] def action (a : Turing.Action k Bool State) : Statement k State :=
  (List.finRange k).foldr (fun i next => workAction i (a.workTapes i) next)
    (moveInput a.inputTape
      (a.output.elim id (fun b => push .reversed (fun _ => b))
        (load (fun v => { v with state := a.state, symbol := none, busy := false })
          (goto (fun _ => .run)))))

/-- Stacks discarded before output reversal. -/
@[expose] def auxiliaries (k : ℕ) : List (Stack k) :=
  [.input, .before] ++ (List.finRange k).flatMap (fun i => [.work i false, .work i true])

/-- Discard one cell from each auxiliary stack and remember whether any was nonempty. -/
@[expose] def discard (s : Stack k) (next : Statement k State) : Statement k State :=
  pop s (fun v a => { v with busy := v.busy || a.isSome }) next

/-- A cleanup round either reduces auxiliary storage or advances to output reversal. -/
@[expose] def clean : Statement k State :=
  load (fun v => { v with busy := false })
    ((auxiliaries k).foldr discard
      (branch (fun v => v.busy) (goto (fun _ => .clean)) (goto (fun _ => .reverse))))

/-- The fixed program has finite control and a finite alphabet on every stack. -/
@[expose] def program [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    Label → Statement k State
  | .run => peek .input (fun v a => { v with symbol := a })
      (TM2.select fun v => match v.state with
        | none => goto (fun _ => .clean)
        | some q => action (transition q (if v.atLeft then none else v.symbol) v.head))
  | .clean => clean
  | .reverse => pop .reversed (fun v a => { v with symbol := a })
      (branch (fun v => v.symbol.isSome)
        (push .output (fun v => v.symbol.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => initialControl q₀) halt))

/-- The actual Mathlib `FinTM2` produced by the reverse compiler. -/
abbrev machine [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    FinTM2 where
  K := Stack k
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .run
  σ := Control k State
  initialState := initialControl q₀
  m := program q₀ transition

end

end Turing.MultiTapeTM.ToTM2
