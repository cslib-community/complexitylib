/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.PointerMachine.Symbols
import Mathlib.Tactic.FinCases

/-!
# Typed pointer-machine clients

Abstract names coexist with integer sizes and references. Checked runs exercise allocation,
links, typed fields, arithmetic and equality without any conversion between these domains.
-/

-- This leaf contains examples and private fixtures, not a public library API.
set_option linter.privateModule false

open Cslib.PointerMachine

private inductive Name where
  | oak | ash
  deriving DecidableEq

private abbrev layout : Layout 2 := ⟨3, 1, fun _ => 2, fun _ => 1⟩
private abbrev S := State (Symbols.model Name) layout

private def initial : S :=
  (((State.empty : S).setData (t := 0) 0 Name.oak).setData (t := 0) 1 Name.ash).setData
    (t := 1) 0 (2 : Int) |>.setData (t := 1) 1 (3 : Int)

private def code : List (Instr (Symbols.model Name) layout) :=
  [.alloc 0, .alloc 1, .storePtr 0 0 1,
   .storeData (t := 0) 1 0 0, .op Symbols.Op.add 0 0 1,
   .storeData (t := 1) 1 0 0, .null 1, .loadPtr 2 0 0,
   .loadData (t := 0) 1 2 0, .loadData (t := 1) 1 2 0,
   .dataEq (t := 0) 0 1 12, .jump 99, .halt]

-- Explicit snapshots keep the example independent of the evaluator being checked.
private def state : ℕ → S
  | 0 => initial
  | 1 => { initial with
      pc := 1
      size := 1
      ptr := Function.update initial.ptr 0 (some (.node (NodeId.ofIndex 0))) }
  | 2 => { state 1 with
      pc := 2
      size := 2
      ptr := Function.update (state 1).ptr 1 (some (.node (NodeId.ofIndex 1))) }
  | 3 => { state 2 with
      pc := 3
      heap := Function.update (state 2).heap (NodeId.ofIndex 0)
        { Node.empty with ptr := Function.const _ (some (.node (NodeId.ofIndex 1))) } }
  | 4 => { state 3 with
      pc := 4
      heap := Function.update (state 3).heap (NodeId.ofIndex 1)
        (Node.empty.setData (t := 0) 0 Name.oak) }
  | 5 => { (state 4).setData (t := 1) 0 (5 : Int) with pc := 5 }
  | 6 => { state 5 with
      pc := 6
      heap := Function.update (state 5).heap (NodeId.ofIndex 1)
        (((state 5).heap (NodeId.ofIndex 1)).setData (t := 1) 0 (5 : Int)) }
  | 7 => { state 6 with pc := 7, ptr := Function.update (state 6).ptr 1 (some .null) }
  | 8 => { state 7 with
      pc := 8
      ptr := Function.update (state 7).ptr 2 (some (.node (NodeId.ofIndex 1))) }
  | 9 => { (state 8).setData (t := 0) 1 Name.oak with pc := 9 }
  | 10 => { (state 9).setData (t := 1) 1 (5 : Int) with pc := 10 }
  | _ + 11 => { state 10 with pc := 12 }

private theorem transition (n : Fin 11) :
    step code (state n) = .next (state (n + 1)) := by
  fin_cases n <;> simp only [state]
  all_goals dsimp [code, initial, step, Instr.eval, State.access, State.address,
      State.empty, State.setData, Node.setData, State.fresh, Node.empty]
  all_goals simp [state, initial, State.empty, State.setData, Node.setData, Node.empty,
    Function.update_apply, Function.update_eq_const_of_subsingleton,
    NodeId.ofIndex_injective.eq_iff]

private theorem execution : Executes code (state 0) (state 11) 12 := by
  refine ⟨11, ?_, ?_, rfl⟩
  · have run (n : ℕ) (hn : n ≤ 11) : Runs code (state 0) (state n) n := by
      induction n with
      | zero => exact .refl _
      | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (transition ⟨n, by omega⟩)
    exact run 11 le_rfl
  · simp [state, step, code]

example : (state 11).data 0 1 = some Name.oak ∧
    (state 11).data 1 1 = some (5 : Int) ∧ (state 11).size = 2 := by
  simp [state, State.setData]

-- The same program and cost work after swapping the two names; integers remain fixed.
example : Executes code
    ((state 0).rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash)))
    ((state 11).rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash))) 12 :=
  execution.rename _

-- The primitive signature cannot accept or produce symbols.
example : IsEmpty (Symbols.Op 0 1 1) := ⟨fun f => nomatch f⟩
example : IsEmpty (Symbols.Op 1 1 0) := ⟨fun f => nomatch f⟩

-- No arithmetic structure is supplied for references.
example : True := by
  fail_if_success have _ : NodeId := NodeId.ofIndex 0 + NodeId.ofIndex 1
  trivial

-- Null stores ignore even an undefined source; control still advances.
private def nullState : S := { State.empty with ptr := fun _ => some .null }

example : (Instr.storeData (t := 0) 0 0 0).eval nullState =
    some { nullState with pc := 1 } := rfl

example : (Instr.loadData (t := 0) 0 0 0).eval nullState =
    some { nullState with pc := 1 } := rfl

example : (Instr.loadPtr 0 0 0 : Instr (Symbols.model Name) layout).eval .empty = none := rfl

-- Allocated fields are undefined, distinct from null; reading one faults.
example : (Instr.loadPtr 1 0 0 : Instr (Symbols.model Name) layout).eval (state 1) = none := by
  simp [state, initial, Instr.eval, State.access, State.address,
    State.empty, State.setData, Node.empty]


-- Allocation overwrites inaccessible storage rather than inheriting symbols from it.
example : match (Instr.alloc 0 : Instr (Symbols.model Name) layout).eval
    { (State.empty : S) with heap := fun _ => Node.empty.setData (t := 0) 0 Name.ash } with
    | some y => (y.heap (State.empty : S).fresh).data 0 0 = none
    | none => False := by
  simp [Instr.eval, State.empty, State.fresh, Node.empty]

-- An allocated-pointer invariant is not automatic for arbitrary input states.
example : ¬({ (State.empty : S) with ptr := fun _ => some (.node (NodeId.ofIndex 0)) }).Valid := by
  simp [State.Valid, State.empty, State.Allocated, layout]

-- A zero-sort, zero-field instance is a pure pointer machine.
private def pureModel : Model 0 where
  Value t := Fin.elim0 t
  decValue t := Fin.elim0 t
  Op a _ _ := Fin.elim0 a
  Test a _ := Fin.elim0 a
  evalOp := fun {a} => Fin.elim0 a
  evalTest := fun {a} => Fin.elim0 a

private abbrev pureLayout : Layout 0 := ⟨1, 0, Fin.elim0, Fin.elim0⟩

example : match (Instr.alloc 0 : Instr pureModel pureLayout).eval .empty with
    | some y => y.size = 1 ∧ y.ptr 0 = some (.node (State.empty : State pureModel pureLayout).fresh)
    | none => False := by simp [Instr.eval, State.empty, State.fresh]
