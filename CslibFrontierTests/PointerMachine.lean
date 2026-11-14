/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module

import CslibFrontier.Computability.PointerMachine.Symbols
import Mathlib.Tactic.FinCases

/-!
# Pointer-machine clients

A checked run exercises creation, links, symbol and integer fields, arithmetic and equality.
Further examples cover null access, new records, invalid pointers and a pure pointer machine.
-/

-- This leaf contains examples and private fixtures, not a public library API.
set_option linter.privateModule false

open Cslib.PointerMachine

private inductive Name where
  | oak | ash
  deriving DecidableEq

/-- Three pointer registers, two data registers, one pointer field and two data fields. -/
private abbrev layout : Layout := ⟨3, 2, 1, 2⟩
private abbrev S := State (Symbols.model Name) layout

private def initial : S :=
  State.empty.setData 0 (Symbols.Value.symbol Name.oak)

private def code : List (Instr (Symbols.model Name) layout) :=
  [.op (.const 3) 1 1 1, .create 0, .create 1, .storePtr 0 0 1,   -- record 0 links to record 1
   .storeData 0 1 0,                        -- record 1 holds the symbol
   .op .add 1 1 1, .storeData 1 1 1,        -- and the integer 3 + 3
   .null 1, .loadPtr 2 0 0,                 -- reach record 1 through the link only
   .moveData 0 1, .loadData 0 0 2,          -- overwrite the symbol, then read it back
   .ifTest .eq 0 0 13, .goto 99, .halt]

/-- The state after `n` steps. -/
private def state : ℕ → S
  | 0 => initial
  | n + 1 => (step code (state n)).getD (state n)

private theorem transition (n : Fin 12) : step code (state n) = some (state (n + 1)) := by
  fin_cases n <;> rfl

private theorem execution : Executes code initial (state 12) 13 := by
  refine ⟨12, ?_, by rfl, rfl⟩
  have run (n : ℕ) (hn : n ≤ 12) : Runs code initial (state n) n := by
    induction n with
    | zero => exact .refl _
    | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (transition ⟨n, by omega⟩)
  exact run 12 le_rfl

-- The output: the symbol read back, the sum, the link, and two records of space.
example : (state 12).data 0 = Symbols.Value.symbol Name.oak := by rfl
example : (state 12).data 1 = Symbols.Value.int 6 := by rfl
example : (state 12).ptr 0 = some 0 ∧ (state 12).ptr 1 = none ∧ (state 12).ptr 2 = some 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl
example : (state 12).heap.length = 2 := by rfl

-- The same program and cost work after swapping the two names; integers are fixed.
example : Executes code
    (initial.rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash)))
    ((state 12).rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash))) 13 :=
  (Executes.rename_iff _).2 execution

-- No symbol appears that was not in the input.
example : ¬Symbols.HasSymbol (state 12) Name.ash := fun h => by
  rcases Symbols.hasSymbol_of_executes execution h with ⟨s, hs⟩ | ⟨n, hn, -⟩
  · fin_cases s <;> simp [initial, State.setData, State.empty] at hs
  · simp [initial, State.setData, State.empty] at hn

-- Arithmetic on a symbol is undefined; it cannot produce or inspect a symbol.
example : Symbols.evalOp .add (.symbol Name.oak) (.int 1) = .undefined := rfl

-- Access through a null pointer does nothing.
example : (Instr.loadData 0 0 0).effect initial = initial := rfl
example : (Instr.storeData 0 0 0).effect initial = initial := rfl

-- A new record has null pointer fields and undefined data fields.
example : ((Instr.create 0).effect initial).deref 0 = some .blank := rfl

-- Validity is a hypothesis on input states, preserved by execution.
example : ¬({ initial with ptr := fun _ => some 0 } : S).Valid := by
  simp [State.Valid, initial, State.setData, State.empty, layout]

example : (state 12).Valid := execution.valid State.empty_valid

-- Access through a pointer that specifies no record also does nothing.
example : (Instr.loadPtr 1 0 0).effect ({ initial with ptr := fun _ => some 0 } : S) =
    { initial with ptr := fun _ => some 0 } := rfl

-- A pure pointer machine has no data.
private def pureModel : Model := ⟨Unit, (), Empty, Empty, nofun, nofun⟩

example : ((Instr.create 0).effect (.empty : State pureModel ⟨1, 0, 2, 0⟩)).heap.length = 1 := rfl

-- A reset data bank can construct a nonzero integer without a preseeded constant.
example : ((Instr.op (Symbols.Op.const 1) 0 0 0).effect
    (State.empty : S)).data 0 = Symbols.Value.int 1 := rfl

-- Initialize the size field of a newly allocated record to one.
example : (((Instr.storeData 0 0 0).effect
    ((Instr.op (Symbols.Op.const 1) 0 0 0).effect
      ((Instr.create 0).effect (State.empty : S)))).deref 0).map (fun n => n.data 0) =
    some (Symbols.Value.int 1) := rfl

-- Chase two parent links, retaining the last nonnull pointer in register 1.
private abbrev chaseLayout : Layout := ⟨3, 0, 1, 0⟩
private abbrev ChaseState := State pureModel chaseLayout
private def chaseInput : ChaseState :=
  ⟨0, (fun r => if r = 0 then some 0 else none), nofun,
    [⟨fun _ => some 1, nofun⟩, ⟨fun _ => none, nofun⟩]⟩
private def chaseCode : List (Instr pureModel chaseLayout) :=
  [.ifPtrEq 0 2 4, .movePtr 1 0, .loadPtr 0 0 0, .goto 0, .halt]
private def chaseState : ℕ → ChaseState
  | 0 => chaseInput
  | n + 1 => (step chaseCode (chaseState n)).getD (chaseState n)
private theorem chaseTransition (n : Fin 9) :
    step chaseCode (chaseState n) = some (chaseState (n + 1)) := by
  fin_cases n <;> rfl
private theorem chaseExecution : Executes chaseCode chaseInput (chaseState 9) 10 := by
  refine ⟨9, ?_, rfl, rfl⟩
  have run (n : ℕ) (hn : n ≤ 9) : Runs chaseCode chaseInput (chaseState n) n := by
    induction n with
    | zero => exact .refl _
    | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (chaseTransition ⟨n, by omega⟩)
  exact run 9 le_rfl
example : (chaseState 9).ptr 0 = none ∧ (chaseState 9).ptr 1 = some 1 := ⟨rfl, rfl⟩
example {y : ChaseState} {t : ℕ} (h : Executes chaseCode chaseInput y t) :
    y = chaseState 9 ∧ t = 10 := h.unique chaseExecution
example : (chaseState 9).heap.length ≤ chaseInput.heap.length + (10 - 1) :=
  chaseExecution.length_le
