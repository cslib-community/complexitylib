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
  (State.empty.setData 0 (Symbols.Value.symbol Name.oak)).setData 1 (Symbols.Value.int 3)

private def code : List (Instr (Symbols.model Name) layout) :=
  [.create 0, .create 1, .storePtr 0 0 1,   -- record 0 links to record 1
   .storeData 0 1 0,                        -- record 1 holds the symbol
   .op .add 1 1 1, .storeData 1 1 1,        -- and the integer 3 + 3
   .null 1, .loadPtr 2 0 0,                 -- reach record 1 through the link only
   .moveData 0 1, .loadData 0 0 2,          -- overwrite the symbol, then read it back
   .ifTest .eq 0 0 12, .goto 99, .halt]

/-- The state after `n` steps. -/
private def state : ℕ → S
  | 0 => initial
  | n + 1 => (step code (state n)).getD (state n)

private theorem transition (n : Fin 11) : step code (state n) = some (state (n + 1)) := by
  fin_cases n <;> rfl

private theorem execution : Executes code initial (state 11) 12 := by
  refine ⟨11, ?_, by rfl, rfl⟩
  have run (n : ℕ) (hn : n ≤ 11) : Runs code initial (state n) n := by
    induction n with
    | zero => exact .refl _
    | succ n ih => exact .tail _ _ _ _ (ih (by omega)) (transition ⟨n, by omega⟩)
  exact run 11 le_rfl

-- The output: the symbol read back, the sum, the link, and two records of space.
example : (state 11).data 0 = Symbols.Value.symbol Name.oak := by rfl
example : (state 11).data 1 = Symbols.Value.int 6 := by rfl
example : (state 11).ptr 0 = some 0 ∧ (state 11).ptr 1 = none ∧ (state 11).ptr 2 = some 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl
example : (state 11).heap.length = 2 := by rfl

-- The same program and cost work after swapping the two names; integers are fixed.
example : Executes code
    (initial.rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash)))
    ((state 11).rename (Symbols.symbolRenaming (Equiv.swap Name.oak Name.ash))) 12 :=
  execution.rename _

-- No symbol appears that was not in the input.
example : ¬Symbols.HasSymbol (state 11) Name.ash := fun h => by
  rcases Symbols.hasSymbol_of_runs execution.choose_spec.1 h with ⟨s, hs⟩ | ⟨n, hn, -⟩
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

example : (state 11).Valid := execution.choose_spec.1.valid State.empty_valid

-- Access through a pointer that specifies no record also does nothing.
example : (Instr.loadPtr 1 0 0).effect ({ initial with ptr := fun _ => some 0 } : S) =
    { initial with ptr := fun _ => some 0 } := rfl

-- A pure pointer machine has no data.
private def pureModel : Model := ⟨Unit, (), Empty, Empty, nofun, nofun⟩

example : ((Instr.create 0).effect (.empty : State pureModel ⟨1, 0, 2, 0⟩)).heap.length = 1 := rfl
