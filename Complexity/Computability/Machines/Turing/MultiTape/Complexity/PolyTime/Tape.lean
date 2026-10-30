/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time operations on finite tape storage

The operations of cslib's existing tapes are certified in plain polynomial time
(`Turing.MultiTapeTM.ComputableInPolyTime`) by composition of list, option and pair operations;
the tidy forms of the closed operations are derived from them. They charge the complete stored
tapes and accept any symbol encoding, including infinite or empty alphabets. Finite-control
interpreters can use these rules without building new tape machines.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.stackTape_cons`: prepend a computed cell,
  retaining the stack's omission of trailing blanks.
* `Turing.MultiTapeTM.ComputableInPolyTime.biTape_moveLeft`, `.biTape_moveRight`,
  `.biTape_write`, `.biTape_step`: native tape operations with `fun_prop` certificates.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.biTape_mk₁`: load a computed list.

## References

Adapts Computability/Probabilistic/Tape.lean from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the tidy calculus, using arbitrary symbol encodings
instead of fixed finite tags.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib.Turing

variable {Symbol α : Type} {input : α ↪ List Bool} {enc : Symbol ↪ List Bool}

/-- Reading the stored list is a change of view of the same encoded bits. -/
@[fun_prop]
theorem stackTape_toList (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime StackTape.toList (encStackTape enc) (encList (encOption enc)) :=
  of_eq fun _ => rfl

/-- Reading a stack head decodes the first cell, with a blank default. -/
@[fun_prop]
theorem stackTape_head (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime StackTape.head (encStackTape enc) (encOption enc) := by
  apply ((headD (encA := encOption enc) none).comp (stackTape_toList enc)).of_enc_eq
  intro tape
  cases tape with | mk values h => cases values <;> rfl

/-- Removing a stack head is the list-tail operation. -/
@[fun_prop]
theorem stackTape_tail (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime StackTape.tail (encStackTape enc) (encStackTape enc) :=
  ((tail (encA := encOption enc)).comp (stackTape_toList enc)).of_enc_eq (fun tape => by
    simp only [Function.comp_def, encStackTape_apply, StackTape.tail_toList])

/-- Prepend a cell without requiring a default symbol or case analysis over the alphabet. -/
@[fun_prop]
theorem stackTape_cons {symbol : α → Option Symbol} {tape : α → StackTape Symbol}
    (hsymbol : ComputableInPolyTime symbol input (encOption enc))
    (htape : ComputableInPolyTime tape input (encStackTape enc)) :
    ComputableInPolyTime (fun a => StackTape.cons (symbol a) (tape a)) input
      (encStackTape enc) := by
  have hcells := (stackTape_toList enc).comp htape
  have hcond : ComputableInPolyTime (fun a => (symbol a).isSome || !(tape a).toList.isEmpty)
      input encBool :=
    bool_or.comp ((optionIsSome hsymbol).prod
      (bool_not.comp ((listIsEmpty (encA := encOption enc)).comp hcells)))
  have hlist : ComputableInPolyTime
      (fun a => if (symbol a).isSome || !(tape a).toList.isEmpty
        then symbol a :: (tape a).toList else []) input (encList (encOption enc)) :=
    hcond.ite (cons' hsymbol hcells) (const [])
  exact hlist.of_enc_eq (fun a => by rw [encStackTape_apply, StackTape.cons_toList])

/-- Map symbols to occupied cells with the list map. -/
@[fun_prop]
theorem stackTape_mapSome (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime StackTape.mapSome (encList enc) (encStackTape enc) :=
  (map (optionSome enc)).of_enc_eq (fun _ => rfl)

private theorem biTape_parts (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime (fun tape : BiTape Symbol => (tape.head, tape.left, tape.right))
      (encBiTape enc) (encPair (encOption enc) (encPair (encStackTape enc) (encStackTape enc))) :=
  of_eq fun _ => rfl

/-- Assemble a tape from its computed head and two sides. -/
@[fun_prop]
theorem biTape_mk {head : α → Option Symbol} {left right : α → StackTape Symbol}
    (hhead : ComputableInPolyTime head input (encOption enc))
    (hleft : ComputableInPolyTime left input (encStackTape enc))
    (hright : ComputableInPolyTime right input (encStackTape enc)) :
    ComputableInPolyTime (fun a => BiTape.mk (head a) (left a) (right a)) input
      (encBiTape enc) :=
  (hhead.prod (hleft.prod hright)).of_enc_eq (fun _ => rfl)

/-- Read the current cell of a computed tape. -/
@[fun_prop]
theorem biTape_head (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime BiTape.head (encBiTape enc) (encOption enc) :=
  (biTape_parts enc).fst'

/-- Extract the stored left side. -/
@[fun_prop]
theorem biTape_left (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime BiTape.left (encBiTape enc) (encStackTape enc) :=
  (biTape_parts enc).snd'.fst'

/-- Extract the stored right side. -/
@[fun_prop]
theorem biTape_right (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime BiTape.right (encBiTape enc) (encStackTape enc) :=
  (biTape_parts enc).snd'.snd'

/-- Move left by the stack operations. -/
@[fun_prop]
theorem biTape_moveLeft (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime BiTape.moveLeft (encBiTape enc) (encBiTape enc) := by
  unfold BiTape.moveLeft
  fun_prop

/-- Move right by the stack operations. -/
@[fun_prop]
theorem biTape_moveRight (enc : Symbol ↪ List Bool) :
    ComputableInPolyTime BiTape.moveRight (encBiTape enc) (encBiTape enc) := by
  unfold BiTape.moveRight
  fun_prop

/-- Write a computed optional symbol, including blank erasure. -/
@[fun_prop]
theorem biTape_write {tape : α → BiTape Symbol} {symbol : α → Option Symbol}
    (htape : ComputableInPolyTime tape input (encBiTape enc))
    (hsymbol : ComputableInPolyTime symbol input (encOption enc)) :
    ComputableInPolyTime (fun a => (tape a).write (symbol a)) input (encBiTape enc) := by
  unfold BiTape.write
  fun_prop

/-- Execute a fixed native action, charging the full encoded tape. -/
@[fun_prop]
theorem biTape_step (action : Option (Option Symbol) × SignType)
    {tape : α → BiTape Symbol}
    (htape : ComputableInPolyTime tape input (encBiTape enc)) :
    ComputableInPolyTime (fun a => (tape a).step action) input (encBiTape enc) := by
  rcases action with ⟨write, move⟩
  cases write <;> cases move <;>
    simp only [BiTape.step, Option.elim_none, Option.elim_some] <;> fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

open Cslib.Turing

variable {Symbol α : Type} {input : α ↪ List Bool} {enc : Symbol ↪ List Bool}

/-- Reading the stored list is a change of view of the same encoded bits. -/
@[fun_prop]
theorem stackTape_toList (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime StackTape.toList (encStackTape enc) (encList (encOption enc)) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.stackTape_toList enc)

/-- Reading a stack head decodes the first cell, with a blank default. -/
@[fun_prop]
theorem stackTape_head (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime StackTape.head (encStackTape enc) (encOption enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.stackTape_head enc)

/-- Removing a stack head is the certified list-tail operation. -/
@[fun_prop]
theorem stackTape_tail (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime StackTape.tail (encStackTape enc) (encStackTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.stackTape_tail enc)

/-- Prepend a cell without requiring a default symbol or case analysis over the alphabet. -/
@[fun_prop]
theorem stackTape_cons {symbol : α → Option Symbol} {tape : α → StackTape Symbol}
    (hsymbol : ComputableTidilyInPolyTime symbol input (encOption enc))
    (htape : ComputableTidilyInPolyTime tape input (encStackTape enc)) :
    ComputableTidilyInPolyTime (fun a => StackTape.cons (symbol a) (tape a)) input
      (encStackTape enc) := by
  have hlist : ComputableTidilyInPolyTime
      (fun a => if (symbol a).isSome || !(tape a).toList.isEmpty
        then symbol a :: (tape a).toList else []) input (encList (encOption enc)) := by fun_prop
  exact hlist.of_enc_eq (fun a => by rw [encStackTape_apply, StackTape.cons_toList])

/-- Map symbols to occupied cells with the certified list map. -/
@[fun_prop]
theorem stackTape_mapSome (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime StackTape.mapSome (encList enc) (encStackTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.stackTape_mapSome enc)

/-- Assemble a tape from its computed head and two sides. -/
@[fun_prop]
theorem biTape_mk {head : α → Option Symbol} {left right : α → StackTape Symbol}
    (hhead : ComputableTidilyInPolyTime head input (encOption enc))
    (hleft : ComputableTidilyInPolyTime left input (encStackTape enc))
    (hright : ComputableTidilyInPolyTime right input (encStackTape enc)) :
    ComputableTidilyInPolyTime (fun a => BiTape.mk (head a) (left a) (right a)) input
      (encBiTape enc) :=
  (hhead.prod (hleft.prod hright)).of_enc_eq (fun _ => rfl)

/-- Read the current cell of a computed tape. -/
@[fun_prop]
theorem biTape_head (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.head (encBiTape enc) (encOption enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.biTape_head enc)

/-- Extract the stored left side. -/
@[fun_prop]
theorem biTape_left (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.left (encBiTape enc) (encStackTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.biTape_left enc)

/-- Extract the stored right side. -/
@[fun_prop]
theorem biTape_right (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.right (encBiTape enc) (encStackTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.biTape_right enc)

/-- Move left by the existing stack operations. -/
@[fun_prop]
theorem biTape_moveLeft (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.moveLeft (encBiTape enc) (encBiTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.biTape_moveLeft enc)

/-- Move right by the existing stack operations. -/
@[fun_prop]
theorem biTape_moveRight (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.moveRight (encBiTape enc) (encBiTape enc) :=
  ComputableInPolyTime.tidy (ComputableInPolyTime.biTape_moveRight enc)

/-- Write a computed optional symbol, including blank erasure. -/
@[fun_prop]
theorem biTape_write {tape : α → BiTape Symbol} {symbol : α → Option Symbol}
    (htape : ComputableTidilyInPolyTime tape input (encBiTape enc))
    (hsymbol : ComputableTidilyInPolyTime symbol input (encOption enc)) :
    ComputableTidilyInPolyTime (fun a => (tape a).write (symbol a)) input (encBiTape enc) := by
  unfold BiTape.write
  fun_prop

/-- Execute a fixed native action, charging the full encoded tape. -/
@[fun_prop]
theorem biTape_step (action : Option (Option Symbol) × SignType)
    {tape : α → BiTape Symbol}
    (htape : ComputableTidilyInPolyTime tape input (encBiTape enc)) :
    ComputableTidilyInPolyTime (fun a => (tape a).step action) input (encBiTape enc) :=
  (ComputableInPolyTime.tidy
    (ComputableInPolyTime.biTape_step (enc := enc) action ComputableInPolyTime.id')).comp htape

/-- Loading a list constructs a head and two stacks with no default symbol. -/
@[fun_prop]
theorem biTape_mk₁ (enc : Symbol ↪ List Bool) :
    ComputableTidilyInPolyTime BiTape.mk₁ (encList enc) (encBiTape enc) := by
  have hparts : ComputableTidilyInPolyTime
      (fun values : List Symbol => BiTape.mk (values.head?) StackTape.nil
        (StackTape.mapSome values.tail)) (encList enc) (encBiTape enc) := by fun_prop
  apply hparts.of_enc_eq
  intro values
  cases values <;> rfl

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
