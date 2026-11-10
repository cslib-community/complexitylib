/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BiTape
public import CslibFrontier.Foundations.Data.StackTape
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Indexed observations, native actions, and Mathlib `Tape` equivalence on bidirectional tapes

Bolton Bailey's upstream `BiTape` stores finite data relative to the current head. Its integer
view includes blank gaps and negative displacements. The representation relation allows a native
integer-indexed tape to have any absolute head position. We also provide the canonical equivalence
`BiTape.equivTape` between `BiTape Symbol` and Mathlib's `_root_.Turing.Tape (Option Symbol)`.

## Main definitions

* `Cslib.Turing.BiTape.read`: observe the tape at an integer displacement.
* `Cslib.Turing.BiTape.step`: an optional write followed by a signed move.
* `Cslib.Turing.BiTape.Represents`: agreement with a native tape and its head position.
* `Cslib.Turing.BiTape.equivTape`: equivalence between `BiTape Symbol` and
  `_root_.Turing.Tape (Option Symbol)`.

## Main results

* `Cslib.Turing.BiTape.Represents.step`: native actions preserve the represented tape.
* `Cslib.Turing.BiTape.spaceUsed_step_le`: each action adds at most one stored cell.
* `Cslib.Turing.BiTape.equivTape_mk₁`, `equivTape_write`, `equivTape_move`, `nth_equivTape`:
  `equivTape` commutes with tape initialization, writes, head movement, and indexed reads.

## References

Ports the additions to Foundations/Data/BiTape.lean and the tape action laws from
Computability/Machines/Turing/MultiTape/FiniteTape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Turing.BiTape

variable {Symbol : Type*}

/-- A tape is determined by its current symbol and two stored sides. -/
@[ext] theorem ext {left right : BiTape Symbol} (head : left.head = right.head)
    (before : left.left = right.left) (after : left.right = right.right) : left = right := by
  cases left
  cases right
  cases head
  cases before
  cases after
  rfl

/-- Read a cell at an integer displacement from the current head. Negative positions lie to
the left; cells outside the finite stored contents are blank. -/
def read (tape : BiTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => tape.head
  | .ofNat (position + 1) => tape.right.read position
  | .negSucc position => tape.left.read position

/-- Reading at displacement `0` is reading the head. -/
@[simp] lemma read_zero (tape : BiTape Symbol) : tape.read 0 = tape.head := rfl

/-- The empty tape reads blank at every displacement. -/
@[simp] lemma read_nil (position : ℤ) : (nil : BiTape Symbol).read position = none := by
  cases position with
  | ofNat position => cases position <;> simp [read, nil]
  | negSucc position => simp [read, nil]

/-- Loading a word puts its first symbol under the head and leaves all negative cells blank. -/
lemma read_mk₁ (values : List Symbol) (position : ℤ) :
    (mk₁ values).read position = if 0 ≤ position then values[position.toNat]? else none := by
  cases values with
  | nil => simp [mk₁]
  | cons value values =>
    cases position with
    | ofNat position =>
      cases position <;> simp [read, mk₁, add_nonneg]
    | negSucc position => simp [read, mk₁]

/-- Moving the head right shifts the relative reading coordinates by one cell. -/
lemma read_moveRight (tape : BiTape Symbol) (position : ℤ) :
    tape.moveRight.read position = tape.read (position + 1) := by
  cases position with
  | ofNat position => cases position <;> rfl
  | negSucc position =>
    cases position with
    | zero => simp [read, moveRight]
    | succ position =>
      have h : Int.negSucc (position + 1) + 1 = Int.negSucc position := by lia
      simp [read, moveRight, h]

/-- Moving the head left shifts the relative reading coordinates by one cell. -/
lemma read_moveLeft (tape : BiTape Symbol) (position : ℤ) :
    tape.moveLeft.read position = tape.read (position - 1) := by
  have h := read_moveRight tape.moveLeft (position - 1)
  simpa using h.symm

/-- A write changes exactly the current cell in the integer-indexed view. -/
lemma read_write (tape : BiTape Symbol) (symbol : Option Symbol) (position : ℤ) :
    (tape.write symbol).read position = if position = 0 then symbol else tape.read position := by
  cases position with
  | ofNat position =>
    cases position <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc position => simp [read, write]

/-- Apply the work-tape component of a native multi-tape action. -/
def step (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) : BiTape Symbol :=
  let written := action.1.elim tape tape.write
  match action.2 with
  | .neg => written.moveLeft
  | .zero => written
  | .pos => written.moveRight

/-- The finite representation agrees with the native tape at every displacement from its head. -/
def Represents (tape : BiTape Symbol) (contents : ℤ → Option Symbol) (head : ℤ) : Prop :=
  ∀ position, tape.read position = contents (head + position)

/-- Blank finite storage represents the native initial work tape. -/
theorem represents_nil (head : ℤ) : (nil : BiTape Symbol).Represents (fun _ => none) head := by
  intro position
  simp

/-- Related tapes present the same symbol to the machine's transition table. -/
theorem Represents.head {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) : tape.head = contents head := by
  simpa using h 0

/-- Finite tape updates realize precisely the native write and movement, with no restriction
on the head position or on blank gaps within the stored contents. -/
theorem Represents.step {tape : BiTape Symbol} {contents : ℤ → Option Symbol} {head : ℤ}
    (h : tape.Represents contents head) (action : Option (Option Symbol) × SignType) :
    (tape.step action).Represents
      (action.1.elim contents (fun symbol => Function.update contents head symbol))
      (head + action.2) := by
  unfold Represents at h
  intro position
  rcases action with ⟨write, move⟩
  cases write with
  | none =>
    cases move <;> simp [BiTape.step, read_moveLeft, read_moveRight, h,
      sub_eq_add_neg, add_left_comm, add_comm]
  | some symbol =>
    cases move <;>
      simp only [BiTape.step, Option.elim_some, read_moveLeft, read_moveRight, read_write,
        SignType.cast]
    all_goals
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | lia | (rw [h]; congr 1; lia)

/-- A work-tape action increases the finite representation by at most one cell. -/
theorem spaceUsed_step_le (tape : BiTape Symbol) (action : Option (Option Symbol) × SignType) :
    (tape.step action).spaceUsed ≤ tape.spaceUsed + 1 := by
  rcases action with ⟨write, move⟩
  cases write <;> cases move <;>
    simp only [step, Option.elim_none, Option.elim_some]
  all_goals first
    | exact spaceUsed_move _ .left
    | exact spaceUsed_move _ .right
    | simp

/-- Writing the current head symbol leaves the tape unchanged. -/
@[simp] lemma write_head_self (tape : BiTape Symbol) : tape.write tape.head = tape := rfl

/-- The tape loaded with a word has the first symbol of the word, if any, under its head. -/
@[simp] lemma head_mk₁ (l : List Symbol) : (mk₁ l).head = l.head? := by
  cases l <;> rfl

/-- The tape loaded with a word is empty to the left of its head. -/
@[simp] lemma left_mk₁ (l : List Symbol) : (mk₁ l).left = ∅ := by
  cases l <;> rfl

/-- The tape loaded with a word stores the rest of the word to the right of its head. -/
@[simp] lemma right_mk₁ (l : List Symbol) : (mk₁ l).right = StackTape.mapSome l.tail := by
  cases l <;> rfl

/-- Moving left on the tape loaded with `l` and writing `a` gives the tape loaded with `a :: l`. -/
@[simp] lemma write_moveLeft_mk₁ (a : Symbol) (l : List Symbol) :
    (mk₁ l).moveLeft.write (some a) = mk₁ (a :: l) := by
  cases l with
  | nil => rfl
  | cons b tl =>
    ext <;> simp [mk₁, moveLeft, write, StackTape.mapSome, StackTape.cons]

/-- Canonical equivalence between `BiTape Symbol` and Mathlib's
`_root_.Turing.Tape (Option Symbol)`. -/
def equivTape : BiTape Symbol ≃ _root_.Turing.Tape (Option Symbol) where
  toFun tape := ⟨tape.head, StackTape.equivListBlank tape.left, StackTape.equivListBlank tape.right⟩
  invFun tape :=
    ⟨tape.head, StackTape.equivListBlank.symm tape.left, StackTape.equivListBlank.symm tape.right⟩
  left_inv tape := by cases tape; simp
  right_inv tape := by cases tape; simp

/-- `equivTape` preserves the head symbol. -/
@[simp] lemma head_equivTape (tape : BiTape Symbol) : (equivTape tape).head = tape.head := rfl

/-- The left side of `equivTape tape` is the `ListBlank` of the left side of `tape`. -/
@[simp] lemma left_equivTape (tape : BiTape Symbol) :
    (equivTape tape).left = StackTape.equivListBlank tape.left := rfl

/-- The right side of `equivTape tape` is the `ListBlank` of the right side of `tape`. -/
@[simp] lemma right_equivTape (tape : BiTape Symbol) :
    (equivTape tape).right = StackTape.equivListBlank tape.right := rfl

/-- The inverse of `equivTape` preserves the head symbol. -/
@[simp] lemma head_equivTape_symm (tape : _root_.Turing.Tape (Option Symbol)) :
    (equivTape.symm tape).head = tape.head := rfl

/-- The left side of `equivTape.symm tape` is the stack tape of the left side of `tape`. -/
@[simp] lemma left_equivTape_symm (tape : _root_.Turing.Tape (Option Symbol)) :
    (equivTape.symm tape).left = StackTape.equivListBlank.symm tape.left := rfl

/-- The right side of `equivTape.symm tape` is the stack tape of the right side of `tape`. -/
@[simp] lemma right_equivTape_symm (tape : _root_.Turing.Tape (Option Symbol)) :
    (equivTape.symm tape).right = StackTape.equivListBlank.symm tape.right := rfl

/-- `equivTape` sends the empty tape to the blank Mathlib tape. -/
@[simp] lemma equivTape_nil : equivTape (nil : BiTape Symbol) = default := rfl

/-- The inverse of `equivTape` sends the blank Mathlib tape to the empty tape. -/
@[simp] lemma equivTape_symm_default :
    equivTape.symm (default : _root_.Turing.Tape (Option Symbol)) = nil := rfl

/-- `equivTape` sends the tape loaded with a word `l` to Mathlib's `Tape.mk₁ (l.map some)`. -/
@[simp] lemma equivTape_mk₁ (l : List Symbol) :
    equivTape (mk₁ l) = _root_.Turing.Tape.mk₁ (l.map some) := by
  cases l <;> rfl

/-- The inverse of `equivTape` sends Mathlib's `Tape.mk₁ (l.map some)` to the tape loaded
with `l`. -/
@[simp] lemma equivTape_symm_mk₁ (l : List Symbol) :
    equivTape.symm (_root_.Turing.Tape.mk₁ (l.map some)) = mk₁ l := by
  apply equivTape.injective
  simp

/-- `equivTape` commutes with writing. -/
@[simp] lemma equivTape_write (tape : BiTape Symbol) (a : Option Symbol) :
    equivTape (tape.write a) = (equivTape tape).write a := rfl

/-- The inverse of `equivTape` commutes with writing. -/
@[simp] lemma equivTape_symm_write (tape : _root_.Turing.Tape (Option Symbol)) (a : Option Symbol) :
    equivTape.symm (tape.write a) = (equivTape.symm tape).write a := rfl

/-- `equivTape` turns `moveLeft` into Mathlib's move to the left. -/
@[simp] lemma equivTape_moveLeft (tape : BiTape Symbol) :
    equivTape tape.moveLeft = (equivTape tape).move .left := by
  simp [equivTape, moveLeft, _root_.Turing.Tape.move]

/-- `equivTape` turns `moveRight` into Mathlib's move to the right. -/
@[simp] lemma equivTape_moveRight (tape : BiTape Symbol) :
    equivTape tape.moveRight = (equivTape tape).move .right := by
  simp [equivTape, moveRight, _root_.Turing.Tape.move]

/-- `equivTape` commutes with moving the head in either direction. -/
@[simp] lemma equivTape_move (tape : BiTape Symbol) (d : _root_.Turing.Dir) :
    equivTape (tape.move d) = (equivTape tape).move d := by
  cases d <;> simp [move]

/-- The inverse of `equivTape` commutes with moving the head in either direction. -/
@[simp] lemma equivTape_symm_move (tape : _root_.Turing.Tape (Option Symbol))
    (d : _root_.Turing.Dir) :
    equivTape.symm (tape.move d) = (equivTape.symm tape).move d := by
  apply equivTape.injective
  simp

/-- `equivTape` commutes with an optional head move, where `none` leaves the tape in place. -/
@[simp] lemma equivTape_optionMove (tape : BiTape Symbol) (d : Option _root_.Turing.Dir) :
    equivTape (tape.optionMove d) = d.elim (equivTape tape) (fun d => (equivTape tape).move d) := by
  cases d <;> simp [optionMove]

/-- Reading the Mathlib tape at `i` is reading the tape at displacement `i`. -/
@[simp] lemma nth_equivTape (tape : BiTape Symbol) (i : ℤ) :
    (equivTape tape).nth i = tape.read i := by
  cases i with
  | ofNat n =>
    cases n <;> simp [read, _root_.Turing.Tape.nth]
  | negSucc n =>
    simp [read, _root_.Turing.Tape.nth]

/-- Reading `equivTape.symm tape` at displacement `i` is reading `tape` at `i`. -/
@[simp] lemma read_equivTape_symm (tape : _root_.Turing.Tape (Option Symbol)) (i : ℤ) :
    (equivTape.symm tape).read i = tape.nth i := by
  rw [← nth_equivTape (equivTape.symm tape) i, equivTape.apply_symm_apply]

end Cslib.Turing.BiTape
