/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.StackTape
public import Mathlib.Computability.TuringMachine.Tape

/-!
# Indexed observations and Mathlib `ListBlank` equivalence for finite stack tapes

These additions give Bolton Bailey's upstream `StackTape` an indexed view that reads blank
outside its stored list, together with the canonical equivalence with Mathlib's quotient
one-sided tape `_root_.Turing.ListBlank (Option Symbol)`.

## Main definitions

* `Cslib.Turing.StackTape.read`: observe the tape at a natural-number displacement.
* `Cslib.Turing.StackTape.ofList`: fold a list of optional symbols onto an empty stack tape.
* `Cslib.Turing.StackTape.equivListBlank`: equivalence between `StackTape Symbol` and
  `_root_.Turing.ListBlank (Option Symbol)`.

## Main results

* `Cslib.Turing.StackTape.read_eq_getElem?`: agreement with padded list lookup.
* `Cslib.Turing.StackTape.read_mapSome`: loading a word preserves its indexed symbols.
* `Cslib.Turing.StackTape.equivListBlank_cons`, `head_equivListBlank`, `tail_equivListBlank`,
  `nth_equivListBlank`: `equivListBlank` commutes with stack-tape operations and indexed reads.

## References

Ports the additions to Foundations/Data/StackTape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, retaining the upstream tape representation.
-/

@[expose] public section

namespace Cslib.Turing.StackTape

open scoped _root_.Turing

variable {Symbol : Type*}

/-- Equality of stored lists determines equality of stack tapes. -/
@[ext] theorem ext {left right : StackTape Symbol} (h : left.toList = right.toList) :
    left = right := by
  cases left
  cases right
  cases h
  rfl

/-- The stored list of `tail` is the tail of the stored list. -/
@[simp] lemma tail_toList (tape : StackTape Symbol) : tape.tail.toList = tape.toList.tail := by
  cases tape with | mk values h => cases values <;> rfl

/-- Prepending retains blank cells only when there is stored data beyond them. -/
lemma cons_toList (symbol : Option Symbol) (tape : StackTape Symbol) :
    (cons symbol tape).toList =
      if symbol.isSome || !tape.toList.isEmpty then symbol :: tape.toList else [] := by
  cases symbol <;> cases tape with | mk values h => cases values <;> rfl

/-- Read a cell, treating every position beyond the finite representation as blank. -/
def read : StackTape Symbol → ℕ → Option Symbol
  | tape, 0 => tape.head
  | tape, position + 1 => tape.tail.read position

/-- Reading at `0` is reading the head. -/
@[simp] lemma read_zero (tape : StackTape Symbol) : tape.read 0 = tape.head := rfl

/-- Reading at `position + 1` is reading the tail at `position`. -/
@[simp] lemma read_succ (tape : StackTape Symbol) (position : ℕ) :
    tape.read (position + 1) = tape.tail.read position := rfl

/-- The empty stack tape reads blank everywhere. -/
@[simp] lemma read_nil (position : ℕ) : (nil : StackTape Symbol).read position = none := by
  induction position <;> simp_all [read, head, tail, nil]

/-- The indexed view agrees with the stored list, with absent cells read as blanks. -/
lemma read_eq_getElem? (tape : StackTape Symbol) (position : ℕ) :
    tape.read position = tape.toList[position]?.join := by
  induction position generalizing tape with
  | zero => cases tape with | mk values h => cases values <;> rfl
  | succ position ih =>
    rw [read_succ, ih]
    cases tape with | mk values h => cases values <;> simp [tail, nil]

/-- The tape loaded with a word reads its symbol at each position, and blank past its end. -/
@[simp] lemma read_mapSome (values : List Symbol) (position : ℕ) :
    (mapSome values).read position = values[position]? := by
  simp only [read_eq_getElem?, mapSome, List.getElem?_map]
  cases values[position]? <;> rfl

/-- Prepending a blank to the empty stack tape leaves it empty. -/
@[simp] lemma cons_none_nil : cons none (nil : StackTape Symbol) = nil := by
  ext
  simp

/-- Construct a `StackTape` from an arbitrary list of optional symbols by folding `cons`. -/
def ofList (values : List (Option Symbol)) : StackTape Symbol :=
  values.foldr cons nil

/-- `ofList` turns the empty list into the empty stack tape. -/
@[simp] lemma ofList_nil : (ofList [] : StackTape Symbol) = nil := rfl

/-- `ofList` turns list prepending into `cons`. -/
@[simp] lemma ofList_cons (a : Option Symbol) (l : List (Option Symbol)) :
    ofList (a :: l) = cons a (ofList l) := rfl

/-- A list of blanks gives the empty stack tape. -/
@[simp] lemma ofList_replicate_none (n : ℕ) :
    (ofList (List.replicate n none) : StackTape Symbol) = nil := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- Trailing blanks do not change `ofList`. -/
lemma ofList_append_replicate_none (l : List (Option Symbol)) (n : ℕ) :
    ofList (l ++ List.replicate n none) = ofList l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- `ofList` recovers a stack tape from its stored list. -/
@[simp] lemma ofList_toList (tape : StackTape Symbol) : ofList tape.toList = tape := by
  rcases tape with ⟨values, h⟩
  induction values with
  | nil => rfl
  | cons a tl ih =>
    cases tl with
    | nil =>
      cases a with
      | none => exact False.elim (h rfl)
      | some s => rfl
    | cons b tl' =>
      have h' : (b :: tl').getLast? ≠ some none := by simpa using h
      have iht : ofList (b :: tl') = ⟨b :: tl', h'⟩ := ih h'
      change cons a (ofList (b :: tl')) = _
      rw [iht]
      cases a <;> rfl

/-- `ofList` of the symbols of a word wrapped in `some` is `mapSome` of the word. -/
@[simp] lemma ofList_map_some (l : List Symbol) :
    ofList (l.map some) = mapSome l := by
  exact ofList_toList (mapSome l)

lemma listBlank_mk_cons_toList (a : Option Symbol) (tape : StackTape Symbol) :
    _root_.Turing.ListBlank.mk (cons a tape).toList =
      _root_.Turing.ListBlank.cons a (_root_.Turing.ListBlank.mk tape.toList) := by
  cases a with
  | some s => simp [cons_some_toList]
  | none =>
    rcases tape with ⟨values, h⟩
    cases values with
    | nil =>
      exact Quotient.sound (Or.inl ⟨1, rfl⟩)
    | cons hd tl => rfl

/-- The stored list of `ofList l` gives the same `ListBlank` as `l`. -/
@[simp] lemma listBlank_mk_toList_ofList (l : List (Option Symbol)) :
    _root_.Turing.ListBlank.mk (ofList l).toList = _root_.Turing.ListBlank.mk l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ofList_cons, listBlank_mk_cons_toList, ih, _root_.Turing.ListBlank.cons_mk]

/-- Canonical equivalence between `StackTape Symbol` and Mathlib's
`_root_.Turing.ListBlank (Option Symbol)`. -/
def equivListBlank : StackTape Symbol ≃ _root_.Turing.ListBlank (Option Symbol) where
  toFun tape := _root_.Turing.ListBlank.mk tape.toList
  invFun lb := lb.liftOn ofList (by
    intro l₁ l₂ h
    rcases h with ⟨n, rfl⟩
    exact (ofList_append_replicate_none l₁ n).symm)
  left_inv tape := ofList_toList tape
  right_inv lb := Quotient.inductionOn lb fun l => listBlank_mk_toList_ofList l

/-- `equivListBlank` sends the empty stack tape to the blank `ListBlank`. -/
@[simp] lemma equivListBlank_nil :
    equivListBlank (nil : StackTape Symbol) = default := rfl

/-- The inverse of `equivListBlank` sends the blank `ListBlank` to the empty stack tape. -/
@[simp] lemma equivListBlank_symm_default :
    equivListBlank.symm (default : _root_.Turing.ListBlank (Option Symbol)) = nil := rfl

/-- The inverse of `equivListBlank` sends the `ListBlank` of a list `l` to `ofList l`. -/
@[simp] lemma equivListBlank_symm_mk (l : List (Option Symbol)) :
    equivListBlank.symm (_root_.Turing.ListBlank.mk l) = ofList l := rfl

/-- `equivListBlank` sends `ofList l` to the `ListBlank` of `l`. -/
@[simp] lemma equivListBlank_ofList (l : List (Option Symbol)) :
    equivListBlank (ofList l) = _root_.Turing.ListBlank.mk l :=
  listBlank_mk_toList_ofList l

/-- `equivListBlank` turns stack-tape `cons` into `ListBlank.cons`. -/
@[simp] lemma equivListBlank_cons (a : Option Symbol) (tape : StackTape Symbol) :
    equivListBlank (cons a tape) = _root_.Turing.ListBlank.cons a (equivListBlank tape) :=
  listBlank_mk_cons_toList a tape

/-- The inverse of `equivListBlank` turns `ListBlank.cons` into stack-tape `cons`. -/
@[simp] lemma equivListBlank_symm_cons (a : Option Symbol)
    (lb : _root_.Turing.ListBlank (Option Symbol)) :
    equivListBlank.symm (_root_.Turing.ListBlank.cons a lb) = cons a (equivListBlank.symm lb) := by
  apply equivListBlank.injective
  simp

/-- `equivListBlank` preserves the head. -/
@[simp] lemma head_equivListBlank (tape : StackTape Symbol) :
    (equivListBlank tape).head = tape.head := by
  rcases tape with ⟨values, h⟩
  cases values <;> rfl

/-- The inverse of `equivListBlank` preserves the head. -/
@[simp] lemma head_equivListBlank_symm (lb : _root_.Turing.ListBlank (Option Symbol)) :
    (equivListBlank.symm lb).head = lb.head := by
  rw [← head_equivListBlank (equivListBlank.symm lb), equivListBlank.apply_symm_apply]

/-- `equivListBlank` commutes with taking the tail. -/
@[simp] lemma tail_equivListBlank (tape : StackTape Symbol) :
    (equivListBlank tape).tail = equivListBlank tape.tail := by
  rcases tape with ⟨values, h⟩
  cases values <;> rfl

/-- The inverse of `equivListBlank` commutes with taking the tail. -/
@[simp] lemma tail_equivListBlank_symm (lb : _root_.Turing.ListBlank (Option Symbol)) :
    (equivListBlank.symm lb).tail = equivListBlank.symm lb.tail := by
  apply equivListBlank.injective
  rw [← tail_equivListBlank, equivListBlank.apply_symm_apply, equivListBlank.apply_symm_apply]

/-- `equivListBlank` sends `mapSome l` to the `ListBlank` of `l.map some`. -/
@[simp] lemma equivListBlank_mapSome (l : List Symbol) :
    equivListBlank (mapSome l) = _root_.Turing.ListBlank.mk (l.map some) := rfl

/-- Reading the `ListBlank` at `n` is reading the tape at `n`. -/
@[simp] lemma nth_equivListBlank (tape : StackTape Symbol) (n : ℕ) :
    (equivListBlank tape).nth n = tape.read n := by
  induction n generalizing tape with
  | zero => simp
  | succ n ih =>
    rw [_root_.Turing.ListBlank.nth_succ, tail_equivListBlank, ih, read_succ]

/-- Reading the stack tape `equivListBlank.symm lb` at `n` is reading `lb` at `n`. -/
@[simp] lemma read_equivListBlank_symm (lb : _root_.Turing.ListBlank (Option Symbol)) (n : ℕ) :
    (equivListBlank.symm lb).read n = lb.nth n := by
  rw [← nth_equivListBlank (equivListBlank.symm lb) n, equivListBlank.apply_symm_apply]

end Cslib.Turing.StackTape
