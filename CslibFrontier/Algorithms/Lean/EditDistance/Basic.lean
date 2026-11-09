/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Grid
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# Edit distance: the Wagner–Fischer algorithm

The edit distance between two words under general letter costs, computed by the dynamic program of
[Wagner and Fischer][WagnerFischer1974] (see also [CLRS, Problem 15-5][CLRS2009] and
[Kleinberg and Tardos, Section 6.6][KleinbergTardos2006]).

A cost function `C : Costs α` charges `C.del a` to delete a letter `a`, `C.ins b` to insert a
letter `b`, and `C.sub a b` to replace `a` by `b` (keeping a letter is the replacement `sub a a`,
of cost `C.sub a a`, usually `0`). An *edit script* is a list of such operations; read left to
right, it consumes its *source* word and produces its *target* word. A script is the same thing as
an alignment of the two words, or a *trace* in the terminology of Wagner and Fischer: every letter
of the source is deleted or replaced exactly once, and every letter of the target is inserted or is
the result of exactly one replacement, in order.

`Cslib.Algorithms.Lean.EditDistance.editDist C x y` is the Wagner–Fischer table entry for `x` and
`y`, and `Cslib.Algorithms.Lean.EditDistance.isLeast_editDist` proves that it is the least cost of a
script from `x` to `y`. `Cslib.Algorithms.Lean.EditDistance.optScript` reads an optimal script off
the table.

## Scope

Costs are natural numbers and arbitrary: no triangle inequality or symmetry is assumed. The
theorem is about scripts (alignments, traces). Wagner and Fischer also consider sequences of edit
operations applied one after another at arbitrary positions, and show that under their cost
conditions the least cost of such a sequence equals the least cost of a trace. That equivalence is
not formalized here.

Mathlib used to have `Levenshtein.Cost` and `levenshtein` (`Mathlib/Data/List/EditDistance`), with
the same three cost fields over separate source and target alphabets and the same recurrence, but
no characterization as a least cost over scripts. That API was removed from Mathlib in
leanprover-community/mathlib4#29196 and is absent from the pinned Mathlib, so nothing here bridges
to it.

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.Costs`: letter costs; `Costs.unit` (Levenshtein) and
  `Costs.indel` (`1` per insertion or deletion, `2` per replacement by a different letter).
* `Cslib.Algorithms.Lean.EditDistance.EditOp`, `EditScript`: edit operations and scripts, with
  `EditScript.src`, `EditScript.tgt` and `EditScript.cost`.
* `Cslib.Algorithms.Lean.EditDistance.editDist`: the Wagner–Fischer table entry.
* `Cslib.Algorithms.Lean.EditDistance.optScript`: an optimal script, by traceback.
* `Cslib.Algorithms.Lean.EditDistance.editDistM`: the algorithm in `TimeM`.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.editDist_le_cost`: every script from `x` to `y` costs at least
  `editDist C x y`.
* `Cslib.Algorithms.Lean.EditDistance.src_optScript`, `tgt_optScript`, `cost_optScript`:
  `optScript C x y` is a script from `x` to `y` of cost `editDist C x y`.
* `Cslib.Algorithms.Lean.EditDistance.isLeast_editDist`: `editDist C x y` is the least cost of a
  script from `x` to `y`.
* `Cslib.Algorithms.Lean.EditDistance.ret_editDistM`, `time_editDistM`: `editDistM` returns
  `editDist C x y` and costs exactly `(|x| + 1) (|y| + 1)`, one unit per table entry (see the cost
  model of `Cslib.Algorithms.Lean.EditDistance.GridDP.valueM`).

## References

* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [J. Kleinberg and É. Tardos, *Algorithm Design*][KleinbergTardos2006]
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

variable {α : Type*}

/-- Letter costs for edit distance: `del a` deletes `a`, `ins b` inserts `b`, and `sub a b`
replaces `a` by `b`. -/
structure Costs (α : Type*) where
  /-- The cost of deleting a letter. -/
  del : α → ℕ
  /-- The cost of inserting a letter. -/
  ins : α → ℕ
  /-- The cost of replacing the first letter by the second. -/
  sub : α → α → ℕ

namespace Costs

variable [DecidableEq α]

/-- Unit costs: every deletion, insertion and replacement by a different letter costs `1`, and
keeping a letter is free. The resulting distance is the Levenshtein distance. -/
@[expose] def unit : Costs α where
  del _ := 1
  ins _ := 1
  sub a b := if a = b then 0 else 1

/-- Insertion and deletion costs: `1` per insertion or deletion, and `2` for replacing a letter by
a different one, the cost of a deletion followed by an insertion; keeping a letter is free.
Replacements are not forbidden, and `optScript Costs.indel` may return them, but splitting each
into a deletion and an insertion keeps the cost, so the distance is the insertion–deletion distance
(`Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_indel`). -/
@[expose] def indel : Costs α where
  del _ := 1
  ins _ := 1
  sub a b := if a = b then 0 else 2

@[simp] theorem unit_del (a : α) : (unit : Costs α).del a = 1 := rfl
@[simp] theorem unit_ins (b : α) : (unit : Costs α).ins b = 1 := rfl
@[simp] theorem unit_sub (a b : α) : (unit : Costs α).sub a b = if a = b then 0 else 1 := rfl
@[simp] theorem indel_del (a : α) : (indel : Costs α).del a = 1 := rfl
@[simp] theorem indel_ins (b : α) : (indel : Costs α).ins b = 1 := rfl
@[simp] theorem indel_sub (a b : α) : (indel : Costs α).sub a b = if a = b then 0 else 2 := rfl

theorem unit_sub_self (a : α) : (unit : Costs α).sub a a = 0 := by simp [unit]
theorem indel_sub_self (a : α) : (indel : Costs α).sub a a = 0 := by simp [indel]

end Costs

/-- An edit operation: delete a letter, insert a letter, or replace a letter by a letter. -/
inductive EditOp (α : Type*) where
  /-- Delete the letter. -/
  | del (a : α)
  /-- Insert the letter. -/
  | ins (b : α)
  /-- Replace the first letter by the second. -/
  | sub (a b : α)
  deriving @[expose] DecidableEq, Repr

namespace EditOp

/-- The letters an operation consumes from the source word. -/
@[expose] def src : EditOp α → List α
  | del a => [a]
  | ins _ => []
  | sub a _ => [a]

/-- The letters an operation produces in the target word. -/
@[expose] def tgt : EditOp α → List α
  | del _ => []
  | ins b => [b]
  | sub _ b => [b]

/-- The cost of an operation. -/
@[expose] def cost (C : Costs α) : EditOp α → ℕ
  | del a => C.del a
  | ins b => C.ins b
  | sub a b => C.sub a b

end EditOp

/-- An edit script: a list of edit operations, read left to right. -/
abbrev EditScript (α : Type*) := List (EditOp α)

namespace EditScript

/-- The source word of a script: the letters it consumes, in order. -/
def src (s : EditScript α) : List α := s.flatMap EditOp.src

/-- The target word of a script: the letters it produces, in order. -/
def tgt (s : EditScript α) : List α := s.flatMap EditOp.tgt

/-- The cost of a script: the sum of the costs of its operations. -/
def cost (C : Costs α) (s : EditScript α) : ℕ := (s.map (EditOp.cost C)).sum

@[simp] theorem src_nil : src ([] : EditScript α) = [] := List.flatMap_nil
@[simp] theorem tgt_nil : tgt ([] : EditScript α) = [] := List.flatMap_nil
@[simp] theorem cost_nil (C : Costs α) : cost C ([] : EditScript α) = 0 := by
  simp only [cost, List.map_nil, List.sum_nil]

@[simp] theorem src_cons (o : EditOp α) (s : EditScript α) : src (o :: s) = o.src ++ src s :=
  List.flatMap_cons
@[simp] theorem tgt_cons (o : EditOp α) (s : EditScript α) : tgt (o :: s) = o.tgt ++ tgt s :=
  List.flatMap_cons
@[simp] theorem cost_cons (C : Costs α) (o : EditOp α) (s : EditScript α) :
    cost C (o :: s) = o.cost C + cost C s := by
  simp only [cost, List.map_cons, List.sum_cons]

theorem src_append (s t : EditScript α) : src (s ++ t) = src s ++ src t := List.flatMap_append
theorem tgt_append (s t : EditScript α) : tgt (s ++ t) = tgt s ++ tgt t := List.flatMap_append
theorem cost_append (C : Costs α) (s t : EditScript α) :
    cost C (s ++ t) = cost C s + cost C t := by
  simp only [cost, List.map_append, List.sum_append]

end EditScript

open EditScript

/-- The Wagner–Fischer table, over pairs of suffixes. -/
@[expose] def wagnerFischer (C : Costs α) : GridDP α ℕ where
  nilNil := 0
  consNil a d := C.del a + d
  nilCons b d := C.ins b + d
  consCons a b d u l := min (C.sub a b + d) (min (C.del a + u) (C.ins b + l))

/-- The edit distance from `x` to `y` under the costs `C`: the Wagner–Fischer table entry. -/
@[expose] def editDist (C : Costs α) (x y : List α) : ℕ :=
  (wagnerFischer C).value x y

/-- The Wagner–Fischer algorithm in `TimeM`, charging one unit per table entry. -/
@[expose] def editDistM (C : Costs α) (x y : List α) : TimeM ℕ ℕ :=
  (wagnerFischer C).valueM x y

variable (C : Costs α)

@[simp] theorem editDist_nil_nil : editDist C [] [] = 0 := rfl

theorem editDist_cons_nil (a : α) (x : List α) :
    editDist C (a :: x) [] = C.del a + editDist C x [] := rfl

theorem editDist_nil_cons (b : α) (y : List α) :
    editDist C [] (b :: y) = C.ins b + editDist C [] y := rfl

/-- The Wagner–Fischer recurrence. -/
theorem editDist_cons_cons (a b : α) (x y : List α) :
    editDist C (a :: x) (b :: y) =
      min (C.sub a b + editDist C x y)
        (min (C.del a + editDist C x (b :: y)) (C.ins b + editDist C (a :: x) y)) :=
  (wagnerFischer C).value_cons_cons a b x y

/-- Deleting every letter of `x`. -/
theorem editDist_nil_right (x : List α) : editDist C x [] = (x.map C.del).sum := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [editDist_cons_nil, ih, List.map_cons, List.sum_cons]

/-- Inserting every letter of `y`. -/
theorem editDist_nil_left (y : List α) : editDist C [] y = (y.map C.ins).sum := by
  induction y with
  | nil => rfl
  | cons b y ih => rw [editDist_nil_cons, ih, List.map_cons, List.sum_cons]

theorem editDist_cons_left_le (a : α) (x y : List α) :
    editDist C (a :: x) y ≤ C.del a + editDist C x y := by
  cases y with
  | nil => exact Nat.le_of_eq (editDist_cons_nil C a x)
  | cons b y => rw [editDist_cons_cons]; omega

theorem editDist_cons_right_le (b : α) (x y : List α) :
    editDist C x (b :: y) ≤ C.ins b + editDist C x y := by
  cases x with
  | nil => exact Nat.le_of_eq (editDist_nil_cons C b y)
  | cons a x => rw [editDist_cons_cons]; omega

theorem editDist_cons_cons_le (a b : α) (x y : List α) :
    editDist C (a :: x) (b :: y) ≤ C.sub a b + editDist C x y := by
  rw [editDist_cons_cons]; omega

/-- Every script from `x` to `y` costs at least `editDist C x y`. -/
theorem editDist_le_cost (s : EditScript α) : editDist C s.src s.tgt ≤ s.cost C := by
  induction s with
  | nil => exact Nat.le_refl 0
  | cons o s ih =>
    cases o with
    | del a =>
      simp only [src_cons, tgt_cons, cost_cons, EditOp.src, EditOp.tgt, EditOp.cost,
        List.singleton_append, List.nil_append]
      have := editDist_cons_left_le C a (src s) (tgt s)
      omega
    | ins b =>
      simp only [src_cons, tgt_cons, cost_cons, EditOp.src, EditOp.tgt, EditOp.cost,
        List.singleton_append, List.nil_append]
      have := editDist_cons_right_le C b (src s) (tgt s)
      omega
    | sub a b =>
      simp only [src_cons, tgt_cons, cost_cons, EditOp.src, EditOp.tgt, EditOp.cost,
        List.singleton_append]
      have := editDist_cons_cons_le C a b (src s) (tgt s)
      omega

/-- The traceback for a nonempty source and target: given the optimal scripts `d`, `u`, `l` for
`(x, y)`, `(x, b :: y)` and `(a :: x, y)`, extend the cheapest of them. Ties prefer a replacement,
then a deletion. -/
@[expose] def optScriptStep (a b : α) (dx ux lx : ℕ) (d u l : EditScript α) :
    EditScript α :=
  if C.sub a b + dx ≤ min (C.del a + ux) (C.ins b + lx) then .sub a b :: d
  else if C.del a + ux ≤ C.ins b + lx then .del a :: u
  else .ins b :: l

/-- An optimal script from `x` to `y`, read off the Wagner–Fischer table. This is a
specification for proofs and `decide`: each choice consults the entries `editDist C x' y'` directly
instead of a stored table, so it is not the linear-time traceback, which is not formalized. -/
@[expose] def optScript : List α → List α → EditScript α
  | [], y => y.map .ins
  | a :: x, y => optScriptAux a x (optScript x) y
where
  /-- The scripts from `a :: x`, given the scripts from `x`. -/
  optScriptAux (a : α) (x : List α) (f : List α → EditScript α) : List α → EditScript α
    | [] => .del a :: f []
    | b :: y =>
      optScriptStep C a b (editDist C x y) (editDist C x (b :: y)) (editDist C (a :: x) y)
        (f y) (f (b :: y)) (optScriptAux a x f y)

theorem optScript_nil (y : List α) : optScript C [] y = y.map .ins := rfl

theorem optScript_cons_nil (a : α) (x : List α) :
    optScript C (a :: x) [] = .del a :: optScript C x [] := rfl

theorem optScript_cons_cons (a b : α) (x y : List α) :
    optScript C (a :: x) (b :: y) =
      optScriptStep C a b (editDist C x y) (editDist C x (b :: y)) (editDist C (a :: x) y)
        (optScript C x y) (optScript C x (b :: y)) (optScript C (a :: x) y) := rfl

/-- `optScript C x y` is a script from `x` to `y` of cost `editDist C x y`. -/
theorem optScript_spec : ∀ x y : List α,
    (optScript C x y).src = x ∧ (optScript C x y).tgt = y ∧
      (optScript C x y).cost C = editDist C x y
  | [], y => by
    refine ⟨?_, ?_, ?_⟩
    · induction y with
      | nil => rfl
      | cons b y ih => simpa [optScript_nil, EditOp.src] using ih
    · induction y with
      | nil => rfl
      | cons b y ih => simpa [optScript_nil, EditOp.tgt] using ih
    · rw [optScript_nil, editDist_nil_left, EditScript.cost, List.map_map]
      rfl
  | a :: x, [] => by
    obtain ⟨h1, h2, h3⟩ := optScript_spec x []
    rw [optScript_cons_nil, src_cons, tgt_cons, cost_cons, h1, h2, h3, editDist_cons_nil]
    exact ⟨rfl, rfl, rfl⟩
  | a :: x, b :: y => by
    obtain ⟨d1, d2, d3⟩ := optScript_spec x y
    obtain ⟨u1, u2, u3⟩ := optScript_spec x (b :: y)
    obtain ⟨l1, l2, l3⟩ := optScript_spec (a :: x) y
    rw [optScript_cons_cons, editDist_cons_cons, optScriptStep]
    split_ifs with h h'
    · rw [src_cons, tgt_cons, cost_cons, d1, d2, d3]
      exact ⟨rfl, rfl, by simp only [EditOp.cost]; omega⟩
    · rw [src_cons, tgt_cons, cost_cons, u1, u2, u3]
      exact ⟨rfl, rfl, by simp only [EditOp.cost]; omega⟩
    · rw [src_cons, tgt_cons, cost_cons, l1, l2, l3]
      exact ⟨rfl, rfl, by simp only [EditOp.cost]; omega⟩
termination_by x y => x.length + y.length

@[simp] theorem src_optScript (x y : List α) : (optScript C x y).src = x := (optScript_spec C x y).1

@[simp] theorem tgt_optScript (x y : List α) : (optScript C x y).tgt = y :=
  (optScript_spec C x y).2.1

theorem cost_optScript (x y : List α) : (optScript C x y).cost C = editDist C x y :=
  (optScript_spec C x y).2.2

/-- **Wagner–Fischer.** The table entry `editDist C x y` is the least cost of an edit script (an
alignment, or trace) from `x` to `y`. -/
theorem isLeast_editDist (x y : List α) :
    IsLeast {c | ∃ s : EditScript α, s.src = x ∧ s.tgt = y ∧ s.cost C = c} (editDist C x y) := by
  refine ⟨⟨optScript C x y, src_optScript C x y, tgt_optScript C x y, cost_optScript C x y⟩, ?_⟩
  rintro c ⟨s, rfl, rfl, rfl⟩
  exact editDist_le_cost C s

/-- `editDistM` computes the edit distance. -/
@[simp] theorem ret_editDistM (x y : List α) : (editDistM C x y).ret = editDist C x y :=
  (wagnerFischer C).ret_valueM x y

/-- The Wagner–Fischer algorithm costs exactly `(|x| + 1) (|y| + 1)`, one unit per table entry. -/
theorem time_editDistM (x y : List α) : (editDistM C x y).time = (x.length + 1) * (y.length + 1) :=
  (wagnerFischer C).time_valueM x y

end Cslib.Algorithms.Lean.EditDistance
