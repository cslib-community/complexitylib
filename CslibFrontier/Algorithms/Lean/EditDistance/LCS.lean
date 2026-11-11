/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Basic

/-!
# Longest common subsequence

The length of a longest common subsequence of two words, computed by the dynamic program of
[CLRS, Section 15.4][CLRS2009] (the same table as [Wagner and Fischer][WagnerFischer1974], with
letter matches rewarded instead of operations charged). A subsequence is a sublist in the sense of
`List.Sublist`: a word obtained by deleting letters, not necessarily consecutive.

`Cslib.Algorithms.Lean.EditDistance.lcsLength x y` is the table entry, and
`Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength` proves that it is the greatest length of
a common subsequence; `Cslib.Algorithms.Lean.EditDistance.lcs` reads one off the table. The two
problems are dual: under `Costs.indel` (`1` per insertion or deletion, `2` per replacement by a
different letter) the edit distance is `|x| + |y| - 2 · lcsLength x y`
(`Cslib.Algorithms.Lean.EditDistance.editDist_indel_add_two_mul`). Replacements by a different
letter are allowed, and `optScript Costs.indel` may return them, but splitting each into a deletion
and an insertion keeps the cost, so this is also the least cost of a script without them
(`Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_indel`): the insertion–deletion distance.

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.lcsLength`: the table entry.
* `Cslib.Algorithms.Lean.EditDistance.lcs`: a longest common subsequence, by traceback.
* `Cslib.Algorithms.Lean.EditDistance.lcsLengthM`: the algorithm in `TimeM`.
* `Cslib.Algorithms.Lean.EditDistance.EditScript.kept`: the letters a script keeps.
* `Cslib.Algorithms.Lean.EditDistance.EditScript.IsIndel`: a script with no replacement by a
  different letter; `EditScript.splitSubs` turns a script into one.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.length_le_lcsLength`: every common subsequence has length at
  most `lcsLength x y`.
* `Cslib.Algorithms.Lean.EditDistance.lcs_spec`: `lcs x y` is a common subsequence of length
  `lcsLength x y`.
* `Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength`: `lcsLength x y` is the greatest
  length of a common subsequence.
* `Cslib.Algorithms.Lean.EditDistance.editDist_indel_add_two_mul`:
  `editDist Costs.indel x y + 2 · lcsLength x y = |x| + |y|`.
* `Cslib.Algorithms.Lean.EditDistance.isLeast_editDist_indel`: `editDist Costs.indel x y` is the
  least cost of a script from `x` to `y` with no replacement by a different letter.
* `Cslib.Algorithms.Lean.EditDistance.ret_lcsLengthM`, `time_lcsLengthM`: `lcsLengthM` returns
  `lcsLength x y` and costs exactly `(|x| + 1) (|y| + 1)`, one unit per table entry (see the cost
  model of `Cslib.Algorithms.Lean.EditDistance.GridDP.valueM`).

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [R. A. Wagner and M. J. Fischer, *The string-to-string correction problem*][WagnerFischer1974]
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

open scoped List

variable {α : Type*} [DecidableEq α]

/-- The longest-common-subsequence table, over pairs of suffixes. -/
@[expose] def lcsTable : GridDP α ℕ where
  nilNil := 0
  consNil _ d := d
  nilCons _ d := d
  consCons a b d u l := if a = b then d + 1 else max u l

/-- The length of a longest common subsequence of `x` and `y`: the table entry. -/
@[expose] def lcsLength (x y : List α) : ℕ := lcsTable.value x y

/-- The longest-common-subsequence algorithm in `TimeM`, charging one unit per table entry. -/
@[expose] def lcsLengthM (x y : List α) : TimeM ℕ ℕ := lcsTable.valueM x y

@[simp] theorem lcsLength_nil_left (y : List α) : lcsLength [] y = 0 := by
  induction y with
  | nil => rfl
  | cons b y ih => exact (lcsTable.value_nil_cons b y).trans ih

@[simp] theorem lcsLength_nil_right (x : List α) : lcsLength x [] = 0 := by
  induction x with
  | nil => rfl
  | cons a x ih => exact (lcsTable.value_cons_nil a x).trans ih

/-- The recurrence of [CLRS, Theorem 15.1][CLRS2009]. -/
theorem lcsLength_cons_cons (a b : α) (x y : List α) :
    lcsLength (a :: x) (b :: y) =
      if a = b then lcsLength x y + 1 else max (lcsLength x (b :: y)) (lcsLength (a :: x) y) :=
  lcsTable.value_cons_cons a b x y

/-- Every common subsequence of `x` and `y` has length at most `lcsLength x y`. -/
theorem length_le_lcsLength : ∀ {x y z : List α}, z <+ x → z <+ y → z.length ≤ lcsLength x y
  | [], _, z, hx, _ => by
    rw [List.sublist_nil.1 hx]
    exact Nat.zero_le _
  | _ :: _, [], z, _, hy => by
    rw [List.sublist_nil.1 hy]
    exact Nat.zero_le _
  | a :: x, b :: y, [], _, _ => Nat.zero_le _
  | a :: x, b :: y, c :: z, hx, hy => by
    rw [lcsLength_cons_cons]
    split_ifs with hab
    · subst hab
      have := length_le_lcsLength hx.of_cons_cons hy.of_cons_cons
      rw [List.length_cons]
      omega
    · by_cases hca : c = a
      · subst hca
        have := length_le_lcsLength hx (hy.of_cons_of_ne hab)
        omega
      · have := length_le_lcsLength (hx.of_cons_of_ne hca) hy
        omega
termination_by x y => x.length + y.length

/-- A longest common subsequence of `x` and `y`, read off the table. Ties prefer dropping the
first letter of `x`. This is a specification for proofs and `decide`: each choice consults the
entries `lcsLength x' y'` directly instead of a stored table, so it is not the linear-time
traceback, which is not formalized. -/
@[expose] def lcs : List α → List α → List α
  | [], _ => []
  | a :: x, y => lcsAux a x (lcs x) y
where
  /-- The longest common subsequences of `a :: x`, given those of `x`. -/
  lcsAux (a : α) (x : List α) (f : List α → List α) : List α → List α
    | [] => []
    | b :: y =>
      if a = b then a :: f y
      else if lcsLength (a :: x) y ≤ lcsLength x (b :: y) then f (b :: y)
      else lcsAux a x f y

@[simp] theorem lcs_nil_left (y : List α) : lcs [] y = [] := rfl

@[simp] theorem lcs_nil_right (x : List α) : lcs x [] = [] := by
  cases x <;> rfl

theorem lcs_cons_cons (a b : α) (x y : List α) :
    lcs (a :: x) (b :: y) =
      if a = b then a :: lcs x y
      else if lcsLength (a :: x) y ≤ lcsLength x (b :: y) then lcs x (b :: y)
      else lcs (a :: x) y := rfl

/-- `lcs x y` is a common subsequence of `x` and `y` of length `lcsLength x y`. -/
theorem lcs_spec : ∀ x y : List α,
    lcs x y <+ x ∧ lcs x y <+ y ∧ (lcs x y).length = lcsLength x y
  | [], y => ⟨List.nil_sublist _, List.nil_sublist _, (lcsLength_nil_left y).symm⟩
  | a :: x, [] => by
    rw [lcs_nil_right, lcsLength_nil_right]
    exact ⟨List.nil_sublist _, List.nil_sublist _, rfl⟩
  | a :: x, b :: y => by
    rw [lcs_cons_cons, lcsLength_cons_cons]
    split_ifs with hab h
    · subst hab
      obtain ⟨h1, h2, h3⟩ := lcs_spec x y
      exact ⟨h1.cons_cons a, h2.cons_cons a, by rw [List.length_cons, h3]⟩
    · obtain ⟨h1, h2, h3⟩ := lcs_spec x (b :: y)
      exact ⟨h1.cons a, h2, by rw [h3]; omega⟩
    · obtain ⟨h1, h2, h3⟩ := lcs_spec (a :: x) y
      exact ⟨h1, h2.cons b, by rw [h3]; omega⟩
termination_by x y => x.length + y.length

/-- `lcsLength x y` is the greatest length of a common subsequence of `x` and `y`. -/
theorem isGreatest_lcsLength (x y : List α) :
    IsGreatest {k | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = k} (lcsLength x y) := by
  refine ⟨⟨lcs x y, lcs_spec x y⟩, ?_⟩
  rintro k ⟨z, hx, hy, rfl⟩
  exact length_le_lcsLength hx hy

/-- `lcsLengthM` computes `lcsLength`. -/
@[simp] theorem ret_lcsLengthM (x y : List α) : (lcsLengthM x y).ret = lcsLength x y :=
  lcsTable.ret_valueM x y

/-- The longest-common-subsequence algorithm costs exactly `(|x| + 1) (|y| + 1)`, one unit per
table entry. -/
theorem time_lcsLengthM (x y : List α) :
    (lcsLengthM x y).time = (x.length + 1) * (y.length + 1) :=
  lcsTable.time_valueM x y

/-! ### Insertion–deletion distance -/

open EditScript

namespace EditScript

/-- The letters a script keeps: the targets of its replacements of a letter by itself. -/
def kept : EditScript α → List α
  | [] => []
  | .del _ :: s => kept s
  | .ins _ :: s => kept s
  | .sub a b :: s => if a = b then a :: kept s else kept s

theorem kept_sublist_src : ∀ s : EditScript α, s.kept <+ s.src
  | [] => by
    rw [kept, src_nil]
  | .del a :: s => by
    rw [kept, src_cons, EditOp.src, List.singleton_append]
    exact (kept_sublist_src s).cons a
  | .ins b :: s => by
    rw [kept, src_cons, EditOp.src, List.nil_append]
    exact kept_sublist_src s
  | .sub a b :: s => by
    rw [kept, src_cons]
    split_ifs
    · exact (kept_sublist_src s).cons_cons a
    · exact (kept_sublist_src s).cons a

theorem kept_sublist_tgt : ∀ s : EditScript α, s.kept <+ s.tgt
  | [] => by
    rw [kept, tgt_nil]
  | .del a :: s => by
    rw [kept, tgt_cons, EditOp.tgt, List.nil_append]
    exact kept_sublist_tgt s
  | .ins b :: s => by
    rw [kept, tgt_cons, EditOp.tgt, List.singleton_append]
    exact (kept_sublist_tgt s).cons b
  | .sub a b :: s => by
    rw [kept, tgt_cons]
    split_ifs with h
    · subst h
      exact (kept_sublist_tgt s).cons_cons a
    · exact (kept_sublist_tgt s).cons b

/-- Under `Costs.indel`, a script costs `|src| + |tgt|` less twice the number of letters it
keeps. -/
theorem cost_indel_add_two_mul : ∀ s : EditScript α,
    s.cost Costs.indel + 2 * s.kept.length = s.src.length + s.tgt.length
  | [] => by
    rw [cost_nil, kept, src_nil, tgt_nil]
    rfl
  | .del a :: s => by
    have := cost_indel_add_two_mul s
    simp only [cost_cons, kept, src_cons, tgt_cons, EditOp.cost, EditOp.src, EditOp.tgt,
      Costs.indel_del, List.length_append, List.length_singleton, List.length_nil]
    omega
  | .ins b :: s => by
    have := cost_indel_add_two_mul s
    simp only [cost_cons, kept, src_cons, tgt_cons, EditOp.cost, EditOp.src, EditOp.tgt,
      Costs.indel_ins, List.length_append, List.length_singleton, List.length_nil]
    omega
  | .sub a b :: s => by
    have := cost_indel_add_two_mul s
    simp only [cost_cons, kept, src_cons, tgt_cons, EditOp.cost, EditOp.src, EditOp.tgt,
      Costs.indel_sub, List.length_append, List.length_singleton]
    split_ifs
    · rw [List.length_cons]
      omega
    · omega

/-- A script with no replacement by a different letter: each operation is an insertion, a
deletion, or keeps a letter. -/
def IsIndel (s : EditScript α) : Prop := ∀ o ∈ s, ∀ a b, o = .sub a b → a = b

omit [DecidableEq α] in
theorem isIndel_nil : IsIndel ([] : EditScript α) := by
  intro o h
  cases h

omit [DecidableEq α] in
theorem isIndel_cons {o : EditOp α} {s : EditScript α} :
    IsIndel (o :: s) ↔ (∀ a b, o = .sub a b → a = b) ∧ IsIndel s :=
  List.forall_mem_cons

/-- Split each replacement by a different letter into a deletion followed by an insertion. -/
def splitSubs : EditScript α → EditScript α
  | [] => []
  | .del a :: s => .del a :: splitSubs s
  | .ins b :: s => .ins b :: splitSubs s
  | .sub a b :: s => if a = b then .sub a b :: splitSubs s else .del a :: .ins b :: splitSubs s

theorem src_splitSubs : ∀ s : EditScript α, (splitSubs s).src = s.src
  | [] => by rw [splitSubs]
  | .del a :: s => by simp only [splitSubs, src_cons, src_splitSubs s]
  | .ins b :: s => by simp only [splitSubs, src_cons, src_splitSubs s]
  | .sub a b :: s => by
    rw [splitSubs]
    split_ifs <;> simp only [src_cons, EditOp.src, List.nil_append, src_splitSubs s]

theorem tgt_splitSubs : ∀ s : EditScript α, (splitSubs s).tgt = s.tgt
  | [] => by rw [splitSubs]
  | .del a :: s => by simp only [splitSubs, tgt_cons, tgt_splitSubs s]
  | .ins b :: s => by simp only [splitSubs, tgt_cons, tgt_splitSubs s]
  | .sub a b :: s => by
    rw [splitSubs]
    split_ifs <;> simp only [tgt_cons, EditOp.tgt, List.nil_append, tgt_splitSubs s]

/-- Under `Costs.indel`, splitting replacements keeps the cost. -/
theorem cost_indel_splitSubs : ∀ s : EditScript α,
    (splitSubs s).cost Costs.indel = s.cost Costs.indel
  | [] => by rw [splitSubs]
  | .del a :: s => by simp only [splitSubs, cost_cons, cost_indel_splitSubs s]
  | .ins b :: s => by simp only [splitSubs, cost_cons, cost_indel_splitSubs s]
  | .sub a b :: s => by
    rw [splitSubs]
    split_ifs with h
    · simp only [cost_cons, cost_indel_splitSubs s]
    · simp only [cost_cons, EditOp.cost, Costs.indel_del, Costs.indel_ins, Costs.indel_sub, h,
        ↓reduceIte, cost_indel_splitSubs s]
      omega

theorem isIndel_splitSubs : ∀ s : EditScript α, (splitSubs s).IsIndel
  | [] => by
    rw [splitSubs]
    exact isIndel_nil
  | .del a :: s => by
    rw [splitSubs, isIndel_cons]
    exact ⟨fun _ _ h => (nomatch h), isIndel_splitSubs s⟩
  | .ins b :: s => by
    rw [splitSubs, isIndel_cons]
    exact ⟨fun _ _ h => (nomatch h), isIndel_splitSubs s⟩
  | .sub a b :: s => by
    rw [splitSubs]
    split_ifs with h
    · rw [isIndel_cons]
      refine ⟨fun _ _ h' => ?_, isIndel_splitSubs s⟩
      cases h'
      exact h
    · rw [isIndel_cons, isIndel_cons]
      exact ⟨fun _ _ h' => (nomatch h'), fun _ _ h' => (nomatch h'), isIndel_splitSubs s⟩

end EditScript

theorem editDist_indel_nil_right (x : List α) : editDist Costs.indel x [] = x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [editDist_cons_nil, ih, List.length_cons, Nat.add_comm]; rfl

theorem editDist_indel_nil_left (y : List α) : editDist Costs.indel [] y = y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => rw [editDist_nil_cons, ih, List.length_cons, Nat.add_comm]; rfl

/-- Deleting every letter of `x` and inserting every letter of `y`. -/
theorem editDist_indel_le_length_add (x y : List α) :
    editDist Costs.indel x y ≤ x.length + y.length := by
  induction x with
  | nil => exact Nat.le_of_eq (by rw [editDist_indel_nil_left, List.length_nil, Nat.zero_add])
  | cons a x ih =>
    have := editDist_cons_left_le Costs.indel a x y
    simp only [Costs.indel_del, List.length_cons] at this ⊢
    omega

/-- A common subsequence `z` of `x` and `y` gives a script keeping `z`. -/
theorem editDist_indel_add_two_mul_le : ∀ {x y z : List α}, z <+ x → z <+ y →
    editDist Costs.indel x y + 2 * z.length ≤ x.length + y.length
  | [], y, z, hx, _ => by
    rw [List.sublist_nil.1 hx, editDist_indel_nil_left]
    simp only [List.length_nil]
    omega
  | a :: x, [], z, _, hy => by
    rw [List.sublist_nil.1 hy, editDist_indel_nil_right]
    simp only [List.length_nil]
    omega
  | a :: x, b :: y, [], _, _ => by
    have := editDist_indel_le_length_add (a :: x) (b :: y)
    simp only [List.length_nil]
    omega
  | a :: x, b :: y, c :: z, hx, hy => by
    by_cases hca : c = a
    · subst hca
      by_cases hcb : c = b
      · subst hcb
        have := editDist_indel_add_two_mul_le hx.of_cons_cons hy.of_cons_cons
        have h' := editDist_cons_cons_le Costs.indel c c x y
        rw [Costs.indel_sub_self] at h'
        simp only [List.length_cons] at this ⊢
        omega
      · have := editDist_indel_add_two_mul_le hx (hy.of_cons_of_ne hcb)
        have h' := editDist_cons_right_le Costs.indel b (c :: x) y
        simp only [Costs.indel_ins, List.length_cons] at this h' ⊢
        omega
    · have := editDist_indel_add_two_mul_le (hx.of_cons_of_ne hca) hy
      have h' := editDist_cons_left_le Costs.indel a x (b :: y)
      simp only [Costs.indel_del, List.length_cons] at this h' ⊢
      omega
termination_by x y => x.length + y.length

/-- Under `Costs.indel`, the edit distance is `|x| + |y| - 2 · lcsLength x y`. By
`isLeast_editDist_indel`, it is also the least number of insertions and deletions in a script
from `x` to `y`. -/
theorem editDist_indel_add_two_mul (x y : List α) :
    editDist Costs.indel x y + 2 * lcsLength x y = x.length + y.length := by
  refine Nat.le_antisymm ?_ ?_
  · obtain ⟨h1, h2, h3⟩ := lcs_spec x y
    rw [← h3]
    exact editDist_indel_add_two_mul_le h1 h2
  · have hk := (optScript Costs.indel x y).cost_indel_add_two_mul
    have hle := length_le_lcsLength ((optScript Costs.indel x y).kept_sublist_src)
      ((optScript Costs.indel x y).kept_sublist_tgt)
    rw [src_optScript, tgt_optScript, cost_optScript] at hk
    rw [src_optScript, tgt_optScript] at hle
    omega

/-- Under `Costs.indel`, replacements by a different letter gain nothing: `editDist Costs.indel x y`
is the least cost of a script from `x` to `y` with no such replacement, that is, the least number
of insertions and deletions turning `x` into `y`. The witness splits the replacements of
`optScript Costs.indel x y`. -/
theorem isLeast_editDist_indel (x y : List α) :
    IsLeast {c | ∃ s : EditScript α, s.IsIndel ∧ s.src = x ∧ s.tgt = y ∧ s.cost Costs.indel = c}
      (editDist Costs.indel x y) := by
  refine ⟨⟨splitSubs (optScript Costs.indel x y), isIndel_splitSubs _, ?_, ?_, ?_⟩, ?_⟩
  · rw [src_splitSubs, src_optScript]
  · rw [tgt_splitSubs, tgt_optScript]
  · rw [cost_indel_splitSubs, cost_optScript]
  · rintro c ⟨s, -, rfl, rfl, rfl⟩
    exact editDist_le_cost Costs.indel s

end Cslib.Algorithms.Lean.EditDistance
