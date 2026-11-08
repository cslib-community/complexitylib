/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EditDistance.Basic

/-!
# Longest common subsequence

The length of a longest common subsequence of two words, computed by the dynamic program of
[CLRS, Section 15.4][CLRS2009] (the same table as [Wagner and Fischer][WagnerFischer1974], with
letter matches rewarded instead of operations charged). A subsequence is a sublist in the sense of
`List.Sublist`: a word obtained by deleting letters, not necessarily consecutive.

`Cslib.Algorithms.Lean.EditDistance.lcsLength x y` is the table entry, and
`Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength` proves that it is the greatest length of
a common subsequence; `Cslib.Algorithms.Lean.EditDistance.lcs` reads one off the table. The two
problems are dual: with insertions and deletions of cost `1` (`Costs.indel`), the edit distance is
`|x| + |y| - 2 · lcsLength x y` (`Cslib.Algorithms.Lean.EditDistance.dist_indel_add_two_mul`).

## Main definitions

* `Cslib.Algorithms.Lean.EditDistance.lcsLength`: the table entry.
* `Cslib.Algorithms.Lean.EditDistance.lcs`: a longest common subsequence, by traceback.
* `Cslib.Algorithms.Lean.EditDistance.lcsLengthM`: the algorithm in `TimeM`.
* `Cslib.Algorithms.Lean.EditDistance.EditScript.kept`: the letters a script keeps.

## Main results

* `Cslib.Algorithms.Lean.EditDistance.length_le_lcsLength`: every common subsequence has length at
  most `lcsLength x y`.
* `Cslib.Algorithms.Lean.EditDistance.lcs_spec`: `lcs x y` is a common subsequence of length
  `lcsLength x y`.
* `Cslib.Algorithms.Lean.EditDistance.isGreatest_lcsLength`: `lcsLength x y` is the greatest
  length of a common subsequence.
* `Cslib.Algorithms.Lean.EditDistance.dist_indel_add_two_mul`:
  `dist Costs.indel x y + 2 · lcsLength x y = |x| + |y|`.
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

omit [DecidableEq α] in
private theorem sublist_of_cons_sublist_cons_of_ne {c b : α} {z y : List α}
    (h : c :: z <+ b :: y) (hcb : c ≠ b) : c :: z <+ y := by
  rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, -⟩
  · exact h
  · exact absurd (List.cons.inj hr).1 hcb

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
        have := length_le_lcsLength hx (sublist_of_cons_sublist_cons_of_ne hy hab)
        omega
      · have := length_le_lcsLength (sublist_of_cons_sublist_cons_of_ne hx hca) hy
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

/-! ### Edit distance with insertions and deletions -/

open EditScript

namespace EditScript

/-- The letters a script keeps: the targets of its replacements of a letter by itself. -/
@[expose] def kept : EditScript α → List α
  | [] => []
  | .sub a b :: s => if a = b then a :: kept s else kept s
  | _ :: s => kept s

theorem kept_sublist_src : ∀ s : EditScript α, s.kept <+ s.src
  | [] => List.Sublist.slnil
  | .del a :: s => (kept_sublist_src s).cons a
  | .ins b :: s => kept_sublist_src s
  | .sub a b :: s => by
    rw [kept, src_cons]
    split_ifs
    · exact (kept_sublist_src s).cons_cons a
    · exact (kept_sublist_src s).cons a

theorem kept_sublist_tgt : ∀ s : EditScript α, s.kept <+ s.tgt
  | [] => List.Sublist.slnil
  | .del a :: s => kept_sublist_tgt s
  | .ins b :: s => (kept_sublist_tgt s).cons b
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
  | [] => rfl
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

end EditScript

theorem dist_indel_nil_right (x : List α) : dist Costs.indel x [] = x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [dist_cons_nil, ih, List.length_cons, Nat.add_comm]; rfl

theorem dist_indel_nil_left (y : List α) : dist Costs.indel [] y = y.length := by
  induction y with
  | nil => rfl
  | cons b y ih => rw [dist_nil_cons, ih, List.length_cons, Nat.add_comm]; rfl

/-- Deleting every letter of `x` and inserting every letter of `y`. -/
theorem dist_indel_le_length_add (x y : List α) :
    dist Costs.indel x y ≤ x.length + y.length := by
  induction x with
  | nil => exact Nat.le_of_eq (by rw [dist_indel_nil_left, List.length_nil, Nat.zero_add])
  | cons a x ih =>
    have := dist_cons_left_le Costs.indel a x y
    simp only [Costs.indel_del, List.length_cons] at this ⊢
    omega

/-- A common subsequence `z` of `x` and `y` gives a script keeping `z`. -/
theorem dist_indel_add_two_mul_le : ∀ {x y z : List α}, z <+ x → z <+ y →
    dist Costs.indel x y + 2 * z.length ≤ x.length + y.length
  | [], y, z, hx, _ => by
    rw [List.sublist_nil.1 hx, dist_indel_nil_left]
    simp only [List.length_nil]
    omega
  | a :: x, [], z, _, hy => by
    rw [List.sublist_nil.1 hy, dist_indel_nil_right]
    simp only [List.length_nil]
    omega
  | a :: x, b :: y, [], _, _ => by
    have := dist_indel_le_length_add (a :: x) (b :: y)
    simp only [List.length_nil]
    omega
  | a :: x, b :: y, c :: z, hx, hy => by
    by_cases hca : c = a
    · subst hca
      by_cases hcb : c = b
      · subst hcb
        have := dist_indel_add_two_mul_le hx.of_cons_cons hy.of_cons_cons
        have h' := dist_cons_cons_le Costs.indel c c x y
        rw [Costs.indel_sub_self] at h'
        simp only [List.length_cons] at this ⊢
        omega
      · have := dist_indel_add_two_mul_le hx (sublist_of_cons_sublist_cons_of_ne hy hcb)
        have h' := dist_cons_right_le Costs.indel b (c :: x) y
        simp only [Costs.indel_ins, List.length_cons] at this h' ⊢
        omega
    · have := dist_indel_add_two_mul_le (sublist_of_cons_sublist_cons_of_ne hx hca) hy
      have h' := dist_cons_left_le Costs.indel a x (b :: y)
      simp only [Costs.indel_del, List.length_cons] at this h' ⊢
      omega
termination_by x y => x.length + y.length

/-- With insertions and deletions of cost `1` only, the edit distance is
`|x| + |y| - 2 · lcsLength x y`. -/
theorem dist_indel_add_two_mul (x y : List α) :
    dist Costs.indel x y + 2 * lcsLength x y = x.length + y.length := by
  refine Nat.le_antisymm ?_ ?_
  · obtain ⟨h1, h2, h3⟩ := lcs_spec x y
    rw [← h3]
    exact dist_indel_add_two_mul_le h1 h2
  · have hk := (optScript Costs.indel x y).cost_indel_add_two_mul
    have hle := length_le_lcsLength ((optScript Costs.indel x y).kept_sublist_src)
      ((optScript Costs.indel x y).kept_sublist_tgt)
    rw [src_optScript, tgt_optScript, cost_optScript] at hk
    rw [src_optScript, tgt_optScript] at hle
    omega

end Cslib.Algorithms.Lean.EditDistance
