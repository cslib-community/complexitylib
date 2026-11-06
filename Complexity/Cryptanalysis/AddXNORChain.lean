/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNOR

/-!
# Forward and backward Add/XNOR chains

[WangLvShenZhang2027], Lemmas 1 and 3 (PDF pp. 6–7), Lemma 6
(PDF p. 14), and Lemma 9 (PDF p. 23). A list pairs each operator with its
operand. Evaluation is left associative; inverse evaluation reverses the steps.
All projection statements apply to arbitrary word widths and every prefix.

## Main definitions

* `eval`, `backward`, `project`: full-width chain evaluation and projection.
* `carryWord`, `accumulatedCarries`, `affine`: exact carry and affine components.
* `Solvable`: unrestricted operator-choice decision predicate.

## Main results

* `eval_project`, `backward_project`: forward and backward triangularity.
* `eval_eq_xor_parity_carries`, `solution_parity`: carry decomposition and forced parity.
* `eval_append_eq_iff`, `unique_cut`: meeting and positional representation.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

/-- Parity of the XNOR operators in a chain. -/
@[expose] def xnorParity {m : ℕ} : List (Bool × BitVec m) → Bool
  | [] => false
  | (b, _) :: xs => b ^^ xnorParity xs

/-- Evaluate a sequence of operator/operand pairs from the given initial word. -/
@[expose] def eval {m : ℕ} : List (Bool × BitVec m) → BitVec m → BitVec m
  | [], s => s
  | (b, a) :: xs, s => eval xs (step b s a)

/-- Inverse of one step, including modular subtraction for addition. -/
@[expose] def unstep {m : ℕ} (b : Bool) (t a : BitVec m) : BitVec m :=
  if b then ~~~(t ^^^ a) else t - a

/-- Complementing the state conjugates a forward step to its inverse. This
allows backward preprocessing to reuse the forward counter kernel unchanged. -/
theorem unstep_not {m : ℕ} (b : Bool) (s a : BitVec m) :
    unstep b (~~~s) a = ~~~(step b s a) := by
  cases b
  · simp only [unstep, step, Bool.false_eq_true, ↓reduceIte,
      BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg, BitVec.neg_add]
    ac_rfl
  · simp [unstep, step, BitVec.not_xor_left]

/-- Recover the initial word from a target, undoing the last step first. -/
@[expose] def backward {m : ℕ} : List (Bool × BitVec m) → BitVec m → BitVec m
  | [], t => t
  | (b, a) :: xs, t => unstep b (backward xs t) a

/-- Both operations have actual two-sided inverses. -/
theorem unstep_step {m : ℕ} (b : Bool) (s a : BitVec m) :
    unstep b (step b s a) a = s := by
  cases b <;> simp [step, unstep, BitVec.not_xor_left, BitVec.xor_assoc]

/-- Applying a step after its inverse recovers the target. -/
theorem step_unstep {m : ℕ} (b : Bool) (t a : BitVec m) :
    step b (unstep b t a) a = t := by
  cases b <;> simp [step, unstep, BitVec.not_xor_left, BitVec.xor_assoc]

/-- Reverse evaluation recovers every initial state. -/
theorem backward_eval {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    backward xs (eval xs s) = s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨b, a⟩; simp only [eval, backward, ih, unstep_step]

/-- Every target has a unique preimage under forward evaluation. -/
theorem eval_backward {m : ℕ} (xs : List (Bool × BitVec m)) (t : BitVec m) :
    eval xs (backward xs t) = t := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨b, a⟩; simp only [eval, backward, step_unstep, ih]

/-- A fixed full chain permutes the entire word space. -/
theorem eval_bijective {m : ℕ} (xs : List (Bool × BitVec m)) :
    Function.Bijective (eval xs) :=
  ⟨Function.LeftInverse.injective (backward_eval xs),
    Function.RightInverse.surjective (eval_backward xs)⟩

/-- Concatenation of steps is composition, in the order of left evaluation. -/
theorem eval_append {m : ℕ} (xs ys : List (Bool × BitVec m)) (s : BitVec m) :
    eval (xs ++ ys) s = eval ys (eval xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨b, a⟩; simp only [List.cons_append, eval, ih]

/-- Inverse evaluation is forward evaluation of reversed steps, conjugated by
complementation. This applies to operator/operand pairs together. -/
theorem backward_eq_not_eval_reverse {m : ℕ} (xs : List (Bool × BitVec m)) (t : BitVec m) :
    backward xs t = ~~~(eval xs.reverse (~~~t)) := by
  induction xs with
  | nil => simp [backward, eval]
  | cons x xs ih =>
    obtain ⟨b, a⟩ := x
    rw [backward, ih, List.reverse_cons, eval_append]
    simpa only [eval] using unstep_not b (eval xs.reverse (~~~t)) a

/-- Exact forward/backward meeting criterion at any cut. -/
theorem eval_append_eq_iff {m : ℕ} (xs ys : List (Bool × BitVec m))
    (s t : BitVec m) : eval (xs ++ ys) s = t ↔ eval xs s = backward ys t := by
  rw [eval_append]
  constructor
  · intro h
    rw [← backward_eval ys (eval xs s), h]
  · intro h
    rw [h, eval_backward]

/-- Project every operand to its low p bits, retaining all operator choices. -/
@[expose] def project {m : ℕ} (p : ℕ) (xs : List (Bool × BitVec m)) :
    List (Bool × BitVec p) := xs.map fun (b, a) => (b, a.setWidth p)

/-- Both available operations commute with every downward width projection. -/
theorem step_project {m p : ℕ} (hp : p ≤ m) (b : Bool) (s a : BitVec m) :
    (step b s a).setWidth p = step b (s.setWidth p) (a.setWidth p) := by
  cases b <;> simp [step, BitVec.setWidth_add, BitVec.setWidth_not, hp]

/-- Forward evaluation commutes with projection, including all prefixes. -/
theorem eval_project {m p : ℕ} (hp : p ≤ m) (xs : List (Bool × BitVec m))
    (s : BitVec m) : (eval xs s).setWidth p = eval (project p xs) (s.setWidth p) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    simp only [eval, ih, step_project hp, project, List.map_cons]

/-- The inverse step commutes with projection; no separate borrow hypothesis. -/
theorem unstep_project {m p : ℕ} (hp : p ≤ m) (b : Bool) (t a : BitVec m) :
    (unstep b t a).setWidth p = unstep b (t.setWidth p) (a.setWidth p) := by
  apply (show Function.Injective (fun s => step b s (a.setWidth p)) from
    fun _ _ h => by simpa only [unstep_step] using congrArg (fun s => unstep b s (a.setWidth p)) h)
  change step b _ _ = step b _ _
  rw [← step_project hp, step_unstep, step_unstep]

/-- Full backward evaluation also commutes with projection. -/
theorem backward_project {m p : ℕ} (hp : p ≤ m) (xs : List (Bool × BitVec m))
    (t : BitVec m) :
    (backward xs t).setWidth p = backward (project p xs) (t.setWidth p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    simp only [backward, unstep_project hp, ih, project, List.map_cons]

/-- A full-width solution meets every projected target. -/
theorem solution_project {m p : ℕ} (hp : p ≤ m) (xs : List (Bool × BitVec m))
    (s t : BitVec m) (h : eval xs s = t) :
    eval (project p xs) (s.setWidth p) = t.setWidth p := by
  rw [← eval_project hp, h]

/-- The carry word, characterized bitwise below by Lean's ripple-carry recurrence. -/
@[expose] def carryWord {m : ℕ} (s a : BitVec m) : BitVec m := (s + a) ^^^ s ^^^ a

/-- Every bit is the actual incoming addition carry, with bit zero false. -/
theorem carryWord_bit {m : ℕ} (s a : BitVec m) (i : ℕ) (hi : i < m) :
    (carryWord s a).getLsbD i = BitVec.carry i s a false := by
  simp only [carryWord, BitVec.getLsbD_xor, BitVec.getLsbD_add hi]
  cases s.getLsbD i <;> cases a.getLsbD i <;> cases BitVec.carry i s a false <;> rfl

/-- XOR of the carries of precisely the addition steps, using actual running states. -/
@[expose] def accumulatedCarries {m : ℕ} : List (Bool × BitVec m) → BitVec m → BitVec m
  | [], _ => 0
  | (b, a) :: xs, s =>
    (if b then 0 else carryWord s a) ^^^ accumulatedCarries xs (step b s a)

/-- Affine model obtained by replacing every addition by XOR. -/
@[expose] def affine {m : ℕ} : List (Bool × BitVec m) → BitVec m → BitVec m
  | [], s => s
  | (b, a) :: xs, s => affine xs (if b then ~~~(s ^^^ a) else s ^^^ a)

private theorem xor_right_comm {m : ℕ} (x y z : BitVec m) :
    x ^^^ y ^^^ z = x ^^^ z ^^^ y := by
  rw [BitVec.xor_assoc, BitVec.xor_comm y z, ← BitVec.xor_assoc]

private theorem affine_xor {m : ℕ} (xs : List (Bool × BitVec m)) (s d : BitVec m) :
    affine xs (s ^^^ d) = affine xs s ^^^ d := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    cases b <;> simp only [affine, Bool.false_eq_true, ↓reduceIte]
    · rw [xor_right_comm, ih]
    · rw [xor_right_comm, BitVec.not_xor_left, ih]

/-- Lemma 6: the full chain is its affine model corrected by all addition carries. -/
theorem eval_carry_decomposition {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    eval xs s = affine xs s ^^^ accumulatedCarries xs s := by
  induction xs generalizing s with
  | nil => simp [eval, affine, accumulatedCarries]
  | cons x xs ih =>
    rcases x with ⟨b, a⟩
    cases b <;>
      simp only [eval, affine, accumulatedCarries, step, Bool.false_eq_true, ↓reduceIte, ih]
    · have hs : s + a = (s ^^^ a) ^^^ carryWord s a := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [carryWord, BitVec.getLsbD_xor]
        cases s.getLsbD i <;> cases a.getLsbD i <;> cases (s + a).getLsbD i <;> rfl
      rw [hs, affine_xor, BitVec.xor_assoc]
    · simp

/-- XOR of all noninitial operands, independent of the operator choices. -/
@[expose] def operandsXor {m : ℕ} : List (Bool × BitVec m) → BitVec m
  | [] => 0
  | (_, a) :: xs => a ^^^ operandsXor xs

/-- The affine part in Lemma 6 is exactly the XOR of operands corrected by
XNOR parity, with an all-ones word for odd parity. -/
theorem affine_eq {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    affine xs s = (s ^^^ operandsXor xs) ^^^ (if xnorParity xs then ~~~0 else 0) := by
  induction xs generalizing s with
  | nil => simp [affine, operandsXor, xnorParity]
  | cons h xs ih =>
    rcases h with ⟨b, a⟩
    simp only [affine, operandsXor, xnorParity, ih]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    cases b <;> by_cases hp : xnorParity xs = true <;>
      simp only [hp, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_xor,
        BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
    all_goals
      cases s.getLsbD i <;> cases a.getLsbD i <;>
        cases (operandsXor xs).getLsbD i <;> simp_all

/-- Lemma 6 with the operand XOR and operator parity written explicitly. -/
theorem eval_eq_xor_parity_carries {m : ℕ} (xs : List (Bool × BitVec m)) (s : BitVec m) :
    eval xs s = ((s ^^^ operandsXor xs) ^^^ (if xnorParity xs then ~~~0 else 0)) ^^^
      accumulatedCarries xs s := by
  rw [eval_carry_decomposition, affine_eq]

private theorem step_bit_zero {m : ℕ} (hm : 0 < m) (b : Bool) (s a : BitVec m) :
    (step b s a).getLsbD 0 = (s.getLsbD 0 ^^ a.getLsbD 0 ^^ b) := by
  cases b <;> simp only [step, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_add hm,
    BitVec.carry_zero, BitVec.getLsbD_not, hm, decide_true, Bool.true_and, BitVec.getLsbD_xor]
  all_goals cases s.getLsbD 0 <;> cases a.getLsbD 0 <;> rfl

/-- Corollary 3: the least significant bit is exactly affine. -/
theorem eval_bit_zero {m : ℕ} (hm : 0 < m) (xs : List (Bool × BitVec m)) (s : BitVec m) :
    (eval xs s).getLsbD 0 = (s.getLsbD 0 ^^ (operandsXor xs).getLsbD 0 ^^ xnorParity xs) := by
  induction xs generalizing s with
  | nil => simp [eval, operandsXor, xnorParity]
  | cons h xs ih =>
    rcases h with ⟨b, a⟩
    simp only [eval, ih, step_bit_zero hm, operandsXor, xnorParity, BitVec.getLsbD_xor]
    cases s.getLsbD 0 <;> cases a.getLsbD 0 <;> cases b <;>
      cases (operandsXor xs).getLsbD 0 <;> cases xnorParity xs <;> rfl

/-- Every zero solution has the forced XNOR parity determined by the operands. -/
theorem solution_parity {m : ℕ} (hm : 0 < m) (xs : List (Bool × BitVec m))
    (s : BitVec m) (h : eval xs s = 0) :
    xnorParity xs = (s.getLsbD 0 ^^ (operandsXor xs).getLsbD 0) := by
  have he := eval_bit_zero hm xs s
  have hz : (0 : BitVec m).getLsbD 0 = false := by simp
  rw [h, hz] at he
  cases hs : s.getLsbD 0 <;> cases ha : (operandsXor xs).getLsbD 0 <;>
    cases hp : xnorParity xs <;> simp_all only [Bool.false_xor,
      Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_eq_true]

/-- Zero or general-target decision problem with every operator a free choice.
The initial word is separate from the list of remaining operands. -/
@[expose] def Solvable {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) : Prop :=
  ∃ bs : List Bool, bs.length = as.length ∧ eval (bs.zip as) s = t

/-- A fixed cut gives exactly one prefix/suffix representation of any operator word.
This is uniqueness in the natural positional model, not an algorithmic lower bound. -/
theorem unique_cut (bs : List Bool) (k : ℕ) (hk : k ≤ bs.length) :
    ∃! p : List Bool × List Bool, p.1.length = k ∧ p.1 ++ p.2 = bs := by
  refine ⟨(bs.take k, bs.drop k), ⟨by simp [hk], by simp⟩, ?_⟩
  rintro ⟨xs, ys⟩ ⟨hlen, hcat⟩
  apply Prod.ext
  · have h := congrArg (List.take k) hcat
    simpa [← hlen] using h
  · have h := congrArg (List.drop k) hcat
    simpa [← hlen] using h

end Cslib.Cryptanalysis.AddXNOR
