/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.Complexity.FineGrained.LCS

/-!
# LCS Proof Helpers
-/

public section

namespace Cslib.Complexity.OV.LCS

open Cslib.Algorithms.Lean.EditDistance
open scoped List
open LCSSymbol







theorem my_sublist_append_right {α : Type*} (A C : List α) : A <+ A ++ C := by
  induction A with
  | nil => exact List.nil_sublist _
  | cons a A ih => exact List.Sublist.cons_cons _ ih

theorem lcsLength_le_length_right {α : Type*} [DecidableEq α] (x y : List α) : lcsLength x y ≤ y.length := by
  obtain ⟨hx, hy, hlen⟩ := lcs_spec x y
  rw [← hlen]
  exact List.Sublist.length_le hy

theorem lcsLength_eq_length_of_sublist {α : Type*} [DecidableEq α] {x y : List α} (h : y <+ x) : lcsLength x y = y.length := by
  apply Nat.le_antisymm
  · exact lcsLength_le_length_right x y
  · exact length_le_lcsLength h (List.Sublist.refl y)

theorem DummyBlock_sublist_VG1' (d : Nat) (a : List Bool) : DummyBlock d <+ VG1' d a := by
  unfold DummyBlock VG1'
  have h1 : List.replicate (M d) s0 ++ List.replicate (W d) s1 <+ (List.replicate (M d) s0 ++ List.replicate (W d) s1) ++ R1 a := my_sublist_append_right _ _
  have h2 : List.replicate (M d) s2 <+ List.replicate (M d) s2 := List.Sublist.refl _
  exact List.Sublist.append h1 h2

theorem lcsLength_VG1_DummyBlock (d : Nat) (a : List Bool) :
    lcsLength (VG1' d a) (DummyBlock d) = 2 * M d + W d := by
  rw [lcsLength_eq_length_of_sublist (DummyBlock_sublist_VG1' d a)]
  unfold DummyBlock
  simp [List.length_append, List.length_replicate]
  omega




def val1 : List LCSSymbol → Bool → Nat
| [], _ => 0
| s5 :: w, _ => val1 w false
| s4 :: w, _ => 1 + val1 w true
| s6 :: w, false => 1 + val1 w false
| s6 :: w, true => val1 w false
| _ :: w, b => 1 + val1 w b

def val2 : List LCSSymbol → Bool → Nat
| [], _ => 0
| s5 :: w, _ => 1 + val2 w false
| s4 :: w, _ => val2 w true
| s6 :: w, false => val2 w false
| s6 :: w, true => 1 + val2 w false
| _ :: w, b => val2 w b

theorem val1_false_le_true_succ (w : List LCSSymbol) : val1 w false ≤ 1 + val1 w true := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons x w ih => cases x <;> (simp [val1]; try omega)

theorem val2_true_le_false_succ (w : List LCSSymbol) : val2 w true ≤ 1 + val2 w false := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons x w ih => cases x <;> (simp [val2]; try omega)

theorem val1_true_le_false (w : List LCSSymbol) : val1 w true ≤ val1 w false := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons x w ih => cases x <;> (simp [val1]; try omega)

theorem val2_false_le_true (w : List LCSSymbol) : val2 w false ≤ val2 w true := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons x w ih => cases x <;> (simp [val2]; try omega)

theorem val1_add_val2 (w : List LCSSymbol) (b : Bool) : val1 w b + val2 w b = w.length := by
  induction w generalizing b with
  | nil => rfl
  | cons x w ih => 
    cases x <;> cases b <;> simp [val1, val2]
    all_goals {
      try {
        have h1 := ih false
        have h2 := ih true
        omega
      }
    }

theorem val1_le_cons (w : List LCSSymbol) (x : LCSSymbol) (b : Bool) : val1 w b ≤ val1 (x :: w) b := by
  cases x <;> cases b <;> simp [val1]
  all_goals {
    try {
      have h1 := val1_false_le_true_succ w
      have h2 := val1_true_le_false w
      omega
    }
  }

theorem val2_le_cons (w : List LCSSymbol) (x : LCSSymbol) (b : Bool) : val2 w b ≤ val2 (x :: w) b := by
  cases x <;> cases b <;> simp [val2]
  all_goals {
    try {
      have h1 := val2_true_le_false_succ w
      have h2 := val2_false_le_true w
      omega
    }
  }

theorem sublist_val1 {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : ∀ b, val1 w1 b ≤ val1 w2 b := by
  induction h with
  | slnil => intro b; rfl
  | cons x h ih =>
    intro b
    apply Nat.le_trans (ih b)
    exact val1_le_cons _ _ _
  | cons_cons x h ih =>
    intro b
    cases x <;> cases b <;> simp [val1] <;> exact ih _

theorem sublist_val2 {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : ∀ b, val2 w1 b ≤ val2 w2 b := by
  induction h with
  | slnil => intro b; rfl
  | cons x h ih =>
    intro b
    apply Nat.le_trans (ih b)
    exact val2_le_cons _ _ _
  | cons_cons x h ih =>
    intro b
    cases x <;> cases b <;> simp [val2] <;> exact ih _





theorem val1_CG1_false (u : Bool) (w : List LCSSymbol) : val1 (CG1 u ++ w) false = 1 + val1 w false := by
  cases u <;> simp [CG1, val1]

theorem val2_CG2_false (v : Bool) (w : List LCSSymbol) : val2 (CG2 v ++ w) false = 2 + val2 w false := by
  cases v <;> simp [CG2, val2]
  all_goals { omega }

theorem val1_flatten (a : List Bool) : ∀ w, val1 ((a.map CG1).flatten ++ w) false = a.length + val1 w false := by
  induction a with
  | nil => intro w; simp [List.flatten, List.map]
  | cons u a ih =>
    intro w
    simp [List.map, List.flatten, List.append_assoc]
    rw [val1_CG1_false, ih]
    omega

theorem val1_R1_eq (a : List Bool) : val1 (R1 a) false = a.length := by
  have h := val1_flatten a []
  simp at h
  exact h

theorem val2_flatten (b : List Bool) : ∀ w, val2 ((b.map CG2).flatten ++ w) false = 2 * b.length + val2 w false := by
  induction b with
  | nil => intro w; simp [List.flatten, List.map]
  | cons v b ih =>
    intro w
    simp [List.map, List.flatten, List.append_assoc]
    rw [val2_CG2_false, ih]
    omega

theorem val2_R2_eq (b : List Bool) : val2 (R2 b) false = 2 * b.length := by
  have h := val2_flatten b []
  simp at h
  exact h


theorem lcsLength_R1_R2_le (d : Nat) (a b : List Bool) (ha : a.length = d) (hb : b.length = d) :
    lcsLength (R1 a) (R2 b) ≤ 3 * d := by
  obtain ⟨hw1, hw2, hwlen⟩ := lcs_spec (R1 a) (R2 b)
  rw [← hwlen]
  have h1 : val1 _ false ≤ val1 (R1 a) false := sublist_val1 hw1 _
  have h2 : val2 _ false ≤ val2 (R2 b) false := sublist_val2 hw2 _
  have eq1 := val1_R1_eq a
  have eq2 := val2_R2_eq b
  have h3 := val1_add_val2 (lcs (R1 a) (R2 b)) false
  omega


open LCSSymbol
open scoped List

private def count1 : List LCSSymbol → Nat
| [] => 0
| s1 :: w => 1 + count1 w
| _ :: w => count1 w

private def countR : List LCSSymbol → Nat
| [] => 0
| s4 :: w => 1 + countR w
| s5 :: w => 1 + countR w
| s6 :: w => 1 + countR w
| _ :: w => countR w

private def count0 : List LCSSymbol → Nat
| [] => 0
| s0 :: w => 1 + count0 w
| _ :: w => count0 w

private def count2 : List LCSSymbol → Nat
| [] => 0
| s2 :: w => 1 + count2 w
| _ :: w => count2 w

private def count3 : List LCSSymbol → Nat
| [] => 0
| s3 :: w => 1 + count3 w
| _ :: w => count3 w

private theorem length_eq_counts (w : List LCSSymbol) :
  w.length = count0 w + count1 w + count2 w + count3 w + countR w := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> (simp [count0, count1, count2, count3, countR, List.length]; omega)

private theorem count0_append (w1 w2 : List LCSSymbol) : count0 (w1 ++ w2) = count0 w1 + count0 w2 := by
  induction w1 with
  | nil => simp [count0]
  | cons x w1 ih => cases x <;> (simp [count0]; omega)

private theorem count2_append (w1 w2 : List LCSSymbol) : count2 (w1 ++ w2) = count2 w1 + count2 w2 := by
  induction w1 with
  | nil => simp [count2]
  | cons x w1 ih => cases x <;> (simp [count2]; omega)

private theorem count3_append (w1 w2 : List LCSSymbol) : count3 (w1 ++ w2) = count3 w1 + count3 w2 := by
  induction w1 with
  | nil => simp [count3]
  | cons x w1 ih => cases x <;> (simp [count3]; omega)

private theorem count1_append (w1 w2 : List LCSSymbol) : count1 (w1 ++ w2) = count1 w1 + count1 w2 := by
  induction w1 with
  | nil => simp [count1]
  | cons x w1 ih => cases x <;> (simp [count1]; omega)

private theorem countR_append (w1 w2 : List LCSSymbol) : countR (w1 ++ w2) = countR w1 + countR w2 := by
  induction w1 with
  | nil => simp [countR]
  | cons x w1 ih => cases x <;> (simp [countR]; omega)

private theorem count0_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : count0 w1 ≤ count0 w2 := by
  induction h with
  | slnil => rfl
  | cons x h ih => cases x <;> (simp [count0]; omega)
  | cons_cons x h ih => cases x <;> (simp [count0]; omega)

private theorem count1_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : count1 w1 ≤ count1 w2 := by
  induction h with
  | slnil => rfl
  | cons x h ih => cases x <;> (simp [count1]; omega)
  | cons_cons x h ih => cases x <;> (simp [count1]; omega)

private theorem count2_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : count2 w1 ≤ count2 w2 := by
  induction h with
  | slnil => rfl
  | cons x h ih => cases x <;> (simp [count2]; omega)
  | cons_cons x h ih => cases x <;> (simp [count2]; omega)

private theorem count3_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : count3 w1 ≤ count3 w2 := by
  induction h with
  | slnil => rfl
  | cons x h ih => cases x <;> (simp [count3]; omega)
  | cons_cons x h ih => cases x <;> (simp [count3]; omega)

private theorem countR_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : countR w1 ≤ countR w2 := by
  induction h with
  | slnil => rfl
  | cons x h ih => cases x <;> (simp [countR]; omega)
  | cons_cons x h ih => cases x <;> (simp [countR]; omega)

private def isR (x : LCSSymbol) : Bool :=
  match x with
  | LCSSymbol.s4 => true
  | LCSSymbol.s5 => true
  | LCSSymbol.s6 => true
  | _ => false

private theorem length_filter_isR (w : List LCSSymbol) : (w.filter isR).length = countR w := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> (simp [isR, countR, List.filter]; omega)

private theorem filter_isR_replicate_not_R (n : Nat) (x : LCSSymbol) (h : isR x = false) :
  (List.replicate n x).filter isR = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, List.filter, h, ih]

private theorem isR_s0 : isR LCSSymbol.s0 = false := rfl
private theorem isR_s1 : isR LCSSymbol.s1 = false := rfl
private theorem isR_s2 : isR LCSSymbol.s2 = false := rfl
private theorem isR_s3 : isR LCSSymbol.s3 = false := rfl

private theorem filter_isR_CG1 (u : Bool) : (CG1 u).filter isR = CG1 u := by cases u <;> rfl
private theorem filter_isR_CG2 (v : Bool) : (CG2 v).filter isR = CG2 v := by cases v <;> rfl

private theorem filter_isR_R1 (a : List Bool) : (R1 a).filter isR = R1 a := by
  induction a with
  | nil => rfl
  | cons u a ih =>
    have : R1 (u :: a) = CG1 u ++ R1 a := rfl
    rw [this, List.filter_append, filter_isR_CG1, ih]

private theorem filter_isR_R2 (b : List Bool) : (R2 b).filter isR = R2 b := by
  induction b with
  | nil => rfl
  | cons v b ih =>
    have : R2 (v :: b) = CG2 v ++ R2 b := rfl
    rw [this, List.filter_append, filter_isR_CG2, ih]

private theorem filter_isR_VG1 (d : Nat) (a : List Bool) : (VG1' d a).filter isR = R1 a := by
  unfold VG1'
  simp [List.filter_append, filter_isR_replicate_not_R _ _ isR_s0, filter_isR_replicate_not_R _ _ isR_s1, filter_isR_replicate_not_R _ _ isR_s2, filter_isR_R1]

private theorem filter_isR_VG2 (d : Nat) (b : List Bool) : (VG2' d b).filter isR = R2 b := by
  unfold VG2'
  simp [List.filter_append, filter_isR_replicate_not_R _ _ isR_s0, filter_isR_replicate_not_R _ _ isR_s1, filter_isR_replicate_not_R _ _ isR_s2, filter_isR_R2]

private theorem count0_replicate_s0 (n : Nat) : count0 (List.replicate n s0) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, count0, ih]; omega

private theorem count0_replicate_not_0 (n : Nat) (x : LCSSymbol) (h : x ≠ s0) : count0 (List.replicate n x) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases x <;> (try contradiction) <;> simp [List.replicate, count0, ih]

private theorem count1_replicate_s1 (n : Nat) : count1 (List.replicate n s1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, count1, ih]; omega

private theorem count1_replicate_not_1 (n : Nat) (x : LCSSymbol) (h : x ≠ s1) : count1 (List.replicate n x) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases x <;> (try contradiction) <;> simp [List.replicate, count1, ih]

private theorem count2_replicate_s2 (n : Nat) : count2 (List.replicate n s2) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, count2, ih]; omega

private theorem count2_replicate_not_2 (n : Nat) (x : LCSSymbol) (h : x ≠ s2) : count2 (List.replicate n x) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases x <;> (try contradiction) <;> simp [List.replicate, count2, ih]

private theorem count3_replicate_not_3 (n : Nat) (x : LCSSymbol) (h : x ≠ s3) : count3 (List.replicate n x) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases x <;> (try contradiction) <;> simp [List.replicate, count3, ih]

private theorem count0_CG1 (u : Bool) : count0 (CG1 u) = 0 := by cases u <;> rfl
private theorem count0_R1 (a : List Bool) : count0 (R1 a) = 0 := by
  induction a with
  | nil => rfl
  | cons u a ih =>
    have : R1 (u :: a) = CG1 u ++ R1 a := rfl
    rw [this, count0_append, count0_CG1, ih]

private theorem count2_CG1 (u : Bool) : count2 (CG1 u) = 0 := by cases u <;> rfl
private theorem count2_R1 (a : List Bool) : count2 (R1 a) = 0 := by
  induction a with
  | nil => rfl
  | cons u a ih =>
    have : R1 (u :: a) = CG1 u ++ R1 a := rfl
    rw [this, count2_append, count2_CG1, ih]

private theorem count3_CG1 (u : Bool) : count3 (CG1 u) = 0 := by cases u <;> rfl
private theorem count3_R1 (a : List Bool) : count3 (R1 a) = 0 := by
  induction a with
  | nil => rfl
  | cons u a ih =>
    have : R1 (u :: a) = CG1 u ++ R1 a := rfl
    rw [this, count3_append, count3_CG1, ih]

private theorem count1_CG2 (v : Bool) : count1 (CG2 v) = 0 := by cases v <;> rfl
private theorem count1_R2 (b : List Bool) : count1 (R2 b) = 0 := by
  induction b with
  | nil => rfl
  | cons v b ih =>
    have : R2 (v :: b) = CG2 v ++ R2 b := rfl
    rw [this, count1_append, count1_CG2, ih]

private theorem count0_VG1 (d : Nat) (a : List Bool) : count0 (VG1' d a) = M d := by
  unfold VG1'
  simp only [count0_append]
  rw [count0_replicate_s0]
  have h1 : count0 (List.replicate (W d) s1) = 0 := count0_replicate_not_0 _ _ (by decide)
  have h2 : count0 (List.replicate (M d) s2) = 0 := count0_replicate_not_0 _ _ (by decide)
  rw [h1, h2, count0_R1]
  omega

private theorem count2_VG1 (d : Nat) (a : List Bool) : count2 (VG1' d a) = M d := by
  unfold VG1'
  simp only [count2_append]
  rw [count2_replicate_s2]
  have h1 : count2 (List.replicate (M d) s0) = 0 := count2_replicate_not_2 _ _ (by decide)
  have h2 : count2 (List.replicate (W d) s1) = 0 := count2_replicate_not_2 _ _ (by decide)
  rw [h1, h2, count2_R1]
  omega

private theorem count3_VG1 (d : Nat) (a : List Bool) : count3 (VG1' d a) = 0 := by
  unfold VG1'
  simp only [count3_append]
  have h1 : count3 (List.replicate (M d) s0) = 0 := count3_replicate_not_3 _ _ (by decide)
  have h2 : count3 (List.replicate (W d) s1) = 0 := count3_replicate_not_3 _ _ (by decide)
  have h3 : count3 (List.replicate (M d) s2) = 0 := count3_replicate_not_3 _ _ (by decide)
  rw [h1, h2, h3, count3_R1]

private theorem count1_VG2 (d : Nat) (b : List Bool) : count1 (VG2' d b) = W d := by
  unfold VG2'
  simp only [count1_append]
  rw [count1_replicate_s1]
  have h1 : count1 (List.replicate (M d) s0) = 0 := count1_replicate_not_1 _ _ (by decide)
  have h2 : count1 (List.replicate (M d) s2) = 0 := count1_replicate_not_1 _ _ (by decide)
  rw [h1, h2, count1_R2]
  omega

private def All1BeforeR : List LCSSymbol → Prop
| [] => True
| s4 :: w => count1 w = 0 ∧ All1BeforeR w
| s5 :: w => count1 w = 0 ∧ All1BeforeR w
| s6 :: w => count1 w = 0 ∧ All1BeforeR w
| _ :: w => All1BeforeR w

private def AllRBefore1 : List LCSSymbol → Prop
| [] => True
| s1 :: w => countR w = 0 ∧ AllRBefore1 w
| _ :: w => AllRBefore1 w

private theorem All1BeforeR_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : All1BeforeR w2 → All1BeforeR w1 := by
  induction h with
  | slnil => intro h; exact h
  | cons x h ih =>
    intro h2
    cases x <;> (simp [All1BeforeR] at h2; try apply ih h2)
    · exact ih h2.2
    · exact ih h2.2
    · exact ih h2.2
  | cons_cons x h ih =>
    intro h2
    cases x <;> simp [All1BeforeR] at *
    · exact ih h2
    · exact ih h2
    · exact ih h2
    · exact ih h2
    · have ⟨h2a, h2b⟩ := h2
      exact ⟨by { have hc := count1_sublist h; omega }, ih h2b⟩
    · have ⟨h2a, h2b⟩ := h2
      exact ⟨by { have hc := count1_sublist h; omega }, ih h2b⟩
    · have ⟨h2a, h2b⟩ := h2
      exact ⟨by { have hc := count1_sublist h; omega }, ih h2b⟩

private theorem AllRBefore1_sublist {w1 w2 : List LCSSymbol} (h : w1 <+ w2) : AllRBefore1 w2 → AllRBefore1 w1 := by
  induction h with
  | slnil => intro h; exact h
  | cons x h ih =>
    intro h2
    cases x <;> (simp [AllRBefore1] at h2; try apply ih h2)
    · exact ih h2.2
  | cons_cons x h ih =>
    intro h2
    cases x <;> simp [AllRBefore1] at *
    · exact ih h2
    · have ⟨h2a, h2b⟩ := h2
      exact ⟨by { have hc := countR_sublist h; omega }, ih h2b⟩
    · exact ih h2
    · exact ih h2
    · exact ih h2
    · exact ih h2
    · exact ih h2

private theorem no_1_and_R_of_All (w : List LCSSymbol) :
  All1BeforeR w → AllRBefore1 w → count1 w = 0 ∨ countR w = 0 := by
  induction w with
  | nil =>
    intro _ _
    left
    rfl
  | cons x w ih =>
    intro h1 h2
    cases x
    · cases (ih h1 h2) with
      | inl h => left; assumption
      | inr h => right; assumption
    · have ⟨h2a, h2b⟩ := h2
      right
      simp [countR]
      exact h2a
    · cases (ih h1 h2) with
      | inl h => left; assumption
      | inr h => right; assumption
    · cases (ih h1 h2) with
      | inl h => left; assumption
      | inr h => right; assumption
    · have ⟨h1a, h1b⟩ := h1
      left
      simp [count1]
      exact h1a
    · have ⟨h1a, h1b⟩ := h1
      left
      simp [count1]
      exact h1a
    · have ⟨h1a, h1b⟩ := h1
      left
      simp [count1]
      exact h1a

private theorem All1BeforeR_replicate_s0_append (n : Nat) (w : List LCSSymbol) (h : All1BeforeR w) :
  All1BeforeR (List.replicate n s0 ++ w) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih

private theorem All1BeforeR_replicate_s1_append (n : Nat) (w : List LCSSymbol) (h : All1BeforeR w) :
  All1BeforeR (List.replicate n s1 ++ w) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih

private theorem All1BeforeR_replicate_s2 (n : Nat) : All1BeforeR (List.replicate n s2) := by
  induction n with
  | zero => exact True.intro
  | succ n ih => exact ih

private theorem count1_replicate_s2 (n : Nat) : count1 (List.replicate n s2) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem All1BeforeR_R1_s2 (a : List Bool) (n : Nat) :
  All1BeforeR (R1 a ++ List.replicate n s2) ∧ count1 (R1 a ++ List.replicate n s2) = 0 := by
  induction a with
  | nil =>
    exact ⟨All1BeforeR_replicate_s2 n, count1_replicate_s2 n⟩
  | cons u a ih =>
    have ⟨ih1, ih2⟩ := ih
    have : R1 (u :: a) = CG1 u ++ R1 a := by rfl
    rw [this, List.append_assoc]
    cases u <;> simp [CG1, All1BeforeR, count1, ih1, ih2]

private theorem All1BeforeR_VG1 (d : Nat) (a : List Bool) : All1BeforeR (VG1' d a) := by
  unfold VG1'
  rw [List.append_assoc, List.append_assoc]
  apply All1BeforeR_replicate_s0_append
  apply All1BeforeR_replicate_s1_append
  exact (All1BeforeR_R1_s2 a (M d)).1

private theorem AllRBefore1_replicate_s0_append (n : Nat) (w : List LCSSymbol) (h : AllRBefore1 w) :
  AllRBefore1 (List.replicate n s0 ++ w) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih

private theorem AllRBefore1_replicate_s1_s2 (n m : Nat) :
  AllRBefore1 (List.replicate n s1 ++ List.replicate m s2) ∧ countR (List.replicate n s1 ++ List.replicate m s2) = 0 := by
  induction n with
  | zero =>
    induction m with
    | zero => exact ⟨True.intro, rfl⟩
    | succ m ih => exact ih
  | succ n ih =>
    have ⟨ih1, ih2⟩ := ih
    exact ⟨⟨ih2, ih1⟩, ih2⟩

private theorem AllRBefore1_R2_s1_s2 (b : List Bool) (n m : Nat) :
  AllRBefore1 (R2 b ++ (List.replicate n s1 ++ List.replicate m s2)) := by
  induction b with
  | nil =>
    exact (AllRBefore1_replicate_s1_s2 n m).1
  | cons u b ih =>
    have : R2 (u :: b) = CG2 u ++ R2 b := by rfl
    rw [this]
    simp only [List.append_assoc]
    cases u <;> (simp [CG2, AllRBefore1]; exact ih)

private theorem AllRBefore1_VG2 (d : Nat) (b : List Bool) : AllRBefore1 (VG2' d b) := by
  unfold VG2'
  simp only [List.append_assoc]
  apply AllRBefore1_replicate_s0_append
  exact AllRBefore1_R2_s1_s2 b (W d) (M d)

private theorem w_length_bound (d : Nat) (a b : List Bool) (ha : a.length = d) (hb : b.length = d) (w : List LCSSymbol)
  (hw1 : w <+ VG1' d a) (hw2 : w <+ VG2' d b) : w.length ≤ 2 * M d + 3 * d := by
  have h1 : All1BeforeR w := All1BeforeR_sublist hw1 (All1BeforeR_VG1 d a)
  have h2 : AllRBefore1 w := AllRBefore1_sublist hw2 (AllRBefore1_VG2 d b)
  have hw_len := length_eq_counts w
  have h_count0 : count0 w ≤ count0 (VG1' d a) := count0_sublist hw1
  have h_count1 : count1 w ≤ count1 (VG2' d b) := count1_sublist hw2
  have h_count2 : count2 w ≤ count2 (VG1' d a) := count2_sublist hw1
  have h_count3 : count3 w ≤ count3 (VG1' d a) := count3_sublist hw1
  have h_countR : countR w ≤ 3 * d := by
    have hsub1 : w.filter isR <+ (VG1' d a).filter isR := List.Sublist.filter _ hw1
    have hsub2 : w.filter isR <+ (VG2' d b).filter isR := List.Sublist.filter _ hw2
    rw [filter_isR_VG1] at hsub1
    rw [filter_isR_VG2] at hsub2
    have hsub_len : (w.filter isR).length ≤ lcsLength (R1 a) (R2 b) := length_le_lcsLength hsub1 hsub2
    rw [length_filter_isR] at hsub_len
    have hR_le := lcsLength_R1_R2_le d a b ha hb
    omega
  have h_VG1_0 : count0 (VG1' d a) = M d := count0_VG1 d a
  have h_VG2_1 : count1 (VG2' d b) = W d := count1_VG2 d b
  have h_VG1_2 : count2 (VG1' d a) = M d := count2_VG1 d a
  have h_VG1_3 : count3 (VG1' d a) = 0 := count3_VG1 d a
  have h_ex := no_1_and_R_of_All w h1 h2
  cases h_ex with
  | inl h_ex1 => omega
  | inr h_exR => have hw : W d = 3 * d - 1 := rfl; omega

theorem lcsLength_VG1_VG2_le (d : Nat) (a b : List Bool) (ha : a.length = d) (hb : b.length = d) :
  lcsLength (VG1' d a) (VG2' d b) ≤ 2 * M d + 3 * d := by
  obtain ⟨hw1, hw2, hwlen⟩ := lcs_spec (VG1' d a) (VG2' d b)
  rw [← hwlen]
  apply w_length_bound d a b ha hb _ hw1 hw2

end Cslib.Complexity.OV.LCS
