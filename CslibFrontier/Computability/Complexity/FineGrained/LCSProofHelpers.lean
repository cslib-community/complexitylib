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

end Cslib.Complexity.OV.LCS
