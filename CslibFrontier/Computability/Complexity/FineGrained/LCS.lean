/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Complexity.FineGrained.Diameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Orthogonal vectors hardness of longest common subsequence

This module reduces the orthogonal vectors problem to the longest common subsequence problem,
following the gadget approach of Abboud, Backurs and Vassilevska Williams
[AbboudBackursVassilevskaWilliams2015]. Each vector becomes a block whose `s0` and `s2` runs of
length `LCS.M d = 10 d + 10` prevent profitable matches across blocks. The second string pads
the vector blocks of `B` with `B.length` dummy blocks on each side, separated by `s3` runs.

## Main definitions
* `Cslib.Complexity.OV.LCS.P1`, `Cslib.Complexity.OV.LCS.P2`: the two strings.
* `Cslib.Complexity.OV.toLCS`: the reduction to LCS.

## Main results
* `Cslib.Complexity.OV.LCS.lcsLength_P1_P2`: the gap characterization. For `N` vectors of
  length `d` on each side, `lcsLength (P1 d A) (P2 d B)` exceeds `LCS.BaseScore d N` if and only
  if some `a ∈ A` and `b ∈ B` are orthogonal.
* `Cslib.Complexity.OV.LCS.lcsLength_R1_R2_le_of_not_orthogonal` and
  `Cslib.Complexity.OV.LCS.three_mul_le_lcsLength_R1_R2`: the coordinate gadgets of two vectors
  of length `d` have a common subsequence of length `3 d` exactly when the vectors are orthogonal.

The upper bound charges each symbol of a common subsequence either to a block of `P1` (at most
`LCS.M d + LCS.W d` each) or to an `s0` symbol of `P2`. A counting lemma on `P2` bounds the
`s3` symbols that remain usable.

## References
* [A. Abboud, A. Backurs, V. Vassilevska Williams, *Tight Hardness Results for LCS and Other
  Sequence Similarity Measures*][AbboudBackursVassilevskaWilliams2015]
-/
public section

open scoped List

namespace Cslib.Complexity.OV

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
open Turing.MultiTapeTM

/-- The seven-letter alphabet of the reduction: `s0`, `s2` bound blocks, `s1` pads the vector
part, `s3` separates blocks and `s4`, `s5`, `s6` build the coordinate gadgets. -/
inductive LCSSymbol | s0 | s1 | s2 | s3 | s4 | s5 | s6
  deriving DecidableEq, Repr, Inhabited

open LCSSymbol

/-- The three-bit encoding of `LCSSymbol`. -/
@[expose] def encLCSSymbol : LCSSymbol ↪ List Bool :=
  ⟨fun
    | s0 => [false, false, false]
    | s1 => [false, false, true]
    | s2 => [false, true, false]
    | s3 => [false, true, true]
    | s4 => [true, false, false]
    | s5 => [true, false, true]
    | s6 => [true, true, false],
   by intro x y h; revert h; cases x <;> cases y <;> decide⟩

/-- The coordinate gadget of a bit of a vector of `A`. -/
@[expose] def LCS.CG1 (u : Bool) : List LCSSymbol := if u then [s5, s4, s5] else [s5, s4, s6, s5]
/-- The coordinate gadget of a bit of a vector of `B`. -/
@[expose] def LCS.CG2 (v : Bool) : List LCSSymbol := if v then [s5, s6, s5] else [s5, s6, s4, s5]

/-- The coordinate gadgets of a vector of `A`, concatenated. -/
@[expose] def LCS.R1 (a : List Bool) : List LCSSymbol := (a.map CG1).flatten
/-- The coordinate gadgets of a vector of `B`, concatenated. -/
@[expose] def LCS.R2 (b : List Bool) : List LCSSymbol := (b.map CG2).flatten

/-- The number `3 d - 1` of `s1` symbols padding each block: the score of a non-orthogonal
pair of coordinate gadget strings. -/
@[expose] def LCS.W (d : Nat) : Nat := 3 * d - 1

/-- The length `10 d + 10` of the `s0` and `s2` runs that bound each block. -/
@[expose] def LCS.M (d : Nat) : Nat := 10 * d + 10
/-- The length `10 d + 10` of the `s3` separators of `LCS.P2` (equal to `LCS.M d`). -/
@[expose] def LCS.sepLen (d : Nat) : Nat := 10 * d + 10

/-- The block of a vector of `A`: `s1` padding before its gadgets. -/
@[expose] def LCS.VG1' (d : Nat) (a : List Bool) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ List.replicate (W d) s1 ++ R1 a ++ List.replicate (LCS.M d) s2
/-- The block of a vector of `B`: `s1` padding after its gadgets. -/
@[expose] def LCS.VG2' (d : Nat) (b : List Bool) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ R2 b ++ List.replicate (W d) s1 ++ List.replicate (LCS.M d) s2

/-- The dummy block of `LCS.P2`: it scores `2 M + W` against every block of `LCS.P1`. -/
@[expose] def LCS.DummyBlock (d : Nat) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ List.replicate (W d) s1 ++ List.replicate (LCS.M d) s2

/-- The first string: the blocks of `A` between two long `s3` runs. -/
@[expose] def LCS.P1 (d : Nat) (A : List (List Bool)) : List LCSSymbol :=
  let L := 3 * A.length * LCS.sepLen d
  List.replicate L s3 ++ (A.map (VG1' d)).flatten ++ List.replicate L s3

/-- The `3 * B.length` blocks of `LCS.P2`: `B.length` dummy blocks on each side of the vector
gadgets of `B`. -/
@[expose] def LCS.P2Blocks (d : Nat) (B : List (List Bool)) : List (List LCSSymbol) :=
  List.replicate B.length (LCS.DummyBlock d) ++ B.map (VG2' d) ++
    List.replicate B.length (LCS.DummyBlock d)

/-- The second string: the blocks `LCS.P2Blocks d B` separated by `s3` runs. -/
@[expose] def LCS.P2 (d : Nat) (B : List (List Bool)) : List LCSSymbol :=
  List.intercalate (List.replicate (LCS.sepLen d) s3) (LCS.P2Blocks d B)

/-- The threshold of the gap theorem `LCS.lcsLength_P1_P2`. -/
@[expose] def LCS.BaseScore (d N : Nat) : Nat :=
  N * (2 * LCS.M d + 3 * d - 1) + 2 * N * LCS.sepLen d

/-- The symbols that can occur in the middle part of a block, between its `s0` run and its `s2`
run. -/
@[expose] def LCS.isMid : LCSSymbol → Bool
  | s1 | s4 | s5 | s6 => true
  | _ => false

theorem lcsLength_CG1_CG2_true_true : lcsLength (LCS.CG1 true) (LCS.CG2 true) = 2 := by decide
theorem lcsLength_CG1_CG2_true_false : lcsLength (LCS.CG1 true) (LCS.CG2 false) = 3 := by decide
theorem lcsLength_CG1_CG2_false_true : lcsLength (LCS.CG1 false) (LCS.CG2 true) = 3 := by decide
theorem lcsLength_CG1_CG2_false_false : lcsLength (LCS.CG1 false) (LCS.CG2 false) = 3 := by decide

theorem lcsLength_CG1_CG2 (u v : Bool) :
    lcsLength (LCS.CG1 u) (LCS.CG2 v) = if u ∧ v then 2 else 3 := by
  cases u <;> cases v <;> decide

/-! ### General facts about `lcsLength` -/

section General

variable {α : Type*} [DecidableEq α]

theorem lcsLength_le_length_left (x y : List α) : lcsLength x y ≤ x.length := by
  obtain ⟨hx, -, h⟩ := lcs_spec x y
  exact h ▸ hx.length_le

theorem lcsLength_le_length_right' (x y : List α) : lcsLength x y ≤ y.length := by
  obtain ⟨-, hy, h⟩ := lcs_spec x y
  exact h ▸ hy.length_le

theorem lcsLength_mono {x x' y y' : List α} (hx : x <+ x') (hy : y <+ y') :
    lcsLength x y ≤ lcsLength x' y' := by
  obtain ⟨h₁, h₂, h⟩ := lcs_spec x y
  exact h ▸ length_le_lcsLength (h₁.trans hx) (h₂.trans hy)

/-- Splitting the first argument splits the second: an optimal common subsequence of `x₁ ++ x₂`
and `y` splits into common subsequences of `x₁, y₁` and `x₂, y₂` for some `y = y₁ ++ y₂`. -/
theorem exists_lcsLength_append_le (x₁ x₂ y : List α) :
    ∃ y₁ y₂, y = y₁ ++ y₂ ∧ lcsLength (x₁ ++ x₂) y ≤ lcsLength x₁ y₁ + lcsLength x₂ y₂ := by
  obtain ⟨hx, hy, h⟩ := lcs_spec (x₁ ++ x₂) y
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := List.sublist_append_iff.mp hx
  rw [hz] at hy
  obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := List.append_sublist_iff.mp hy
  refine ⟨y₁, y₂, rfl, ?_⟩
  rw [← h, hz, List.length_append]
  exact Nat.add_le_add (length_le_lcsLength hz₁ hy₁) (length_le_lcsLength hz₂ hy₂)

theorem lcsLength_add_le_lcsLength_append (x₁ x₂ y₁ y₂ : List α) :
    lcsLength x₁ y₁ + lcsLength x₂ y₂ ≤ lcsLength (x₁ ++ x₂) (y₁ ++ y₂) := by
  obtain ⟨h₁, h₁', e₁⟩ := lcs_spec x₁ y₁
  obtain ⟨h₂, h₂', e₂⟩ := lcs_spec x₂ y₂
  rw [← e₁, ← e₂, ← List.length_append]
  exact length_le_lcsLength (h₁.append h₂) (h₁'.append h₂')

/-- Symbols that `x` lacks can be deleted from `y`. -/
theorem lcsLength_filter_right (p : α → Bool) {x : List α} (hx : ∀ c ∈ x, p c) (y : List α) :
    lcsLength x (y.filter p) = lcsLength x y := by
  refine le_antisymm (lcsLength_mono (List.Sublist.refl x) List.filter_sublist) ?_
  obtain ⟨h₁, h₂, h⟩ := lcs_spec x y
  have : (lcs x y).filter p = lcs x y := List.filter_eq_self.mpr fun c hc => hx c (h₁.subset hc)
  rw [← h]
  exact length_le_lcsLength h₁ (this ▸ h₂.filter p)

theorem lcsLength_replicate_left_le (n : ℕ) (c : α) (y : List α) :
    lcsLength (List.replicate n c) y ≤ y.count c := by
  obtain ⟨h₁, h₂, h⟩ := lcs_spec (List.replicate n c) y
  obtain ⟨k, -, hk⟩ := List.sublist_replicate_iff.mp h₁
  rw [← h, hk, List.length_replicate]
  exact List.replicate_sublist_iff.mp (hk ▸ h₂)

end General

/-! ### The non-orthogonal gadget bound -/
section RLevel

open Cslib.Algorithms.Lean.EditDistance
open LCSSymbol

/-! ### Generic sublist splitting -/

section General

variable {α : Type*}

/-- A sublist of `L ++ c :: R` either skips this `c` or matches it. -/
private theorem sublist_cons_split {w L R : List α} {c : α} (h : w <+ L ++ c :: R) :
    w <+ L ++ R ∨ ∃ P S, w = P ++ c :: S ∧ P <+ L ∧ S <+ R := by
  obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact Or.inl (h₁.append h₂)
  · exact Or.inr ⟨w₁, r, rfl, h₁, hr⟩

/-- A marked symbol of a sublist is matched to an occurrence of it. -/
private theorem sublist_mid {P Q L : List α} {c : α} (h : P ++ c :: Q <+ L) :
    ∃ L₁ L₂, L = L₁ ++ c :: L₂ ∧ P <+ L₁ ∧ Q <+ L₂ := by
  obtain ⟨r₁, r₂, rfl, hP, hc⟩ := List.append_sublist_iff.mp h
  obtain ⟨s₁, s₂, rfl, hm, hQ⟩ := List.cons_sublist_iff.mp hc
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem hm
  exact ⟨r₁ ++ t₁, t₂ ++ s₂, by simp, hP.trans (List.sublist_append_left _ _),
    hQ.trans (List.sublist_append_right _ _)⟩

/-- An occurrence of `c ≠ e` in `X ++ [e]` lies in `X`. -/
private theorem eq_append_cons_of_append_singleton {X L₁ L₂ : List α} {c e : α} (hce : c ≠ e)
    (h : X ++ [e] = L₁ ++ c :: L₂) : ∃ Z, X = L₁ ++ c :: Z ∧ L₂ = Z ++ [e] := by
  rcases List.eq_nil_or_concat L₂ with rfl | ⟨Z, z, rfl⟩
  · have := (List.append_inj' h rfl).2
    simp only [List.cons.injEq, and_true] at this
    exact absurd this.symm hce
  · have h' : X ++ [e] = (L₁ ++ c :: Z) ++ [z] := by rw [h]; simp
    obtain ⟨h₁, h₂⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h₂
    subst h₂
    exact ⟨Z, h₁, by simp⟩

end General

/-! ### Potentials -/

private def val1 : List LCSSymbol → Bool → ℕ
  | [], _ => 0
  | s5 :: w, _ => val1 w false
  | s4 :: w, _ => 1 + val1 w true
  | s6 :: w, false => 1 + val1 w false
  | s6 :: w, true => val1 w false
  | _ :: w, b => 1 + val1 w b

private def val2 : List LCSSymbol → Bool → ℕ
  | [], _ => 0
  | s5 :: w, _ => 1 + val2 w false
  | s4 :: w, _ => val2 w true
  | s6 :: w, false => val2 w false
  | s6 :: w, true => 1 + val2 w false
  | _ :: w, b => val2 w b

private theorem val1_false_le_true_succ (w : List LCSSymbol) : val1 w false ≤ 1 + val1 w true := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons x w ih => cases x <;> (simp [val1]; try omega)

private theorem val2_true_le_false_succ (w : List LCSSymbol) : val2 w true ≤ 1 + val2 w false := by
  induction w with
  | nil => exact Nat.zero_le _
  | cons x w ih => cases x <;> (simp [val2]; try omega)

private theorem val1_true_le_false (w : List LCSSymbol) : val1 w true ≤ val1 w false := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons x w ih => cases x <;> (simp [val1]; try omega)

private theorem val2_false_le_true (w : List LCSSymbol) : val2 w false ≤ val2 w true := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons x w ih => cases x <;> (simp [val2]; try omega)

private theorem val1_add_val2 (w : List LCSSymbol) (b : Bool) :
    val1 w b + val2 w b = w.length := by
  induction w generalizing b with
  | nil => rfl
  | cons x w ih =>
    have h1 := ih false
    have h2 := ih true
    cases x <;> cases b <;> simp [val1, val2] <;> omega

private theorem val1_le_cons (w : List LCSSymbol) (x : LCSSymbol) (b : Bool) :
    val1 w b ≤ val1 (x :: w) b := by
  have h1 := val1_false_le_true_succ w
  have h2 := val1_true_le_false w
  cases x <;> cases b <;> simp [val1] <;> omega

private theorem val2_le_cons (w : List LCSSymbol) (x : LCSSymbol) (b : Bool) :
    val2 w b ≤ val2 (x :: w) b := by
  have h1 := val2_true_le_false_succ w
  have h2 := val2_false_le_true w
  cases x <;> cases b <;> simp [val2] <;> omega

private theorem sublist_val1 {w₁ w₂ : List LCSSymbol} (h : w₁ <+ w₂) :
    ∀ b, val1 w₁ b ≤ val1 w₂ b := by
  induction h with
  | slnil => intro b; rfl
  | cons x h ih => exact fun b => (ih b).trans (val1_le_cons _ _ _)
  | cons_cons x h ih =>
    intro b
    cases x <;> cases b <;> simp only [val1, add_le_add_iff_left] <;> exact ih _

private theorem sublist_val2 {w₁ w₂ : List LCSSymbol} (h : w₁ <+ w₂) :
    ∀ b, val2 w₁ b ≤ val2 w₂ b := by
  induction h with
  | slnil => intro b; rfl
  | cons x h ih => exact fun b => (ih b).trans (val2_le_cons _ _ _)
  | cons_cons x h ih =>
    intro b
    cases x <;> cases b <;> simp only [val2, add_le_add_iff_left] <;> exact ih _

/-- An `s5` resets the state of `val1` and contributes nothing. -/
private theorem val1_append_s5 (u v : List LCSSymbol) (s : Bool) :
    val1 (u ++ s5 :: v) s = val1 u s + val1 v false := by
  induction u generalizing s with
  | nil => simp [val1]
  | cons x u ih => cases x <;> cases s <;> simp [val1, ih] <;> omega

/-- The common bound: a common subsequence of `x` and `y` is bounded by the potentials. -/
private theorem length_le_val {w x y : List LCSSymbol} (hx : w <+ x) (hy : w <+ y) :
    w.length ≤ val1 x false + val2 y false := by
  have := val1_add_val2 w false
  have := sublist_val1 hx false
  have := sublist_val2 hy false
  omega

/-! ### Gadget strings -/

private theorem R1_cons (u : Bool) (a : List Bool) : LCS.R1 (u :: a) = LCS.CG1 u ++ LCS.R1 a := by
  simp [LCS.R1]

private theorem R2_cons (v : Bool) (b : List Bool) : LCS.R2 (v :: b) = LCS.CG2 v ++ LCS.R2 b := by
  simp [LCS.R2]

private theorem R1_append (a a' : List Bool) : LCS.R1 (a ++ a') = LCS.R1 a ++ LCS.R1 a' := by
  simp [LCS.R1]

private theorem R2_append (b b' : List Bool) : LCS.R2 (b ++ b') = LCS.R2 b ++ LCS.R2 b' := by
  simp [LCS.R2]

private theorem val1_R1 (a : List Bool) : val1 (LCS.R1 a) false = a.length := by
  induction a with
  | nil => simp [LCS.R1, val1]
  | cons u a ih =>
    rw [R1_cons]
    cases u <;> simp [LCS.CG1, val1, ih] <;> omega

private theorem val2_R2 (b : List Bool) : val2 (LCS.R2 b) false = 2 * b.length := by
  induction b with
  | nil => simp [LCS.R2, val2]
  | cons v b ih =>
    rw [R2_cons]
    cases v <;> simp [LCS.CG2, val2, ih] <;> omega

private theorem val2_CG2_append (v : Bool) (w : List LCSSymbol) :
    val2 (LCS.CG2 v ++ w) false = 2 + val2 w false := by
  cases v <;> simp [LCS.CG2, val2] <;> omega

/-- The swap `s4 ↔ s6`, which exchanges `R1` and `R2`. -/
private def swap46 : LCSSymbol → LCSSymbol
  | s0 => s0
  | s1 => s1
  | s2 => s2
  | s3 => s3
  | s4 => s6
  | s5 => s5
  | s6 => s4

private theorem map_swap46_R1 (a : List Bool) : (LCS.R1 a).map swap46 = LCS.R2 a := by
  induction a with
  | nil => simp [LCS.R1, LCS.R2]
  | cons u a ih =>
    rw [R1_cons, R2_cons, List.map_append, ih]
    cases u <;> simp [LCS.CG1, LCS.CG2, swap46]

private theorem map_swap46_R2 (b : List Bool) : (LCS.R2 b).map swap46 = LCS.R1 b := by
  induction b with
  | nil => simp [LCS.R1, LCS.R2]
  | cons v b ih =>
    rw [R1_cons, R2_cons, List.map_append, ih]
    cases v <;> simp [LCS.CG1, LCS.CG2, swap46]

private theorem R2_ne_s4_cons (b : List Bool) (Z : List LCSSymbol) : LCS.R2 b ≠ s4 :: Z := by
  cases b with
  | nil => simp [LCS.R2]
  | cons v b => rw [R2_cons]; cases v <;> simp [LCS.CG2]

/-- An `s4` of `R2 b` sits in the gadget of a `false` coordinate, which bounds the two potentials
around it. -/
private theorem val_around_s4_le {b : List Bool} :
    ∀ {Z₁ Z₂ : List LCSSymbol}, LCS.R2 b = Z₁ ++ s4 :: Z₂ →
      val2 (Z₁ ++ [s4]) false + val1 (Z₂.map swap46) false + 1 ≤ 2 * b.length := by
  induction b with
  | nil => intro Z₁ Z₂ h; simp [LCS.R2] at h
  | cons v b ih =>
    intro Z₁ Z₂ h
    rw [R2_cons] at h
    rcases List.append_eq_append_iff.mp h with ⟨as, rfl, h'⟩ | ⟨bs, hc, h'⟩
    · have := ih h'
      rw [List.append_assoc, val2_CG2_append, List.length_cons]
      omega
    · cases bs with
      | nil =>
        rw [List.nil_append] at h'
        exact (R2_ne_s4_cons b Z₂ h'.symm).elim
      | cons y bs =>
        simp only [List.cons_append, List.cons.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        cases v
        · rcases Z₁ with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, Z₁⟩⟩⟩⟩ <;>
            simp only [LCS.CG2, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
              List.cons.injEq, List.nil_eq, List.append_eq_nil_iff, reduceCtorEq, false_and,
              and_false, true_and] at hc
          obtain ⟨h₁, h₂, h₃⟩ := hc
          subst h₁ h₂ h₃
          simp [val1, val2, swap46, map_swap46_R2, val1_R1]
          omega
        · have : s4 ∈ LCS.CG2 true := by rw [hc]; simp
          simp [LCS.CG2] at this

/-! ### The three cases at a common `true` coordinate -/

/-- The `s4` of the gadget of `a` is skipped. -/
private theorem length_le_of_skip {x₁ x₂ y : List Bool} {w : List LCSSymbol}
    (hx : w <+ LCS.R1 x₁ ++ s5 :: s5 :: LCS.R1 x₂) (hy : w <+ LCS.R2 y) :
    w.length ≤ x₁.length + x₂.length + 2 * y.length := by
  have := length_le_val hx hy
  rw [val1_append_s5, val2_R2] at this
  simp only [val1, val1_R1] at this
  omega

/-- Both marked symbols are used, the `s4` of the gadget of `a` first. -/
private theorem length_le_of_cross {a₁ a₂ b₁ b₂ : List Bool} {P Q S : List LCSSymbol}
    (hX1 : P <+ LCS.R1 a₁ ++ [s5]) (hX2 : Q ++ s6 :: S <+ s5 :: LCS.R1 a₂)
    (hY1 : P ++ s4 :: Q <+ LCS.R2 b₁ ++ [s5]) (hY2 : S <+ s5 :: LCS.R2 b₂) :
    (P ++ s4 :: (Q ++ s6 :: S)).length ≤
      a₁.length + 2 * b₁.length + 2 * a₂.length + b₂.length + 2 := by
  obtain ⟨L₁, L₂, hL, hPL, hQL⟩ := sublist_mid hY1
  obtain ⟨Z₂, hR, rfl⟩ := eq_append_cons_of_append_singleton (by decide : s4 ≠ s5) hL
  have hgl := val_around_s4_le hR
  have h1 := length_le_val (w := P ++ [s4]) (x := LCS.R1 a₁ ++ s5 :: [s4]) (y := L₁ ++ [s4])
    (by simpa using hX1.append (List.Sublist.refl [s4])) (hPL.append (List.Sublist.refl [s4]))
  rw [val1_append_s5, val1_R1] at h1
  simp only [val1] at h1
  have hT : (Q ++ s6 :: S).map swap46 <+ Z₂.map swap46 ++ s5 :: s4 :: s5 :: LCS.R1 b₂ := by
    simpa [map_swap46_R2, swap46] using (hQL.append (hY2.cons_cons s6)).map swap46
  have hT' : (Q ++ s6 :: S).map swap46 <+ s5 :: LCS.R2 a₂ := by
    simpa [map_swap46_R1, swap46] using hX2.map swap46
  have h2 := length_le_val hT hT'
  rw [val1_append_s5] at h2
  simp only [val1, val2, val1_R1, val2_R2, List.length_map] at h2
  simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
  omega

private theorem length_le_of_true_true {a₁ a₂ b₁ b₂ : List Bool}
    (hk : a₁.length = b₁.length) (hr : a₂.length = b₂.length) {w : List LCSSymbol}
    (hX : w <+ LCS.R1 (a₁ ++ true :: a₂)) (hY : w <+ LCS.R2 (b₁ ++ true :: b₂)) :
    w.length ≤ 3 * (a₁.length + a₂.length) + 2 := by
  have eX : LCS.R1 (a₁ ++ true :: a₂) = (LCS.R1 a₁ ++ [s5]) ++ s4 :: (s5 :: LCS.R1 a₂) := by
    simp [R1_append, R1_cons, LCS.CG1]
  have eY : LCS.R2 (b₁ ++ true :: b₂) = (LCS.R2 b₁ ++ [s5]) ++ s6 :: (s5 :: LCS.R2 b₂) := by
    simp [R2_append, R2_cons, LCS.CG2]
  have hXσ := hX.map swap46
  rw [map_swap46_R1] at hXσ
  have hX' : w <+ (LCS.R1 a₁ ++ [s5]) ++ s4 :: (s5 :: LCS.R1 a₂) := eX ▸ hX
  have hY' : w <+ (LCS.R2 b₁ ++ [s5]) ++ s6 :: (s5 :: LCS.R2 b₂) := eY ▸ hY
  rcases sublist_cons_split hX' with hA | ⟨P₀, S₀, rfl, hP₀, hS₀⟩
  · have := length_le_of_skip (by simpa using hA) hY
    simp only [List.length_append, List.length_cons] at this
    omega
  rcases sublist_cons_split hY' with hB | ⟨P₁, S₁, e, hP₁, hS₁⟩
  · have := length_le_of_skip (by simpa [map_swap46_R2, swap46] using hB.map swap46) hXσ
    simp only [List.length_map, List.length_append, List.length_cons] at this ⊢
    omega
  rcases List.append_eq_append_iff.mp e with ⟨as, rfl, h'⟩ | ⟨bs, rfl, h'⟩
  · cases as with
    | nil => simp at h'
    | cons y Q =>
      simp only [List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have := length_le_of_cross hP₀ hS₀ hP₁ hS₁
      simp only [List.length_append, List.length_cons] at this ⊢
      omega
  · cases bs with
    | nil => simp at h'
    | cons y Q =>
      simp only [List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      have := length_le_of_cross (a₁ := b₁) (a₂ := b₂) (b₁ := a₁) (b₂ := a₂)
        (P := P₁.map swap46) (Q := Q.map swap46) (S := S₀.map swap46)
        (by simpa [map_swap46_R2, swap46] using hP₁.map swap46)
        (by simpa [map_swap46_R2, swap46] using hS₁.map swap46)
        (by simpa [map_swap46_R1, swap46] using hP₀.map swap46)
        (by simpa [map_swap46_R1, swap46] using hS₀.map swap46)
      simp only [List.length_map, List.length_append, List.length_cons] at this ⊢
      omega

/-- A `true` coordinate of a list splits it. -/
private theorem exists_split_of_getD {l : List Bool} {i : ℕ} (h : l.getD i false = true) :
    l = l.take i ++ true :: l.drop (i + 1) ∧ i < l.length := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hx : l[i]? with
  | none => simp [hx] at h
  | some x =>
    simp only [hx, Option.getD_some] at h
    subst h
    obtain ⟨hi, hli⟩ := List.getElem?_eq_some_iff.mp hx
    refine ⟨?_, hi⟩
    conv_lhs => rw [← List.take_append_drop i l]
    rw [← List.getElem_cons_drop hi, hli]

/-- **Non-orthogonal coordinate gadgets.** If `a` and `b` have length `d` and are not orthogonal,
then `LCS.R1 a` and `LCS.R2 b` have no common subsequence of length `3 * d`. -/
theorem LCS.lcsLength_R1_R2_le_of_not_orthogonal {d : ℕ} {a b : List Bool}
    (ha : a.length = d) (hb : b.length = d) (h : ¬Orthogonal a b) :
    lcsLength (LCS.R1 a) (LCS.R2 b) ≤ 3 * d - 1 := by
  simp only [Orthogonal, not_forall, not_or, Bool.not_eq_false] at h
  obtain ⟨i, hai, hbi⟩ := h
  obtain ⟨ea, hia⟩ := exists_split_of_getD hai
  obtain ⟨eb, hib⟩ := exists_split_of_getD hbi
  obtain ⟨hw₁, hw₂, hlen⟩ := lcs_spec (LCS.R1 a) (LCS.R2 b)
  generalize lcs (LCS.R1 a) (LCS.R2 b) = w at hw₁ hw₂ hlen
  rw [← hlen]
  rw [ea] at hw₁
  rw [eb] at hw₂
  have := length_le_of_true_true (by simp; omega) (by simp; omega) hw₁ hw₂
  simp only [List.length_take, List.length_drop] at this
  omega

end RLevel

/-! ### Blocks of `P2` -/

section Mid

open Cslib.Algorithms.Lean.EditDistance
open LCSSymbol

/-- A common subsequence of `x₁ ++ x₂` and `y₁ ++ y₂` either avoids the symbol `c`, and then
lies in `x₂` and `y₁`, or starts with `c`, and then lies in `x₁` and `y₂`. -/
theorem lcsLength_append_le_max {α : Type*} [DecidableEq α] {c : α} {x₁ x₂ y₁ y₂ : List α}
    (hx₁ : ∀ x ∈ x₁, x = c) (hx₂ : c ∉ x₂) (hy₁ : c ∉ y₁) (hy₂ : ∀ y ∈ y₂, y = c) :
    lcsLength (x₁ ++ x₂) (y₁ ++ y₂) ≤ max (lcsLength x₁ y₂) (lcsLength x₂ y₁) := by
  obtain ⟨hx, hy, h⟩ := lcs_spec (x₁ ++ x₂) (y₁ ++ y₂)
  rw [← h]
  obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := List.sublist_append_iff.mp hx
  obtain ⟨w₁, w₂, hw, hw₁, hw₂⟩ := List.sublist_append_iff.mp hy
  have hnil : ∀ {l : List α}, (∀ x ∈ l, x = c) → c ∉ l → l = [] := fun h₁ h₂ =>
    List.eq_nil_iff_forall_not_mem.mpr fun x hx => h₂ (h₁ x hx ▸ hx)
  rcases List.append_eq_append_iff.mp (hz.symm.trans hw) with ⟨as, rfl, h₂⟩ | ⟨bs, rfl, h₂⟩
  · have e₁ : z₁ = [] := hnil (fun x hx => hx₁ x (hz₁.subset hx))
      (fun h => hy₁ (hw₁.subset (List.mem_append_left _ h)))
    have e₂ : w₂ = [] := hnil (fun y hy => hy₂ y (hw₂.subset hy))
      (fun h => hx₂ (hz₂.subset (by rw [h₂]; exact List.mem_append_right _ h)))
    have hs : z₂ <+ y₁ := by
      rw [h₂, e₂, List.append_nil]
      simpa [e₁] using hw₁
    rw [hz, e₁, List.nil_append]
    exact le_max_of_le_right (length_le_lcsLength hz₂ hs)
  · have e₁ : w₁ = [] := hnil (fun x hx => hx₁ x (hz₁.subset (List.mem_append_left _ hx)))
      (fun h => hy₁ (hw₁.subset h))
    have e₂ : z₂ = [] := hnil
      (fun x hx => hy₂ x (hw₂.subset (by rw [h₂]; exact List.mem_append_right _ hx)))
      (fun h => hx₂ (hz₂.subset h))
    rw [h₂, e₂, List.append_nil] at hw₂
    rw [hz, e₂, List.append_nil]
    refine le_max_of_le_left (length_le_lcsLength hz₁ ?_)
    rwa [e₁, List.nil_append]

/-- The middle parts of the vector gadgets match either their `s1` runs or their coordinate
gadgets, not both. -/
theorem LCS.lcsLength_mid_le_max (d : ℕ) (a b : List Bool) :
    lcsLength (List.replicate (LCS.W d) s1 ++ LCS.R1 a) (LCS.R2 b ++ List.replicate (LCS.W d) s1)
      ≤ max (LCS.W d) (lcsLength (LCS.R1 a) (LCS.R2 b)) := by
  have hR1 : s1 ∉ LCS.R1 a := by
    simp only [LCS.R1, List.mem_flatten, List.mem_map, not_exists, not_and]
    rintro _ ⟨v, -, rfl⟩
    cases v <;> simp [LCS.CG1]
  have hR2 : s1 ∉ LCS.R2 b := by
    simp only [LCS.R2, List.mem_flatten, List.mem_map, not_exists, not_and]
    rintro _ ⟨v, -, rfl⟩
    cases v <;> simp [LCS.CG2]
  refine (lcsLength_append_le_max (c := s1) (fun x hx => List.eq_of_mem_replicate hx) hR1 hR2
    (fun y hy => List.eq_of_mem_replicate hy)).trans (max_le_max ?_ le_rfl)
  simpa using lcsLength_le_length_left (List.replicate (LCS.W d) s1)
    (List.replicate (LCS.W d) s1)

end Mid

theorem LCS.lcsLength_mid_le {d : ℕ} {a b : List Bool} (ha : a.length = d) (hb : b.length = d)
    (h : ¬ Orthogonal a b) :
    lcsLength (List.replicate (LCS.W d) s1 ++ LCS.R1 a) (LCS.R2 b ++ List.replicate (LCS.W d) s1)
      ≤ LCS.W d :=
  (LCS.lcsLength_mid_le_max d a b).trans
    (max_le le_rfl (LCS.lcsLength_R1_R2_le_of_not_orthogonal ha hb h))

section P2Structure

open LCSSymbol

/-- A prefix of `A ++ B` is a prefix of `A` or extends `A` by a prefix of `B`. -/
private theorem prefix_append_cases {α : Type*} {p A B : List α} (h : p <+: A ++ B) :
    p <+: A ∨ ∃ t, p = A ++ t ∧ t <+: B := by
  obtain ⟨u, hu⟩ := h
  rcases List.append_eq_append_iff.mp hu with ⟨a, hA, -⟩ | ⟨c, hp, hB⟩
  · exact Or.inl ⟨a, hA.symm⟩
  · exact Or.inr ⟨c, hp, u, hB.symm⟩

/-- Prepending the separator to an intercalation puts a separator before every block. -/
private theorem append_intercalate_cons {α : Type*} (sep G : List α) (Gs : List (List α)) :
    sep ++ sep.intercalate (G :: Gs) = ((G :: Gs).map (sep ++ ·)).flatten := by
  induction Gs generalizing G with
  | nil => simp [List.intercalate_singleton]
  | cons G' Gs ih =>
    rw [List.intercalate_cons_cons, List.map_cons, List.flatten_cons, ← ih]
    simp

/-- The shape of the blocks of `LCS.P2`: an `s0` run of length `k`, then no `s0` or `s3`. -/
private abbrev BlockShape (k : ℕ) (G : List LCSSymbol) : Prop :=
  ∃ g, G = List.replicate k s0 ++ g ∧ s0 ∉ g ∧ s3 ∉ g

private theorem count_prefix_units {k : ℕ} {Gs : List (List LCSSymbol)}
    (hGs : ∀ G ∈ Gs, BlockShape k G) {q : List LCSSymbol}
    (hq : q <+: (Gs.map (List.replicate k s3 ++ ·)).flatten) :
    q.count s0 ≤ q.count s3 ∧ q.count s3 ≤ q.count s0 + k := by
  induction Gs generalizing q with
  | nil =>
    obtain rfl : q = [] := by simpa using hq
    simp
  | cons G Gs ih =>
    obtain ⟨g, rfl, hg0, hg3⟩ := hGs G (by simp)
    have hq' : q <+: List.replicate k s3 ++
        ((List.replicate k s0 ++ g) ++ (Gs.map (List.replicate k s3 ++ ·)).flatten) := by
      simpa using hq
    rcases prefix_append_cases hq' with h | ⟨t, rfl, ht⟩
    · have h0 := h.count_le s0
      have h3 := h.count_le s3
      simp [List.count_replicate] at h0 h3
      omega
    · rcases prefix_append_cases ht with h | ⟨t', rfl, ht'⟩
      · have h0 := h.count_le s0
        have h3 := h.count_le s3
        simp [List.count_replicate, List.count_eq_zero.mpr hg0, List.count_eq_zero.mpr hg3]
          at h0 h3
        simp [List.count_replicate]
        omega
      · have := ih (fun G hG => hGs G (by simp [hG])) ht'
        simp [List.count_replicate, List.count_eq_zero.mpr hg0, List.count_eq_zero.mpr hg3]
        omega

private theorem count_s3_units {k : ℕ} {Gs : List (List LCSSymbol)}
    (hGs : ∀ G ∈ Gs, BlockShape k G) :
    ((Gs.map (List.replicate k s3 ++ ·)).flatten).count s3 = Gs.length * k := by
  induction Gs with
  | nil => simp
  | cons G Gs ih =>
    obtain ⟨g, rfl, -, hg3⟩ := hGs G (by simp)
    simp [List.count_replicate, List.count_eq_zero.mpr hg3, ih (fun G hG => hGs G (by simp [hG]))]
    ring

private theorem count_balance_intercalate {k : ℕ} {Gs : List (List LCSSymbol)}
    (hGs : ∀ G ∈ Gs, BlockShape k G) {T₀ T T₁ : List LCSSymbol}
    (h : (List.replicate k s3).intercalate Gs = T₀ ++ T ++ T₁) :
    T₀.count s3 + T.count s0 + T₁.count s3 ≤ Gs.length * k := by
  cases Gs with
  | nil =>
    obtain ⟨rfl, rfl, rfl⟩ : T₀ = [] ∧ T = [] ∧ T₁ = [] := by simpa [eq_comm] using h
    simp
  | cons G Gs =>
    have hU := append_intercalate_cons (List.replicate k s3) G Gs
    rw [h] at hU
    have c1 := count_prefix_units hGs (q := List.replicate k s3 ++ T₀)
      ⟨T ++ T₁, by rw [← hU]; simp⟩
    have c2 := count_prefix_units hGs (q := List.replicate k s3 ++ T₀ ++ T)
      ⟨T₁, by rw [← hU]; simp⟩
    have tot := count_s3_units hGs
    rw [← hU] at tot
    generalize (G :: Gs).length * k = n at tot ⊢
    simp [List.count_replicate] at c1 c2 tot
    omega

private theorem prefix_units_filter_isMid {k : ℕ} {Gs : List (List LCSSymbol)}
    (hGs : ∀ G ∈ Gs, BlockShape k G) {q : List LCSSymbol}
    (hq : q <+: (Gs.map (List.replicate k s3 ++ ·)).flatten) :
    q.filter LCS.isMid = [] ∨ k ≤ q.count s0 := by
  cases Gs with
  | nil =>
    obtain rfl : q = [] := by simpa using hq
    simp
  | cons G Gs =>
    obtain ⟨g, rfl, -, -⟩ := hGs G (by simp)
    have hq' : q <+: (List.replicate k s3 ++ List.replicate k s0) ++
        (g ++ (Gs.map (List.replicate k s3 ++ ·)).flatten) := by
      simpa using hq
    rcases prefix_append_cases hq' with h | ⟨t, rfl, -⟩
    · left
      simpa [LCS.isMid] using h.sublist.filter LCS.isMid
    · right
      simp [List.count_replicate]

private theorem filter_isMid_of_infix_units {k : ℕ} {Gs : List (List LCSSymbol)}
    (hGs : ∀ G ∈ Gs, BlockShape k G) {T : List LCSSymbol}
    (hT : T <:+: (Gs.map (List.replicate k s3 ++ ·)).flatten) (h0 : T.count s0 < k) :
    T.filter LCS.isMid = [] ∨ ∃ G ∈ Gs, T.filter LCS.isMid <+ G.filter LCS.isMid := by
  induction Gs generalizing T with
  | nil =>
    obtain rfl : T = [] := by simpa using hT
    simp
  | cons G Gs ih =>
    have hGs' : ∀ G ∈ Gs, BlockShape k G := fun G hG => hGs G (by simp [hG])
    have hU : (List.replicate k s3 ++ G).filter LCS.isMid = G.filter LCS.isMid := by
      simp [LCS.isMid]
    rw [List.map_cons, List.flatten_cons, List.infix_append_iff] at hT
    rcases hT with h | h | ⟨a, b, rfl, ha, hb⟩
    · exact Or.inr ⟨G, by simp, hU ▸ h.sublist.filter _⟩
    · rcases ih hGs' h h0 with h' | ⟨G', hG', h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨G', by simp [hG'], h'⟩
    · rcases prefix_units_filter_isMid hGs' hb with hb' | hb'
      · refine Or.inr ⟨G, by simp, ?_⟩
        rw [List.filter_append, hb', List.append_nil, ← hU]
        exact ha.sublist.filter _
      · simp [List.count_append] at h0
        omega

private theorem mem_R2 {b : List Bool} {x : LCSSymbol} (h : x ∈ LCS.R2 b) :
    x = s4 ∨ x = s5 ∨ x = s6 := by
  simp only [LCS.R2, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨v, -, rfl⟩, hx⟩ := h
  cases v <;> simp [LCS.CG2] at hx <;> tauto

private theorem blockShape_P2Blocks (d : ℕ) (B : List (List Bool)) :
    ∀ G ∈ LCS.P2Blocks d B, BlockShape (LCS.M d) G := by
  have hD : BlockShape (LCS.M d) (LCS.DummyBlock d) :=
    ⟨List.replicate (LCS.W d) s1 ++ List.replicate (LCS.M d) s2, by simp [LCS.DummyBlock],
      by simp [List.mem_replicate], by simp [List.mem_replicate]⟩
  intro G hG
  simp only [LCS.P2Blocks, List.mem_append, List.mem_replicate, List.mem_map] at hG
  rcases hG with (⟨-, rfl⟩ | ⟨b, -, rfl⟩) | ⟨-, rfl⟩
  · exact hD
  · refine ⟨LCS.R2 b ++ List.replicate (LCS.W d) s1 ++ List.replicate (LCS.M d) s2,
      by simp [LCS.VG2'], ?_, ?_⟩ <;>
    · simp only [List.mem_append, List.mem_replicate, not_or]
      refine ⟨⟨fun h => ?_, by simp⟩, by simp⟩
      rcases mem_R2 h with h | h | h <;> cases h
  · exact hD

/-- For every split `P2 = T₀ ++ T ++ T₁`, the `s3` symbols of `T₀` and `T₁` and the `s0` symbols
of `T` number at most `3 * B.length * LCS.M d`. -/
theorem LCS.count_balance_P2 (d : ℕ) (B : List (List Bool)) {T₀ T T₁ : List LCSSymbol}
    (h : LCS.P2 d B = T₀ ++ T ++ T₁) :
    T₀.count s3 + T.count s0 + T₁.count s3 ≤ 3 * B.length * LCS.M d := by
  have := count_balance_intercalate (k := LCS.M d) (blockShape_P2Blocks d B) h
  simp only [LCS.P2Blocks, List.length_append, List.length_replicate, List.length_map] at this
  linarith

/-- An infix of `LCS.P2` with fewer than `LCS.M d` symbols `s0` meets the middle part of at most
one block. -/
theorem LCS.filter_isMid_of_infix_P2 (d : ℕ) (B : List (List Bool)) {T : List LCSSymbol}
    (hT : T <:+: LCS.P2 d B) (h0 : T.count s0 < LCS.M d) :
    T.filter LCS.isMid = [] ∨ ∃ G ∈ LCS.P2Blocks d B, T.filter LCS.isMid <+ G.filter LCS.isMid := by
  rcases hB : LCS.P2Blocks d B with _ | ⟨G, Gs⟩
  · left
    rw [LCS.P2, hB] at hT
    obtain rfl : T = [] := by simpa using hT
    simp
  · have hT' : T <:+: ((G :: Gs).map (List.replicate (LCS.M d) s3 ++ ·)).flatten := by
      rw [← append_intercalate_cons]
      rw [LCS.P2, hB] at hT
      exact hT.trans (List.suffix_append _ _).isInfix
    exact filter_isMid_of_infix_units (hB ▸ blockShape_P2Blocks d B) hT' h0

end P2Structure

/-! ### Upper bound -/

private theorem LCS.isMid_of_mem_CG1 : ∀ u : Bool, ∀ c ∈ LCS.CG1 u, LCS.isMid c = true := by decide

private theorem LCS.isMid_of_mem_R1 {a : List Bool} {c : LCSSymbol} (h : c ∈ LCS.R1 a) :
    LCS.isMid c := by
  simp only [LCS.R1, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨u, -, rfl⟩, hc⟩ := h
  exact LCS.isMid_of_mem_CG1 u c hc

private theorem LCS.length_R1_le (a : List Bool) : (LCS.R1 a).length ≤ 4 * a.length := by
  induction a with
  | nil => simp [LCS.R1]
  | cons u a ih =>
    have hu : (LCS.CG1 u).length ≤ 4 := by cases u <;> decide
    have e : LCS.R1 (u :: a) = LCS.CG1 u ++ LCS.R1 a := rfl
    rw [e, List.length_append, List.length_cons]
    omega

private theorem LCS.filter_isMid_replicate {n : ℕ} {c : LCSSymbol} :
    (List.replicate n c).filter LCS.isMid = if LCS.isMid c then List.replicate n c else [] := by
  induction n with
  | zero => split <;> rfl
  | succ n ih => cases h : LCS.isMid c <;> simp_all [List.replicate_succ]

private theorem LCS.filter_isMid_R2 (b : List Bool) : (LCS.R2 b).filter LCS.isMid = LCS.R2 b := by
  induction b with
  | nil => rfl
  | cons v b ih =>
    simp only [LCS.R2, List.map_cons, List.flatten_cons, List.filter_append] at ih ⊢
    rw [ih]; cases v <;> rfl

private theorem LCS.filter_isMid_DummyBlock (d : ℕ) :
    (LCS.DummyBlock d).filter LCS.isMid = List.replicate (LCS.W d) s1 := by
  simp [LCS.DummyBlock, List.filter_append, LCS.filter_isMid_replicate, LCS.isMid]

private theorem LCS.filter_isMid_VG2' (d : ℕ) (b : List Bool) :
    (LCS.VG2' d b).filter LCS.isMid = LCS.R2 b ++ List.replicate (LCS.W d) s1 := by
  simp [LCS.VG2', List.filter_append, LCS.filter_isMid_replicate, LCS.isMid,
    LCS.filter_isMid_R2]

/-- The middle of a `P1` block against an infix of `P2`. -/
theorem LCS.lcsLength_mid_infix_le {d : ℕ} {a : List Bool} {B : List (List Bool)}
    {T : List LCSSymbol} (hT : T <:+: LCS.P2 d B) (ha : a.length = d)
    (hB : ∀ b ∈ B, b.length = d ∧ ¬ Orthogonal a b) :
    lcsLength (List.replicate (LCS.W d) s1 ++ LCS.R1 a) T ≤ LCS.W d + T.count s0 := by
  by_cases h0 : T.count s0 < LCS.M d
  · have hx : ∀ c ∈ List.replicate (LCS.W d) s1 ++ LCS.R1 a, LCS.isMid c := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · rw [List.eq_of_mem_replicate hc]; rfl
      · exact LCS.isMid_of_mem_R1 hc
    rw [← lcsLength_filter_right _ hx]
    rcases LCS.filter_isMid_of_infix_P2 d B hT h0 with h | ⟨G, hG, hsub⟩
    · rw [h, lcsLength_nil_right]; exact Nat.zero_le _
    · refine (lcsLength_mono (List.Sublist.refl _) hsub).trans ?_
      refine le_trans ?_ (Nat.le_add_right _ _)
      simp only [LCS.P2Blocks, List.mem_append, List.mem_replicate, List.mem_map] at hG
      rcases hG with (⟨-, rfl⟩ | ⟨b, hb, rfl⟩) | ⟨-, rfl⟩
      · rw [LCS.filter_isMid_DummyBlock]
        exact (lcsLength_le_length_right' _ _).trans (List.length_replicate ..).le
      · rw [LCS.filter_isMid_VG2']
        exact LCS.lcsLength_mid_le ha (hB b hb).1 (hB b hb).2
      · rw [LCS.filter_isMid_DummyBlock]
        exact (lcsLength_le_length_right' _ _).trans (List.length_replicate ..).le
  · refine (lcsLength_le_length_left _ _).trans ?_
    have := LCS.length_R1_le a
    simp only [List.length_append, List.length_replicate, LCS.M] at h0 ⊢
    omega

private theorem LCS.isInfix_of_append_left {α : Type*} {l₁ l₂ l : List α} (h : l₁ ++ l₂ <:+: l) :
    l₁ <:+: l := (List.prefix_append l₁ l₂).isInfix.trans h

private theorem LCS.isInfix_of_append_right {α : Type*} {l₁ l₂ l : List α} (h : l₁ ++ l₂ <:+: l) :
    l₂ <:+: l := (List.suffix_append l₁ l₂).isInfix.trans h

/-- **SX**: one `P1` block against an infix of `P2`. -/
theorem LCS.lcsLength_VG1'_infix_le {d : ℕ} {a : List Bool} {B : List (List Bool)}
    {T : List LCSSymbol} (hT : T <:+: LCS.P2 d B) (ha : a.length = d)
    (hB : ∀ b ∈ B, b.length = d ∧ ¬ Orthogonal a b) :
    lcsLength (LCS.VG1' d a) T ≤ LCS.M d + LCS.W d + T.count s0 := by
  have hV : LCS.VG1' d a = List.replicate (LCS.M d) s0 ++
      ((List.replicate (LCS.W d) s1 ++ LCS.R1 a) ++ List.replicate (LCS.M d) s2) := by
    simp [LCS.VG1']
  rw [hV]
  obtain ⟨T₀, T', rfl, h₁⟩ := exists_lcsLength_append_le (List.replicate (LCS.M d) s0)
    ((List.replicate (LCS.W d) s1 ++ LCS.R1 a) ++ List.replicate (LCS.M d) s2) T
  obtain ⟨T₁, T₂, rfl, h₂⟩ := exists_lcsLength_append_le
    (List.replicate (LCS.W d) s1 ++ LCS.R1 a) (List.replicate (LCS.M d) s2) T'
  have hT₁ : T₁ <:+: LCS.P2 d B :=
    LCS.isInfix_of_append_left (LCS.isInfix_of_append_right hT)
  have e₀ := lcsLength_replicate_left_le (LCS.M d) s0 T₀
  have e₁ := LCS.lcsLength_mid_infix_le hT₁ ha hB
  have e₂ : lcsLength (List.replicate (LCS.M d) s2) T₂ ≤ LCS.M d :=
    (lcsLength_le_length_left _ _).trans (List.length_replicate ..).le
  simp only [List.count_append]
  omega

/-- **Charging**: the body of `P1` against an infix of `P2`. -/
theorem LCS.lcsLength_body_infix_le {d : ℕ} {B : List (List Bool)} :
    ∀ (As : List (List Bool)), (∀ a ∈ As, a.length = d ∧ ∀ b ∈ B, b.length = d ∧
      ¬ Orthogonal a b) → ∀ {T : List LCSSymbol}, T <:+: LCS.P2 d B →
    lcsLength (As.map (LCS.VG1' d)).flatten T ≤ As.length * (LCS.M d + LCS.W d) + T.count s0
  | [], _, T, _ => by simp
  | a :: As, hAs, T, hT => by
    obtain ⟨T₁, T₂, rfl, h⟩ := exists_lcsLength_append_le (LCS.VG1' d a)
      (As.map (LCS.VG1' d)).flatten T
    have ha := hAs a (List.mem_cons_self ..)
    have e₁ := LCS.lcsLength_VG1'_infix_le (LCS.isInfix_of_append_left hT) ha.1 ha.2
    have e₂ := LCS.lcsLength_body_infix_le As (fun a' h' => hAs a' (List.mem_cons_of_mem _ h'))
      (LCS.isInfix_of_append_right hT)
    simp only [List.map_cons, List.flatten_cons, List.length_cons, List.count_append] at h ⊢
    nlinarith

/-- The upper bound when no pair is orthogonal. -/
theorem LCS.lcsLength_P1_P2_le (d : ℕ) (A B : List (List Bool)) (hAB : A.length = B.length)
    (hA' : ∀ a ∈ A, a.length = d) (hB' : ∀ b ∈ B, b.length = d)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ Orthogonal a b) :
    lcsLength (LCS.P1 d A) (LCS.P2 d B) ≤
      A.length * (LCS.M d + LCS.W d) + 3 * A.length * LCS.M d := by
  set L := 3 * A.length * LCS.sepLen d
  have hP1 : LCS.P1 d A = List.replicate L s3 ++
      ((A.map (LCS.VG1' d)).flatten ++ List.replicate L s3) := by
    simp [LCS.P1, L]
  rw [hP1]
  obtain ⟨T₀, T', h₀, e₀⟩ := exists_lcsLength_append_le (List.replicate L s3)
    ((A.map (LCS.VG1' d)).flatten ++ List.replicate L s3) (LCS.P2 d B)
  obtain ⟨T, T₁, rfl, e₁⟩ := exists_lcsLength_append_le
    (A.map (LCS.VG1' d)).flatten (List.replicate L s3) T'
  have hT : T <:+: LCS.P2 d B := ⟨T₀, T₁, by rw [h₀, List.append_assoc]⟩
  have f₀ := lcsLength_replicate_left_le L s3 T₀
  have f₁ := lcsLength_replicate_left_le L s3 T₁
  have fb := LCS.lcsLength_body_infix_le A (fun a ha => ⟨hA' a ha, fun b hb =>
    ⟨hB' b hb, hno a ha b hb⟩⟩) hT
  have bal := LCS.count_balance_P2 d B (T₀ := T₀) (T := T) (T₁ := T₁)
    (by rw [h₀, List.append_assoc])
  rw [← hAB] at bal
  omega

section Lower

open Cslib.Algorithms.Lean.EditDistance
open LCSSymbol

/-! ### Generic facts -/

section General

variable {α : Type*}

private theorem intercalate_append_of_ne_nil (sep : List α) :
    ∀ {L₁ L₂ : List (List α)}, L₁ ≠ [] → L₂ ≠ [] →
      sep.intercalate (L₁ ++ L₂) = sep.intercalate L₁ ++ sep ++ sep.intercalate L₂
  | [], _, h₁, _ => (h₁ rfl).elim
  | _, [], _, h₂ => (h₂ rfl).elim
  | [G], G' :: L₂, _, _ => by simp [List.intercalate_singleton]
  | G :: G' :: L₁, L₂, _, h₂ => by
    have ih := intercalate_append_of_ne_nil sep (L₁ := G' :: L₁) (L₂ := L₂)
      (List.cons_ne_nil _ _) h₂
    simp only [List.cons_append, List.intercalate_cons_cons] at ih ⊢
    simp [ih]

private theorem flatten_sublist_intercalate (sep : List α) :
    ∀ Gs : List (List α), Gs.flatten <+ sep.intercalate Gs
  | [] => by simp
  | [G] => by simp [List.intercalate_singleton]
  | G :: G' :: Gs => by
    rw [List.intercalate_cons_cons, List.flatten_cons, List.append_assoc]
    exact (List.Sublist.refl G).append
      ((flatten_sublist_intercalate sep (G' :: Gs)).trans (List.sublist_append_right sep _))

private theorem count_intercalate_append_ge [BEq α] (c : α) (sep : List α) :
    ∀ Gs : List (List α), Gs.length * sep.count c ≤ (sep.intercalate Gs ++ sep).count c
  | [] => by simp
  | [G] => by simp [List.intercalate_singleton]
  | G :: G' :: Gs => by
    have := count_intercalate_append_ge c sep (G' :: Gs)
    simp only [List.intercalate_cons_cons, List.count_append, List.length_cons] at this ⊢
    rw [Nat.add_mul, Nat.one_mul]
    omega

variable [DecidableEq α]

private theorem le_lcsLength_replicate_left {n L : ℕ} {c : α} {y : List α} (hL : n ≤ L)
    (hy : n ≤ y.count c) : n ≤ lcsLength (List.replicate L c) y := by
  simpa using length_le_lcsLength ((List.replicate_sublist_replicate c).mpr hL)
    (List.replicate_sublist_iff.mpr hy)

private theorem length_le_lcsLength_self (x : List α) : x.length ≤ lcsLength x x :=
  length_le_lcsLength (List.Sublist.refl x) (List.Sublist.refl x)

/-- Superadditivity over aligned lists of blocks, with a uniform bound on each aligned pair. -/
private theorem mul_le_lcsLength_flatten {c : ℕ} :
    ∀ {Xs Ys : List (List α)}, Xs.length = Ys.length →
      (∀ X ∈ Xs, ∀ Y ∈ Ys, c ≤ lcsLength X Y) → Xs.length * c ≤ lcsLength Xs.flatten Ys.flatten
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp at h
  | X :: Xs, Y :: Ys, h, hc => by
    have ih := mul_le_lcsLength_flatten (Xs := Xs) (Ys := Ys) (by simpa using h)
      (fun X hX Y hY => hc X (by simp [hX]) Y (by simp [hY]))
    have := lcsLength_add_le_lcsLength_append X Xs.flatten Y Ys.flatten
    have h1 := hc X (by simp) Y (by simp)
    simp only [List.length_cons, List.flatten_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

end General

/-! ### Gadgets -/

/-- Orthogonal vectors of equal length `n` give coordinate gadget strings with a common
subsequence of length `3 * n`. -/
theorem LCS.three_mul_le_lcsLength_R1_R2 {a b : List Bool} (hab : a.length = b.length)
    (h : Orthogonal a b) : 3 * a.length ≤ lcsLength (LCS.R1 a) (LCS.R2 b) := by
  induction a generalizing b with
  | nil => simp
  | cons u a ih =>
    cases b with
    | nil => simp at hab
    | cons v b =>
      have h0 : ¬(u = true ∧ v = true) := by
        have := h 0
        cases u <;> cases v <;> simp_all
      have ih' := ih (by simpa using hab) (fun i => by simpa using h (i + 1))
      have hc : lcsLength (LCS.CG1 u) (LCS.CG2 v) = 3 := by
        cases u <;> cases v <;> first | exact absurd ⟨rfl, rfl⟩ h0 | decide
      have hs := lcsLength_add_le_lcsLength_append (LCS.CG1 u) (LCS.R1 a) (LCS.CG2 v) (LCS.R2 b)
      have e1 : LCS.R1 (u :: a) = LCS.CG1 u ++ LCS.R1 a := by simp [LCS.R1]
      have e2 : LCS.R2 (v :: b) = LCS.CG2 v ++ LCS.R2 b := by simp [LCS.R2]
      rw [e1, e2, List.length_cons]
      omega

private theorem dummyBlock_sublist_VG1' (d : ℕ) (a : List Bool) :
    LCS.DummyBlock d <+ LCS.VG1' d a :=
  (List.sublist_append_left _ _).append (List.Sublist.refl _)

private theorem dummyBlock_sublist_VG2' (d : ℕ) (b : List Bool) :
    LCS.DummyBlock d <+ LCS.VG2' d b :=
  ((List.sublist_append_left _ _).append (List.Sublist.refl _)).append (List.Sublist.refl _)

private theorem length_dummyBlock (d : ℕ) :
    (LCS.DummyBlock d).length = 2 * LCS.M d + LCS.W d := by
  simp [LCS.DummyBlock]
  omega

/-- The block pair of an orthogonal pair of vectors. -/
private theorem le_lcsLength_VG1'_VG2' (d : ℕ) {a b : List Bool} (hab : a.length = b.length)
    (h : Orthogonal a b) :
    2 * LCS.M d + 3 * a.length ≤ lcsLength (LCS.VG1' d a) (LCS.VG2' d b) := by
  have e1 : LCS.VG1' d a = List.replicate (LCS.M d) s0 ++
      (List.replicate (LCS.W d) s1 ++ LCS.R1 a) ++ List.replicate (LCS.M d) s2 := by
    simp [LCS.VG1']
  have e2 : LCS.VG2' d b = List.replicate (LCS.M d) s0 ++
      (LCS.R2 b ++ List.replicate (LCS.W d) s1) ++ List.replicate (LCS.M d) s2 := by
    simp [LCS.VG2']
  rw [e1, e2]
  have t1 := lcsLength_add_le_lcsLength_append
    (List.replicate (LCS.M d) s0 ++ (List.replicate (LCS.W d) s1 ++ LCS.R1 a))
    (List.replicate (LCS.M d) s2)
    (List.replicate (LCS.M d) s0 ++ (LCS.R2 b ++ List.replicate (LCS.W d) s1))
    (List.replicate (LCS.M d) s2)
  have t2 := lcsLength_add_le_lcsLength_append (List.replicate (LCS.M d) s0)
    (List.replicate (LCS.W d) s1 ++ LCS.R1 a) (List.replicate (LCS.M d) s0)
    (LCS.R2 b ++ List.replicate (LCS.W d) s1)
  have t3 := lcsLength_mono (List.sublist_append_right (List.replicate (LCS.W d) s1) (LCS.R1 a))
    (List.sublist_append_left (LCS.R2 b) (List.replicate (LCS.W d) s1))
  have r := LCS.three_mul_le_lcsLength_R1_R2 hab h
  have q0 := length_le_lcsLength_self (List.replicate (LCS.M d) s0)
  have q2 := length_le_lcsLength_self (List.replicate (LCS.M d) s2)
  simp only [List.length_replicate] at q0 q2
  omega

private theorem baseScore_arith (d N : ℕ) (hN : 1 ≤ N) :
    N * (2 * LCS.M d + 3 * d - 1) + 1 ≤
      (N - 1) * (2 * LCS.M d + LCS.W d) + (2 * LCS.M d + 3 * d) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [LCS.M, LCS.W]
    omega
  · have hW : LCS.W d + 1 = 3 * d := by simp only [LCS.W]; omega
    have hW' : 2 * LCS.M d + 3 * d - 1 = 2 * LCS.M d + LCS.W d := by omega
    rw [hW', Nat.add_mul, Nat.one_mul]
    omega

/-- **Lower bound of the gap.** An orthogonal pair gives a common subsequence of `LCS.P1 d A` and
`LCS.P2 d B` longer than `LCS.BaseScore d N`. -/
theorem LCS.le_lcsLength_P1_P2 (d N : ℕ) (A B : List (List Bool)) (hA : A.length = N)
    (hB : B.length = N) (hA' : ∀ a ∈ A, a.length = d) (hB' : ∀ b ∈ B, b.length = d)
    (h : ∃ a ∈ A, ∃ b ∈ B, Orthogonal a b) :
    LCS.BaseScore d N + 1 ≤ lcsLength (LCS.P1 d A) (LCS.P2 d B) := by
  obtain ⟨a, haA, b, hbB, hab⟩ := h
  have hal : a.length = d := hA' a haA
  have hbl : b.length = d := hB' b hbB
  obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem haA
  obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hbB
  have hlA : A₁.length + A₂.length + 1 = N := by simp at hA; omega
  have hlB : B₁.length + B₂.length + 1 = N := by simp at hB; omega
  have hVG := le_lcsLength_VG1'_VG2' d (hal.trans hbl.symm) hab
  rw [hal] at hVG
  -- The blocks of `P2` before and after the gadget of `b`.
  obtain ⟨U, hU⟩ : ∃ U, U = List.replicate N (LCS.DummyBlock d) ++ B₁.map (LCS.VG2' d) :=
    ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = B₂.map (LCS.VG2' d) ++ List.replicate N (LCS.DummyBlock d) :=
    ⟨_, rfl⟩
  have hGs : LCS.P2Blocks d (B₁ ++ b :: B₂) = U ++ LCS.VG2' d b :: V := by
    subst hU hV
    simp [LCS.P2Blocks, hB]
  have hUl : U.length = N + B₁.length := by subst hU; simp
  have hVl : V.length = B₂.length + N := by subst hV; simp
  have hDY : ∀ Y ∈ U ++ LCS.VG2' d b :: V, LCS.DummyBlock d <+ Y := by
    intro Y hY
    subst hU hV
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.mem_map] at hY
    rcases hY with (⟨-, rfl⟩ | ⟨b', -, rfl⟩) | rfl | (⟨b', -, rfl⟩ | ⟨-, rfl⟩)
    · exact List.Sublist.refl _
    · exact dummyBlock_sublist_VG2' d b'
    · exact dummyBlock_sublist_VG2' d b
    · exact dummyBlock_sublist_VG2' d b'
    · exact List.Sublist.refl _
  have hpair : ∀ a' : List Bool, ∀ Y ∈ U ++ LCS.VG2' d b :: V,
      2 * LCS.M d + LCS.W d ≤ lcsLength (LCS.VG1' d a') Y := fun a' Y hY =>
    length_dummyBlock d ▸ length_le_lcsLength (dummyBlock_sublist_VG1' d a') (hDY Y hY)
  -- The window of `N` blocks aligned with `A`.
  obtain ⟨j, hj⟩ : ∃ j, j = N + B₁.length - A₁.length := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = N - 1 - A₁.length := ⟨_, rfl⟩
  have hsplit : U ++ LCS.VG2' d b :: V =
      U.take j ++ (U.drop j ++ LCS.VG2' d b :: V.take m) ++ V.drop m := by
    calc U ++ LCS.VG2' d b :: V
        = (U.take j ++ U.drop j) ++ LCS.VG2' d b :: (V.take m ++ V.drop m) := by
          rw [List.take_append_drop, List.take_append_drop]
      _ = _ := by simp only [List.append_assoc, List.cons_append]
  have l1 : (U.take j).length = j := by simp [hUl]; omega
  have l2 : (U.drop j).length = A₁.length := by simp [hUl]; omega
  have l3 : (V.take m).length = A₂.length := by simp [hVl]; omega
  have l4 : (V.drop m).length = B₂.length + N - m := by simp [hVl]
  have hpre : U.take j ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hsuf : V.drop m ≠ [] := List.ne_nil_of_length_pos (by omega)
  -- Decompose both strings.
  have hP1 : LCS.P1 d (A₁ ++ a :: A₂) = List.replicate (3 * N * LCS.sepLen d) s3 ++
      ((A₁ ++ a :: A₂).map (LCS.VG1' d)).flatten ++ List.replicate (3 * N * LCS.sepLen d) s3 := by
    simp only [LCS.P1, hA]
  have hP2 : LCS.P2 d (B₁ ++ b :: B₂) =
      ((List.replicate (LCS.sepLen d) s3).intercalate (U.take j) ++
          List.replicate (LCS.sepLen d) s3) ++
        (List.replicate (LCS.sepLen d) s3).intercalate
          (U.drop j ++ LCS.VG2' d b :: V.take m) ++
        (List.replicate (LCS.sepLen d) s3 ++
          (List.replicate (LCS.sepLen d) s3).intercalate (V.drop m)) := by
    rw [LCS.P2, hGs, hsplit, intercalate_append_of_ne_nil _ (by simp) hsuf,
      intercalate_append_of_ne_nil _ hpre (by simp)]
    simp only [List.append_assoc]
  rw [hP1, hP2]
  refine le_trans ?_ (lcsLength_add_le_lcsLength_append _ _ _ _)
  refine le_trans ?_ (Nat.add_le_add_right (lcsLength_add_le_lcsLength_append _ _ _ _) _)
  -- The `s3` runs against the separators outside the window.
  have hX := le_lcsLength_replicate_left (L := 3 * N * LCS.sepLen d) (c := s3)
    (y := (List.replicate (LCS.sepLen d) s3).intercalate (U.take j) ++
      List.replicate (LCS.sepLen d) s3)
    (n := (U.take j).length * LCS.sepLen d) (Nat.mul_le_mul_right _ (by omega))
    (by simpa using count_intercalate_append_ge s3 (List.replicate (LCS.sepLen d) s3) (U.take j))
  have hZ := le_lcsLength_replicate_left (L := 3 * N * LCS.sepLen d) (c := s3)
    (y := List.replicate (LCS.sepLen d) s3 ++
      (List.replicate (LCS.sepLen d) s3).intercalate (V.drop m))
    (n := (V.drop m).length * LCS.sepLen d) (Nat.mul_le_mul_right _ (by omega)) (by
      have := count_intercalate_append_ge s3 (List.replicate (LCS.sepLen d) s3) (V.drop m)
      simp only [List.count_append, List.count_replicate_self] at this ⊢
      omega)
  -- The vector gadgets against the window.
  have hY : A₁.length * (2 * LCS.M d + LCS.W d) + (2 * LCS.M d + 3 * d) +
      A₂.length * (2 * LCS.M d + LCS.W d) ≤
      lcsLength ((A₁ ++ a :: A₂).map (LCS.VG1' d)).flatten
        ((List.replicate (LCS.sepLen d) s3).intercalate
          (U.drop j ++ LCS.VG2' d b :: V.take m)) := by
    refine le_trans ?_ (lcsLength_mono (List.Sublist.refl _) (flatten_sublist_intercalate _ _))
    rw [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons,
      List.flatten_append, List.flatten_cons]
    refine le_trans ?_ (lcsLength_add_le_lcsLength_append _ _ _ _)
    refine le_trans ?_ (Nat.add_le_add_left (lcsLength_add_le_lcsLength_append _ _ _ _) _)
    have e1 := mul_le_lcsLength_flatten (Xs := A₁.map (LCS.VG1' d)) (Ys := U.drop j)
      (c := 2 * LCS.M d + LCS.W d) (by simp [l2]) (fun X hX Y hY => by
        obtain ⟨a', -, rfl⟩ := List.mem_map.mp hX
        exact hpair a' Y (List.mem_append_left _ (List.mem_of_mem_drop hY)))
    have e2 := mul_le_lcsLength_flatten (Xs := A₂.map (LCS.VG1' d)) (Ys := V.take m)
      (c := 2 * LCS.M d + LCS.W d) (by simp [l3]) (fun X hX Y hY => by
        obtain ⟨a', -, rfl⟩ := List.mem_map.mp hX
        exact hpair a' Y
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hY))))
    simp only [List.length_map] at e1 e2
    omega
  -- Arithmetic.
  have hs1 : (U.take j).length * LCS.sepLen d + (V.drop m).length * LCS.sepLen d =
      2 * N * LCS.sepLen d := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hs2 : A₁.length * (2 * LCS.M d + LCS.W d) + A₂.length * (2 * LCS.M d + LCS.W d) =
      (N - 1) * (2 * LCS.M d + LCS.W d) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have harith := baseScore_arith d N (by omega)
  simp only [LCS.BaseScore]
  omega

end Lower

/-! ### The gap theorem -/

theorem LCS.baseScore_eq {d : ℕ} (hd : 0 < d) (N : ℕ) :
    LCS.BaseScore d N = N * (LCS.M d + LCS.W d) + 3 * N * LCS.M d := by
  have h : 2 * LCS.M d + 3 * d - 1 = LCS.M d + LCS.W d + LCS.M d := by
    simp only [LCS.W]; omega
  rw [LCS.BaseScore, h, show LCS.sepLen d = LCS.M d from rfl]
  ring

theorem LCS.lcsLength_P1_P2 (d N : Nat) (A B : List (List Bool))
    (hA : A.length = N) (hB : B.length = N)
    (hA' : ∀ a ∈ A, a.length = d) (hB' : ∀ b ∈ B, b.length = d) :
    LCS.BaseScore d N + 1 ≤ lcsLength (LCS.P1 d A) (LCS.P2 d B) ↔
      ∃ a ∈ A, ∃ b ∈ B, Orthogonal a b := by
  refine ⟨fun h => ?_, LCS.le_lcsLength_P1_P2 d N A B hA hB hA' hB'⟩
  by_contra hno
  push Not at hno
  have hle := LCS.lcsLength_P1_P2_le d A B (hA.trans hB.symm) hA' hB' hno
  rw [hA] at hle
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [LCS.BaseScore] at h hle
    omega
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos (hA ▸ hN)
    obtain ⟨b, hb⟩ := List.exists_mem_of_length_pos (hB ▸ hN)
    refine hno a ha b hb fun i => Or.inl ?_
    rw [List.length_eq_zero_iff.mp (hA' a ha)]
    rfl
  · rw [LCS.baseScore_eq hd] at h
    omega

/-- The reduction from orthogonal vectors to longest common subsequence. -/
@[expose] def toLCS (p : List (List Bool) × List (List Bool)) : List LCSSymbol × List LCSSymbol :=
  (LCS.P1 (OV.dim p) p.1, LCS.P2 (OV.dim p) p.2)

/-- The first list of an instance, with the second replaced by `[]`. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import CslibFrontier.Computability.Complexity.FineGrained.Diameter


/-!
# Orthogonal vectors hardness of longest common subsequence

This module formalizes the reduction from the orthogonal vectors problem to the longest common
subsequence problem by Abboud, Backurs, and Vassilevska Williams
[AbboudBackursVassilevskaWilliams2015].

## Main definitions
* `Cslib.Complexity.OV.toLCS`: the reduction to LCS.

## Main results
* `Cslib.Complexity.OV.lcsLength_toLCS`: the gap characterization.

## References
* [A. Abboud, A. Backurs, V. Vassilevska Williams, *Tight Hardness Results for LCS
  and Other Sequence Similarity Measures*][AbboudBackursVassilevskaWilliams2015]
-/

public section

namespace Cslib.Complexity.OV

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
open Diameter
open Turing.MultiTapeTM

inductive LCSSymbol | s0 | s1 | s2 | s3 | s4 | s5 | s6
  deriving DecidableEq, Repr, Inhabited

open LCSSymbol

@[expose] def encLCSSymbol : LCSSymbol ↪ List Bool :=
  ⟨fun
    | s0 => [false, false, false]
    | s1 => [false, false, true]
    | s2 => [false, true, false]
    | s3 => [false, true, true]
    | s4 => [true, false, false]
    | s5 => [true, false, true]
    | s6 => [true, true, false],
   by intro x y h; revert h; cases x <;> cases y <;> decide⟩

@[expose] def LCS.CG1 (u : Bool) : List LCSSymbol := if u then [s5, s4, s5] else [s5, s4, s6, s5]
@[expose] def LCS.CG2 (v : Bool) : List LCSSymbol := if v then [s5, s6, s5] else [s5, s6, s4, s5]

@[expose] def LCS.R1 (a : List Bool) : List LCSSymbol := (a.map CG1).flatten
@[expose] def LCS.R2 (b : List Bool) : List LCSSymbol := (b.map CG2).flatten

@[expose] def LCS.W (d : Nat) : Nat := 3 * d - 1

@[expose] def LCS.VG1 (d : Nat) (a : List Bool) : List LCSSymbol := List.replicate (W d) s1 ++ R1 a
@[expose] def LCS.VG2 (d : Nat) (b : List Bool) : List LCSSymbol := R2 b ++ List.replicate (W d) s1

@[expose] def LCS.VG1' (d : Nat) (a : List Bool) : List LCSSymbol := [s0] ++ VG1 d a ++ [s2]
@[expose] def LCS.VG2' (d : Nat) (b : List Bool) : List LCSSymbol := [s0] ++ VG2 d b ++ [s2, s3]

@[expose] def LCS.f (d : Nat) : List Bool := List.replicate d true

@[expose] def LCS.P1 (d : Nat) (A : List (List Bool)) : List LCSSymbol :=
  let L := 3 * A.length
  List.replicate L s3 ++ (A.map (VG1' d)).flatten ++ List.replicate L s3

@[expose] def LCS.P2 (d : Nat) (A B : List (List Bool)) : List LCSSymbol :=
  let dummy := (List.replicate A.length (f d)).map (VG2' d)
  [s3] ++ dummy.flatten ++ (B.map (VG2' d)).flatten ++ dummy.flatten

theorem lcsLength_CG1_CG2_true_true : lcsLength (LCS.CG1 true) (LCS.CG2 true) = 2 := by decide
theorem lcsLength_CG1_CG2_true_false : lcsLength (LCS.CG1 true) (LCS.CG2 false) = 3 := by decide
theorem lcsLength_CG1_CG2_false_true : lcsLength (LCS.CG1 false) (LCS.CG2 true) = 3 := by decide
theorem lcsLength_CG1_CG2_false_false : lcsLength (LCS.CG1 false) (LCS.CG2 false) = 3 := by decide

theorem lcsLength_CG1_CG2 (u v : Bool) :
    lcsLength (LCS.CG1 u) (LCS.CG2 v) = if u ∧ v then 2 else 3 := by
  cases u <;> cases v <;> decide


@[expose] def toLCS (p : List (List Bool) × List (List Bool)) : List LCSSymbol × List LCSSymbol :=
  (LCS.P1 (dim p) p.1, LCS.P2 (dim p) p.1 p.2)



/-- it reads the marker of a bit of the outer frame of `A` (or the first bit of `encOV`),
whether the bit it reads is a frame marker, the coordinate of the current bit, and the number
of the current vector. -/
abbrev LCSParseState : Type := (((Bool × Bool) × Bool) × ℕ) × ℕ

/-- The encoding of the parser state. -/
abbrev encLCSParseState : LCSParseState ↪ List Bool :=
  encPair (encPair (encPair (encPair encBool encBool) encBool) encNat) encNat

/-- A round of the parser, reading one bit. In the first list each bit `c` of the inner frames
comes as `[true, c]` in the outer frame, and the first unmarked bit ends the first list. In the
inner frames, a marker `true` announces a bit of the vector and `false` ends the vector. -/
def lcsParseStep (p : LCSParseState × Bool) : LCSParseState :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then
    if p.2 then ((((false, true), p.1.1.1.2), p.1.1.2), p.1.2)
    else ((((true, false), false), p.1.1.2), p.1.2)
  else if p.1.1.1.2 then ((((p.1.1.1.1.1, false), false), p.1.1.2 + 1), p.1.2)
  else if p.2 then ((((p.1.1.1.1.1, false), true), p.1.1.2), p.1.2)
  else ((((p.1.1.1.1.1, false), false), 0), p.1.2 + 1)

/-- The output of a round of the parser: `f k i b` for the bit `b` of coordinate `i` of the vector
numbered `k`, and `g s k` at the end of the vector numbered `k` of the list `s`. -/
def lcsParseEmit {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β)
    (p : LCSParseState × Bool) : List β :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then []
  else if p.1.1.1.2 then f p.1.2 p.1.1.2 p.2
  else if p.2 then []
  else g p.1.1.1.1.1 p.1.2

/-- **One pass of the parser** over a list of bits, from a state. -/
def lcsParseRun {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β) :
    LCSParseState → List Bool → List β
  | _, [] => []
  | s, b :: l => lcsParseEmit f g (s, b) ++ lcsParseRun f g (lcsParseStep (s, b)) l

section Stream

variable {β : Type} {f : ℕ → ℕ → Bool → List β} {g : Bool → ℕ → List β}

/-- The streamed output of the parser rounds is the encoded output of the pass. -/
theorem streamEmit_eq_lcsParseRun {enc : β ↪ List Bool} (s : LCSParseState) (l : List Bool) :
    streamEmit lcsParseStep (fun p => encList enc (lcsParseEmit f g p)) s l =
      encList enc (lcsParseRun f g s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => rw [streamEmit, ih, lcsParseRun, encList_append]

/-- In the second phase, a frame `[true, b₁, …, true, bₙ, false]` is one vector. -/
theorem lcsParseRun_frame_snd (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), i), k) (frame v ++ rest) =
      bitsOut (f k) i v ++ g true k ++
        lcsParseRun f g ((((true, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [frame_nil, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.cons_append, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
    simp [ih, List.append_assoc]

/-- In the second phase, the frames of a list of vectors. -/
theorem lcsParseRun_frames_snd (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), 0), k) (vs.flatMap frame ++ rest) =
      vecsOut f (g true) k vs ++
        lcsParseRun f g ((((true, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.append_assoc, lcsParseRun_frame_snd, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- In the first phase, the outer frame marks each bit `c` of the inner frames as `[true, c]`. -/
theorem lcsParseRun_frame_fst (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), i), k)
        ((frame v).flatMap (fun b => [true, b]) ++ rest) =
      bitsOut (f k) i v ++ g false k ++
        lcsParseRun f g ((((false, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    cases b <;> simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut, ih, List.append_assoc]

/-- In the first phase, the outer frame of the inner frames of a list of vectors. -/
theorem lcsParseRun_frames_fst (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), 0), k)
        ((vs.flatMap frame).flatMap (fun b => [true, b]) ++ rest) =
      vecsOut f (g false) k vs ++
        lcsParseRun f g ((((false, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.append_assoc, lcsParseRun_frame_fst, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- **The parser on an encoded instance**: it emits the outputs of the first list, then those of
the second, numbering the vectors of both lists consecutively. -/
theorem lcsParseRun_encOV (p : List (List Bool) × List (List Bool)) :
    lcsParseRun f g ((((false, false), false), 0), 0) (encOV p) =
      vecsOut f (g false) 0 p.1 ++ vecsOut f (g true) p.1.length p.2 := by
  have hl (l : List (List Bool)) : encList encBits l = l.flatMap frame := rfl
  have e : encOV p = (p.1.flatMap frame).flatMap (fun b => [true, b]) ++
      (false :: p.2.flatMap frame ++ []) := by
    simp only [encOV, encPair_apply, frame, hl, List.append_nil, List.append_assoc,
      List.singleton_append]
  have h₁ : lcsParseStep (((((false, false), false), 0), 0 + p.1.length), false) =
      ((((true, false), false), 0), p.1.length) := by simp [lcsParseStep]
  have h₂ : lcsParseEmit f g (((((false, false), false), 0), 0 + p.1.length), false) = [] := by
    simp [lcsParseEmit]
  rw [e, lcsParseRun_frames_fst, List.cons_append, lcsParseRun, h₁, h₂, List.nil_append,
    lcsParseRun_frames_snd]
  simp [lcsParseRun]

end Stream

/-! ### The size of the parser state -/

/-- A round increases the coordinate plus the vector number by at most one. -/
private theorem lcsParseStep_le (s : LCSParseState) (b : Bool) :
    (lcsParseStep (s, b)).1.2 + (lcsParseStep (s, b)).2 ≤ s.1.2 + s.2 + 1 := by
  unfold lcsParseStep
  split_ifs <;> simp only <;> omega

/-- The coordinate plus the vector number grow by at most the number of rounds. -/
private theorem foldl_lcsParseStep_le (s : LCSParseState) (l : List Bool) :
    (l.foldl (fun s b => lcsParseStep (s, b)) s).1.2 +
      (l.foldl (fun s b => lcsParseStep (s, b)) s).2 ≤
      s.1.2 + s.2 + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    have := ih (lcsParseStep (s, b))
    have := lcsParseStep_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The length of an encoded parser state. -/
private theorem length_encLCSParseState (s : LCSParseState) :
    (encLCSParseState s).length = 43 + 2 * Nat.size s.1.2 + Nat.size s.2 := by
  simp only [length_encPair, encBool_apply, encNat_apply, Nat.size_eq_bits_len,
    List.length_singleton]
  omega

/-- The parser state after `j` bits holds numbers at most `j`. -/
private theorem length_encLCSParseState_streamState_le (x : List Bool) (j : ℕ) :
    (encLCSParseState (streamState ((((false, false), false), 0), 0) lcsParseStep x j)).length ≤
      43 + 3 * Nat.size x.length := by
  have h₁ : (streamState ((((false, false), false), 0), 0) lcsParseStep x j).1.2 +
      (streamState ((((false, false), false), 0), 0) lcsParseStep x j).2 ≤ x.length := by
    have := foldl_lcsParseStep_le ((((false, false), false), 0), 0) (x.take j)
    simp only [List.length_take, Nat.zero_add] at this
    exact this.trans (min_le_right _ _)
  have h₂ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) lcsParseStep x j).1.2 ≤ x.length by omega)
  have h₃ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) lcsParseStep x j).2 ≤ x.length by omega)
  rw [length_encLCSParseState]
  omega

open ComputableInPolyTime in
/-- A round of the parser is computable in polynomial time. -/
theorem computableInPolyTime_lcsParseStep :
    ComputableInPolyTime lcsParseStep (encPair encLCSParseState encBool) encLCSParseState := by
  unfold lcsParseStep
  fun_prop

open ComputableInPolyTime in
/-- The output of a round of the parser is computable in polynomial time when its outputs are. -/
theorem computableInPolyTime_lcsParseEmit {β : Type} {enc : β ↪ List Bool}
    {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β}
    (hf : ComputableInPolyTime (fun p : LCSParseState × Bool => f p.1.2 p.1.1.2 p.2)
      (encPair encLCSParseState encBool) (encList enc))
    (hg : ComputableInPolyTime (fun p : LCSParseState × Bool => g p.1.1.1.1.1 p.1.2)
      (encPair encLCSParseState encBool) (encList enc)) :
    ComputableInPolyTime (lcsParseEmit f g) (encPair encLCSParseState encBool) (encList enc) := by
  have hnil : ComputableInPolyTime (fun _ : LCSParseState × Bool => ([] : List β))
      (encPair encLCSParseState encBool) (encList enc) := by fun_prop
  have hc₁ : ComputableInPolyTime (fun p : LCSParseState × Bool => !p.1.1.1.1.1 && !p.1.1.1.1.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  have hc₂ : ComputableInPolyTime (fun p : LCSParseState × Bool => p.1.1.1.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  have hc₃ : ComputableInPolyTime (fun p : LCSParseState × Bool => p.2)
      (encPair encLCSParseState encBool) encBool := by fun_prop
  exact ite' hc₁ hnil (ite' hc₂ hf (ite' hc₃ hnil hg))

open ComputableInPolyTime in
/-- **One pass of the parser** over an encoded instance runs within time `L (log L) ^ D` on inputs
of length `L`, when its outputs are computable in polynomial time. -/
theorem computableInO_lcsParseRun {β : Type} {enc : β ↪ List Bool} {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β} (fin : List β)
    (hfg : ComputableInPolyTime (lcsParseEmit f g) (encPair encLCSParseState encBool)
      (encList enc)) :
    ∃ D, ComputableInO
      (fun x : List Bool => lcsParseRun f g ((((false, false), false), 0), 0) x ++ fin)
      encBits (encList enc) (fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D)
      fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D := by
  obtain ⟨dN, _, hN_deg⟩ := computableInPolyTime_lcsParseStep.exists_degree
  obtain ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩ := Internal.NormalForm.degree hN_deg
  obtain ⟨dE, _, hE_deg⟩ := hfg.exists_degree
  obtain ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩ := Internal.NormalForm.degree hE_deg
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (α := List Bool)
    (encIn := encBits)
    (encOut := encLCSParseState) ((((false, false), false), 0), 0)
  obtain ⟨cF, hF⟩ := computableInTimeAndSpace_of_const (α := LCSParseState)
    (encIn := encLCSParseState)
    (encOut := encList enc) fin
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  have hI' : ComputableTidilyInTimeAndSpace
      (fun _ : List Bool => ((((false, false), false), 0), 0))
      encBits encLCSParseState (fun _ => 2 * cI + 2) (fun _ => 0) :=
    hI.computableTidilyInTimeAndSpace
  have hF' : ComputableTidilyInTimeAndSpace (fun _ : LCSParseState => fin)
      encLCSParseState (encList enc)
      (fun _ => 2 * cF + 2) (fun _ => 0) := hF.computableTidilyInTimeAndSpace
  -- the rounds take time polylogarithmic in the input length
  have hpow (x : List Bool) (d : ℕ) (hd : d ≤ dN + dE + 1) :
      (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤
        89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    calc (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤ (89 * (Nat.size x.length + 1)) ^ d :=
          Nat.pow_le_pow_left (by omega) d
      _ = 89 ^ d * (Nat.size x.length + 1) ^ d := Nat.mul_pow _ _ _
      _ ≤ 89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) := by gcongr
  have hround (x : List Bool) (j : ℕ) (hj : j < x.length) (c₁ c₂ : ℕ)
      (u₁ u₂ : LCSParseState × Bool → ℕ)
      (h₁ : ∀ a, u₁ a ≤ c₁ * ((encPair encLCSParseState encBool a).length + 1) ^ dN)
      (h₂ : ∀ a, u₂ a ≤ c₂ * ((encPair encLCSParseState encBool a).length + 1) ^ dE) :
      u₁ (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]) +
        u₂ (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]) ≤
      c₁ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
        c₂ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE := by
    have hs : (encLCSParseState
        (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j]).1).length ≤
        43 + 3 * Nat.size x.length := length_encLCSParseState_streamState_le x j
    have e : (encPair encLCSParseState encBool
        (streamState ((((false, false), false), 0), 0) lcsParseStep x j, x[j])).length + 1 ≤
        2 * (43 + 3 * Nat.size x.length) + 3 := by
      rw [length_encPair, encBool_apply, List.length_singleton]
      omega
    exact Nat.add_le_add ((h₁ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
      ((h₂ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold reader (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [reader, InputReader.read])
    (encA := encBool) (fun x => x) (fun x => by simp) hI' hN hE hF'
    (g := fun x : List Bool => lcsParseRun f g ((((false, false), false), 0), 0) x ++ fin)
    (fun x => by rw [encList_append, streamEmit_eq_lcsParseRun])
    (tMax := fun x => cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (sMax := fun x => cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (lMax := fun x => 43 + 3 * Nat.size x.length)
    (fun x j hj => hround x j hj cN cE tN tE htN htE)
    (fun x j hj => hround x j hj cN' cE' sN sE hsN hsE)
    (fun x j _ => length_encLCSParseState_streamState_le x j)
    (fun x j hj => by rw [encBool_apply, List.length_singleton]; omega)
  set M := cN * 89 ^ dN + cE * 89 ^ dE + cN' * 89 ^ dN + cE' * 89 ^ dE
  have key (L Y t l a b : ℕ) (hY : 1 ≤ Y) (ht : t ≤ M * Y) (hl : l ≤ 43 * Y) :
      a + b + L + L * (t + l + 1) + l + 1 ≤ (a + b + M + 100) * ((L + 1) * Y + 1) := by
    nlinarith [Nat.mul_le_mul_left L ht, Nat.mul_le_mul_left L hl, Nat.mul_le_mul_left L hY]
  have key2 (L Y s l a b : ℕ) (hY : 1 ≤ Y) (hs : s ≤ M * Y) (hl : l ≤ 43 * Y) :
      0 + 0 + s + l + 1 ≤ (a + b + M + 100) * ((L + 1) * Y + 1) := by
    have h1 : s + l + 1 ≤ (M + 43) * Y + 1 := by nlinarith
    have h2 : (M + 43) * Y + 1 ≤ (a + b + M + 100) * Y := by nlinarith
    have h3 : (a + b + M + 100) * Y ≤ (a + b + M + 100) * ((L + 1) * Y + 1) := by nlinarith
    omega
  have hY (x : List Bool) : 1 ≤ (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    Nat.one_le_pow _ _ (by omega)
  have hl (x : List Bool) : 43 + 3 * Nat.size x.length ≤
      43 * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have := Nat.le_self_pow (show dN + dE + 1 ≠ 0 by omega) (Nat.size x.length + 1)
    omega
  have ht (x : List Bool) : cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  have hs (x : List Bool) : cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN' (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE' (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  refine ⟨dN + dE + 1, ComputableInO.of_bounds h.computableInTimeAndSpace
    (c * (2 * cI + 2 + (2 * cF + 2) + M + 100))
    (fun x => by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      rw [encBits_apply]
      exact key _ _ _ _ _ _ (hY x) (ht x) (hl x))
    (fun x => by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      exact key2 x.length _ _ _ (2 * cI + 2) (2 * cF + 2) (hY x) (hs x) (hl x))
    (fun x => by
      apply (h.computableInTimeAndSpace.length_le x).trans
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      rw [encBits_apply]
      exact key _ _ _ _ _ _ (hY x) (ht x) (hl x))⟩



theorem computableInPolyTime_toLCS :
    ComputableInPolyTime toLCS encOV (encPair (encList encLCSSymbol) (encList encLCSSymbol)) := by
  sorry

def extractA (p : List (List Bool) × List (List Bool)) : List (List Bool) × List (List Bool) :=
  (p.1, [])
/-- The second list of an instance, with the first replaced by `[]`. -/
def extractB (p : List (List Bool) × List (List Bool)) : List (List Bool) × List (List Bool) :=
  ([], p.2)

theorem comp_extractA : ComputableInO extractA encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ :=
    ComputableInO.of_linear (.of_eq fun _ => rfl)
  have fst : ComputableInO (fun p : _ × _ => p.1) encOV (encList encBits) _ _ :=
    ComputableInO.fst' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod fst nil
  exact pair.mono 2 (fun p => by omega) (fun p => by omega)

theorem comp_extractB : ComputableInO extractB encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ :=
    ComputableInO.of_linear (.of_eq fun _ => rfl)
  have snd : ComputableInO (fun p : _ × _ => p.2) encOV (encList encBits) _ _ :=
    ComputableInO.snd' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod nil snd
  exact pair.mono 2 (fun p => by omega) (fun p => by omega)
end Cslib.Complexity.OV
