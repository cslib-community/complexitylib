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
public import CslibFrontier.Computability.Complexity.FineGrained.Diameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Orthogonal vectors hardness of longest common subsequence

This module reduces the orthogonal vectors problem to the longest common subsequence problem,
following the gadget approach of Abboud, Backurs and Vassilevska Williams
\[AbboudBackursVassilevskaWilliams2015\]. Each vector becomes a block whose `s0` and `s2` runs of
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
* `Cslib.Complexity.OV.computableInPolyTime_toLCS`: the reduction is computable in polynomial
  time.
* `Cslib.Complexity.OV.exists_computableInO_toLCS`: the reduction runs within time
  `L ((d + 1) (log L + 1)) ^ D` on instances of dimension `d` encoded in length `L`. It is
  assembled from streaming passes over the encoded instance whose state holds the dimension in
  unary; a first pass computes the dimension.

The upper bound charges each symbol of a common subsequence either to a block of `P1` (at most
`LCS.M d + LCS.W d` each) or to an `s0` symbol of `P2`. A counting lemma on `P2` bounds the
`s3` symbols that remain usable.

## References
* [A. Abboud, A. Backurs, V. Vassilevska Williams, *Tight Hardness Results for LCS and Other
  Sequence Similarity Measures*]\[AbboudBackursVassilevskaWilliams2015\]
-/
public section

open scoped List

namespace Cslib.Complexity.OV
open Diameter

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
open Diameter
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

/-- it reads the marker of a bit of the outer frame of `A` (or the first bit of `encOV`),
whether the bit it reads is a frame marker, the coordinate of the current bit, and the number
of the current vector. -/
abbrev LCSParseState : Type := (((Bool × Bool) × Bool) × ℕ) × ℕ

/-- The encoding of the parser state. -/
abbrev encLCSParseState : LCSParseState ↪ List Bool :=
  encPair (encPair (encPair (encPair encBool encBool) encBool) encNat) encNat

namespace LIn

abbrev s1 (p : LCSParseState × Bool) := p.1.1.1.1.1
abbrev s2 (p : LCSParseState × Bool) := p.1.1.1.1.2
abbrev marker (p : LCSParseState × Bool) := p.1.1.1.2
abbrev coord (p : LCSParseState × Bool) := p.1.1.2
abbrev vec (p : LCSParseState × Bool) := p.1.2
abbrev bit (p : LCSParseState × Bool) := p.2

end LIn

/-- A round of the parser, reading one bit. In the first list each bit `c` of the inner frames
comes as `[true, c]` in the outer frame, and the first unmarked bit ends the first list. In the
inner frames, a marker `true` announces a bit of the vector and `false` ends the vector. -/
def lcsParseStep (p : LCSParseState × Bool) : LCSParseState :=
  if !LIn.s1 p && !LIn.s2 p then
    if LIn.bit p then
      ((((false, true), LIn.marker p), LIn.coord p), LIn.vec p)
    else
      ((((true, false), false), LIn.coord p), LIn.vec p)
  else if LIn.marker p then
    ((((LIn.s1 p, false), false), LIn.coord p + 1), LIn.vec p)
  else if LIn.bit p then
    ((((LIn.s1 p, false), true), LIn.coord p), LIn.vec p)
  else
    ((((LIn.s1 p, false), false), 0), LIn.vec p + 1)

section Passes

variable {β : Type}

/-- The output of a round of the parser: `f s k i b` for the bit `b` of coordinate `i` of the
vector numbered `k` of the list `s` (`false` for the first list), and `g s k i` at the end of that
vector, which has `i` bits. -/
def lcsParseEmit (f : Bool → ℕ → ℕ → Bool → List β) (g : Bool → ℕ → ℕ → List β)
    (p : LCSParseState × Bool) : List β :=
  if !LIn.s1 p && !LIn.s2 p then []
  else if LIn.marker p then
    f (LIn.s1 p) (LIn.vec p) (LIn.coord p) (LIn.bit p)
  else if LIn.bit p then []
  else g (LIn.s1 p) (LIn.vec p) (LIn.coord p)

/-- **One pass of the parser** over a list of bits, from a state. -/
def lcsParseRun (f : Bool → ℕ → ℕ → Bool → List β) (g : Bool → ℕ → ℕ → List β) :
    LCSParseState → List Bool → List β
  | _, [] => []
  | s, b :: l => lcsParseEmit f g (s, b) ++ lcsParseRun f g (lcsParseStep (s, b)) l

/-- The concatenated outputs of the vectors of a list, numbered from `k`: for the vector `v`
numbered `k`, the outputs `f k i b` of its bits followed by `g k v.length`. -/
def lcsVecsOut (f : ℕ → ℕ → Bool → List β) (g : ℕ → ℕ → List β) :
    ℕ → List (List Bool) → List β
  | _, [] => []
  | k, v :: vs => bitsOut (f k) 0 v ++ g k v.length ++ lcsVecsOut f g (k + 1) vs

section Frames

variable {f : Bool → ℕ → ℕ → Bool → List β} {g : Bool → ℕ → ℕ → List β}

theorem lcsParseRun_frame_snd (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), i), k) (frame v ++ rest) =
      bitsOut (f true k) i v ++ g true k (i + v.length) ++
        lcsParseRun f g ((((true, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [frame_nil, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.cons_append, lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
    simp [ih, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 v.length]

theorem lcsParseRun_frames_snd (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((true, false), false), 0), k) (vs.flatMap frame ++ rest) =
      lcsVecsOut (f true) (g true) k vs ++
        lcsParseRun f g ((((true, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [lcsVecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.append_assoc, lcsParseRun_frame_snd, ih]
    simp [lcsVecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

theorem lcsParseRun_frame_fst (i k : ℕ) (v : List Bool) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), i), k)
        ((frame v).flatMap (fun b => [true, b]) ++ rest) =
      bitsOut (f false k) i v ++ g false k (i + v.length) ++
        lcsParseRun f g ((((false, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    cases b <;>
      simp [lcsParseRun, lcsParseEmit, lcsParseStep, bitsOut, ih, List.append_assoc, Nat.add_assoc,
        Nat.add_comm 1 v.length]

theorem lcsParseRun_frames_fst (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    lcsParseRun f g ((((false, false), false), 0), k)
        ((vs.flatMap frame).flatMap (fun b => [true, b]) ++ rest) =
      lcsVecsOut (f false) (g false) k vs ++
        lcsParseRun f g ((((false, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [lcsVecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.append_assoc, lcsParseRun_frame_fst, ih]
    simp [lcsVecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

theorem lcsParseRun_encOV (p : List (List Bool) × List (List Bool)) :
    lcsParseRun f g ((((false, false), false), 0), 0) (encOV p) =
      lcsVecsOut (f false) (g false) 0 p.1 ++ lcsVecsOut (f true) (g true) p.1.length p.2 := by
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

end Frames



end Passes

/-! ### The size of the parser state -/

/-- A round increases the coordinate plus the vector number by at most one. -/
private theorem lcsParseStep_le (s : LCSParseState) (b : Bool) :
    (lcsParseStep (s, b)).1.2 + (lcsParseStep (s, b)).2 ≤ s.1.2 + s.2 + 1 := by
  unfold lcsParseStep LIn.s1 LIn.s2 LIn.marker LIn.coord LIn.vec LIn.bit
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

section Passes

variable {β : Type}

/-! ### Outputs of the passes -/

private theorem bitsOut_nil_fun (i : ℕ) (v : List Bool) :
    bitsOut (fun _ _ => ([] : List β)) i v = [] := by
  induction v generalizing i with
  | nil => rfl
  | cons b v ih => simp [bitsOut, ih]

private theorem lcsVecsOut_const (c : List β) (k : ℕ) (vs : List (List Bool)) :
    lcsVecsOut (fun _ _ _ => []) (fun _ _ => c) k vs = vs.flatMap (fun _ => c) := by
  induction vs generalizing k with
  | nil => rfl
  | cons v vs ih => simp [lcsVecsOut, bitsOut_nil_fun, ih]

private theorem bitsOut_gadget_pos (pre : List β) (CG : Bool → List β) (v : List Bool) (i : ℕ)
    (hi : 0 < i) :
    bitsOut (fun i b => (if i = 0 then pre else []) ++ CG b) i v = v.flatMap CG := by
  induction v generalizing i with
  | nil => rfl
  | cons b v ih =>
    simp [bitsOut, ih (i + 1) (by omega), Nat.pos_iff_ne_zero.mp hi]

private theorem lcsVecsOut_gadget (pre suf : List β) (CG : Bool → List β) (k : ℕ)
    (vs : List (List Bool)) :
    lcsVecsOut (fun _ i b => (if i = 0 then pre else []) ++ CG b)
      (fun _ i => (if i = 0 then pre else []) ++ suf) k vs =
      vs.flatMap (fun v => pre ++ v.flatMap CG ++ suf) := by
  induction vs generalizing k with
  | nil => rfl
  | cons v vs ih =>
    simp only [lcsVecsOut, ih, List.flatMap_cons]
    congr 1
    rcases v with _ | ⟨b, v⟩
    · simp [bitsOut]
    · simp [bitsOut, bitsOut_gadget_pos pre CG v 1 one_pos, List.append_assoc]

private theorem flatMap_const_replicate {α γ : Type*} (l : List α) (m : ℕ) (a : γ) :
    l.flatMap (fun _ => List.replicate m a) = List.replicate (l.length * m) a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, ih, ← List.replicate_add, List.length_cons, Nat.succ_mul,
      Nat.add_comm]

/-! ### The dimension -/

/-- The initial state of the parser. -/
private abbrev LCS.parseStart : LCSParseState := ((((false, false), false), 0), 0)

/-- A round of the dimension pass: the parser reads a bit, and the largest coordinate read so far
is kept in binary. -/
private def LCS.dimStep (q : (LCSParseState × ℕ) × Bool) : LCSParseState × ℕ :=
  (lcsParseStep (q.1.1, q.2),
    if (q.1.1.1.1.1.1 || q.1.1.1.1.1.2) && q.1.1.1.1.2 && decide (q.1.2 < q.1.1.1.2 + 1) then
      q.1.1.1.2 + 1 else q.1.2)

/-- The coordinates read by the dimension pass, as outputs of the parser. -/
private def LCS.dimBits (_ : Bool) (_ i : ℕ) (_ : Bool) : List ℕ := [i + 1]
/-- The dimension pass outputs nothing at the ends of the vectors. -/
private def LCS.dimEnd (_ : Bool) (_ _ : ℕ) : List ℕ := []

private theorem dimStep_eq (s : LCSParseState) (m : ℕ) (b : Bool) :
    LCS.dimStep ((s, m), b) =
      (lcsParseStep (s, b), (lcsParseEmit LCS.dimBits LCS.dimEnd (s, b)).foldl max m) := by
  obtain ⟨⟨⟨⟨s1, s2⟩, mk⟩, c⟩, v⟩ := s
  refine Prod.ext rfl ?_
  cases s1 <;> cases s2 <;> cases mk <;> cases b <;>
    simp only [LCS.dimStep, lcsParseEmit, LCS.dimBits, LCS.dimEnd, LIn.s1, LIn.s2, LIn.marker,
      LIn.coord, LIn.bit,
      ] <;> simp <;> split_ifs <;> omega

private theorem foldl_dimStep (l : List Bool) (s : LCSParseState) (m : ℕ) :
    l.foldl (fun q b => LCS.dimStep (q, b)) (s, m) =
      (l.foldl (fun s b => lcsParseStep (s, b)) s,
        (lcsParseRun LCS.dimBits LCS.dimEnd s l).foldl max m) := by
  induction l generalizing s m with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, dimStep_eq, ih, List.foldl_cons, lcsParseRun, List.foldl_append]

/-- The largest coordinate read in a list of bits: the dimension of an encoded instance. -/
private def LCS.dimOf (x : List Bool) : ℕ :=
  (x.foldl (fun q b => LCS.dimStep (q, b)) (LCS.parseStart, 0)).2

private theorem foldl_max_bitsOut (s : Bool) (k i m : ℕ) (v : List Bool) (h : i ≤ m) :
    (bitsOut (LCS.dimBits s k) i v).foldl max m = max m (i + v.length) := by
  induction v generalizing i m with
  | nil => simp [bitsOut]; omega
  | cons b v ih =>
    simp only [bitsOut, LCS.dimBits, List.singleton_append, List.foldl_cons]
    rw [ih (i + 1) (max m (i + 1)) (le_max_right _ _)]
    simp only [List.length_cons]
    omega

private theorem listMax_cons {α : Type*} (f : α → ℕ) (a : α) (l : List α) :
    listMax f (a :: l) = max (f a) (listMax f l) := rfl

private theorem listMax_append {α : Type*} (f : α → ℕ) (l₁ l₂ : List α) :
    listMax f (l₁ ++ l₂) = max (listMax f l₁) (listMax f l₂) := by
  induction l₁ with
  | nil => simp [listMax]
  | cons a l ih => rw [List.cons_append, listMax_cons, listMax_cons, ih, Nat.max_assoc]

private theorem foldl_max_lcsVecsOut (s : Bool) (k m : ℕ) (vs : List (List Bool)) :
    (lcsVecsOut (LCS.dimBits s) (LCS.dimEnd s) k vs).foldl max m =
      max m (listMax List.length vs) := by
  induction vs generalizing k m with
  | nil => simp [lcsVecsOut, listMax]
  | cons v vs ih =>
    rw [lcsVecsOut, List.foldl_append, List.foldl_append,
      foldl_max_bitsOut s k 0 m v (Nat.zero_le _), LCS.dimEnd, List.foldl_nil, ih, listMax_cons]
    omega

private theorem dimOf_encOV (p : List (List Bool) × List (List Bool)) :
    LCS.dimOf (encOV p) = OV.dim p := by
  rw [LCS.dimOf, LCS.parseStart, foldl_dimStep]
  dsimp only
  rw [lcsParseRun_encOV, List.foldl_append, foldl_max_lcsVecsOut, foldl_max_lcsVecsOut, OV.dim,
    listMax_append]
  omega



/-- A bound used for a round. -/
private theorem pow_le_three_pow_mul {a l d K : ℕ} (ha : a + 1 ≤ 3 * (l + 1)) (hd : d ≤ K) :
    (a + 1) ^ d ≤ 3 ^ K * (l + 1) ^ K :=
  calc (a + 1) ^ d ≤ (3 * (l + 1)) ^ d := Nat.pow_le_pow_left ha _
    _ ≤ (3 * (l + 1)) ^ K := Nat.pow_le_pow_right (by omega) hd
    _ = 3 ^ K * (l + 1) ^ K := Nat.mul_pow _ _ _

open ComputableInPolyTime in
/-- **One pass over a bit string** with polynomial-time rounds: when the states stay within
length `lMax x`, the pass costs its initialization, its finish and `(x.length + 1)` rounds of
time polynomial in `lMax x`. -/
private theorem bitStream {σ ω : Type} {encS : σ ↪ List Bool} {encOut : ω ↪ List Bool}
    {init : List Bool → σ} {next : σ × Bool → σ} {emit : σ × Bool → List Bool}
    {finish : σ → List Bool} {g : List Bool → ω} {tI sI : List Bool → ℕ} {tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encBits encS tI sI)
    (hnext : ComputableInPolyTime next (encPair encS encBool) encS)
    (hemit : ComputableInPolyTime emit (encPair encS encBool) encBits)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encBits tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next emit (init x) x ++
      finish (streamState (init x) next x x.length))
    (lMax : List Bool → ℕ)
    (hS : ∀ x, ∀ j ≤ x.length, (encS (streamState (init x) next x j)).length ≤ lMax x) :
    ∃ c K, ComputableTidilyInTimeAndSpace g encBits encOut
      (fun x => c * (tI x + tF (streamState (init x) next x x.length) +
        (x.length + 1) * (lMax x + 1) ^ K))
      (fun x => c * (sI x + sF (streamState (init x) next x x.length) + (lMax x + 1) ^ K)) := by
  obtain ⟨dN, _, hN_deg⟩ := hnext.exists_degree
  obtain ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩ := Internal.NormalForm.degree hN_deg
  obtain ⟨dE, _, hE_deg⟩ := hemit.exists_degree
  obtain ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩ := Internal.NormalForm.degree hE_deg
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  have hround (x : List Bool) (j : ℕ) (hj : j < x.length) (c₁ c₂ : ℕ)
      (u₁ u₂ : σ × Bool → ℕ)
      (h₁ : ∀ a, u₁ a ≤ c₁ * ((encPair encS encBool a).length + 1) ^ dN)
      (h₂ : ∀ a, u₂ a ≤ c₂ * ((encPair encS encBool a).length + 1) ^ dE) :
      u₁ (streamState (init x) next x j, x[j]) + u₂ (streamState (init x) next x j, x[j]) ≤
        (c₁ + c₂) * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)) := by
    have e : (encPair encS encBool (streamState (init x) next x j, x[j])).length + 1 ≤
        3 * (lMax x + 1) := by
      have := hS x j hj.le
      rw [length_encPair, encBool_apply, List.length_singleton]
      dsimp only
      omega
    have p₁ := pow_le_three_pow_mul e (Nat.le_add_right dN dE)
    have p₂ := pow_le_three_pow_mul e (Nat.le_add_left dE dN)
    rw [Nat.add_mul]
    exact Nat.add_le_add ((h₁ _).trans (Nat.mul_le_mul_left _ p₁))
      ((h₂ _).trans (Nat.mul_le_mul_left _ p₂))
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold reader (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [reader, InputReader.read])
    (encA := encBool) (encE := encBits) (encF := encBits) (fun x => x) (fun x => by simp)
    hinit hN hE hfinish (g := g) (fun x => by simpa only [encBits_apply] using hg x)
    (tMax := fun x => (cN + cE) * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)))
    (sMax := fun x => (cN' + cE') * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)))
    (lMax := fun x => lMax x + 1)
    (fun x j hj => hround x j hj cN cE tN tE htN htE)
    (fun x j hj => hround x j hj cN' cE' sN sE hsN hsE)
    (fun x j hj => (hS x j hj).trans (Nat.le_succ _))
    (fun x j hj => by rw [encBool_apply, List.length_singleton]; omega)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = (cN + cE + cN' + cE') * 3 ^ (dN + dE) := ⟨_, rfl⟩
  have hA : (cN + cE) * 3 ^ (dN + dE) ≤ C₀ := hC₀ ▸ Nat.mul_le_mul_right _ (by omega)
  have hB : (cN' + cE') * 3 ^ (dN + dE) ≤ C₀ := hC₀ ▸ Nat.mul_le_mul_right _ (by omega)
  refine ⟨c * (C₀ + 4), dN + dE + 1, h.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [encBits_apply]
    generalize tI x = a, tF (streamState (init x) next x x.length) = b, x.length = L
    have hY : (lMax x + 1) ^ (dN + dE) ≤ (lMax x + 1) ^ (dN + dE + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hl : lMax x + 1 ≤ (lMax x + 1) ^ (dN + dE + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : (cN + cE) * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)) ≤
        C₀ * (lMax x + 1) ^ (dN + dE + 1) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul hA hY
    generalize (lMax x + 1) ^ (dN + dE + 1) = Z at hl h3
    generalize (cN + cE) * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)) = W at h3
    rw [Nat.mul_assoc c]
    apply Nat.mul_le_mul_left c
    nlinarith
  · generalize sI x = a, sF (streamState (init x) next x x.length) = b
    have hY : (lMax x + 1) ^ (dN + dE) ≤ (lMax x + 1) ^ (dN + dE + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hl : lMax x + 1 ≤ (lMax x + 1) ^ (dN + dE + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : (cN' + cE') * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)) ≤
        C₀ * (lMax x + 1) ^ (dN + dE + 1) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul hB hY
    generalize (lMax x + 1) ^ (dN + dE + 1) = Z at hl h3
    generalize (cN' + cE') * (3 ^ (dN + dE) * (lMax x + 1) ^ (dN + dE)) = W at h3
    rw [Nat.mul_assoc c]
    apply Nat.mul_le_mul_left c
    nlinarith



/-! ### Computing the dimension in a pass -/

/-- The state of a pass: the dimension, in unary, and the parser state. -/
private abbrev LCSPassState : Type := ℕ × LCSParseState

/-- The encoding of a pass state. -/
private abbrev encLCSPassState : LCSPassState ↪ List Bool := encPair encUnary encLCSParseState

/-- The initial state of a pass on an encoded instance. -/
private def LCS.passInit (x : List Bool) : LCSPassState := (LCS.dimOf x, LCS.parseStart)

/-- The output of the dimension pass. -/
private def LCS.dimFinish (q : LCSParseState × ℕ) : List Bool :=
  encLCSPassState (q.2, LCS.parseStart)

private theorem dimStep_bound (s : LCSParseState) (m : ℕ) (b : Bool) :
    max (LCS.dimStep ((s, m), b)).2
      ((LCS.dimStep ((s, m), b)).1.1.2 + (LCS.dimStep ((s, m), b)).1.2) ≤
      max m (s.1.2 + s.2) + 1 := by
  have h := lcsParseStep_le s b
  have h₁ : (LCS.dimStep ((s, m), b)).1 = lcsParseStep (s, b) := rfl
  have h₂ : (LCS.dimStep ((s, m), b)).2 = m ∨ (LCS.dimStep ((s, m), b)).2 = s.1.2 + 1 := by
    change (if _ then _ else _) = _ ∨ (if _ then _ else _) = _
    split_ifs <;> simp
  rw [h₁]
  rcases h₂ with h₂ | h₂ <;> rw [h₂] <;> simp only [Nat.max_def] <;> split_ifs <;> omega

private theorem foldl_dimStep_bound (l : List Bool) (s : LCSParseState) (m : ℕ) :
    max (l.foldl (fun q b => LCS.dimStep (q, b)) (s, m)).2
      ((l.foldl (fun q b => LCS.dimStep (q, b)) (s, m)).1.1.2 +
        (l.foldl (fun q b => LCS.dimStep (q, b)) (s, m)).1.2) ≤ max m (s.1.2 + s.2) + l.length := by
  induction l generalizing s m with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons]
    have h₁ := ih (LCS.dimStep ((s, m), b)).1 (LCS.dimStep ((s, m), b)).2
    have h₂ := dimStep_bound s m b
    simp only [Prod.mk.eta, List.length_cons] at h₁ ⊢
    omega

open ComputableInPolyTime in
private theorem tA : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool => q.1.1.1.2 + 1)
      (encPair (encPair encLCSParseState encNat) encBool) encNat := by
  fun_prop

open ComputableInPolyTime in
private theorem tB : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool =>
      (q.1.1.1.1.1.1 || q.1.1.1.1.1.2) && q.1.1.1.1.2)
      (encPair (encPair encLCSParseState encNat) encBool) encBool := by
  fun_prop

open ComputableInPolyTime in
private theorem tC : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool =>
      decide (q.1.2 < q.1.1.1.2 + 1))
      (encPair (encPair encLCSParseState encNat) encBool) encBool :=
  binary_lt' (by fun_prop) tA

open ComputableInPolyTime in
private theorem computableInPolyTime_dimStep :
    ComputableInPolyTime LCS.dimStep (encPair (encPair encLCSParseState encNat) encBool)
      (encPair encLCSParseState encNat) := by
  have hs : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool => (q.1.1, q.2))
      (encPair (encPair encLCSParseState encNat) encBool) (encPair encLCSParseState encBool) := by
    fun_prop
  have hstep := ComputableInPolyTime.comp' (f := lcsParseStep)
    (g := fun q : (LCSParseState × ℕ) × Bool => (q.1.1, q.2)) computableInPolyTime_lcsParseStep hs
  have hc : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool =>
      (q.1.1.1.1.1.1 || q.1.1.1.1.1.2) && q.1.1.1.1.2 && decide (q.1.2 < q.1.1.1.2 + 1))
      (encPair (encPair encLCSParseState encNat) encBool) encBool :=
    ComputableInPolyTime.bool_and' tB tC
  have hm0 : ComputableInPolyTime (fun q : (LCSParseState × ℕ) × Bool => q.1.2)
      (encPair (encPair encLCSParseState encNat) encBool) encNat := by
    fun_prop
  exact hstep.prod (ite' hc tA hm0)


/-- A power of a quantity bounded by a multiple of `X ≥ 1`. -/
private theorem pow_le_mul_pow {a X c n D : ℕ} (ha : a ≤ c * X) (hX : 1 ≤ X) (hn : n ≤ D) :
    a ^ n ≤ c ^ n * X ^ D :=
  calc a ^ n ≤ (c * X) ^ n := Nat.pow_le_pow_left ha n
    _ = c ^ n * X ^ n := Nat.mul_pow _ _ _
    _ ≤ c ^ n * X ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hn)

private theorem streamEmit_nil {σ α : Type*} (next : σ × α → σ) (s : σ) (l : List α) :
    streamEmit next (fun _ => []) s l = [] := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [streamEmit, ih]

private theorem size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private theorem streamState_dimStep (x : List Bool) (j : ℕ) :
    streamState (LCS.parseStart, 0) LCS.dimStep x j =
      (streamState LCS.parseStart lcsParseStep x j,
        (streamState (LCS.parseStart, 0) LCS.dimStep x j).2) := by
  simp only [streamState]
  rw [foldl_dimStep]

private theorem snd_streamState_dimStep_le (x : List Bool) (j : ℕ) :
    (streamState (LCS.parseStart, 0) LCS.dimStep x j).2 ≤ x.length := by
  have := foldl_dimStep_bound (x.take j) LCS.parseStart 0
  simp only [streamState, List.length_take] at this ⊢
  omega

private theorem dimOf_le (x : List Bool) : LCS.dimOf x ≤ x.length := by
  have := snd_streamState_dimStep_le x x.length
  simpa [streamState, LCS.dimOf] using this

private theorem length_encDimState_le (x : List Bool) (j : ℕ) :
    (encPair encLCSParseState encNat (streamState (LCS.parseStart, 0) LCS.dimStep x j)).length ≤
      87 + 7 * Nat.size x.length := by
  rw [streamState_dimStep, length_encPair]
  dsimp only
  have h₁ : (encLCSParseState (streamState LCS.parseStart lcsParseStep x j)).length ≤
      43 + 3 * Nat.size x.length := length_encLCSParseState_streamState_le x j
  have h₂ := Nat.size_le_size (snd_streamState_dimStep_le x j)
  simp only [encNat_apply, Nat.size_eq_bits_len]
  omega

open ComputableInPolyTime in
/-- **The dimension pass**: the initial state of a pass is computable within time
`O(L (log L) ^ K)`. -/
private theorem exists_tidy_initB : ∃ c K,
    ComputableTidilyInTimeAndSpace LCS.passInit encBits encLCSPassState
    (fun x => c * ((x.length + 1) * (Nat.size x.length + 1) ^ K))
    (fun x => c * ((x.length + 1) * (Nat.size x.length + 1) ^ K)) := by
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encPair encLCSParseState encNat) (LCS.parseStart, 0)
  have hI' := hI.computableTidilyInTimeAndSpace
  have hemit : ComputableInPolyTime (fun _ : (LCSParseState × ℕ) × Bool => ([] : List Bool))
      (encPair (encPair encLCSParseState encNat) encBool) encBits := ComputableInPolyTime.const _
  have hfinO : ComputableInO LCS.dimFinish (encPair encLCSParseState encNat) encBits
      (fun q => (encPair encLCSParseState encNat q).length + q.2 +
        (encPair encLCSParseState encNat q).length)
      (fun q => (encPair encLCSParseState encNat q).length + q.2 +
        (encPair encLCSParseState encNat q).length) :=
    ((ComputableInO.natToUnary.comp (ComputableInO.snd encLCSParseState encNat)).prod
      (ComputableInO.const (encIn := encPair encLCSParseState encNat)
        (encMid := encLCSParseState) LCS.parseStart)).of_enc_eq
      (g := LCS.dimFinish) (encC := encBits) (fun q => by simp [LCS.dimFinish, encBits_apply])
  obtain ⟨cF, hF, -⟩ := hfinO.tidy
  obtain ⟨c, K, h⟩ := bitStream (init := fun _ => (LCS.parseStart, 0)) hI'
    computableInPolyTime_dimStep hemit hF (g := LCS.passInit) (encOut := encLCSPassState)
    (fun x => by
      rw [streamEmit_nil, List.nil_append]
      simp [LCS.passInit, LCS.dimFinish, LCS.dimOf, streamState])
    (fun x => 87 + 7 * Nat.size x.length) (fun x j _ => length_encDimState_le x j)
  refine ⟨c * (2 * cI + 2 + 200 * cF + 88 ^ K), K, h.mono (fun x => ?_) (fun x => ?_)⟩
  all_goals
    beta_reduce
    have hl := length_encDimState_le x x.length
    have hm := snd_streamState_dimStep_le x x.length
    have hZ := size_le_self x.length
    have hY : 1 ≤ (Nat.size x.length + 1) ^ K := Nat.one_le_pow _ _ (by omega)
    have hp : (87 + 7 * Nat.size x.length + 1) ^ K ≤ 88 ^ K * (Nat.size x.length + 1) ^ K :=
      pow_le_mul_pow (by omega) (by omega) le_rfl
    generalize (encPair encLCSParseState encNat
      (streamState (LCS.parseStart, 0) LCS.dimStep x x.length)).length = E at hl
    generalize (streamState (LCS.parseStart, 0) LCS.dimStep x x.length).2 = m at hm
    generalize (Nat.size x.length + 1) ^ K = Y at hY hp
    generalize Nat.size x.length = Z at hl hZ hp
    generalize x.length = L at hl hm hZ
    simp only [Nat.mul_assoc c]
    apply Nat.mul_le_mul_left c
    have h1 : (2 * cI + 2) ≤ (2 * cI + 2) * ((L + 1) * Y) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hY)
    have h2 : cF * (E + m + E + 1) ≤ 200 * cF * ((L + 1) * Y) := by
      have : E + m + E + 1 ≤ 200 * ((L + 1) * Y) := by
        have : L + 1 ≤ (L + 1) * Y := Nat.le_mul_of_pos_right _ hY
        omega
      calc cF * (E + m + E + 1) ≤ cF * (200 * ((L + 1) * Y)) := Nat.mul_le_mul_left _ this
        _ = 200 * cF * ((L + 1) * Y) := by ring
    have h3 : (L + 1) * (87 + 7 * Z + 1) ^ K ≤ 88 ^ K * ((L + 1) * Y) :=
      calc (L + 1) * (87 + 7 * Z + 1) ^ K ≤ (L + 1) * (88 ^ K * Y) := Nat.mul_le_mul_left _ hp
        _ = 88 ^ K * ((L + 1) * Y) := by ring
    have h4 : (87 + 7 * Z + 1) ^ K ≤ 88 ^ K * ((L + 1) * Y) :=
      hp.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))
    nlinarith

/-! ### The passes -/

/-- A round of a pass: the dimension is kept and the parser reads a bit. -/
private def LCS.passNext (q : LCSPassState × Bool) : LCSPassState :=
  (q.1.1, lcsParseStep (q.1.2, q.2))

private theorem streamState_lcsPassNext (d : ℕ) (s : LCSParseState) (l : List Bool) (j : ℕ) :
    streamState (d, s) LCS.passNext l j = (d, streamState s lcsParseStep l j) := by
  simp only [streamState]
  generalize l.take j = l'
  induction l' generalizing s with
  | nil => rfl
  | cons b l ih => exact ih _

private theorem streamEmit_lcsPassNext {enc : β ↪ List Bool} (f : ℕ → Bool → ℕ → ℕ → Bool → List β)
    (g : ℕ → Bool → ℕ → ℕ → List β) (d : ℕ) (s : LCSParseState) (l : List Bool) :
    streamEmit LCS.passNext (fun q => encList enc (lcsParseEmit (f q.1.1) (g q.1.1) (q.1.2, q.2)))
      (d, s) l = encList enc (lcsParseRun (f d) (g d) s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    rw [streamEmit, lcsParseRun, encList_append]
    exact congrArg _ (ih _)

/-- The time bound of the passes: `L ((d + 1) (log L + 1)) ^ D` on `N` vectors of dimension `d`
encoded in length `L`. -/
private def LCS.passBound (D : ℕ) (p : List (List Bool) × List (List Bool)) : ℕ :=
  ((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D

private theorem passBound_mono {D D' : ℕ} (h : D ≤ D') (p : List (List Bool) × List (List Bool)) :
    LCS.passBound D p ≤ LCS.passBound D' p :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (by omega)) h)

open ComputableInPolyTime in
private theorem computableInPolyTime_lcsPassNext :
    ComputableInPolyTime LCS.passNext (encPair encLCSPassState encBool) encLCSPassState := by
  have hs : ComputableInPolyTime (fun q : LCSPassState × Bool => (q.1.2, q.2))
      (encPair encLCSPassState encBool) (encPair encLCSParseState encBool) := by fun_prop
  have hd : ComputableInPolyTime (fun q : LCSPassState × Bool => q.1.1)
      (encPair encLCSPassState encBool) encUnary := by fun_prop
  exact hd.prod (ComputableInPolyTime.comp' (f := lcsParseStep)
    (g := fun q : LCSPassState × Bool => (q.1.2, q.2)) computableInPolyTime_lcsParseStep hs)

open ComputableInPolyTime in
/-- **A pass over an encoded instance** with polynomial-time rounds and finish, whose state holds
the dimension in unary, runs within the time `LCS.passBound D`. -/
private theorem computableInO_pass {ω : Type} {encOut : ω ↪ List Bool}
    {emit : LCSPassState × Bool → List Bool} {fin : LCSPassState → List Bool}
    {g : List (List Bool) × List (List Bool) → ω}
    (hemit : ComputableInPolyTime emit (encPair encLCSPassState encBool) encBits)
    (hfin : ComputableInPolyTime fin encLCSPassState encBits)
    (hg : ∀ p, encOut (g p) = streamEmit LCS.passNext emit (OV.dim p, LCS.parseStart) (encOV p) ++
      fin (OV.dim p, streamState LCS.parseStart lcsParseStep (encOV p) (encOV p).length)) :
    ∃ D, ComputableInO g encOV encOut (LCS.passBound D) (LCS.passBound D) := by
  obtain ⟨cA, KA, hA⟩ := exists_tidy_initB
  obtain ⟨dF, _, hF_deg⟩ := hfin.exists_degree
  obtain ⟨tF, sF, ⟨cF, htF⟩, ⟨cF', hsF⟩, hF⟩ := Internal.NormalForm.degree hF_deg
  have hS (x : List Bool) (j : ℕ) (_ : j ≤ x.length) :
      (encLCSPassState (streamState (LCS.passInit x) LCS.passNext x j)).length ≤
        2 * LCS.dimOf x + 44 + 3 * Nat.size x.length := by
    rw [LCS.passInit, streamState_lcsPassNext, length_encPair]
    dsimp only
    have h₁ : (encLCSParseState (streamState LCS.parseStart lcsParseStep x j)).length ≤
        43 + 3 * Nat.size x.length := length_encLCSParseState_streamState_le x j
    rw [encUnary_apply, List.length_replicate]
    omega
  obtain ⟨c, K, h⟩ := bitStream hA computableInPolyTime_lcsPassNext hemit hF
    (g := fun x => streamEmit LCS.passNext emit (LCS.passInit x) x ++
      fin (streamState (LCS.passInit x) LCS.passNext x x.length))
    (encOut := encBits) (fun x => by rw [encBits_apply]) _ hS
  set D := KA + K + dF with hD
  -- the bound in terms of the encoded instance
  have key (x : List Bool) (cc : ℕ) (u : LCSPassState → ℕ)
      (hu : ∀ a, u a ≤ cc * ((encLCSPassState a).length + 1) ^ dF) :
      c * (cA * ((x.length + 1) * (Nat.size x.length + 1) ^ KA) +
        u (streamState (LCS.passInit x) LCS.passNext x x.length) +
        (x.length + 1) * (2 * LCS.dimOf x + 44 + 3 * Nat.size x.length + 1) ^ K) ≤
      c * (cA + cc * 45 ^ dF + 45 ^ K) *
        ((x.length + 1) * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D) := by
    have hX : 1 ≤ (LCS.dimOf x + 1) * (Nat.size x.length + 1) := Nat.mul_pos (by omega) (by omega)
    have hZX : Nat.size x.length + 1 ≤ (LCS.dimOf x + 1) * (Nat.size x.length + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hdX : LCS.dimOf x + 1 ≤ (LCS.dimOf x + 1) * (Nat.size x.length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hℓ : 2 * LCS.dimOf x + 44 + 3 * Nat.size x.length + 1 ≤
        45 * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) := by omega
    have p1 : (Nat.size x.length + 1) ^ KA ≤
        1 ^ KA * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D :=
      pow_le_mul_pow (by omega) hX (by omega)
    have hu' := hu (streamState (LCS.passInit x) LCS.passNext x x.length)
    have hl := hS x x.length le_rfl
    have p2 :
        ((encLCSPassState (streamState (LCS.passInit x) LCS.passNext x x.length)).length + 1) ^ dF ≤
        45 ^ dF * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D :=
      pow_le_mul_pow (by omega) hX (by omega)
    have p3 : (2 * LCS.dimOf x + 44 + 3 * Nat.size x.length + 1) ^ K ≤
        45 ^ K * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D :=
      pow_le_mul_pow hℓ hX (by omega)
    rw [one_pow, one_mul] at p1
    generalize ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D = Y at p1 p2 p3
    generalize u (streamState (LCS.passInit x) LCS.passNext x x.length) = U at hu'
    generalize
      ((encLCSPassState (streamState (LCS.passInit x) LCS.passNext x x.length)).length + 1) ^ dF
      = P at hu' p2
    generalize (2 * LCS.dimOf x + 44 + 3 * Nat.size x.length + 1) ^ K = Q at p3
    generalize (Nat.size x.length + 1) ^ KA = R at p1
    have hU : U ≤ cc * 45 ^ dF * Y := by
      calc U ≤ cc * P := hu'
        _ ≤ cc * (45 ^ dF * Y) := Nat.mul_le_mul_left _ p2
        _ = cc * 45 ^ dF * Y := by ring
    rw [Nat.mul_assoc c]
    apply Nat.mul_le_mul_left c
    have h1 : cA * ((x.length + 1) * R) ≤ cA * ((x.length + 1) * Y) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p1)
    have h2 : (x.length + 1) * Q ≤ 45 ^ K * ((x.length + 1) * Y) := by
      calc (x.length + 1) * Q ≤ (x.length + 1) * (45 ^ K * Y) := Nat.mul_le_mul_left _ p3
        _ = 45 ^ K * ((x.length + 1) * Y) := by ring
    have h3 : cc * 45 ^ dF * Y ≤ cc * 45 ^ dF * ((x.length + 1) * Y) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    nlinarith
  have h' : ComputableInO (fun x => streamEmit LCS.passNext emit (LCS.passInit x) x ++
      fin (streamState (LCS.passInit x) LCS.passNext x x.length)) encBits encBits
      (fun x => (x.length + 1) * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D)
      (fun x => (x.length + 1) * ((LCS.dimOf x + 1) * (Nat.size x.length + 1)) ^ D) := by
    refine ComputableInO.of_bounds h.computableInTimeAndSpace
      (c * (cA + cF * 45 ^ dF + 45 ^ K) + c * (cA + cF' * 45 ^ dF + 45 ^ K))
      (fun x => ?_) (fun x => ?_) (fun x => ?_)
    · exact (key x cF tF htF).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))
    · refine le_trans ?_ ((key x cF' sF hsF).trans
        (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_succ _)))
      exact Nat.mul_le_mul_left c (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _)
    · exact ((h.computableInTimeAndSpace.length_le x).trans (key x cF tF htF)).trans
        (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))
  refine ⟨D, ((h'.of_encIn_eq (encD := encOV) (fun p => encOV p) (fun _ => rfl)).of_enc_eq
    (g := g) (encC := encOut) (fun p => ?_)).mono_le (fun p => ?_) (fun p => ?_)⟩
  · simp only [Function.comp_apply, encBits_apply, hg p, LCS.passInit, dimOf_encOV,
      streamState_lcsPassNext]
  · simp only [Function.comp_apply, dimOf_encOV, LCS.passBound, le_refl]
  · simp only [Function.comp_apply, dimOf_encOV, LCS.passBound, le_refl]

open ComputableInPolyTime in
/-- The emission of a pass round is polynomial-time when the outputs of the bits and of the ends
of the vectors are. -/
private theorem computableInPolyTime_lcsPassEmit {enc : β ↪ List Bool}
    {f : ℕ → Bool → ℕ → ℕ → Bool → List β} {g : ℕ → Bool → ℕ → ℕ → List β}
    (hf : ComputableInPolyTime
      (fun q : LCSPassState × Bool => f q.1.1 q.1.2.1.1.1.1 q.1.2.2 q.1.2.1.2 q.2)
      (encPair encLCSPassState encBool) (encList enc))
    (hg : ComputableInPolyTime
      (fun q : LCSPassState × Bool => g q.1.1 q.1.2.1.1.1.1 q.1.2.2 q.1.2.1.2)
      (encPair encLCSPassState encBool) (encList enc)) :
    ComputableInPolyTime
      (fun q : LCSPassState × Bool => encList enc (lcsParseEmit (f q.1.1) (g q.1.1) (q.1.2, q.2)))
      (encPair encLCSPassState encBool) encBits := by
  have hnil : ComputableInPolyTime (fun _ : LCSPassState × Bool => ([] : List β))
      (encPair encLCSPassState encBool) (encList enc) := ComputableInPolyTime.const _
  have hc₁ : ComputableInPolyTime (fun q : LCSPassState × Bool => !q.1.2.1.1.1.1 && !q.1.2.1.1.1.2)
      (encPair encLCSPassState encBool) encBool := by fun_prop
  have hc₂ : ComputableInPolyTime (fun q : LCSPassState × Bool => q.1.2.1.1.2)
      (encPair encLCSPassState encBool) encBool := by fun_prop
  have hc₃ : ComputableInPolyTime (fun q : LCSPassState × Bool => q.2)
      (encPair encLCSPassState encBool) encBool := by fun_prop
  exact encoding_comp (ite' hc₁ hnil (ite' hc₂ hf (ite' hc₃ hnil hg)))



private theorem intercalate_eq_headD_append {α : Type*} (sep : List α) (L : List (List α)) :
    sep.intercalate L = L.headD [] ++ L.tail.flatMap (fun l => sep ++ l) := by
  rcases L with _ | ⟨l, rest⟩
  · rfl
  · induction rest generalizing l with
    | nil => simp
    | cons l' r ih =>
      rw [List.intercalate_cons_cons, ih]
      simp [List.append_assoc]

open ComputableInPolyTime in
private theorem computableInPolyTime_CG1 :
    ComputableInPolyTime LCS.CG1 encBool (encList encLCSSymbol) := by
  unfold LCS.CG1
  fun_prop

open ComputableInPolyTime in
private theorem computableInPolyTime_CG2 :
    ComputableInPolyTime LCS.CG2 encBool (encList encLCSSymbol) := by
  unfold LCS.CG2
  fun_prop

private theorem bits_list :
    ComputableInPolyTime (fun w : List Bool => w) encBits (encList encBool) :=
  (bits_encList_polyTime encBool).1

open ComputableInPolyTime in
private theorem computableInPolyTime_R1 :
    ComputableInPolyTime LCS.R1 encBits (encList encLCSSymbol) := by
  have e : LCS.R1 = fun a => a.flatMap LCS.CG1 := funext fun a => by
    simp [LCS.R1, List.flatMap]
  rw [e]
  exact flatMapWithInput (list := fun a => a) bits_list
    (computableInPolyTime_CG1.comp (snd encBits encBool))

open ComputableInPolyTime in
private theorem computableInPolyTime_R2 :
    ComputableInPolyTime LCS.R2 encBits (encList encLCSSymbol) := by
  have e : LCS.R2 = fun a => a.flatMap LCS.CG2 := funext fun a => by
    simp [LCS.R2, List.flatMap]
  rw [e]
  exact flatMapWithInput (list := fun a => a) bits_list
    (computableInPolyTime_CG2.comp (snd encBits encBool))

open ComputableInPolyTime in
private theorem computableInPolyTime_VG1' :
    ComputableInPolyTime (fun q : ℕ × List Bool => LCS.VG1' q.1 q.2)
      (encPair encUnary encBits) (encList encLCSSymbol) := by
  have := computableInPolyTime_R1
  unfold LCS.VG1' LCS.M LCS.W
  fun_prop


open ComputableInPolyTime in
private theorem computableInPolyTime_VG2' :
    ComputableInPolyTime (fun q : ℕ × List Bool => LCS.VG2' q.1 q.2)
      (encPair encUnary encBits) (encList encLCSSymbol) := by
  have := computableInPolyTime_R2
  unfold LCS.VG2' LCS.M LCS.W
  fun_prop

private theorem foldl_max_eq (l : List ℕ) (a : ℕ) : l.foldl max a = max a (l.foldr max 0) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.foldr_cons, Nat.max_assoc]

open ComputableInPolyTime in
private theorem computableInPolyTime_P1 :
    ComputableInPolyTime (fun q : ℕ × List (List Bool) => LCS.P1 q.1 q.2)
      (encPair encUnary (encList encBits)) (encList encLCSSymbol) := by
  have e : (fun q : ℕ × List (List Bool) => LCS.P1 q.1 q.2) = fun q =>
      List.replicate (3 * q.2.length * (10 * q.1 + 10)) s3 ++
        (q.2.flatMap (fun a => LCS.VG1' q.1 a) ++
          List.replicate (3 * q.2.length * (10 * q.1 + 10)) s3) :=
    funext fun q => by simp only [LCS.P1, LCS.sepLen, List.flatMap, List.append_assoc]
  rw [e]
  have hq : ComputableInPolyTime (fun p : (ℕ × List (List Bool)) × List Bool => (p.1.1, p.2))
      (encPair (encPair encUnary (encList encBits)) encBits) (encPair encUnary encBits) := by
    fun_prop
  have hV : ComputableInPolyTime (fun p : (ℕ × List (List Bool)) × List Bool => LCS.VG1' p.1.1 p.2)
      (encPair (encPair encUnary (encList encBits)) encBits) (encList encLCSSymbol) :=
    ComputableInPolyTime.comp' (f := fun q : ℕ × List Bool => LCS.VG1' q.1 q.2)
      (g := fun p : (ℕ × List (List Bool)) × List Bool => (p.1.1, p.2))
      computableInPolyTime_VG1' hq
  have hR : ComputableInPolyTime
      (fun q : ℕ × List (List Bool) => List.replicate (3 * q.2.length * (10 * q.1 + 10)) s3)
      (encPair encUnary (encList encBits)) (encList encLCSSymbol) := by
    fun_prop
  exact listAppend' hR (listAppend' (flatMapWithInput
    (f := fun (q : ℕ × List (List Bool)) (a : List Bool) => LCS.VG1' q.1 a)
    (snd _ _) hV) hR)

open ComputableInPolyTime in
private theorem computableInPolyTime_P2 :
    ComputableInPolyTime (fun q : ℕ × List (List Bool) => LCS.P2 q.1 q.2)
      (encPair encUnary (encList encBits)) (encList encLCSSymbol) := by
  have e : (fun q : ℕ × List (List Bool) => LCS.P2 q.1 q.2) = fun q =>
      (LCS.P2Blocks q.1 q.2).headD [] ++ (LCS.P2Blocks q.1 q.2).tail.flatMap
        (fun l => List.replicate (10 * q.1 + 10) s3 ++ l) :=
    funext fun q => by
      simp only [LCS.P2, LCS.sepLen]
      exact intercalate_eq_headD_append _ _
  rw [e]
  have hD : ComputableInPolyTime (fun q : ℕ × List (List Bool) => LCS.DummyBlock q.1)
      (encPair encUnary (encList encBits)) (encList encLCSSymbol) := by
    unfold LCS.DummyBlock LCS.M LCS.W; fun_prop
  have hq : ComputableInPolyTime (fun p : (ℕ × List (List Bool)) × List Bool => (p.1.1, p.2))
      (encPair (encPair encUnary (encList encBits)) encBits) (encPair encUnary encBits) := by
    fun_prop
  have hV : ComputableInPolyTime (fun p : (ℕ × List (List Bool)) × List Bool => LCS.VG2' p.1.1 p.2)
      (encPair (encPair encUnary (encList encBits)) encBits) (encList encLCSSymbol) :=
    ComputableInPolyTime.comp' (f := fun q : ℕ × List Bool => LCS.VG2' q.1 q.2)
      (g := fun p : (ℕ × List (List Bool)) × List Bool => (p.1.1, p.2))
      computableInPolyTime_VG2' hq
  have hn : ComputableInPolyTime (fun q : ℕ × List (List Bool) => q.2.length)
      (encPair encUnary (encList encBits)) encUnary := by fun_prop
  have hB : ComputableInPolyTime (fun q : ℕ × List (List Bool) => LCS.P2Blocks q.1 q.2)
      (encPair encUnary (encList encBits)) (encList (encList encLCSSymbol)) := by
    unfold LCS.P2Blocks
    exact listAppend' (listAppend' (replicate hn hD)
      (mapWithInput
        (f := fun (q : ℕ × List (List Bool)) (a : List Bool) => LCS.VG2' q.1 a) (snd _ _) hV))
      (replicate hn hD)
  have hS : ComputableInPolyTime
      (fun p : (ℕ × List (List Bool)) × List LCSSymbol =>
        List.replicate (10 * p.1.1 + 10) s3 ++ p.2)
      (encPair (encPair encUnary (encList encBits)) (encList encLCSSymbol))
      (encList encLCSSymbol) := by
    fun_prop
  exact listAppend' ((headD []).comp hB)
    (flatMapWithInput (f := fun (q : ℕ × List (List Bool)) (l : List LCSSymbol) =>
        List.replicate (10 * q.1 + 10) s3 ++ l)
      ((tail (encA := encList encLCSSymbol)).comp hB) hS)

open ComputableInPolyTime in
private theorem computableInPolyTime_dim :
    ComputableInPolyTime OV.dim encOV encUnary := by
  have e : OV.dim = fun p => ((p.1 ++ p.2).map List.length).foldl max 0 := funext fun p => by
    rw [OV.dim, listMax, foldl_max_eq, Nat.zero_max]
  rw [e]
  exact (unary_foldl_max 0).comp (by unfold encOV; fun_prop)


/-! ### The passes of the reduction -/

private theorem flatMap_const_eq {α γ : Type*} (l : List α) (c : List γ) :
    l.flatMap (fun _ => c) = (List.replicate l.length c).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

/-- Separated blocks without their first separator are the intercalated blocks. -/
private theorem drop_flatMap_append {α : Type*} (sep : List α) (L : List (List α)) {n : ℕ}
    (hn : sep.length = n) :
    (L.flatMap (fun l => sep ++ l)).drop n = sep.intercalate L := by
  subst hn
  rcases L with _ | ⟨l, rest⟩
  · simp
  · rw [List.flatMap_cons, List.append_assoc, List.drop_left, intercalate_eq_headD_append]
    rfl

private theorem flatMap_eq_map_flatten {α γ : Type*} (l : List α) (f g : α → List γ)
    (h : ∀ a, f a = g a) : l.flatMap f = (l.map g).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, h, ih]

/-- No output for the bits of the vectors. -/
private def LCS.noBits (_ : ℕ) (_ : Bool) (_ _ : ℕ) (_ : Bool) : List LCSSymbol := []

/-- The pass for the `s3` runs of `LCS.P1`: a run of length `3 (10 d + 10)` at the end of each
vector of `A`. -/
private def LCS.runEnd (d : ℕ) (side : Bool) (_ _ : ℕ) : List LCSSymbol :=
  if side then [] else List.replicate (3 * LCS.sepLen d) s3

/-- The pass for the blocks of `LCS.P1`: the bits of the vectors of `A`. -/
private def LCS.blockBits (d : ℕ) (side : Bool) (_ i : ℕ) (b : Bool) : List LCSSymbol :=
  if side then [] else
    (if i = 0 then List.replicate (LCS.M d) s0 ++ List.replicate (LCS.W d) s1 else []) ++
      LCS.CG1 b

/-- The pass for the blocks of `LCS.P1`: the ends of the vectors of `A`. -/
private def LCS.blockEnd (d : ℕ) (side : Bool) (_ i : ℕ) : List LCSSymbol :=
  if side then [] else
    (if i = 0 then List.replicate (LCS.M d) s0 ++ List.replicate (LCS.W d) s1 else []) ++
      List.replicate (LCS.M d) s2

/-- The pass for the dummy blocks of `LCS.P2`: a separator and a dummy block at the end of each
vector of `B`. -/
private def LCS.dummyEnd (d : ℕ) (side : Bool) (_ _ : ℕ) : List LCSSymbol :=
  if side then List.replicate (LCS.sepLen d) s3 ++ LCS.DummyBlock d else []

/-- The pass for the vector blocks of `LCS.P2`: the bits of the vectors of `B`. -/
private def LCS.blockBits₂ (d : ℕ) (side : Bool) (_ i : ℕ) (b : Bool) : List LCSSymbol :=
  if side then
    (if i = 0 then List.replicate (LCS.sepLen d) s3 ++ List.replicate (LCS.M d) s0 else []) ++
      LCS.CG2 b
  else []

/-- The pass for the vector blocks of `LCS.P2`: the ends of the vectors of `B`. -/
private def LCS.blockEnd₂ (d : ℕ) (side : Bool) (_ i : ℕ) : List LCSSymbol :=
  if side then
    (if i = 0 then List.replicate (LCS.sepLen d) s3 ++ List.replicate (LCS.M d) s0 else []) ++
      (List.replicate (LCS.W d) s1 ++ List.replicate (LCS.M d) s2)
  else []

private theorem lcsParseRun_runEnd (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    lcsParseRun (LCS.noBits d) (LCS.runEnd d) LCS.parseStart (encOV p) =
      List.replicate (3 * p.1.length * LCS.sepLen d) s3 := by
  rw [lcsParseRun_encOV]
  have h₁ : lcsVecsOut (LCS.noBits d false) (LCS.runEnd d false) 0 p.1 =
      p.1.flatMap (fun _ => List.replicate (3 * LCS.sepLen d) s3) :=
    lcsVecsOut_const _ 0 p.1
  have h₂ : lcsVecsOut (LCS.noBits d true) (LCS.runEnd d true) p.1.length p.2 = [] := by
    rw [show LCS.runEnd d true = fun _ _ => [] from rfl,
      show LCS.noBits d true = fun _ _ _ => [] from rfl,
      lcsVecsOut_const]
    simp
  rw [h₁, h₂, List.append_nil, flatMap_const_replicate]
  congr 1
  ring

private theorem lcsParseRun_block (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    lcsParseRun (LCS.blockBits d) (LCS.blockEnd d) LCS.parseStart (encOV p) =
      (p.1.map (LCS.VG1' d)).flatten := by
  rw [lcsParseRun_encOV]
  have h₁ : lcsVecsOut (LCS.blockBits d false) (LCS.blockEnd d false) 0 p.1 =
      p.1.flatMap (fun v => (List.replicate (LCS.M d) s0 ++ List.replicate (LCS.W d) s1) ++
        v.flatMap LCS.CG1 ++ List.replicate (LCS.M d) s2) :=
    lcsVecsOut_gadget _ _ _ 0 p.1
  have h₂ : lcsVecsOut (LCS.blockBits d true) (LCS.blockEnd d true) p.1.length p.2 = [] := by
    rw [show LCS.blockEnd d true = fun _ _ => [] from rfl,
      show LCS.blockBits d true = fun _ _ _ => [] from rfl, lcsVecsOut_const]
    simp
  rw [h₁, h₂, List.append_nil]
  exact flatMap_eq_map_flatten _ _ _ fun v => by
    simp [LCS.VG1', LCS.R1, List.flatMap, List.append_assoc]

private theorem lcsParseRun_dummy (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    lcsParseRun (LCS.noBits d) (LCS.dummyEnd d) LCS.parseStart (encOV p) =
      p.2.flatMap (fun _ => List.replicate (LCS.sepLen d) s3 ++ LCS.DummyBlock d) := by
  rw [lcsParseRun_encOV]
  have h₁ : lcsVecsOut (LCS.noBits d false) (LCS.dummyEnd d false) 0 p.1 = [] := by
    rw [show LCS.dummyEnd d false = fun _ _ => [] from rfl,
      show LCS.noBits d false = fun _ _ _ => [] from rfl, lcsVecsOut_const]
    simp
  have h₂ : lcsVecsOut (LCS.noBits d true) (LCS.dummyEnd d true) p.1.length p.2 =
      p.2.flatMap (fun _ => List.replicate (LCS.sepLen d) s3 ++ LCS.DummyBlock d) :=
    lcsVecsOut_const _ _ p.2
  rw [h₁, h₂, List.nil_append]

private theorem lcsParseRun_block₂ (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    lcsParseRun (LCS.blockBits₂ d) (LCS.blockEnd₂ d) LCS.parseStart (encOV p) =
      p.2.flatMap (fun v => List.replicate (LCS.sepLen d) s3 ++ LCS.VG2' d v) := by
  rw [lcsParseRun_encOV]
  have h₁ : lcsVecsOut (LCS.blockBits₂ d false) (LCS.blockEnd₂ d false) 0 p.1 = [] := by
    rw [show LCS.blockEnd₂ d false = fun _ _ => [] from rfl,
      show LCS.blockBits₂ d false = fun _ _ _ => [] from rfl, lcsVecsOut_const]
    simp
  have h₂ : lcsVecsOut (LCS.blockBits₂ d true) (LCS.blockEnd₂ d true) p.1.length p.2 =
      p.2.flatMap (fun v => (List.replicate (LCS.sepLen d) s3 ++ List.replicate (LCS.M d) s0) ++
        v.flatMap LCS.CG2 ++ (List.replicate (LCS.W d) s1 ++ List.replicate (LCS.M d) s2)) :=
    lcsVecsOut_gadget _ _ _ _ p.2
  rw [h₁, h₂, List.nil_append]
  refine (flatMap_eq_map_flatten _ _ _ fun v => ?_).trans
    (flatMap_eq_map_flatten _ _ _ fun _ => rfl).symm
  simp [LCS.VG2', LCS.R2, List.flatMap, List.append_assoc]

/-- `LCS.P1` from the passes. -/
private theorem P1_eq_passes (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    LCS.P1 d p.1 = lcsParseRun (LCS.noBits d) (LCS.runEnd d) LCS.parseStart (encOV p) ++
      (lcsParseRun (LCS.blockBits d) (LCS.blockEnd d) LCS.parseStart (encOV p) ++
        lcsParseRun (LCS.noBits d) (LCS.runEnd d) LCS.parseStart (encOV p)) := by
  rw [lcsParseRun_runEnd, lcsParseRun_block, LCS.P1]
  simp only [List.append_assoc]

/-- `LCS.P2` from the passes. -/
private theorem P2_eq_passes (d : ℕ) (p : List (List Bool) × List (List Bool)) :
    LCS.P2 d p.2 = (lcsParseRun (LCS.noBits d) (LCS.dummyEnd d) LCS.parseStart (encOV p) ++
      (lcsParseRun (LCS.blockBits₂ d) (LCS.blockEnd₂ d) LCS.parseStart (encOV p) ++
        lcsParseRun (LCS.noBits d) (LCS.dummyEnd d) LCS.parseStart (encOV p))).drop
          (LCS.sepLen d) := by
  rw [lcsParseRun_dummy, lcsParseRun_block₂, LCS.P2,
    ← drop_flatMap_append (List.replicate (LCS.sepLen d) s3) _ (List.length_replicate ..)]
  congr 1
  simp only [LCS.P2Blocks, List.flatMap_append, List.flatMap_replicate, flatMap_const_eq,
    List.flatMap_map, List.append_assoc]

/-! ### Assembling the passes -/

open ComputableInO in
private theorem ComputableInO.append_of {γ α : Type} {encIn : γ ↪ List Bool} {enc : α ↪ List Bool}
    {a b : γ → List α} {T : γ → ℕ}
    (ha : ComputableInO a encIn (encList enc) T T) (hb : ComputableInO b encIn (encList enc) T T) :
    ComputableInO (fun x => a x ++ b x) encIn (encList enc) T T := by
  obtain ⟨c₁, h₁⟩ := ha.length_le
  obtain ⟨c₂, h₂⟩ := hb.length_le
  refine (ComputableInO.comp' (f := fun q : List α × List α => q.1 ++ q.2)
    (append' (enc := enc)) (ha.prod hb)).mono (2 * c₁ + c₂ + 3) (fun x => ?_) (fun x => ?_) <;>
  · have := h₁ x
    have := h₂ x
    simp only [length_encPair]
    nlinarith

open ComputableInO in
private theorem ComputableInO.drop_of {γ α : Type} {encIn : γ ↪ List Bool} {enc : α ↪ List Bool}
    {l : γ → List α} {n : γ → ℕ} {T : γ → ℕ}
    (hl : ComputableInO l encIn (encList enc) T T) (hn : ComputableInO n encIn encUnary T T) :
    ComputableInO (fun x => (l x).drop (n x)) encIn (encList enc) T T := by
  obtain ⟨c₁, h₁⟩ := hl.length_le
  obtain ⟨c₂, h₂⟩ := hn.length_le
  refine (drop' hl hn).mono (2 * c₁ + c₂ + 3) (fun x => ?_) (fun x => ?_) <;>
  · have := h₁ x
    have := h₂ x
    simp only [length_encPair]
    nlinarith

open ComputableInPolyTime in
private theorem exists_computableInO_lcsRun {f : ℕ → Bool → ℕ → ℕ → Bool → List LCSSymbol}
    {g : ℕ → Bool → ℕ → ℕ → List LCSSymbol}
    (hf : ComputableInPolyTime
      (fun q : LCSPassState × Bool => f q.1.1 q.1.2.1.1.1.1 q.1.2.2 q.1.2.1.2 q.2)
      (encPair encLCSPassState encBool) (encList encLCSSymbol))
    (hg : ComputableInPolyTime
      (fun q : LCSPassState × Bool => g q.1.1 q.1.2.1.1.1.1 q.1.2.2 q.1.2.1.2)
      (encPair encLCSPassState encBool) (encList encLCSSymbol)) :
    ∃ D, ComputableInO (fun p => lcsParseRun (f (OV.dim p)) (g (OV.dim p)) LCS.parseStart (encOV p))
      encOV (encList encLCSSymbol) (LCS.passBound D) (LCS.passBound D) :=
  computableInO_pass (computableInPolyTime_lcsPassEmit hf hg) (ComputableInPolyTime.const [])
    (fun p => by rw [streamEmit_lcsPassNext, List.append_nil])

open ComputableInPolyTime in
/-- **The reduction from orthogonal vectors to longest common subsequence runs in time
`L ((d + 1) (log L + 1)) ^ D`** on `N` vectors of dimension `d` encoded in length `L`. -/
private theorem exists_computableInO_toLCS' : ∃ D, ComputableInO toLCS encOV
    (encPair (encList encLCSSymbol) (encList encLCSSymbol)) (LCS.passBound D)
      (LCS.passBound D) := by
  obtain ⟨D₁, hR⟩ := exists_computableInO_lcsRun (f := LCS.noBits) (g := LCS.runEnd)
    (by unfold LCS.noBits; fun_prop) (by unfold LCS.runEnd LCS.sepLen; fun_prop)
  obtain ⟨D₂, hM⟩ := exists_computableInO_lcsRun (f := LCS.blockBits) (g := LCS.blockEnd)
    (by unfold LCS.blockBits LCS.M LCS.W LCS.CG1; fun_prop)
    (by unfold LCS.blockEnd LCS.M LCS.W; fun_prop)
  obtain ⟨D₃, hX⟩ := exists_computableInO_lcsRun (f := LCS.noBits) (g := LCS.dummyEnd)
    (by unfold LCS.noBits; fun_prop)
    (by unfold LCS.dummyEnd LCS.sepLen LCS.DummyBlock LCS.M LCS.W; fun_prop)
  obtain ⟨D₄, hY⟩ := exists_computableInO_lcsRun (f := LCS.blockBits₂) (g := LCS.blockEnd₂)
    (by unfold LCS.blockBits₂ LCS.sepLen LCS.M LCS.CG2; fun_prop)
    (by unfold LCS.blockEnd₂ LCS.sepLen LCS.M LCS.W; fun_prop)
  obtain ⟨D₅, hN⟩ := computableInO_pass (emit := fun _ => [])
    (fin := fun q => encUnary (LCS.sepLen q.1))
    (g := fun p => LCS.sepLen (OV.dim p)) (encOut := encUnary) (ComputableInPolyTime.const _)
    (by unfold LCS.sepLen; fun_prop) (fun p => by rw [streamEmit_nil, List.nil_append])
  set D := D₁ + D₂ + D₃ + D₄ + D₅
  have w {γ : Type} {e : γ ↪ List Bool} {h : List (List Bool) × List (List Bool) → γ} {D' : ℕ}
      (hD : D' ≤ D) (hh : ComputableInO h encOV e (LCS.passBound D') (LCS.passBound D')) :
      ComputableInO h encOV e (LCS.passBound D) (LCS.passBound D) :=
    hh.mono_le (passBound_mono hD) (passBound_mono hD)
  have hR' := w (by omega) hR
  have hM' := w (by omega) hM
  have hX' := w (by omega) hX
  have hY' := w (by omega) hY
  have hN' := w (by omega) hN
  have hP1 : ComputableInO (fun p => (toLCS p).1) encOV (encList encLCSSymbol)
      (LCS.passBound D) (LCS.passBound D) :=
    (ComputableInO.append_of hR' (ComputableInO.append_of hM' hR')).of_enc_eq
      (fun p => by rw [toLCS, P1_eq_passes])
  have hP2 : ComputableInO (fun p => (toLCS p).2) encOV (encList encLCSSymbol)
      (LCS.passBound D) (LCS.passBound D) :=
    (ComputableInO.drop_of (ComputableInO.append_of hX' (ComputableInO.append_of hY' hX'))
      hN').of_enc_eq (fun p => by rw [toLCS, P2_eq_passes])
  refine ⟨D, ((hP1.prod hP2).mono 2 (fun p => by omega) (fun p => by omega)).of_enc_eq
    (fun p => rfl)⟩



end Passes

/-- **The reduction from orthogonal vectors to longest common subsequence is computable in
polynomial time.** -/
theorem computableInPolyTime_toLCS :
    ComputableInPolyTime toLCS encOV (encPair (encList encLCSSymbol) (encList encLCSSymbol)) := by
  have hd := computableInPolyTime_dim
  unfold toLCS
  refine (computableInPolyTime_P1.comp (hd.prod ?_)).prod
    (computableInPolyTime_P2.comp (hd.prod ?_))
  · unfold encOV; exact ComputableInPolyTime.fst _ _
  · unfold encOV; exact ComputableInPolyTime.snd _ _


open ComputableInPolyTime in
/-- **The reduction from orthogonal vectors to longest common subsequence runs in quasi-linear
time times a polynomial in the dimension**: within time `L ((d + 1) (log L + 1)) ^ D` on instances
of dimension `d` encoded in length `L`. The factor `d + 1` cannot be dropped: every block of
`LCS.P1` has length at least `20 d`, also for the vectors shorter than the dimension, so instances
with one long vector and many short ones have quadratic output. -/
theorem exists_computableInO_toLCS : ∃ D, ComputableInO toLCS encOV
    (encPair (encList encLCSSymbol) (encList encLCSSymbol))
    (fun p => ((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D)
    (fun p => ((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D) :=
  exists_computableInO_toLCS'

end Cslib.Complexity.OV
