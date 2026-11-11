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

This module formalizes the reduction from the orthogonal vectors problem to the longest common
subsequence problem by Abboud, Backurs, and Vassilevska Williams [AbboudBackursVassilevskaWilliams2015].

## Main definitions
* `Cslib.Complexity.OV.toLCS`: the reduction to LCS.

## Main results
* `Cslib.Complexity.OV.lcsLength_toLCS`: the gap characterization.

## References
* [A. Abboud, A. Backurs, V. Vassilevska Williams, *Tight Hardness Results for LCS and Other Sequence Similarity Measures*][AbboudBackursVassilevskaWilliams2015]
-/

public section

open scoped List

namespace Cslib.Complexity.OV

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
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

@[expose] def LCS.M (d : Nat) : Nat := 10 * d + 10
@[expose] def LCS.B_len (d : Nat) : Nat := 10 * d + 10

@[expose] def LCS.VG1' (d : Nat) (a : List Bool) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ List.replicate (W d) s1 ++ R1 a ++ List.replicate (LCS.M d) s2
@[expose] def LCS.VG2' (d : Nat) (b : List Bool) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ R2 b ++ List.replicate (W d) s1 ++ List.replicate (LCS.M d) s2

@[expose] def LCS.DummyBlock (d : Nat) : List LCSSymbol :=
  List.replicate (LCS.M d) s0 ++ List.replicate (W d) s1 ++ List.replicate (LCS.M d) s2

@[expose] def LCS.P1 (d : Nat) (A : List (List Bool)) : List LCSSymbol :=
  let L := 3 * A.length * LCS.B_len d
  List.replicate L s3 ++ (A.map (VG1' d)).flatten ++ List.replicate L s3

/-- The `3 * B.length` blocks of `LCS.P2`: `B.length` dummy blocks on each side of the vector
gadgets of `B`. -/
@[expose] def LCS.P2Blocks (d : Nat) (B : List (List Bool)) : List (List LCSSymbol) :=
  List.replicate B.length (LCS.DummyBlock d) ++ B.map (VG2' d) ++
    List.replicate B.length (LCS.DummyBlock d)

@[expose] def LCS.P2 (d : Nat) (B : List (List Bool)) : List LCSSymbol :=
  List.intercalate (List.replicate (LCS.B_len d) s3) (LCS.P2Blocks d B)

@[expose] def LCS.BaseScore (d N : Nat) : Nat :=
  N * (2 * LCS.M d + 3 * d - 1) + 2 * N * LCS.B_len d

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

theorem LCS.lcsLength_P1_P2 (d N : Nat) (A B : List (List Bool))
    (hA : A.length = N) (hB : B.length = N)
    (hA' : ∀ a ∈ A, a.length = d) (hB' : ∀ b ∈ B, b.length = d) :
    BaseScore d N + 1 ≤ lcsLength (P1 d A) (P2 d B) ↔ ∃ a ∈ A, ∃ b ∈ B, Orthogonal a b := by
  sorry



@[expose] def toLCS (p : List (List Bool) × List (List Bool)) : List LCSSymbol × List LCSSymbol :=
  (LCS.P1 (OV.dim p) p.1, LCS.P2 (OV.dim p) p.2)

def extractA (p : List (List Bool) × List (List Bool)) : List (List Bool) × List (List Bool) := (p.1, [])
def extractB (p : List (List Bool) × List (List Bool)) : List (List Bool) × List (List Bool) := ([], p.2)

theorem comp_extractA : ComputableInO extractA encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ := ComputableInO.of_linear (.of_eq fun _ => rfl)
  have fst : ComputableInO (fun p : _ × _ => p.1) encOV (encList encBits) _ _ :=
    ComputableInO.fst' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod fst nil
  exact pair.mono 2 (fun p => by omega) (fun p => by omega)

theorem comp_extractB : ComputableInO extractB encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ := ComputableInO.of_linear (.of_eq fun _ => rfl)
  have snd : ComputableInO (fun p : _ × _ => p.2) encOV (encList encBits) _ _ :=
    ComputableInO.snd' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod nil snd
  exact pair.mono 2 (fun p => by omega) (fun p => by omega)
end Cslib.Complexity.OV
