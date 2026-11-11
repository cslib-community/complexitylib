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

namespace Cslib.Complexity.OV

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
open Turing.MultiTapeTM

inductive LCSSymbol | s0 | s1 | s2 | s3 | s4 | s5 | s6
  deriving DecidableEq, Repr, Inhabited, Fintype

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

end Cslib.Complexity.OV

@[expose] def toLCS (p : List (List Bool) × List (List Bool)) : List LCSSymbol × List LCSSymbol :=
  (LCS.P1 (OV.dim p) p.1, LCS.P2 (OV.dim p) p.1 p.2)

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
  sorry

theorem comp_extractB : ComputableInO extractB encOV encOV
  (fun p => (encOV p).length + 1) (fun p => (encOV p).length + 1) := by
  have id : ComputableInO (fun p : _ × _ => p) encOV encOV _ _ := ComputableInO.of_linear (.of_eq fun _ => rfl)
  have snd : ComputableInO (fun p : _ × _ => p.2) encOV (encList encBits) _ _ :=
    ComputableInO.snd' (enc₁ := encList encBits) (enc₂ := encList encBits) id
  have nil : ComputableInO (fun p : _ × _ => ([] : List (List Bool))) encOV (encList encBits) _ _ :=
    ComputableInO.const []
  have pair := ComputableInO.prod nil snd
  sorry
