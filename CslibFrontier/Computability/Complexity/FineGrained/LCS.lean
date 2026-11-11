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

inductive LCSSymbol | s0 | s1 | s2 | s3 | s4 | s5 | s6
  deriving DecidableEq, Repr, Inhabited, Fintype

open LCSSymbol

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

@[expose] def LCS.P1 (d N : Nat) (A : List (List Bool)) : List LCSSymbol :=
  let L := 3 * N
  List.replicate L s3 ++ (A.map (VG1' d)).flatten ++ List.replicate L s3

@[expose] def LCS.P2 (d N : Nat) (B : List (List Bool)) : List LCSSymbol :=
  let dummy := (List.replicate (N - 1) (f d)).map (VG2' d)
  [s3] ++ dummy.flatten ++ (B.map (VG2' d)).flatten ++ dummy.flatten

end Cslib.Complexity.OV
