/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
public import CslibFrontier.Computability.Complexity.FineGrained.LCS
public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.Complexity.FineGrained.Diameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Orthogonal vectors hardness of edit distance

This module formalizes the reduction from the orthogonal vectors problem to the edit distance
problem by Backurs and Indyk [BackursIndyk2015], derived cleanly via the LCS reduction by Abboud,
Backurs, and Vassilevska Williams [AbboudBackursVassilevskaWilliams2015].

## Main definitions
* `Cslib.Complexity.OV.toEditDistance`: the reduction to edit distance.

## References
* [A. Backurs, P. Indyk, *Edit Distance Cannot Be Computed in Strongly Subquadratic
  Time*][BackursIndyk2015]
-/

public section

namespace Cslib.Complexity.OV

open Cslib.Algorithms.Lean.EditDistance
open Cslib.Complexity
open Turing.MultiTapeTM

open LCSSymbol

@[expose] def toEditDistance (p : List (List Bool) × List (List Bool)) :
    List LCSSymbol × List LCSSymbol :=
  let d := OV.dim p
  let N := max p.1.length p.2.length
  let A := p.1 ++ List.replicate (N - p.1.length) (LCS.f d)
  let B := p.2 ++ List.replicate (N - p.2.length) (LCS.f d)
  (LCS.P1 d N A, LCS.P2 d N B)

end Cslib.Complexity.OV
