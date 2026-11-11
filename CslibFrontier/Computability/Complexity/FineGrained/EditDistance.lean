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
  toLCS p

theorem exists_computableInO_toEditDistance :
    ∃ D, ComputableInO toEditDistance encOV
      (encPair (encList encLCSSymbol) (encList encLCSSymbol))
      (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D)
      (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D) := by
  sorry

-- We need the true mathematical gap theorem using editDist_indel_add_two_mul
theorem Edit.editDist_P1_P2 (d : Nat) (A B : List (List Bool)) :
    editDist Costs.indel (LCS.P1 d A) (LCS.P2 d A B) =
      (LCS.P1 d A).length + (LCS.P2 d A B).length -
        2 * lcsLength (LCS.P1 d A) (LCS.P2 d A B) := by
  have hlen := editDist_indel_add_two_mul (LCS.P1 d A) (LCS.P2 d A B)
  omega

theorem not_decidableInTimeO_editDist_of_OVH (hOVH : OVH) {ε : ℝ} (hε : 0 < ε)
    {S : Set (List LCSSymbol × List LCSSymbol)}
    (hS_gap : ∀ p : List (List Bool) × List (List Bool),
      (∃ a ∈ p.1, ∃ b ∈ p.2, Orthogonal a b) ↔ toEditDistance p ∈ S) :
    ¬DecidableInTimeO S (encPair (encList encLCSSymbol) (encList encLCSSymbol)) fun p =>
      (((encPair (encList encLCSSymbol) (encList encLCSSymbol)) p).length : ℝ) ^ (2 - ε) := by
  sorry

end Cslib.Complexity.OV
