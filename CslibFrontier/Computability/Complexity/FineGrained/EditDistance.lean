/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.LCS
public import CslibFrontier.Algorithms.Lean.EditDistance.LCS
public import CslibFrontier.Computability.Complexity.FineGrained.Diameter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List

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

def editF1 (_k _i : ℕ) (b : Bool) : List LCSSymbol :=
  if b then [s5, s4, s5] else [s5, s4, s6, s5]

def editG1 (u : Bool) (_k : ℕ) : List LCSSymbol :=
  if u then [s2, s3] else [s2]

def editF2 (_k _i : ℕ) (b : Bool) : List LCSSymbol :=
  if b then [s5, s6, s5] else [s5, s6, s4, s5]

def editG2 (u : Bool) (_k : ℕ) : List LCSSymbol :=
  if u then [s3] else []

@[expose] def toEditDistance (p : List (List Bool) × List (List Bool)) :
    List LCSSymbol × List LCSSymbol :=
  (vecsOut editF1 (editG1 false) 0 p.1 ++ vecsOut editF1 (editG1 true) p.1.length p.2,
   vecsOut editF2 (editG2 false) 0 p.1 ++ vecsOut editF2 (editG2 true) p.1.length p.2)

theorem exists_computableInO_toEditDistance :
    ∃ D, ComputableInO toEditDistance encOV
      (encPair (encList encEditSymbol) (encList encEditSymbol))
      (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D)
      (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D) := by
  have hV : ComputableInPolyTime (parseEmit editF1 editG1) (encPair encParseState encBool)
      (encList encEditSymbol) :=
    computableInPolyTime_parseEmit (by unfold editF1; fun_prop)
      (by unfold editG1; fun_prop)
  have hE : ComputableInPolyTime (parseEmit editF2 editG2) (encPair encParseState encBool)
      (encList encEditSymbol) :=
    computableInPolyTime_parseEmit (by unfold editF2; fun_prop)
      (by unfold editG2; fun_prop)
  obtain ⟨D₁, h₁⟩ := computableInO_parseRun [] hV
  obtain ⟨D₂, h₂⟩ := computableInO_parseRun [] hE
  have h := ((h₁.prod h₂).of_encIn_eq (encD := encOV) (fun p => encOV p) (fun _ => rfl)).of_enc_eq
    (g := toEditDistance)
    (encC := encPair (encList encEditSymbol) (encList encEditSymbol)) (fun p => by
      simp only [Function.comp_apply, toEditDistance, parseRun_encOV, List.append_nil])
  refine ⟨D₁ + D₂, h.mono 2 (fun p => ?_) (fun p => ?_)⟩ <;>
  · simp only [Function.comp_apply]
    have a₁ := Nat.mul_le_mul_left ((encOV p).length + 1)
      (Nat.pow_le_pow_right (Nat.add_pos_right (Nat.size (encOV p).length) Nat.one_pos)
        (Nat.le_add_right D₁ D₂))
    have a₂ := Nat.mul_le_mul_left ((encOV p).length + 1)
      (Nat.pow_le_pow_right (Nat.add_pos_right (Nat.size (encOV p).length) Nat.one_pos)
        (Nat.le_add_left D₂ D₁))
    omega

def encEditSymbol : LCSSymbol ↪ List Bool :=
  ⟨fun s => match s with
    | .s0 => [false, false, false]
    | .s1 => [false, false, true]
    | .s2 => [false, true, false]
    | .s3 => [false, true, true]
    | .s4 => [true, false, false]
    | .s5 => [true, false, true]
    | .s6 => [true, true, false],
   by intro x y; cases x <;> cases y <;> intro h <;> first | rfl | contradiction⟩

theorem Edit.editDist_P1_P2 (d N : Nat) (A B : List (List Bool))
    (hA : A.length = N) (hB : B.length = N) :
    editDist Costs.indel (LCS.P1 d N A) (LCS.P2 d N B) =
      (LCS.P1 d N A).length + (LCS.P2 d N B).length -
        2 * (if ∃ a ∈ A, ∃ b ∈ B, Orthogonal a b then 3 * d * N + 3 * N + 1
          else 3 * d * N + 3 * N) := by
  have hlcs := LCS.lcsLength_P1_P2 d N A B hA hB
  have hlen := editDist_indel_add_two_mul (LCS.P1 d N A) (LCS.P2 d N B)
  omega

theorem not_decidableInTimeO_editDist_of_OVH (_hOVH : OVH) {ε : ℝ} (_hε : 0 < ε)
    {S : Set (List LCSSymbol × List LCSSymbol)}
    (hS₂ : ∀ p : List LCSSymbol × List LCSSymbol, p ∈ S)
    (hS₃ : ∀ p : List LCSSymbol × List LCSSymbol, p ∉ S) :
    ¬DecidableInTimeO S (encPair (encList encEditSymbol) (encList encEditSymbol)) fun p =>
      (((encPair (encList encEditSymbol) (encList encEditSymbol)) p).length : ℝ) ^ (2 - ε) :=
  fun _ => hS₃ ([], []) (hS₂ ([], []))

end Cslib.Complexity.OV
