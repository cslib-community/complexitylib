/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap
import Complexity.Foundations.Combinatorics.Expander.AffineTower
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Arithmetic expanders and compositional rotation certificates

Small rotations execute directly. The field with 257 elements meets the tower's spectral
hypothesis without graph search. Its large constant degree is not a claim of practical graph
enumeration, and the base certificate below is not a uniform certificate for the tower.
-/

namespace ComplexityTests.ExplicitExpanders

open Cslib Turing.MultiTapeTM

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩

-- All three labelled neighbors of a vertex, including their return labels.
example : (RotationMap.affinePlane (ZMod 3)).rot ((1, 1), 0) = ((0, 2), 1) := by decide
example : (RotationMap.affinePlane (ZMod 3)).rot ((1, 1), 1) = ((1, 0), 1) := by decide
example : (RotationMap.affinePlane (ZMod 3)).rot ((1, 1), 2) = ((2, 1), 1) := by decide

-- A full arithmetic-base rotation evaluates without materializing its vertex or edge sets.
example : (RotationMap.affinePlaneTowerBase (ZMod 257)).rot
    (((((1, 2), (3, 4)), (5, 6)), (7, 8)), (9, 10)) =
      (((((9, 7), (39, 113)), (55, 52)), (10, 5)), (1, 7)) := by decide

-- This is an actual field satisfying the arithmetic base's spectral hypothesis.
example : (RotationMap.affinePlaneTowerBase (ZMod 257)).spectralExpansion ≤ 1 / 5 := by
  apply RotationMap.spectralExpansion_affinePlaneTowerBase_le_one_div_five
  norm_num

example (n : ℕ) : (RotationMap.affinePlaneTower (ZMod 257) n).spectralExpansion ≤ 2 / 5 := by
  apply RotationMap.spectralExpansion_affinePlaneTower_le
  norm_num

example (n : ℕ) :
    Fintype.card
      (RotationMap.ZigzagTowerVertex (RotationMap.AffinePlaneTowerBaseVertex (ZMod 257)) n) =
      257 ^ (8 * (n + 1)) := by
  simp only [RotationMap.card_affinePlaneTowerVertex, ZMod.card]

private abbrev planeEncoding {K : Type} (encode : K ↪ List Bool) := encPair encode encode

private abbrev baseEncoding {K : Type} (encode : K ↪ List Bool) :=
  encPair (encPair (encPair (planeEncoding encode) (planeEncoding encode))
    (planeEncoding encode)) (planeEncoding encode)

-- The same straight-line construction works with any certified field arithmetic and encoding.
example {K : Type} [Field K] (encode : K ↪ List Bool)
    (hmul : ComputableTidilyInPolyTime (fun p : K × K => p.1 * p.2)
      (planeEncoding encode) encode)
    (hsub : ComputableTidilyInPolyTime (fun p : K × K => p.1 - p.2)
      (planeEncoding encode) encode) :
    ComputableTidilyInPolyTime (RotationMap.affinePlaneTowerBase K).rot
      (encPair (baseEncoding encode) (planeEncoding encode))
      (encPair (baseEncoding encode) (planeEncoding encode)) := by
  fun_prop [RotationMap.affinePlaneTowerBase]

-- Only the fixed field operations use the finite-domain theorem; graph products compose them.
example (encode : ZMod 257 ↪ List Bool) :
    ComputableTidilyInPolyTime (RotationMap.affinePlaneTowerBase (ZMod 257)).rot
      (encPair (baseEncoding encode) (planeEncoding encode))
      (encPair (baseEncoding encode) (planeEncoding encode)) := by
  have hmul : ComputableTidilyInPolyTime (fun p : ZMod 257 × ZMod 257 => p.1 * p.2)
      (planeEncoding encode) encode := .of_finite _
  have hsub : ComputableTidilyInPolyTime (fun p : ZMod 257 × ZMod 257 => p.1 - p.2)
      (planeEncoding encode) encode := .of_finite _
  fun_prop [RotationMap.affinePlaneTowerBase]

-- Equivalent direct and let-bound spellings, with a supplied rotation on an arbitrary type.
example {V D E : Type} (G : RotationMap V D) (H : RotationMap D E)
    (vertex : V ↪ List Bool) (label : D ↪ List Bool) (small : E ↪ List Bool)
    (hG : ComputableTidilyInPolyTime G.rot (encPair vertex label) (encPair vertex label))
    (hH : ComputableTidilyInPolyTime H.rot (encPair label small) (encPair label small)) :
    ComputableTidilyInPolyTime
      (fun p : ((V × D) × (E × E)) × Bool => ((G.zigzag H).rot p.1, !p.2))
      (encPair (encPair (encPair vertex label) (encPair small small)) encBool)
      (encPair (encPair (encPair vertex label) (encPair small small)) encBool) := by
  fail_if_success (clear hG; fun_prop)
  fail_if_success (clear hH; fun_prop)
  fun_prop

example {V D E : Type} (G : RotationMap V D) (H : RotationMap D E)
    (vertex : V ↪ List Bool) (label : D ↪ List Bool) (small : E ↪ List Bool)
    (hG : ComputableTidilyInPolyTime G.rot (encPair vertex label) (encPair vertex label))
    (hH : ComputableTidilyInPolyTime H.rot (encPair label small) (encPair label small)) :
    ComputableTidilyInPolyTime
      (fun p : ((V × D) × (E × E)) × Bool =>
        let next := (G.zigzag H).rot p.1
        (next, !p.2))
      (encPair (encPair (encPair vertex label) (encPair small small)) encBool)
      (encPair (encPair (encPair vertex label) (encPair small small)) encBool) := by
  fun_prop

end ComplexityTests.ExplicitExpanders
