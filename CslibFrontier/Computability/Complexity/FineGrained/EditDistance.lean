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
import CslibFrontier.Foundations.Data.Nat.LogRpow

/-!
# Orthogonal vectors hardness of edit distance

This module formalizes the reduction from the orthogonal vectors problem to the edit distance
problem by Backurs and Indyk \[BackursIndyk2015\], derived cleanly via the LCS reduction by Abboud,
Backurs, and Vassilevska Williams \[AbboudBackursVassilevskaWilliams2015\].

## Main definitions
* `Cslib.Complexity.OV.toEditDistance`: the reduction to edit distance.

## Main results
* `Cslib.Complexity.OV.exists_computableInO_toEditDistance`: the reduction runs within time
  `L ((d + 1) (log L + 1)) ^ D` on instances of dimension `d` encoded in length `L`.
* `Cslib.Complexity.OV.not_decidableInTimeO_editDist_of_OVH`: under the orthogonal vectors
  hypothesis, no target of the reduction is decidable in time `L ^ (2 - ε)`.

## References
* [A. Backurs, P. Indyk, *Edit Distance Cannot Be Computed in Strongly Subquadratic
  Time*]\[BackursIndyk2015\]
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

/-- **The reduction to edit distance runs in quasi-linear time times a polynomial in the
dimension**: within time `L ((d + 1) (log L + 1)) ^ D` on instances of dimension `d` encoded in
length `L` (`Cslib.Complexity.OV.exists_computableInO_toLCS`). -/
theorem exists_computableInO_toEditDistance :
    ∃ D, ComputableInO toEditDistance encOV
      (encPair (encList encLCSSymbol) (encList encLCSSymbol))
      (fun p => ((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D)
      (fun p => ((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D) :=
  exists_computableInO_toLCS

-- We need the true mathematical gap theorem using editDist_indel_add_two_mul
theorem Edit.editDist_P1_P2 (d : Nat) (A B : List (List Bool)) :
    editDist Costs.indel (LCS.P1 d A) (LCS.P2 d B) =
      (LCS.P1 d A).length + (LCS.P2 d B).length -
        2 * lcsLength (LCS.P1 d A) (LCS.P2 d B) := by
  have hlen := editDist_indel_add_two_mul (LCS.P1 d A) (LCS.P2 d B)
  omega

/-- **Orthogonal vectors hardness of edit distance**: under the orthogonal vectors hypothesis,
for every `ε > 0`, no set `S` of string pairs into which `toEditDistance` reduces the orthogonal
vectors problem is decidable within time `L ^ (2 - ε)` on pairs encoded in length `L`. The
reduction takes time `N ^ (1 + δ)` times a polynomial in the dimension `d` on `N` vectors, which
the orthogonal vectors hypothesis allows. -/
theorem not_decidableInTimeO_editDist_of_OVH (hOVH : OVH) {ε : ℝ} (hε : 0 < ε)
    {S : Set (List LCSSymbol × List LCSSymbol)}
    (hS_gap : ∀ p : List (List Bool) × List (List Bool),
      (∃ a ∈ p.1, ∃ b ∈ p.2, Orthogonal a b) ↔ toEditDistance p ∈ S) :
    ¬DecidableInTimeO S (encPair (encList encLCSSymbol) (encList encLCSSymbol)) fun p =>
      (((encPair (encList encLCSSymbol) (encList encLCSSymbol)) p).length : ℝ) ^ (2 - ε) := by
  intro hS
  obtain ⟨g, t, c, hg, hgS, ht⟩ := hS.exists_computableInO
  obtain ⟨D, hred⟩ := exists_computableInO_toEditDistance
  obtain ⟨cR, hcR⟩ := hred.length_le
  set ε₀ := min ε 1 with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₁ : ε₀ ≤ 1 := min_le_right ε 1
  have hεε : ε₀ ≤ ε := min_le_left ε 1
  obtain ⟨K, hK, hKb⟩ := Nat.exists_size_add_one_pow_le_mul_rpow D (ε := ε₀ / 4) (by positivity)
  have hdec := hg.comp hred
  set r : ℝ := 2 - ε₀ / 2 with hr
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set C₁ : ℝ := cR * (K + 1) + 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := by
    have : (0 : ℝ) ≤ cR * (K + 1) := by positivity
    linarith
  set encE := encPair (encList encLCSSymbol) (encList encLCSSymbol) with hencE
  -- the time of the composed decider, in terms of `X = L + 1` and `W = (d + 1) ^ D`
  have hbound (p : List (List Bool) × List (List Bool)) :
      ((((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D +
          t (toEditDistance p) : ℕ) : ℝ) ≤
        (K + c * C₁ ^ 2) * (((OV.dim p : ℝ) + 1) ^ D) ^ 2 * (((encOV p).length : ℝ) + 1) ^ r +
          c := by
    set X : ℝ := ((encOV p).length : ℝ) + 1 with hX
    set W : ℝ := ((OV.dim p : ℝ) + 1) ^ D with hW
    have hX1 : 1 ≤ X := by linarith [(Nat.cast_nonneg (encOV p).length : (0 : ℝ) ≤ _)]
    have hX0 : 0 < X := by linarith
    have hW1 : 1 ≤ W := one_le_pow₀ (by linarith [(Nat.cast_nonneg (OV.dim p) : (0 : ℝ) ≤ _)])
    have hT : ((((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D :
        ℕ) : ℝ) ≤ K * W * X ^ (1 + ε₀ / 4) := by
      have e : ((((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D :
          ℕ) : ℝ) = X * W * ((Nat.size (encOV p).length + 1 : ℕ) : ℝ) ^ D := by
        push_cast
        rw [mul_pow]
        ring
      rw [e, Real.rpow_add hX0, Real.rpow_one]
      have := hKb (encOV p).length
      calc X * W * ((Nat.size (encOV p).length + 1 : ℕ) : ℝ) ^ D ≤
            X * W * (K * X ^ (ε₀ / 4)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = K * W * (X * X ^ (ε₀ / 4)) := by ring
    -- the reduced instance has encoded length `O(W X ^ (1 + δ))`
    have hXp : 1 ≤ X ^ (1 + ε₀ / 4) := Real.one_le_rpow hX1 (by positivity)
    have hWX : 1 ≤ W * X ^ (1 + ε₀ / 4) := one_le_mul_of_one_le_of_one_le hW1 hXp
    have hLG : ((encE (toEditDistance p)).length : ℝ) + 1 ≤ C₁ * W * X ^ (1 + ε₀ / 4) := by
      have h' : ((encE (toEditDistance p)).length : ℝ) ≤
          cR * (((((encOV p).length + 1) * ((OV.dim p + 1) *
            (Nat.size (encOV p).length + 1)) ^ D : ℕ) : ℝ) + 1) := by
        exact_mod_cast hcR p
      have hcR0 : (0 : ℝ) ≤ cR := Nat.cast_nonneg cR
      have := mul_le_mul_of_nonneg_left hT hcR0
      have hK0 : (0 : ℝ) ≤ K := by linarith
      nlinarith
    have hpowLG : ((encE (toEditDistance p)).length : ℝ) ^ (2 - ε) ≤
        (((encE (toEditDistance p)).length : ℝ) + 1) ^ (2 - ε₀) := by
      rcases Nat.eq_zero_or_pos (encE (toEditDistance p)).length with h0 | h0
      · rw [h0, Nat.cast_zero, zero_add, Real.one_rpow]
        by_cases h2 : 2 - ε = 0
        · rw [h2, Real.rpow_zero]
        · rw [Real.zero_rpow h2]
          exact zero_le_one
      · have h1 : (1 : ℝ) ≤ (encE (toEditDistance p)).length := by exact_mod_cast h0
        calc ((encE (toEditDistance p)).length : ℝ) ^ (2 - ε)
            ≤ ((encE (toEditDistance p)).length : ℝ) ^ (2 - ε₀) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ ≤ (((encE (toEditDistance p)).length : ℝ) + 1) ^ (2 - ε₀) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hCW : 1 ≤ C₁ * W := one_le_mul_of_one_le_of_one_le hC₁1 hW1
    have hLGr : (((encE (toEditDistance p)).length : ℝ) + 1) ^ (2 - ε₀) ≤
        C₁ ^ 2 * W ^ 2 * X ^ r := by
      calc (((encE (toEditDistance p)).length : ℝ) + 1) ^ (2 - ε₀)
          ≤ (C₁ * W * X ^ (1 + ε₀ / 4)) ^ (2 - ε₀) :=
            Real.rpow_le_rpow (by positivity) hLG (by linarith)
        _ = (C₁ * W) ^ (2 - ε₀) * X ^ ((1 + ε₀ / 4) * (2 - ε₀)) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0.le]
        _ ≤ (C₁ * W) ^ (2 : ℝ) * X ^ r := by
            refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hCW (by linarith))
              (Real.rpow_le_rpow_of_exponent_le hX1 ?_) (by positivity) (by positivity)
            nlinarith
        _ = C₁ ^ 2 * W ^ 2 * X ^ r := by rw [Real.rpow_two]; ring
    have htLG : (t (toEditDistance p) : ℝ) ≤ c * (C₁ ^ 2 * W ^ 2 * X ^ r) + c :=
      (ht _).trans (by nlinarith [hpowLG.trans hLGr])
    have hXr : X ^ (1 + ε₀ / 4) ≤ X ^ r := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hWW : W ≤ W ^ 2 := by nlinarith
    have hK0 : (0 : ℝ) ≤ K := by linarith
    have h1 : K * W * X ^ (1 + ε₀ / 4) ≤ K * W ^ 2 * X ^ r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hWW hK0) hXr (by positivity) (by positivity)
    push_cast
    push_cast at hT
    nlinarith
  -- in terms of the number `N` of vectors and the dimension `d`
  set C₂ : ℝ := K + c * C₁ ^ 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by have : (0 : ℝ) ≤ K := by linarith
                           positivity
  have hfinal (p : List (List Bool) × List (List Bool)) :
      ((((encOV p).length + 1) * ((OV.dim p + 1) * (Nat.size (encOV p).length + 1)) ^ D +
          t (toEditDistance p) : ℕ) : ℝ) ≤
        (40 * C₂ + c) * ((((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
          ((OV.dim p : ℝ) + 1) ^ (2 * D + 2))) + (40 * C₂ + c) := by
    have hb := hbound p
    set X : ℝ := ((encOV p).length : ℝ) + 1 with hX
    set W : ℝ := ((OV.dim p : ℝ) + 1) ^ D with hW
    set Y : ℝ := ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) * ((OV.dim p : ℝ) + 1) ^ 2
    have hY0 : 0 ≤ Y := by positivity
    have hXr : X ^ r ≤ 36 * Y + 4 := OV.encOV_length_rpow_le p (by linarith)
    -- the dimension factor is at most the target when there are vectors, and one otherwise
    have hW2 : W ^ 2 ≤ W ^ 2 * Y + 1 := by
      rcases Nat.eq_zero_or_pos (p.1.length + p.2.length) with hN | hN
      · have h1 : p.1 = [] := List.eq_nil_of_length_eq_zero (by omega)
        have h2 : p.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hd : OV.dim p = 0 := by simp [OV.dim, h1, h2, listMax]
        have : W = 1 := by rw [hW, hd]; simp
        rw [this, one_pow, one_mul]
        linarith only [hY0]
      · have hN1 : (1 : ℝ) ≤ ((p.1.length + p.2.length : ℕ) : ℝ) := by exact_mod_cast hN
        have hd1 : (1 : ℝ) ≤ (OV.dim p : ℝ) + 1 := by
          linarith [(Nat.cast_nonneg (OV.dim p) : (0 : ℝ) ≤ _)]
        have : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1 (by linarith))
          (one_le_pow₀ hd1)
        linarith only [le_mul_of_one_le_right (sq_nonneg W) this]
    have hYW : ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
        ((OV.dim p : ℝ) + 1) ^ (2 * D + 2) = W ^ 2 * Y := by
      change _ = (((OV.dim p : ℝ) + 1) ^ D) ^ 2 * (((p.1.length + p.2.length : ℕ) : ℝ) ^
        (2 - ε₀ / 2) * ((OV.dim p : ℝ) + 1) ^ 2)
      ring
    have hYW' : (40 * C₂ + c) * (((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
        ((OV.dim p : ℝ) + 1) ^ (2 * D + 2)) = (40 * C₂ + c) * (W ^ 2 * Y) := by rw [hYW]
    have e1 : C₂ * W ^ 2 * X ^ r ≤ C₂ * W ^ 2 * (36 * Y + 4) :=
      mul_le_mul_of_nonneg_left hXr (by positivity)
    have e2 : C₂ * W ^ 2 * (36 * Y + 4) ≤ 40 * C₂ * (W ^ 2 * Y) + 4 * C₂ := by
      have := mul_le_mul_of_nonneg_left hW2 hC₂0
      linarith only [this]
    have e3 : 0 ≤ c * (W ^ 2 * Y) := by positivity
    linarith only [hb, e1, e2, e3, hYW', hC₂0]
  refine hOVH (ε₀ / 2) (half_pos hε₀) (2 * D + 2)
    ((DecidableInTimeO.of_computableInO hdec (fun p => ?_) (fun p => hfinal p)).mono
    (⌈40 * C₂ + c⌉₊) (fun p => ?_) (fun p => by positivity))
  · rw [Function.comp_apply, ← hgS, ← hS_gap]
    rfl
  · have hC : (40 * C₂ + c) ≤ (⌈40 * C₂ + c⌉₊ : ℝ) := Nat.le_ceil _
    have hY0 : (0 : ℝ) ≤ ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
        ((OV.dim p : ℝ) + 1) ^ (2 * D + 2) := by positivity
    linarith only [mul_le_mul_of_nonneg_right hC hY0, hC]

end Cslib.Complexity.OV
