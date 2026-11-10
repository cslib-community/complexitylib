/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Time
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
public import Mathlib.Data.Nat.Log

/-!
# Admitted native 3SUM inputs

The magnitude restriction and logarithmic physical-width threshold are shared by the ordinary
3SUM algorithm and its input-reading lower bound. The threshold depends on input length and the
fixed magnitude exponent, and admits every wider physical word. Admitted signed inputs fit.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Exactly the exponent already proved for every preprocessing word. -/
@[expose] def envelopeExponent (κ : ℕ) : ℕ := 2720 * κ + 16456

/-- A constant for fixed exponent and concrete callee, independent of length and word width. -/
@[expose] def widthCoefficient (κ d : ℕ) : ℕ :=
  1300 * κ + 7865 + (d + 1) * (envelopeExponent κ + 20) + 20

/-- Positive logarithmic physical width, including empty inputs. -/
@[expose] def width (κ d n : ℕ) : ℕ := widthCoefficient κ d * Nat.clog 2 (n + 2)

/-- The original polynomial magnitude restriction and logarithmic physical-width threshold
`width κ 123357 input.length`, where `123357` is the width coefficient of the concrete callee
`ExactTriangle.ParameterSelecting.callee`. Unfolded, the threshold is
`(335535060 * κ + 2032454293) * Nat.clog 2 (input.length + 2)`.
This admits every width above the threshold, independently of the particular input values. -/
@[expose] def Admissible (κ : ℕ) (input : List ℤ) (W : ℕ) : Prop :=
  width κ 123357 input.length ≤ W ∧
    ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)

/-- Admitted input/width pairs satisfy the decision API's separate input-fit condition. -/
theorem Admissible.inputFits {κ W : ℕ} {input : List ℤ} (h : Admissible κ input W) :
    InputFits W (input.map Signed.encode) := by
  let n := input.length
  let L := Nat.clog 2 (n + 2)
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (by omega)
  have hn : n + 2 ≤ 2 ^ L := Nat.le_pow_clog (by decide) _
  have hC : κ + 3 ≤ widthCoefficient κ 123357 := by
    dsimp only [widthCoefficient, envelopeExponent]
    omega
  have hW : (κ + 3) * L ≤ W := (Nat.mul_le_mul_right L hC).trans h.1
  refine ⟨?_, ?_⟩
  · simp only [List.length_map]
    apply lt_of_lt_of_le (show input.length < 2 ^ L by change n < 2 ^ L; omega)
    exact Nat.pow_le_pow_right Nat.two_pos (by nlinarith)
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have habs : (z.natAbs : ℤ) ≤ ((n + 2) ^ κ : ℕ) := by
      simpa only [Int.natCast_natAbs] using h.2 z hz
    have habs' : z.natAbs ≤ (n + 2) ^ κ := by exact_mod_cast habs
    have hpow : (n + 2) ^ κ ≤ 2 ^ (κ * L) := by
      simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hn κ
    have hfit : Signed.encode z < 2 ^ (κ * L + 2) := by
      have hpos := Nat.two_pow_pos (κ * L)
      rw [pow_add]
      unfold Signed.encode
      split_ifs <;> omega
    exact hfit.trans_le (Nat.pow_le_pow_right Nat.two_pos (by nlinarith))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
