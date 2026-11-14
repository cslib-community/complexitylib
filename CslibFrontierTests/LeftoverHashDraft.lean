/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

import CslibFrontier.Probability.Extractor.LeftoverHash
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.Event

open scoped ENNReal

open Cslib Cslib.Probability Cslib.Probability.PMF

set_option linter.privateModule false
set_option autoImplicit false

private def matrixHash (s : BitString 8) (x : BitString 8) : BitString 1 :=
  BitString.LinearHash.hash (BitString.blocksEquiv (m := 1) (k := 8) s) x

private theorem matrixUniversal :
    IsUniversalHash (PMF.uniformOfFintype (BitString 8)) matrixHash
      (ENNReal.ofReal ((1 + (1 / 8 : ℝ)) / (2 : ℝ) ^ 1)) := by
  have h := BitString.LinearHash.isTwoUniversal_flat 8 1
  apply h.mono
  rw [show (Fintype.card (BitString 1) : ℝ≥0∞) = 2 by simp]
  apply (ENNReal.toReal_le_toReal (by simp) (by simp)).mp
  norm_num

-- A genuine source: all eight input bits are uniform, with entropy exactly eight.
example : dist
    ((PMF.uniformOfFintype (BitString 8)).bind fun x =>
      (PMF.uniformOfFintype (BitString 8)).map fun s => Fin.append (matrixHash s x) s)
    (PMF.uniformOfFintype (BitString 9)) ≤ Real.sqrt (2 * (1 / 8 : ℝ)) := by
  apply matrixUniversal.isExtractor_append_of_entropy_div (by norm_num)
  rw [minEntropy_uniformOfFintype, BitString.logb_card]
  norm_num

-- Digest-first layout, checked through the public accessors.
example (x s : BitString 8) :
    BitString.fstBits (Fin.append (matrixHash s x) s) = matrixHash s x ∧
    BitString.sndBits (Fin.append (matrixHash s x) s) = s := by simp

-- Zero digest: even a completely deterministic family satisfies the collision bound.
example : IsExtractor (fun (_ : BitString 1) (s : BitString 2) =>
    Fin.append (fun (_ : Fin 0) => false) s) 0 (Real.sqrt (2 * (1 / 8 : ℝ))) := by
  have hh : IsUniversalHash (PMF.uniformOfFintype (BitString 2))
      (fun (_ : BitString 2) (_ : BitString 1) (_ : Fin 0) => false)
      (ENNReal.ofReal ((1 + (1 / 8 : ℝ)) / (2 : ℝ) ^ 0)) := by
    intro x y _
    exact (PMF.toOuterMeasure_le_one _ _).trans (by norm_num)
  simpa only [Nat.cast_zero, zero_div] using
    hh.isExtractor_append_of_entropy_div (by norm_num)

-- Large δ also permits a constant one-bit digest (collision probability one).
example : IsExtractor (fun (_ : BitString 1) (s : BitString 0) =>
    Fin.append (fun (_ : Fin 1) => false) s) (1 / (2 : ℝ)) (Real.sqrt (2 * 2)) := by
  have hh : IsUniversalHash (PMF.uniformOfFintype (BitString 0))
      (fun (_ : BitString 0) (_ : BitString 1) (_ : Fin 1) => false)
      (ENNReal.ofReal ((1 + (2 : ℝ)) / (2 : ℝ) ^ 1)) := by
    intro x y _
    exact (PMF.toOuterMeasure_le_one _ _).trans (by norm_num)
  simpa only [Nat.cast_one] using hh.isExtractor_append_of_entropy_div (by norm_num)
