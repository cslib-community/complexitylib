/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.LevelWeight
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Basic.ENNReal.BigOperators

/-!
# The spectral sample

By Parseval's identity, the squared Fourier coefficients of a Boolean function read as signs sum
to one, so they are the probabilities of a distribution on sets of coordinates: the *spectral
sample* `𝒮_f` (`BitString.spectralSample`), which draws `S` with probability `f̂(S) ^ 2`
[O'Donnell, Definition 1.18][ODonnell2014]. The size of the spectral sample is `k` with probability
the Fourier weight `W^k[f]` at degree `k` (`BitString.spectralSample_map_card_apply`).

## Main definitions

* `Cslib.BitString.spectralSample`: the spectral sample of a Boolean function.

## Main results

* `Cslib.BitString.spectralSample_apply`: the spectral sample draws `S` with probability
  `f̂(S) ^ 2`.
* `Cslib.BitString.spectralSample_map_card_apply`: its size is `k` with probability `W^k[f]`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral sample of a Boolean function `f` read as signs: the distribution on sets of
coordinates that draws `S` with probability `f̂(S) ^ 2` [O'Donnell, Definition 1.18][ODonnell2014].
-/
noncomputable def spectralSample (f : (ι → Bool) → Bool) : PMF (Finset ι) :=
  PMF.ofFintype (fun S => ENNReal.ofReal (fourierCoeff (fun x => signVal (f x)) S ^ 2)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _, sum_fourierCoeff_sq_signVal,
      ENNReal.ofReal_one]

/-- The spectral sample draws `S` with probability `f̂(S) ^ 2`. -/
theorem spectralSample_apply (f : (ι → Bool) → Bool) (S : Finset ι) :
    spectralSample f S = ENNReal.ofReal (fourierCoeff (fun x => signVal (f x)) S ^ 2) := by
  rw [spectralSample, PMF.ofFintype_apply]

/-- **The size of the spectral sample** is `k` with probability the Fourier weight `W^k[f]` at
degree `k` [O'Donnell, Definition 1.19][ODonnell2014]. -/
theorem spectralSample_map_card_apply (f : (ι → Bool) → Bool) (k : ℕ) :
    (spectralSample f).map card k = ENNReal.ofReal (levelWeight k fun x => signVal (f x)) := by
  rw [PMF.map_apply, tsum_fintype, levelWeight,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  by_cases h : #S = k
  · simp [h, spectralSample_apply]
  · simp [h, Ne.symm h]

end Cslib.BitString
