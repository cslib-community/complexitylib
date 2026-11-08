/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.Extractor.LeftoverHash

/-! Seeded extractors: concrete instances, a satisfiable entropy hypothesis and seedless failure.
-/

namespace ComplexityTests.Extractor

open Cslib Cslib.Probability Cslib.Probability.PMF

/-- Multiplying a 4-bit source by a random `1 × 4` Boolean matrix is a strong
`(3, 1 / 4)`-extractor: `1 + 2 log₂ 2 = 3`. -/
theorem linearHash_isStrongExtractor :
    IsStrongExtractor (fun (x : BitString 4) (rows : Fin 1 → BitString 4) =>
      BitString.LinearHash.hash rows x) 3 (1 / 4) := by
  have h := BitString.LinearHash.isStrongExtractor 4 1 (δ := 1 / 2) (by norm_num) (k := 3)
    (by norm_num [Real.logb_self_eq_one])
  norm_num at h ⊢
  exact h

-- The entropy hypothesis is satisfiable: the uniform 4-bit source has min-entropy 4.
example :
    dist ((PMF.uniformOfFintype (BitString 4)).bind fun x =>
        (PMF.uniformOfFintype (Fin 1 → BitString 4)).map fun rows =>
          (rows, BitString.LinearHash.hash rows x))
      (PMF.uniformOfFintype ((Fin 1 → BitString 4) × BitString 1)) ≤ 1 / 4 := by
  refine linearHash_isStrongExtractor _ ?_
  rw [minEntropy_uniformOfFintype, show Fintype.card (BitString 4) = 2 ^ 4 by simp,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

-- Strong extractors are extractors.
example :
    IsExtractor (fun (x : BitString 4) (rows : Fin 1 → BitString 4) =>
      BitString.LinearHash.hash rows x) 3 (1 / 4) :=
  linearHash_isStrongExtractor.isExtractor

-- Without a seed, reading the first bit of a 3-bit source fails for 2-sources.
example : ¬ IsExtractor (fun (x : BitString 3) (_ : Unit) => x 0) 2 (1 / 4) := by
  have h := not_isExtractor_bool_of_subsingleton (Input := BitString 3) (Seed := Unit)
    (fun x _ => x 0) (ε := 1 / 4) (by norm_num)
  rw [show Fintype.card (BitString 3) = 2 ^ 3 by simp, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  norm_num at h
  exact h

end ComplexityTests.Extractor
