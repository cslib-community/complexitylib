/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Packing
import CslibFrontierTests.RealizablePAC

/-! Checks for packing numbers of a class on a sample: for thresholds on `ℕ`, which shatter no
two points, separated sets of labelings have a size bound independent of the number of points, and
the labelings of any sample have a small net at every scale. -/

namespace CslibFrontierTests.Packing

open Cslib.MachineLearning.PACLearning
open CslibFrontierTests.RealizablePAC (thresholds card_le_one_of_setShatters_thresholds)

/-- Labelings of `m` points by thresholds that pairwise differ on at least half of the points
number at most `16 ^ 2 = 256`, whatever `m`. -/
example {m : ℕ} (x : Fin m → ℕ) (P : Finset (Fin m → Bool))
    (hPC : ∀ u ∈ P, u ∈ restriction thresholds x)
    (hP : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → (1 / 2 : ℝ) * m ≤ hammingDist u v) : P.card ≤ 256 := by
  have := card_le_div_pow_of_le_hammingDist
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) hPC (by norm_num) (by norm_num) hP
  norm_num at this
  exact_mod_cast this

/-- At scale `m / 4`, the labelings of `m > 0` points by thresholds have a net of at most
`32 ^ 2 = 1024` labelings that thresholds realize. -/
example {m : ℕ} (hm : 0 < m) (x : Fin m → ℕ) :
    ∃ N : Finset (Fin m → Bool), (∀ u ∈ N, u ∈ restriction thresholds x) ∧ N.card ≤ 1024 ∧
      ∀ u ∈ restriction thresholds x, ∃ v ∈ N, (hammingDist u v : ℝ) < 1 / 4 * m := by
  classical
  set V := (Set.toFinite (restriction thresholds x)).toFinset
  obtain ⟨N, hNV, hNsep, hnet⟩ :=
    exists_subset_le_hammingDist_forall_exists_hammingDist_lt V (r := 1 / 4 * m) (by positivity)
  have hNC : ∀ u ∈ N, u ∈ restriction thresholds x := fun u hu =>
    (Set.Finite.mem_toFinset _).1 (hNV hu)
  refine ⟨N, hNC, ?_, fun u hu => hnet u ((Set.Finite.mem_toFinset _).2 hu)⟩
  have := card_le_div_pow_of_le_hammingDist (ε := 1 / 4)
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) hNC (by norm_num) (by norm_num) hNsep
  norm_num at this
  exact_mod_cast this

end CslibFrontierTests.Packing
