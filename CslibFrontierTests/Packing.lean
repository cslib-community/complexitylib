/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.PACLearning.Packing
import CslibFrontierTests.RealizablePAC
import CslibFrontier.Foundations.Data.Code.HammingBound

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

/-- At Hamming scale `m / 4`, the labelings of `m` points by thresholds have a net of at most
`32 ^ 2 = 1024` labelings that thresholds realize: a maximal separated subset
(`Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`) is a net, and the packing
bound limits its size. -/
example {m : ℕ} (x : Fin m → ℕ) :
    ∃ N : Finset (Fin m → Bool), (∀ u ∈ N, u ∈ restriction thresholds x) ∧ N.card ≤ 1024 ∧
      ∀ u ∈ restriction thresholds x, ∃ v ∈ N, hammingDist v u ≤ m / 4 := by
  classical
  set V := (Set.toFinite (restriction thresholds x)).toFinset
  obtain ⟨N, hNV, hNsep, hnet⟩ :=
    Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le V (m / 4)
  have hNC : ∀ u ∈ N, u ∈ restriction thresholds x := fun u hu =>
    (Set.Finite.mem_toFinset _).1 (hNV hu)
  refine ⟨N, hNC, ?_, fun u hu => hnet u ((Set.Finite.mem_toFinset _).2 hu)⟩
  have hsep : ∀ u ∈ N, ∀ v ∈ N, u ≠ v → (1 / 4 : ℝ) * m ≤ hammingDist u v := by
    intro u hu v hv huv
    have h4 : m ≤ 4 * hammingDist u v := by have := hNsep hu hv huv; omega
    have : (m : ℝ) ≤ 4 * hammingDist u v := by exact_mod_cast h4
    linarith
  have := card_le_div_pow_of_le_hammingDist (ε := 1 / 4)
    (fun _ hW => card_le_one_of_setShatters_thresholds hW) hNC (by norm_num) (by norm_num) hsep
  norm_num at this
  exact_mod_cast this

end CslibFrontierTests.Packing
