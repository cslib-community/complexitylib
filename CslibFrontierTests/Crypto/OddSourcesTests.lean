/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoPartyTightness
import CslibFrontier.Probability.PMF.Map

/-!
# Odd-source extraction regression clients

These clients exercise both class orientations, positive output lengths, exact index
probabilities and the original padded laws. An odd index space and even branch space
show why the hypotheses matter. Threshold privacy belongs to the threshold-construction tests.
-/

public section

open Finset Cslib.Probability
open scoped Cslib.Probability.PMF
open Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

namespace CslibFrontierTests.OddSources

private def small : Finset (Fin 3) := {0}
private def large : Finset (Fin 3) := {1, 2}

private theorem small_ne : small.Nonempty := by decide
private theorem small_compl_ne : (univ \ small).Nonempty := by decide
private theorem large_ne : large.Nonempty := by decide
private theorem large_compl_ne : (univ \ large).Nonempty := by decide

-- A half-index choice gives three keys and true probability exactly 1/3.
example : (OddSources.keys small ({0} : Finset (Fin 2))).card = 3 := by decide

example : (((OddSources.source small small_ne small_compl_ne ({0} : Finset (Fin 2))).map
    (fun k => decide (k.2 ∈ ({0} : Finset (Fin 2))))) true).toReal = 1 / 3 := by
  rw [OddSources.source_index_probability]
  norm_num [OddSources.indexCount, small, Fin.sum_univ_succ, OddSources.card_keys]

-- The larger class can equally well be the class selected inside T.
example : (((OddSources.source large large_ne large_compl_ne ({0} : Finset (Fin 2))).map
    (fun k => decide (k.2 ∈ ({0} : Finset (Fin 2))))) true).toReal = 2 / 3 := by
  rw [OddSources.source_index_probability]
  norm_num [OddSources.indexCount, large, Fin.sum_univ_succ, OddSources.card_keys]

-- Two output bits, not merely a Bool × O surrogate in the public statement.
example (ext : Fin 3 × Fin 4 → (Fin 2 → Bool)) :
    ∃ T, (1 : ℝ) / 6 ≤ dist
      ((OddSources.source small small_ne small_compl_ne T).map ext)
      (PMF.uniformOfFintype (Fin 2 → Bool)) := by
  convert OddSources.no_string_extractor small small_ne small_compl_ne
    (by decide) 2 (by omega) ext using 1; norm_num

-- Matching all-source bounds and attained equality in the reversed orientation.
example : ∃ g : Fin 4 → Bool,
    (∀ T, dist ((OddSources.source large large_ne large_compl_ne T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 6) ∧
    (∃ T, dist ((OddSources.source large large_ne large_compl_ne T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = (1 : ℝ) / 6) := by
  obtain ⟨g, _, hu, T, ht⟩ := OddSources.exists_tight_index_extractor
    (I := Fin 4) large large_ne large_compl_ne 1 (Or.inr (by decide)) (by decide)
  exact ⟨g, by norm_num at hu; exact hu, T, by norm_num at ht; exact ht⟩

-- Seven branches give the r=3 constant 1/14, using actual finite sources.
example (ext : Fin 7 × Fin 2 → Bool) :
    ∃ T, (1 : ℝ) / 14 ≤ dist
      ((OddSources.source ({0, 1, 2, 3} : Finset (Fin 7)) (by decide) (by decide) T).map ext)
      (PMF.uniformOfFintype Bool) := by
  convert OddSources.no_bit_extractor ({0, 1, 2, 3} : Finset (Fin 7))
    (I := Fin 2) (by decide) (by decide) (by decide) ext using 1; norm_num

-- A singleton index has no balanced bit and cannot attain the even-index upper bound.
example (g : Fin 1 → Bool) :
    dist ((source (∅ : Finset (Fin 1))).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = (1 : ℝ) / 2 := by
  have he : (fun k : Key (Fin 1) => g k.2) = fun _ => g 0 := by
    funext k
    rw [Fin.eq_zero k.2]
  rw [he]
  have hm := PMF.map_const (source (∅ : Finset (Fin 1))) (g 0)
  rw [← Function.const_def] at hm
  rw [hm, PMF.dist_uniformOfFintype_bool]
  cases hg : g 0 <;> norm_num [PMF.pure_apply]

/-- The original padded construction, at a concrete even index size. -/
theorem four_index_padded_tight : ∃ g : Fin 4 → Bool,
    (∀ T, dist ((paddedSource T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 6) ∧
    (∃ T, dist ((paddedSource T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = (1 : ℝ) / 6) :=
  exists_tight_padded_bit_extractor (by decide)

-- All three ambient branches are present across the two extreme original sources.
example : keys (univ : Finset (Fin 4)) ∪ keys ∅ = univ := by
  ext ⟨b, i⟩
  cases b <;> simp

-- Nonempty complementary choices are substantive: neither extreme branch set works.
example : ¬(∅ : Finset (Fin 3)).Nonempty := by decide
example : ¬(univ \ (univ : Finset (Fin 3))).Nonempty := by decide

-- Even branch cardinality permits perfect extraction on every source in this class.
example : ∃ ext : (Bool × Bool) × Fin 1 → Bool, ∀ T : Finset (Fin 1),
    dist ((OddSources.source ({(false, false), (false, true)} : Finset (Bool × Bool))
      (by decide) (by decide) T).map ext) (PMF.uniformOfFintype Bool) = 0 := by
  refine ⟨fun ((_, bit), _) => bit, ?_⟩
  intro T
  fin_cases T <;>
    norm_num [PMF.dist_uniformOfFintype_bool, PMF.map_apply_toReal, OddSources.source,
      PMF.uniformOfFinset_apply, OddSources.card_keys, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_succ]

end CslibFrontierTests.OddSources
