/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources
public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomnessBinary
import all Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness

/-!
# Exact two-party extraction error

The `1/6` lower bound for the original source laws of [Aggarwal2026], Section 3,
is sharp. This module identifies those laws with the common complementary-branch
family and transports its balanced-index extractor, including the padded ambient
key alphabet. No source law is replaced by a different gadget.

## Main results

* `exists_tight_bit_extractor`: exact `1/6` worst-source error on the original `source`.
* `exists_tight_padded_bit_extractor`: the same result on `paddedSource`.
* `binary_padded_extraction_tight`: nonvacuous instantiation at every binary field size.

## References

* [Aggarwal2026], Theorem 4.1 with `n = 2` and Lemma 4.4, submission PDF pp. 8–9.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

open Finset Cslib.Probability
open scoped Cslib.Probability.PMF

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

private theorem central_nonempty : ({Branch.central} : Finset Branch).Nonempty := by decide

private theorem sides_nonempty :
    (univ \ ({Branch.central} : Finset Branch)).Nonempty := by decide

omit [Nonempty V] in
/-- The generic branch family recovers precisely the original three-branch supports. -/
theorem odd_keys_eq_keys (T : Finset V) :
    OddSources.keys {Branch.central} T = keys T := by
  ext ⟨b, i⟩
  cases b <;> simp [OddSources.mem_keys, mem_keys]

/-- Identification of actual uniform laws, rather than merely equal support sizes. -/
theorem odd_source_eq_source (T : Finset V) :
    OddSources.source {Branch.central} (by decide) (by decide) T = source T := by
  unfold OddSources.source source
  congr 1
  exact odd_keys_eq_keys T

/-- The original flat source family has exact optimal bit extraction error `1/6`
whenever its index space has even cardinality. -/
theorem exists_tight_bit_extractor (heven : Even (Fintype.card V)) :
    ∃ g : V → Bool,
      (∀ T, dist ((source T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 6) ∧
      (∃ T, dist ((source T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) = (1 : ℝ) / 6) := by
  obtain ⟨g, _, hu, T, ht⟩ := OddSources.exists_tight_index_extractor
    (I := V) {Branch.central} central_nonempty sides_nonempty 1 (Or.inl ⟨rfl, by decide⟩) heven
  have hc : Fintype.card Branch = 3 := by decide
  simp only [odd_source_eq_source, hc] at hu ht
  norm_num at hu ht
  exact ⟨g, hu, T, ht⟩

/-- Padding the unused fourth branch preserves the exact optimal `1/6` error. -/
theorem exists_tight_padded_bit_extractor (heven : Even (Fintype.card V)) :
    ∃ g : V → Bool,
      (∀ T, dist ((paddedSource T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 6) ∧
      (∃ T, dist ((paddedSource T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) = (1 : ℝ) / 6) := by
  obtain ⟨g, hu, T, ht⟩ := exists_tight_bit_extractor (V := V) heven
  refine ⟨g, ?_, T, ?_⟩
  · intro S
    simpa only [paddedSource_eq_map, PMF.map_comp, Function.comp_def, pad] using hu S
  · simpa only [paddedSource_eq_map, PMF.map_comp, Function.comp_def, pad] using ht

open scoped Classical in
/-- In particular, every field used by Theorem 1.1 has exact optimal error `1/6`.
The index extractor and source law are those of the original padded construction. -/
theorem binary_padded_extraction_tight (b : ℕ) (hb : 2 ≤ b) :
    let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
    ∃ g : GaloisField 2 b → Bool,
      (∀ T, dist ((paddedSource T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 6) ∧
      (∃ T, dist ((paddedSource T).map (fun k => g k.2))
        (PMF.uniformOfFintype Bool) = (1 : ℝ) / 6) := by
  classical
  let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 b) = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b (by omega)]
  apply exists_tight_padded_bit_extractor
  rw [hc]
  exact even_two.pow_of_ne_zero (by omega)

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
