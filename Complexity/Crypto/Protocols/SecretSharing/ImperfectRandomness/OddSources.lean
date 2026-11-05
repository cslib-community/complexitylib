/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF.Uniform

/-!
# Source classes from complementary branch sets

The common source family in [Aggarwal2026], Sections 4 and 5: at each index,
a source includes either every branch in a fixed set or every branch outside it.
These definitions specify actual uniform laws. They do not assume the extraction
or privacy conclusions of the threshold constructions.

## Main definitions

* `keys`: the allowed branch/index pairs for a choice of indices.
* `source`: the uniform law on those pairs.

## References

* [Aggarwal2026], equations (6) and (8).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources

open Finset Cslib.Probability

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B] [DecidableEq I]

/-- At indices in `T`, take the branches in `A`; at other indices, take the complement. -/
@[expose] def keys (A : Finset B) (T : Finset I) : Finset (B × I) :=
  univ.filter fun k => (k.1 ∈ A ↔ k.2 ∈ T)

/-- Membership records exactly which branch choice is used at an index. -/
@[simp] theorem mem_keys (A : Finset B) (T : Finset I) (k : B × I) :
    k ∈ keys A T ↔ (k.1 ∈ A ↔ k.2 ∈ T) := by
  simp [keys]

/-- The two source blocks are products of their branch and index choices. -/
theorem keys_eq_union_product (A : Finset B) (T : Finset I) :
    keys A T = (A ×ˢ T) ∪ ((univ \ A) ×ˢ (univ \ T)) := by
  ext k
  simp only [mem_keys, mem_union, mem_product, mem_sdiff, mem_univ, true_and]
  tauto

/-- Exact support size for an arbitrary complementary pair of branch classes. -/
theorem card_keys (A : Finset B) (T : Finset I) :
    (keys A T).card = A.card * T.card +
      (Fintype.card B - A.card) * (Fintype.card I - T.card) := by
  have hd : Disjoint A (univ \ A) := disjoint_sdiff
  rw [keys_eq_union_product,
    card_union_of_disjoint (disjoint_product.mpr (Or.inl hd)), card_product, card_product,
    card_sdiff_of_subset (subset_univ A), card_sdiff_of_subset (subset_univ T), card_univ,
    card_univ]

/-- Nonempty branch choices and index space give a nonempty source for every `T`. -/
theorem keys_nonempty [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) : (keys A T).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty I›
  by_cases hi : i ∈ T
  · obtain ⟨b, hb⟩ := hA
    exact ⟨(b, i), by simp [hb, hi]⟩
  · obtain ⟨b, hb⟩ := hAc
    exact ⟨(b, i), by simp [(mem_sdiff.mp hb).2, hi]⟩

/-- The actual flat source indexed by `T`, with no additional dealer randomness. -/
@[expose] noncomputable def source [Nonempty I] (A : Finset B) (hA : A.Nonempty)
    (hAc : (univ \ A).Nonempty) (T : Finset I) : PMF (B × I) :=
  PMF.uniformOfFinset (keys A T) (keys_nonempty A hA hAc T)

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.OddSources
