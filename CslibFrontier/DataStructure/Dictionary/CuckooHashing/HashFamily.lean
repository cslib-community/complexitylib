/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CuckooHashing.Basic
public import CslibFrontier.Probability.PMF

/-!
# Probabilistic cuckoo hash-pair contract

`IsCuckooHashPair` packages the expected displacement, whole-set rehash, and incremental replay
failure bounds required by a cuckoo dictionary. The seed distribution and both hash functions are
arbitrary; no machine representation or concrete hash-family construction is assumed.

The contract is an original strengthened sufficient interface inspired by Pagh and Rodler
[PaghRodler2004], Section 2.3 (8 December 2003 manuscript, pp. 6–10). Its walk count takes the
supremum over all valid placements, and its goodness event requires successful replay in every
insertion order. `CslibFrontier.DataStructure.Dictionary.CuckooHashing` proves the contract from
sufficient independence assumptions. The Word-RAM specialization is in
`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Analysis`.

## Main definitions

* `IsCuckooHashPair`: expected walk bound, whole-set failure probability at most `1 / 2`, and
  one-step replay failure bound over an arbitrary seed law.

## Main results

* `IsCuckooHashPair.mono_consts`: monotonicity in the walk and rehash constants.
* `isCuckooHashPair_le_two`: hash-pair-independent instance for `n_max ≤ 2` and positive eviction
  cap, with `C_walk = 1` and `C_reh = 0`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, pp. 6–10).
-/

public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing

open Cslib.Probability
open scoped ENNReal

/-- **General cuckoo hash pair interface (`IsCuckooHashPair`)**:
an original strengthened sufficient assumption bundle inspired by Pagh and Rodler [PaghRodler2004]
(8 December 2003 manuscript, Section 2.3 "Analysis", pp. 6–10), asserting over a
seed distribution `μ : PMF Θ` and hash pair `h₁ h₂ : Θ → Fin U → Fin m`:
1. (`expected_walk_le`): for any set `S` of fewer than `n_max` keys and absent key `u ∉ S`, the
   expected number of worst-case displacement rounds `cuckooWalkRounds` (`sSup` over all
   `ValidPlacement`s of `S`) is at most `C_walk` (cf. [PaghRodler2004], §2.3, Lemma 1 on manuscript
   p. 7 and Eq. (3) on manuscript p. 9);
2. (`rehash_prob_le_half`): for any set `S` of at most `n_max` keys, the probability that `θ ∼ μ`
   fails `GoodForSet` (all `Nodup` sublists in `S`) is at most `1 / 2` (so each rehash attempt
   succeeds with probability at least `1 / 2` and the surviving seed set has measure at least
   `1 / 2`); and
3. (`step_rehash_prob_le`): for any insertion-order prefix `ks` of fewer than `n_max` distinct keys
   and new key `u ∉ ks`, the one-step incremental failure probability that `θ ∼ μ` survives
   `pureReplay (h₁ θ) (h₂ θ) MaxLoop ks` yet fails `pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])`
   is at most `C_reh / (max n_max 1 * max MaxLoop 1)` (cf. [PaghRodler2004], §2.3, manuscript
   pp. 9–10). -/
structure IsCuckooHashPair {Θ : Type*} (μ : PMF Θ) {U m : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (n_max MaxLoop C_walk C_reh : ℕ) : Prop where
  /-- Expected displacement rounds per new-key insertion is at most `C_walk`. -/
  expected_walk_le : ∀ (S : Finset (Fin U)) (u : Fin U), S.card < n_max → u ∉ S →
    (∑' θ : Θ, μ θ * (cuckooWalkRounds (h₁ θ) (h₂ θ) MaxLoop S u : ℝ≥0∞)) ≤ C_walk
  /-- Whole-set rehash failure probability on any key set `S` of size `≤ n_max` is at most
  `1 / 2`. -/
  rehash_prob_le_half : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
    μ.toOuterMeasure {θ : Θ | ¬ GoodForSet (h₁ θ) (h₂ θ) MaxLoop S} ≤ 1 / 2
  /-- One-step incremental rehash probability when appending a new key `u ∉ ks` to a duplicate-free
  key list `ks` of length `< n_max` is at most `C_reh / (max n_max 1 * max MaxLoop 1)`. -/
  step_rehash_prob_le : ∀ (ks : List (Fin U)) (u : Fin U),
    ks.Nodup → ks.length < n_max → u ∉ ks →
    μ.toOuterMeasure
      {θ : Θ | (pureReplay (h₁ θ) (h₂ θ) MaxLoop ks).isSome ∧
        (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isNone} ≤
      (C_reh : ℝ≥0∞) / ((max n_max 1 : ℝ≥0∞) * (max MaxLoop 1 : ℝ≥0∞))

/-- Monotonicity of `IsCuckooHashPair` in the constants `C_walk` and `C_reh`. -/
theorem IsCuckooHashPair.mono_consts {Θ : Type*} {μ : PMF Θ} {U m : ℕ}
    {h₁ h₂ : Θ → Fin U → Fin m}
    {n_max MaxLoop C_walk C_walk' C_reh C_reh' : ℕ}
    (hp : IsCuckooHashPair μ h₁ h₂ n_max MaxLoop C_walk C_reh)
    (hw : C_walk ≤ C_walk') (hr : C_reh ≤ C_reh') :
    IsCuckooHashPair μ h₁ h₂ n_max MaxLoop C_walk' C_reh' where
  expected_walk_le S u hS hu :=
    (hp.expected_walk_le S u hS hu).trans (by exact_mod_cast hw)
  rehash_prob_le_half := hp.rehash_prob_le_half
  step_rehash_prob_le ks u hnodup hlen hu :=
    (hp.step_rehash_prob_le ks u hnodup hlen hu).trans
      (ENNReal.div_le_div_right (by exact_mod_cast hr) _)

/-- Reusable hash-pair-independent `IsCuckooHashPair` instance for `n_max ≤ 2` and `0 < MaxLoop`
(`C_walk = 1`, `C_reh = 0`) over any seed distribution `μ` and arbitrary hash pair `(h₁, h₂)`
(without any independence assumption): inserting up to `2` keys into two tables `T₁, T₂` always
completes in `1` round with zero rehashes (even if both keys collide in `T₁`, the displaced first
key is placed into an empty slot of `T₂`). -/
theorem isCuckooHashPair_le_two {Θ : Type*} (μ : PMF Θ) {U m n_max MaxLoop : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (hn : n_max ≤ 2) (hloop : 0 < MaxLoop) :
    IsCuckooHashPair μ h₁ h₂ n_max MaxLoop 1 0 where
  expected_walk_le S u hcard _ := by
    have hcard1 : S.card ≤ 1 := by omega
    calc (∑' θ : Θ, μ θ * (cuckooWalkRounds (h₁ θ) (h₂ θ) MaxLoop S u : ℝ≥0∞))
      _ ≤ ∑' θ : Θ, μ θ * (1 : ℝ≥0∞) := by
          gcongr with θ
          exact_mod_cast cuckooWalkRounds_le_one_of_card_le_one (h₁ θ) (h₂ θ) MaxLoop hcard1 u
      _ = ((1 : ℕ) : ℝ≥0∞) := by
          simp only [mul_one, PMF.tsum_coe, Nat.cast_one]
  rehash_prob_le_half S hcard := by
    have hgood : ∀ θ : Θ, GoodForSet (h₁ θ) (h₂ θ) MaxLoop S := by
      intro θ ks hnodup hsub
      have hlen : ks.length ≤ 2 := by
        have h1 : ks.toFinset ⊆ S := fun x hx => hsub x (List.mem_toFinset.mp hx)
        have h2 : ks.toFinset.card ≤ S.card := Finset.card_le_card h1
        rw [List.card_toFinset, List.dedup_eq_self.mpr hnodup] at h2
        omega
      exact pureReplay_isSome_of_length_le_two _ _ hloop hlen
    have hempty : {θ : Θ | ¬ GoodForSet (h₁ θ) (h₂ θ) MaxLoop S} = ∅ := by
      ext θ; simp [hgood θ]
    rw [hempty]
    simp
  step_rehash_prob_le ks u _ hlen _ := by
    have hlen' : (ks ++ [u]).length ≤ 2 := by simp; omega
    have hsome : ∀ θ : Θ, (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isSome :=
      fun θ => pureReplay_isSome_of_length_le_two _ _ hloop hlen'
    have hempty :
        {θ : Θ | (pureReplay (h₁ θ) (h₂ θ) MaxLoop ks).isSome ∧
          (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isNone} = ∅ := by
      ext θ
      simp [Option.isNone_iff_eq_none, Option.ne_none_iff_isSome.mpr (hsome θ)]
    rw [hempty]
    simp

end Cslib.DataStructure.Dictionary.CuckooHashing
