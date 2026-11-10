/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctValidHistory
public import CslibFrontier.DataStructure.HashFamily.WordRAM.ReducedKWise
import CslibFrontier.Tactic.Realize

/-!
# Quotient Hashing, `DictStateInv`, and Feistel-Dispatched `Memory.Prog` Operations

This module couples the bucket-level `Memory.Prog` operations of the fixed-capacity succinct
dictionary with the two-stage universe-reduced 3-wise independent hash family
(`Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise`) and proves the full dictionary-level state
transition, space, initialization, and expected probe-excess bounds.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.qBits`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.hashB`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.hashSpace`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.space`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.initSteps`:
  hash parameter instantiation, total Word-RAM footprint, and initialization instruction budget.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.bucketMapOfState`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.DictStateInv`:
  coupling between `Dictionary.State U` and `BucketStateInv` via one-round Feistel reconstruction
  `feistelReconstruct`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.extractQuotProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryWithHashProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertWithHashProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deletePrepWithHashProg`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteFinishWithHashProg`:
  `Memory.Prog` operations performing Feistel bit extraction and bucket dispatch, realized to
  native Word-RAM code via `realize`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.initSteps_le`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.space_le_succinctWords`:
  linear initialization instruction bound and succinct word-space bound.
* `tsum_uniform_probeExcess_reducedPolyHash_le_five`:
  expected combined probe excess `≤ 5` under a uniformly sampled `ReducedPolySeed`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.queryWithHashProg_dict_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.insertWithHashProg_dict_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.deleteWithHashProg_dict_spec`:
  dictionary-level functional correctness and amortized `memoryCost` bounds for `query`, `insert`,
  and two-phase `delete`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Hash parameters, `space_le_succinctWords`, and `initSteps_le` -/

/-- Effective quotient bit-width `max (quotientBits U n_max) 1 ≥ 1` passed to `ReducedKWise`. -/
@[expose]
def qBits (U n_max : ℕ) : ℕ :=
  max (quotientBits U n_max) 1

/-- Reduction target bit-width parameter `totalMicroBits n_max + 1 = ⌊log₂ n_max⌋ + 1` passed to
`ReducedKWise`, ensuring `n_max + 1 ≤ 2 ^ hashB n_max`. -/
@[expose]
def hashB (n_max : ℕ) : ℕ :=
  totalMicroBits n_max + 1

/-- Word-RAM footprint of the 3-wise independent quotient hash family (`ReducedKWise.space`). -/
@[expose]
def hashSpace (U w n_max : ℕ) : ℕ :=
  ReducedKWise.space w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3

/-- Total Word-RAM footprint `totalSpace U V w n_max (hashSpace U w n_max)` of the succinct
dictionary in `w`-bit words. -/
@[expose]
def space (U V w n_max : ℕ) : ℕ :=
  totalSpace U V w n_max (hashSpace U w n_max)

/-- Initialization instruction budget (`2` plus `ReducedKWise.initTableSteps` and
`ReducedKWise.resampleSteps`; with `3` allocation instructions in `allocSpan`, the total
initialization time is `initTime = initSteps U n_max + 1`). -/
@[expose]
def initSteps (U n_max : ℕ) : ℕ :=
  2 + ReducedKWise.initTableSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) +
    ReducedKWise.resampleSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3

theorem qBits_pos (U n_max : ℕ) : 0 < qBits U n_max :=
  lt_max_of_lt_right Nat.one_pos

theorem quotientBits_le_qBits (U n_max : ℕ) : quotientBits U n_max ≤ qBits U n_max :=
  le_max_left _ _

theorem two_pow_quotientBits_le_two_pow_qBits (U n_max : ℕ) :
    2 ^ quotientBits U n_max ≤ 2 ^ qBits U n_max :=
  Nat.pow_le_pow_right two_pos (quotientBits_le_qBits U n_max)

theorem qBits_le_of_le_pow {U w n_max : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) :
    qBits U n_max ≤ w := by
  unfold qBits
  exact max_le (quotientBits_le_of_le_pow hU) hw

theorem totalMicroBits_le_three_mul_hashB (n_max : ℕ) :
    totalMicroBits n_max ≤ 3 * hashB n_max := by
  unfold hashB
  omega

theorem hashB_div_two_le_log (n_max : ℕ) :
    hashB n_max / 2 ≤ Nat.log 2 n_max := by
  unfold hashB
  rw [totalMicroBits_eq_log]
  omega

theorem two_pow_hashB_div_two_le (n_max : ℕ) :
    2 ^ (hashB n_max / 2) ≤ max n_max 1 := by
  calc 2 ^ (hashB n_max / 2)
      ≤ 2 ^ Nat.log 2 n_max := Nat.pow_le_pow_right two_pos (hashB_div_two_le_log n_max)
    _ = totalMicroBuckets n_max := by rw [totalMicroBuckets, totalMicroBits_eq_log]
    _ ≤ max n_max 1 := totalMicroBuckets_le n_max

theorem max_eight_two_pow_hashB_div_two_le (n_max : ℕ) :
    max 8 (2 ^ (hashB n_max / 2)) ≤ 8 + n_max := by
  have h := two_pow_hashB_div_two_le n_max
  omega

theorem reducedTableBits_hash_le (U n_max : ℕ) :
    reducedTableBits (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) ≤
      8 + n_max :=
  (reducedTableBits_le (w₀ := qBits U n_max) (totalMicroBits_le_three_mul_hashB n_max)).trans
    (max_eight_two_pow_hashB_div_two_le n_max)

theorem two_pow_two_mul_reducedChunkBits_hash_le (U n_max : ℕ) :
    2 ^ (2 * reducedChunkBits
      (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max))) ≤ 8 + n_max := by
  set t := reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)
  have hc_pos : 0 < 2 * reducedChunkBits t := by
    have := reducedChunkBits_pos t; omega
  have hle : 2 ^ (2 * reducedChunkBits t) ≤ reducedTableBits t := by
    dsimp only [reducedTableBits]
    exact Nat.le_mul_of_pos_left _ hc_pos
  exact hle.trans (reducedTableBits_hash_le U n_max)

/-- Explicit linear bound on `initSteps U n_max`: `initSteps U n_max ≤ 31 * n_max + 1091`. -/
theorem initSteps_le (U n_max : ℕ) :
    initSteps U n_max ≤ 31 * n_max + 1091 := by
  unfold initSteps ReducedKWise.initTableSteps ReducedKWise.resampleSteps
  have htab := two_pow_two_mul_reducedChunkBits_hash_le U n_max
  have hseed := ReducedKWise.seedWords_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  omega

/-- Multiplicative form of `initSteps_le`: `initSteps U n_max ≤ 1091 * (n_max + 1)`. -/
theorem initSteps_le_mul (U n_max : ℕ) :
    initSteps U n_max ≤ 1091 * (n_max + 1) := by
  have h := initSteps_le U n_max
  omega

theorem eight_le_hashSpace (U w n_max : ℕ) : 8 ≤ hashSpace U w n_max := by
  unfold hashSpace ReducedKWise.space ReducedKWise.seedWords ReducedKWise.tableWords
    reducedLimbCount reducedHalfLimbs reducedTableWords
  have : 1 ≤
      3 ^ min (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) 3 :=
    Nat.one_le_pow _ 3 (by decide)
  have : 1 ≤ 2 ^ (2 * reducedChunkBits
      (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) -
      reducedPackShift
        (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) w) :=
    Nat.one_le_two_pow
  omega

theorem two_le_w_of_fits_space {U V w n_max base : ℕ}
    (hfit : Fits w (base + space U V w n_max)) : 2 ≤ w := by
  have h8 : 8 ≤ space U V w n_max := by
    unfold space totalSpace offGM offLM offVal offQuot
    have := eight_le_hashSpace U w n_max
    omega
  have hlt : 8 < 2 ^ w := lt_of_le_of_lt (by omega) hfit
  by_contra h
  have hw1 : w ≤ 1 := by omega
  have hpow : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos hw1
  omega

theorem two_mul_reducedChunkBits_hash_le {U w n_max : ℕ}
    (hw2 : 2 ≤ w) (hnU : n_max ≤ U) (hU : U ≤ 2 ^ w) :
    2 * reducedChunkBits
      (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) ≤ w :=
  two_mul_reducedChunkBits_le
    (qBits_le_of_le_pow (by omega) hU)
    (totalMicroBits_le_of_le_pow hnU hU)
    hw2

theorem two_mul_reducedChunkBits_hash_lt {U V w n_max base : ℕ}
    (hnU : n_max ≤ U) (hU : U ≤ 2 ^ w)
    (hfit : Fits w (base + space U V w n_max)) :
    2 * reducedChunkBits
      (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) < w := by
  have hw2 := two_le_w_of_fits_space hfit
  have hfit_hash : Fits w (base + hashSpace U w n_max) := by
    refine hfit.of_le ?_
    unfold space totalSpace offGM offLM offVal offQuot
    omega
  exact ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
    (two_mul_reducedChunkBits_hash_le hw2 hnU hU) hfit_hash

theorem tableWords_hash_le {U w n_max : ℕ} (hw : 0 < w) (hnU : n_max ≤ U) (hU : U ≤ 2 ^ w) :
    ReducedKWise.tableWords w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) ≤
      12 + packedWords (2 * n_max) 1 w := by
  by_cases hw2 : 2 ≤ w
  · have htw := ReducedKWise.tableWords_le
      (w₀ := qBits U n_max) (b := hashB n_max)
      (qBits_le_of_le_pow (n_max := n_max) hw hU)
      (totalMicroBits_le_three_mul_hashB n_max)
      (totalMicroBits_le_of_le_pow hnU hU)
      hw2
    have hm := max_eight_two_pow_hashB_div_two_le n_max
    have hdiv1 : 2 * max 8 (2 ^ (hashB n_max / 2)) / w ≤ (16 + 2 * n_max) / w :=
      Nat.div_le_div_right (by omega)
    have hdiv2 : (16 + 2 * n_max) / w < 9 + (2 * n_max + w - 1) / w := by
      refine Nat.div_lt_of_lt_mul ?_
      have h2 := Nat.div_add_mod (2 * n_max + w - 1) w
      have hm2 : (2 * n_max + w - 1) % w < w := Nat.mod_lt _ hw
      have h16 : 16 ≤ w * 8 := by omega
      have hmul : w * (9 + (2 * n_max + w - 1) / w) =
          w * 8 + (w * ((2 * n_max + w - 1) / w) + w) := by ring
      omega
    simp only [packedWords, Nat.mul_one]
    omega
  · have hw1 : w = 1 := by omega
    subst hw1
    have hU2 : U ≤ 2 := hU
    have hn2 : n_max ≤ 2 := hnU.trans hU2
    have hq1 : qBits U n_max = 1 := by
      unfold qBits quotientBits keyBits
      have : Nat.clog 2 U ≤ 1 := by
        calc Nat.clog 2 U ≤ Nat.clog 2 2 := Nat.clog_mono_right 2 hU2
          _ = 1 := by decide
      omega
    have htm1 : totalMicroBits n_max ≤ 1 := by
      rw [totalMicroBits_eq_log]
      calc Nat.log 2 n_max ≤ Nat.log 2 2 := Nat.log_mono_right hn2
        _ = 1 := by decide
    have hB : reducedTargetBits (qBits U n_max) (hashB n_max) (totalMicroBits n_max) ≤ 1 := by
      unfold reducedTargetBits
      rw [hq1]
      omega
    have ht0 :
        reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max) = 0 := by
      unfold reducedTrinomialStep trinomialStepAux
      rw [ite_eq_left (by omega)]
    have hc1 :
        reducedChunkBits
          (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max)) = 1 := by
      rw [ht0]
      decide
    have htw4 :
        ReducedKWise.tableWords 1 (qBits U n_max) (hashB n_max) (totalMicroBits n_max) ≤ 4 := by
      unfold ReducedKWise.tableWords reducedTableWords
      rw [hc1]
      exact Nat.pow_le_pow_right two_pos (Nat.sub_le 2 _)
    omega

theorem hashSpace_le {U w n_max : ℕ} (hw : 0 < w) (hnU : n_max ≤ U) (hU : U ≤ 2 ^ w) :
    hashSpace U w n_max ≤ 175 + packedWords (2 * n_max) 1 w := by
  unfold hashSpace ReducedKWise.space
  have hs := ReducedKWise.seedWords_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  have ht := tableWords_hash_le hw hnU hU
  omega

/-- **Succinct word-space bound (`space_le_succinctWords`):**
for every `0 < w`, `n_max ≤ U`, and `U ≤ 2 ^ w` (including `Fits w U`), the total space
`space U V w n_max` is at most `Dynamic.succinctWords 81 213 U V w n_max`. -/
theorem space_le_succinctWords {U V w n_max : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U ≤ 2 ^ w) :
    space U V w n_max ≤ Dynamic.succinctWords 81 213 U V w n_max := by
  have hh := hashSpace_le hw hnU hU
  have htab := totalSpace_le_succinctWords (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := hashSpace U w n_max)
  have h12345 := div_add_packedWords_le
    (Dynamic.optBits U V n_max + 79 * n_max * Dynamic.logLogFactor n_max) 35
    (2 * n_max) 1 w
  have hll := Dynamic.one_le_logLogFactor n_max
  have h2n : (2 * n_max) * 1 ≤ 2 * n_max * Dynamic.logLogFactor n_max := by
    calc (2 * n_max) * 1 = 2 * n_max * 1 := by ring
      _ ≤ 2 * n_max * Dynamic.logLogFactor n_max := by gcongr
  have hnum :
      Dynamic.optBits U V n_max + 79 * n_max * Dynamic.logLogFactor n_max +
        (2 * n_max) * 1 + w - 1 ≤
      Dynamic.optBits U V n_max + 81 * n_max * Dynamic.logLogFactor n_max + w - 1 := by
    have : 81 * n_max * Dynamic.logLogFactor n_max =
        79 * n_max * Dynamic.logLogFactor n_max + 2 * n_max * Dynamic.logLogFactor n_max := by ring
    omega
  have hdiv :
      (Dynamic.optBits U V n_max + 79 * n_max * Dynamic.logLogFactor n_max +
        (2 * n_max) * 1 + w - 1) / w ≤
      (Dynamic.optBits U V n_max + 81 * n_max * Dynamic.logLogFactor n_max + w - 1) / w :=
    Nat.div_le_div_right hnum
  unfold space
  unfold Dynamic.succinctWords at htab ⊢
  omega

/-! ## Section 2: Expected `probeExcess` bound (`≤ 5`) under `ReducedPolySeed` -/

/-- Seed space `ReducedPolySeed (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3` of the
two-stage quotient hash family. -/
abbrev QuotHashSeed (U n_max : ℕ) : Type :=
  ReducedPolySeed (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3

/-- Stage 1 multiply-shift reduction mapping `u : Fin U` via `quotientFin U n_max u` into
`Fin (2 ^ min (qBits U n_max) (3 * hashB n_max))`. -/
@[expose]
def qStage1 (U n_max : ℕ) (α : ReducedTopSeed (qBits U n_max)) (u : Fin U) :
    Fin (2 ^ min (qBits U n_max) (3 * hashB n_max)) :=
  multiplyShiftReduced (2 ^ quotientBits U n_max) (qBits U n_max) (3 * hashB n_max) α
    (quotientFin U n_max u)

/-- Stage 2 degree-`< 3` trinomial polynomial hash mapping reduced quotients into
`Fin (2 ^ totalMicroBits n_max)`. -/
@[expose]
noncomputable def polyStage2 (U n_max : ℕ) :
    ReducedBotSeed (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 →
      Fin (2 ^ min (qBits U n_max) (3 * hashB n_max)) →
        Fin (2 ^ totalMicroBits n_max) :=
  trinomialPolyHash
    (reducedTrinomialStep (qBits U n_max) (hashB n_max) (totalMicroBits n_max))
    3
    (2 ^ min (qBits U n_max) (3 * hashB n_max))
    (totalMicroBits n_max)

theorem isKWiseIndependentHash_polyStage2 (U n_max : ℕ) :
    IsKWiseIndependentHash 3 (polyStage2 U n_max) :=
  isKWiseIndependentHash_trinomialPolyHash
    (two_pow_min_le_two_pow_reducedTrinomialDeg (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max))
    (le_reducedTrinomialDeg (qBits U n_max) (hashB n_max) (totalMicroBits n_max))

/-- **Two-stage expected `probeExcess` bound (`≤ 5`):**
for any `S : Finset (Fin U)` and `u : Fin U` with `#(S.erase u) ≤ n_max ≤ U`, the expected
`probeExcess` under a uniformly chosen `θ : QuotHashSeed U n_max` is at most `5`. -/
theorem tsum_uniform_probeExcess_reducedPolyHash_le_five {U n_max : ℕ} (hnU : n_max ≤ U)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max) :
    (∑' θ : QuotHashSeed U n_max,
      (PMF.uniformOfFintype (QuotHashSeed U n_max)) θ *
        (probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2 S u : ℝ≥0∞)) ≤ 5 := by
  classical
  let S_Q : Finset (Fin (2 ^ quotientBits U n_max)) :=
    (insert u (S.erase u)).image (quotientFin U n_max)
  let G : Finset (ReducedTopSeed (qBits U n_max)) :=
    reducedGoodTop (2 ^ quotientBits U n_max) (qBits U n_max) (3 * hashB n_max) S_Q
  have hG : ∀ α ∈ G, ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qStage1 U n_max α u₁ = qStage1 U n_max α u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val := by
    intro α hα u₁ hu₁ u₂ hu₂ hcoll
    have hinj := mem_reducedGoodTop.mp hα
    have hq₁ : quotientFin U n_max u₁ ∈ S_Q := mem_image_of_mem _ hu₁
    have hq₂ : quotientFin U n_max u₂ ∈ S_Q := mem_image_of_mem _ hu₂
    exact keyQuotient_eq_of_quotientFin_eq hnU u₁ u₂ (hinj hq₁ hq₂ hcoll)
  have hbad : #(univ \ G) * (2 * #(S.erase u)) ≤
      2 * Fintype.card (ReducedTopSeed (qBits U n_max)) := by
    have hcard_SQ : #S_Q ≤ #(S.erase u) + 1 :=
      card_image_le.trans (card_insert_le u (S.erase u))
    have h1 : #S_Q ≤ n_max + 1 := hcard_SQ.trans (by omega)
    have h2 : #S_Q - 1 ≤ n_max := by omega
    have h3 : 2 * #(S.erase u) ≤ 2 * (n_max + 1) := by omega
    have hpow_B : n_max + 1 ≤ 2 ^ hashB n_max := by
      unfold hashB
      rw [totalMicroBits_eq_log]
      rcases Nat.eq_zero_or_pos n_max with rfl | hn
      · decide
      · exact Nat.lt_pow_succ_log_self one_lt_two n_max
    have hcube : (n_max + 1) ^ 3 ≤ 2 ^ (3 * hashB n_max) := by
      calc (n_max + 1) ^ 3
          ≤ (2 ^ hashB n_max) ^ 3 := Nat.pow_le_pow_left hpow_B 3
        _ = 2 ^ (3 * hashB n_max) := by rw [← Nat.pow_mul, Nat.mul_comm]
    have hprod_le : (#S_Q * (#S_Q - 1)) * (2 * #(S.erase u)) ≤ 2 * 2 ^ (3 * hashB n_max) := by
      have hm1 : #S_Q * (#S_Q - 1) ≤ (n_max + 1) * (n_max + 1) :=
        Nat.mul_le_mul h1 (by omega)
      have hm2 : (#S_Q * (#S_Q - 1)) * (2 * #(S.erase u)) ≤
          ((n_max + 1) * (n_max + 1)) * (2 * (n_max + 1)) :=
        Nat.mul_le_mul hm1 h3
      have hring : ((n_max + 1) * (n_max + 1)) * (2 * (n_max + 1)) = 2 * (n_max + 1) ^ 3 := by
        ring
      rw [hring] at hm2
      exact hm2.trans (Nat.mul_le_mul_left 2 hcube)
    have hunion := card_not_injOn_multiplyShiftReduced_le
      (U := 2 ^ quotientBits U n_max) (w₀ := qBits U n_max) (R := 3 * hashB n_max)
      (qBits_pos U n_max) (two_pow_quotientBits_le_two_pow_qBits U n_max) S_Q
    have hmul :
        (#(univ \ G) * (2 * #(S.erase u))) * 2 ^ (3 * hashB n_max) ≤
          (2 * 2 ^ (qBits U n_max - 1)) * 2 ^ (3 * hashB n_max) := by
      calc (#(univ \ G) * (2 * #(S.erase u))) * 2 ^ (3 * hashB n_max)
          = (#(univ \ G) * 2 ^ (3 * hashB n_max)) * (2 * #(S.erase u)) := by ring
        _ ≤ ((#S_Q * (#S_Q - 1)) * 2 ^ (qBits U n_max - 1)) * (2 * #(S.erase u)) :=
            Nat.mul_le_mul_right _ hunion
        _ = ((#S_Q * (#S_Q - 1)) * (2 * #(S.erase u))) * 2 ^ (qBits U n_max - 1) := by ring
        _ ≤ (2 * 2 ^ (3 * hashB n_max)) * 2 ^ (qBits U n_max - 1) :=
            Nat.mul_le_mul_right _ hprod_le
        _ = (2 * 2 ^ (qBits U n_max - 1)) * 2 ^ (3 * hashB n_max) := by ring
    have hcancel := Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos (3 * hashB n_max))
    simpa [ReducedTopSeed] using hcancel
  have hmain := tsum_uniform_probeExcess_twoStage_le
    (qOf := qStage1 U n_max) (H := polyStage2 U n_max) (C_bad := 2)
    (isKWiseIndependentHash_polyStage2 U n_max) S u hS G hG hbad
  simpa using hmain

/-! ## Section 3: `bucketMapOfState`, `DictStateInv`, and probe-excess cardinality bounds -/

/-- Evaluate the two-stage quotient hash on an arbitrary natural-number quotient `q`. -/
@[expose]
noncomputable def evalQuotHash (U n_max : ℕ) (θ : QuotHashSeed U n_max) (q : ℕ) :
    Fin (2 ^ totalMicroBits n_max) :=
  reducedPolyHash (2 ^ quotientBits U n_max) (qBits U n_max) (hashB n_max) (totalMicroBits n_max)
    3 θ ⟨q % 2 ^ quotientBits U n_max, Nat.mod_lt _ (by positivity)⟩

/-- Integer value `(evalQuotHash U n_max θ q).val < 2 ^ totalMicroBits n_max`. -/
@[expose]
noncomputable def hValOfSeed (U n_max : ℕ) (θ : QuotHashSeed U n_max) (q : ℕ) : ℕ :=
  (evalQuotHash U n_max θ q).val

/-- Local micro-bucket index `hValOfSeed U n_max θ q >>> bucketBits n_max < numMicroPerBucket n_max`
associated with quotient `q`. -/
@[expose]
noncomputable def mOfSeed (U n_max : ℕ) (θ : QuotHashSeed U n_max) (q : ℕ) : ℕ :=
  hValOfSeed U n_max θ q >>> bucketBits n_max

theorem hValOfSeed_lt (U n_max : ℕ) (θ : QuotHashSeed U n_max) (q : ℕ) :
    hValOfSeed U n_max θ q < 2 ^ totalMicroBits n_max :=
  (evalQuotHash U n_max θ q).isLt

theorem mOfSeed_lt (U n_max : ℕ) (θ : QuotHashSeed U n_max) (q : ℕ) :
    mOfSeed U n_max θ q < numMicroPerBucket n_max := by
  unfold mOfSeed numMicroPerBucket
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add]
  exact hValOfSeed_lt U n_max θ q

theorem evalQuotHash_keyQuotient_eq (U n_max : ℕ) (θ : QuotHashSeed U n_max) (u : Fin U) :
    evalQuotHash U n_max θ (keyQuotient (bucketBits n_max) u.val) =
      polyStage2 U n_max θ.2 (qStage1 U n_max θ.1 u) :=
  rfl

theorem feistelBucketHash_val_eq_hValOfSeed (U n_max : ℕ) (θ : QuotHashSeed U n_max) (u : Fin U) :
    (feistelBucketHash n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2 u).val =
      feistelBucket (bucketBits n_max) (hValOfSeed U n_max θ) u.val := by
  rw [feistelBucketHash_val_eq_feistelBucket]
  rfl

theorem feistelLocalMicro_val_eq_mOfSeed (U n_max : ℕ) (θ : QuotHashSeed U n_max) (u : Fin U) :
    (feistelLocalMicro n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2 u).val =
      mOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) := by
  dsimp only [feistelLocalMicro, mOfSeed, hValOfSeed]
  rw [Nat.shiftRight_eq_div_pow, evalQuotHash_keyQuotient_eq]

/-- Per-bucket quotient-to-value map induced by an abstract dictionary state
`s_abs : Dictionary.State U` via `feistelReconstruct`. -/
@[expose]
def bucketMapOfState (U n_max : ℕ) (h1 : ℕ → ℕ) (s_abs : Dictionary.State U) (b q : ℕ) :
    Option ℕ :=
  if h : feistelReconstruct (bucketBits n_max) h1 b q < U ∧
      b < numBuckets n_max ∧ q < 2 ^ quotientBits U n_max then
    s_abs ⟨feistelReconstruct (bucketBits n_max) h1 b q, h.1⟩
  else
    none

@[simp]
theorem bucketMapOfState_empty (U n_max : ℕ) (h1 : ℕ → ℕ) :
    bucketMapOfState U n_max h1 (Dictionary.empty U) = fun _ _ => none := by
  funext b q
  unfold bucketMapOfState
  split_ifs <;> rfl

theorem bucketMapOfState_feistelBucket {U n_max : ℕ} (hnU : n_max ≤ U) (h1 : ℕ → ℕ)
    (s_abs : Dictionary.State U) (u : Fin U) :
    bucketMapOfState U n_max h1 s_abs
      (feistelBucket (bucketBits n_max) h1 u.val)
      (keyQuotient (bucketBits n_max) u.val) = s_abs u := by
  unfold bucketMapOfState
  have hrec := feistelReconstruct_feistelBucket (bucketBits n_max) h1 u.val
  have hb : feistelBucket (bucketBits n_max) h1 u.val < numBuckets n_max :=
    feistelBucket_lt (bucketBits n_max) h1 u.val
  have hq : keyQuotient (bucketBits n_max) u.val < 2 ^ quotientBits U n_max :=
    keyQuotient_lt_two_pow_quotientBits hnU u.isLt
  have hcond : feistelReconstruct (bucketBits n_max) h1
      (feistelBucket (bucketBits n_max) h1 u.val)
      (keyQuotient (bucketBits n_max) u.val) < U ∧
      feistelBucket (bucketBits n_max) h1 u.val < numBuckets n_max ∧
      keyQuotient (bucketBits n_max) u.val < 2 ^ quotientBits U n_max := by
    rw [hrec]
    exact ⟨u.isLt, hb, hq⟩
  rw [dite_eq_left hcond]
  congr 1
  exact Fin.ext hrec

theorem bucketMapOfState_update {U n_max : ℕ} (hnU : n_max ≤ U) (h1 : ℕ → ℕ)
    (s_abs : Dictionary.State U) (u : Fin U) (v_opt : Option ℕ) :
    let b := feistelBucket (bucketBits n_max) h1 u.val
    let q := keyQuotient (bucketBits n_max) u.val
    Function.update (bucketMapOfState U n_max h1 s_abs) b
      (Function.update (bucketMapOfState U n_max h1 s_abs b) q v_opt) =
    bucketMapOfState U n_max h1 (Function.update s_abs u v_opt) := by
  intro b q
  funext b' q'
  by_cases hbeq : b' = b
  · subst hbeq
    rw [Function.update_self]
    by_cases hqeq : q' = q
    · subst hqeq
      rw [Function.update_self, bucketMapOfState_feistelBucket hnU h1 _ u, Function.update_self]
    · rw [Function.update_of_ne hqeq]
      unfold bucketMapOfState
      split_ifs with h
      · have hne : (⟨feistelReconstruct (bucketBits n_max) h1 b q', h.1⟩ : Fin U) ≠ u := by
          intro heq
          have hval : feistelReconstruct (bucketBits n_max) h1 b q' = u.val :=
            congrArg Fin.val heq
          have hqr := (feistelBucket_feistelReconstruct h1 h.2.1 q').2
          rw [hval] at hqr
          exact hqeq hqr.symm
        rw [Function.update_of_ne hne]
      · rfl
  · rw [Function.update_of_ne hbeq]
    unfold bucketMapOfState
    split_ifs with h
    · have hne : (⟨feistelReconstruct (bucketBits n_max) h1 b' q', h.1⟩ : Fin U) ≠ u := by
        intro heq
        have hval : feistelReconstruct (bucketBits n_max) h1 b' q' = u.val :=
          congrArg Fin.val heq
        have hbr := (feistelBucket_feistelReconstruct h1 h.2.1 q').1
        rw [hval] at hbr
        exact hbeq hbr.symm
      rw [Function.update_of_ne hne]
    · rfl

/-- Full dictionary state invariant coupling `s_abs : Dictionary.State U` with `BucketStateInv` at
`base` under quotient hash seed `θ`. -/
structure DictStateInv (U V w₀ n_max base : ℕ) (θ : QuotHashSeed U n_max)
    (s_abs : Dictionary.State U) (s : Memory.State) : Prop where
  hbucket : ∃ L, BucketStateInv U V w₀ n_max (hashSpace U w₀ n_max) base
    (mOfSeed U n_max θ) L (bucketMapOfState U n_max (hValOfSeed U n_max θ) s_abs) s
  htot : totalSlots n_max (gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem) =
    (Dictionary.dom s_abs).card

/-- An all-zero dictionary memory region satisfies `DictStateInv` for `Dictionary.empty U` with
zero `slotPotential`. -/
theorem dictStateInv_of_zero {U V w₀ n_max base : ℕ} (θ : QuotHashSeed U n_max)
    {s : Memory.State}
    (hgm0 : ∀ i, gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem i = 0)
    (hlm0 : ∀ p, lmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem p = 0) :
    DictStateInv U V w₀ n_max base θ (Dictionary.empty U) s ∧
    slotPotential n_max (gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem) = 0 := by
  obtain ⟨hinv, htot0, hpot0⟩ :=
    bucketStateInv_of_zero (U := U) (V := V) (w₀ := w₀) (n_max := n_max)
      (h_space := hashSpace U w₀ n_max) (base := base) (mOfSeed U n_max θ) hgm0 hlm0
  refine ⟨⟨⟨fun _ _ => [], ?_⟩, ?_⟩, hpot0⟩
  · rwa [bucketMapOfState_empty]
  · rw [htot0]
    simp [Dictionary.dom_empty]

/-- Under `BucketStateInv ... (bucketMapOfState U n_max (hValOfSeed U n_max θ) s_abs)`, the length
of the micro-chain `L b m` for key `u` is at most `1 + microCollCount` and the bucket overflow
`bCount b - effBucketCap n_max` is at most `1 + bucketOvfCount`. -/
theorem chain_and_overflow_le_probeExcess {U V w₀ n_max base : ℕ}
    (θ : QuotHashSeed U n_max) {L : ℕ → ℕ → List ℕ}
    {s_abs : Dictionary.State U} {s : Memory.State}
    (hinv : BucketStateInv U V w₀ n_max (hashSpace U w₀ n_max) base
      (mOfSeed U n_max θ) L (bucketMapOfState U n_max (hValOfSeed U n_max θ) s_abs) s)
    (u : Fin U) :
    let h1 := hValOfSeed U n_max θ
    let b := feistelBucket (bucketBits n_max) h1 u.val
    let q := keyQuotient (bucketBits n_max) u.val
    let m := mOfSeed U n_max θ q
    let gm := gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem
    (L b m).length ≤
      1 + microCollCount n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u ∧
    bCount n_max gm b - effBucketCap n_max ≤
      1 + bucketOvfCount n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u ∧
    8 * (L b m).length + 6 * (bCount n_max gm b - effBucketCap n_max) ≤
      14 + 8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u := by
  classical
  intro h1 b q m gm
  have hb : b < numBuckets n_max := feistelBucket_lt (bucketBits n_max) h1 u.val
  have hm : m < numMicroPerBucket n_max := mOfSeed_lt U n_max θ q
  let qSlot (j : ℕ) : ℕ :=
    quotAt base U w₀ n_max (hashSpace U w₀ n_max) s.mem (slotOf n_max gm b j)
  let uVal (j : ℕ) : ℕ :=
    feistelReconstruct (bucketBits n_max) h1 b (qSlot j)
  have hslot_key : ∀ j < bCount n_max gm b,
      ∃ hu_j : uVal j < U,
        (⟨uVal j, hu_j⟩ : Fin U) ∈ Dictionary.dom s_abs ∧
        feistelBucket (bucketBits n_max) h1 (uVal j) = b ∧
        keyQuotient (bucketBits n_max) (uVal j) = qSlot j := by
    intro j hj
    have hsome := hinv.hmap_some b hb j hj
    change bucketMapOfState U n_max h1 s_abs b (qSlot j) = some _ at hsome
    unfold bucketMapOfState at hsome
    split_ifs at hsome with hcond
    refine ⟨hcond.1, Dictionary.mem_dom_iff_isSome.mpr (by rw [hsome]; rfl), ?_⟩
    exact feistelBucket_feistelReconstruct h1 hb (qSlot j)
  let keyAt (j : ℕ) : Fin U :=
    if hj : j < bCount n_max gm b then
      ⟨uVal j, (hslot_key j hj).1⟩
    else
      u
  have hkeyAt_props : ∀ j (hj : j < bCount n_max gm b),
      keyAt j ∈ Dictionary.dom s_abs ∧
      feistelBucketHash n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2 (keyAt j) =
        feistelBucketHash n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2 u ∧
      keyQuotient (bucketBits n_max) (keyAt j).val = qSlot j := by
    intro j hj
    have hval : (keyAt j).val = uVal j := by
      dsimp only [keyAt]
      rw [dite_eq_left hj]
    obtain ⟨hu_j, hdom, hb_j, hq_j⟩ := hslot_key j hj
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [keyAt]
      rw [dite_eq_left hj]
      exact hdom
    · apply Fin.ext
      rw [feistelBucketHash_val_eq_hValOfSeed, feistelBucketHash_val_eq_hValOfSeed, hval, hb_j]
    · rw [hval, hq_j]
  have hkeyAt_inj : ∀ j₁ < bCount n_max gm b, ∀ j₂ < bCount n_max gm b,
      keyAt j₁ = keyAt j₂ → j₁ = j₂ := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hq₁ := (hkeyAt_props j₁ hj₁).2.2
    have hq₂ := (hkeyAt_props j₂ hj₂).2.2
    rw [heq] at hq₁
    exact hinv.hnodup_q b hb j₁ hj₁ j₂ hj₂ (hq₁.symm.trans hq₂)
  -- Bound 1: micro-chain length
  have hlen : (L b m).length ≤
      1 + microCollCount n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u := by
    have hnodup : (L b m).Nodup := (hinv.hchains.1 b hb m hm).nodup
    have hcard_eq : (L b m).length = #(L b m).toFinset :=
      (List.toFinset_card_of_nodup hnodup).symm
    rw [hcard_eq]
    refine card_microSlots_le (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
      (Dictionary.dom s_abs) u (L b m).toFinset keyAt ?_ ?_
    · intro j₁ hj₁ j₂ hj₂ heq
      have hj₁_lt := ((hinv.hchain_mem b hb m hm j₁).mp (List.mem_toFinset.mp hj₁)).1
      have hj₂_lt := ((hinv.hchain_mem b hb m hm j₂).mp (List.mem_toFinset.mp hj₂)).1
      exact hkeyAt_inj j₁ hj₁_lt j₂ hj₂_lt heq
    · intro j hj
      obtain ⟨hj_lt, _, hm_j⟩ := (hinv.hchain_mem b hb m hm j).mp (List.mem_toFinset.mp hj)
      obtain ⟨hdom, hb_eq, hq_eq⟩ := hkeyAt_props j hj_lt
      refine ⟨hdom, (feistelMicroHash_eq_iff n_max _ _ θ.2 (keyAt j) u).mpr ⟨hb_eq, ?_⟩⟩
      apply Fin.ext
      rw [feistelLocalMicro_val_eq_mOfSeed, feistelLocalMicro_val_eq_mOfSeed, hq_eq]
      exact hm_j
  -- Bound 2: bucket overflow
  have hovf : bCount n_max gm b - effBucketCap n_max ≤
      1 + bucketOvfCount n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u := by
    refine bucketOverflow_le (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
      (Dictionary.dom s_abs) u (fun j : Fin (bCount n_max gm b) => keyAt j.val) ?_ ?_
    · intro j₁ j₂ heq
      exact Fin.ext (hkeyAt_inj j₁.val j₁.isLt j₂.val j₂.isLt heq)
    · intro j
      exact ⟨(hkeyAt_props j.val j.isLt).1, (hkeyAt_props j.val j.isLt).2.1⟩
  refine ⟨hlen, hovf, ?_⟩
  unfold probeExcess
  omega

/-! ## Section 4: Feistel-dispatched `Memory.Prog` operations realized via `realize` -/

/-- Well-formedness condition `0 < w₀ ∧ n_max ≤ U ∧ U < 2 ^ w₀ ∧ V ≤ 2 ^ w₀` on the dictionary
parameters `(U, V, w₀, n_max)`. -/
@[expose]
def DictParamsWf (U V w₀ n_max : ℕ) : Prop :=
  0 < w₀ ∧ n_max ≤ U ∧ U < 2 ^ w₀ ∧ V ≤ 2 ^ w₀

/-- Parameter-free pure `Memory.Prog` extracting the key quotient `keyQuotient (bucketBits n_max) u`
via right shift `d.2 >>> dpBucketBits d.1`. -/
@[expose]
def extractQuotGenProg (d : DictParams × ℕ) : Memory.Prog ℕ :=
  pure (d.2 >>> dpBucketBits d.1)

/-- Pure `Memory.Prog` extracting the key quotient `keyQuotient (bucketBits n_max) u` via right
shift `u >>> bucketBits n_max`. -/
@[expose]
def extractQuotProg (n_max : ℕ) (u : ℕ) : Memory.Prog ℕ :=
  pure (u >>> bucketBits n_max)

@[simp]
theorem extractQuotGenProg_mk (U V w n_max h_space u : ℕ) :
    extractQuotGenProg (mkDictParams U V w n_max h_space, u) = extractQuotProg n_max u := rfl

/-- Precondition for `extractQuotProg`. -/
@[expose]
def ExtractQuotPre (n_max w u : ℕ) (_s : Memory.State) : Prop :=
  Fits w u ∧ Fits w (bucketBits n_max)

/-- Parameter-free precondition for `extractQuotGenProg`. -/
@[expose]
def ExtractQuotGenPre (w : ℕ) (d : DictParams × ℕ) (s : Memory.State) : Prop :=
  ExtractQuotPre (dpNMax d.1) w d.2 s

@[simp]
theorem extractQuotGenPre_mk (U V w₀ n_max h_space w u : ℕ) (s : Memory.State) :
    ExtractQuotGenPre w (mkDictParams U V w₀ n_max h_space, u) s ↔
      ExtractQuotPre n_max w u s := Iff.rfl

theorem realizes_extractQuotGen :
    Realizes .exact extractQuotGenProg
      (WordEncoding.encode (α := DictParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      ExtractQuotGenPre
      (fun _ _ => 0) := by
  realize

/-- Helper lemma: `(h_q &&& (2 ^ b - 1)) ^^^ (u &&& (2 ^ b - 1)) = (h_q % 2 ^ b) ^^^ keyLow b u`. -/
theorem and_mask_xor_eq_feistelBucket (b u h_q : ℕ) :
    (h_q &&& (2 ^ b - 1)) ^^^ (u &&& (2 ^ b - 1)) = (h_q % 2 ^ b) ^^^ keyLow b u := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- Helper lemma: `Fits w (bucketBits n_max)` and `Fits w (2 ^ bucketBits n_max - 1)` from
`DictEnvGen`. -/
theorem fits_bucketBits_and_mask {U V w₀ n_max h_space w base : ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base) (hw : 0 < w₀) (hnU : n_max ≤ U)
    (hU : U < 2 ^ w₀) :
    Fits w (bucketBits n_max) ∧ Fits w (2 ^ bucketBits n_max - 1) := by
  have h2b_le : 2 ^ bucketBits n_max ≤ max n_max 1 :=
    (Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits n_max)).trans
      (totalMicroBuckets_le n_max)
  have hfit_2b : Fits w (2 ^ bucketBits n_max) :=
    fits_of_le_max_n_one henv hw hnU hU h2b_le
  exact ⟨hfit_2b.of_le (le_of_lt Nat.lt_two_pow_self), hfit_2b.of_le (Nat.sub_le _ _)⟩

/-- Parameter-free Feistel-dispatched `query` in `Memory.Prog` (`d = (dp, ((base, u), h_q))`). -/
@[expose]
def queryWithHashGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog (Option ℕ) := do
  let b_bits ← pure (dpBucketBits d.1)
  let b_mask ← pure (dpBucketMask d.1)
  let u_low ← pure (d.2.1.2 &&& b_mask)
  let h_low ← pure (d.2.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.2.1.2 >>> b_bits)
  let m ← pure (d.2.2 >>> b_bits)
  queryBodyGenProg (d.1, (((d.2.1.1, b), q), m))

/-- Feistel-dispatched `query` in `Memory.Prog` (`d = ((base, u), h_q)`): computes
`b = (h_q &&& (2 ^ b_bits - 1)) ^^^ (u &&& (2 ^ b_bits - 1))`, `q = u >>> b_bits`, and
`m = h_q >>> b_bits`, then runs `queryBodyProg`. -/
@[expose]
def queryWithHashProg (U V w₀ n_max : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog (Option ℕ) := do
  let b_bits ← pure (bucketBits n_max)
  let b_mask ← pure (2 ^ bucketBits n_max - 1)
  let u_low ← pure (d.1.2 &&& b_mask)
  let h_low ← pure (d.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.1.2 >>> b_bits)
  let m ← pure (d.2 >>> b_bits)
  queryBodyProg U V w₀ n_max (hashSpace U w₀ n_max) (((d.1.1, b), q), m)

@[simp]
theorem queryWithHashGenProg_mk (U V w₀ n_max : ℕ) (d : (ℕ × ℕ) × ℕ) :
    queryWithHashGenProg (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) =
      queryWithHashProg U V w₀ n_max d := by
  simp only [queryWithHashGenProg, queryWithHashProg, p_bucketBits_mk, p_bucketMask_mk,
    queryBodyGenProg_mk]

/-- Precondition for `queryWithHashProg` in `Realizes`. -/
@[expose]
def QueryWithHashPre (U V w₀ n_max w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let b := (d.2 &&& (2 ^ bucketBits n_max - 1)) ^^^ (d.1.2 &&& (2 ^ bucketBits n_max - 1))
  let q := d.1.2 >>> bucketBits n_max
  let m := d.2 >>> bucketBits n_max
  DictParamsWf U V w₀ n_max ∧
  d.1.2 < U ∧
  d.2 < 2 ^ totalMicroBits n_max ∧
  SearchMicroChainPre U V w₀ n_max (hashSpace U w₀ n_max) w (((d.1.1, b), q), m) s

/-- Parameter-free precondition for `queryWithHashGenProg` in `Realizes`. -/
@[expose]
def QueryWithHashGenPre (w : ℕ) (d : DictParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  let b := (d.2.2 &&& dpBucketMask d.1) ^^^ (d.2.1.2 &&& dpBucketMask d.1)
  let q := d.2.1.2 >>> dpBucketBits d.1
  let m := d.2.2 >>> dpBucketBits d.1
  DictParamsWf (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) ∧
  d.2.1.2 < dpU d.1 ∧
  d.2.2 < 2 ^ totalMicroBits (dpNMax d.1) ∧
  SearchMicroChainGenPre w (d.1, (((d.2.1.1, b), q), m)) s

@[simp]
theorem queryWithHashGenPre_mk (U V w₀ n_max w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    QueryWithHashGenPre w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) s ↔
      QueryWithHashPre U V w₀ n_max w d s := Iff.rfl

/-- Parameter-free `Realizes .exact` certificate for `queryWithHashGenProg`. -/
theorem realizes_queryWithHashGen :
    Realizes .exact queryWithHashGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Option ℕ))
      QueryWithHashGenPre
      (fun _ _ => 0) := by
  have hqb := realizes_queryBodyGen
  realize
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.2.2.2.1
    simpDictParamsWith [queryWithHashGenPre_mk, QueryWithHashPre,
      searchMicroChainGenPre_mk, SearchMicroChainPre, queryBodyGenProg_mk]
  )
  · rw [and_mask_xor_eq_feistelBucket]
    exact (fits_bucketBits_and_mask h.2.2.2.1 hw hnU hU).2.of_le
      (Nat.le_sub_one_of_lt (feistelBucket_lt (bucketBits n_max) (fun _ => d.2) d.1.2))
  · exact h.2.2.2

theorem validProg_queryWithHash {U V w n_max : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : QueryWithHashPre U V w n_max w d s) :
    ValidProg w (dictFrontier U V w n_max (hashSpace U w n_max) d.1.1) s
      (queryWithHashProg U V w n_max d) := by
  exact validProg_queryBody hpre.1.1 hpre.2.2.2

/-- Parameter-free Feistel-dispatched `insert` in `Memory.Prog`
(`d = (dp, (((base, u), v_new), h_q))`). -/
@[expose]
def insertWithHashGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let b_bits ← pure (dpBucketBits d.1)
  let b_mask ← pure (dpBucketMask d.1)
  let u_low ← pure (d.2.1.1.2 &&& b_mask)
  let h_low ← pure (d.2.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.2.1.1.2 >>> b_bits)
  let m ← pure (d.2.2 >>> b_bits)
  insertBodyGenProg (d.1, ((((d.2.1.1.1, b), q), d.2.1.2), m))

/-- Feistel-dispatched `insert` in `Memory.Prog` (`d = (((base, u), v_new), h_q)`). -/
@[expose]
def insertWithHashProg (U V w₀ n_max : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let b_bits ← pure (bucketBits n_max)
  let b_mask ← pure (2 ^ bucketBits n_max - 1)
  let u_low ← pure (d.1.1.2 &&& b_mask)
  let h_low ← pure (d.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.1.1.2 >>> b_bits)
  let m ← pure (d.2 >>> b_bits)
  insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max) ((((d.1.1.1, b), q), d.1.2), m)

@[simp]
theorem insertWithHashGenProg_mk (U V w₀ n_max : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    insertWithHashGenProg (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) =
      insertWithHashProg U V w₀ n_max d := by
  simp only [insertWithHashGenProg, insertWithHashProg, p_bucketBits_mk, p_bucketMask_mk,
    insertBodyGenProg_mk]

/-- Precondition for `insertWithHashProg` in `Realizes`. -/
@[expose]
def InsertWithHashPre (U V w₀ n_max w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let b := (d.2 &&& (2 ^ bucketBits n_max - 1)) ^^^ (d.1.1.2 &&& (2 ^ bucketBits n_max - 1))
  let q := d.1.1.2 >>> bucketBits n_max
  let m := d.2 >>> bucketBits n_max
  DictParamsWf U V w₀ n_max ∧
  d.1.1.2 < U ∧
  d.2 < 2 ^ totalMicroBits n_max ∧
  InsertBodyPre U V w₀ n_max (hashSpace U w₀ n_max) w ((((d.1.1.1, b), q), d.1.2), m) s

/-- Parameter-free precondition for `insertWithHashGenProg` in `Realizes`. -/
@[expose]
def InsertWithHashGenPre (w : ℕ) (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  let b := (d.2.2 &&& dpBucketMask d.1) ^^^ (d.2.1.1.2 &&& dpBucketMask d.1)
  let q := d.2.1.1.2 >>> dpBucketBits d.1
  let m := d.2.2 >>> dpBucketBits d.1
  DictParamsWf (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) ∧
  d.2.1.1.2 < dpU d.1 ∧
  d.2.2 < 2 ^ totalMicroBits (dpNMax d.1) ∧
  InsertBodyGenPre w (d.1, ((((d.2.1.1.1, b), q), d.2.1.2), m)) s

@[simp]
theorem insertWithHashGenPre_mk (U V w₀ n_max w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    InsertWithHashGenPre w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) s ↔
      InsertWithHashPre U V w₀ n_max w d s := Iff.rfl

/-- Parameter-free `Realizes .exact` certificate for `insertWithHashGenProg`. -/
theorem realizes_insertWithHashGen :
    Realizes .exact insertWithHashGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      InsertWithHashGenPre
      (fun _ _ => 0) := by
  have hib := realizes_insertBodyGen
  realize
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.2.2.2.1.1
    simpDictParamsWith [insertWithHashGenPre_mk, InsertWithHashPre,
      insertBodyGenPre_mk, InsertBodyPre, SearchMicroChainPre, insertBodyGenProg_mk]
  )
  · rw [and_mask_xor_eq_feistelBucket]
    exact (fits_bucketBits_and_mask h.2.2.2.1.1 hw hnU hU).2.of_le
      (Nat.le_sub_one_of_lt (feistelBucket_lt (bucketBits n_max) (fun _ => d.2) d.1.1.2))
  · exact h.2.2.2

theorem validProg_insertWithHash {U V w n_max : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State}
    (hpre : InsertWithHashPre U V w n_max w d s) :
    ValidProg w (dictFrontier U V w n_max (hashSpace U w n_max) d.1.1.1) s
      (insertWithHashProg U V w n_max d) := by
  exact validProg_insertBody hpre.1.1 hpre.1.2.1 hpre.1.2.2.1 hpre.1.2.2.2 hpre.2.2.2

/-- Parameter-free Phase 1 of Feistel-dispatched `delete` in `Memory.Prog`
(`d = (dp, ((base, u), h_q))`). -/
@[expose]
def deletePrepWithHashGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let b_bits ← pure (dpBucketBits d.1)
  let b_mask ← pure (dpBucketMask d.1)
  let u_low ← pure (d.2.1.2 &&& b_mask)
  let h_low ← pure (d.2.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.2.1.2 >>> b_bits)
  let m ← pure (d.2.2 >>> b_bits)
  deletePrepGenProg (d.1, (((d.2.1.1, b), q), m))

/-- Phase 1 of Feistel-dispatched `delete` in `Memory.Prog` (`d = ((base, u), h_q)`):
computes `(b, q, m)` from `(u, h_q)` and runs `deletePrepProg`. -/
@[expose]
def deletePrepWithHashProg (U V w₀ n_max : ℕ) (d : (ℕ × ℕ) × ℕ) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let b_bits ← pure (bucketBits n_max)
  let b_mask ← pure (2 ^ bucketBits n_max - 1)
  let u_low ← pure (d.1.2 &&& b_mask)
  let h_low ← pure (d.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let q ← pure (d.1.2 >>> b_bits)
  let m ← pure (d.2 >>> b_bits)
  deletePrepProg U V w₀ n_max (hashSpace U w₀ n_max) (((d.1.1, b), q), m)

@[simp]
theorem deletePrepWithHashGenProg_mk (U V w₀ n_max : ℕ) (d : (ℕ × ℕ) × ℕ) :
    deletePrepWithHashGenProg (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) =
      deletePrepWithHashProg U V w₀ n_max d := by
  simp only [deletePrepWithHashGenProg, deletePrepWithHashProg, p_bucketBits_mk, p_bucketMask_mk,
    deletePrepGenProg_mk]

/-- Parameter-free `Realizes .exact` certificate for `deletePrepWithHashGenProg`. -/
theorem realizes_deletePrepWithHashGen :
    Realizes .exact deletePrepWithHashGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      QueryWithHashGenPre
      (fun _ _ => 0) := by
  have hdp := realizes_deletePrepGen
  realize
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.2.2.2.1
    simpDictParamsWith [queryWithHashGenPre_mk, QueryWithHashPre,
      searchMicroChainGenPre_mk, SearchMicroChainPre, deletePrepGenProg_mk]
  )
  · rw [and_mask_xor_eq_feistelBucket]
    exact (fits_bucketBits_and_mask h.2.2.2.1 hw hnU hU).2.of_le
      (Nat.le_sub_one_of_lt (feistelBucket_lt (bucketBits n_max) (fun _ => d.2) d.1.2))
  · exact h.2.2.2

theorem validProg_deletePrepWithHash {U V w n_max : ℕ}
    {d : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : QueryWithHashPre U V w n_max w d s) :
    ValidProg w (dictFrontier U V w n_max (hashSpace U w n_max) d.1.1) s
      (deletePrepWithHashProg U V w n_max d) := by
  exact validProg_deletePrep hpre.1.1 hpre.2.2.2

/-- Parameter-free Phase 2 of Feistel-dispatched `delete` in `Memory.Prog`
(`d = (dp, ((((base, u), h_q), ((found, j_del), phys_del)), h_q_last))`). -/
@[expose]
def deleteFinishWithHashGenProg
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ)) : Memory.Prog Unit := do
  let b_bits ← pure (dpBucketBits d.1)
  let b_mask ← pure (dpBucketMask d.1)
  let u_low ← pure (d.2.1.1.1.2 &&& b_mask)
  let h_low ← pure (d.2.1.1.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let m ← pure (d.2.1.1.2 >>> b_bits)
  let m_last ← pure (d.2.2 >>> b_bits)
  deleteFinishGenProg
    (d.1, (((((d.2.1.1.1.1, b), d.2.1.2.1), d.2.1.2.2), m), m_last))

/-- Phase 2 of Feistel-dispatched `delete` in `Memory.Prog`
(`d = ((((base, u), h_q), ((found, j_del), phys_del)), h_q_last)`):
computes `(b, m)` from `(u, h_q)` and `m_last = h_q_last >>> bucketBits n_max`, then runs
`deleteFinishProg`. -/
@[expose]
def deleteFinishWithHashProg (U V w₀ n_max : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ) : Memory.Prog Unit := do
  let b_bits ← pure (bucketBits n_max)
  let b_mask ← pure (2 ^ bucketBits n_max - 1)
  let u_low ← pure (d.1.1.1.2 &&& b_mask)
  let h_low ← pure (d.1.1.2 &&& b_mask)
  let b ← pure (h_low ^^^ u_low)
  let m ← pure (d.1.1.2 >>> b_bits)
  let m_last ← pure (d.2 >>> b_bits)
  deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
    (((((d.1.1.1.1, b), d.1.2.1), d.1.2.2), m), m_last)

@[simp]
theorem deleteFinishWithHashGenProg_mk (U V w₀ n_max : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ) :
    deleteFinishWithHashGenProg (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) =
      deleteFinishWithHashProg U V w₀ n_max d := by
  simp only [deleteFinishWithHashGenProg, deleteFinishWithHashProg, p_bucketBits_mk,
    p_bucketMask_mk, deleteFinishGenProg_mk]

/-- Precondition for `deleteFinishWithHashProg` in `Realizes`. -/
@[expose]
def DeleteFinishWithHashPre (U V w₀ n_max w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ) (s : Memory.State) : Prop :=
  let b := (d.1.1.2 &&& (2 ^ bucketBits n_max - 1)) ^^^ (d.1.1.1.2 &&& (2 ^ bucketBits n_max - 1))
  let m := d.1.1.2 >>> bucketBits n_max
  let m_last := d.2 >>> bucketBits n_max
  DictParamsWf U V w₀ n_max ∧
  d.1.1.2 < 2 ^ totalMicroBits n_max ∧
  d.2 < 2 ^ totalMicroBits n_max ∧
  DeleteFinishPre U V w₀ n_max (hashSpace U w₀ n_max) w
    (((((d.1.1.1.1, b), d.1.2.1), d.1.2.2), m), m_last) s

/-- Parameter-free precondition for `deleteFinishWithHashGenProg` in `Realizes`. -/
@[expose]
def DeleteFinishWithHashGenPre (w : ℕ)
    (d : DictParams × ((((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ)) (s : Memory.State) : Prop :=
  let b := (d.2.1.1.2 &&& dpBucketMask d.1) ^^^ (d.2.1.1.1.2 &&& dpBucketMask d.1)
  let m := d.2.1.1.2 >>> dpBucketBits d.1
  let m_last := d.2.2 >>> dpBucketBits d.1
  DictParamsWf (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) ∧
  d.2.1.1.2 < 2 ^ totalMicroBits (dpNMax d.1) ∧
  d.2.2 < 2 ^ totalMicroBits (dpNMax d.1) ∧
  DeleteFinishGenPre w
    (d.1, (((((d.2.1.1.1.1, b), d.2.1.2.1), d.2.1.2.2), m), m_last)) s

@[simp]
theorem deleteFinishWithHashGenPre_mk (U V w₀ n_max w : ℕ)
    (d : (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ) (s : Memory.State) :
    DeleteFinishWithHashGenPre w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max), d) s ↔
      DeleteFinishWithHashPre U V w₀ n_max w d s := Iff.rfl

/-- Parameter-free `Realizes .exact` certificate for `deleteFinishWithHashGenProg`. -/
theorem realizes_deleteFinishWithHashGen :
    Realizes .exact deleteFinishWithHashGenProg
      (WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ)))
      (WordEncoding.encode (α := Unit))
      DeleteFinishWithHashGenPre
      (fun _ _ => 0) := by
  have hdf := realizes_deleteFinishGen
  realize
  all_goals (
    rcases d with ⟨dp, d⟩
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.2.2.2.1
    simpDictParamsWith [deleteFinishWithHashGenPre_mk, DeleteFinishWithHashPre,
      deleteFinishGenPre_mk, DeleteFinishPre, DeleteFoundPre, deleteFinishGenProg_mk]
  )
  · rw [and_mask_xor_eq_feistelBucket]
    exact (fits_bucketBits_and_mask h.2.2.2.1 hw hnU hU).2.of_le
      (Nat.le_sub_one_of_lt (feistelBucket_lt (bucketBits n_max) (fun _ => d.1.1.2) d.1.1.1.2))
  · exact h.2.2.2

theorem validProg_deleteFinishWithHash {U V w n_max : ℕ}
    {d : (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ} {s : Memory.State}
    (hpre : DeleteFinishWithHashPre U V w n_max w d s) :
    ValidProg w (dictFrontier U V w n_max (hashSpace U w n_max) d.1.1.1.1) s
      (deleteFinishWithHashProg U V w n_max d) := by
  exact validProg_deleteFinish hpre.1.1 hpre.1.2.1 hpre.1.2.2.1 hpre.1.2.2.2 hpre.2.2.2

/-! ## Section 5: Dictionary-level `DictStateInv` + `probeExcess` transition specifications -/

/-- The Feistel dispatch shared by the dictionary-level specifications. The masks and shifts of the
`*WithHashProg` programs recover the bucket, quotient and micro-bucket of key `u`, the bucket and
micro-bucket are in range, and under `DictStateInv` the dispatched query precondition holds (it is
also the precondition of the first phase of `delete`). -/
private theorem dispatch_spec {U V w₀ n_max w base : ℕ}
    (hwf : DictParamsWf U V w₀ n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max)) base)
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} {s : Memory.State}
    (hinv : DictStateInv U V w₀ n_max base θ s_abs s) (u : Fin U) :
    let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
    (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u.val &&& (2 ^ bucketBits n_max - 1)) =
        feistelBucket (bucketBits n_max) (hValOfSeed U n_max θ) u.val ∧
      u.val >>> bucketBits n_max = keyQuotient (bucketBits n_max) u.val ∧
      h_q >>> bucketBits n_max = mOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) ∧
      feistelBucket (bucketBits n_max) (hValOfSeed U n_max θ) u.val < numBuckets n_max ∧
      mOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val) < numMicroPerBucket n_max ∧
      QueryWithHashPre U V w₀ n_max w ((base, u.val), h_q) s := by
  intro h_q
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  have hb_eq := and_mask_xor_eq_feistelBucket (bucketBits n_max) u.val h_q
  have hb_lt := feistelBucket_lt (bucketBits n_max) (hValOfSeed U n_max θ) u.val
  have hm_lt := mOfSeed_lt U n_max θ (keyQuotient (bucketBits n_max) u.val)
  refine ⟨hb_eq, Nat.shiftRight_eq_div_pow u.val (bucketBits n_max), rfl, hb_lt, hm_lt, hwf,
    u.isLt, hValOfSeed_lt U n_max θ _, ?_⟩
  dsimp only
  rw [hb_eq]
  exact hb_inv.searchMicroChainPre henv hb_lt hm_lt

/-- Dictionary-level specification of `queryWithHashProg`: establishes `QueryWithHashPre`, leaves
`s` unchanged, returns `s_abs u`, and uses at most `26 + 8 * probeExcess` memory cost. -/
theorem queryWithHashProg_dict_spec {U V w₀ n_max w base : ℕ}
    (hwf : DictParamsWf U V w₀ n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max)) base)
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} {s : Memory.State}
    (hinv : DictStateInv U V w₀ n_max base θ s_abs s) (u : Fin U) :
    let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
    let d := ((base, u.val), h_q)
    let prog := queryWithHashProg U V w₀ n_max d
    QueryWithHashPre U V w₀ n_max w d s ∧
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = s_abs u ∧
    memoryCost prog s ≤
      26 + 8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
        (Dictionary.dom s_abs) u := by
  intro h_q d prog
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  let h1 := hValOfSeed U n_max θ
  let b := feistelBucket (bucketBits n_max) h1 u.val
  let q := keyQuotient (bucketBits n_max) u.val
  let m := mOfSeed U n_max θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hpre⟩ := dispatch_spec (w := w) hwf henv θ hinv u
  have hprog_eq : prog = queryBodyProg U V w₀ n_max (hashSpace U w₀ n_max) (((base, b), q), m) := by
    change queryBodyProg U V w₀ n_max (hashSpace U w₀ n_max)
      (((base, (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u.val &&& (2 ^ bucketBits n_max - 1))),
        u.val >>> bucketBits n_max), h_q >>> bucketBits n_max) = _
    rw [hb_eq, hq_eq, hm_eq]
  have hspec := queryBodyProg_bucket_spec hb_inv henv hb_lt (q_target := q) (m := m) rfl hm_lt
  have hprobe := (chain_and_overflow_le_probeExcess θ hb_inv u).2.2
  have hcost_prog : memoryCost prog s =
      memoryCost (queryBodyProg U V w₀ n_max (hashSpace U w₀ n_max) (((base, b), q), m)) s :=
    congrArg (memoryCost · s) hprog_eq
  refine ⟨hpre, ?_, ?_, ?_⟩
  · rw [congrArg ((Memory.spec 0).clientState s) hprog_eq]
    exact hspec.1
  · rw [congrArg ((Memory.spec 0).clientResult s) hprog_eq, hspec.2.2,
      bucketMapOfState_feistelBucket hwf.2.1 h1 s_abs u]
  · rw [hcost_prog]
    have hcost := hspec.2.1
    dsimp only [b, q, m, h1] at hcost hprobe ⊢
    omega

/-- Dictionary-level specification of `insertWithHashProg`: establishes `InsertWithHashPre`,
preserves `DictStateInv` for `Function.update s_abs u (some v)`, preserves memory outside the
dictionary table arrays, and satisfies the amortized `memoryCost + 66 * slotPotential` bound. -/
theorem insertWithHashProg_dict_spec {U V w₀ n_max w base : ℕ}
    (hwf : DictParamsWf U V w₀ n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max)) base)
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} {s : Memory.State}
    (hinv : DictStateInv U V w₀ n_max base θ s_abs s)
    (u : Fin U) (v : ℕ)
    (hval : (Dynamic.spec U V n_max).valid s_abs (.insert u v)) :
    let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
    let d := (((base, u.val), v), h_q)
    let prog := insertWithHashProg U V w₀ n_max d
    let s' := (Memory.spec 0).clientState s prog
    let gm₀ := gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem
    let gm' := gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s'.mem
    InsertWithHashPre U V w₀ n_max w d s ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot (hashSpace U w₀ n_max) ≤ a ∧
        a < base + space U V w₀ n_max) → s'.mem a = s.mem a) ∧
    DictStateInv U V w₀ n_max base θ (Function.update s_abs u (some v)) s' ∧
    memoryCost prog s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 184 +
        8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
          (Dictionary.dom s_abs) u := by
  intro h_q d prog s' gm₀ gm'
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  let h1 := hValOfSeed U n_max θ
  let b := feistelBucket (bucketBits n_max) h1 u.val
  let q := keyQuotient (bucketBits n_max) u.val
  let m := mOfSeed U n_max θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, -, hu, hh_q, hsearch⟩ :=
    dispatch_spec (w := w) hwf henv θ hinv u
  have hq_lt : q < 2 ^ quotientBits U n_max := keyQuotient_lt_two_pow_quotientBits hwf.2.1 u.isLt
  have hv_lt : v < 2 ^ valBits V :=
    hval.2.trans_le (Nat.le_pow_clog (by decide) V)
  have hpre : InsertWithHashPre U V w₀ n_max w d s :=
    ⟨hwf, hu, hh_q, hsearch, hq_eq.trans_lt hq_lt, hv_lt⟩
  have hprog_eq : prog =
      insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max) ((((base, b), q), v), m) := by
    change insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max)
      ((((base, (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u.val &&& (2 ^ bucketBits n_max - 1))),
        u.val >>> bucketBits n_max), v), h_q >>> bucketBits n_max) = _
    rw [hb_eq, hq_eq, hm_eq]
  have hs'_eq : s' = (Memory.spec 0).clientState s
      (insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max) ((((base, b), q), v), m)) :=
    congrArg ((Memory.spec 0).clientState s) hprog_eq
  have hcost_prog : memoryCost prog s =
      memoryCost (insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max) ((((base, b), q), v), m)) s :=
    congrArg (memoryCost · s) hprog_eq
  have hB_eq : bucketMapOfState U n_max h1 s_abs b q = s_abs u :=
    bucketMapOfState_feistelBucket hwf.2.1 h1 s_abs u
  have hcap : (bucketMapOfState U n_max h1 s_abs b q).isSome ∨ totalSlots n_max gm₀ < n_max := by
    rw [hB_eq, hinv.htot]
    exact hval.1.symm
  have hspec := insertBodyProg_bucket_spec hwf.1 hb_inv henv hb_lt (q_target := q) (v_new := v)
    (m := m) rfl hm_lt hq_lt hv_lt hcap
  obtain ⟨hf, hout, ⟨L', hinv'⟩, htot', hcost⟩ := hspec
  rw [bucketMapOfState_update hwf.2.1 h1 s_abs u (some v)] at hinv'
  have hgm'_eq : gm' = gmAt base U V w₀ n_max (hashSpace U w₀ n_max)
      ((Memory.spec 0).clientState s
        (insertBodyProg U V w₀ n_max (hashSpace U w₀ n_max) ((((base, b), q), v), m))).mem := by
    dsimp only [gm']
    rw [hs'_eq]
  have htot_dom : totalSlots n_max gm' =
      (Dictionary.dom (Function.update s_abs u (some v))).card := by
    rw [hgm'_eq, htot', hB_eq, hinv.htot]
    split_ifs with his
    · exact (Dictionary.card_dom_insert_eq_of_isSome his v).symm
    · exact (Dictionary.card_dom_insert_eq_of_eq_none (Option.not_isSome_iff_eq_none.mp his) v).symm
  have hprobe := (chain_and_overflow_le_probeExcess θ hb_inv u).2.2
  refine ⟨hpre, ?_, ?_, ⟨⟨L', ?_⟩, htot_dom⟩, ?_⟩
  · rw [hs'_eq]; exact hf
  · intro a ha
    rw [hs'_eq]
    exact hout a ha
  · rw [hs'_eq]; exact hinv'
  · rw [hcost_prog, hgm'_eq]
    dsimp only [b, q, m, h1, gm₀] at hcost hprobe ⊢
    omega

private theorem exists_quad_eq (x : ((ℕ × ℕ) × ℕ) × ℕ) :
    ∃ found j_del phys_del q_last : ℕ, x = (((found, j_del), phys_del), q_last) :=
  ⟨x.1.1.1, x.1.1.2, x.1.2, x.2, rfl⟩

/-- Dictionary-level specification of the two-phase `delete` (`deletePrepWithHashProg` followed by
`deleteFinishWithHashProg`): establishes both preconditions, preserves `DictStateInv` for
`Function.update s_abs u none`, preserves memory outside the dictionary table arrays, and bounds the
combined amortized `memoryCost` by `270 + 8 * probeExcess`. -/
theorem deleteWithHashProg_dict_spec {U V w₀ n_max w base : ℕ}
    (hwf : DictParamsWf U V w₀ n_max)
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max (hashSpace U w₀ n_max)) base)
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} {s : Memory.State}
    (hinv : DictStateInv U V w₀ n_max base θ s_abs s) (u : Fin U) :
    let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
    let d_prep := ((base, u.val), h_q)
    let prog_prep := deletePrepWithHashProg U V w₀ n_max d_prep
    ∃ found j_del phys_del q_last : ℕ,
      let prep := (((found, j_del), phys_del), q_last)
      let h_q_last := hValOfSeed U n_max θ q_last
      let d_fin := ((((base, u.val), h_q), ((found, j_del), phys_del)), h_q_last)
      let prog_fin := deleteFinishWithHashProg U V w₀ n_max d_fin
      let s' := (Memory.spec 0).clientState s prog_fin
      let gm₀ := gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s.mem
      let gm' := gmAt base U V w₀ n_max (hashSpace U w₀ n_max) s'.mem
      (Memory.spec 0).clientResult s prog_prep = prep ∧
      QueryWithHashPre U V w₀ n_max w d_prep s ∧
      (Memory.spec 0).clientState s prog_prep = s ∧
      q_last < 2 ^ quotientBits U n_max ∧
      DeleteFinishWithHashPre U V w₀ n_max w d_fin s ∧
      s'.frontier = s.frontier ∧
      (∀ a, ¬(base + offQuot (hashSpace U w₀ n_max) ≤ a ∧
          a < base + space U V w₀ n_max) → s'.mem a = s.mem a) ∧
      DictStateInv U V w₀ n_max base θ (Function.update s_abs u none) s' ∧
      memoryCost prog_prep s + memoryCost prog_fin s + 66 * slotPotential n_max gm' ≤
        66 * slotPotential n_max gm₀ + 270 +
          8 * probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
            (Dictionary.dom s_abs) u := by
  intro h_q d_prep prog_prep
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  let h1 := hValOfSeed U n_max θ
  let b := feistelBucket (bucketBits n_max) h1 u.val
  let q := keyQuotient (bucketBits n_max) u.val
  let m := mOfSeed U n_max θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hpre_prep⟩ := dispatch_spec (w := w) hwf henv θ hinv u
  have hprep_eq : prog_prep =
      deletePrepProg U V w₀ n_max (hashSpace U w₀ n_max) (((base, b), q), m) := by
    change deletePrepProg U V w₀ n_max (hashSpace U w₀ n_max)
      (((base, (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u.val &&& (2 ^ bucketBits n_max - 1))),
        u.val >>> bucketBits n_max), h_q >>> bucketBits n_max) = _
    rw [hb_eq, hq_eq, hm_eq]
  have hprep_spec := deletePrepProg_bucket_spec hb_inv henv hb_lt (q_target := q) (m := m) rfl hm_lt
  have hfin_spec := deleteFinishProg_bucket_spec hwf.1 hb_inv henv hb_lt (q_target := q) (m := m)
    rfl hm_lt (fun q' _ => mOfSeed_lt U n_max θ q')
  obtain ⟨found, j_del, phys_del, q_last, hprep_val⟩ :=
    exists_quad_eq ((Memory.spec 0).clientResult s
      (deletePrepProg U V w₀ n_max (hashSpace U w₀ n_max) (((base, b), q), m)))
  dsimp only at hprep_spec hfin_spec
  rw [hprep_val] at hprep_spec hfin_spec
  dsimp only at hprep_spec hfin_spec
  refine ⟨found, j_del, phys_del, q_last, ?_⟩
  intro prep h_q_last d_fin prog_fin s' gm₀ gm'
  have hfin_eq : prog_fin =
      deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
        (((((base, b), (found, j_del)), phys_del), m), mOfSeed U n_max θ q_last) := by
    change deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
      (((((base, (h_q &&& (2 ^ bucketBits n_max - 1)) ^^^ (u.val &&& (2 ^ bucketBits n_max - 1))),
        (found, j_del)), phys_del), h_q >>> bucketBits n_max), h_q_last >>> bucketBits n_max) = _
    rw [hb_eq, hm_eq]
    rfl
  obtain ⟨hpre_fin_inner, hf, hout, ⟨L', hinv'⟩, htot', hcost_fin⟩ := hfin_spec
  rw [bucketMapOfState_update hwf.2.1 h1 s_abs u none] at hinv'
  have hpre_fin : DeleteFinishWithHashPre U V w₀ n_max w d_fin s := by
    refine ⟨hwf, hValOfSeed_lt U n_max θ q, hValOfSeed_lt U n_max θ q_last, ?_⟩
    dsimp only [d_fin]
    rw [hb_eq, hm_eq]
    exact hpre_fin_inner
  have hs'_eq : s' = (Memory.spec 0).clientState s
      (deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
        (((((base, b), (found, j_del)), phys_del), m), mOfSeed U n_max θ q_last)) :=
    congrArg ((Memory.spec 0).clientState s) hfin_eq
  have hgm'_eq : gm' = gmAt base U V w₀ n_max (hashSpace U w₀ n_max)
      ((Memory.spec 0).clientState s
        (deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
          (((((base, b), (found, j_del)), phys_del), m), mOfSeed U n_max θ q_last))).mem := by
    dsimp only [gm']
    rw [hs'_eq]
  have hcost_prep_eq : memoryCost prog_prep s =
      memoryCost (deletePrepProg U V w₀ n_max (hashSpace U w₀ n_max) (((base, b), q), m)) s :=
    congrArg (memoryCost · s) hprep_eq
  have hcost_fin_eq : memoryCost prog_fin s =
      memoryCost (deleteFinishProg U V w₀ n_max (hashSpace U w₀ n_max)
        (((((base, b), (found, j_del)), phys_del), m), mOfSeed U n_max θ q_last)) s :=
    congrArg (memoryCost · s) hfin_eq
  have hB_eq : bucketMapOfState U n_max h1 s_abs b q = s_abs u :=
    bucketMapOfState_feistelBucket hwf.2.1 h1 s_abs u
  have htot_dom : totalSlots n_max gm' =
      (Dictionary.dom (Function.update s_abs u none)).card := by
    rw [hgm'_eq, htot', hB_eq, hinv.htot]
    split_ifs with his
    · exact (Dynamic.card_dom_delete_eq_of_isSome his).symm
    · exact (Dynamic.card_dom_delete_eq_of_eq_none (Option.not_isSome_iff_eq_none.mp his)).symm
  have hprobe := (chain_and_overflow_le_probeExcess θ hb_inv u).2.2
  have hcost_prep := hprep_spec.2.1
  refine ⟨(congrArg ((Memory.spec 0).clientResult s) hprep_eq).trans hprep_val,
    hpre_prep, ?_, hprep_spec.2.2.1, hpre_fin, ?_, ?_, ⟨⟨L', ?_⟩, htot_dom⟩, ?_⟩
  · rw [congrArg ((Memory.spec 0).clientState s) hprep_eq]
    exact hprep_spec.1
  · rw [hs'_eq]; exact hf
  · intro a ha
    rw [hs'_eq]
    exact hout a ha
  · rw [hs'_eq]; exact hinv'
  · rw [hcost_prep_eq, hcost_fin_eq, hgm'_eq]
    dsimp only [b, q, m, h1, gm₀] at hcost_prep hcost_fin hprobe ⊢
    omega

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
