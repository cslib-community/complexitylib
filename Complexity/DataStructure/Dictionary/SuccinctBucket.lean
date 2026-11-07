/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.FeistelQuotient
public import Complexity.DataStructure.Dictionary.WordRAM.BitPackedArray
public import Complexity.Foundations.Data.BitString.Prefix
public import Complexity.Probability.PMF.Expect
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Partitioned-bucket, micro-bucket, and slab-hysteresis model for succinct dictionaries

This file develops the pure structural, combinatorial, and probabilistic core of the fixed-capacity
succinct dictionary with deletions. It combines the bucket partition and fingerprint-indexed buckets
of [Bender, Farach-Colton, J. Kuszmaul and W. Kuszmaul, SOSA 2024,
Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024] with one-round Feistel quotienting
([Arbitman, Naor and Segev, FOCS 2010, Claim 5.7][ArbitmanNaorSegev2010];
[Bender, Conway, Farach-Colton, Kuszmaul and Tagliavini, *J. ACM* 2023,
Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]). Storage uses zero-wasted-slot
full-slab / tail-item packing ([Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, STOC
2022, Sections 5.2 and 6.1, Lemma 24][BenderFarachColtonKuszmaulKuszmaulLiu2022]) together with this
formalization's own micro-bucket chains and slab-hysteresis potential:

1. **Unified bucket and micro-bucket decomposition (`totalMicroBits_eq_log`):**
   At capacity `n_max`, each key is assigned a `bucketBits n_max`-bit Feistel bucket
   (`numBuckets n_max = 2 ^ bucketBits n_max`) and a `microBits n_max`-bit local micro-bucket
   (`microBits n_max = min ⌊log₂ n_max⌋ (3 * logLogFactor n_max)`), where
   `totalMicroBits n_max = bucketBits n_max + microBits n_max = ⌊log₂ n_max⌋` across all `n_max`.
   Thus the total number of `(bucket, microBucket)` chains across the entire table is
   `totalMicroBuckets n_max = 2 ^ ⌊log₂ n_max⌋ ∈ (n_max / 2, max n_max 1]`, and each bucket
   indexes up to `effBucketCap n_max = 4 * 2 ^ microBits n_max` local slots using
   `effBucketPosBits n_max ≤ microBits n_max + 3 ≤ 6 * logLogFactor n_max` bits per pointer.
2. **Pointwise hysteresis slab potential (`bucketPotential`):**
   When `0 < bucketBits n_max`, each bucket partitions its `c_b = q_b * K + r_b` items into `q_b`
   full slabs of `K = slabSize n_max = (slabScale n_max)^2` items and `r_b < 2 * K` tail items
   (with `1 ≤ r_b` whenever `0 < q_b`). Promoting `K` tail items when `r_b` reaches `2 * K` and
   demoting a full slab when `r_b` drops to `0` with `0 < q_b` are paid for deterministically
   (pointwise for every hash seed) by the hysteresis potential `bucketPotential K q_b r_b`.
3. **3-wise independent expected collision and overflow bounds (`expect_probeExcess_le_three_on`,
   `tsum_uniform_probeExcess_twoStage_le`):**
   A single 3-wise independent hash family `H : ι → Q → Fin (2 ^ totalMicroBits n_max)` provides
   both the combined `(bucket, microBucket)` hash `feistelMicroHash` and (by bit-prefix projection
   `projLowBits`) the 3-wise independent bucket hash `feistelBucketHash`. For any key set `S` and
   key `u` with `#(S.erase u) ≤ n_max`, when the first stage `qOf` is quotient-injective on
   `insert u (S.erase u)`, `expect_probeExcess_le_three_on` bounds the expected micro-bucket
   collisions with keys in `S.erase u` by `2` and the expected bucket overflow above
   `effBucketCap n_max` by `1`, giving at most `3` expected excess probes. For a two-stage hash
   family whose first stage has collision bound `C_bad`, `tsum_uniform_probeExcess_twoStage_le`
   bounds expected excess probes by `3 + C_bad` whenever `#(S.erase u) ≤ n_max`, across operation
   sequences of arbitrary length without sticky collision flags or seed resampling.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctBucket.microBits`, `numMicroPerBucket`, `totalMicroBits`,
  `totalMicroBuckets`, `effBucketCap`, `effBucketPosBits`, `slabBits`, `slabSize`,
  `dirSlabsPerBucket`, `tailCapPerBucket`, `maxFullSlabs`, `maxTailItems`, `globalPtrBits`:
  dimension and bit-width parameters.
* `Cslib.DataStructure.Dictionary.SuccinctBucket.bucketPotential`,
  `pushBackCounts`, `pushBackWork`, `popBackCounts`, `popBackWork`: hysteresis slab potential and
  transitions.
* `Cslib.DataStructure.Dictionary.SuccinctBucket.feistelMicroHash`, `feistelBucketHash`,
  `feistelLocalMicro`, `microCollCount`, `bucketOvfCount`, `probeExcess`: Feistel micro-bucket and
  bucket hashes and per-operation excess probe counts.

## Main results

* `totalMicroBits_eq_log`, `numBuckets_mul_effBucketCap_le`, `numBuckets_mul_slabScale_cubed_le`,
  `globalPtrBits_le_two_mul_slabScale`: exact bit-budget identities across all `n_max`.
* `bucketPotential_pushBack_le`, `bucketPotential_popBack_le`: deterministic hysteresis
  amortization bounds.
* `isKWiseIndependentHash_projLowBits`, `expect_microCollCount_le_two_on`,
  `expect_bucketOvfCount_le_one_on`, `expect_probeExcess_le_three_on`,
  `sum_probeExcess_le_three_mul_card_on`, `tsum_uniform_probeExcess_twoStage_le`: expected
  probe-excess bounds under 3-wise independence.
* `succinct_space_le_succinctWords`, `tableArrays_words_le_succinctWords`: master word-level space
  accounting.

## References

* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*, Claim 5.7][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, *On the Optimal
  Time/Space Tradeoff for Hash Tables*, Sections 5.2 and 6.1,
  Lemma 24][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, *Iceberg Hashing:
  Optimizing Many Hash-Table Criteria at Once*,
  Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctBucket

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Micro-bucket, effective bucket capacity, and slab parameters -/

/-- Number of local micro-bucket bits `min ⌊log₂ n⌋ (3 * logLogFactor n)` within each Feistel
bucket. -/
@[expose]
def microBits (n : ℕ) : ℕ :=
  min (Nat.log 2 n) (3 * Dynamic.logLogFactor n)

/-- Number of micro-buckets `2 ^ microBits n` per Feistel bucket. -/
@[expose]
def numMicroPerBucket (n : ℕ) : ℕ :=
  2 ^ microBits n

/-- Total number of `(bucket, microBucket)` address bits `bucketBits n + microBits n = ⌊log₂ n⌋`. -/
@[expose]
def totalMicroBits (n : ℕ) : ℕ :=
  bucketBits n + microBits n

/-- Total number of micro-buckets `2 ^ totalMicroBits n = 2 ^ ⌊log₂ n⌋` across all buckets. -/
@[expose]
def totalMicroBuckets (n : ℕ) : ℕ :=
  2 ^ totalMicroBits n

/-- Effective per-bucket indexed local slot capacity `4 * 2 ^ microBits n`. -/
@[expose]
def effBucketCap (n : ℕ) : ℕ :=
  4 * numMicroPerBucket n

/-- Bit-width `⌈log₂ (min n (effBucketCap n) + 1)⌉` of 1-based local slot pointers
`0 .. min n (effBucketCap n)`. -/
@[expose]
def effBucketPosBits (n : ℕ) : ℕ :=
  Nat.clog 2 (min n (effBucketCap n) + 1)

/-- Base-2 logarithm of the slab size: `0` when `bucketBits n = 0` (single-bucket regime) and
`2 * logLogFactor n` when `0 < bucketBits n` (multi-bucket slab regime). -/
@[expose]
def slabBits (n : ℕ) : ℕ :=
  if bucketBits n = 0 then 0 else 2 * Dynamic.logLogFactor n

/-- Full-slab size `K = 2 ^ slabBits n` (`1` when `bucketBits n = 0`, `(slabScale n)^2` when
`0 < bucketBits n`). -/
@[expose]
def slabSize (n : ℕ) : ℕ :=
  2 ^ slabBits n

/-- Number of direct-indexed full-slab directory entries per bucket: `0` when `bucketBits n = 0` and
`4 * slabScale n` when `0 < bucketBits n` (covering all `4 * (slabScale n)^3 = effBucketCap n`
indexed local slots). -/
@[expose]
def dirSlabsPerBucket (n : ℕ) : ℕ :=
  if bucketBits n = 0 then 0 else 4 * slabScale n

/-- Maximum number of tail items per bucket (`0` when `bucketBits n = 0`, `2 * slabSize n` when
`0 < bucketBits n`). -/
@[expose]
def tailCapPerBucket (n : ℕ) : ℕ :=
  if bucketBits n = 0 then 0 else 2 * slabSize n

/-- Maximum number of full slabs across the entire table (`0` when `bucketBits n = 0`,
`n / slabSize n` when `0 < bucketBits n`). -/
@[expose]
def maxFullSlabs (n : ℕ) : ℕ :=
  if bucketBits n = 0 then 0 else n / slabSize n

/-- Maximum number of tail items across the entire table (`numBuckets n * tailCapPerBucket n`). -/
@[expose]
def maxTailItems (n : ℕ) : ℕ :=
  numBuckets n * tailCapPerBucket n

/-- Bit-width `⌈log₂ (n + 1)⌉` capable of representing any global index or count in `0 .. n`. -/
@[expose]
def globalPtrBits (n : ℕ) : ℕ :=
  Nat.clog 2 (n + 1)

/-- Quotient `keyQuotient (bucketBits n) u.val` packaged in `Fin (2 ^ quotientBits U n)`. -/
@[expose]
def quotientFin (U n : ℕ) (u : Fin U) : Fin (2 ^ quotientBits U n) :=
  ⟨keyQuotient (bucketBits n) u.val % 2 ^ quotientBits U n, Nat.mod_lt _ (by positivity)⟩

/-- When `n ≤ U`, `(quotientFin U n u).val = keyQuotient (bucketBits n) u.val`. -/
theorem quotientFin_val_eq {U n : ℕ} (hnU : n ≤ U) (u : Fin U) :
    (quotientFin U n u).val = keyQuotient (bucketBits n) u.val :=
  Nat.mod_eq_of_lt (keyQuotient_lt_two_pow_quotientBits hnU u.isLt)

/-- When `n ≤ U`, equality of `quotientFin U n` implies equality of `keyQuotient (bucketBits n)`. -/
theorem keyQuotient_eq_of_quotientFin_eq {U n : ℕ} (hnU : n ≤ U) (u₁ u₂ : Fin U)
    (h : quotientFin U n u₁ = quotientFin U n u₂) :
    keyQuotient (bucketBits n) u₁.val = keyQuotient (bucketBits n) u₂.val := by
  have hval := congrArg Fin.val h
  rwa [quotientFin_val_eq hnU, quotientFin_val_eq hnU] at hval

/-- For every `n : ℕ`, `totalMicroBits n = Nat.log 2 n`. -/
theorem totalMicroBits_eq_log (n : ℕ) : totalMicroBits n = Nat.log 2 n := by
  unfold totalMicroBits bucketBits microBits
  omega

/-- `bucketBits n` is at most `totalMicroBits n`. -/
theorem bucketBits_le_totalMicroBits (n : ℕ) : bucketBits n ≤ totalMicroBits n :=
  Nat.le_add_right _ _

/-- `microBits n` is at most `3 * Dynamic.logLogFactor n`. -/
theorem microBits_le_three_mul_logLogFactor (n : ℕ) :
    microBits n ≤ 3 * Dynamic.logLogFactor n :=
  Nat.min_le_right _ _

/-- Whenever `n ≤ U`, `totalMicroBits n ≤ keyBits U`. -/
theorem totalMicroBits_le_keyBits {U n : ℕ} (hnU : n ≤ U) :
    totalMicroBits n ≤ keyBits U := by
  rw [totalMicroBits_eq_log]
  unfold keyBits
  exact (Nat.log_mono_right hnU).trans (Nat.log_le_clog 2 U)

/-- If `U ≤ 2 ^ w` and `n ≤ U`, then `totalMicroBits n ≤ w`. -/
theorem totalMicroBits_le_of_le_pow {U w n : ℕ} (hnU : n ≤ U) (hU : U ≤ 2 ^ w) :
    totalMicroBits n ≤ w :=
  (totalMicroBits_le_keyBits hnU).trans (Nat.clog_le_of_le_pow hU)

/-- `numMicroPerBucket n` is always positive. -/
theorem numMicroPerBucket_pos (n : ℕ) : 0 < numMicroPerBucket n := by
  unfold numMicroPerBucket
  positivity

/-- `totalMicroBuckets n` is always positive. -/
theorem totalMicroBuckets_pos (n : ℕ) : 0 < totalMicroBuckets n := by
  unfold totalMicroBuckets
  positivity

/-- `totalMicroBuckets n` factors as `numBuckets n * numMicroPerBucket n`. -/
theorem totalMicroBuckets_eq_mul (n : ℕ) :
    totalMicroBuckets n = numBuckets n * numMicroPerBucket n := by
  unfold totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
  rw [Nat.pow_add]

/-- For every `n : ℕ`, `totalMicroBuckets n ≤ max n 1`. -/
theorem totalMicroBuckets_le (n : ℕ) : totalMicroBuckets n ≤ max n 1 := by
  rw [totalMicroBuckets, totalMicroBits_eq_log]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · exact (Nat.pow_log_le_self 2 (by omega)).trans (le_max_left n 1)

/-- When `1 ≤ n`, `totalMicroBuckets n ≤ n`. -/
theorem totalMicroBuckets_le_self {n : ℕ} (hn : 1 ≤ n) : totalMicroBuckets n ≤ n := by
  have h := totalMicroBuckets_le n
  rwa [max_eq_left hn] at h

/-- For every `n : ℕ`, `n ≤ 2 * totalMicroBuckets n`. -/
theorem le_two_mul_totalMicroBuckets (n : ℕ) : n ≤ 2 * totalMicroBuckets n := by
  rw [totalMicroBuckets, totalMicroBits_eq_log]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
    rw [Nat.pow_succ'] at hlt
    omega

/-- For every `n : ℕ`, `n ≤ (2 * numMicroPerBucket n) * numBuckets n`. -/
theorem le_two_mul_numMicro_mul_numBuckets (n : ℕ) :
    n ≤ (2 * numMicroPerBucket n) * numBuckets n := by
  have h := le_two_mul_totalMicroBuckets n
  rw [totalMicroBuckets_eq_mul] at h
  linarith

/-- `effBucketCap n` is at least `4`. -/
theorem four_le_effBucketCap (n : ℕ) : 4 ≤ effBucketCap n := by
  unfold effBucketCap
  have := numMicroPerBucket_pos n
  omega

/-- `effBucketCap n` is always positive. -/
theorem effBucketCap_pos (n : ℕ) : 0 < effBucketCap n := by
  have := four_le_effBucketCap n
  omega

/-- When `bucketBits n = 0`, `n < effBucketCap n` (so bucket `0` never overflows
`effBucketCap n`). -/
theorem lt_effBucketCap_of_bucketBits_eq_zero {n : ℕ} (hb : bucketBits n = 0) :
    n < effBucketCap n := by
  have h1 : numBuckets n = 1 := by simp [numBuckets, hb]
  have h2 := le_two_mul_numMicro_mul_numBuckets n
  rw [h1, mul_one] at h2
  unfold effBucketCap
  have := numMicroPerBucket_pos n
  omega

/-- When `0 < bucketBits n`, `microBits n = 3 * Dynamic.logLogFactor n` and
`effBucketCap n = 4 * (slabScale n) ^ 3`. -/
theorem effBucketCap_eq_four_mul_slabScale_cubed_of_pos {n : ℕ} (hb : 0 < bucketBits n) :
    effBucketCap n = 4 * (slabScale n) ^ 3 := by
  have hle : 3 * Dynamic.logLogFactor n ≤ Nat.log 2 n := by
    unfold bucketBits at hb
    omega
  have hm : microBits n = 3 * Dynamic.logLogFactor n := min_eq_right hle
  unfold effBucketCap numMicroPerBucket slabScale
  rw [hm, Nat.mul_comm 3 (Dynamic.logLogFactor n), pow_mul]

/-- Every 1-based local slot pointer `0 .. min n (effBucketCap n)` fits strictly below
`2 ^ effBucketPosBits n`. -/
theorem min_effBucketCap_lt_two_pow_effBucketPosBits (n : ℕ) :
    min n (effBucketCap n) < 2 ^ effBucketPosBits n := by
  unfold effBucketPosBits
  have hle : min n (effBucketCap n) + 1 ≤ 2 ^ Nat.clog 2 (min n (effBucketCap n) + 1) :=
    Nat.le_pow_clog (by decide) (min n (effBucketCap n) + 1)
  omega

/-- At capacity `0`, `effBucketPosBits 0 = 0`. -/
@[simp]
theorem effBucketPosBits_zero : effBucketPosBits 0 = 0 := by decide

/-- `effBucketPosBits n` is at most `6 * Dynamic.logLogFactor n`. -/
theorem effBucketPosBits_le (n : ℕ) :
    effBucketPosBits n ≤ 6 * Dynamic.logLogFactor n := by
  unfold effBucketPosBits
  have hcap : effBucketCap n = 2 ^ (microBits n + 2) := by
    unfold effBucketCap numMicroPerBucket
    rw [Nat.pow_add]
    ring
  have hpow : min n (effBucketCap n) + 1 ≤ 2 ^ (microBits n + 3) := by
    have hmin : min n (effBucketCap n) ≤ effBucketCap n := Nat.min_le_right _ _
    rw [hcap] at hmin
    have hpos := Nat.two_pow_pos (microBits n + 2)
    rw [Nat.pow_succ]
    omega
  have hclog : Nat.clog 2 (min n (effBucketCap n) + 1) ≤ microBits n + 3 :=
    Nat.clog_le_of_le_pow hpow
  have h1 := microBits_le_three_mul_logLogFactor n
  have h2 := Dynamic.one_le_logLogFactor n
  omega

/-- Total indexed local slots across all buckets satisfy
`numBuckets n * effBucketCap n = 4 * totalMicroBuckets n ≤ 4 * max n 1`. -/
theorem numBuckets_mul_effBucketCap_le (n : ℕ) :
    numBuckets n * effBucketCap n ≤ 4 * max n 1 := by
  calc numBuckets n * effBucketCap n
      = 4 * (numBuckets n * numMicroPerBucket n) := by
        unfold effBucketCap
        ring
    _ = 4 * totalMicroBuckets n := by rw [← totalMicroBuckets_eq_mul]
    _ ≤ 4 * max n 1 := Nat.mul_le_mul_left 4 (totalMicroBuckets_le n)

/-- When `1 ≤ n`, `numBuckets n * effBucketCap n ≤ 4 * n`. -/
theorem numBuckets_mul_effBucketCap_le_four_mul {n : ℕ} (hn : 1 ≤ n) :
    numBuckets n * effBucketCap n ≤ 4 * n := by
  have h := numBuckets_mul_effBucketCap_le n
  rwa [max_eq_left hn] at h

/-- `slabSize n` is always at least `1`. -/
theorem one_le_slabSize (n : ℕ) : 1 ≤ slabSize n := by
  unfold slabSize
  exact Nat.one_le_two_pow

/-- `slabSize n` is always positive. -/
theorem slabSize_pos (n : ℕ) : 0 < slabSize n :=
  one_le_slabSize n

/-- When `0 < bucketBits n`, `slabSize n = (slabScale n) ^ 2` and `4 ≤ slabSize n`. -/
theorem slabSize_eq_sq_of_pos {n : ℕ} (hb : 0 < bucketBits n) :
    slabSize n = (slabScale n) ^ 2 ∧ 4 ≤ slabSize n := by
  have hb0 : bucketBits n ≠ 0 := by omega
  have h1 : slabSize n = (slabScale n) ^ 2 := by
    unfold slabSize slabBits slabScale
    rw [ite_eq_right hb0, Nat.mul_comm 2 (Dynamic.logLogFactor n), pow_mul]
  refine ⟨h1, ?_⟩
  rw [h1]
  have h2 := two_le_slabScale n
  nlinarith

/-- When `0 < bucketBits n`, `numBuckets n * (slabScale n) ^ 3 ≤ n`. -/
theorem numBuckets_mul_slabScale_cubed_le {n : ℕ} (hb : 0 < bucketBits n) :
    numBuckets n * (slabScale n) ^ 3 ≤ n := by
  have hle : 3 * Dynamic.logLogFactor n < Nat.log 2 n := by
    unfold bucketBits at hb
    omega
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    simp at hle
  unfold numBuckets bucketBits slabScale
  rw [← pow_mul, ← pow_add, Nat.mul_comm (Dynamic.logLogFactor n) 3,
    Nat.sub_add_cancel (by omega)]
  exact Nat.pow_log_le_self 2 (by omega)

/-- `n` is strictly less than `2 ^ globalPtrBits n`. -/
theorem lt_two_pow_globalPtrBits (n : ℕ) : n < 2 ^ globalPtrBits n := by
  unfold globalPtrBits
  have hle : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by decide) (n + 1)
  omega

/-- At capacity `0`, `globalPtrBits 0 = 0`. -/
@[simp]
theorem globalPtrBits_zero : globalPtrBits 0 = 0 := by decide

/-- `effBucketPosBits n` is at most `globalPtrBits n`. -/
theorem effBucketPosBits_le_globalPtrBits (n : ℕ) :
    effBucketPosBits n ≤ globalPtrBits n :=
  Nat.clog_mono_right 2 (by omega)

/-- Whenever `n ≤ U` and `U < 2 ^ w`, `globalPtrBits n ≤ w`. -/
theorem globalPtrBits_le_of_lt_pow {U w n : ℕ} (hnU : n ≤ U) (hU : U < 2 ^ w) :
    globalPtrBits n ≤ w :=
  Nat.clog_le_of_le_pow (by omega)

/-- Whenever `n ≤ U` and `U < 2 ^ w`, `effBucketPosBits n ≤ w`. -/
theorem effBucketPosBits_le_of_lt_pow {U w n : ℕ} (hnU : n ≤ U) (hU : U < 2 ^ w) :
    effBucketPosBits n ≤ w :=
  (effBucketPosBits_le_globalPtrBits n).trans (globalPtrBits_le_of_lt_pow hnU hU)

/-- When `0 < bucketBits n`, `globalPtrBits n ≤ 2 * slabScale n`. -/
theorem globalPtrBits_le_two_mul_slabScale {n : ℕ} (hb : 0 < bucketBits n) :
    globalPtrBits n ≤ 2 * slabScale n := by
  have hcube := numBuckets_mul_slabScale_cubed_le hb
  have hscale := two_le_slabScale n
  have hb_pos := numBuckets_pos n
  have hcube8 : 8 ≤ (slabScale n) ^ 3 :=
    calc 8 = 2 ^ 3 := by decide
      _ ≤ (slabScale n) ^ 3 := Nat.pow_le_pow_left hscale 3
  have hn8 : 8 ≤ n := by nlinarith
  have hmax : max n 4 = n := max_eq_left (by omega)
  have hle2n : n + 1 ≤ 2 * max n 4 := by omega
  have hclog1 : Nat.clog 2 (n + 1) ≤ Nat.clog 2 (max n 4) + 1 := by
    calc Nat.clog 2 (n + 1)
        ≤ Nat.clog 2 (2 * max n 4) := Nat.clog_mono_right 2 hle2n
      _ = Nat.clog 2 (max n 4) + 1 := by
        rw [Nat.clog_of_two_le (by decide : 1 < 2) (by omega : 2 ≤ 2 * max n 4)]
        congr 2
        omega
  have hclog2 : Nat.clog 2 (max n 4) ≤ slabScale n := by
    unfold slabScale Dynamic.logLogFactor
    exact Nat.le_pow_clog (by decide) (Nat.clog 2 (max n 4))
  unfold globalPtrBits
  omega

/-- For every `n : ℕ`, `maxTailItems n ≤ n`. -/
theorem maxTailItems_le (n : ℕ) : maxTailItems n ≤ n := by
  unfold maxTailItems tailCapPerBucket
  split_ifs with hb
  · simp
  · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
    have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
    have hslab := (slabSize_eq_sq_of_pos hb_pos).1
    have hscale := two_le_slabScale n
    calc numBuckets n * (2 * slabSize n)
        = numBuckets n * (slabScale n) ^ 2 * 2 := by
          rw [hslab]
          ring
      _ ≤ numBuckets n * (slabScale n) ^ 2 * slabScale n := by gcongr
      _ = numBuckets n * (slabScale n) ^ 3 := by ring
      _ ≤ n := hcube

/-- For every `n : ℕ`, `maxFullSlabs n ≤ n`. -/
theorem maxFullSlabs_le (n : ℕ) : maxFullSlabs n ≤ n := by
  unfold maxFullSlabs
  split_ifs
  · exact Nat.zero_le n
  · exact Nat.div_le_self n (slabSize n)

/-- For every `n : ℕ`, `maxTailItems n * globalPtrBits n ≤ 4 * n`. -/
theorem maxTailItems_mul_globalPtrBits_le (n : ℕ) :
    maxTailItems n * globalPtrBits n ≤ 4 * n := by
  unfold maxTailItems tailCapPerBucket
  split_ifs with hb
  · simp
  · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
    have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
    have hslab := (slabSize_eq_sq_of_pos hb_pos).1
    have hptr := globalPtrBits_le_two_mul_slabScale hb_pos
    calc numBuckets n * (2 * slabSize n) * globalPtrBits n
        ≤ numBuckets n * (2 * (slabScale n) ^ 2) * (2 * slabScale n) := by
          rw [hslab]
          gcongr
      _ = 4 * (numBuckets n * (slabScale n) ^ 3) := by ring
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hcube

/-- For every `n : ℕ`, `(numBuckets n * dirSlabsPerBucket n) * globalPtrBits n ≤ 4 * n`. -/
theorem slabDir_bits_le (n : ℕ) :
    (numBuckets n * dirSlabsPerBucket n) * globalPtrBits n ≤ 4 * n := by
  unfold dirSlabsPerBucket
  split_ifs with hb
  · simp
  · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
    have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
    have hscale := two_le_slabScale n
    have hptr := globalPtrBits_le_two_mul_slabScale hb_pos
    calc numBuckets n * (4 * slabScale n) * globalPtrBits n
        ≤ numBuckets n * (4 * slabScale n) * (2 * slabScale n) := by gcongr
      _ = 4 * (numBuckets n * (slabScale n) ^ 2 * 2) := by ring
      _ ≤ 4 * (numBuckets n * (slabScale n) ^ 2 * slabScale n) := by gcongr
      _ = 4 * (numBuckets n * (slabScale n) ^ 3) := by ring
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hcube

/-- For every `n : ℕ`, `maxFullSlabs n * globalPtrBits n ≤ n`. -/
theorem maxFullSlabs_mul_globalPtrBits_le (n : ℕ) :
    maxFullSlabs n * globalPtrBits n ≤ n := by
  unfold maxFullSlabs
  split_ifs with hb
  · simp
  · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
    have hslab := (slabSize_eq_sq_of_pos hb_pos).1
    have hscale := two_le_slabScale n
    have hptr := globalPtrBits_le_two_mul_slabScale hb_pos
    have hdiv_le : n / slabSize n * slabSize n ≤ n := Nat.div_mul_le_self n (slabSize n)
    have h2L_le_sq : 2 * slabScale n ≤ slabSize n := by
      rw [hslab]
      nlinarith
    calc n / slabSize n * globalPtrBits n
        ≤ n / slabSize n * (2 * slabScale n) := by gcongr
      _ ≤ n / slabSize n * slabSize n := by gcongr
      _ ≤ n := hdiv_le

/-- For every `n : ℕ`, when `0 < bucketBits n`, `2 * (numBuckets n * globalPtrBits n) ≤ n`. -/
theorem two_mul_numBuckets_mul_globalPtrBits_le_of_pos {n : ℕ} (hb : 0 < bucketBits n) :
    2 * (numBuckets n * globalPtrBits n) ≤ n := by
  have hcube := numBuckets_mul_slabScale_cubed_le hb
  have hscale := two_le_slabScale n
  have hptr := globalPtrBits_le_two_mul_slabScale hb
  have hsq : 4 ≤ (slabScale n) ^ 2 := by nlinarith
  have h4L_le_cube : 4 * slabScale n ≤ (slabScale n) ^ 3 := by
    calc 4 * slabScale n ≤ (slabScale n) ^ 2 * slabScale n := by nlinarith
      _ = (slabScale n) ^ 3 := by ring
  calc 2 * (numBuckets n * globalPtrBits n)
      ≤ 2 * (numBuckets n * (2 * slabScale n)) := by gcongr
    _ = numBuckets n * (4 * slabScale n) := by ring
    _ ≤ numBuckets n * (slabScale n) ^ 3 := by gcongr
    _ ≤ n := hcube

/-- For every `n : ℕ`, when `0 < bucketBits n`, `numBuckets n * globalPtrBits n ≤ n`. -/
theorem numBuckets_mul_globalPtrBits_le_of_pos {n : ℕ} (hb : 0 < bucketBits n) :
    numBuckets n * globalPtrBits n ≤ n := by
  have h := two_mul_numBuckets_mul_globalPtrBits_le_of_pos hb
  omega

/-! ## Section 2: Hysteresis slab potential (`bucketPotential`) -/

/-- Per-bucket slab hysteresis potential `ϕ(K, q, r)` for slab size `K`:
* `r - K` when `K ≤ r` (accumulating potential toward a slab promotion at `r = 2 * K`);
* `K - r` when `0 < q ∧ r < K` (accumulating potential toward a slab demotion at `r = 0`);
* `0` when `q = 0 ∧ r < K`. -/
@[expose]
def bucketPotential (K q r : ℕ) : ℕ :=
  if K ≤ r then r - K
  else if 0 < q then K - r
  else 0

/-- An empty bucket (`q = 0`, `r = 0`) has zero hysteresis potential. -/
@[simp]
theorem bucketPotential_zero (K : ℕ) : bucketPotential K 0 0 = 0 := by
  unfold bucketPotential
  split_ifs <;> omega

/-- When `r ≤ 2 * K`, `bucketPotential K q r ≤ K`. -/
theorem bucketPotential_le (K q r : ℕ) (hr : r ≤ 2 * K) :
    bucketPotential K q r ≤ K := by
  unfold bucketPotential
  split_ifs <;> omega

/-- Updated `(q', r')` slab and tail counts after appending one item to a bucket with counts
`(q, r)`: promotes `K` tail items to a new full slab when `r + 1 = 2 * K`. -/
@[expose]
def pushBackCounts (K q r : ℕ) : ℕ × ℕ :=
  if r + 1 = 2 * K then (q + 1, K) else (q, r + 1)

/-- Number of items moved between the tail pool and full-slab pool by `pushBackCounts`. -/
@[expose]
def pushBackWork (K r : ℕ) : ℕ :=
  if r + 1 = 2 * K then K else 0

/-- Updated `(q', r')` slab and tail counts after removing the last item from a bucket with counts
`(q, r)` (`1 ≤ r`): demotes the last full slab into `K` tail items when `r = 1 ∧ 0 < q`. -/
@[expose]
def popBackCounts (K q r : ℕ) : ℕ × ℕ :=
  if r = 1 ∧ 0 < q then (q - 1, K) else (q, r - 1)

/-- Number of items moved between the full-slab pool and tail pool by `popBackCounts`. -/
@[expose]
def popBackWork (K q r : ℕ) : ℕ :=
  if r = 1 ∧ 0 < q then K else 0

/-- `pushBackCounts` increments the total item count `q * K + r` by `1`. -/
theorem pushBackCounts_sum (K q r : ℕ) :
    (pushBackCounts K q r).1 * K + (pushBackCounts K q r).2 = q * K + r + 1 := by
  unfold pushBackCounts
  split_ifs with h
  · dsimp only
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · dsimp only
    omega

/-- `pushBackCounts` preserves the hysteresis upper bound `r' < 2 * K` and positivity `1 ≤ r'`. -/
theorem pushBackCounts_bounds {K q r : ℕ} (hK : 1 ≤ K) (hr : r < 2 * K) :
    1 ≤ (pushBackCounts K q r).2 ∧ (pushBackCounts K q r).2 < 2 * K := by
  unfold pushBackCounts
  split_ifs <;> dsimp only <;> omega

/-- `popBackCounts` decrements the total item count `q * K + r` by `1` when `1 ≤ r`. -/
theorem popBackCounts_sum {K q r : ℕ} (hr : 1 ≤ r) :
    (popBackCounts K q r).1 * K + (popBackCounts K q r).2 = q * K + r - 1 := by
  unfold popBackCounts
  split_ifs with h
  · dsimp only
    rcases h with ⟨rfl, hq⟩
    have hmul : (q - 1) * K + K = q * K := by
      calc (q - 1) * K + K = (q - 1 + 1) * K := by ring
        _ = q * K := by rw [Nat.sub_add_cancel hq]
    omega
  · dsimp only
    omega

/-- `popBackCounts` preserves `r' < 2 * K` and `(0 < q' → 1 ≤ r')`. -/
theorem popBackCounts_bounds {K q r : ℕ} (hK : 1 ≤ K) (hr1 : 1 ≤ r) (hr2 : r < 2 * K) :
    (popBackCounts K q r).2 < 2 * K ∧
      (0 < (popBackCounts K q r).1 → 1 ≤ (popBackCounts K q r).2) := by
  unfold popBackCounts
  split_ifs <;> dsimp only <;> omega

/-- **Pointwise hysteresis amortization for `pushBack`:**
`bucketPotential K q' r' + pushBackWork K r ≤ bucketPotential K q r + 1`. -/
theorem bucketPotential_pushBack_le (K q r : ℕ) :
    bucketPotential K (pushBackCounts K q r).1 (pushBackCounts K q r).2 +
      pushBackWork K r ≤ bucketPotential K q r + 1 := by
  unfold bucketPotential pushBackCounts pushBackWork
  split_ifs <;> dsimp only at * <;> omega

/-- **Pointwise hysteresis amortization for `popBack`:**
`bucketPotential K q' r' + popBackWork K q r ≤ bucketPotential K q r + 1`. -/
theorem bucketPotential_popBack_le (K q r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < 2 * K) :
    bucketPotential K (popBackCounts K q r).1 (popBackCounts K q r).2 +
      popBackWork K q r ≤ bucketPotential K q r + 1 := by
  unfold bucketPotential popBackCounts popBackWork
  split_ifs <;> dsimp only at * <;> omega

/-! ## Section 3: Feistel micro-bucket and bucket hash decomposition & expected cost bounds -/

section ProbabilityBounds

variable {ι Q : Type*} [Fintype ι]

/-- Project an `m`-bit hash value in `Fin (2 ^ m)` onto its low `b ≤ m` bits in `Fin (2 ^ b)`. -/
@[expose]
def projLowBits {b m : ℕ} (_hbm : b ≤ m) (z : Fin (2 ^ m)) : Fin (2 ^ b) :=
  ⟨z.val % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩

/-- Projecting a `k`-wise independent hash family `H : ι → Q → Fin (2 ^ m)` onto its low `b ≤ m`
bits via `projLowBits` preserves `k`-wise independence. -/
theorem isKWiseIndependentHash_projLowBits {k b m : ℕ} (hbm : b ≤ m)
    {H : ι → Q → Fin (2 ^ m)} (hh : IsKWiseIndependentHash k H) :
    IsKWiseIndependentHash k (fun i q => projLowBits hbm (H i q)) := by
  have h1 := hh.map_equiv (BitString.equivFin m).symm
  have h2 := h1.comp_surjective_addMonoidHom
    (BitString.restrictBitsAddHom hbm)
    (BitString.restrictBitsAddHom_surjective hbm)
  have h3 := h2.map_equiv (BitString.equivFin b)
  have heq : (fun i q => projLowBits hbm (H i q)) =
      fun i q => BitString.equivFin b
        (BitString.restrictBitsAddHom hbm ((BitString.equivFin m).symm (H i q))) := by
    funext i q
    apply Fin.ext
    rw [BitString.val_equivFin_restrictBitsAddHom hbm, Equiv.apply_symm_apply]
    rfl
  rwa [heq]

omit [Fintype ι] in
/-- Projecting `feistelXor b m hbm qOf H i u` onto its low `b` bits agrees with `feistelXor`
evaluated on the projected hash `fun i q => projLowBits hbm (H i q)`. -/
theorem projLowBits_feistelXor {U b m : ℕ} (hbm : b ≤ m) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ m)) (i : ι) (u : Fin U) :
    projLowBits hbm (feistelXor b m hbm qOf H i u) =
      feistelXor b b le_rfl qOf (fun i q => projLowBits hbm (H i q)) i u := by
  apply Fin.ext
  dsimp only [projLowBits, feistelXor]
  rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (keyLow_lt b u.val)]

/-- Combined `(bucket, microBucket)` Feistel hash mapping `u : Fin U` into
`Fin (2 ^ totalMicroBits n_max)`. -/
@[expose]
def feistelMicroHash {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u : Fin U) :
    Fin (2 ^ totalMicroBits n_max) :=
  feistelXor (bucketBits n_max) (totalMicroBits n_max)
    (bucketBits_le_totalMicroBits n_max) qOf H i u

/-- Feistel bucket hash mapping `u : Fin U` into `Fin (2 ^ bucketBits n_max)` (the low
`bucketBits n_max` bits of `feistelMicroHash`). -/
@[expose]
def feistelBucketHash {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u : Fin U) :
    Fin (2 ^ bucketBits n_max) :=
  projLowBits (bucketBits_le_totalMicroBits n_max) (feistelMicroHash n_max qOf H i u)

/-- Local micro-bucket index `(H i (qOf u)).val / 2 ^ bucketBits n_max < numMicroPerBucket n_max`
within `u`'s Feistel bucket. -/
@[expose]
def feistelLocalMicro {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u : Fin U) :
    Fin (numMicroPerBucket n_max) :=
  ⟨(H i (qOf u)).val / 2 ^ bucketBits n_max, by
    dsimp only [numMicroPerBucket]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact (H i (qOf u)).isLt⟩

omit [Fintype ι] in
/-- `(feistelMicroHash n_max qOf H i u).val` decomposes into `feistelBucketHash` in the low
`bucketBits n_max` bits and `feistelLocalMicro` in the high `microBits n_max` bits. -/
theorem feistelMicroHash_val_eq {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u : Fin U) :
    (feistelMicroHash n_max qOf H i u).val =
      (feistelLocalMicro n_max qOf H i u).val * 2 ^ bucketBits n_max +
        (feistelBucketHash n_max qOf H i u).val := by
  have hdiv : (feistelMicroHash n_max qOf H i u).val / 2 ^ bucketBits n_max =
      (feistelLocalMicro n_max qOf H i u).val := by
    dsimp only [feistelMicroHash, feistelXor, feistelLocalMicro]
    rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (keyLow_lt (bucketBits n_max) u.val), Nat.xor_zero]
  have hmod : (feistelMicroHash n_max qOf H i u).val % 2 ^ bucketBits n_max =
      (feistelBucketHash n_max qOf H i u).val := rfl
  have h := Nat.div_add_mod (feistelMicroHash n_max qOf H i u).val (2 ^ bucketBits n_max)
  rw [hdiv, hmod, Nat.mul_comm] at h
  exact h.symm

omit [Fintype ι] in
/-- Two keys land in the same global micro-bucket `feistelMicroHash` if and only if they land in
the same Feistel bucket `feistelBucketHash` and the same local micro-bucket `feistelLocalMicro`. -/
theorem feistelMicroHash_eq_iff {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u₁ u₂ : Fin U) :
    feistelMicroHash n_max qOf H i u₁ = feistelMicroHash n_max qOf H i u₂ ↔
      feistelBucketHash n_max qOf H i u₁ = feistelBucketHash n_max qOf H i u₂ ∧
        feistelLocalMicro n_max qOf H i u₁ = feistelLocalMicro n_max qOf H i u₂ := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    have hdiv : (feistelMicroHash n_max qOf H i u₁).val / 2 ^ bucketBits n_max =
        (feistelLocalMicro n_max qOf H i u₁).val := by
      dsimp only [feistelMicroHash, feistelXor, feistelLocalMicro]
      rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (keyLow_lt (bucketBits n_max) u₁.val), Nat.xor_zero]
    have hdiv2 : (feistelMicroHash n_max qOf H i u₂).val / 2 ^ bucketBits n_max =
        (feistelLocalMicro n_max qOf H i u₂).val := by
      dsimp only [feistelMicroHash, feistelXor, feistelLocalMicro]
      rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (keyLow_lt (bucketBits n_max) u₂.val), Nat.xor_zero]
    refine ⟨congrArg (projLowBits (bucketBits_le_totalMicroBits n_max)) h, Fin.ext ?_⟩
    rw [← hdiv, ← hdiv2, hval]
  · rintro ⟨hb, hm⟩
    apply Fin.ext
    rw [feistelMicroHash_val_eq, feistelMicroHash_val_eq, hb, hm]

omit [Fintype ι] in
/-- `feistelBucketHash` agrees with `feistelBucket` on the integer hash output `(H i (qOf u)).val`.
-/
theorem feistelBucketHash_val_eq_feistelBucket {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (u : Fin U) :
    (feistelBucketHash n_max qOf H i u).val =
      feistelBucket (bucketBits n_max) (fun _ => (H i (qOf u)).val) u.val := by
  dsimp only [feistelBucketHash, projLowBits, feistelMicroHash, feistelXor,
    feistelBucket]
  rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (keyLow_lt (bucketBits n_max) u.val)]

/-- Number of keys in `S.erase u` colliding with `u` in the combined `(bucket, microBucket)` hash
`feistelMicroHash`. -/
@[expose]
def microCollCount {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (S : Finset (Fin U)) (u : Fin U) : ℕ :=
  #{x ∈ S.erase u | feistelMicroHash n_max qOf H i x = feistelMicroHash n_max qOf H i u}

/-- Number of keys in `S.erase u` in `u`'s Feistel bucket beyond the indexed local capacity
`effBucketCap n_max`. -/
@[expose]
def bucketOvfCount {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (S : Finset (Fin U)) (u : Fin U) : ℕ :=
  #{x ∈ S.erase u | feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u} -
    effBucketCap n_max

/-- Combined excess probe count `microCollCount + bucketOvfCount` for key `u` against `S`. -/
@[expose]
def probeExcess {U : ℕ} (n_max : ℕ) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι) (S : Finset (Fin U)) (u : Fin U) : ℕ :=
  microCollCount n_max qOf H i S u + bucketOvfCount n_max qOf H i S u

/-- **Expected micro-bucket collision bound:** under a pairwise-independent hash `H`, for any
`S : Finset (Fin U)` with `#(S.erase u) ≤ n_max` such that `qOf` is quotient-injective on
`insert u (S.erase u)`, the expected number of keys in `S.erase u` landing in `u`'s micro-bucket is
at most `2`. -/
theorem expect_microCollCount_le_two_on {U n_max : ℕ}
    {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ totalMicroBits n_max)} (hh : IsPairwiseIndependentHash H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val) :
    𝔼 i, (microCollCount n_max qOf H i S u : ℚ) ≤ 2 := by
  classical
  have hexp : 𝔼 i, (microCollCount n_max qOf H i S u : ℚ) ≤
      (#(S.erase u) : ℚ) / (2 ^ totalMicroBits n_max : ℚ) := by
    unfold microCollCount feistelMicroHash
    rw [expect_card_feistelXor_eq_on (𝕜 := ℚ) (bucketBits_le_totalMicroBits n_max) hh S u hq]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_filter_le _ _)) (by positivity)
  have hle : (#(S.erase u) : ℚ) / (2 ^ totalMicroBits n_max : ℚ) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hcard : #(S.erase u) ≤ 2 * 2 ^ totalMicroBits n_max :=
      hS.trans (le_two_mul_totalMicroBuckets n_max)
    exact_mod_cast hcard
  exact hexp.trans hle

/-- **Expected bucket overflow bound:** under a 3-wise independent hash `H`, for any
`S : Finset (Fin U)` with `#(S.erase u) ≤ n_max` such that `qOf` is quotient-injective on
`insert u (S.erase u)`, the expected overflow above `effBucketCap n_max` in `u`'s Feistel bucket is
at most `1`. -/
theorem expect_bucketOvfCount_le_one_on {U n_max : ℕ}
    {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ totalMicroBits n_max)} (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val) :
    𝔼 i, (bucketOvfCount n_max qOf H i S u : ℚ) ≤ 1 := by
  classical
  let H_b : ι → Q → Fin (2 ^ bucketBits n_max) :=
    fun i q => projLowBits (bucketBits_le_totalMicroBits n_max) (H i q)
  have hh_b : IsKWiseIndependentHash 3 H_b :=
    isKWiseIndependentHash_projLowBits (bucketBits_le_totalMicroBits n_max) hh
  let D : ℕ := 2 * numMicroPerBucket n_max
  have hD : 1 ≤ D := by
    dsimp only [D]
    have := numMicroPerBucket_pos n_max
    omega
  have h2D : 2 * D = effBucketCap n_max := by
    dsimp only [D, effBucketCap]
    ring
  have hSD : #(S.erase u) ≤ D * 2 ^ bucketBits n_max :=
    hS.trans (le_two_mul_numMicro_mul_numBuckets n_max)
  have hovf := expect_feistelXor_overflow_le_on le_rfl hD hh_b S u hSD hq
  have heq (i : ι) :
      #{x ∈ S.erase u |
          feistelXor (bucketBits n_max) (bucketBits n_max) le_rfl qOf H_b i x =
            feistelXor (bucketBits n_max) (bucketBits n_max) le_rfl qOf H_b i u} - 2 * D =
        bucketOvfCount n_max qOf H i S u := by
    rw [h2D]
    dsimp only [bucketOvfCount, feistelBucketHash, feistelMicroHash, H_b]
    simp only [projLowBits_feistelXor]
  simp only [heq] at hovf
  exact hovf

/-- **Master expected probe-excess bound:** under a 3-wise independent hash `H`, for any
`S : Finset (Fin U)` with `#(S.erase u) ≤ n_max` such that `qOf` is quotient-injective on
`insert u (S.erase u)`, the expected combined probe excess `probeExcess n_max qOf H i S u` is at
most `3`. -/
theorem expect_probeExcess_le_three_on {U n_max : ℕ}
    {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ totalMicroBits n_max)} (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val) :
    𝔼 i, (probeExcess n_max qOf H i S u : ℚ) ≤ 3 := by
  have : Nonempty ι := hh.nonempty
  have hhpw : IsPairwiseIndependentHash H := hh.isPairwiseIndependentHash (by decide)
  have h1 := expect_microCollCount_le_two_on hhpw S u hS hq
  have h2 := expect_bucketOvfCount_le_one_on hh S u hS hq
  unfold probeExcess
  push_cast
  rw [expect_add_distrib]
  linarith

/-- Natural-number sum form of `expect_probeExcess_le_three_on`: the sum of `probeExcess` over all
seeds `i : ι` is at most `3 * Fintype.card ι`. -/
theorem sum_probeExcess_le_three_mul_card_on {U n_max : ℕ}
    {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ totalMicroBits n_max)} (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val) :
    (∑ i : ι, probeExcess n_max qOf H i S u) ≤ 3 * Fintype.card ι := by
  have := hh.nonempty
  have hexp := expect_probeExcess_le_three_on hh S u hS hq
  rw [Fintype.expect_eq_sum_div_card] at hexp
  have hcard_pos : (0 : ℚ) < (Fintype.card ι : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hcard_pos] at hexp
  exact_mod_cast hexp

omit [Fintype ι] in
/-- Deterministic worst-case bound on `probeExcess`: for any seed `i`,
`probeExcess n_max qOf H i S u ≤ 2 * #(S.erase u)`. -/
theorem probeExcess_le_two_mul_card {U n_max : ℕ}
    (qOf : Fin U → Q) (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι)
    (S : Finset (Fin U)) (u : Fin U) :
    probeExcess n_max qOf H i S u ≤ 2 * #(S.erase u) := by
  unfold probeExcess microCollCount bucketOvfCount
  have h1 : #{x ∈ S.erase u | feistelMicroHash n_max qOf H i x = feistelMicroHash n_max qOf H i u} ≤
      #(S.erase u) := card_filter_le _ _
  have h2 : #{x ∈ S.erase u |
      feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u} -
        effBucketCap n_max ≤ #(S.erase u) :=
    (Nat.sub_le _ _).trans (card_filter_le _ _)
  omega

omit [Fintype ι] in
/-- **Two-stage universe-reduced expected probe-excess bound:** for a product seed space
`ι₁ × ι₂` where the first stage `qOf : ι₁ → Fin U → Q` is quotient-injective on
`insert u (S.erase u)` on a good seed set `G ⊆ univ` with
`#(univ \ G) * (2 * #(S.erase u)) ≤ C_bad * Fintype.card ι₁`, and the second stage
`H : ι₂ → Q → Fin (2 ^ totalMicroBits n_max)` is 3-wise independent, the expected `probeExcess`
under `PMF.uniformOfFintype (ι₁ × ι₂)` is at most `3 + C_bad`. -/
theorem tsum_uniform_probeExcess_twoStage_le {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Nonempty ι₁] [Fintype ι₂] [Nonempty ι₂]
    {U n_max C_bad : ℕ}
    (qOf : ι₁ → Fin U → Q)
    (H : ι₂ → Q → Fin (2 ^ totalMicroBits n_max)) (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ n_max)
    (G : Finset ι₁)
    (hG : ∀ i₁ ∈ G, ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf i₁ u₁ = qOf i₁ u₂ →
        keyQuotient (bucketBits n_max) u₁.val = keyQuotient (bucketBits n_max) u₂.val)
    (hbad : #(univ \ G) * (2 * #(S.erase u)) ≤ C_bad * Fintype.card ι₁) :
    (∑' p : ι₁ × ι₂,
      (PMF.uniformOfFintype (ι₁ × ι₂)) p *
        (probeExcess n_max (qOf p.1) H p.2 S u : ℝ≥0∞)) ≤ ((3 + C_bad : ℕ) : ℝ≥0∞) := by
  classical
  have hinner (i₁ : ι₁) :
      (∑ i₂ : ι₂, probeExcess n_max (qOf i₁) H i₂ S u) ≤
        (if i₁ ∈ G then 3 else 2 * #(S.erase u)) * Fintype.card ι₂ := by
    split_ifs with hi₁
    · exact sum_probeExcess_le_three_mul_card_on hh S u hS (hG i₁ hi₁)
    · calc (∑ i₂ : ι₂, probeExcess n_max (qOf i₁) H i₂ S u)
          ≤ ∑ _i₂ : ι₂, (2 * #(S.erase u)) :=
            sum_le_sum fun i₂ _ => probeExcess_le_two_mul_card (qOf i₁) H i₂ S u
        _ = (2 * #(S.erase u)) * Fintype.card ι₂ := by
            rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  have houter :
      (∑ i₁ : ι₁, (if i₁ ∈ G then 3 else 2 * #(S.erase u))) ≤
        (3 + C_bad) * Fintype.card ι₁ := by
    have hsplit :
        (∑ i₁ : ι₁, (if i₁ ∈ G then 3 else 2 * #(S.erase u))) =
          ∑ i₁ ∈ univ.filter (· ∈ G), 3 +
            ∑ i₁ ∈ univ.filter (· ∉ G), (2 * #(S.erase u)) := by
      rw [← sum_ite]
    have hG_le : ∑ _i₁ ∈ univ.filter (· ∈ G), 3 ≤ 3 * Fintype.card ι₁ := by
      rw [sum_const, smul_eq_mul, mul_comm]
      exact Nat.mul_le_mul_left 3 (card_filter_le _ _)
    have hbad_eq : univ.filter (· ∉ G) = univ \ G := by
      ext i₁
      simp [mem_sdiff]
    have hbad_le : ∑ _i₁ ∈ univ.filter (· ∉ G), (2 * #(S.erase u)) ≤ C_bad * Fintype.card ι₁ := by
      rw [hbad_eq, sum_const, smul_eq_mul]
      exact hbad
    have hdist : (3 + C_bad) * Fintype.card ι₁ =
        3 * Fintype.card ι₁ + C_bad * Fintype.card ι₁ := Nat.add_mul _ _ _
    omega
  have hprod :
      (∑ p : ι₁ × ι₂, probeExcess n_max (qOf p.1) H p.2 S u) ≤
        (3 + C_bad) * Fintype.card (ι₁ × ι₂) := by
    rw [Fintype.sum_prod_type]
    calc (∑ i₁ : ι₁, ∑ i₂ : ι₂, probeExcess n_max (qOf i₁) H i₂ S u)
        ≤ ∑ i₁ : ι₁, (if i₁ ∈ G then 3 else 2 * #(S.erase u)) * Fintype.card ι₂ :=
          sum_le_sum fun i₁ _ => hinner i₁
      _ = (∑ i₁ : ι₁, (if i₁ ∈ G then 3 else 2 * #(S.erase u))) * Fintype.card ι₂ := by
          rw [← sum_mul]
      _ ≤ ((3 + C_bad) * Fintype.card ι₁) * Fintype.card ι₂ :=
          Nat.mul_le_mul_right _ houter
      _ = (3 + C_bad) * Fintype.card (ι₁ × ι₂) := by
          rw [Fintype.card_prod, mul_assoc]
  calc (∑' p : ι₁ × ι₂,
        (PMF.uniformOfFintype (ι₁ × ι₂)) p *
          (probeExcess n_max (qOf p.1) H p.2 S u : ℝ≥0∞))
      = (Fintype.card (ι₁ × ι₂) : ℝ≥0∞)⁻¹ *
          ((∑ p : ι₁ × ι₂, probeExcess n_max (qOf p.1) H p.2 S u : ℕ) : ℝ≥0∞) := by
        rw [tsum_fintype]
        simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum, Nat.cast_sum]
    _ ≤ (Fintype.card (ι₁ × ι₂) : ℝ≥0∞)⁻¹ *
          (((3 + C_bad) * Fintype.card (ι₁ × ι₂) : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ((3 + C_bad : ℕ) : ℝ≥0∞) := by
        push_cast
        rw [mul_comm ((3 : ℝ≥0∞) + (C_bad : ℝ≥0∞)), ← mul_assoc,
          ENNReal.inv_mul_cancel, one_mul]
        · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        · exact ENNReal.natCast_ne_top _

end ProbabilityBounds

/-! ## Section 4: Cardinality bounds for injective bucket and micro-bucket slot maps -/

/-- If a finset `J : Finset ℕ` of local slot indices injects via `keyAt : ℕ → Fin U` into the keys
of `S` landing in `u`'s micro-bucket, then `#J ≤ 1 + microCollCount n_max qOf H i S u`. -/
theorem card_microSlots_le {ι Q : Type*} {U n_max : ℕ}
    (qOf : Fin U → Q) (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι)
    (S : Finset (Fin U)) (u : Fin U)
    (J : Finset ℕ) (keyAt : ℕ → Fin U)
    (hinj : Set.InjOn keyAt J)
    (hmem : ∀ j ∈ J, keyAt j ∈ S ∧
      feistelMicroHash n_max qOf H i (keyAt j) = feistelMicroHash n_max qOf H i u) :
    #J ≤ 1 + microCollCount n_max qOf H i S u := by
  classical
  let target : Finset (Fin U) :=
    insert u {x ∈ S.erase u | feistelMicroHash n_max qOf H i x = feistelMicroHash n_max qOf H i u}
  have hsub : J.image keyAt ⊆ target := by
    intro x hx
    rcases mem_image.mp hx with ⟨j, hj, rfl⟩
    rcases hmem j hj with ⟨hjS, hjM⟩
    by_cases hju : keyAt j = u
    · rw [hju]
      exact mem_insert_self u _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨hju, hjS⟩, hjM⟩)
  calc #J = #(J.image keyAt) := (card_image_of_injOn hinj).symm
    _ ≤ #target := card_le_card hsub
    _ ≤ 1 + microCollCount n_max qOf H i S u := by
        have := card_insert_le u
          {x ∈ S.erase u | feistelMicroHash n_max qOf H i x = feistelMicroHash n_max qOf H i u}
        dsimp only [target, microCollCount] at this ⊢
        omega

/-- If a bucket contains `c_b` items that inject via `keyAt : Fin c_b → Fin U` into the keys of `S`
landing in `u`'s Feistel bucket, then the overflow count `c_b - effBucketCap n_max` is at most
`1 + bucketOvfCount n_max qOf H i S u`. -/
theorem bucketOverflow_le {ι Q : Type*} {U n_max c_b : ℕ}
    (qOf : Fin U → Q) (H : ι → Q → Fin (2 ^ totalMicroBits n_max)) (i : ι)
    (S : Finset (Fin U)) (u : Fin U)
    (keyAt : Fin c_b → Fin U)
    (hinj : Function.Injective keyAt)
    (hmem : ∀ j : Fin c_b, keyAt j ∈ S ∧
      feistelBucketHash n_max qOf H i (keyAt j) = feistelBucketHash n_max qOf H i u) :
    c_b - effBucketCap n_max ≤ 1 + bucketOvfCount n_max qOf H i S u := by
  classical
  let target : Finset (Fin U) :=
    insert u {x ∈ S.erase u |
      feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u}
  have hsub : univ.image keyAt ⊆ target := by
    intro x hx
    rcases mem_image.mp hx with ⟨j, _, rfl⟩
    rcases hmem j with ⟨hjS, hjB⟩
    by_cases hju : keyAt j = u
    · rw [hju]
      exact mem_insert_self u _
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨hju, hjS⟩, hjB⟩)
  have hcb : c_b ≤ 1 +
      #{x ∈ S.erase u | feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u} := by
    calc c_b = #(univ : Finset (Fin c_b)) := by simp
      _ = #(univ.image keyAt) := (card_image_of_injective univ hinj).symm
      _ ≤ #target := card_le_card hsub
      _ ≤ 1 + #{x ∈ S.erase u |
          feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u} := by
        have := card_insert_le u
          {x ∈ S.erase u | feistelBucketHash n_max qOf H i x = feistelBucketHash n_max qOf H i u}
        dsimp only [target] at this ⊢
        omega
  unfold bucketOvfCount
  omega

/-! ## Section 5: Master word-level space accounting (`succinctWords`) -/

/-- **Master succinct word-space bound:** if `n_max ≤ U` and the auxiliary bit budget `B_aux` is at
most `C_aux * n_max * Dynamic.logLogFactor n_max`, then storing `n_max` quotients of
`quotientBits U n_max` bits, `n_max` values of `valBits V` bits, `B_aux` auxiliary bits (with
additive word overhead `C_pad`), and `C_hdr` header/hash words uses at most
`Dynamic.succinctWords (C_aux + 5) (C_pad + C_hdr) U V w n_max` words across all `w`. -/
theorem succinct_space_le_succinctWords {U V w n_max B_aux C_aux C_pad C_hdr : ℕ}
    (hnU : n_max ≤ U)
    (haux : B_aux ≤ C_aux * n_max * Dynamic.logLogFactor n_max) :
    (n_max * quotientBits U n_max + n_max * valBits V + B_aux + w - 1) / w + C_pad + C_hdr ≤
      Dynamic.succinctWords (C_aux + 5) (C_pad + C_hdr) U V w n_max := by
  unfold Dynamic.succinctWords
  have hqv := quotient_val_bits_le_optBits (V := V) hnU
  have hnum :
      n_max * quotientBits U n_max + n_max * valBits V + B_aux + w - 1 ≤
        Dynamic.optBits U V n_max + (C_aux + 5) * n_max * Dynamic.logLogFactor n_max + w - 1 := by
    have hmul : n_max * (quotientBits U n_max + valBits V) =
        n_max * quotientBits U n_max + n_max * valBits V := Nat.left_distrib _ _ _
    have hdist : (C_aux + 5) * n_max * Dynamic.logLogFactor n_max =
        C_aux * n_max * Dynamic.logLogFactor n_max + 5 * n_max * Dynamic.logLogFactor n_max := by
      ring
    omega
  have hdiv :
      (n_max * quotientBits U n_max + n_max * valBits V + B_aux + w - 1) / w ≤
        (Dynamic.optBits U V n_max +
          (C_aux + 5) * n_max * Dynamic.logLogFactor n_max + w - 1) / w :=
    Nat.div_le_div_right hnum
  omega

/-- Total number of `effBucketPosBits n`-bit entries in the local micro-bucket metadata array
`LocalMeta`: for each of the `numBuckets n` buckets, `numMicroPerBucket n` micro-bucket heads plus
`2 * effBucketCap n` doubly-linked list pointers (`next` and `prev`). -/
@[expose]
def localMetaLen (n : ℕ) : ℕ :=
  numBuckets n * (numMicroPerBucket n + 2 * effBucketCap n)

/-- Number of variable per-bucket and per-slab `globalPtrBits n`-bit entries in `GlobalMeta`: `0` in
the single-bucket regime (`bucketBits n = 0`), and `numBuckets n * (3 + dirSlabsPerBucket n +
2 * tailCapPerBucket n) + 4 * maxFullSlabs n` in the multi-bucket slab regime (`0 < bucketBits n`).
-/
@[expose]
def globalMetaVarLen (n : ℕ) : ℕ :=
  if bucketBits n = 0 then 0
  else numBuckets n * (3 + dirSlabsPerBucket n + 2 * tailCapPerBucket n) + 4 * maxFullSlabs n

/-- Total number of `globalPtrBits n`-bit entries in `GlobalMeta`: `4` global header slots (slots
`0` and `1` store `n_slabs` and `n_tails`; slots `2` and `3` are unused) plus `globalMetaVarLen n`.
-/
@[expose]
def globalMetaLen (n : ℕ) : ℕ :=
  4 + globalMetaVarLen n

/-- For every `n : ℕ`, `localMetaLen n * effBucketPosBits n ≤ 54 * n * Dynamic.logLogFactor n`. -/
theorem localMetaLen_mul_effBucketPosBits_le (n : ℕ) :
    localMetaLen n * effBucketPosBits n ≤ 54 * n * Dynamic.logLogFactor n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [effBucketPosBits_zero]
  · have hlen : localMetaLen n ≤ 9 * n := by
      have h1 := totalMicroBuckets_le_self hn
      have h2 := numBuckets_mul_effBucketCap_le_four_mul hn
      have h3 := totalMicroBuckets_eq_mul n
      unfold localMetaLen
      nlinarith
    have hbits := effBucketPosBits_le n
    calc localMetaLen n * effBucketPosBits n
        ≤ (9 * n) * (6 * Dynamic.logLogFactor n) := Nat.mul_le_mul hlen hbits
      _ = 54 * n * Dynamic.logLogFactor n := by ring

/-- For every `n : ℕ`, `globalMetaVarLen n * globalPtrBits n ≤ 18 * n`. -/
theorem globalMetaVarLen_mul_globalPtrBits_le (n : ℕ) :
    globalMetaVarLen n * globalPtrBits n ≤ 18 * n := by
  unfold globalMetaVarLen
  split_ifs with hb
  · simp
  · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
    have h1 := two_mul_numBuckets_mul_globalPtrBits_le_of_pos hb_pos
    have h2 := slabDir_bits_le n
    have h3 : (numBuckets n * tailCapPerBucket n) * globalPtrBits n ≤ 4 * n :=
      maxTailItems_mul_globalPtrBits_le n
    have h4 := maxFullSlabs_mul_globalPtrBits_le n
    have hexpand :
        (numBuckets n * (3 + dirSlabsPerBucket n + 2 * tailCapPerBucket n) + 4 * maxFullSlabs n) *
          globalPtrBits n =
          3 * (numBuckets n * globalPtrBits n) +
          (numBuckets n * dirSlabsPerBucket n) * globalPtrBits n +
          2 * ((numBuckets n * tailCapPerBucket n) * globalPtrBits n) +
          4 * (maxFullSlabs n * globalPtrBits n) := by ring
    rw [hexpand]
    omega

/-- For every `n : ℕ`, `globalMetaLen n * globalPtrBits n ≤ 20 * n * Dynamic.logLogFactor n`. -/
theorem globalMetaLen_mul_globalPtrBits_le (n : ℕ) :
    globalMetaLen n * globalPtrBits n ≤ 20 * n * Dynamic.logLogFactor n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [globalPtrBits_zero]
  · unfold globalMetaLen
    rw [Nat.right_distrib]
    by_cases hb : bucketBits n = 0
    · have hvar : globalMetaVarLen n = 0 := by simp [globalMetaVarLen, hb]
      rw [hvar, Nat.zero_mul, Nat.add_zero]
      have hlog : Nat.log 2 n ≤ 3 * Dynamic.logLogFactor n := by
        unfold bucketBits at hb
        omega
      have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
      have hpow : n + 1 ≤ 2 ^ (3 * Dynamic.logLogFactor n + 1) :=
        (by omega : n + 1 ≤ 2 ^ (Nat.log 2 n + 1)).trans
          (Nat.pow_le_pow_right (by decide) (by omega))
      have hclog : globalPtrBits n ≤ 3 * Dynamic.logLogFactor n + 1 :=
        Nat.clog_le_of_le_pow hpow
      have hll := Dynamic.one_le_logLogFactor n
      have h4 : 4 * globalPtrBits n ≤ 20 * Dynamic.logLogFactor n := by omega
      calc 4 * globalPtrBits n
          ≤ 20 * Dynamic.logLogFactor n := h4
        _ = 20 * 1 * Dynamic.logLogFactor n := by ring
        _ ≤ 20 * n * Dynamic.logLogFactor n := by
          gcongr
          exact hn
    · have hb_pos : 0 < bucketBits n := Nat.pos_of_ne_zero hb
      have hvar := globalMetaVarLen_mul_globalPtrBits_le n
      have hptr := globalPtrBits_le_two_mul_slabScale hb_pos
      have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
      have hscale := two_le_slabScale n
      have hb_num := numBuckets_pos n
      have hsq : 4 ≤ (slabScale n) ^ 2 := by nlinarith
      have h4L : 4 * globalPtrBits n ≤ 2 * n := by
        calc 4 * globalPtrBits n
            ≤ 4 * (2 * slabScale n) := by gcongr
          _ = 2 * (4 * slabScale n) := by ring
          _ ≤ 2 * ((slabScale n) ^ 2 * slabScale n) := by nlinarith
          _ = 2 * (1 * (slabScale n) ^ 3) := by ring
          _ ≤ 2 * (numBuckets n * (slabScale n) ^ 3) := by
            gcongr
            exact hb_num
          _ ≤ 2 * n := Nat.mul_le_mul_left 2 hcube
      have hll := Dynamic.one_le_logLogFactor n
      calc 4 * globalPtrBits n + globalMetaVarLen n * globalPtrBits n
          ≤ 20 * n := by omega
        _ = 20 * n * 1 := by ring
        _ ≤ 20 * n * Dynamic.logLogFactor n := by gcongr

/-- When `0 < bucketBits n`, `globalMetaLen n ≤ n`. -/
theorem globalMetaLen_le_of_bucketBits_pos {n : ℕ} (hb : 0 < bucketBits n) :
    globalMetaLen n ≤ n := by
  have hb0 : bucketBits n ≠ 0 := by omega
  have hll1 := Dynamic.one_le_logLogFactor n
  have hlog4 : 4 ≤ Nat.log 2 n := by
    unfold bucketBits at hb
    omega
  have hclog4 : 4 ≤ Nat.clog 2 (max n 4) :=
    (hlog4.trans (Nat.log_mono_right (le_max_left n 4))).trans (Nat.log_le_clog 2 _)
  have hll2 : 2 ≤ Dynamic.logLogFactor n := by
    unfold Dynamic.logLogFactor
    rw [show (2 : ℕ) = Nat.clog 2 4 by decide]
    exact Nat.clog_mono_right 2 hclog4
  have hlog7 : 7 ≤ Nat.log 2 n := by
    unfold bucketBits at hb
    omega
  have hclog5 : 5 ≤ Nat.clog 2 (max n 4) :=
    ((by omega : 5 ≤ Nat.log 2 n).trans (Nat.log_mono_right (le_max_left n 4))).trans
      (Nat.log_le_clog 2 _)
  have hll3 : 3 ≤ Dynamic.logLogFactor n := by
    unfold Dynamic.logLogFactor
    rw [show (3 : ℕ) = Nat.clog 2 5 by decide]
    exact Nat.clog_mono_right 2 hclog5
  have hS8 : 8 ≤ slabScale n := by
    unfold slabScale
    rw [show (8 : ℕ) = 2 ^ 3 by decide]
    exact Nat.pow_le_pow_right (by decide) hll3
  have hB1 : 1 ≤ numBuckets n := numBuckets_pos n
  have hcube := numBuckets_mul_slabScale_cubed_le hb
  have hK : slabSize n = (slabScale n) ^ 2 := (slabSize_eq_sq_of_pos hb).1
  have hS2_16 : 16 ≤ slabSize n := by
    rw [hK]
    nlinarith
  have hdiv : n / slabSize n ≤ n / 16 :=
    Nat.div_le_div_left hS2_16 (by decide)
  have h5 : 3 + 4 * slabScale n + 2 * (2 * (slabScale n) ^ 2) ≤ 5 * (slabScale n) ^ 2 := by
    nlinarith
  have hm5 :
      numBuckets n * (3 + 4 * slabScale n + 2 * (2 * (slabScale n) ^ 2)) ≤
        5 * (numBuckets n * (slabScale n) ^ 2) := by
    calc numBuckets n * (3 + 4 * slabScale n + 2 * (2 * (slabScale n) ^ 2))
        ≤ numBuckets n * (5 * (slabScale n) ^ 2) := Nat.mul_le_mul_left _ h5
      _ = 5 * (numBuckets n * (slabScale n) ^ 2) := by ring
  have h4le : 4 ≤ numBuckets n * (slabScale n) ^ 2 := by
    calc 4 ≤ 1 * 16 := by decide
      _ ≤ numBuckets n * (slabScale n) ^ 2 := Nat.mul_le_mul hB1 (by nlinarith)
  have h8 : 8 * (numBuckets n * (slabScale n) ^ 2) ≤ n := by
    calc 8 * (numBuckets n * (slabScale n) ^ 2)
        ≤ slabScale n * (numBuckets n * (slabScale n) ^ 2) :=
          Nat.mul_le_mul_right _ hS8
      _ = numBuckets n * (slabScale n) ^ 3 := by ring
      _ ≤ n := hcube
  unfold globalMetaLen globalMetaVarLen dirSlabsPerBucket tailCapPerBucket maxFullSlabs
  rw [ite_eq_right hb0, ite_eq_right hb0, ite_eq_right hb0, ite_eq_right hb0]
  rw [hK] at hdiv ⊢
  omega

/-- **Succinct table word-space bound:** the sum of the word sizes of `Quotients`,
`Values`, the 9 `LocalMeta` sub-arrays of length `totalMicroBuckets n_max`, `GlobalMeta`, and
`C_hdr` header/hash words is at most `Dynamic.succinctWords 79 (35 + C_hdr) U V w n_max` across
all `w`. -/
theorem tableArrays_words_le_succinctWords {U V w n_max C_hdr : ℕ} (hnU : n_max ≤ U) :
    packedWords n_max (quotientBits U n_max) w +
      packedWords n_max (valBits V) w +
      9 * packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w +
      packedWords (globalMetaLen n_max) (globalPtrBits n_max) w + C_hdr ≤
      Dynamic.succinctWords 79 (35 + C_hdr) U V w n_max := by
  have hlm_eq : 9 * totalMicroBuckets n_max = localMetaLen n_max := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]
    ring
  have h12 := packedWords_add_le n_max (quotientBits U n_max) n_max (valBits V) w
  have h123 := div_add_mul_packedWords_le 9
    (n_max * quotientBits U n_max + n_max * valBits V) 5
    (totalMicroBuckets n_max) (effBucketPosBits n_max) w
  rw [hlm_eq] at h123
  have h1234 := div_add_packedWords_le
    (n_max * quotientBits U n_max + n_max * valBits V +
      localMetaLen n_max * effBucketPosBits n_max) 32
    (globalMetaLen n_max) (globalPtrBits n_max) w
  have hlm := localMetaLen_mul_effBucketPosBits_le n_max
  have hgm := globalMetaLen_mul_globalPtrBits_le n_max
  have haux :
      localMetaLen n_max * effBucketPosBits n_max +
        globalMetaLen n_max * globalPtrBits n_max ≤
        74 * n_max * Dynamic.logLogFactor n_max := by
    have hdist : 74 * n_max * Dynamic.logLogFactor n_max =
        54 * n_max * Dynamic.logLogFactor n_max + 20 * n_max * Dynamic.logLogFactor n_max := by
      ring
    omega
  have hmaster :
      (n_max * quotientBits U n_max + n_max * valBits V +
        (localMetaLen n_max * effBucketPosBits n_max +
          globalMetaLen n_max * globalPtrBits n_max) + w - 1) / w + 35 + C_hdr ≤
        Dynamic.succinctWords 79 (35 + C_hdr) U V w n_max :=
    succinct_space_le_succinctWords
      (U := U) (V := V) (w := w) (n_max := n_max)
      (B_aux := localMetaLen n_max * effBucketPosBits n_max +
        globalMetaLen n_max * globalPtrBits n_max)
      (C_aux := 74) (C_pad := 35) (C_hdr := C_hdr) hnU haux
  have hassoc :
      n_max * quotientBits U n_max + n_max * valBits V +
        localMetaLen n_max * effBucketPosBits n_max +
        globalMetaLen n_max * globalPtrBits n_max =
      n_max * quotientBits U n_max + n_max * valBits V +
        (localMetaLen n_max * effBucketPosBits n_max +
          globalMetaLen n_max * globalPtrBits n_max) := by ring
  rw [hassoc] at h1234
  omega

end Cslib.DataStructure.Dictionary.SuccinctBucket
