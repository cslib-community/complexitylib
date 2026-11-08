/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.Dynamic.Spec
public import Complexity.Probability.KWiseIndependent
public import Mathlib.Data.LawfulXor.Equiv
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Nat.Choose
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# One-round Feistel quotienting and universal succinct bit accounting

This file formalizes the one-round Feistel permutation used for quotienting keys in succinct hash
tables ([Arbitman, Naor and Segev, FOCS 2010, Claim 5.7][ArbitmanNaorSegev2010];
[Bender, Conway, Farach-Colton, Kuszmaul and Tagliavini, *J. ACM* 2023, Section 7, arXiv
pp. 31–33][BenderConwayFarachColtonKuszmaulTagliavini2023]) together with the universal
bit-accounting inequality comparing quotient + value storage against the information-theoretic
optimum `Dynamic.optBits U V n = ⌈log₂ C(U, n)⌉ + n * ⌈log₂ V⌉` across all `0 ≤ n ≤ U`.

Given a universe bound `U`, capacity `n ≤ U`, and bucket bit-width
`b = bucketBits n = ⌊log₂ n⌋ - 3 * logLogFactor n`:
1. Every key `u < U` has `keyBits U = ⌈log₂ U⌉` bits and splits into a low `b`-bit part
   `keyLow b u = u % 2^b` and a high `(keyBits U - b)`-bit quotient `keyQuotient b u = u / 2^b`.
2. Given a hash function `h1 : ℕ → ℕ`, key `u` maps to bucket
   `feistelBucket b h1 u = (h1 (keyQuotient b u) % 2^b) ^^^ keyLow b u < 2^b`
   and stores only `keyQuotient b u < 2^(quotientBits U n)`.
3. From `(bucket, keyQuotient b u)`, `feistelReconstruct b h1 bucket (keyQuotient b u)` recovers
   `u` uniquely (`feistelReconstruct_feistelBucket`). Consequently, distinct keys sharing the same
   quotient always map to distinct Feistel buckets (`feistelBucket_ne_of_keyQuotient_eq_of_ne`).
4. Across all `0 ≤ n ≤ U`, storing `n` quotients of `quotientBits U n` bits and `n` values of
   `valBits V = ⌈log₂ V⌉` bits uses at most
   `Dynamic.optBits U V n + 5 * n * Dynamic.logLogFactor n` bits (`quotient_val_bits_le_optBits`).

## Main definitions

* `Cslib.DataStructure.Dictionary.FeistelQuotient.keyBits`, `valBits`, `slabScale`, `bucketBits`,
  `numBuckets`, `quotientBits`: bit-width and bucket/slab parameters.
* `Cslib.DataStructure.Dictionary.FeistelQuotient.keyLow`, `keyQuotient`, `feistelBucket`,
  `feistelReconstruct`, `feistelXor`: one-round Feistel bucket assignment and key reconstruction.

## Main results

* `bucketBits_le_keyBits`, `quotientBits_add_bucketBits`: `bucketBits n ≤ keyBits U` and
  `quotientBits U n + bucketBits n = keyBits U` for all `n ≤ U`.
* `feistelReconstruct_feistelBucket`, `eq_of_feistelBucket_eq_of_keyQuotient_eq`,
  `feistelBucket_ne_of_keyQuotient_eq_of_ne`: exact invertibility of Feistel quotienting.
* `pow_le_pow_mul_choose`: `U ^ n ≤ n ^ n * U.choose n` for all `n ≤ U`.
* `quotient_bits_le_choose`, `quotient_val_bits_le_optBits`: universal succinct bit accounting
  valid for all `0 ≤ n ≤ U`.
* `expect_card_feistelXor_eq_on`, `expect_feistelXor_mul_sub_one_le_on`,
  `expect_feistelXor_overflow_le_on`: pairwise and 3-wise independence bounds for Feistel bucket and
  micro-chain collisions and bucket overflow.

## References

* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*, Claim 5.7][ArbitmanNaorSegev2010]
* [M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, *Iceberg Hashing:
  Optimizing Many Hash-Table Criteria at Once*,
  Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]
-/

public section

namespace Cslib.DataStructure.Dictionary.FeistelQuotient

open Cslib.DataStructure.Dictionary

/-! ## Section 1: Bit-width parameters and bucket/slab scales -/

/-- Number of bits `⌈log₂ U⌉` needed to represent keys in `Fin U`. -/
@[expose]
def keyBits (U : ℕ) : ℕ :=
  Nat.clog 2 U

/-- Number of bits `⌈log₂ V⌉` needed to represent values in `Fin V`. -/
@[expose]
def valBits (V : ℕ) : ℕ :=
  Nat.clog 2 V

/-- Poly-logarithmic scale parameter `L = 2^(logLogFactor n) ≥ 2`, satisfying
`log₂ n ≤ L ≤ 2 * ⌈log₂ (max n 4)⌉`. -/
@[expose]
def slabScale (n : ℕ) : ℕ :=
  2 ^ Dynamic.logLogFactor n

/-- Number of bucket index bits `b = ⌊log₂ n⌋ - 3 * logLogFactor n`. -/
@[expose]
def bucketBits (n : ℕ) : ℕ :=
  Nat.log 2 n - 3 * Dynamic.logLogFactor n

/-- Number of Feistel buckets `M = 2^(bucketBits n)`. -/
@[expose]
def numBuckets (n : ℕ) : ℕ :=
  2 ^ bucketBits n

/-- Number of stored quotient bits per key `q_bits = ⌈log₂ U⌉ - bucketBits n`. -/
@[expose]
def quotientBits (U n : ℕ) : ℕ :=
  keyBits U - bucketBits n

/-- `slabScale n` is always at least `2`. -/
theorem two_le_slabScale (n : ℕ) : 2 ≤ slabScale n := by
  unfold slabScale
  calc 2 = 2 ^ 1 := by decide
    _ ≤ 2 ^ Dynamic.logLogFactor n :=
      Nat.pow_le_pow_right (by decide) (Dynamic.one_le_logLogFactor n)

/-- `slabScale n` is always positive. -/
theorem slabScale_pos (n : ℕ) : 0 < slabScale n := by
  have := two_le_slabScale n
  omega

/-- `numBuckets n` is always positive. -/
theorem numBuckets_pos (n : ℕ) : 0 < numBuckets n := by
  unfold numBuckets
  positivity

/-- Whenever `n ≤ U`, the bucket bit-width `bucketBits n` is at most `keyBits U`. -/
theorem bucketBits_le_keyBits {U n : ℕ} (hnU : n ≤ U) :
    bucketBits n ≤ keyBits U := by
  unfold bucketBits keyBits
  have h1 : Nat.log 2 n - 3 * Dynamic.logLogFactor n ≤ Nat.log 2 n := Nat.sub_le _ _
  have h2 : Nat.log 2 n ≤ Nat.log 2 U := Nat.log_mono_right hnU
  have h3 : Nat.log 2 U ≤ Nat.clog 2 U := Nat.log_le_clog 2 U
  omega

/-- Whenever `n ≤ U`, `quotientBits U n + bucketBits n = keyBits U`. -/
theorem quotientBits_add_bucketBits {U n : ℕ} (hnU : n ≤ U) :
    quotientBits U n + bucketBits n = keyBits U :=
  Nat.sub_add_cancel (bucketBits_le_keyBits hnU)

/-- If `U ≤ 2 ^ w`, then `quotientBits U n ≤ w`. -/
theorem quotientBits_le_of_le_pow {U w n : ℕ} (hU : U ≤ 2 ^ w) :
    quotientBits U n ≤ w :=
  (Nat.sub_le _ _).trans (Nat.clog_le_of_le_pow hU)

/-- For every `n`, `n ≤ 2 ^ (bucketBits n + 3 * Dynamic.logLogFactor n + 1)`. -/
theorem le_two_pow_bucketBits_add (n : ℕ) :
    n ≤ 2 ^ (bucketBits n + 3 * Dynamic.logLogFactor n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
    have hle : Nat.log 2 n + 1 ≤ bucketBits n + 3 * Dynamic.logLogFactor n + 1 := by
      unfold bucketBits
      omega
    exact hlt.le.trans (Nat.pow_le_pow_right (by decide) hle)

/-- For every `n`, `n ≤ 2 * numBuckets n * (slabScale n) ^ 3`. -/
theorem le_two_mul_numBuckets_mul_slabScale_cubed (n : ℕ) :
    n ≤ 2 * numBuckets n * (slabScale n) ^ 3 := by
  have h := le_two_pow_bucketBits_add n
  have heq : 2 ^ (bucketBits n + 3 * Dynamic.logLogFactor n + 1) =
      2 * numBuckets n * (slabScale n) ^ 3 := by
    unfold numBuckets slabScale
    rw [← Nat.pow_mul, Nat.mul_comm (Dynamic.logLogFactor n) 3, Nat.pow_add, Nat.pow_add,
      Nat.pow_one]
    ring
  omega

/-! ## Section 2: One-round Feistel quotienting and exact key reconstruction -/

/-- The low `b` bits `u % 2^b` of a key `u`. -/
@[expose]
def keyLow (b u : ℕ) : ℕ :=
  u % (2 ^ b)

/-- The quotient `u / 2^b` obtained by dropping the low `b` bits of `u`. -/
@[expose]
def keyQuotient (b u : ℕ) : ℕ :=
  u / (2 ^ b)

/-- One-round Feistel bucket index `(h1 (keyQuotient b u) % 2^b) ^^^ keyLow b u < 2^b`. -/
@[expose]
def feistelBucket (b : ℕ) (h1 : ℕ → ℕ) (u : ℕ) : ℕ :=
  (h1 (keyQuotient b u) % (2 ^ b)) ^^^ keyLow b u

/-- Inverse reconstruction of key `u` from its Feistel bucket index `bucket` and stored quotient
`q = keyQuotient b u`. -/
@[expose]
def feistelReconstruct (b : ℕ) (h1 : ℕ → ℕ) (bucket q : ℕ) : ℕ :=
  q * (2 ^ b) + ((h1 q % (2 ^ b)) ^^^ (bucket % (2 ^ b)))

/-- `keyLow b u` is strictly less than `2 ^ b`. -/
theorem keyLow_lt (b u : ℕ) : keyLow b u < 2 ^ b :=
  Nat.mod_lt u (by positivity)

/-- `feistelBucket b h1 u` is strictly less than `2 ^ b`. -/
theorem feistelBucket_lt (b : ℕ) (h1 : ℕ → ℕ) (u : ℕ) :
    feistelBucket b h1 u < 2 ^ b := by
  unfold feistelBucket
  exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (keyLow_lt b u)

/-- Whenever `n ≤ U` and `u < U`, the quotient `keyQuotient (bucketBits n) u` fits in
`quotientBits U n` bits (`< 2 ^ (quotientBits U n)`). -/
theorem keyQuotient_lt_two_pow_quotientBits {U n u : ℕ} (hnU : n ≤ U) (hu : u < U) :
    keyQuotient (bucketBits n) u < 2 ^ quotientBits U n := by
  unfold keyQuotient
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, quotientBits_add_bucketBits hnU]
  exact hu.trans_le (Nat.le_pow_clog (by decide) U)

/-- Reconstructing from `feistelBucket b h1 u` and `keyQuotient b u` recovers `u` exactly. -/
@[simp]
theorem feistelReconstruct_feistelBucket (b : ℕ) (h1 : ℕ → ℕ) (u : ℕ) :
    feistelReconstruct b h1 (feistelBucket b h1 u) (keyQuotient b u) = u := by
  unfold feistelReconstruct
  rw [Nat.mod_eq_of_lt (feistelBucket_lt b h1 u)]
  unfold feistelBucket keyQuotient keyLow
  have hxor :
      (h1 (u / 2 ^ b) % 2 ^ b) ^^^ ((h1 (u / 2 ^ b) % 2 ^ b) ^^^ (u % 2 ^ b)) = u % 2 ^ b := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hxor, Nat.div_add_mod']

/-- Reconstructing any `(bucket, q)` with `bucket < 2 ^ b` produces a key whose Feistel bucket is
`bucket` and whose quotient is `q`. -/
theorem feistelBucket_feistelReconstruct {b : ℕ} (h1 : ℕ → ℕ) {bucket : ℕ} (hb : bucket < 2 ^ b)
    (q : ℕ) :
    feistelBucket b h1 (feistelReconstruct b h1 bucket q) = bucket ∧
      keyQuotient b (feistelReconstruct b h1 bucket q) = q := by
  unfold feistelReconstruct
  rw [Nat.mod_eq_of_lt hb]
  set r := (h1 q % 2 ^ b) ^^^ bucket
  have hr : r < 2 ^ b := Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hb
  have hq : (q * 2 ^ b + r) / 2 ^ b = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hr, Nat.zero_add]
  have hlow : (q * 2 ^ b + r) % 2 ^ b = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  refine ⟨?_, hq⟩
  unfold feistelBucket keyQuotient keyLow
  rw [hq, hlow]
  dsimp only [r]
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Two keys landing in the same Feistel bucket with the same quotient are equal. -/
theorem eq_of_feistelBucket_eq_of_keyQuotient_eq {b : ℕ} {h1 : ℕ → ℕ} {u₁ u₂ : ℕ}
    (hb : feistelBucket b h1 u₁ = feistelBucket b h1 u₂)
    (hq : keyQuotient b u₁ = keyQuotient b u₂) :
    u₁ = u₂ := by
  calc u₁ = feistelReconstruct b h1 (feistelBucket b h1 u₁) (keyQuotient b u₁) :=
        (feistelReconstruct_feistelBucket b h1 u₁).symm
    _ = feistelReconstruct b h1 (feistelBucket b h1 u₂) (keyQuotient b u₂) := by rw [hb, hq]
    _ = u₂ := feistelReconstruct_feistelBucket b h1 u₂

/-- Two distinct keys that share the same quotient `keyQuotient b u₁ = keyQuotient b u₂` always map
to distinct Feistel buckets for every hash function `h1`. -/
theorem feistelBucket_ne_of_keyQuotient_eq_of_ne {b : ℕ} {h1 : ℕ → ℕ} {u₁ u₂ : ℕ}
    (hq : keyQuotient b u₁ = keyQuotient b u₂) (hne : u₁ ≠ u₂) :
    feistelBucket b h1 u₁ ≠ feistelBucket b h1 u₂ :=
  fun hb => hne (eq_of_feistelBucket_eq_of_keyQuotient_eq hb hq)

/-! ## Section 3: Universal quotienting bit accounting against `Dynamic.optBits` -/

/-- For all `n ≤ U`, `U ^ n ≤ n ^ n * U.choose n`. -/
theorem pow_le_pow_mul_choose {U n : ℕ} (hnU : n ≤ U) :
    U ^ n ≤ n ^ n * U.choose n := by
  simpa [Nat.choose_self, Nat.mul_comm] using Nat.choose_mul_pow_le hnU n

/-- Universal quotient bit bound: for every `n ≤ U`, storing `n` quotients of `quotientBits U n`
bits uses at most `⌈log₂ C(U, n)⌉ + 5 * n * Dynamic.logLogFactor n` bits. -/
theorem quotient_bits_le_choose {U n : ℕ} (hnU : n ≤ U) :
    n * quotientBits U n ≤
      Nat.clog 2 (U.choose n) + 5 * n * Dynamic.logLogFactor n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hU : 1 ≤ U := hn.trans_le hnU
    have hpow_key : 2 ^ keyBits U ≤ 2 * U := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
    have hpow_n : n ≤ 2 ^ (bucketBits n + 3 * Dynamic.logLogFactor n + 1) :=
      le_two_pow_bucketBits_add n
    have hchoose : U.choose n ≤ 2 ^ Nat.clog 2 (U.choose n) :=
      Nat.le_pow_clog (by decide) (U.choose n)
    have hmain :
        2 ^ (n * keyBits U) ≤
          2 ^ (n + n * (bucketBits n + 3 * Dynamic.logLogFactor n + 1) +
            Nat.clog 2 (U.choose n)) := by
      calc 2 ^ (n * keyBits U)
          = (2 ^ keyBits U) ^ n := by rw [Nat.mul_comm, Nat.pow_mul]
        _ ≤ (2 * U) ^ n := Nat.pow_le_pow_left hpow_key n
        _ = 2 ^ n * U ^ n := Nat.mul_pow 2 U n
        _ ≤ 2 ^ n * (n ^ n * U.choose n) :=
            Nat.mul_le_mul_left (2 ^ n) (pow_le_pow_mul_choose hnU)
        _ ≤ 2 ^ n * ((2 ^ (bucketBits n + 3 * Dynamic.logLogFactor n + 1)) ^ n *
              2 ^ Nat.clog 2 (U.choose n)) :=
            Nat.mul_le_mul_left (2 ^ n)
              (Nat.mul_le_mul (Nat.pow_le_pow_left hpow_n n) hchoose)
        _ = 2 ^ (n + n * (bucketBits n + 3 * Dynamic.logLogFactor n + 1) +
              Nat.clog 2 (U.choose n)) := by
            rw [← Nat.pow_mul, Nat.mul_comm (bucketBits n + 3 * Dynamic.logLogFactor n + 1) n,
              ← Nat.pow_add, ← Nat.pow_add, ← Nat.add_assoc]
    have hexp :
        n * keyBits U ≤
          n + n * (bucketBits n + 3 * Dynamic.logLogFactor n + 1) +
            Nat.clog 2 (U.choose n) :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmain
    have hsplit : keyBits U = quotientBits U n + bucketBits n :=
      (quotientBits_add_bucketBits hnU).symm
    have hll : 1 ≤ Dynamic.logLogFactor n := Dynamic.one_le_logLogFactor n
    rw [hsplit, Nat.mul_add] at hexp
    nlinarith

/-- Universal quotient + value bit bound: for every `n ≤ U` and `V`, storing `n` quotients of
`quotientBits U n` bits and `n` values of `valBits V = ⌈log₂ V⌉` bits uses at most
`Dynamic.optBits U V n + 5 * n * Dynamic.logLogFactor n` bits. -/
theorem quotient_val_bits_le_optBits {U V n : ℕ} (hnU : n ≤ U) :
    n * (quotientBits U n + valBits V) ≤
      Dynamic.optBits U V n + 5 * n * Dynamic.logLogFactor n := by
  have hq := quotient_bits_le_choose hnU
  unfold Dynamic.optBits valBits
  linarith

/-! ## Section 4: Pairwise and 3-wise independence bounds for Feistel buckets and micro-chains -/

section ProbabilityBounds

open Cslib.Probability Finset
open scoped BigOperators

variable {ι Q : Type*} [Fintype ι]

/-- Typed Feistel XOR map sending key `u : Fin U` to
`⟨(H i (qOf u)).val ^^^ keyLow b u.val, ...⟩ : Fin (2 ^ m)` whenever `b ≤ m`.
When `m = b`, this is the Feistel bucket index in `Fin (2 ^ b)`; when `m = b + p`, its low `b`
bits give the Feistel bucket index and its high `p` bits give the per-bucket micro-chain index. -/
@[expose]
def feistelXor {U : ℕ} (b m : ℕ) (hbm : b ≤ m) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ m)) (i : ι) (u : Fin U) : Fin (2 ^ m) :=
  ⟨(H i (qOf u)).val ^^^ keyLow b u.val,
    Nat.xor_lt_two_pow (H i (qOf u)).isLt
      ((keyLow_lt b u.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))⟩

omit [Fintype ι] in
/-- Two distinct keys sharing the same `qOf` value and the same `keyQuotient b` value never collide
under `feistelXor`, for any seed `i`. -/
theorem feistelXor_ne_of_qOf_eq_pt {U b m : ℕ} (hbm : b ≤ m) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ m)) (i : ι) {u₁ u₂ : Fin U}
    (hquot : keyQuotient b u₁.val = keyQuotient b u₂.val)
    (hne : u₁ ≠ u₂) (hqq : qOf u₁ = qOf u₂) :
    feistelXor b m hbm qOf H i u₁ ≠ feistelXor b m hbm qOf H i u₂ := by
  intro heq
  have hval : (H i (qOf u₁)).val ^^^ keyLow b u₁.val =
      (H i (qOf u₂)).val ^^^ keyLow b u₂.val := congrArg Fin.val heq
  rw [hqq] at hval
  have hlow : keyLow b u₁.val = keyLow b u₂.val := by
    have h1 := congrArg ((H i (qOf u₂)).val ^^^ ·) hval
    rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, ← Nat.xor_assoc, Nat.xor_self,
      Nat.zero_xor] at h1
  have hu : u₁.val = u₂.val := by
    calc u₁.val = 2 ^ b * keyQuotient b u₁.val + keyLow b u₁.val :=
          (Nat.div_add_mod u₁.val (2 ^ b)).symm
      _ = 2 ^ b * keyQuotient b u₂.val + keyLow b u₂.val := by rw [hquot, hlow]
      _ = u₂.val := Nat.div_add_mod u₂.val (2 ^ b)
  exact hne (Fin.ext hu)

omit [Fintype ι] in
/-- Two `feistelXor` values are equal iff `H i (qOf u₁)` equals `Equiv.xor Δ (H i (qOf u₂))`. -/
theorem feistelXor_eq_iff {U b m : ℕ} (hbm : b ≤ m) (qOf : Fin U → Q)
    (H : ι → Q → Fin (2 ^ m)) (i : ι) (u₁ u₂ : Fin U) :
    feistelXor b m hbm qOf H i u₁ = feistelXor b m hbm qOf H i u₂ ↔
      H i (qOf u₁) =
        Equiv.xor ⟨keyLow b u₂.val ^^^ keyLow b u₁.val,
          Nat.xor_lt_two_pow
            ((keyLow_lt b u₂.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))
            ((keyLow_lt b u₁.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))⟩
          (H i (qOf u₂)) := by
  simp only [feistelXor, Equiv.xor_apply, Fin.ext_iff]
  change (H i (qOf u₁)).val ^^^ keyLow b u₁.val = (H i (qOf u₂)).val ^^^ keyLow b u₂.val ↔
    (H i (qOf u₁)).val =
      ((keyLow b u₂.val ^^^ keyLow b u₁.val) ^^^ (H i (qOf u₂)).val) % 2 ^ m
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow
      ((keyLow_lt b u₂.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))
      ((keyLow_lt b u₁.val).trans_le (Nat.pow_le_pow_right (by decide) hbm)))
    (H i (qOf u₂)).isLt), Nat.xor_comm _ (H i (qOf u₂)).val]
  constructor
  · intro h
    have h1 := congrArg (· ^^^ keyLow b u₁.val) h
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.xor_assoc] at h1
  · intro h
    rw [h, Nat.xor_assoc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- For a pairwise independent hash family `H` and distinct quotients `q₁ ≠ q₂`, the probability
that `H i q₁ = e (H i q₂)` is `1 / |Y|`. -/
theorem expect_boole_apply_eq_equiv {Y 𝕜 : Type*} [Fintype Y] [DecidableEq Y]
    [Semifield 𝕜] [CharZero 𝕜] {H : ι → Q → Y} (hh : IsPairwiseIndependentHash H)
    {q₁ q₂ : Q} (hne : q₁ ≠ q₂) (e : Y ≃ Y) :
    𝔼 i, (if H i q₁ = e (H i q₂) then (1 : 𝕜) else 0) = (Fintype.card Y : 𝕜)⁻¹ := by
  have hsplit (i : ι) :
      (if H i q₁ = e (H i q₂) then (1 : 𝕜) else 0) =
        ∑ y : Y, if H i q₁ = e y ∧ H i q₂ = y then 1 else 0 := by
    have h1 : (∑ y : Y, if H i q₁ = e y ∧ H i q₂ = y then (1 : 𝕜) else 0) =
        ∑ y : Y, if H i q₂ = y then (if H i q₁ = e y then 1 else 0) else 0 := by
      refine Fintype.sum_congr _ _ fun y => ?_
      by_cases hy : H i q₂ = y <;> simp [hy]
    rw [h1, Fintype.sum_ite_eq]
  simp only [hsplit]
  rw [expect_sum_comm]
  have hterm (y : Y) :
      𝔼 i, (if H i q₁ = e y ∧ H i q₂ = y then (1 : 𝕜) else 0) =
        ((Fintype.card Y : 𝕜) ^ 2)⁻¹ := by
    rw [Fintype.expect_boole, hh.dens_filter_apply_eq_and_apply_eq hne (e y) y,
      NNRat.cast_inv, NNRat.cast_pow, NNRat.cast_natCast]
  simp only [hterm, sum_const, card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · simp [h0]
  · have hne_zero : (Fintype.card Y : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne_zero, one_mul]

/-- Under a pairwise independent hash `H : ι → Q → Fin (2 ^ m)`, for any `S : Finset (Fin U)` and
`u : Fin U` such that `qOf` is quotient-injective on `insert u (S.erase u)`, the expected number of
keys `x ∈ S.erase u` colliding with `u` under `feistelXor` is
`#({x ∈ S.erase u | qOf x ≠ qOf u}) / 2 ^ m`. -/
theorem expect_card_feistelXor_eq_on [DecidableEq Q] {U b m : ℕ} {𝕜 : Type*}
    [Semifield 𝕜] [CharZero 𝕜]
    (hbm : b ≤ m) {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ m)} (hh : IsPairwiseIndependentHash H)
    (S : Finset (Fin U)) (u : Fin U)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ → keyQuotient b u₁.val = keyQuotient b u₂.val) :
    𝔼 i, (#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : 𝕜) =
      (#{x ∈ S.erase u | qOf x ≠ qOf u} : 𝕜) / (2 ^ m : 𝕜) := by
  let S' : Finset (Fin U) := {x ∈ S.erase u | qOf x ≠ qOf u}
  have hfilter (i : ι) :
      {x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} =
        {x ∈ S' | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} := by
    ext x
    simp only [S', mem_filter, mem_erase]
    refine ⟨fun ⟨⟨hne, hxS⟩, hcoll⟩ => ⟨⟨⟨hne, hxS⟩, ?_⟩, hcoll⟩,
      fun ⟨⟨h1, _⟩, hcoll⟩ => ⟨h1, hcoll⟩⟩
    intro hqq
    have hx_mem : x ∈ insert u (S.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨hne, hxS⟩)
    have hu_mem : u ∈ insert u (S.erase u) := mem_insert_self u (S.erase u)
    exact feistelXor_ne_of_qOf_eq_pt hbm qOf H i (hq x hx_mem u hu_mem hqq) hne hqq hcoll
  have hcard (i : ι) :
      (#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : 𝕜) =
        ∑ x ∈ S',
          if feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u then (1 : 𝕜) else 0 := by
    rw [hfilter i, card_filter, Nat.cast_sum]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  simp only [hcard]
  rw [expect_sum_comm]
  have hterm : ∀ x ∈ S',
      𝔼 i, (if feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u then (1 : 𝕜) else 0) =
        ((2 ^ m : ℕ) : 𝕜)⁻¹ := by
    intro x hx
    have hqne : qOf x ≠ qOf u := (mem_filter.mp hx).2
    let e : Fin (2 ^ m) ≃ Fin (2 ^ m) :=
      Equiv.xor ⟨keyLow b u.val ^^^ keyLow b x.val,
        Nat.xor_lt_two_pow
          ((keyLow_lt b u.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))
          ((keyLow_lt b x.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))⟩
    have hiff (i : ι) :
        (feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u) ↔
          H i (qOf x) = e (H i (qOf u)) :=
      feistelXor_eq_iff hbm qOf H i x u
    simp only [hiff]
    have h1 := expect_boole_apply_eq_equiv (𝕜 := 𝕜) hh hqne e
    simpa [Fintype.card_fin] using h1
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- Under a 3-wise independent hash family `H`, the values at three pairwise distinct inputs
`q, q₁, q₂` are mutually independent and uniform. -/
theorem dens_filter_apply_eq_three {Y : Type*} [Fintype Y] [DecidableEq Y]
    {H : ι → Q → Y} (hh : IsKWiseIndependentHash 3 H)
    {q q₁ q₂ : Q} (hq₁ : q₁ ≠ q) (hq₂ : q₂ ≠ q) (h12 : q₁ ≠ q₂)
    (y y₁ y₂ : Y) :
    dens {i | H i q = y ∧ H i q₁ = y₁ ∧ H i q₂ = y₂} = ((Fintype.card Y : ℚ≥0) ^ 3)⁻¹ := by
  classical
  let T : Finset Q := insert q {q₁, q₂}
  have hq_notMem : q ∉ ({q₁, q₂} : Finset Q) := by
    simp [hq₁.symm, hq₂.symm]
  have hcard : #T = 3 := by
    dsimp only [T]
    rw [card_insert_of_notMem hq_notMem, card_pair h12]
  have h3 := hh.dens_filter_restrict_eq (T := T) (by omega)
    fun z => if z.1 = q then y else if z.1 = q₁ then y₁ else y₂
  rw [hcard] at h3
  rw [← h3]
  congr 1
  ext i
  simp only [T, mem_filter, mem_univ, true_and, funext_iff, Subtype.forall, mem_insert,
    mem_singleton, restrict]
  constructor
  · rintro ⟨hy, hy₁, hy₂⟩ z (rfl | rfl | rfl)
    · simp [hy]
    · simp [hq₁, hy₁]
    · simp [hq₂, h12.symm, hy₂]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h q (Or.inl rfl)
    · simpa [hq₁] using h q₁ (Or.inr (Or.inl rfl))
    · simpa [hq₂, h12.symm] using h q₂ (Or.inr (Or.inr rfl))

/-- Under a 3-wise independent hash family `H` and pairwise distinct `q, q₁, q₂`, the probability
that `H i q₁ = e₁ (H i q)` and `H i q₂ = e₂ (H i q)` is `1 / |Y|²`. -/
theorem expect_boole_apply_eq_equiv_two {Y 𝕜 : Type*} [Fintype Y] [DecidableEq Y]
    [Semifield 𝕜] [CharZero 𝕜] {H : ι → Q → Y} (hh : IsKWiseIndependentHash 3 H)
    {q q₁ q₂ : Q} (hq₁ : q₁ ≠ q) (hq₂ : q₂ ≠ q) (h12 : q₁ ≠ q₂)
    (e₁ e₂ : Y ≃ Y) :
    𝔼 i, (if H i q₁ = e₁ (H i q) ∧ H i q₂ = e₂ (H i q) then (1 : 𝕜) else 0) =
      ((Fintype.card Y : 𝕜) ^ 2)⁻¹ := by
  have hsplit (i : ι) :
      (if H i q₁ = e₁ (H i q) ∧ H i q₂ = e₂ (H i q) then (1 : 𝕜) else 0) =
        ∑ y : Y, if H i q = y ∧ H i q₁ = e₁ y ∧ H i q₂ = e₂ y then 1 else 0 := by
    have h1 : (∑ y : Y, if H i q = y ∧ H i q₁ = e₁ y ∧ H i q₂ = e₂ y then (1 : 𝕜) else 0) =
        ∑ y : Y, if H i q = y then (if H i q₁ = e₁ y ∧ H i q₂ = e₂ y then 1 else 0) else 0 := by
      refine Fintype.sum_congr _ _ fun y => ?_
      by_cases hy : H i q = y <;> simp [hy]
    rw [h1, Fintype.sum_ite_eq]
  simp only [hsplit]
  rw [expect_sum_comm]
  have hterm (y : Y) :
      𝔼 i, (if H i q = y ∧ H i q₁ = e₁ y ∧ H i q₂ = e₂ y then (1 : 𝕜) else 0) =
        ((Fintype.card Y : 𝕜) ^ 3)⁻¹ := by
    rw [Fintype.expect_boole, dens_filter_apply_eq_three hh hq₁ hq₂ h12 y (e₁ y) (e₂ y),
      NNRat.cast_inv, NNRat.cast_pow, NNRat.cast_natCast]
  simp only [hterm, sum_const, card_univ, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · simp [h0]
  · have hne_zero : (Fintype.card Y : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    have hpow : (Fintype.card Y : 𝕜) ^ 3 = (Fintype.card Y : 𝕜) * (Fintype.card Y : 𝕜) ^ 2 := by
      ring
    rw [hpow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne_zero, one_mul]

/-- Under a 3-wise independent hash `H : ι → Q → Fin (2 ^ m)`, when `qOf` is quotient-injective on
`insert u (S.erase u)`, the second factorial moment of the number of keys in `S.erase u` colliding
with `u` under `feistelXor` is at most `(#({x ∈ S.erase u | qOf x ≠ qOf u}) / 2 ^ m) ^ 2`. -/
theorem expect_feistelXor_mul_sub_one_le_on [DecidableEq Q] {U b m : ℕ}
    (hbm : b ≤ m) {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ m)} (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ → keyQuotient b u₁.val = keyQuotient b u₂.val) :
    𝔼 i,
      ((#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : ℚ) *
        ((#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : ℚ) -
          1)) ≤
      ((#{x ∈ S.erase u | qOf x ≠ qOf u} : ℚ) / (2 ^ m : ℚ)) ^ 2 := by
  let S' : Finset (Fin U) := {x ∈ S.erase u | qOf x ≠ qOf u}
  have hfilter (i : ι) :
      {x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} =
        {x ∈ S' | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} := by
    ext x
    simp only [S', mem_filter, mem_erase]
    refine ⟨fun ⟨⟨hne, hxS⟩, hcoll⟩ => ⟨⟨⟨hne, hxS⟩, ?_⟩, hcoll⟩,
      fun ⟨⟨h1, _⟩, hcoll⟩ => ⟨h1, hcoll⟩⟩
    intro hqq
    have hx_mem : x ∈ insert u (S.erase u) := mem_insert_of_mem (mem_erase.mpr ⟨hne, hxS⟩)
    have hu_mem : u ∈ insert u (S.erase u) := mem_insert_self u (S.erase u)
    exact feistelXor_ne_of_qOf_eq_pt hbm qOf H i (hq x hx_mem u hu_mem hqq) hne hqq hcoll
  have hcell (i : ι) :
      ((#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : ℚ) *
        ((#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} : ℚ) -
          1)) =
        ∑ p ∈ S'.offDiag,
          if feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
              feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u
          then (1 : ℚ) else 0 := by
    rw [hfilter i]
    have hoff : {x ∈ S' | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u}.offDiag =
        {p ∈ S'.offDiag |
          feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
            feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u} := by
      ext p
      simp only [mem_offDiag, mem_filter]
      tauto
    rw [sum_boole, ← hoff, offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  simp only [hcell]
  rw [expect_sum_comm]
  have hpair : ∀ p ∈ S'.offDiag,
      𝔼 i, (if feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
          feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u then (1 : ℚ) else 0) ≤
        (((2 ^ m : ℕ) : ℚ) ^ 2)⁻¹ := by
    intro p hp
    rcases mem_offDiag.mp hp with ⟨hp1, hp2, hne12⟩
    have hq1 : qOf p.1 ≠ qOf u := (mem_filter.mp hp1).2
    have hq2 : qOf p.2 ≠ qOf u := (mem_filter.mp hp2).2
    by_cases hqq : qOf p.1 = qOf p.2
    · have hzero (i : ι) :
          (if feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
              feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u then (1 : ℚ) else 0) =
            0 := by
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        have hp1_mem : p.1 ∈ insert u (S.erase u) := mem_insert_of_mem (mem_filter.mp hp1).1
        have hp2_mem : p.2 ∈ insert u (S.erase u) := mem_insert_of_mem (mem_filter.mp hp2).1
        exact feistelXor_ne_of_qOf_eq_pt hbm qOf H i
          (hq p.1 hp1_mem p.2 hp2_mem hqq) hne12 hqq (h1.trans h2.symm)
      simp only [hzero]
      have hexp0 : (𝔼 _i : ι, (0 : ℚ)) = 0 := by simp
      rw [hexp0]
      positivity
    · let e₁ : Fin (2 ^ m) ≃ Fin (2 ^ m) :=
        Equiv.xor ⟨keyLow b u.val ^^^ keyLow b p.1.val,
          Nat.xor_lt_two_pow
            ((keyLow_lt b u.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))
            ((keyLow_lt b p.1.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))⟩
      let e₂ : Fin (2 ^ m) ≃ Fin (2 ^ m) :=
        Equiv.xor ⟨keyLow b u.val ^^^ keyLow b p.2.val,
          Nat.xor_lt_two_pow
            ((keyLow_lt b u.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))
            ((keyLow_lt b p.2.val).trans_le (Nat.pow_le_pow_right (by decide) hbm))⟩
      have hiff (i : ι) :
          (feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
              feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u) ↔
            (H i (qOf p.1) = e₁ (H i (qOf u)) ∧ H i (qOf p.2) = e₂ (H i (qOf u))) :=
        and_congr (feistelXor_eq_iff hbm qOf H i p.1 u) (feistelXor_eq_iff hbm qOf H i p.2 u)
      simp only [hiff]
      have heq := expect_boole_apply_eq_equiv_two (𝕜 := ℚ) hh hq1 hq2 hqq e₁ e₂
      rw [Fintype.card_fin] at heq
      exact heq.le
  calc ∑ p ∈ S'.offDiag,
        𝔼 i, (if feistelXor b m hbm qOf H i p.1 = feistelXor b m hbm qOf H i u ∧
            feistelXor b m hbm qOf H i p.2 = feistelXor b m hbm qOf H i u then (1 : ℚ) else 0)
      ≤ ∑ _p ∈ S'.offDiag, (((2 ^ m : ℕ) : ℚ) ^ 2)⁻¹ := sum_le_sum hpair
    _ = (#S'.offDiag : ℚ) * (((2 ^ m : ℕ) : ℚ) ^ 2)⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((#S' : ℚ) ^ 2) * (((2 ^ m : ℕ) : ℚ) ^ 2)⁻¹ := by
        gcongr
        rw [offDiag_card, sq]
        exact_mod_cast Nat.sub_le (#S' * #S') #S'
    _ = ((#S' : ℚ) / (2 ^ m : ℚ)) ^ 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        ring

/-- Pointwise quadratic upper bound on truncated excess above `2 * D`: for any `N, D : ℕ` and
`0 ≤ μ ≤ D` in `ℚ`, `((N - 2 * D : ℕ) : ℚ) * D ≤ ((N : ℚ) - μ) ^ 2`. -/
theorem nat_sub_two_mul_le_sq {N D : ℕ} {μ : ℚ} (hμ0 : 0 ≤ μ) (hμD : μ ≤ D) :
    ((N - 2 * D : ℕ) : ℚ) * (D : ℚ) ≤ ((N : ℚ) - μ) ^ 2 := by
  by_cases hle : N ≤ 2 * D
  · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero, zero_mul]
    exact sq_nonneg _
  · have hle' : 2 * D ≤ N := by omega
    rw [Nat.cast_sub hle', Nat.cast_mul, Nat.cast_ofNat]
    have hN : (2 : ℚ) * (D : ℚ) ≤ (N : ℚ) := by exact_mod_cast hle'
    nlinarith

/-- **3-wise independent Feistel bucket overflow bound**: under a 3-wise independent hash
`H : ι → Q → Fin (2 ^ m)`, for any `D ≥ 1` and `S : Finset (Fin U)` with
`#(S.erase u) ≤ D * 2 ^ m` such that `qOf` is quotient-injective on `insert u (S.erase u)`, the
expected overflow above `2 * D` in `u`'s Feistel bucket is at most `1`. -/
theorem expect_feistelXor_overflow_le_on {U b m D : ℕ}
    (hbm : b ≤ m) (hD : 1 ≤ D) {qOf : Fin U → Q}
    {H : ι → Q → Fin (2 ^ m)} (hh : IsKWiseIndependentHash 3 H)
    (S : Finset (Fin U)) (u : Fin U) (hS : #(S.erase u) ≤ D * 2 ^ m)
    (hq : ∀ u₁ ∈ insert u (S.erase u), ∀ u₂ ∈ insert u (S.erase u),
      qOf u₁ = qOf u₂ → keyQuotient b u₁.val = keyQuotient b u₂.val) :
    𝔼 i,
      (((#{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u} -
          2 * D : ℕ) : ℚ)) ≤ 1 := by
  classical
  have : Nonempty ι := hh.nonempty
  let S' : Finset (Fin U) := {x ∈ S.erase u | qOf x ≠ qOf u}
  let N (i : ι) : ℕ :=
    #{x ∈ S.erase u | feistelXor b m hbm qOf H i x = feistelXor b m hbm qOf H i u}
  let μ : ℚ := (#S' : ℚ) / (2 ^ m : ℚ)
  have hμ0 : 0 ≤ μ := by positivity
  have hμD : μ ≤ (D : ℚ) := by
    dsimp only [μ]
    rw [div_le_iff₀ (by positivity)]
    have hcard : #S' ≤ D * 2 ^ m := (card_filter_le _ _).trans hS
    exact_mod_cast hcard
  have hhpw : IsPairwiseIndependentHash H := hh.isPairwiseIndependentHash (by decide)
  have hexp1 : 𝔼 i, (N i : ℚ) = μ :=
    expect_card_feistelXor_eq_on (𝕜 := ℚ) hbm hhpw S u hq
  have hexp2 : 𝔼 i, (N i : ℚ) * ((N i : ℚ) - 1) ≤ μ ^ 2 :=
    expect_feistelXor_mul_sub_one_le_on hbm hh S u hq
  have hsq (i : ι) :
      ((N i : ℚ) - μ) ^ 2 =
        (N i : ℚ) * ((N i : ℚ) - 1) + (1 - 2 * μ) * (N i : ℚ) + μ ^ 2 := by
    ring
  have hvar : 𝔼 i, ((N i : ℚ) - μ) ^ 2 ≤ (D : ℚ) := by
    simp only [hsq]
    rw [expect_add_distrib, expect_add_distrib, ← mul_expect, Fintype.expect_const, hexp1]
    linarith
  have hpt : 𝔼 i, ((N i - 2 * D : ℕ) : ℚ) * (D : ℚ) ≤ (D : ℚ) := by
    calc 𝔼 i, ((N i - 2 * D : ℕ) : ℚ) * (D : ℚ)
        ≤ 𝔼 i, ((N i : ℚ) - μ) ^ 2 :=
          expect_le_expect fun i _ => nat_sub_two_mul_le_sq hμ0 hμD
      _ ≤ (D : ℚ) := hvar
  rw [← expect_mul] at hpt
  have hD_pos : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  nlinarith

end ProbabilityBounds

end Cslib.DataStructure.Dictionary.FeistelQuotient
