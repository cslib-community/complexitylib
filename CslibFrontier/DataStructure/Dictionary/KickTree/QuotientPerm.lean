/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.KickTree.RoundSeed
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.KWiseIndependent.Coupling
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance.Coupling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universal key-quotienting bijection across arbitrary universes `U ≥ n`

This module constructs an explicit, computable, zero-collision key-quotienting bijection
`quotientPermEquiv : Fin (2 ^ a) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m))` (for all `m ≤ a`) and a
universal full-quotient bit-width bound `mul_fullQuotBits_le_clog_choose` (for all `U, n`),
together with high-probability intra-shard `κ`-wise (`κ = Θ(c log n)`) distributional transfer
(for target bucket sets lying within a single shard `σ` via `bucketShard _ b = σ`) across every
universe `U ≥ n` once `n ≥ quotientPermThreshold c`, without assuming `U ≥ n ^ (1 + Ω(1))` or
`log U ≤ poly(log n)`.

## Source attribution and formalization adaptations

* **Primary sources**:
  - [BenderFarachColtonKuszmaulKuszmaulLiu2022] (`arXiv:2111.00602v2`): Section 1 (PDF pp. 2–3 /
    printed pp. 1–2), Section 2.4 (PDF p. 8 / printed p. 7, lines 376–386, fn. 12), Section 5.3
    Theorem 21 (PDF pp. 34–36 / printed pp. 33–35, quotiented `k`-kick trees via a uniformly random
    permutation on `[U]`, simulated for `|U| ≤ poly(n)` using `poly(n)`-independent permutations,
    and `Pr[∏_{x ∈ R} Q_x = 1] ≤ (|Q| / |U|) ^ |R|`), and Section 6.1 Theorems 22–23
    (PDF pp. 37–39 / printed pp. 36–38, large keys via indirection; formal theorem numbering starts
    at Theorem 2 on PDF p. 12 / printed p. 11).
  - [ArbitmanNaorSegev2010] (`arXiv:0912.5424v3`): Section 5.2 (PDF pp. 21–23 / printed pp. 20–22,
    1-round Feistel sharded permutation construction and intra-shard injectivity), Claim 5.4,
    Section 5.3 Theorem 5.6 (PDF p. 25 / printed p. 24, `(1 / 2) * (2 * δ) ^ t` contraction quoted
    from [KaplanNaorReingold2009]), and Section 5.4 Claim 5.7 (PDF p. 26 / printed p. 25, bin load
    / capacity bounds).
  - [NaorReingold1999] (*J. Cryptology* 12(1):29–66, 1999): Section 2.3 Definition 2.10 item 2
    (p. 36 / PDF p. 8, uniform distribution on tuples of distinct elements), Section 3.2
    Definition 3.1 & Theorems 3.1–3.2 (pp. 38–39 / PDF pp. 10–11), Section 5.2 Theorem 5.2
    (pp. 48–50 / PDF pp. 20–22), Section 6 Definition 6.1 (p. 52 / PDF p. 24), and Section 8
    Corollary 8.1 (pp. 60–61 / PDF pp. 32–33).
* **Original formalization adaptations**:
  - Rather than assuming an idealized uniformly random permutation on `[U]` simulated via
    `poly(n)`-independent permutations for `U = poly(n)` or large-key indirection,
    `quotientPermEquiv` combines **Case A** (`m + caseAGap c n ≤ a`, 2-round unbalanced Feistel
    `caseAEquiv`) and **Case B** (`a < m + caseAGap c n`, Arbitman–Naor–Segev 1-round Feistel
    sharding + `nrRounds c` unbalanced 3-round Feistel Naor–Reingold blocks).
  - Case B routes keys into `2 ^ ⌊m / 2⌋` shards that share one Naor–Reingold permutation instance;
    the `κ`-wise tail bounds are stated for target bucket sets inside a single shard `σ`.
  - `QuotientPermSeed` instantiates round functions via `multiplyShiftReduced` / `oddMulModWord`
    (`CslibFrontier.Probability.KWiseIndependent.ReducedLimbs`) and a shared `DoubleTabTopSeed`
    (`CslibFrontier.Probability.KWiseIndependent.DoubleTabulation` [Thorup2013]), requiring an
    explicit large asymptotic capacity threshold `quotientPermThreshold c ≤ n` (e.g.
    `quotientPermThreshold 0 = 2 ^ 50239744`, which is an asymptotic theoretical threshold ensuring
    all failure probabilities are negligible, satisfying `4 ≤ quotientPermThreshold c`). Word-RAM
    circuit compilation belongs to the downstream Word-RAM hash layer.

## Main definitions

* `Cslib.DataStructure.Dictionary.KickTree.bucketIndexBits`,
  `Cslib.DataStructure.Dictionary.KickTree.fullQuotBits`,
  `Cslib.DataStructure.Dictionary.KickTree.embedKey`: bucket bit-width `⌊log₂ n⌋`, full-quotient
  bit-width `⌈log₂ U⌉ - ⌊log₂ n⌋`, and canonical embedding `Fin U → Fin (2 ^ keyBits U)`.
* `Cslib.DataStructure.Dictionary.KickTree.QuotientPermRounds`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermEquiv`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermEncode`,
  `Cslib.DataStructure.Dictionary.KickTree.quotientPermDecode`,
  `Cslib.DataStructure.Dictionary.KickTree.fullQuotientPermEquiv`: unified deterministic quotienting
  bijections across Case A (`caseAEquiv` in `RoundSeed`) and Case B (`caseBEquiv` in
  `SmallUniversePerm`).
* `Cslib.DataStructure.Dictionary.KickTree.QuotientPermSeed`,
  `Cslib.DataStructure.Dictionary.KickTree.concreteRounds`,
  `Cslib.DataStructure.Dictionary.KickTree.concreteBucket`,
  `Cslib.DataStructure.Dictionary.KickTree.concreteQuot`,
  `Cslib.DataStructure.Dictionary.KickTree.concreteAux`,
  `Cslib.DataStructure.Dictionary.KickTree.fullBucket`,
  `Cslib.DataStructure.Dictionary.KickTree.fullQuot`,
  `Cslib.DataStructure.Dictionary.KickTree.fullDecode`,
  `Cslib.DataStructure.Dictionary.KickTree.fullAux`: concrete computable seed bundle and
  instantiated quotienting bijection + auxiliary hash.

## Main results

* `Cslib.DataStructure.Dictionary.KickTree.mul_fullQuotBits_le_clog_choose`,
  `Cslib.DataStructure.Dictionary.KickTree.mul_fullQuotBits_add_valBits_le_optBits`:
  `n * fullQuotBits U n ≤ Nat.clog 2 (U.choose n) + 2 * n` for all `U, n`.
* `Cslib.DataStructure.Dictionary.KickTree.dist_concreteCaseA_restrict_le`,
  `Cslib.DataStructure.Dictionary.KickTree.dist_concreteCaseB_shardTuple_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_concreteCaseB_shardLoad_outside_le`: concrete Case A
  and Case B statistical-distance transfer and shard-load concentration bounds.
* `Cslib.DataStructure.Dictionary.KickTree.prob_concreteQuotientPerm_forall_mem_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_concreteQuotientPerm_forall_mem_perKey_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_fullQuotientPerm_forall_mem_le`,
  `Cslib.DataStructure.Dictionary.KickTree.prob_fullQuotientPerm_forall_mem_perKey_le`: unified
  intra-shard `κ`-tuple multiplicative tail transfer (for target bucket sets `B` / `B u` lying in a
  common shard `σ`, `bucketShard _ b = σ`) across all `U ≥ n` once `n ≥ quotientPermThreshold c`
  (`≤ 1 / n ^ (c + 1)`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, *On the Optimal
  Time/Space Tradeoff for Hash Tables*][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*][ArbitmanNaorSegev2010]
* [M. Naor and O. Reingold, *On the Construction of Pseudorandom Permutations: Luby–Rackoff
  Revisited*][NaorReingold1999]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.KickTree

open Cslib.DataStructure.Dictionary Cslib.DataStructure.Dictionary.FeistelPerm
open Cslib.Probability Cslib.Probability.PMF Finset Fintype
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Section 1: Full-quotient bit-width and information-theoretic space bound -/

/-- Bucket-index bit-width `⌊log₂ n⌋` for full key quotienting at capacity `n`. -/
@[expose] def bucketIndexBits (n : ℕ) : ℕ :=
  Nat.log 2 n

/-- Stored quotient bit-width `⌈log₂ U⌉ - ⌊log₂ n⌋` per key at universe `U` and capacity `n`. -/
@[expose] def fullQuotBits (U n : ℕ) : ℕ :=
  FeistelQuotient.keyBits U - bucketIndexBits n

/-- Whenever `n ≤ U`, `bucketIndexBits n ≤ FeistelQuotient.keyBits U`. -/
theorem bucketIndexBits_le_keyBits {U n : ℕ} (hnU : n ≤ U) :
    bucketIndexBits n ≤ FeistelQuotient.keyBits U :=
  (Nat.log_mono_right hnU).trans (Nat.log_le_clog 2 U)

/-- Whenever `n ≤ U`, `bucketIndexBits n + fullQuotBits U n = FeistelQuotient.keyBits U`. -/
theorem bucketIndexBits_add_fullQuotBits {U n : ℕ} (hnU : n ≤ U) :
    bucketIndexBits n + fullQuotBits U n = FeistelQuotient.keyBits U :=
  Nat.add_sub_of_le (bucketIndexBits_le_keyBits hnU)

/-- If `U ≤ 2 ^ w`, then `fullQuotBits U n ≤ w`. -/
theorem fullQuotBits_le_of_le_pow {U w n : ℕ} (hU : U ≤ 2 ^ w) :
    fullQuotBits U n ≤ w :=
  (Nat.sub_le _ _).trans (Nat.clog_le_of_le_pow hU)

/-- Canonical injective embedding `Fin U → Fin (2 ^ keyBits U)` preserving `.val`. -/
@[expose] def embedKey {U : ℕ} (u : Fin U) : Fin (2 ^ FeistelQuotient.keyBits U) :=
  ⟨u.val, u.isLt.trans_le (Nat.le_pow_clog (by decide) U)⟩

@[simp] theorem val_embedKey {U : ℕ} (u : Fin U) : (embedKey u).val = u.val := rfl

theorem embedKey_injective (U : ℕ) : Function.Injective (@embedKey U) :=
  fun _ _ h => Fin.ext (congrArg (Fin.val : Fin (2 ^ FeistelQuotient.keyBits U) → ℕ) h)

/-- **Universal information-theoretic full-quotient bit bound**: for all `U` and `n` (including
`n = 0`, `n = U`, and `U < n`), `n` quotients of `fullQuotBits U n` bits occupy at most
`⌈log₂ C(U, n)⌉ + 2 * n` bits. -/
theorem mul_fullQuotBits_le_clog_choose (U n : ℕ) :
    n * fullQuotBits U n ≤ Nat.clog 2 (U.choose n) + 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases lt_or_ge U n with hUn | hnU
  · have hkey : FeistelQuotient.keyBits U ≤ bucketIndexBits n + 1 :=
      Nat.clog_le_of_le_pow (hUn.le.trans (Nat.lt_pow_succ_log_self (by decide) n).le)
    have hq : fullQuotBits U n ≤ 1 := by unfold fullQuotBits; omega
    rw [Nat.choose_eq_zero_of_lt hUn, Nat.clog_zero_right, Nat.zero_add]
    nlinarith [Nat.mul_le_mul_left n hq]
  · have hU : 1 ≤ U := hn.trans_le hnU
    have hpow_key : 2 ^ FeistelQuotient.keyBits U ≤ 2 * U :=
      Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
    have hpow_n : n ≤ 2 ^ (bucketIndexBits n + 1) :=
      (Nat.lt_pow_succ_log_self (by decide) n).le
    have hchoose : U.choose n ≤ 2 ^ Nat.clog 2 (U.choose n) :=
      Nat.le_pow_clog (by decide) (U.choose n)
    have hmain : 2 ^ (n * FeistelQuotient.keyBits U) ≤
        2 ^ (n + n * (bucketIndexBits n + 1) + Nat.clog 2 (U.choose n)) := by
      calc 2 ^ (n * FeistelQuotient.keyBits U)
          = (2 ^ FeistelQuotient.keyBits U) ^ n := by rw [Nat.mul_comm, Nat.pow_mul]
        _ ≤ (2 * U) ^ n := Nat.pow_le_pow_left hpow_key n
        _ = 2 ^ n * U ^ n := Nat.mul_pow 2 U n
        _ ≤ 2 ^ n * (n ^ n * U.choose n) :=
            Nat.mul_le_mul_left (2 ^ n) (FeistelQuotient.pow_le_pow_mul_choose hnU)
        _ ≤ 2 ^ n * ((2 ^ (bucketIndexBits n + 1)) ^ n * 2 ^ Nat.clog 2 (U.choose n)) :=
            Nat.mul_le_mul_left (2 ^ n) (Nat.mul_le_mul (Nat.pow_le_pow_left hpow_n n) hchoose)
        _ = 2 ^ (n + n * (bucketIndexBits n + 1) + Nat.clog 2 (U.choose n)) := by
            rw [← Nat.pow_mul, Nat.mul_comm (bucketIndexBits n + 1) n, ← Nat.pow_add,
              ← Nat.pow_add, ← Nat.add_assoc]
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmain
    rw [← bucketIndexBits_add_fullQuotBits hnU, Nat.mul_add] at hexp
    linarith

/-- Full-quotient + value space against `Dynamic.optBits U V n = ⌈log₂ C(U, n)⌉ + n * ⌈log₂ V⌉`. -/
theorem mul_fullQuotBits_add_valBits_le_optBits (U V n : ℕ) :
    n * (fullQuotBits U n + FeistelQuotient.valBits V) ≤ Dynamic.optBits U V n + 2 * n := by
  have hq := mul_fullQuotBits_le_clog_choose U n
  unfold Dynamic.optBits FeistelQuotient.valBits
  linarith

/-! ## Section 2: Unified deterministic key-quotienting bijection (`Case A` + `Case B`) -/

/-- Unified round-function bundle across Case A and Case B. -/
structure QuotientPermRounds (a m c n : ℕ) where
  /-- Case A 2-round unbalanced Feistel functions (`m + caseAGap c n ≤ a`). -/
  caseA : CaseARounds a m
  /-- Case B sharded `nrRounds c`-block Naor–Reingold functions (`a < m + caseAGap c n`). -/
  caseB : CaseBRounds a m (nrRounds c)

/-- **Universal deterministic key-quotienting bijection** across all `m ≤ a`: dispatches to
`caseAEquiv` when `m + caseAGap c n ≤ a` and to `caseBEquiv` when `a < m + caseAGap c n`. -/
@[expose] def quotientPermEquiv {a m c n : ℕ} (hma : m ≤ a) (r : QuotientPermRounds a m c n) :
    Fin (2 ^ a) ≃ Fin (2 ^ m) × Fin (2 ^ (a - m)) :=
  if m + caseAGap c n ≤ a then caseAEquiv hma r.caseA else caseBEquiv hma r.caseB

/-- Forward key-quotienting map `u ↦ (bucket, quot)` in `O(c)` round evaluations. -/
@[expose] def quotientPermEncode {a m c n : ℕ} (hma : m ≤ a) (r : QuotientPermRounds a m c n)
    (u : Fin (2 ^ a)) : Fin (2 ^ m) × Fin (2 ^ (a - m)) :=
  quotientPermEquiv hma r u

/-- Inverse key-reconstruction map `(bucket, quot) ↦ u` in `O(c)` round evaluations. -/
@[expose] def quotientPermDecode {a m c n : ℕ} (hma : m ≤ a) (r : QuotientPermRounds a m c n)
    (p : Fin (2 ^ m) × Fin (2 ^ (a - m))) : Fin (2 ^ a) :=
  (quotientPermEquiv hma r).symm p

@[simp] theorem quotientPermDecode_quotientPermEncode {a m c n : ℕ} (hma : m ≤ a)
    (r : QuotientPermRounds a m c n) (u : Fin (2 ^ a)) :
    quotientPermDecode hma r (quotientPermEncode hma r u) = u :=
  (quotientPermEquiv hma r).symm_apply_apply u

@[simp] theorem quotientPermEncode_quotientPermDecode {a m c n : ℕ} (hma : m ≤ a)
    (r : QuotientPermRounds a m c n) (p : Fin (2 ^ m) × Fin (2 ^ (a - m))) :
    quotientPermEncode hma r (quotientPermDecode hma r p) = p :=
  (quotientPermEquiv hma r).apply_symm_apply p

/-- Full-quotient specialization `(u : Fin (2 ^ keyBits U)) ≃ Fin (2 ^ bucketIndexBits n) ×
Fin (2 ^ fullQuotBits U n)` for any `n ≤ U`. -/
@[expose] def fullQuotientPermEquiv {U c n : ℕ} (hnU : n ≤ U)
    (r : QuotientPermRounds (FeistelQuotient.keyBits U) (bucketIndexBits n) c n) :
    Fin (2 ^ FeistelQuotient.keyBits U) ≃
      Fin (2 ^ bucketIndexBits n) × Fin (2 ^ fullQuotBits U n) :=
  quotientPermEquiv (bucketIndexBits_le_keyBits hnU) r

/-! ## Section 3: Concrete Double-Tabulation + `oddMulModWord` instantiation -/

/-- Concrete computable seed bundle for the universal key-quotienting bijection and auxiliary
hash across all `m ≤ a`. -/
structure QuotientPermSeed (a m b_aux c n : ℕ) where
  /-- Shared top-level simple-tabulation table `T₁` (`[Thorup2013]`). -/
  top : DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  /-- Case A Round-1 odd-multiplier reduction seed on `Fin (2 ^ m)`. -/
  α₀ : Fin (2 ^ (m - 1))
  /-- Case A Round-1 bottom table producing `(a - m)`-bit quotient masks. -/
  botA₀ : DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m)
  /-- Case A Round-2 odd-multiplier reduction seed on `Fin (2 ^ (a - m))`. -/
  α₁ : Fin (2 ^ (a - m - 1))
  /-- Case A Round-2 bottom table producing combined `(m + b_aux)`-bit `(bucket, aux)` masks. -/
  botA₁₂ : DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)
  /-- Case B Arbitman–Naor–Segev 1-round Feistel shard bottom table. -/
  botShard : DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (shardBits m)
  /-- Case B `nrRounds c` independent Naor–Reingold block bottom tables. -/
  botNR : QuotientPermNRSeed c a m n
  /-- Case B auxiliary hash bottom table producing `b_aux`-bit outputs. -/
  botAuxB : DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) b_aux

/-- Product equivalence witnessing `Fintype` and uniform-marginal factorization of
`QuotientPermSeed`. -/
def quotientPermSeedEquivProd (a m b_aux c n : ℕ) :
    QuotientPermSeed a m b_aux c n ≃
      DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n) ×
      (Fin (2 ^ (m - 1)) ×
        DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m) ×
        Fin (2 ^ (a - m - 1)) ×
        DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)) ×
      (DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (shardBits m) ×
        QuotientPermNRSeed c a m n ×
        DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) b_aux) where
  toFun θ := (θ.top, (θ.α₀, θ.botA₀, θ.α₁, θ.botA₁₂), (θ.botShard, θ.botNR, θ.botAuxB))
  invFun
    | (top, (α₀, botA₀, α₁, botA₁₂), (botShard, botNR, botAuxB)) =>
      ⟨top, α₀, botA₀, α₁, botA₁₂, botShard, botNR, botAuxB⟩
  left_inv θ := by cases θ; rfl
  right_inv p := by rcases p with ⟨_, ⟨_, _, _, _⟩, ⟨_, _, _⟩⟩; rfl

instance {a m b_aux c n : ℕ} : Fintype (QuotientPermSeed a m b_aux c n) :=
  Fintype.ofEquiv _ (quotientPermSeedEquivProd a m b_aux c n).symm

instance {a m b_aux c n : ℕ} : Nonempty (QuotientPermSeed a m b_aux c n) :=
  ⟨⟨fun _ _ _ => 0, 0, fun _ _ => 0, 0, fun _ _ => 0, fun _ _ => 0,
    ⟨fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩, fun _ _ => 0⟩⟩

/-- Concrete `QuotientPermRounds` instantiated from `θ : QuotientPermSeed a m b_aux c n`. -/
@[expose] def concreteRounds {a m b_aux c n : ℕ} (θ : QuotientPermSeed a m b_aux c n) :
    QuotientPermRounds a m c n where
  caseA :=
    { g₀ := reducedDoubleTab c n m (a - m) θ.α₀ θ.top θ.botA₀
      g₁ := fun q =>
        (splitBucketAuxEquiv m b_aux
          (reducedDoubleTab c n (a - m) (m + b_aux) θ.α₁ θ.top θ.botA₁₂ q)).1 }
  caseB :=
    { fShard := doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
        (2 ^ suffixBits a m) (shardBits m) θ.top θ.botShard
      nrBlocks := fun r =>
        { f₀ := doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
            (2 ^ nrHalfLow (suffixBits a m)) (nrHalfHigh (suffixBits a m)) θ.top
            (θ.botNR.blocks r).s₀
          f₁ := doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
            (2 ^ nrHalfHigh (suffixBits a m)) (nrHalfLow (suffixBits a m)) θ.top
            (θ.botNR.blocks r).s₁
          f₂ := doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
            (2 ^ nrHalfLow (suffixBits a m)) (nrHalfHigh (suffixBits a m)) θ.top
            (θ.botNR.blocks r).s₂ } }

/-- Concrete bucket index `(quotientPermEquiv hma (concreteRounds θ) u).1 : Fin (2 ^ m)`. -/
@[expose] def concreteBucket {a m b_aux c n : ℕ} (hma : m ≤ a)
    (θ : QuotientPermSeed a m b_aux c n) (u : Fin (2 ^ a)) : Fin (2 ^ m) :=
  (quotientPermEquiv hma (concreteRounds θ) u).1

/-- Concrete stored quotient `(quotientPermEquiv hma (concreteRounds θ) u).2` in
`Fin (2 ^ (a - m))`. -/
@[expose] def concreteQuot {a m b_aux c n : ℕ} (hma : m ≤ a)
    (θ : QuotientPermSeed a m b_aux c n) (u : Fin (2 ^ a)) : Fin (2 ^ (a - m)) :=
  (quotientPermEquiv hma (concreteRounds θ) u).2

/-- Concrete `b_aux`-bit auxiliary hash accompanying `concreteBucket`. -/
@[expose] def concreteAux {a m b_aux c n : ℕ} (hma : m ≤ a)
    (θ : QuotientPermSeed a m b_aux c n) (u : Fin (2 ^ a)) : Fin (2 ^ b_aux) :=
  if m + caseAGap c n ≤ a then
    (splitBucketAuxEquiv m b_aux
      (reducedDoubleTab c n (a - m) (m + b_aux) θ.α₁ θ.top θ.botA₁₂
        (caseAQuot hma (reducedDoubleTab c n m (a - m) θ.α₀ θ.top θ.botA₀) u))).2
  else
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ a) b_aux θ.top θ.botAuxB u

/-- **Concrete Case A statistical-distance transfer**: when `m + caseAGap c n ≤ a`,
`quotientPermThreshold c ≤ n`, `#S ≤ n`, and `T ⊆ S` (`#T ≤ quotientPermInd c n`), the joint
distribution of `(concreteBucket hma θ u, concreteAux hma θ u)_{u ∈ T}` under uniform
`θ : QuotientPermSeed a m b_aux c n` is within `1 / n ^ (c + 1)` of uniform. -/
theorem dist_concreteCaseA_restrict_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hgap : m + caseAGap c n ≤ a) (hn : quotientPermThreshold c ≤ n)
    {S T : Finset (Fin (2 ^ a))} (hS : #S ≤ n) (hTS : T ⊆ S)
    (hT : #T ≤ quotientPermInd c n) :
    dist ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).map fun θ (u : T) =>
        (concreteBucket hma θ u.1, concreteAux hma θ u.1))
      (PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))) ≤
      1 / (n : ℝ) ^ (c + 1) := by
  classical
  let Top := DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  let BotA₀ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m)
  let BotA₁₂ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)
  let CaseB := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (shardBits m) ×
    QuotientPermNRSeed c a m n ×
    DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) b_aux
  have : Nonempty Top := ⟨fun _ _ _ => 0⟩
  have : Nonempty BotA₀ := ⟨fun _ _ => 0⟩
  have : Nonempty BotA₁₂ := ⟨fun _ _ => 0⟩
  have : Nonempty CaseB := ⟨(fun _ _ => 0, Classical.arbitrary _, fun _ _ => 0)⟩
  let eA : QuotientPermSeed a m b_aux c n ≃
      (Top × (Fin (2 ^ (m - 1)) × BotA₀ × Fin (2 ^ (a - m - 1)) × BotA₁₂)) × CaseB :=
    { toFun := fun θ =>
        ((θ.top, (θ.α₀, θ.botA₀, θ.α₁, θ.botA₁₂)), (θ.botShard, θ.botNR, θ.botAuxB))
      invFun := fun p =>
        ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun θ => by cases θ; rfl
      right_inv := fun p => by rcases p with ⟨⟨_, _, _, _, _⟩, ⟨_, _, _⟩⟩; rfl }
  have hmarg : ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).map fun θ (u : T) =>
      (concreteBucket hma θ u.1, concreteAux hma θ u.1)) =
      (PMF.uniformOfFintype Top).bind fun τ =>
        (PMF.uniformOfFintype (Fin (2 ^ (m - 1)))).bind fun α₀ =>
          (PMF.uniformOfFintype BotA₀).bind fun botA₀ =>
            (PMF.uniformOfFintype (Fin (2 ^ (a - m - 1)))).bind fun α₁ =>
              (PMF.uniformOfFintype BotA₁₂).map fun botA₁₂ (u : T) =>
                caseABucketAux hma (reducedDoubleTab c n m (a - m) α₀ τ botA₀)
                  (reducedDoubleTab c n (a - m) (m + b_aux) α₁ τ botA₁₂) u.1 := by
    let F : Top × (Fin (2 ^ (m - 1)) × BotA₀ × Fin (2 ^ (a - m - 1)) × BotA₁₂) →
        T → Fin (2 ^ m) × Fin (2 ^ b_aux) :=
      fun p u => caseABucketAux hma (reducedDoubleTab c n m (a - m) p.2.1 p.1 p.2.2.1)
        (reducedDoubleTab c n (a - m) (m + b_aux) p.2.2.2.1 p.1 p.2.2.2.2) u.1
    have hfun : (fun θ : QuotientPermSeed a m b_aux c n => fun u : T =>
        (concreteBucket hma θ u.1, concreteAux hma θ u.1)) = (F ∘ Prod.fst ∘ eA) := by
      ext θ u : 2
      simp [concreteBucket, concreteAux, quotientPermEquiv, concreteRounds, hgap, caseABucketAux,
        F, eA]
    rw [hfun, ← PMF.map_comp, ← PMF.map_comp, uniformOfFintype_map_equiv eA,
      uniformOfFintype_prod_map_fst]
    rw [← uniformOfFintype_prod Top, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype Top).bind ·) (funext fun τ => ?_)
    simp only [PMF.map_comp, Function.comp_def]
    rw [← uniformOfFintype_prod (Fin (2 ^ (m - 1))), PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun α₀ => ?_)
    simp only [PMF.map_comp, Function.comp_def]
    rw [← uniformOfFintype_prod BotA₀, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype _).bind ·) (funext fun botA₀ => ?_)
    simp only [PMF.map_comp, Function.comp_def]
    rw [← uniformOfFintype_prod (Fin (2 ^ (a - m - 1))), PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, F]
    rfl
  rw [hmarg]
  exact dist_caseA_reducedDoubleTab_le hma hgap hn hS hTS hT

private theorem le_chars_mul_charBits_of_lt_caseAGap {a m c n : ℕ}
    (hcaseB : a < m + caseAGap c n) (hn : quotientPermThreshold c ≤ n)
    (hm_hi : m ≤ 8 * quotientPermCharBits n) :
    a ≤ quotientPermChars c * quotientPermCharBits n := by
  have hclog2 : Nat.clog 2 (max n 2) ≤ 8 * quotientPermCharBits n :=
    (Nat.clog_mono_right 2 (max_le_max_left n (by decide))).trans
      (clog_max_le_eight_mul_charBits hn).1
  have hgap_ub : caseAGap c n ≤ (c + 3) * (8 * quotientPermCharBits n) :=
    Nat.mul_le_mul_left (c + 3) hclog2
  rw [quotientPermChars_eq]; nlinarith

/-- **Concrete Case B shard-tuple statistical-distance transfer**: when
`bucketIndexBits n ≤ m ≤ a < m + caseAGap c n`, `m ≤ 8 * quotientPermCharBits n`,
`quotientPermThreshold c ≤ n`, `#T ≤ quotientPermInd c n`, and
`yEmb : T ↪ Fin (2 ^ suffixBits a m)`, the distribution of `(shard, nrPerm ∘ yEmb, concreteAux)`
under uniform `θ : QuotientPermSeed a m b_aux c n` is within `1 / (4 * n ^ (c + 2))` of
`Uniform × UniformInj × Uniform`. -/
theorem dist_concreteCaseB_shardTuple_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hcaseB : a < m + caseAGap c n) (hn : quotientPermThreshold c ≤ n)
    (hm_lo : bucketIndexBits n ≤ m) (hm_hi : m ≤ 8 * quotientPermCharBits n)
    {T : Finset (Fin (2 ^ a))} (hT : #T ≤ quotientPermInd c n)
    (yEmb : T ↪ Fin (2 ^ suffixBits a m)) :
    haveI : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
    dist ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).map fun θ =>
        ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
            (concreteRounds θ).caseB.fShard (yEmb u)),
          ((Equiv.refl T).embeddingCongr
            (nrComposedEquiv (suffixBits a m) (nrRounds c) (concreteRounds θ).caseB.nrBlocks) yEmb,
            fun u : T => concreteAux hma θ u.1)))
      (PMF.uniformOfFintype
        ((T → Fin (2 ^ shardBits m)) ×
          ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))))) ≤
      1 / (4 * (n : ℝ) ^ (c + 2)) := by
  classical
  have : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
  have hnotA : ¬ (m + caseAGap c n ≤ a) := not_le.mpr hcaseB
  obtain ⟨hb_log, h2κ, _, _⟩ := quotientPermInd_le_self_of_threshold hn
  have ha_ub : a ≤ quotientPermChars c * quotientPermCharBits n :=
    le_chars_mul_charBits_of_lt_caseAGap hcaseB hn hm_hi
  have ha'_lo : 2 * quotientPermCharBits n ≤ suffixBits a m := by
    unfold bucketIndexBits at hm_lo
    dsimp only [suffixBits, shardBits]
    omega
  have ha'_ub : suffixBits a m ≤ quotientPermChars c * quotientPermCharBits n :=
    (Nat.sub_le _ _).trans ha_ub
  have hlo_ub : nrHalfLow (suffixBits a m) ≤ quotientPermChars c * quotientPermCharBits n :=
    (nrHalfLow_le _).trans ha'_ub
  have hhi_ub : nrHalfHigh (suffixBits a m) ≤ quotientPermChars c * quotientPermCharBits n :=
    (Nat.sub_le _ _).trans ha'_ub
  let Top := DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  let BotSh := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (shardBits m)
  let NR₀ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n)
    (nrHalfHigh (suffixBits a m))
  let NR₁ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n)
    (nrHalfLow (suffixBits a m))
  let NR₂ := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n)
    (nrHalfHigh (suffixBits a m))
  let BotAux := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) b_aux
  let CaseA := Fin (2 ^ (m - 1)) ×
    DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m) ×
    Fin (2 ^ (a - m - 1)) ×
    DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)
  have : Nonempty Top := ⟨fun _ _ _ => 0⟩
  have : Nonempty BotSh := ⟨fun _ _ => 0⟩
  have : Nonempty NR₀ := ⟨fun _ _ => 0⟩
  have : Nonempty NR₁ := ⟨fun _ _ => 0⟩
  have : Nonempty NR₂ := ⟨fun _ _ => 0⟩
  have : Nonempty BotAux := ⟨fun _ _ => 0⟩
  have : Nonempty CaseA := ⟨(0, fun _ _ => 0, 0, fun _ _ => 0)⟩
  let eB : QuotientPermSeed a m b_aux c n ≃
      (Top × (BotSh × (NRComposedSeed (nrRounds c) NR₀ NR₁ NR₂ × BotAux))) × CaseA :=
    { toFun := fun θ =>
        ((θ.top, (θ.botShard, (θ.botNR, θ.botAuxB))), (θ.α₀, θ.botA₀, θ.α₁, θ.botA₁₂))
      invFun := fun p =>
        ⟨p.1.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2, p.1.2.1, p.1.2.2.1, p.1.2.2.2⟩
      left_inv := fun θ => by cases θ; rfl
      right_inv := fun p => by rcases p with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rfl }
  let h_sh (τ : Top) (b : BotSh) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ suffixBits a m) (shardBits m) τ b
  let h_nr₀ (τ : Top) (b : NR₀) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ nrHalfLow (suffixBits a m)) (nrHalfHigh (suffixBits a m)) τ b
  let h_nr₁ (τ : Top) (b : NR₁) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ nrHalfHigh (suffixBits a m)) (nrHalfLow (suffixBits a m)) τ b
  let h_nr₂ (τ : Top) (b : NR₂) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ nrHalfLow (suffixBits a m)) (nrHalfHigh (suffixBits a m)) τ b
  let h_aux (τ : Top) (b : BotAux) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ a) b_aux τ b
  have hmarg : ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).map fun θ =>
      ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
          (concreteRounds θ).caseB.fShard (yEmb u)),
        ((Equiv.refl T).embeddingCongr
          (nrComposedEquiv (suffixBits a m) (nrRounds c) (concreteRounds θ).caseB.nrBlocks) yEmb,
          fun u : T => concreteAux hma θ u.1))) =
      (PMF.uniformOfFintype Top).bind fun τ =>
        (PMF.uniformOfFintype BotSh).bind fun s_sh =>
          (nrComposedSeedDist (suffixBits a m) (nrRounds c)
              (h_nr₀ τ) (h_nr₁ τ) (h_nr₂ τ)).bind fun π =>
            (PMF.uniformOfFintype BotAux).map fun s_aux =>
              ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
                  h_sh τ s_sh (yEmb u)),
                ((Equiv.refl T).embeddingCongr π yEmb, fun u : T => h_aux τ s_aux u.1)) := by
    let G : Top × (BotSh × (NRComposedSeed (nrRounds c) NR₀ NR₁ NR₂ × BotAux)) →
        (T → Fin (2 ^ shardBits m)) × ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux))) :=
      fun q =>
        ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
            h_sh q.1 q.2.1 (yEmb u)),
          ((Equiv.refl T).embeddingCongr (nrComposedEquiv (suffixBits a m) (nrRounds c) (fun r =>
              ⟨h_nr₀ q.1 (q.2.2.1.blocks r).s₀, h_nr₁ q.1 (q.2.2.1.blocks r).s₁,
                h_nr₂ q.1 (q.2.2.1.blocks r).s₂⟩)) yEmb,
            fun u : T => h_aux q.1 q.2.2.2 u.1))
    have hfun : (fun θ : QuotientPermSeed a m b_aux c n =>
        ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
            (concreteRounds θ).caseB.fShard (yEmb u)),
          ((Equiv.refl T).embeddingCongr
            (nrComposedEquiv (suffixBits a m) (nrRounds c) (concreteRounds θ).caseB.nrBlocks) yEmb,
            fun u : T => concreteAux hma θ u.1))) = (G ∘ Prod.fst ∘ eB) := by
      ext θ : 1
      simp [G, eB, concreteRounds, concreteAux, hnotA, h_sh, h_nr₀, h_nr₁, h_nr₂, h_aux]
    rw [hfun, ← PMF.map_comp, ← PMF.map_comp, uniformOfFintype_map_equiv eB,
      uniformOfFintype_prod_map_fst]
    rw [← uniformOfFintype_prod Top, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype Top).bind ·) (funext fun τ => ?_)
    simp only [PMF.map_comp, Function.comp_def]
    rw [← uniformOfFintype_prod BotSh, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype BotSh).bind ·) (funext fun s_sh => ?_)
    simp only [PMF.map_comp, Function.comp_def]
    rw [← uniformOfFintype_prod (NRComposedSeed (nrRounds c) NR₀ NR₁ NR₂) BotAux, PMF.map_bind,
      nrComposedSeedDist_eq, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def, G]
  rw [hmarg]
  let GoodTop : Set Top := {τ | IsKUnique (quotientPermInd c n) (simpleTabTuple τ)}
  have habs := dist_caseB_shardTuple_le hma (one_le_nrRounds c) h_sh h_nr₀ h_nr₁ h_nr₂ h_aux hT
    yEmb GoodTop (prob_not_isKUnique_quotientPerm_le hn)
    (fun τ hτ => isKWise_doubleTab_pow_of_le ha'_ub hτ)
    (fun τ hτ => (isKWise_doubleTab_pow_of_le hlo_ub hτ).mono h2κ)
    (fun τ hτ => isKWise_doubleTab_pow_of_le hhi_ub hτ)
    (fun τ hτ => isKWise_doubleTab_pow_of_le hlo_ub hτ)
    (fun τ hτ => isKWise_doubleTab_pow_of_le ha_ub hτ)
  have hnr := nr_contraction_quotientPerm_le hn ha'_lo
  have hrB : 1 / (8 * (n : ℝ) ^ (c + 2)) + 1 / (8 * (n : ℝ) ^ (c + 2)) =
      1 / (4 * (n : ℝ) ^ (c + 2)) := by ring
  linarith

private theorem shard_suffix_ratio_eq {a m : ℕ} (hma : m ≤ a) (k : ℕ) :
    ((1 : ℝ) / (2 ^ shardBits m : ℝ)) *
      (((k * 2 ^ (a - m) : ℕ) : ℝ) / (2 ^ suffixBits a m : ℝ)) =
      (k : ℝ) / (2 ^ m : ℝ) := by
  have h1 : shardBits m + suffixBits a m = a := Nat.add_sub_of_le (shardBits_le_of_le hma)
  have h2 : m + (a - m) = a := Nat.add_sub_of_le hma
  have hpow : (2 ^ shardBits m : ℝ) * (2 ^ suffixBits a m : ℝ) =
      (2 ^ m : ℝ) * (2 ^ (a - m) : ℝ) := by rw [← pow_add, ← pow_add, h1, h2]
  push_cast
  rw [div_mul_div_comm, one_mul, hpow, mul_div_mul_right _ _ (by positivity)]

/-- **Concrete Case B shard-load concentration**: in Case B (`a < m + caseAGap c n`), the
probability that any shard `σ : Fin (2 ^ shardBits m)` deviates from mean load
`#S / 2 ^ shardBits m` by at least `a_dev > 0` is bounded via
`FeistelPerm.dens_exists_bucketLoad_sub_ge_le`. -/
theorem prob_concreteCaseB_shardLoad_outside_le {a m b_aux c n k_mom : ℕ}
    (hma : m ≤ a) (hcaseB : a < m + caseAGap c n) (hn : quotientPermThreshold c ≤ n)
    (hm_hi : m ≤ 8 * quotientPermCharBits n)
    (hk_pos : 1 ≤ k_mom) (hk_ind : 2 * k_mom ≤ quotientPermInd c n)
    (S : Finset (Fin (2 ^ a))) {a_dev : ℝ}
    (hk_mu : 2 * (k_mom : ℝ) ≤ 3 * ((#S : ℝ) / (2 ^ shardBits m : ℝ))) (ha_dev : 0 < a_dev) :
    ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).toOuterMeasure
      {θ | ∃ σ : Fin (2 ^ shardBits m),
        a_dev ≤ |(#(S.filter fun u => bucketShard m (concreteBucket hma θ u) = σ) : ℝ) -
          (#S : ℝ) / (2 ^ shardBits m : ℝ)|}).toReal ≤
      1 / (8 * (n : ℝ) ^ (c + 2)) +
        (2 ^ (shardBits m + 1) : ℝ) *
          (3 * (k_mom : ℝ) * ((#S : ℝ) / (2 ^ shardBits m : ℝ)) / a_dev ^ 2) ^ k_mom := by
  classical
  have hnotA : ¬ (m + caseAGap c n ≤ a) := not_le.mpr hcaseB
  have ha_ub : a ≤ quotientPermChars c * quotientPermCharBits n :=
    le_chars_mul_charBits_of_lt_caseAGap hcaseB hn hm_hi
  have ha'_ub : suffixBits a m ≤ quotientPermChars c * quotientPermCharBits n :=
    (Nat.sub_le _ _).trans ha_ub
  let Top := DoubleTabTopSeed (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
  let BotSh := DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (shardBits m)
  let Rest := (Fin (2 ^ (m - 1)) ×
    DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (a - m) ×
    Fin (2 ^ (a - m - 1)) ×
    DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) (m + b_aux)) ×
    (QuotientPermNRSeed c a m n ×
      DoubleTabBotSeed (quotientPermInter c) (quotientPermCharBits n) b_aux)
  have : Nonempty Top := ⟨fun _ _ _ => 0⟩
  have : Nonempty BotSh := ⟨fun _ _ => 0⟩
  have : Nonempty Rest := ⟨((0, fun _ _ => 0, 0, fun _ _ => 0),
    (Classical.arbitrary _, fun _ _ => 0))⟩
  let eSh : QuotientPermSeed a m b_aux c n ≃ (Top × BotSh) × Rest :=
    { toFun := fun θ => ((θ.top, θ.botShard),
        ((θ.α₀, θ.botA₀, θ.α₁, θ.botA₁₂), (θ.botNR, θ.botAuxB)))
      invFun := fun p => ⟨p.1.1, p.2.1.1, p.2.1.2.1, p.2.1.2.2.1, p.2.1.2.2.2,
        p.1.2, p.2.2.1, p.2.2.2⟩
      left_inv := fun θ => by cases θ; rfl
      right_inv := fun p => by rcases p with ⟨⟨_, _⟩, ⟨_, _, _, _⟩, ⟨_, _⟩⟩; rfl }
  let S_sh := S.map (bitDomainEquiv (shardBits_le_of_le hma)).toEmbedding
  have hS_card : #S_sh = #S := card_map _
  let h_sh (τ : Top) (b : BotSh) :=
    doubleTabHash (quotientPermChars c) (quotientPermInter c) (quotientPermCharBits n)
      (2 ^ suffixBits a m) (shardBits m) τ b
  let E_pair : Set (Top × BotSh) := {p | ∃ σ : Fin (2 ^ shardBits m),
    a_dev ≤ |(bucketLoad (h_sh p.1 p.2) S_sh σ : ℝ) - (#S_sh : ℝ) / (2 ^ shardBits m : ℝ)|}
  have hload (θ : QuotientPermSeed a m b_aux c n) (σ : Fin (2 ^ shardBits m)) :
      #(S.filter fun u => bucketShard m (concreteBucket hma θ u) = σ) =
        bucketLoad (h_sh θ.top θ.botShard) S_sh σ := by
    unfold bucketLoad S_sh
    rw [filter_map, card_map]
    refine congrArg Finset.card (filter_congr fun u _ => ?_)
    have hsh :
        bucketShard m (concreteBucket hma θ u) = caseBShard hma (concreteRounds θ).caseB u := by
      simp [concreteBucket, quotientPermEquiv, hnotA, caseBShard]
    rw [hsh, caseBShard_eq_feistelHead]
    rfl
  have hm_eq : (PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).map (Prod.fst ∘ eSh) =
      PMF.uniformOfFintype (Top × BotSh) := by
    rw [← PMF.map_comp, uniformOfFintype_map_equiv eSh, uniformOfFintype_prod_map_fst]
  have hev : (PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).toOuterMeasure
      {θ | ∃ σ : Fin (2 ^ shardBits m),
        a_dev ≤ |(#(S.filter fun u => bucketShard m (concreteBucket hma θ u) = σ) : ℝ) -
          (#S : ℝ) / (2 ^ shardBits m : ℝ)|} =
      (PMF.uniformOfFintype (Top × BotSh)).toOuterMeasure E_pair := by
    rw [← hm_eq, PMF.toOuterMeasure_map_apply]
    congr 1; ext θ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply, Equiv.coe_fn_mk,
      hload, hS_card, E_pair, eSh]
  rw [hev]
  have hp := prob_doubleTab_bucketLoad_outside_le hn ha'_ub hk_pos hk_ind S_sh
    (by rwa [hS_card]) ha_dev
  simpa only [E_pair, h_sh, hS_card] using hp

private theorem prob_concreteQuotientPerm_master_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hn : quotientPermThreshold c ≤ n)
    (hm_lo : bucketIndexBits n ≤ m) (hm_hi : m ≤ 8 * quotientPermCharBits n)
    {S T : Finset (Fin (2 ^ a))} (hS : #S ≤ n) (hTS : T ⊆ S) (hT : #T ≤ quotientPermInd c n)
    (σ : Fin (2 ^ shardBits m))
    (B : Fin (2 ^ a) → Finset (Fin (2 ^ m)))
    (hB : ∀ u ∈ T, ∀ b ∈ B u, bucketShard m b = σ)
    (A : Fin (2 ^ a) → Finset (Fin (2 ^ b_aux)))
    {c_mult : ℝ} (hc_mult : 1 ≤ c_mult)
    (hcaseB_emb : ¬ (m + caseAGap c n ≤ a) →
      ∀ hinj : Set.InjOn (keySuffix hma) (T : Set (Fin (2 ^ a))),
        haveI : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) :=
          ⟨⟨fun u => keySuffix hma u.1, fun u₁ u₂ h => Subtype.ext (hinj u₁.2 u₂.2 h)⟩⟩
        ((1 : ℝ) / (2 ^ shardBits m : ℝ)) ^ Fintype.card T *
          ((PMF.uniformOfFintype (T ↪ Fin (2 ^ suffixBits a m))).toOuterMeasure
            {e | ∀ i : T, e i ∈ intraShardSuffixSet hma (B i.1)}).toReal *
          (∏ u : T, ((#(A u.1) : ℝ) / (2 ^ b_aux : ℝ))) ≤
          c_mult * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ))))) :
    ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).toOuterMeasure
      {θ | ∀ u ∈ T, concreteBucket hma θ u ∈ B u ∧ concreteAux hma θ u ∈ A u}).toReal ≤
      c_mult * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) +
        1 / (n : ℝ) ^ (c + 1) := by
  classical
  let μ := PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)
  have h4n : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (four_le_quotientPermThreshold c).trans hn
  have hprod_nonneg : 0 ≤ ∏ u ∈ T,
      (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ))) :=
    Finset.prod_nonneg fun _ _ => by positivity
  by_cases hgap : m + caseAGap c n ≤ a
  · let Φ (θ : QuotientPermSeed a m b_aux c n) (u : T) :=
      (concreteBucket hma θ u.1, concreteAux hma θ u.1)
    let E : Set (T → Fin (2 ^ m) × Fin (2 ^ b_aux)) :=
      {f | ∀ u : T, (f u).1 ∈ B u.1 ∧ (f u).2 ∈ A u.1}
    have hmap : μ.toOuterMeasure
        {θ | ∀ u ∈ T, concreteBucket hma θ u ∈ B u ∧ concreteAux hma θ u ∈ A u} =
        (μ.map Φ).toOuterMeasure E := by
      rw [PMF.toOuterMeasure_map_apply]; congr 1; ext θ; simp [Φ, E]
    rw [hmap]
    have habs := abs_toOuterMeasure_toReal_sub_le_dist (μ.map Φ)
      (PMF.uniformOfFintype (T → Fin (2 ^ m) × Fin (2 ^ b_aux))) E
    have hd := dist_concreteCaseA_restrict_le (b_aux := b_aux) hma hgap hn hS hTS hT
    have hunif := prob_uniformOfFintype_pi_prod_forall_mem
      (T := T) (fun u => B u.1) (fun u => A u.1)
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hunif
    rw [Finset.prod_coe_sort T
      (fun u => (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ))))] at hunif
    have h1_le : (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) ≤
        c_mult * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) :=
      le_mul_of_one_le_left hprod_nonneg hc_mult
    linarith [(le_abs_self _).trans habs]
  · have hcaseB : a < m + caseAGap c n := not_le.mp hgap
    by_cases hinj : Set.InjOn (keySuffix hma) (T : Set (Fin (2 ^ a)))
    · let yEmb : T ↪ Fin (2 ^ suffixBits a m) :=
        ⟨fun u => keySuffix hma u.1, fun u₁ u₂ h => Subtype.ext (hinj u₁.2 u₂.2 h)⟩
      have : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
      let Q (u : T) := intraShardSuffixSet hma (B u.1)
      let Ψ (θ : QuotientPermSeed a m b_aux c n) :=
        ((fun u : T => (bitDomainEquiv (shardBits_le_of_le hma) u.1).1 ^^^
            (concreteRounds θ).caseB.fShard (yEmb u)),
          ((Equiv.refl T).embeddingCongr
            (nrComposedEquiv (suffixBits a m) (nrRounds c) (concreteRounds θ).caseB.nrBlocks) yEmb,
            fun u : T => concreteAux hma θ u.1))
      let S_all : Set ((T → Fin (2 ^ shardBits m)) ×
          ((T ↪ Fin (2 ^ suffixBits a m)) × (T → Fin (2 ^ b_aux)))) :=
        {p | let (sh, emb, aux) := p; ∀ u : T, sh u = σ ∧ emb u ∈ Q u ∧ aux u ∈ A u.1}
      have hmap : μ.toOuterMeasure
          {θ | ∀ u ∈ T, concreteBucket hma θ u ∈ B u ∧ concreteAux hma θ u ∈ A u} =
          (μ.map Ψ).toOuterMeasure S_all := by
        rw [PMF.toOuterMeasure_map_apply]; congr 1; ext θ
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, S_all, Subtype.forall]
        refine forall₂_congr fun u hu => ?_
        have hbk : concreteBucket hma θ u =
            (shardLocalMergeEquiv a m ((Ψ θ).1 ⟨u, hu⟩,
              suffixSplitEquiv hma ((Ψ θ).2.1 ⟨u, hu⟩))).1 := by
          simp [concreteBucket, quotientPermEquiv, hgap, caseBEquiv, Ψ, yEmb, keySuffix,
            feistelPair, feistelHead]
        rw [hbk, mem_intraShardSuffixSet_iff hma σ (hB u hu)]
        exact and_assoc
      rw [hmap]
      have habs := abs_toOuterMeasure_toReal_sub_le_dist (μ.map Ψ) (PMF.uniformOfFintype _) S_all
      have hd := dist_concreteCaseB_shardTuple_le (b_aux := b_aux) hma hcaseB hn hm_lo hm_hi hT yEmb
      have hprod := prob_shardTuple_event_eq (T := T) σ Q (fun u => A u.1)
      have hmain := hcaseB_emb hgap hinj
      have hd_le : 1 / (4 * (n : ℝ) ^ (c + 2)) ≤ 1 / (n : ℝ) ^ (c + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        calc (n : ℝ) ^ (c + 1) ≤ (n : ℝ) ^ (c + 1) * (4 * (n : ℝ)) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
          _ = 4 * (n : ℝ) ^ (c + 2) := by ring
      linarith [(le_abs_self _).trans habs]
    · have hemp : {θ : QuotientPermSeed a m b_aux c n |
          ∀ u ∈ T, concreteBucket hma θ u ∈ B u ∧ concreteAux hma θ u ∈ A u} = ∅ := by
        ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hmem; apply hinj
        refine (injOn_yR_of_caseBShard_eq hma (concreteRounds θ).caseB σ).mono fun u hu => ?_
        have h1 := (hmem u hu).1
        simp only [concreteBucket, quotientPermEquiv, hgap, ↓reduceIte] at h1
        exact hB u hu _ h1
      have hzero : univ.filter (· ∈ (∅ : Set (QuotientPermSeed a m b_aux c n))) = ∅ :=
        filter_eq_empty_iff.mpr fun _ _ h => h
      rw [hemp, toOuterMeasure_uniformOfFintype_toReal, hzero, Finset.card_empty, Nat.cast_zero,
        zero_div]
      have hc_nn : 0 ≤ c_mult := by linarith
      exact add_nonneg (mul_nonneg hc_nn hprod_nonneg) (by positivity)

/-- **Unified `Fin (2 ^ a)` multiplicative tail bound across Case A and Case B** (shared intra-shard
target bucket set `B` and auxiliary set `A`). -/
theorem prob_concreteQuotientPerm_forall_mem_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hn : quotientPermThreshold c ≤ n)
    (hm_lo : bucketIndexBits n ≤ m) (hm_hi : m ≤ 8 * quotientPermCharBits n)
    {S T : Finset (Fin (2 ^ a))} (hS : #S ≤ n) (hTS : T ⊆ S) (hT : #T ≤ quotientPermInd c n)
    (σ : Fin (2 ^ shardBits m)) (B : Finset (Fin (2 ^ m))) (hB : ∀ b ∈ B, bucketShard m b = σ)
    (A : Finset (Fin (2 ^ b_aux))) :
    ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).toOuterMeasure
      {θ | ∀ u ∈ T, concreteBucket hma θ u ∈ B ∧ concreteAux hma θ u ∈ A}).toReal ≤
      (((#B : ℝ) / (2 ^ m : ℝ)) * ((#A : ℝ) / (2 ^ b_aux : ℝ))) ^ #T +
        1 / (n : ℝ) ^ (c + 1) := by
  classical
  have hmst := prob_concreteQuotientPerm_master_le hma hn hm_lo hm_hi hS hTS hT σ
    (fun _ => B) (fun _ _ => hB) (fun _ => A) (c_mult := 1) le_rfl fun _ hinj => by
      let yEmb : T ↪ Fin (2 ^ suffixBits a m) :=
        ⟨fun u => keySuffix hma u.1, fun u₁ u₂ h => Subtype.ext (hinj u₁.2 u₂.2 h)⟩
      have : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
      let Q₀ := intraShardSuffixSet hma B
      have hcardT : Fintype.card T ≤ Fintype.card (Fin (2 ^ suffixBits a m)) :=
        Fintype.card_le_of_injective yEmb yEmb.injective
      have hemb := prob_uniformOfFintype_embedding_forall_mem_le hcardT Q₀
      simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hemb
      have hQ_card : (#Q₀ : ℝ) = ((#B * 2 ^ (a - m) : ℕ) : ℝ) :=
        congrArg Nat.cast (card_intraShardSuffixSet hma σ hB)
      calc _ ≤ ((1 : ℝ) / (2 ^ shardBits m : ℝ)) ^ Fintype.card T *
              (((#Q₀ : ℝ) / (2 ^ suffixBits a m : ℝ)) ^ Fintype.card T) *
              (((#A : ℝ) / (2 ^ b_aux : ℝ)) ^ Fintype.card T) := by
            simp only [Finset.prod_const, Finset.card_univ]; gcongr
        _ = 1 * (∏ _u ∈ T, (((#B : ℝ) / (2 ^ m : ℝ)) * ((#A : ℝ) / (2 ^ b_aux : ℝ)))) := by
            rw [one_mul, Finset.prod_const, hQ_card, Fintype.card_coe, ← mul_pow, ← mul_pow,
              shard_suffix_ratio_eq hma #B]
  simpa only [one_mul, Finset.prod_const] using hmst

/-- **Per-key `Fin (2 ^ a)` multiplicative tail bound across Case A and Case B** (per-key
intra-shard target bucket sets `B u` satisfying `∀ u ∈ T, ∀ b ∈ B u, bucketShard m b = σ`,
factor `2`). -/
theorem prob_concreteQuotientPerm_forall_mem_perKey_le {a m b_aux c n : ℕ}
    (hma : m ≤ a) (hn : quotientPermThreshold c ≤ n)
    (hm_lo : bucketIndexBits n ≤ m) (hm_hi : m ≤ 8 * quotientPermCharBits n)
    {S T : Finset (Fin (2 ^ a))} (hS : #S ≤ n) (hTS : T ⊆ S) (hT : #T ≤ quotientPermInd c n)
    (σ : Fin (2 ^ shardBits m))
    (B : Fin (2 ^ a) → Finset (Fin (2 ^ m)))
    (hB : ∀ u ∈ T, ∀ b ∈ B u, bucketShard m b = σ)
    (A : Fin (2 ^ a) → Finset (Fin (2 ^ b_aux))) :
    ((PMF.uniformOfFintype (QuotientPermSeed a m b_aux c n)).toOuterMeasure
      {θ | ∀ u ∈ T, concreteBucket hma θ u ∈ B u ∧ concreteAux hma θ u ∈ A u}).toReal ≤
      2 * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) +
        1 / (n : ℝ) ^ (c + 1) := by
  classical
  exact prob_concreteQuotientPerm_master_le hma hn hm_lo hm_hi hS hTS hT σ B hB A
    (c_mult := 2) (by norm_num) fun _ hinj => by
      let yEmb : T ↪ Fin (2 ^ suffixBits a m) :=
        ⟨fun u => keySuffix hma u.1, fun u₁ u₂ h => Subtype.ext (hinj u₁.2 u₂.2 h)⟩
      have : Nonempty (T ↪ Fin (2 ^ suffixBits a m)) := ⟨yEmb⟩
      let Q (u : T) := intraShardSuffixSet hma (B u.1)
      obtain ⟨_, _, _, h2κ2⟩ := quotientPermInd_le_self_of_threshold hn
      have ha'_b : quotientPermCharBits n ≤ suffixBits a m := by
        unfold bucketIndexBits at hm_lo; dsimp only [suffixBits, shardBits]; omega
      have hcard2 : 2 * (Fintype.card T) ^ 2 ≤ Fintype.card (Fin (2 ^ suffixBits a m)) := by
        rw [Fintype.card_coe, Fintype.card_fin]
        exact (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hT 2)).trans
          (h2κ2.trans (Nat.pow_le_pow_right (by decide) ha'_b))
      have hemb := prob_uniformOfFintype_embedding_forall_mem_perKey_le hcard2 Q
      simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hemb
      calc _ ≤ ((1 : ℝ) / (2 ^ shardBits m : ℝ)) ^ Fintype.card T *
              (2 * ∏ u : T, ((#(Q u) : ℝ) / (2 ^ suffixBits a m : ℝ))) *
              (∏ u : T, ((#(A u.1) : ℝ) / (2 ^ b_aux : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hemb (by positivity))
              (Finset.prod_nonneg fun _ _ => by positivity)
        _ = 2 * (((∏ _u : T, ((1 : ℝ) / (2 ^ shardBits m : ℝ))) *
              (∏ u : T, ((#(Q u) : ℝ) / (2 ^ suffixBits a m : ℝ)))) *
              (∏ u : T, ((#(A u.1) : ℝ) / (2 ^ b_aux : ℝ)))) := by
            rw [Finset.prod_const, Finset.card_univ]; ring
        _ = 2 * ∏ u : T, ((((1 : ℝ) / (2 ^ shardBits m : ℝ)) *
              ((#(Q u) : ℝ) / (2 ^ suffixBits a m : ℝ))) *
              ((#(A u.1) : ℝ) / (2 ^ b_aux : ℝ))) := by
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        _ = 2 * ∏ u : T, (((#(B u.1) : ℝ) / (2 ^ m : ℝ)) *
              ((#(A u.1) : ℝ) / (2 ^ b_aux : ℝ))) := by
            congr 1; refine Finset.prod_congr rfl fun u _ => ?_
            have hQc : (#(Q u) : ℝ) = ((#(B u.1) * 2 ^ (a - m) : ℕ) : ℝ) :=
              congrArg Nat.cast (card_intraShardSuffixSet hma σ (hB u.1 u.2))
            rw [hQc, shard_suffix_ratio_eq hma #(B u.1)]
        _ = 2 * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ m : ℝ)) *
              ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) := by
            rw [Finset.prod_coe_sort T
              (fun u => (((#(B u) : ℝ) / (2 ^ m : ℝ)) * ((#(A u) : ℝ) / (2 ^ b_aux : ℝ))))]

/-- Full-quotient bucket index `Fin (2 ^ bucketIndexBits n)` of `u : Fin U` (`n ≤ U`). -/
@[expose] def fullBucket {U b_aux c n : ℕ} (hnU : n ≤ U)
    (θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)
    (u : Fin U) : Fin (2 ^ bucketIndexBits n) :=
  concreteBucket (bucketIndexBits_le_keyBits hnU) θ (embedKey u)

/-- Full-quotient stored quotient `Fin (2 ^ fullQuotBits U n)` of `u : Fin U` (`n ≤ U`). -/
@[expose] def fullQuot {U b_aux c n : ℕ} (hnU : n ≤ U)
    (θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)
    (u : Fin U) : Fin (2 ^ fullQuotBits U n) :=
  concreteQuot (bucketIndexBits_le_keyBits hnU) θ (embedKey u)

/-- Inverse key-reconstruction map `(bucket, quot) ↦ Fin (2 ^ keyBits U)` for `n ≤ U`. -/
@[expose] def fullDecode {U b_aux c n : ℕ} (hnU : n ≤ U)
    (θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)
    (p : Fin (2 ^ bucketIndexBits n) × Fin (2 ^ fullQuotBits U n)) :
    Fin (2 ^ FeistelQuotient.keyBits U) :=
  quotientPermDecode (bucketIndexBits_le_keyBits hnU) (concreteRounds θ) p

@[simp] theorem fullDecode_fullBucket_fullQuot {U b_aux c n : ℕ} (hnU : n ≤ U)
    (θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n) (u : Fin U) :
    fullDecode hnU θ (fullBucket hnU θ u, fullQuot hnU θ u) = embedKey u :=
  quotientPermDecode_quotientPermEncode (bucketIndexBits_le_keyBits hnU) (concreteRounds θ)
    (embedKey u)

/-- Auxiliary `b_aux`-bit hash accompanying `fullBucket` for `u : Fin U` (`n ≤ U`). -/
@[expose] def fullAux {U b_aux c n : ℕ} (hnU : n ≤ U)
    (θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)
    (u : Fin U) : Fin (2 ^ b_aux) :=
  concreteAux (bucketIndexBits_le_keyBits hnU) θ (embedKey u)

private theorem bucketIndexBits_le_eight_mul_charBits (n : ℕ) :
    bucketIndexBits n ≤ 8 * quotientPermCharBits n := by
  rw [quotientPermCharBits_eq]; unfold bucketIndexBits; omega

/-- **Universal `Fin U` multiplicative tail bound across every `U ≥ n` above
`quotientPermThreshold c`** (shared intra-shard target bucket set `B` with
`∀ b ∈ B, bucketShard (bucketIndexBits n) b = σ` and auxiliary set `A`, factor `1`, without
assuming `U ≥ n ^ (1 + Ω(1))` or `log U ≤ poly(log n)`). -/
theorem prob_fullQuotientPerm_forall_mem_le {U b_aux c n : ℕ}
    (hnU : n ≤ U) (hn : quotientPermThreshold c ≤ n)
    {S T : Finset (Fin U)} (hS : #S ≤ n) (hTS : T ⊆ S) (hT : #T ≤ quotientPermInd c n)
    (σ : Fin (2 ^ shardBits (bucketIndexBits n)))
    (B : Finset (Fin (2 ^ bucketIndexBits n)))
    (hB : ∀ b ∈ B, bucketShard (bucketIndexBits n) b = σ)
    (A : Finset (Fin (2 ^ b_aux))) :
    ((PMF.uniformOfFintype
        (QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)).toOuterMeasure
      {θ | ∀ u ∈ T, fullBucket hnU θ u ∈ B ∧ fullAux hnU θ u ∈ A}).toReal ≤
      (((#B : ℝ) / (2 ^ bucketIndexBits n : ℝ)) * ((#A : ℝ) / (2 ^ b_aux : ℝ))) ^ #T +
        1 / (n : ℝ) ^ (c + 1) := by
  let emb : Fin U ↪ Fin (2 ^ FeistelQuotient.keyBits U) := ⟨embedKey, embedKey_injective U⟩
  let S' := S.map emb
  let T' := T.map emb
  have hS' : #S' ≤ n := (card_map emb).trans_le hS
  have hTS' : T' ⊆ S' := map_subset_map.mpr hTS
  have hT' : #T' ≤ quotientPermInd c n := (card_map emb).trans_le hT
  have hev : ({θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n |
      ∀ u ∈ T, fullBucket hnU θ u ∈ B ∧ fullAux hnU θ u ∈ A}) =
      {θ | ∀ u' ∈ T', concreteBucket (bucketIndexBits_le_keyBits hnU) θ u' ∈ B ∧
        concreteAux (bucketIndexBits_le_keyBits hnU) θ u' ∈ A} := by
    ext θ; simp [T', emb, fullBucket, fullAux]
  rw [hev, ← card_map emb]
  exact prob_concreteQuotientPerm_forall_mem_le (bucketIndexBits_le_keyBits hnU) hn le_rfl
    (bucketIndexBits_le_eight_mul_charBits n) hS' hTS' hT' σ B hB A

/-- **Universal per-key `Fin U` multiplicative tail bound across every `U ≥ n` above
`quotientPermThreshold c`** (per-key intra-shard target bucket sets `B u` satisfying
`∀ u ∈ T, ∀ b ∈ B u, bucketShard (bucketIndexBits n) b = σ` and auxiliary sets `A u`, factor `2`,
without assuming `U ≥ n ^ (1 + Ω(1))` or `log U ≤ poly(log n)`). -/
theorem prob_fullQuotientPerm_forall_mem_perKey_le {U b_aux c n : ℕ}
    (hnU : n ≤ U) (hn : quotientPermThreshold c ≤ n)
    {S T : Finset (Fin U)} (hS : #S ≤ n) (hTS : T ⊆ S) (hT : #T ≤ quotientPermInd c n)
    (σ : Fin (2 ^ shardBits (bucketIndexBits n)))
    (B : Fin U → Finset (Fin (2 ^ bucketIndexBits n)))
    (hB : ∀ u ∈ T, ∀ b ∈ B u, bucketShard (bucketIndexBits n) b = σ)
    (A : Fin U → Finset (Fin (2 ^ b_aux))) :
    ((PMF.uniformOfFintype
        (QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n)).toOuterMeasure
      {θ | ∀ u ∈ T, fullBucket hnU θ u ∈ B u ∧ fullAux hnU θ u ∈ A u}).toReal ≤
      2 * (∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ bucketIndexBits n : ℝ)) *
        ((#(A u) : ℝ) / (2 ^ b_aux : ℝ)))) +
        1 / (n : ℝ) ^ (c + 1) := by
  classical
  let emb : Fin U ↪ Fin (2 ^ FeistelQuotient.keyBits U) := ⟨embedKey, embedKey_injective U⟩
  let S' := S.map emb
  let T' := T.map emb
  let B' (u' : Fin (2 ^ FeistelQuotient.keyBits U)) : Finset (Fin (2 ^ bucketIndexBits n)) :=
    if h : u'.val < U then B ⟨u'.val, h⟩ else ∅
  let A' (u' : Fin (2 ^ FeistelQuotient.keyBits U)) : Finset (Fin (2 ^ b_aux)) :=
    if h : u'.val < U then A ⟨u'.val, h⟩ else ∅
  have hB_emb (u : Fin U) : B' (embedKey u) = B u := by simp [B', u.isLt]
  have hA_emb (u : Fin U) : A' (embedKey u) = A u := by simp [A', u.isLt]
  have hB' : ∀ u' ∈ T', ∀ b ∈ B' u', bucketShard (bucketIndexBits n) b = σ := by
    intro u' hu' b hb
    rcases mem_map.mp hu' with ⟨u, hu, rfl⟩
    dsimp only [emb, Function.Embedding.coeFn_mk] at hb
    rw [hB_emb] at hb
    exact hB u hu b hb
  have hev : ({θ : QuotientPermSeed (FeistelQuotient.keyBits U) (bucketIndexBits n) b_aux c n |
      ∀ u ∈ T, fullBucket hnU θ u ∈ B u ∧ fullAux hnU θ u ∈ A u}) =
      {θ | ∀ u' ∈ T', concreteBucket (bucketIndexBits_le_keyBits hnU) θ u' ∈ B' u' ∧
        concreteAux (bucketIndexBits_le_keyBits hnU) θ u' ∈ A' u'} := by
    ext θ; simp [T', hB_emb, hA_emb, fullBucket, fullAux, emb]
  have hprod_eq : (∏ u' ∈ T', (((#(B' u') : ℝ) / (2 ^ bucketIndexBits n : ℝ)) *
      ((#(A' u') : ℝ) / (2 ^ b_aux : ℝ)))) =
      ∏ u ∈ T, (((#(B u) : ℝ) / (2 ^ bucketIndexBits n : ℝ)) *
        ((#(A u) : ℝ) / (2 ^ b_aux : ℝ))) := by
    rw [Finset.prod_map]; simp [emb, hB_emb, hA_emb]
  rw [hev, ← hprod_eq]
  exact prob_concreteQuotientPerm_forall_mem_perKey_le (bucketIndexBits_le_keyBits hnU) hn le_rfl
    (bucketIndexBits_le_eight_mul_charBits n) ((card_map emb).trans_le hS)
    (map_subset_map.mpr hTS) ((card_map emb).trans_le hT) σ B' hB' A'

end Cslib.DataStructure.Dictionary.KickTree
