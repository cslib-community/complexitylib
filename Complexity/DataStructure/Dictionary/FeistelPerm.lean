/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.FeistelQuotient
public import Complexity.Probability.KWiseIndependent.DoubleTabulation
public import Complexity.Probability.KWiseIndependent.Trinomial
public import Complexity.Probability.PMF.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.Power
import Complexity.Probability.KWiseIndependent.Concentration
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Assumption-free Feistel permutation families (`Lemmas 5.1–5.2` and `Corollaries B.5–B.6`)

This module formalizes the one-round Feistel hash permutation families used for multi-level child
routing (`ℋ_ℓ^ch`) and key-ID compression (`ℋ_ℓ^id`) in Tianxiao Li, Jingxun Liang, Huacheng Yu,
and Renfei Zhou, *"Dynamic Dictionary with Subconstant Wasted Bits per Key"*, *Proc. 2024 Annual
ACM-SIAM Symposium on Discrete Algorithms (SODA 2024)*, pp. 171–207 [LiLiangYuZhou2024]
(`arXiv:2310.20536v1`, Section 5.4, PDF pp. 30–33 / printed pp. 29–32, Lemmas 5.1–5.2; Appendix B,
PDF pp. 41–44 / printed pp. 40–43, Definition B.1, Claim B.2, Claim B.3, Theorem B.4, and
Corollaries B.5–B.6).

## Source statements, notation mapping, and proof adaptations

In [LiLiangYuZhou2024] (`arXiv:2310.20536v1`):
* **Mixed-domain one-round Feistel permutation (Definition B.1, PDF p. 41 / printed p. 40;
  Corollaries B.5–B.6, PDF pp. 43–44 / printed pp. 42–43; cf. [LubyRackoff1988])**:
  For a round function `f : α → Fin (2 ^ s)` (specialized to `α = Fin T` on `{0, 1}^s × Fin T`
  and to `α = Fin (2 ^ (L - s))` on `{0, 1}^L`), `feistelPair f (x_L, x_R) = (x_L ^^^ f x_R, x_R)`
  is an exact involution (`feistelPair_involutive`, `feistelPairEquiv`). On flat integers
  `Fin (2 ^ s * T)`, `mixedDomainEquiv s T` splits `u` into `(u % 2 ^ s, u / 2 ^ s)` via
  `FeistelQuotient.keyLow` and `FeistelQuotient.keyQuotient`, so extracting `(x_L, x_R)` and
  reconstructing `x_L + 2 ^ s * x_R` reduce to bit-mask and bit-shift operations even when `T` is
  not a power of two (top level `ℓ = 0`, where `B_0 = 2 ^ s` is a power of two while
  `T = 2 ^ I_1 * Q_1` or `Q_1` is general).
* **Child-router Feistel family `ℋ_ℓ^ch` (Lemma 5.1, PDF p. 32 / printed p. 31 & PDF pp. 41–42 /
  printed pp. 40–41; Claim B.3, PDF pp. 41–42 / printed pp. 40–41; Corollary B.5, PDF p. 43 /
  printed p. 42)**:
  Grouping `S : Finset (Fin (2 ^ s) × Fin T)` by `z = x.2 ∈ S.image Prod.snd`, distinct keys with
  the same right part `z` never collide in `feistelHead f` (`feistelHead_ne_of_snd_eq_of_ne`), so
  `bucketLoad f S b = #{z ∈ S.image Prod.snd | (b ^^^ f z, z) ∈ S}` is a sum of `{0, 1}` indicators
  determined by distinct coordinates `f z` with total mean `#S / 2 ^ s`. Instantiating `f`
  unconditionally via Mikkel Thorup's double tabulation [Thorup2013] (`ChildRouterSeed c q b s`)
  bounds bucket-load deviations by `δ_dt + 2 ^ (s + 1) * (3 * m * μ / a ^ 2) ^ m` and yields failure
  probability `≤ 1 / (4 * (#S) ^ 2)` for the `(1 / 5) * (#S / 2 ^ s) ^ (2 / 3)` window.
* **ID-compressor Feistel family `ℋ_ℓ^id` (Lemma 5.2, PDF p. 33 / printed p. 32 & PDF pp. 42–43 /
  printed pp. 41–42; Corollary B.6, PDF pp. 43–44 / printed pp. 42–43)**:
  Under any pairwise independent round family `h : ι → Fin T → Fin (2 ^ s)` [CarterWegman1979],
  [WegmanCarter1981], keys sharing `x.2` never collide and keys with `x₁.2 ≠ x₂.2` collide in
  `feistelHead` with probability `1 / 2 ^ s`, giving non-injectivity probability
  `≤ #S * (#S - 1) / (2 * 2 ^ s) ≤ (#S) ^ 2 / (2 * 2 ^ s) ≤ (#S) ^ 2 / 2 ^ s` (and
  `≤ 2 / n_next ^ 2` when `n_bar ^ 2 * n_next ^ 2 ≤ 4 * 2 ^ s`). Instantiating `f` unconditionally
  via `2`-wise trinomial polynomial hashing (`IdCompressorSeed s T`, `trinomialPolyHash`) uses
  `2 * trinomialDeg T s ≤ 6 * max ⌈log₂ max(T, 2)⌉ (max s 1) = O(s + log T)` seed bits.
* **Adaptations and scope**:
  - Instead of invoking Theorem B.4 ([LiLiangYuZhou2024], PDF p. 42 / printed p. 41;
    [SchmidtSiegelSrinivasan1995, Theorem 5]), `dens_bucketLoad_sub_ge_le` uses the elementary
    variance-sensitive `2m`-th central moment and Markov tail bounds
    `Cslib.Probability.expect_sum_sub_expect_pow_le` and
    `Cslib.Probability.dens_abs_sum_sub_expect_le` from
    `Complexity.Probability.KWiseIndependent.Concentration` (extending the limited-independence
    moment method of [BellareRompel1994]), giving
    `Pr[|∑ (g_z - E[g_z])| ≥ a] ≤ 2 * (3 * m * μ / a ^ 2) ^ m` whenever `2 * m ≤ 3 * μ`.
  - Lemma 5.1(c) and Corollary B.5(c) state `n ≥ 2 ^ s * s ^ 4` and in Claim B.3's proof
    ([LiLiangYuZhou2024], PDF p. 42 / printed p. 41) assume sufficiently large `s` (for
    `s = 1, n = 16`, `[8 - 4/5, 8 + 4/5]` contains only `8`, so on any 16 keys with distinct right
    coordinates a random round function fails with probability `> 4/5 > 1 / (4 * 16 ^ 2)`). We
    expose the quantitative hypothesis `2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S` (applicable
    down to `s = 1` once `#S` is large enough; Section 5.4's tree parameter schedule is not
    formalized in this module) and prove that `2 ^ s * s ^ 4 ≤ #S` implies it for
    `s ≥ childRouterMinS` (`childRouter_conc_of_two_pow_mul_pow_four_le`).
  - Replacing Claim B.2's idealized asymptotic independence with Thorup's high-probability double
    tabulation [Thorup2013] introduces an explicit finite-size premise
    `childRouterThreshold ε_inv α_inv ≤ #S` in the closed-form theorems
    `dens_childRouter_bucketLoad_outside_le_of_threshold` and
    `dens_childRouterBit_bucketLoad_outside_le` — an astronomically large constant absent from
    Lemma 5.1(c) and Corollary B.5(c) in [LiLiangYuZhou2024]. Below that threshold, the parametric
    `2m`-wise bound `dens_exists_bucketLoad_sub_ge_le` has no `childRouterThreshold` requirement
    when paired with an exact `2m`-wise family such as `trinomialPolyHash`.
  - Part (a) of Lemmas 5.1–5.2 and Corollaries B.5–B.6 — constant-time Word-RAM evaluation of the
    Feistel permutation and its inverse — is not proved in this pure probability and combinatorics
    module. Word-RAM evaluation and resampling certificates for the underlying `doubleTabHash` and
    `trinomialPolyHash` round functions live in
    `Complexity.DataStructure.HashFamily.WordRAM.DoubleTabulation` and
    `Complexity.DataStructure.HashFamily.WordRAM.KWise`; Feistel wrapper evaluation, the end-to-end
    dictionary, super-polynomial-`U` universe reduction, and Section 4 / Appendix C adapter-tree
    hashing belong to separate modules.

## Main definitions

* `Cslib.DataStructure.Dictionary.FeistelPerm.feistelHead`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelPair`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.recoverLeft`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelPairEquiv`: one-round Feistel head projection,
  involution, left-coordinate recovery, and `Equiv.Perm` on `Fin (2 ^ s) × α`.
* `Cslib.DataStructure.Dictionary.FeistelPerm.mixedDomainEquiv`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelMixedEquiv`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.bitDomainEquiv`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelBitEquiv`: flat bijections on `Fin (2 ^ s * T)`
  and `Fin (2 ^ L)`.
* `Cslib.DataStructure.Dictionary.FeistelPerm.bucketLoad`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.ChildRouterSeed`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterSeedBits`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterRound`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterPerm`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterMixedPerm`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterBitPerm`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterHalfInd`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterChars`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterCharBits`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterRep`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterSpaceConst`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterThreshold`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterMinS`: child-router Feistel family and
  parameter schedule (`Lemma 5.1`, `Corollary B.5`).
* `Cslib.DataStructure.Dictionary.FeistelPerm.IdCompressorSeed`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorSeedBits`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorRound`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorHead`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorPerm`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorMixedPerm`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorBitPerm`: `2`-wise trinomial ID-compressor
  Feistel family (`Lemma 5.2`, `Corollary B.6`).

## Main results

* `Cslib.DataStructure.Dictionary.FeistelPerm.feistelPair_involutive`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.recoverLeft_feistelHead`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelHead_ne_of_snd_eq_of_ne`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.injOn_snd_of_feistelHead_eq`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelMixedEquiv_involutive`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.feistelBitEquiv_involutive`: exact involutivity,
  lossless recovery, and right-part uniqueness per bucket.
* `Cslib.DataStructure.Dictionary.FeistelPerm.dens_bucketLoad_sub_ge_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_exists_bucketLoad_sub_ge_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_childRouter_exists_bucketLoad_sub_ge_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_childRouter_bucketLoad_outside_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.prob_childRouter_bucketLoad_outside_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouterSeedBits_pow_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_childRouter_bucketLoad_outside_le_of_threshold`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_childRouterBit_bucketLoad_outside_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.childRouter_conc_of_two_pow_mul_pow_four_le`:
  `Claim B.3`, `Corollary B.5`, and `Lemma 5.1` bucket-load concentration and seed-space bounds.
* `Cslib.DataStructure.Dictionary.FeistelPerm.dens_not_injOn_feistelHead_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.idCompressorSeedBits_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.isKWiseIndependentHash_idCompressorRound`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_not_injOn_idCompressorHead_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.prob_not_injOn_idCompressorHead_le`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_not_injOn_idCompressorHead_le_two_div_sq`,
  `Cslib.DataStructure.Dictionary.FeistelPerm.dens_not_injOn_idCompressorBit_le`: `Corollary B.6`
  and `Lemma 5.2` collision and seed-space bounds.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
  Key*][LiLiangYuZhou2024]
* [J. P. Schmidt, A. Siegel, and A. Srinivasan, *Chernoff–Hoeffding Bounds for Applications with
  Limited Independence*][SchmidtSiegelSrinivasan1995]
* [M. Luby and C. Rackoff, *How to Construct Pseudorandom Permutations from Pseudorandom
  Functions*][LubyRackoff1988]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
* [M. Bellare and J. Rompel, *Randomness-Efficient Oblivious Sampling*][BellareRompel1994]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [J. L. Carter and M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [M. N. Wegman and J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*, Claim 5.7][ArbitmanNaorSegev2010]
* [M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, *Iceberg Hashing:
  Optimizing Many Hash-Table Criteria at Once*,
  Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]
-/

public section

namespace Cslib.DataStructure.Dictionary.FeistelPerm

open Cslib.DataStructure.Dictionary Cslib.Probability Finset Fintype
open scoped BigOperators ENNReal

/-! ## Section 1: Mixed-domain one-round Feistel involution
(`Definition B.1`, `Corollaries B.5–B.6`) -/

/-- The `s`-bit Feistel head projection `x_L ^^^ f x_R` (`ĥ(x)` in Appendix B of
[LiLiangYuZhou2024], `arXiv:2310.20536v1`, Proof of Lemma 5.1, PDF p. 41 / printed p. 40, and
Corollaries B.5–B.6, PDF pp. 43–44 / printed pp. 42–43). -/
@[expose]
def feistelHead {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) : Fin (2 ^ s) :=
  x.1 ^^^ f x.2

/-- Mixed-domain one-round Feistel map `(x_L, x_R) ↦ (x_L ^^^ f x_R, x_R)` (`Definition B.1`,
PDF p. 41 / printed p. 40, and `Corollaries B.5–B.6`, PDF pp. 43–44 / printed pp. 42–43 of
[LiLiangYuZhou2024], `arXiv:2310.20536v1`; cf. [LubyRackoff1988]). -/
@[expose]
def feistelPair {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) :
    Fin (2 ^ s) × α :=
  (feistelHead f x, x.2)

/-- Recover the left `s`-bit coordinate `x_L = b ^^^ f x_R` from `(b, x_R) = feistelPair f x`. -/
@[expose]
def recoverLeft {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (b : Fin (2 ^ s)) (xR : α) :
    Fin (2 ^ s) :=
  b ^^^ f xR

@[simp]
theorem val_feistelHead {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) :
    (feistelHead f x).val = x.1.val ^^^ (f x.2).val :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.1.isLt (f x.2).isLt)

@[simp]
theorem val_recoverLeft {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (b : Fin (2 ^ s)) (xR : α) :
    (recoverLeft f b xR).val = b.val ^^^ (f xR).val :=
  Nat.mod_eq_of_lt (Nat.xor_lt_two_pow b.isLt (f xR).isLt)

@[simp]
theorem recoverLeft_feistelHead {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) :
    recoverLeft f (feistelHead f x) x.2 = x.1 := by
  simp [recoverLeft, feistelHead]

@[simp]
theorem feistelHead_recoverLeft {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s))
    (b : Fin (2 ^ s)) (xR : α) :
    feistelHead f (recoverLeft f b xR, xR) = b := by
  simp [recoverLeft, feistelHead]

@[simp]
theorem feistelPair_feistelPair {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) :
    feistelPair f (feistelPair f x) = x := by
  ext <;> simp [feistelPair, feistelHead]

/-- Every one-round Feistel map `feistelPair f` on `Fin (2 ^ s) × α` is an exact involution. -/
theorem feistelPair_involutive {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) :
    Function.Involutive (feistelPair f) :=
  feistelPair_feistelPair f

/-- `feistelPair f` packaged as a self-inverse permutation `Equiv.Perm (Fin (2 ^ s) × α)`. -/
@[expose]
def feistelPairEquiv {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) :
    Equiv.Perm (Fin (2 ^ s) × α) where
  toFun := feistelPair f
  invFun := feistelPair f
  left_inv := feistelPair_feistelPair f
  right_inv := feistelPair_feistelPair f

@[simp]
theorem feistelPairEquiv_apply {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) (x : Fin (2 ^ s) × α) :
    feistelPairEquiv f x = feistelPair f x :=
  rfl

@[simp]
theorem feistelPairEquiv_symm {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s)) :
    (feistelPairEquiv f).symm = feistelPairEquiv f :=
  rfl

/-- Characterization of `feistelHead f x = b` via left-coordinate recovery `x.1 = b ^^^ f x.2`. -/
theorem feistelHead_eq_iff {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s))
    (x : Fin (2 ^ s) × α) (b : Fin (2 ^ s)) :
    feistelHead f x = b ↔ x.1 = b ^^^ f x.2 :=
  xor_eq_iff_left_eq x.1 (f x.2) b

/-- Two pairs with the same Feistel head and the same right coordinate are equal. -/
theorem eq_of_feistelHead_eq_of_snd_eq {s : ℕ} {α : Type*} {f : α → Fin (2 ^ s)}
    {x₁ x₂ : Fin (2 ^ s) × α}
    (hhd : feistelHead f x₁ = feistelHead f x₂) (hsnd : x₁.2 = x₂.2) :
    x₁ = x₂ := by
  ext
  · rw [← recoverLeft_feistelHead f x₁, ← recoverLeft_feistelHead f x₂, hhd, hsnd]
  · exact hsnd

/-- Distinct keys sharing the same right coordinate `x₁.2 = x₂.2` never collide under `feistelHead`
([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Appendix B, Claim B.3 proof, PDF p. 42 / printed p. 41,
and Lemma 5.2 proof, PDF p. 43 / printed p. 42). -/
theorem feistelHead_ne_of_snd_eq_of_ne {s : ℕ} {α : Type*} {f : α → Fin (2 ^ s)}
    {x₁ x₂ : Fin (2 ^ s) × α} (hsnd : x₁.2 = x₂.2) (hne : x₁ ≠ x₂) :
    feistelHead f x₁ ≠ feistelHead f x₂ :=
  fun hhd => hne (eq_of_feistelHead_eq_of_snd_eq hhd hsnd)

/-- Among all keys routed into a single child bucket `b : Fin (2 ^ s)`, the right coordinate
`Prod.snd` (`y_prim` in [LiLiangYuZhou2024], `arXiv:2310.20536v1`, Section 5.4, PDF p. 32 /
printed p. 31) is injective. -/
theorem injOn_snd_of_feistelHead_eq {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s))
    (b : Fin (2 ^ s)) :
    Set.InjOn Prod.snd {x : Fin (2 ^ s) × α | feistelHead f x = b} :=
  fun _ hx₁ _ hx₂ hsnd => eq_of_feistelHead_eq_of_snd_eq (hx₁.trans hx₂.symm) hsnd

/-- Bit-mask/shift mixed-domain equivalence `Fin (2 ^ s * T) ≃ Fin (2 ^ s) × Fin T` sending `u` to
`(u % 2 ^ s, u / 2 ^ s)` and `(x_L, x_R)` to `x_L + 2 ^ s * x_R`. -/
@[expose]
def mixedDomainEquiv (s T : ℕ) : Fin (2 ^ s * T) ≃ Fin (2 ^ s) × Fin T :=
  (finCongr (Nat.mul_comm (2 ^ s) T)).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin T) (Fin (2 ^ s))))

@[simp]
theorem val_mixedDomainEquiv_fst (s T : ℕ) (u : Fin (2 ^ s * T)) :
    (mixedDomainEquiv s T u).1.val = FeistelQuotient.keyLow s u.val :=
  rfl

@[simp]
theorem val_mixedDomainEquiv_snd (s T : ℕ) (u : Fin (2 ^ s * T)) :
    (mixedDomainEquiv s T u).2.val = FeistelQuotient.keyQuotient s u.val :=
  rfl

@[simp]
theorem val_mixedDomainEquiv_symm (s T : ℕ) (p : Fin (2 ^ s) × Fin T) :
    ((mixedDomainEquiv s T).symm p).val = p.1.val + 2 ^ s * p.2.val :=
  rfl

/-- Flat mixed-domain one-round Feistel permutation on `Fin (2 ^ s * T)` conjugated through
`mixedDomainEquiv s T`. -/
@[expose]
def feistelMixedEquiv {s T : ℕ} (f : Fin T → Fin (2 ^ s)) : Equiv.Perm (Fin (2 ^ s * T)) :=
  (mixedDomainEquiv s T).symm.permCongr (feistelPairEquiv f)

@[simp]
theorem feistelMixedEquiv_apply {s T : ℕ} (f : Fin T → Fin (2 ^ s)) (u : Fin (2 ^ s * T)) :
    feistelMixedEquiv f u = (mixedDomainEquiv s T).symm (feistelPair f (mixedDomainEquiv s T u)) :=
  rfl

theorem feistelMixedEquiv_involutive {s T : ℕ} (f : Fin T → Fin (2 ^ s)) :
    Function.Involutive (feistelMixedEquiv f) := fun u => by
  simp [feistelMixedEquiv_apply]

@[simp]
theorem feistelMixedEquiv_symm {s T : ℕ} (f : Fin T → Fin (2 ^ s)) :
    (feistelMixedEquiv f).symm = feistelMixedEquiv f :=
  Equiv.ext fun u =>
    (feistelMixedEquiv f).symm_apply_eq.mpr (feistelMixedEquiv_involutive f u).symm

/-- Bridge to `FeistelQuotient.feistelBucket`: under `mixedDomainEquiv s T`, `feistelHead` agrees
with `FeistelQuotient.feistelBucket s`. -/
theorem val_feistelHead_mixedDomainEquiv_eq_feistelBucket {s T : ℕ} (h1 : ℕ → ℕ)
    (u : Fin (2 ^ s * T)) :
    (feistelHead (fun q : Fin T => ⟨h1 q.val % 2 ^ s, Nat.mod_lt _ (Nat.two_pow_pos s)⟩)
      (mixedDomainEquiv s T u)).val = FeistelQuotient.feistelBucket s h1 u.val := by
  rw [val_feistelHead, val_mixedDomainEquiv_fst, val_mixedDomainEquiv_snd,
    FeistelQuotient.feistelBucket, Nat.xor_comm]

/-- Bridge to `FeistelQuotient.feistelReconstruct`: inverse reassembly on `Fin (2 ^ s * T)` agrees
with `FeistelQuotient.feistelReconstruct s`. -/
theorem val_mixedDomainEquiv_symm_recoverLeft_eq_feistelReconstruct {s T : ℕ} (h1 : ℕ → ℕ)
    (b : Fin (2 ^ s)) (q : Fin T) :
    ((mixedDomainEquiv s T).symm
      (recoverLeft (fun r : Fin T => ⟨h1 r.val % 2 ^ s, Nat.mod_lt _ (Nat.two_pow_pos s)⟩)
        b q, q)).val =
      FeistelQuotient.feistelReconstruct s h1 b.val q.val := by
  rw [val_mixedDomainEquiv_symm, val_recoverLeft, FeistelQuotient.feistelReconstruct,
    Nat.mod_eq_of_lt b.isLt, Nat.xor_comm b.val, Nat.mul_comm q.val, Nat.add_comm]

/-- Power-of-two domain split `Fin (2 ^ L) ≃ Fin (2 ^ s) × Fin (2 ^ (L - s))` when `s ≤ L`
(`Definition B.1` and `Lemmas 5.1–5.2`). -/
@[expose]
def bitDomainEquiv {s L : ℕ} (hsL : s ≤ L) : Fin (2 ^ L) ≃ Fin (2 ^ s) × Fin (2 ^ (L - s)) :=
  (finCongr (by rw [← Nat.pow_add, Nat.add_sub_of_le hsL])).trans
    (mixedDomainEquiv s (2 ^ (L - s)))

/-- Flat one-round Feistel permutation on `Fin (2 ^ L)` for `s ≤ L` (`Definition B.1`). -/
@[expose]
def feistelBitEquiv {s L : ℕ} (hsL : s ≤ L) (f : Fin (2 ^ (L - s)) → Fin (2 ^ s)) :
    Equiv.Perm (Fin (2 ^ L)) :=
  (bitDomainEquiv hsL).symm.permCongr (feistelPairEquiv f)

@[simp]
theorem feistelBitEquiv_apply {s L : ℕ} (hsL : s ≤ L) (f : Fin (2 ^ (L - s)) → Fin (2 ^ s))
    (u : Fin (2 ^ L)) :
    feistelBitEquiv hsL f u = (bitDomainEquiv hsL).symm (feistelPair f (bitDomainEquiv hsL u)) :=
  rfl

theorem feistelBitEquiv_involutive {s L : ℕ} (hsL : s ≤ L)
    (f : Fin (2 ^ (L - s)) → Fin (2 ^ s)) :
    Function.Involutive (feistelBitEquiv hsL f) := fun u => by
  simp [feistelBitEquiv_apply]

@[simp]
theorem feistelBitEquiv_symm {s L : ℕ} (hsL : s ≤ L) (f : Fin (2 ^ (L - s)) → Fin (2 ^ s)) :
    (feistelBitEquiv hsL f).symm = feistelBitEquiv hsL f :=
  Equiv.ext fun u =>
    (feistelBitEquiv hsL f).symm_apply_eq.mpr (feistelBitEquiv_involutive hsL f u).symm


/-! ## Section 2: Child-router Feistel family `ℋ_ℓ^ch`
(`Claim B.3`, `Lemma 5.1`, `Corollary B.5`) -/

section ChildRouter

/-- Number of keys in `S : Finset (Fin (2 ^ s) × α)` routed to child bucket `b : Fin (2 ^ s)` under
`feistelHead f` (`|ĥ⁻¹(y)|` in Claim B.3, PDF p. 41 / printed p. 40 of [LiLiangYuZhou2024],
`arXiv:2310.20536v1`). -/
@[expose]
def bucketLoad {s : ℕ} {α : Type*} (f : α → Fin (2 ^ s))
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) : ℕ :=
  #{x ∈ S | feistelHead f x = b}

/-- Within any bucket `b`, projecting `{x ∈ S | feistelHead f x = b}` to `Prod.snd` (`y_prim`)
preserves cardinality ([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Section 5.4, PDF p. 32 /
printed p. 31). -/
theorem card_image_snd_filter_feistelHead_eq {s : ℕ} {α : Type*} [DecidableEq α]
    (f : α → Fin (2 ^ s)) (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) :
    #(({x ∈ S | feistelHead f x = b}).image Prod.snd) = bucketLoad f S b :=
  card_image_of_injOn ((injOn_snd_of_feistelHead_eq f b).mono fun _ hx => (mem_filter.mp hx).2)

/-- Bucket loads partition `#S` across all `2 ^ s` child buckets. -/
theorem sum_bucketLoad_eq_card {s : ℕ} {α : Type*}
    (f : α → Fin (2 ^ s)) (S : Finset (Fin (2 ^ s) × α)) :
    ∑ b : Fin (2 ^ s), bucketLoad f S b = #S := by
  unfold bucketLoad
  exact (card_eq_sum_card_fiberwise (f := feistelHead f) (t := univ) fun _ _ => mem_univ _).symm

private def bucketInd {s : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) (z : α) (y : Fin (2 ^ s)) : ℝ :=
  if (b ^^^ y, z) ∈ S then 1 else 0

private theorem bucketInd_mem_Icc {s : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) (z : α) (y : Fin (2 ^ s)) :
    bucketInd S b z y ∈ Set.Icc 0 1 := by
  dsimp only [bucketInd]
  split_ifs <;> constructor <;> norm_num

private theorem bucketLoad_eq_sum_bucketInd {s : ℕ} {α : Type*} [DecidableEq α]
    (f : α → Fin (2 ^ s)) (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) :
    (bucketLoad f S b : ℝ) = ∑ z ∈ S.image Prod.snd, bucketInd S b z (f z) := by
  have hcard : bucketLoad f S b = #{z ∈ S.image Prod.snd | (b ^^^ f z, z) ∈ S} := by
    refine card_nbij' Prod.snd (fun z => (b ^^^ f z, z)) ?_ ?_ ?_ ?_
    · intro x hx
      rcases mem_filter.mp hx with ⟨hxS, hhd⟩
      have hx1 : x.1 = b ^^^ f x.2 := (feistelHead_eq_iff f x b).mp hhd
      refine mem_filter.mpr ⟨mem_image_of_mem Prod.snd hxS, ?_⟩
      rwa [← hx1, Prod.mk.eta]
    · intro z hz
      rcases mem_filter.mp hz with ⟨_, hzS⟩
      exact mem_filter.mpr ⟨hzS, by simp [feistelHead]⟩
    · intro x hx
      have hx1 : x.1 = b ^^^ f x.2 := (feistelHead_eq_iff f x b).mp (mem_filter.mp hx).2
      dsimp only
      rw [← hx1, Prod.mk.eta]
    · intro _ _; rfl
  rw [hcard, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun z _ => ?_
  dsimp only [bucketInd]
  split_ifs <;> simp

private theorem expect_bucketInd_eq {s : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) (z : α) :
    (𝔼 y : Fin (2 ^ s), bucketInd S b z y) = (#{x ∈ S | x.2 = z} : ℝ) / (2 ^ s : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  dsimp only [bucketInd]
  rw [sum_boole]
  congr 1
  refine card_nbij' (fun y => (b ^^^ y, z)) (fun x => b ^^^ x.1) ?_ ?_ ?_ ?_
  · intro y hy
    exact mem_filter.mpr ⟨(mem_filter.mp hy).2, rfl⟩
  · intro x hx
    rcases mem_filter.mp hx with ⟨hxS, hxz⟩
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rwa [xor_cancel_left, ← hxz, Prod.mk.eta]
  · intro y _; exact xor_cancel_left b y
  · intro x hx
    dsimp only
    rw [xor_cancel_left, ← (mem_filter.mp hx).2, Prod.mk.eta]

private theorem sum_expect_bucketInd_eq {s : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) :
    ∑ z ∈ S.image Prod.snd, (𝔼 y : Fin (2 ^ s), bucketInd S b z y) =
      (#S : ℝ) / (2 ^ s : ℝ) := by
  simp only [expect_bucketInd_eq, ← sum_div]
  congr 1
  exact_mod_cast (card_eq_sum_card_image Prod.snd S).symm

private theorem dens_exists_le_sum {ι β : Type*} [Fintype ι] [Fintype β]
    (P : ι → β → Prop) [∀ b, DecidablePred (fun i => P i b)]
    [DecidablePred (fun i => ∃ b, P i b)] :
    (dens {i : ι | ∃ b : β, P i b} : ℝ) ≤ ∑ b : β, (dens {i : ι | P i b} : ℝ) := by
  classical
  have hsub : ({i : ι | ∃ b : β, P i b} : Finset ι) ⊆
      (univ : Finset β).biUnion fun b => {i : ι | P i b} := fun i hi => by
    obtain ⟨b, hb⟩ := (mem_filter.mp hi).2
    exact mem_biUnion.mpr ⟨b, mem_univ b, mem_filter.mpr ⟨mem_univ i, hb⟩⟩
  exact (NNRat.cast_le.mpr ((dens_le_dens hsub).trans dens_biUnion_le)).trans_eq
    (map_sum (NNRat.castHom ℝ) _ _)

/-- **General `2m`-wise independent Feistel single-bucket tail bound (`Claim B.3`)**:
for any `1 ≤ m`, `2m`-wise independent round family `h : ι → α → Fin (2 ^ s)`, finite set `S` with
`2 * m ≤ 3 * (#S / 2 ^ s)`, bucket `b`, and `a > 0`, `bucketLoad (h i) S b` deviates from
`#S / 2 ^ s` by at least `a` with seed density at most `2 * (3 * m * (#S / 2 ^ s) / a ^ 2) ^ m`. -/
theorem dens_bucketLoad_sub_ge_le {ι α : Type*} [Fintype ι] {s m : ℕ}
    (hm : 1 ≤ m) {h : ι → α → Fin (2 ^ s)} (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset (Fin (2 ^ s) × α)) (b : Fin (2 ^ s)) {a : ℝ}
    (hmμ : 2 * (m : ℝ) ≤ 3 * ((#S : ℝ) / (2 ^ s : ℝ))) (ha : 0 < a) :
    (dens {i : ι | a ≤ |(bucketLoad (h i) S b : ℝ) - (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ) ≤
      2 * (3 * (m : ℝ) * ((#S : ℝ) / (2 ^ s : ℝ)) / a ^ 2) ^ m := by
  classical
  have heq (i : ι) : (bucketLoad (h i) S b : ℝ) - (#S : ℝ) / (2 ^ s : ℝ) =
      ∑ z ∈ S.image Prod.snd,
        (bucketInd S b z (h i z) - 𝔼 y : Fin (2 ^ s), bucketInd S b z y) := by
    rw [sum_sub_distrib, bucketLoad_eq_sum_bucketInd, sum_expect_bucketInd_eq]
  simp only [heq]
  exact dens_abs_sum_sub_expect_le hm hh (S.image Prod.snd) (bucketInd S b)
    (fun z _ y => bucketInd_mem_Icc S b z y) (sum_expect_bucketInd_eq S b).le hmμ ha

/-- **General `2m`-wise independent Feistel all-buckets union bound (`Corollary B.5(c)` /
`Lemma 5.1(c)` parametric form)**: union-bounding `dens_bucketLoad_sub_ge_le` over all `2 ^ s`
child buckets. -/
theorem dens_exists_bucketLoad_sub_ge_le {ι α : Type*} [Fintype ι] {s m : ℕ}
    (hm : 1 ≤ m) {h : ι → α → Fin (2 ^ s)} (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset (Fin (2 ^ s) × α)) {a : ℝ}
    (hmμ : 2 * (m : ℝ) ≤ 3 * ((#S : ℝ) / (2 ^ s : ℝ))) (ha : 0 < a) :
    (dens {i : ι | ∃ b : Fin (2 ^ s),
        a ≤ |(bucketLoad (h i) S b : ℝ) - (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ) ≤
      (2 ^ (s + 1) : ℝ) * (3 * (m : ℝ) * ((#S : ℝ) / (2 ^ s : ℝ)) / a ^ 2) ^ m := by
  calc (dens {i : ι | ∃ b : Fin (2 ^ s),
          a ≤ |(bucketLoad (h i) S b : ℝ) - (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ)
      ≤ ∑ b : Fin (2 ^ s),
          (dens {i : ι | a ≤ |(bucketLoad (h i) S b : ℝ) - (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ) :=
        dens_exists_le_sum _
    _ ≤ ∑ _b : Fin (2 ^ s),
          2 * (3 * (m : ℝ) * ((#S : ℝ) / (2 ^ s : ℝ)) / a ^ 2) ^ m :=
        sum_le_sum fun b _ => dens_bucketLoad_sub_ge_le hm hh S b hmμ ha
    _ = (2 ^ (s + 1) : ℝ) * (3 * (m : ℝ) * ((#S : ℝ) / (2 ^ s : ℝ)) / a ^ 2) ^ m := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          pow_succ]
        ring

/-- Concrete seed space for the child-router Feistel family `ℋ_ℓ^ch` instantiated via Mikkel
Thorup's double tabulation [Thorup2013] (`d = 2 * q * c`, matching `WordRAM.DoubleTabulation`). -/
abbrev ChildRouterSeed (c q b s : ℕ) : Type :=
  DoubleTabTopSeed c (2 * q * c) b × DoubleTabBotSeed (2 * q * c) b s

/-- Exact bit length `2 * q * c * 2 ^ b * (c * b + s)` of a seed in `ChildRouterSeed c q b s`. -/
def childRouterSeedBits (c q b s : ℕ) : ℕ :=
  2 * q * c * 2 ^ b * (c * b + s)

theorem childRouterSeedBits_eq (c q b s : ℕ) :
    childRouterSeedBits c q b s = 2 * q * c * 2 ^ b * (c * b + s) := by
  rfl

/-- `ChildRouterSeed c q b s` has cardinality `2 ^ childRouterSeedBits c q b s`. -/
theorem card_childRouterSeed (c q b s : ℕ) :
    Fintype.card (ChildRouterSeed c q b s) = 2 ^ childRouterSeedBits c q b s := by
  simp only [ChildRouterSeed, DoubleTabTopSeed, DoubleTabBotSeed, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, childRouterSeedBits]
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  ring

/-- Double-tabulation round function `Fin T → Fin (2 ^ s)` for seed `θ : ChildRouterSeed c q b s`.
-/
def childRouterRound (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) : Fin T → Fin (2 ^ s) :=
  doubleTabHash c (2 * q * c) b T s θ.1 θ.2

theorem childRouterRound_eq (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    childRouterRound c q b s T θ = doubleTabHash c (2 * q * c) b T s θ.1 θ.2 := by
  rfl

theorem childRouterRound_apply (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) (z : Fin T) :
    childRouterRound c q b s T θ z = doubleTabHash c (2 * q * c) b T s θ.1 θ.2 z := by
  rfl

/-- Child-router Feistel permutation on `Fin (2 ^ s) × Fin T` (`Corollary B.5`). -/
def childRouterPerm (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    Equiv.Perm (Fin (2 ^ s) × Fin T) :=
  feistelPairEquiv (childRouterRound c q b s T θ)

@[simp]
theorem childRouterPerm_apply (c q b s T : ℕ) (θ : ChildRouterSeed c q b s)
    (x : Fin (2 ^ s) × Fin T) :
    childRouterPerm c q b s T θ x = feistelPair (childRouterRound c q b s T θ) x := by
  rfl

@[simp]
theorem childRouterPerm_symm (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    (childRouterPerm c q b s T θ).symm = childRouterPerm c q b s T θ := by
  rfl

theorem childRouterPerm_involutive (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    Function.Involutive (childRouterPerm c q b s T θ) :=
  feistelPair_involutive (childRouterRound c q b s T θ)

/-- Flat child-router Feistel permutation on `Fin (2 ^ s * T)`. -/
def childRouterMixedPerm (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    Equiv.Perm (Fin (2 ^ s * T)) :=
  feistelMixedEquiv (childRouterRound c q b s T θ)

@[simp]
theorem childRouterMixedPerm_apply (c q b s T : ℕ) (θ : ChildRouterSeed c q b s)
    (u : Fin (2 ^ s * T)) :
    childRouterMixedPerm c q b s T θ u = feistelMixedEquiv (childRouterRound c q b s T θ) u := by
  rfl

@[simp]
theorem childRouterMixedPerm_symm (c q b s T : ℕ) (θ : ChildRouterSeed c q b s) :
    (childRouterMixedPerm c q b s T θ).symm = childRouterMixedPerm c q b s T θ := by
  exact feistelMixedEquiv_symm (childRouterRound c q b s T θ)

/-- Flat child-router Feistel permutation on `Fin (2 ^ L)` for `s ≤ L` (`Lemma 5.1`). -/
def childRouterBitPerm {s L : ℕ} (hsL : s ≤ L) (c q b : ℕ) (θ : ChildRouterSeed c q b s) :
    Equiv.Perm (Fin (2 ^ L)) :=
  feistelBitEquiv hsL (childRouterRound c q b s (2 ^ (L - s)) θ)

@[simp]
theorem childRouterBitPerm_apply {s L : ℕ} (hsL : s ≤ L) (c q b : ℕ)
    (θ : ChildRouterSeed c q b s) (u : Fin (2 ^ L)) :
    childRouterBitPerm hsL c q b θ u =
      feistelBitEquiv hsL (childRouterRound c q b s (2 ^ (L - s)) θ) u := by
  rfl

@[simp]
theorem childRouterBitPerm_symm {s L : ℕ} (hsL : s ≤ L) (c q b : ℕ)
    (θ : ChildRouterSeed c q b s) :
    (childRouterBitPerm hsL c q b θ).symm = childRouterBitPerm hsL c q b θ := by
  exact feistelBitEquiv_symm hsL (childRouterRound c q b s (2 ^ (L - s)) θ)

private theorem dens_prod_le_of_good {α β : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    [Fintype β] (G : Finset α) (P : α → β → Prop)
    [∀ a, DecidablePred (P a)] [DecidablePred (fun p : α × β => P p.1 p.2)]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hgood : ∀ a ∈ G, (dens {y : β | P a y} : ℝ) ≤ δ) :
    (dens {p : α × β | P p.1 p.2} : ℝ) ≤ (dens {a : α | a ∉ G} : ℝ) + δ := by
  rw [← Fintype.expect_boole (fun p : α × β => P p.1 p.2),
    Fintype.expect_prod_type (fun p : α × β => if P p.1 p.2 then (1 : ℝ) else 0)]
  refine (expect_le_expect (g := fun a => (if a ∉ G then (1 : ℝ) else 0) + δ)
    fun a _ => ?_).trans_eq ?_
  · refine (expect_congr rfl fun y _ => (by congr : _ = if P a y then (1 : ℝ) else 0)).trans_le ?_
    rw [Fintype.expect_boole]
    by_cases ha : a ∈ G
    · simp only [ha, not_true_eq_false, ↓reduceIte, zero_add]
      exact hgood a ha
    · simp only [ha, not_false_eq_true, ↓reduceIte]
      have h1 : (dens {y : β | P a y} : ℝ) ≤ 1 := by exact_mod_cast dens_le_one
      linarith
  · rw [expect_add_distrib, Fintype.expect_boole, Fintype.expect_const]

/-- **Unconditional Double-Tabulation Feistel concentration (`Corollary B.5(c)` parametric form)**:
bounds the seed density on `ChildRouterSeed c q b s` where any child bucket deviates from
`#S / 2 ^ s` by at least `a` by `δ_dt + 2 ^ (s + 1) * (3 * m * (#S / 2 ^ s) / a ^ 2) ^ m`. -/
theorem dens_childRouter_exists_bucketLoad_sub_ge_le {c q b s T m : ℕ}
    (hc : 1 ≤ c) (hq : 1 ≤ q) (hm : 1 ≤ m) (hT : T ≤ 2 ^ (c * b))
    (hcode : 2 * doubleTabCodeBound c (2 * q * c) q (2 * m) ≤ 2 ^ ((q - 1) * b))
    (S : Finset (Fin (2 ^ s) × Fin T)) {a : ℝ}
    (hmμ : 2 * (m : ℝ) ≤ 3 * ((#S : ℝ) / (2 ^ s : ℝ))) (ha : 0 < a) :
    (dens {θ : ChildRouterSeed c q b s | ∃ bucket : Fin (2 ^ s),
        a ≤ |(bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) -
          (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ) ≤
      2 * (doubleTabCodeBound c (2 * q * c) q (2 * m) : ℝ) ^ 2 /
        (2 ^ (2 * (q - 1) * b) : ℝ) +
      (2 ^ (s + 1) : ℝ) * (3 * (m : ℝ) * ((#S : ℝ) / (2 ^ s : ℝ)) / a ^ 2) ^ m := by
  classical
  let G : Finset (DoubleTabTopSeed c (2 * q * c) b) :=
    univ.filter fun T₁ => IsKUnique (2 * m) (simpleTabTuple T₁)
  have hprod := dens_prod_le_of_good G
    (fun T₁ T₂ => ∃ bucket : Fin (2 ^ s),
      a ≤ |(bucketLoad (doubleTabHash c (2 * q * c) b T s T₁ T₂) S bucket : ℝ) -
        (#S : ℝ) / (2 ^ s : ℝ)|)
    (by positivity)
    (fun T₁ hT₁ => dens_exists_bucketLoad_sub_ge_le hm
      (isKWiseIndependentHash_doubleTabHash_of_isKUnique hT (mem_filter.mp hT₁).2) S hmμ ha)
  have hdt : (dens {T₁ : DoubleTabTopSeed c (2 * q * c) b | T₁ ∉ G} : ℝ) ≤
      2 * (doubleTabCodeBound c (2 * q * c) q (2 * m) : ℝ) ^ 2 /
        (2 ^ (2 * (q - 1) * b) : ℝ) := by
    have hnotG : ({T₁ : DoubleTabTopSeed c (2 * q * c) b | T₁ ∉ G} : Finset _) =
        univ.filter fun T₁ => ¬ IsKUnique (2 * m) (simpleTabTuple T₁) := by
      ext T₁; simp [G]
    rw [hnotG, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast]
    have hN_pos : (0 : ℝ) < Fintype.card (DoubleTabTopSeed c (2 * q * c) b) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have hW_pos : (0 : ℝ) < (2 ^ (2 * (q - 1) * b) : ℝ) := by positivity
    rw [div_le_div_iff₀ hN_pos hW_pos]
    have hcard := card_not_isKUnique_le hc hq rfl hcode
    have hpow : ((2 ^ ((q - 1) * b)) ^ 2 : ℕ) = 2 ^ (2 * (q - 1) * b) := by
      rw [← Nat.pow_mul]; congr 1; ring
    rw [hpow] at hcard
    have hreal : (2 ^ (2 * (q - 1) * b) : ℝ) *
        (#(univ.filter fun T₁ : DoubleTabTopSeed c (2 * q * c) b =>
          ¬ IsKUnique (2 * m) (simpleTabTuple T₁)) : ℝ) ≤
        2 * (doubleTabCodeBound c (2 * q * c) q (2 * m) : ℝ) ^ 2 *
          Fintype.card (DoubleTabTopSeed c (2 * q * c) b) := by
      exact_mod_cast hcard
    linarith
  calc _ ≤ (dens {p : ChildRouterSeed c q b s | ∃ bucket : Fin (2 ^ s),
          a ≤ |(bucketLoad (doubleTabHash c (2 * q * c) b T s p.1 p.2) S bucket : ℝ) -
            (#S : ℝ) / (2 ^ s : ℝ)|} : ℝ) := by
        exact_mod_cast dens_le_dens fun θ hθ => by
          simp only [mem_filter, mem_univ, true_and] at hθ ⊢
          exact hθ
    _ ≤ _ := hprod
    _ ≤ _ := add_le_add hdt le_rfl

/-- Half-independence exponent `m = 3 * ⌈log₂ max(n, 2)⌉ + 4` (`k = 2 * m`), chosen so that
`2 ^ (s + 1) * (1 / 2) ^ m ≤ 1 / (8 * n ^ 2)` whenever `2 ^ s ≤ n`. -/
def childRouterHalfInd (n : ℕ) : ℕ :=
  3 * Nat.clog 2 (max n 2) + 4

theorem childRouterHalfInd_eq (n : ℕ) :
    childRouterHalfInd n = 3 * Nat.clog 2 (max n 2) + 4 := by
  rfl

/-- **Unconditional Double-Tabulation child-router concentration (`Corollary B.5(c)` &
`Lemma 5.1(c)` `(1/5)(n / 2 ^ s) ^ (2/3)` form)**:
whenever `T ≤ 2 ^ (c * b)`, `4 * #S * doubleTabCodeBound ... ≤ 2 ^ ((q - 1) * b)`, and
`2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S`, every bucket load lies in
`[#S / 2 ^ s - (1/5)(#S / 2 ^ s)^(2/3), #S / 2 ^ s + (1/5)(#S / 2 ^ s)^(2/3)]` except on at most
a `1 / (4 * (#S) ^ 2)` fraction of seeds `θ : ChildRouterSeed c q b s`. -/
theorem dens_childRouter_bucketLoad_outside_le {c q b s T : ℕ}
    (hc : 1 ≤ c) (hq : 1 ≤ q) (hT : T ≤ 2 ^ (c * b))
    (S : Finset (Fin (2 ^ s) × Fin T))
    (hcode : 4 * #S * doubleTabCodeBound c (2 * q * c) q (2 * childRouterHalfInd #S) ≤
      2 ^ ((q - 1) * b))
    (hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S) :
    (dens {θ : ChildRouterSeed c q b s |
      ¬ ∀ bucket : Fin (2 ^ s),
        (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ s : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  classical
  set m := childRouterHalfInd #S
  set μ : ℝ := (#S : ℝ) / (2 ^ s : ℝ)
  set a : ℝ := ((1 : ℝ) / 5) * μ ^ ((2 : ℝ) / 3)
  have hm4 : 4 ≤ m := by dsimp [m, childRouterHalfInd]; omega
  have hm : 1 ≤ m := by omega
  have hS_pos : 1 ≤ #S := by
    have h1 : 1 ≤ 2 ^ s * (150 * m) ^ 3 := Nat.mul_pos (Nat.two_pow_pos s) (by positivity)
    omega
  have h2code : 2 * doubleTabCodeBound c (2 * q * c) q (2 * m) ≤ 2 ^ ((q - 1) * b) := by
    calc 2 * doubleTabCodeBound c (2 * q * c) q (2 * m)
        ≤ 4 * #S * doubleTabCodeBound c (2 * q * c) q (2 * m) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ ((q - 1) * b) := hcode
  have hμ_pos : 0 < μ := by dsimp [μ]; positivity
  set u : ℝ := μ ^ ((1 : ℝ) / 3)
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hμ_pos _
  have hu3 : u ^ 3 = μ := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
    norm_num
  have hu2 : μ ^ ((2 : ℝ) / 3) = u ^ 2 := by
    dsimp [u]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
    norm_num
  have h150_cube : (150 * (m : ℝ)) ^ 3 ≤ u ^ 3 := by
    rw [hu3]
    dsimp [μ]
    rw [le_div_iff₀ (by positivity)]
    have hc_real : (2 ^ s : ℝ) * (150 * (m : ℝ)) ^ 3 ≤ (#S : ℝ) := by exact_mod_cast hconc
    linarith
  have h150 : 150 * (m : ℝ) ≤ u :=
    (pow_le_pow_iff_left₀ (by positivity) hu_pos.le (by decide : 3 ≠ 0)).mp h150_cube
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have hm_real : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hmμ : 2 * (m : ℝ) ≤ 3 * μ := by
    rw [← hu3]
    nlinarith [sq_nonneg u]
  have hrat : 3 * (m : ℝ) * μ / a ^ 2 ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ (pow_pos ha_pos 2)]
    have ha2 : a ^ 2 = ((1 : ℝ) / 25) * u ^ 4 := by dsimp [a]; rw [hu2]; ring
    rw [ha2, ← hu3]
    nlinarith [pow_pos hu_pos 3]
  have hmain := dens_childRouter_exists_bucketLoad_sub_ge_le hc hq hm hT h2code S hmμ ha_pos
  have hdt : 2 * (doubleTabCodeBound c (2 * q * c) q (2 * m) : ℝ) ^ 2 /
      (2 ^ (2 * (q - 1) * b) : ℝ) ≤ 1 / (8 * (#S : ℝ) ^ 2) := by
    have hsq_nat : 16 * #S ^ 2 * (doubleTabCodeBound c (2 * q * c) q (2 * m)) ^ 2 ≤
        2 ^ (2 * (q - 1) * b) := by
      calc 16 * #S ^ 2 * (doubleTabCodeBound c (2 * q * c) q (2 * m)) ^ 2
          = (4 * #S * doubleTabCodeBound c (2 * q * c) q (2 * m)) ^ 2 := by ring
        _ ≤ (2 ^ ((q - 1) * b)) ^ 2 := Nat.pow_le_pow_left hcode 2
        _ = 2 ^ (2 * (q - 1) * b) := by rw [← Nat.pow_mul]; congr 1; ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq_real : 16 * (#S : ℝ) ^ 2 * (doubleTabCodeBound c (2 * q * c) q (2 * m) : ℝ) ^ 2 ≤
        (2 ^ (2 * (q - 1) * b) : ℝ) := by exact_mod_cast hsq_nat
    linarith
  have hch : (2 ^ (s + 1) : ℝ) * (3 * (m : ℝ) * μ / a ^ 2) ^ m ≤ 1 / (8 * (#S : ℝ) ^ 2) := by
    have hpow_le : (3 * (m : ℝ) * μ / a ^ 2) ^ m ≤ ((1 : ℝ) / 2) ^ m := by gcongr
    have h2m_nat : 8 * #S ^ 2 * 2 ^ (s + 1) ≤ 2 ^ m := by
      set Ln := Nat.clog 2 (max #S 2)
      have hSn : #S ≤ 2 ^ Ln := (le_max_left #S 2).trans (Nat.le_pow_clog (by decide) _)
      have hsS : 2 ^ s ≤ #S := by
        calc 2 ^ s = 2 ^ s * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ s * (150 * m) ^ 3 :=
              Nat.mul_le_mul_left _ (Nat.one_le_pow 3 (150 * m) (by omega))
          _ ≤ #S := hconc
      calc 8 * #S ^ 2 * 2 ^ (s + 1)
          = 16 * #S ^ 2 * 2 ^ s := by rw [pow_succ]; ring
        _ ≤ 16 * (2 ^ Ln) ^ 2 * 2 ^ Ln :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hSn 2)) (hsS.trans hSn)
        _ = 2 ^ (3 * Ln + 4) := by
            have h16 : (16 : ℕ) = 2 ^ 4 := by decide
            rw [h16, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
            congr 1; ring
        _ = 2 ^ m := rfl
    have h2m_real : 8 * (#S : ℝ) ^ 2 * (2 ^ (s + 1) : ℝ) ≤ (2 ^ m : ℝ) := by
      exact_mod_cast h2m_nat
    calc (2 ^ (s + 1) : ℝ) * (3 * (m : ℝ) * μ / a ^ 2) ^ m
        ≤ (2 ^ (s + 1) : ℝ) * ((1 : ℝ) / 2) ^ m :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ = (2 ^ (s + 1) : ℝ) / (2 ^ m : ℝ) := by rw [one_div, inv_pow, div_eq_mul_inv]
      _ ≤ 1 / (8 * (#S : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
  calc _ ≤ (dens {θ : ChildRouterSeed c q b s | ∃ bucket : Fin (2 ^ s),
          a ≤ |(bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) - μ|} : ℝ) := by
        exact_mod_cast dens_le_dens fun θ hθ => by
          simp only [mem_filter, mem_univ, true_and] at hθ ⊢
          push Not at hθ
          obtain ⟨bucket, hb⟩ := hθ
          refine ⟨bucket, le_abs.mpr ?_⟩
          by_cases hlo : μ - a ≤ (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ)
          · exact Or.inl (by linarith [hb hlo])
          · exact Or.inr (by linarith)
    _ ≤ _ := hmain
    _ ≤ 1 / (8 * (#S : ℝ) ^ 2) + 1 / (8 * (#S : ℝ) ^ 2) := add_le_add hdt hch
    _ = 1 / (4 * (#S : ℝ) ^ 2) := by ring

/-- `PMF.uniformOfFintype` event-probability form of `dens_childRouter_bucketLoad_outside_le`. -/
theorem prob_childRouter_bucketLoad_outside_le {c q b s T : ℕ}
    (hc : 1 ≤ c) (hq : 1 ≤ q) (hT : T ≤ 2 ^ (c * b))
    (S : Finset (Fin (2 ^ s) × Fin T))
    (hcode : 4 * #S * doubleTabCodeBound c (2 * q * c) q (2 * childRouterHalfInd #S) ≤
      2 ^ ((q - 1) * b))
    (hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S) :
    ((PMF.uniformOfFintype (ChildRouterSeed c q b s)).toOuterMeasure
      {θ : ChildRouterSeed c q b s |
        ¬ ∀ bucket : Fin (2 ^ s),
          (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
              (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ∧
            (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ≤
              (#S : ℝ) / (2 ^ s : ℝ) +
                ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)}).toReal ≤
      1 / (4 * (#S : ℝ) ^ 2) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    dens_childRouter_bucketLoad_outside_le hc hq hT S hcode hconc

/-- Character count `c = 2 * max ε_inv 1` for pre-given space exponent `ε = 1 / ε_inv` in
`Corollary B.5` and `Lemma 5.1`. -/
def childRouterChars (ε_inv : ℕ) : ℕ :=
  2 * max ε_inv 1

/-- Character bit-width `b = max 1 ⌈⌈log₂ max(T, 2)⌉ / max c 1⌉` covering `Fin T`. -/
def childRouterCharBits (c T : ℕ) : ℕ :=
  max 1 ((Nat.clog 2 (max T 2) + max c 1 - 1) / max c 1)

/-- Repetition factor `q = c * max α_inv 1 + 2` for gap bound `2 ^ s * T ≤ T ^ α_inv`. -/
def childRouterRep (ε_inv α_inv : ℕ) : ℕ :=
  childRouterChars ε_inv * max α_inv 1 + 2

/-- Constant `O_{ε_inv, α_inv}(1)` factor in
`(childRouterSeedBits ...) ^ max ε_inv 1 ≤ C * (2 ^ s * T)`. -/
def childRouterSpaceConst (ε_inv α_inv : ℕ) : ℕ :=
  let c := childRouterChars ε_inv
  let q := childRouterRep ε_inv α_inv
  (2 * q * c) ^ max ε_inv 1 * 2 ^ (2 * c ^ 2 + c + 2)

/-- Minimum character bit-width ensuring `4 * B ≤ 2 ^ b` via `Nat.pow_le_two_pow`. -/
private def childRouterMinB (ε_inv α_inv : ℕ) : ℕ :=
  let c := childRouterChars ε_inv
  let A := c * max α_inv 1
  let q := childRouterRep ε_inv α_inv
  let d := 2 * q * c
  let D := 2 * c * q
  max (4 * c * d ^ q * (c * (6 * A + 8)) ^ D) (4 * (D + 1) ^ 2)

/-- Explicit input-cardinality threshold such that whenever `2 ^ s * T ≤ T ^ max α_inv 1` and
`childRouterThreshold ε_inv α_inv ≤ #S`, the `Corollary B.5` / `Lemma 5.1` parameters satisfy
`4 * #S * doubleTabCodeBound ... ≤ 2 ^ ((q - 1) * b)`. -/
def childRouterThreshold (ε_inv α_inv : ℕ) : ℕ :=
  2 ^ (childRouterChars ε_inv * max α_inv 1 * childRouterMinB ε_inv α_inv)

theorem childRouterThreshold_eq (ε_inv α_inv : ℕ) :
    let c := childRouterChars ε_inv
    let A := c * max α_inv 1
    let q := childRouterRep ε_inv α_inv
    let d := 2 * q * c
    let D := 2 * c * q
    childRouterThreshold ε_inv α_inv =
      2 ^ (A * max (4 * c * d ^ q * (c * (6 * A + 8)) ^ D) (4 * (D + 1) ^ 2)) := by
  rfl

/-- Explicit threshold `s₀ = 2100 ^ 3` above which `#S ≥ 2 ^ s * s ^ 4` implies
`2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S` ([LiLiangYuZhou2024], `arXiv:2310.20536v1`,
Appendix B, Claim B.3 proof, PDF p. 42 / printed p. 41). -/
def childRouterMinS : ℕ :=
  2100 ^ 3

theorem childRouterChars_eq (ε_inv : ℕ) : childRouterChars ε_inv = 2 * max ε_inv 1 := by
  rfl

theorem childRouterCharBits_eq (c T : ℕ) :
    childRouterCharBits c T = max 1 ((Nat.clog 2 (max T 2) + max c 1 - 1) / max c 1) := by
  rfl

theorem childRouterRep_eq (ε_inv α_inv : ℕ) :
    childRouterRep ε_inv α_inv = childRouterChars ε_inv * max α_inv 1 + 2 := by
  rfl

theorem childRouterSpaceConst_eq (ε_inv α_inv : ℕ) :
    childRouterSpaceConst ε_inv α_inv =
      (2 * childRouterRep ε_inv α_inv * childRouterChars ε_inv) ^ max ε_inv 1 *
        2 ^ (2 * (childRouterChars ε_inv) ^ 2 + childRouterChars ε_inv + 2) := by
  rfl

theorem one_le_childRouterThreshold (ε_inv α_inv : ℕ) :
    1 ≤ childRouterThreshold ε_inv α_inv :=
  Nat.two_pow_pos _

theorem childRouterMinS_eq : childRouterMinS = 2100 ^ 3 := by
  rfl

theorem le_two_pow_mul_childRouterCharBits {c T : ℕ} (hc : 1 ≤ c) :
    T ≤ 2 ^ (c * childRouterCharBits c T) := by
  have hmax_c : max c 1 = c := max_eq_left hc
  set LT := Nat.clog 2 (max T 2)
  have hdiv : LT ≤ ((LT + c - 1) / c) * c := by
    have hmod := Nat.div_add_mod (LT + c - 1) c
    have hlt := Nat.mod_lt (LT + c - 1) hc
    rw [Nat.mul_comm]
    omega
  have hle_exp : LT ≤ c * childRouterCharBits c T := by grind [childRouterCharBits, Nat.mul_comm]
  calc T ≤ max T 2 := le_max_left T 2
    _ ≤ 2 ^ LT := Nat.le_pow_clog (by decide) _
    _ ≤ 2 ^ (c * childRouterCharBits c T) := Nat.pow_le_pow_right (by decide) hle_exp

/-- **Seed bit-space bound (`Corollary B.5(b)` & `Lemma 5.1(b)`)**: for every `ε_inv, α_inv, s : ℕ`
and `1 ≤ T`,
`(childRouterSeedBits ...) ^ max ε_inv 1 ≤ childRouterSpaceConst ε_inv α_inv * (2 ^ s * T)`,
i.e., storing a seed takes `O_{ε, α}((2 ^ s * T) ^ ε)` bits. -/
theorem childRouterSeedBits_pow_le (ε_inv α_inv s : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    (childRouterSeedBits (childRouterChars ε_inv) (childRouterRep ε_inv α_inv)
      (childRouterCharBits (childRouterChars ε_inv) T) s) ^ max ε_inv 1 ≤
      childRouterSpaceConst ε_inv α_inv * (2 ^ s * T) := by
  set E := max ε_inv 1
  set c := childRouterChars ε_inv
  set q := childRouterRep ε_inv α_inv
  set b := childRouterCharBits c T
  set LT := Nat.clog 2 (max T 2)
  have hE : 1 ≤ E := le_max_right _ _
  have hc_eq : c = 2 * E := rfl
  have hc : 2 ≤ c := by omega
  have hLT1 : 1 ≤ LT := by
    have h2 : 2 ≤ max T 2 := le_max_right T 2
    exact (show 1 = Nat.clog 2 2 by decide) ▸ Nat.clog_mono_right 2 h2
  have hb_eq : b = (LT + c - 1) / c := by
    dsimp only [b, childRouterCharBits]
    rw [max_eq_left (by omega : 1 ≤ c)]
    exact max_eq_right (Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega))
  have hcb_le : c * b ≤ LT + c - 1 := by
    rw [hb_eq]
    exact Nat.mul_div_le (LT + c - 1) c
  have hpow_LT : 2 ^ LT ≤ 4 * T := by
    calc 2 ^ LT ≤ 2 * max T 2 := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
      _ ≤ 2 * (2 * T) := Nat.mul_le_mul_left 2 (by omega)
      _ = 4 * T := by ring
  have hfac1 : ((2 ^ b) ^ E) ^ 2 ≤ 2 ^ (c + 1) * (2 ^ s * T) := by
    calc ((2 ^ b) ^ E) ^ 2 = 2 ^ (c * b) := by
          rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 1; rw [hc_eq]; ring
      _ ≤ 2 ^ (LT + c - 1) := Nat.pow_le_pow_right (by decide) hcb_le
      _ = 2 ^ (c - 1) * 2 ^ LT := by
          rw [← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ (c - 1) * (4 * T) := Nat.mul_le_mul_left _ hpow_LT
      _ = 2 ^ (c + 1) * T := by
          have h4 : (4 : ℕ) = 2 ^ 2 := by decide
          rw [h4, ← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
      _ ≤ 2 ^ (c + 1) * (2 ^ s * T) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left T (Nat.two_pow_pos s))
  have hfac2 : ((c * b + s) ^ E) ^ 2 ≤ 2 ^ (4 * c ^ 2 + 2) * (2 ^ s * T) := by
    set u := 4 * c ^ 2 + LT + s
    have hle_u : c * b + s ≤ u := by
      dsimp only [u]
      have : c ≤ 4 * c ^ 2 := by nlinarith
      omega
    have hu_pow : u ^ c ≤ 2 ^ u := Nat.pow_le_two_pow (by omega) (by dsimp [u]; omega)
    calc ((c * b + s) ^ E) ^ 2 = (c * b + s) ^ c := by
          rw [← Nat.pow_mul]; congr 1; rw [hc_eq]; ring
      _ ≤ u ^ c := Nat.pow_le_pow_left hle_u c
      _ ≤ 2 ^ u := hu_pow
      _ = 2 ^ (4 * c ^ 2) * 2 ^ LT * 2 ^ s := by
          dsimp [u]; rw [Nat.pow_add, Nat.pow_add]
      _ ≤ 2 ^ (4 * c ^ 2) * (4 * T) * 2 ^ s := by gcongr
      _ = 2 ^ (4 * c ^ 2 + 2) * (2 ^ s * T) := by
          have h4 : (4 : ℕ) = 2 ^ 2 := by decide
          rw [h4, Nat.pow_add]; ring
  have hsq : ((2 ^ b * (c * b + s)) ^ E) ^ 2 ≤ (2 ^ (2 * c ^ 2 + c + 2) * (2 ^ s * T)) ^ 2 := by
    calc ((2 ^ b * (c * b + s)) ^ E) ^ 2
        = ((2 ^ b) ^ E) ^ 2 * ((c * b + s) ^ E) ^ 2 := by rw [Nat.mul_pow, Nat.mul_pow]
      _ ≤ (2 ^ (c + 1) * (2 ^ s * T)) * (2 ^ (4 * c ^ 2 + 2) * (2 ^ s * T)) := by gcongr
      _ = (2 ^ (c + 1) * 2 ^ (4 * c ^ 2 + 2)) * (2 ^ s * T) ^ 2 := by ring
      _ = 2 ^ (4 * c ^ 2 + c + 3) * (2 ^ s * T) ^ 2 := by
          rw [← Nat.pow_add]; congr 2; ring
      _ ≤ 2 ^ (2 * (2 * c ^ 2 + c + 2)) * (2 ^ s * T) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ = (2 ^ (2 * c ^ 2 + c + 2) * (2 ^ s * T)) ^ 2 := by
          rw [Nat.mul_pow (2 ^ (2 * c ^ 2 + c + 2)) (2 ^ s * T) 2, ← Nat.pow_mul, Nat.mul_comm 2]
  have hprod_le : (2 ^ b * (c * b + s)) ^ E ≤ 2 ^ (2 * c ^ 2 + c + 2) * (2 ^ s * T) :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  dsimp only [childRouterSeedBits, childRouterSpaceConst]
  calc (2 * q * c * 2 ^ b * (c * b + s)) ^ E
      = (2 * q * c) ^ E * (2 ^ b * (c * b + s)) ^ E := by rw [Nat.mul_assoc, Nat.mul_pow]
    _ ≤ (2 * q * c) ^ E * (2 ^ (2 * c ^ 2 + c + 2) * (2 ^ s * T)) := by gcongr
    _ = (2 * q * c) ^ E * 2 ^ (2 * c ^ 2 + c + 2) * (2 ^ s * T) := by ring

private theorem childRouter_code_le_of_threshold {ε_inv α_inv s T : ℕ}
    (hgap : 2 ^ s * T ≤ T ^ max α_inv 1)
    (S : Finset (Fin (2 ^ s) × Fin T))
    (hthresh : childRouterThreshold ε_inv α_inv ≤ #S) :
    let c := childRouterChars ε_inv
    let q := childRouterRep ε_inv α_inv
    let b := childRouterCharBits c T
    4 * #S * doubleTabCodeBound c (2 * q * c) q (2 * childRouterHalfInd #S) ≤
      2 ^ ((q - 1) * b) := by
  intro c q b
  set A := c * max α_inv 1
  set d := 2 * q * c
  set D := 2 * c * q
  have hc : 2 ≤ c := by dsimp [c, childRouterChars]; have := le_max_right ε_inv 1; omega
  have hA2 : 2 ≤ A := by
    dsimp [A]
    calc 2 = 2 * 1 := by decide
      _ ≤ c * max α_inv 1 := Nat.mul_le_mul hc (le_max_right α_inv 1)
  have hb1 : 1 ≤ b := le_max_left 1 _
  have hT_cb : T ≤ 2 ^ (c * b) := le_two_pow_mul_childRouterCharBits (by omega)
  have hS_le : #S ≤ 2 ^ (A * b) := by
    calc #S ≤ Fintype.card (Fin (2 ^ s) × Fin T) := card_le_univ S
      _ = 2 ^ s * T := by rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      _ ≤ T ^ max α_inv 1 := hgap
      _ ≤ (2 ^ (c * b)) ^ max α_inv 1 := Nat.pow_le_pow_left hT_cb _
      _ = 2 ^ (A * b) := by rw [← Nat.pow_mul]; congr 1; dsimp [A]; ring
  have hb_min : childRouterMinB ε_inv α_inv ≤ b := by
    have hpow_le : 2 ^ (A * childRouterMinB ε_inv α_inv) ≤ 2 ^ (A * b) :=
      hthresh.trans hS_le
    have hmul_le : A * childRouterMinB ε_inv α_inv ≤ A * b :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow_le
    exact Nat.le_of_mul_le_mul_left hmul_le (by omega)
  have hclogS : Nat.clog 2 (max #S 2) ≤ A * b := by
    have h2 : 2 ≤ 2 ^ (A * b) := by
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ (A * b) := Nat.pow_le_pow_right (by decide) (by nlinarith)
    exact Nat.clog_le_of_le_pow (max_le hS_le h2)
  have h2m_le : 2 * childRouterHalfInd #S ≤ (6 * A + 8) * b := by
    dsimp [childRouterHalfInd]
    nlinarith
  set K := 4 * c * d ^ q * (c * (6 * A + 8)) ^ D
  have h4B_le_K : 4 * doubleTabCodeBound c d q (2 * childRouterHalfInd #S) ≤ K * b ^ D := by
    dsimp [doubleTabCodeBound, K, D]
    have hstep : c * (2 * childRouterHalfInd #S) ≤ c * (6 * A + 8) * b := by
      calc c * (2 * childRouterHalfInd #S)
          ≤ c * ((6 * A + 8) * b) := Nat.mul_le_mul_left c h2m_le
        _ = c * (6 * A + 8) * b := (Nat.mul_assoc _ _ _).symm
    calc 4 * (c * ((c * (2 * childRouterHalfInd #S)) ^ (2 * c) * d) ^ q)
        ≤ 4 * (c * (((c * (6 * A + 8) * b) ^ (2 * c) * d) ^ q)) :=
          Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left c
            (Nat.pow_le_pow_left (Nat.mul_le_mul_right d (Nat.pow_le_pow_left hstep _)) q))
      _ = 4 * c * d ^ q * (c * (6 * A + 8)) ^ (2 * c * q) * b ^ (2 * c * q) := by
          rw [Nat.mul_pow (c * (6 * A + 8)) b (2 * c),
            Nat.mul_pow _ d q, Nat.mul_pow _ (b ^ (2 * c)) q,
            ← Nat.pow_mul, ← Nat.pow_mul]
          ring
  have hK_le_b : K ≤ b := (le_max_left K _).trans hb_min
  have hD_le_b : 4 * (D + 1) ^ 2 ≤ b := (le_max_right K _).trans hb_min
  have h4B_le_pow : 4 * doubleTabCodeBound c d q (2 * childRouterHalfInd #S) ≤ 2 ^ b := by
    calc 4 * doubleTabCodeBound c d q (2 * childRouterHalfInd #S)
        ≤ K * b ^ D := h4B_le_K
      _ ≤ b * b ^ D := Nat.mul_le_mul_right _ hK_le_b
      _ = b ^ (D + 1) := (pow_succ' b D).symm
      _ ≤ 2 ^ b := Nat.pow_le_two_pow (by omega) hD_le_b
  calc 4 * #S * doubleTabCodeBound c d q (2 * childRouterHalfInd #S)
      = #S * (4 * doubleTabCodeBound c d q (2 * childRouterHalfInd #S)) := by ring
    _ ≤ 2 ^ (A * b) * 2 ^ b := Nat.mul_le_mul hS_le h4B_le_pow
    _ = 2 ^ ((q - 1) * b) := by
        rw [← Nat.pow_add]; congr 1
        dsimp [q, childRouterRep, A, c]
        ring

/-- **Closed-form mixed-domain child-router concentration** ([LiLiangYuZhou2024],
`arXiv:2310.20536v1`, Appendix B, Corollary B.5(c), PDF p. 43 / printed p. 42): for pre-given
constants `ε_inv, α_inv` with `2 ^ s * T ≤ T ^ max α_inv 1`,
`childRouterThreshold ε_inv α_inv ≤ #S`, and `2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S`,
every bucket load lies within `± (1/5)(#S / 2 ^ s) ^ (2/3)` of `#S / 2 ^ s` except with seed
density `≤ 1 / (4 * (#S) ^ 2)`. -/
theorem dens_childRouter_bucketLoad_outside_le_of_threshold {ε_inv α_inv s T : ℕ}
    (hgap : 2 ^ s * T ≤ T ^ max α_inv 1)
    (S : Finset (Fin (2 ^ s) × Fin T))
    (hthresh : childRouterThreshold ε_inv α_inv ≤ #S)
    (hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S) :
    let c := childRouterChars ε_inv
    let q := childRouterRep ε_inv α_inv
    let b := childRouterCharBits c T
    (dens {θ : ChildRouterSeed c q b s |
      ¬ ∀ bucket : Fin (2 ^ s),
        (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ∧
          (bucketLoad (childRouterRound c q b s T θ) S bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ s : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  have hc : 1 ≤ childRouterChars ε_inv := by
    dsimp [childRouterChars]; have := le_max_right ε_inv 1; omega
  have hq : 1 ≤ childRouterRep ε_inv α_inv := by dsimp [childRouterRep]; omega
  exact dens_childRouter_bucketLoad_outside_le hc hq
    (le_two_pow_mul_childRouterCharBits hc) S
    (childRouter_code_le_of_threshold hgap S hthresh) hconc

/-- **Closed-form flat-domain child-router concentration on `Fin (2 ^ L)`** ([LiLiangYuZhou2024],
`arXiv:2310.20536v1`, Section 5.4, Lemma 5.1(c), PDF p. 32 / printed p. 31, and Appendix B,
PDF pp. 41–42 / printed pp. 40–41): specialization of
`dens_childRouter_bucketLoad_outside_le_of_threshold` to `T = 2 ^ (L - s)` via `bitDomainEquiv hsL`.
-/
theorem dens_childRouterBit_bucketLoad_outside_le {ε_inv α_inv s L : ℕ}
    (hsL : s ≤ L) (hgap : L ≤ max α_inv 1 * (L - s))
    (S : Finset (Fin (2 ^ L)))
    (hthresh : childRouterThreshold ε_inv α_inv ≤ #S)
    (hconc : 2 ^ s * (150 * childRouterHalfInd #S) ^ 3 ≤ #S) :
    let c := childRouterChars ε_inv
    let q := childRouterRep ε_inv α_inv
    let b := childRouterCharBits c (2 ^ (L - s))
    (dens {θ : ChildRouterSeed c q b s |
      ¬ ∀ bucket : Fin (2 ^ s),
        (#S : ℝ) / (2 ^ s : ℝ) - ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3) ≤
            (bucketLoad (childRouterRound c q b s (2 ^ (L - s)) θ)
              (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ∧
          (bucketLoad (childRouterRound c q b s (2 ^ (L - s)) θ)
              (S.map (bitDomainEquiv hsL).toEmbedding) bucket : ℝ) ≤
            (#S : ℝ) / (2 ^ s : ℝ) + ((1 : ℝ) / 5) * ((#S : ℝ) / (2 ^ s : ℝ)) ^ ((2 : ℝ) / 3)} :
      ℝ) ≤ 1 / (4 * (#S : ℝ) ^ 2) := by
  have hgap_pow : 2 ^ s * 2 ^ (L - s) ≤ (2 ^ (L - s)) ^ max α_inv 1 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hsL, ← Nat.pow_mul, Nat.mul_comm (L - s)]
    exact Nat.pow_le_pow_right (by decide) hgap
  let S' := S.map (bitDomainEquiv hsL).toEmbedding
  have hcard : #S' = #S := card_map _
  simpa only [S', hcard] using
    dens_childRouter_bucketLoad_outside_le_of_threshold hgap_pow S' (hcard.symm ▸ hthresh)
      (hcard.symm ▸ hconc)

/-- When `s ≥ childRouterMinS` (`2100 ^ 3`), the paper's condition `2 ^ s * s ^ 4 ≤ n` implies
the quantitative concentration hypothesis `2 ^ s * (150 * childRouterHalfInd n) ^ 3 ≤ n`
([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Appendix B, Claim B.3 proof, PDF p. 42 /
printed p. 41). -/
theorem childRouter_conc_of_two_pow_mul_pow_four_le {s n : ℕ}
    (hs : childRouterMinS ≤ s) (hn : 2 ^ s * s ^ 4 ≤ n) :
    2 ^ s * (150 * childRouterHalfInd n) ^ 3 ≤ n := by
  set x := n / 2 ^ s
  have hs_val : 2100 ^ 3 ≤ s := hs
  have hs4_x : s ^ 4 ≤ x :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos s)).mpr (by rwa [Nat.mul_comm])
  have hx2 : 2 ≤ x := by
    have hs2 : 2 ≤ s := by omega
    have : 2 ^ 4 ≤ s ^ 4 := Nat.pow_le_pow_left hs2 4
    omega
  set Lx := Nat.clog 2 (max x 2)
  have hmax_x : max x 2 = x := max_eq_left hx2
  have hn_le_pow : max n 2 ≤ 2 ^ (s + 1 + Lx) := by
    have hn_lt : n < 2 ^ s * (x + 1) := by
      calc n = 2 ^ s * x + n % 2 ^ s := (Nat.div_add_mod n (2 ^ s)).symm
        _ < 2 ^ s * x + 2 ^ s := Nat.add_lt_add_left (Nat.mod_lt n (Nat.two_pow_pos s)) _
        _ = 2 ^ s * (x + 1) := by ring
    have hx_le : x ≤ 2 ^ Lx := (le_max_left x 2).trans (Nat.le_pow_clog (by decide) _)
    have hn_le : n ≤ 2 ^ (s + 1 + Lx) := by
      calc n ≤ 2 ^ s * (2 * x) := hn_lt.le.trans (Nat.mul_le_mul_left (2 ^ s) (by omega))
        _ ≤ 2 ^ s * (2 * 2 ^ Lx) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hx_le)
        _ = 2 ^ (s + 1 + Lx) := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]; ring
    exact max_le hn_le (calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ (s + 1 + Lx) := Nat.pow_le_pow_right (by decide) (by omega))
  have hm_le : childRouterHalfInd n ≤ 3 * s + 3 * Lx + 7 := by
    have hclog : Nat.clog 2 (max n 2) ≤ s + 1 + Lx := Nat.clog_le_of_le_pow hn_le_pow
    dsimp [childRouterHalfInd]; omega
  have hcube_x : (150 * childRouterHalfInd n) ^ 3 ≤ x := by
    by_cases hLx : Lx ≤ s
    · have h150 : 150 * childRouterHalfInd n ≤ 1050 * s := by omega
      calc (150 * childRouterHalfInd n) ^ 3
          ≤ (1050 * s) ^ 3 := Nat.pow_le_pow_left h150 3
        _ = 1050 ^ 3 * s ^ 3 := by ring
        _ ≤ s * s ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = s ^ 4 := (pow_succ' s 3).symm
        _ ≤ x := hs4_x
    · have hs_lt : s < Lx := not_le.mp hLx
      have hpow_lt : 2 ^ (Lx - 1) < x := by
        by_contra hge
        have hclog_le := Nat.clog_le_of_le_pow (hmax_x.symm ▸ not_lt.mp hge)
        omega
      have h150 : 150 * childRouterHalfInd n ≤ 2100 * (Lx - 1) := by omega
      have hpow4 : (Lx - 1) ^ 4 ≤ 2 ^ (Lx - 1) :=
        Nat.pow_le_two_pow (by decide) (by omega)
      calc (150 * childRouterHalfInd n) ^ 3
          ≤ (2100 * (Lx - 1)) ^ 3 := Nat.pow_le_pow_left h150 3
        _ = 2100 ^ 3 * (Lx - 1) ^ 3 := by ring
        _ ≤ (Lx - 1) * (Lx - 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = (Lx - 1) ^ 4 := (pow_succ' (Lx - 1) 3).symm
        _ ≤ 2 ^ (Lx - 1) := hpow4
        _ ≤ x := hpow_lt.le
  calc 2 ^ s * (150 * childRouterHalfInd n) ^ 3
      ≤ 2 ^ s * x := Nat.mul_le_mul_left _ hcube_x
    _ ≤ n := Nat.mul_div_le n (2 ^ s)

end ChildRouter

/-! ## Section 3: ID-compressor Feistel family `ℋ_ℓ^id` (`Lemma 5.2`, `Corollary B.6`) -/

section IdCompressor

/-- **General pairwise-independent Feistel ID-compression bound (`Lemma 5.2(c)` &
`Corollary B.6(c)`)**: for any pairwise independent round family `h : ι → α → Fin (2 ^ s)` on a
nonempty finite seed space `ι` and any `S : Finset (Fin (2 ^ s) × α)`, `feistelHead (h i)` fails
to be injective on `S` with seed density at most `#S * (#S - 1) / (2 * 2 ^ s)`. -/
theorem dens_not_injOn_feistelHead_le {ι α : Type*} [Fintype ι] [Nonempty ι]
    {s : ℕ} {h : ι → α → Fin (2 ^ s)} (hh : IsPairwiseIndependentHash h)
    (S : Finset (Fin (2 ^ s) × α)) :
    (dens {i : ι | ¬ Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α))} : ℝ) ≤
      ((#S * (#S - 1) : ℕ) : ℝ) / (2 * (2 ^ s : ℝ)) := by
  classical
  have hpt (i : ι) :
      2 * (if ¬ Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α)) then (1 : ℝ) else 0) ≤
        ∑ p ∈ S.offDiag,
          if feistelHead (h i) p.1 = feistelHead (h i) p.2 then (1 : ℝ) else 0 := by
    by_cases hbad : Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α))
    · rw [ite_eq_right (not_not.mpr hbad), mul_zero]
      exact sum_nonneg fun p _ => by split_ifs <;> norm_num
    · rw [ite_eq_left hbad, mul_one, sum_boole]
      unfold Set.InjOn at hbad
      push Not at hbad
      obtain ⟨x, hx, y, hy, hhd, hne⟩ := hbad
      have hpair_ne : (x, y) ≠ (y, x) := fun hp => hne (congrArg Prod.fst hp)
      have hsub : ({(x, y), (y, x)} : Finset ((Fin (2 ^ s) × α) × (Fin (2 ^ s) × α))) ⊆
          {p ∈ S.offDiag | feistelHead (h i) p.1 = feistelHead (h i) p.2} := by
        intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hx, hy, hne⟩, hhd⟩
        · rw [mem_singleton.mp hp]
          exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hy, hx, hne.symm⟩, hhd.symm⟩
      have h2 : 2 ≤ #{p ∈ S.offDiag | feistelHead (h i) p.1 = feistelHead (h i) p.2} := by
        calc 2 = #({(x, y), (y, x)} : Finset _) := (card_pair hpair_ne).symm
          _ ≤ _ := card_le_card hsub
      exact_mod_cast h2
  have hpair : ∀ p ∈ S.offDiag,
      𝔼 i : ι, (if feistelHead (h i) p.1 = feistelHead (h i) p.2 then (1 : ℝ) else 0) ≤
        ((2 ^ s : ℝ))⁻¹ := by
    intro p hp
    rcases mem_offDiag.mp hp with ⟨_, _, hne⟩
    by_cases hsnd : p.1.2 = p.2.2
    · have hzero (i : ι) :
          (if feistelHead (h i) p.1 = feistelHead (h i) p.2 then (1 : ℝ) else 0) = 0 :=
        ite_eq_right (feistelHead_ne_of_snd_eq_of_ne hsnd hne)
      simp only [hzero, Fintype.expect_const]
      positivity
    · let e : Fin (2 ^ s) ≃ Fin (2 ^ s) := Equiv.xor (p.1.1 ^^^ p.2.1)
      have hiff (i : ι) :
          (feistelHead (h i) p.1 = feistelHead (h i) p.2) ↔ h i p.1.2 = e (h i p.2.2) := by
        dsimp only [feistelHead, e, Equiv.xor_apply]
        rw [xor_eq_iff_right_eq, ← xor_assoc]
        rfl
      simp only [hiff]
      have heq := FeistelQuotient.expect_boole_apply_eq_equiv (𝕜 := ℝ) hh hsnd e
      rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at heq
      exact heq.le
  have hexp_le :
      2 * (dens {i : ι | ¬ Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α))} : ℝ) ≤
        ((#S * (#S - 1) : ℕ) : ℝ) / (2 ^ s : ℝ) := by
    calc 2 * (dens {i : ι | ¬ Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α))} : ℝ)
        = 𝔼 i : ι,
            2 * (if ¬ Set.InjOn (feistelHead (h i)) (S : Set (Fin (2 ^ s) × α))
              then (1 : ℝ) else 0) := by
            rw [← mul_expect, Fintype.expect_boole]
      _ ≤ 𝔼 i : ι, ∑ p ∈ S.offDiag,
            if feistelHead (h i) p.1 = feistelHead (h i) p.2 then (1 : ℝ) else 0 :=
          expect_le_expect fun i _ => hpt i
      _ = ∑ p ∈ S.offDiag,
            𝔼 i : ι, (if feistelHead (h i) p.1 = feistelHead (h i) p.2 then (1 : ℝ) else 0) :=
          expect_sum_comm _ _ _
      _ ≤ ∑ _p ∈ S.offDiag, ((2 ^ s : ℝ))⁻¹ := sum_le_sum hpair
      _ = ((#S * (#S - 1) : ℕ) : ℝ) / (2 ^ s : ℝ) := by
          rw [sum_const, offDiag_card, nsmul_eq_mul, div_eq_mul_inv]
          congr 1
          rcases Nat.eq_zero_or_pos #S with h0 | hpos
          · simp [h0]
          · rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [le_div_iff₀ (by positivity)]
  have hpow_pos : (0 : ℝ) < 2 ^ s := by positivity
  rw [le_div_iff₀ hpow_pos] at hexp_le
  linarith

/-- Concrete seed space `Fin 2 → Fin (2 ^ trinomialDeg T s)` for the `2`-wise trinomial
ID-compressor Feistel family `ℋ_ℓ^id` (`Lemma 5.2` & `Corollary B.6`, with arguments `(s, T)`
matching `Fin (2 ^ s) × Fin T`). -/
abbrev IdCompressorSeed (s T : ℕ) : Type :=
  Fin 2 → Fin (2 ^ trinomialDeg T s)

/-- Exact bit length `2 * trinomialDeg T s` of an `IdCompressorSeed s T`. -/
def idCompressorSeedBits (s T : ℕ) : ℕ :=
  2 * trinomialDeg T s

theorem idCompressorSeedBits_eq (s T : ℕ) :
    idCompressorSeedBits s T = 2 * trinomialDeg T s := by
  rfl

/-- `IdCompressorSeed s T` has cardinality `2 ^ idCompressorSeedBits s T`. -/
theorem card_idCompressorSeed (s T : ℕ) :
    Fintype.card (IdCompressorSeed s T) = 2 ^ idCompressorSeedBits s T := by
  simp only [IdCompressorSeed, idCompressorSeedBits, Fintype.card_fun, Fintype.card_fin,
    ← Nat.pow_mul, Nat.mul_comm (trinomialDeg T s) 2]

/-- **Seed bit-space bound (`Corollary B.6(b)` & `Lemma 5.2(b)`)**: storing a seed in
`IdCompressorSeed s T` uses
`2 * trinomialDeg T s ≤ 6 * max ⌈log₂ max(T, 2)⌉ (max s 1) = O(s + log T)` bits. -/
theorem idCompressorSeedBits_le (s T : ℕ) :
    idCompressorSeedBits s T ≤ 6 * max (Nat.clog 2 (max T 2)) (max s 1) := by
  dsimp only [idCompressorSeedBits]
  have h := trinomialDeg_le_three_mul T s
  omega

/-- `2`-wise trinomial polynomial round function `Fin T → Fin (2 ^ s)`. -/
noncomputable def idCompressorRound (s T : ℕ) (θ : IdCompressorSeed s T) : Fin T → Fin (2 ^ s) :=
  trinomialPolyHash (trinomialStep T s) 2 T s θ

theorem idCompressorRound_eq (s T : ℕ) (θ : IdCompressorSeed s T) :
    idCompressorRound s T θ = trinomialPolyHash (trinomialStep T s) 2 T s θ := by
  rfl

theorem idCompressorRound_apply (s T : ℕ) (θ : IdCompressorSeed s T) (z : Fin T) :
    idCompressorRound s T θ z = trinomialPolyHash (trinomialStep T s) 2 T s θ z := by
  rfl

/-- Compressed `s`-bit ID head `feistelHead (idCompressorRound s T θ) x`. -/
noncomputable def idCompressorHead (s T : ℕ) (θ : IdCompressorSeed s T)
    (x : Fin (2 ^ s) × Fin T) : Fin (2 ^ s) :=
  feistelHead (idCompressorRound s T θ) x

@[simp]
theorem idCompressorHead_apply (s T : ℕ) (θ : IdCompressorSeed s T)
    (x : Fin (2 ^ s) × Fin T) :
    idCompressorHead s T θ x = feistelHead (idCompressorRound s T θ) x := by
  rfl

/-- Unconditional `2`-wise trinomial ID-compressor Feistel permutation on `Fin (2 ^ s) × Fin T`
(`Corollary B.6`). -/
noncomputable def idCompressorPerm (s T : ℕ) (θ : IdCompressorSeed s T) :
    Equiv.Perm (Fin (2 ^ s) × Fin T) :=
  feistelPairEquiv (idCompressorRound s T θ)

@[simp]
theorem idCompressorPerm_apply (s T : ℕ) (θ : IdCompressorSeed s T)
    (x : Fin (2 ^ s) × Fin T) :
    idCompressorPerm s T θ x = feistelPair (idCompressorRound s T θ) x := by
  rfl

@[simp]
theorem idCompressorPerm_symm (s T : ℕ) (θ : IdCompressorSeed s T) :
    (idCompressorPerm s T θ).symm = idCompressorPerm s T θ := by
  rfl

theorem idCompressorPerm_involutive (s T : ℕ) (θ : IdCompressorSeed s T) :
    Function.Involutive (idCompressorPerm s T θ) := by
  exact feistelPair_involutive (idCompressorRound s T θ)

theorem recoverLeft_idCompressorHead (s T : ℕ) (θ : IdCompressorSeed s T)
    (x : Fin (2 ^ s) × Fin T) :
    recoverLeft (idCompressorRound s T θ) (idCompressorHead s T θ x) x.2 = x.1 := by
  exact recoverLeft_feistelHead (idCompressorRound s T θ) x

/-- Flat mixed-domain ID-compressor Feistel permutation on `Fin (2 ^ s * T)`. -/
noncomputable def idCompressorMixedPerm (s T : ℕ) (θ : IdCompressorSeed s T) :
    Equiv.Perm (Fin (2 ^ s * T)) :=
  feistelMixedEquiv (idCompressorRound s T θ)

@[simp]
theorem idCompressorMixedPerm_apply (s T : ℕ) (θ : IdCompressorSeed s T)
    (u : Fin (2 ^ s * T)) :
    idCompressorMixedPerm s T θ u = feistelMixedEquiv (idCompressorRound s T θ) u := by
  rfl

@[simp]
theorem idCompressorMixedPerm_symm (s T : ℕ) (θ : IdCompressorSeed s T) :
    (idCompressorMixedPerm s T θ).symm = idCompressorMixedPerm s T θ := by
  exact feistelMixedEquiv_symm (idCompressorRound s T θ)

/-- Flat `Fin (2 ^ L)` ID-compressor Feistel permutation for `s ≤ L` (`Lemma 5.2`). -/
noncomputable def idCompressorBitPerm {s L : ℕ} (hsL : s ≤ L)
    (θ : IdCompressorSeed s (2 ^ (L - s))) : Equiv.Perm (Fin (2 ^ L)) :=
  feistelBitEquiv hsL (idCompressorRound s (2 ^ (L - s)) θ)

@[simp]
theorem idCompressorBitPerm_apply {s L : ℕ} (hsL : s ≤ L)
    (θ : IdCompressorSeed s (2 ^ (L - s))) (u : Fin (2 ^ L)) :
    idCompressorBitPerm hsL θ u =
      feistelBitEquiv hsL (idCompressorRound s (2 ^ (L - s)) θ) u := by
  rfl

@[simp]
theorem idCompressorBitPerm_symm {s L : ℕ} (hsL : s ≤ L)
    (θ : IdCompressorSeed s (2 ^ (L - s))) :
    (idCompressorBitPerm hsL θ).symm = idCompressorBitPerm hsL θ := by
  exact feistelBitEquiv_symm hsL (idCompressorRound s (2 ^ (L - s)) θ)

/-- `idCompressorRound s T` is unconditionally `2`-wise independent for all `s, T : ℕ`. -/
theorem isKWiseIndependentHash_idCompressorRound (s T : ℕ) :
    IsKWiseIndependentHash 2 (idCompressorRound s T) := by
  exact isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg T s)
    (le_trinomialDeg T s)

/-- **Unconditional mixed-domain ID-compressor pairwise-collision bound** ([LiLiangYuZhou2024],
`arXiv:2310.20536v1`, Appendix B, Corollary B.6(c), PDF pp. 43–44 / printed pp. 42–43): on any
finite set `S`, `idCompressorHead s T θ` fails to be injective on `S` with seed density at most
`(#S) ^ 2 / (2 * 2 ^ s)` (hence also `≤ (#S) ^ 2 / 2 ^ s`). -/
theorem dens_not_injOn_idCompressorHead_le (s T : ℕ) (S : Finset (Fin (2 ^ s) × Fin T)) :
    (dens {θ : IdCompressorSeed s T |
      ¬ Set.InjOn (idCompressorHead s T θ) (S : Set (Fin (2 ^ s) × Fin T))} : ℝ) ≤
      (#S : ℝ) ^ 2 / (2 * (2 ^ s : ℝ)) := by
  have hpw := (isKWiseIndependentHash_idCompressorRound s T).isPairwiseIndependentHash le_rfl
  have hbase := dens_not_injOn_feistelHead_le hpw S
  refine hbase.trans ?_
  gcongr
  have hnat : #S * (#S - 1) ≤ #S ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_left #S (Nat.sub_le #S 1)
  exact_mod_cast hnat

/-- `PMF.uniformOfFintype` event-probability form of `dens_not_injOn_idCompressorHead_le`. -/
theorem prob_not_injOn_idCompressorHead_le (s T : ℕ) (S : Finset (Fin (2 ^ s) × Fin T)) :
    ((PMF.uniformOfFintype (IdCompressorSeed s T)).toOuterMeasure
      {θ : IdCompressorSeed s T |
        ¬ Set.InjOn (idCompressorHead s T θ) (S : Set (Fin (2 ^ s) × Fin T))}).toReal ≤
      (#S : ℝ) ^ 2 / (2 * (2 ^ s : ℝ)) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    dens_not_injOn_idCompressorHead_le s T S

/-- **Section 5.4 `2 / n_next ^ 2` instantiation of `Corollary B.6(c)`**
([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Section 5.4, PDF p. 33 / printed p. 32): whenever
`#S ≤ n_bar`, `1 ≤ n_next`, and `n_bar ^ 2 * n_next ^ 2 ≤ 4 * 2 ^ s` (satisfied both when
`n_bar ≤ 2 * n_next ∧ n_next ^ 4 ≤ 2 ^ s` and when `n_next ≤ n_bar ∧ n_bar ^ 4 ≤ 2 * 2 ^ s`),
collision probability is `≤ 2 / n_next ^ 2`. -/
theorem dens_not_injOn_idCompressorHead_le_two_div_sq {s T n_bar n_next : ℕ}
    (S : Finset (Fin (2 ^ s) × Fin T)) (hS : #S ≤ n_bar) (hn : 1 ≤ n_next)
    (hI : n_bar ^ 2 * n_next ^ 2 ≤ 4 * 2 ^ s) :
    (dens {θ : IdCompressorSeed s T |
      ¬ Set.InjOn (idCompressorHead s T θ) (S : Set (Fin (2 ^ s) × Fin T))} : ℝ) ≤
      2 / (n_next : ℝ) ^ 2 := by
  refine (dens_not_injOn_idCompressorHead_le s T S).trans ?_
  have hS_sq : (#S : ℝ) ^ 2 ≤ (n_bar : ℝ) ^ 2 := by gcongr
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hI_real : (n_bar : ℝ) ^ 2 * (n_next : ℝ) ^ 2 ≤ 4 * (2 ^ s : ℝ) := by exact_mod_cast hI
  nlinarith [mul_le_mul_of_nonneg_right hS_sq (sq_nonneg (n_next : ℝ))]

/-- **Unconditional flat-domain ID-compressor collision bound on `Fin (2 ^ L)`**
([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Section 5.4, Lemma 5.2(c), PDF p. 33 / printed p. 32,
and Appendix B, PDF pp. 42–43 / printed pp. 41–42): for `s ≤ L` and any `S : Finset (Fin (2 ^ L))`,
the compressed `s`-bit heads fail to be pairwise distinct on `S` with seed density at most
`(#S) ^ 2 / (2 * 2 ^ s)` (hence also `≤ (#S) ^ 2 / 2 ^ s`). -/
theorem dens_not_injOn_idCompressorBit_le {s L : ℕ} (hsL : s ≤ L) (S : Finset (Fin (2 ^ L))) :
    (dens {θ : IdCompressorSeed s (2 ^ (L - s)) |
      ¬ Set.InjOn (fun u => idCompressorHead s (2 ^ (L - s)) θ (bitDomainEquiv hsL u))
        (S : Set (Fin (2 ^ L)))} : ℝ) ≤
      (#S : ℝ) ^ 2 / (2 * (2 ^ s : ℝ)) := by
  let S' := S.map (bitDomainEquiv hsL).toEmbedding
  have hinj_iff (θ : IdCompressorSeed s (2 ^ (L - s))) :
      Set.InjOn (fun u => idCompressorHead s (2 ^ (L - s)) θ (bitDomainEquiv hsL u))
          (S : Set (Fin (2 ^ L))) ↔
        Set.InjOn (idCompressorHead s (2 ^ (L - s)) θ)
          (S' : Set (Fin (2 ^ s) × Fin (2 ^ (L - s)))) :=
    ⟨fun h x hx y hy heq => by
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
      exact congrArg _ (h hu hv heq),
     fun h u hu v hv heq =>
      (bitDomainEquiv hsL).injective (h (mem_map_of_mem _ hu) (mem_map_of_mem _ hv) heq)⟩
  have hcard : #S' = #S := card_map _
  simpa only [hinj_iff, hcard] using dens_not_injOn_idCompressorHead_le s (2 ^ (L - s)) S'

end IdCompressor

end Cslib.DataStructure.Dictionary.FeistelPerm
