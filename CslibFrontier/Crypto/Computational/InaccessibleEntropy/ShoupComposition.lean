/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Repetition
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PPT

/-!
# Shoup XOR-masking composition (`[Shoup2000]`, `[HHRVW2020]` Lemma 5.7)

This module formalizes Shoup's XOR-masking composition theorem (`[Shoup2000]`; restated as
`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, pp. 29–30), stretching a target collision-resistant
shrinking compression function
$H_K : \{0, 1\}^{b + s} \to \{0, 1\}^b$ ($s \ge 1$) to $t$ sequential steps with a single shared
subkey $K$ and $\lfloor \log_2 t \rfloor + 1$ public $b$-bit XOR masks (`O(|K| + b log t)` total
key bits):

1. **2-adic valuation combinatorics (`shoupIsLastOcc`, `shoupLastOcc`,
   `shoupLastOcc_gt_between`)**: proves the binary trailing-zero (`padicValNat 2`) and
   last-occurrence monotonicity properties underlying Shoup's masking schedule (`[Shoup2000]`;
   `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, pp. 29–30) purely over `ℕ`, and certifies
   `padicValNat 2` and `shoupIsLastOcc` in deterministic polynomial time.
2. **XOR-masked sequential cascade (`shoupState`, `shoupCascade`,
   `exists_shoupCascade_step_collision`)**: iterates `i = 1, ..., t` with mask
   `BitString.listRow b (padicValNat 2 i) masks` and `s`-bit chunk `shoupChunk b s i x`,
   extracting an in-range step collision `(1 ≤ i ≤ t)` from any fixed-length message collision
   when `b ≤ L ≤ b + t * s`.
3. **Key-construction bijection (`shoupPackMasks`, `shoupStepInput_shoupPackMasks`,
   `uniformList_map_shoupPackMasks`, `computableInPolyTime_shoupPackMasks`)**: implements Shoup's
   mask reconstruction via one clean downward scan, proving both that step `iStar` receives
   `listRow b (padicValNat 2 iStar) T ++ shoupChunk b s iStar x` and that `T ↦ shoupPackMasks ... T`
   preserves `BitString.uniformList (shoupMasksLen b t)` via an explicit left-inverse
   `shoupUnpackMasks`.
4. **Target collision-resistant composition (`shoupComposeKeyLen`, `shoupComposeEval`,
   `shoupComposeAdversary`, `targetCollisionResistantOn_shoupCompose`)**: packages `[Shoup2000]` /
   `[HHRVW2020]` Lemma 5.7 cleanly with `O(|y| log t)` key length
   (`shoupComposeKeyLen_le`) and explicit multiplicative loss `dyadicSize (t n)`.

## Main definitions

* `Cslib.Crypto.shoupMaskCount`, `Cslib.Crypto.shoupMasksLen`: number and total bit length of the
  $\lfloor \log_2 t \rfloor + 1$ XOR masks.
* `Cslib.Crypto.shoupChunk`, `Cslib.Crypto.shoupStepInput`, `Cslib.Crypto.shoupState`,
  `Cslib.Crypto.shoupCascade`: Shoup's $\nu_2(i)$-indexed XOR-masked sequential cascade.
* `Cslib.Crypto.shoupPackMasks`: polynomial-time mask-reconstruction algorithm (`[Shoup2000]`;
  `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, pp. 29–30).
* `Cslib.Crypto.shoupComposeKeyLen`, `Cslib.Crypto.shoupComposeEval`,
  `Cslib.Crypto.shoupComposeAdversary`: standalone `[HHRVW2020]` Lemma 5.7 construction and
  reduction.

## Main results

* `Cslib.Crypto.exists_shoupCascade_step_collision`: deterministic step-collision extractor from a
  distinct equal-length message collision on `shoupCascade`.
* `Cslib.Crypto.shoupStepInput_shoupPackMasks`: planted target input at step `iStar`.
* `Cslib.Crypto.uniformList_map_shoupPackMasks`: exact uniform distribution of constructed masks.
* `Cslib.Crypto.shoupComposeKeyLen_le`: `keyLen n + (Nat.log 2 (t n) + 1) * b n ≤
  (Nat.log 2 (t n) + 2) * keyLen n` when `b n ≤ keyLen n` (`O(|y| log t)` bound).
* `Cslib.Crypto.targetCollisionResistantOn_shoupCompose`: `[Shoup2000]` / `[HHRVW2020]`
  Lemma 5.7 security theorem with explicit loss `dyadicSize (t n)`.

## References

* [V. Shoup, *A Composition Theorem for Universal One-Way Hash Functions*, EUROCRYPT 2000,
  LNCS 1807, pp. 445–452][Shoup2000]
* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 5.1.4, Lemma 5.7, pp. 29–30][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset ProbComp Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### 2-adic valuation combinatorics (`[Shoup2000]`; `[HHRVW2020]`, Lemma 5.7, pp. 29–30) -/

private theorem two_prime_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- When `1 ≤ i ≤ t`, its binary trailing-zero count satisfies `padicValNat 2 i ≤ Nat.log 2 t`. -/
theorem padicValNat_two_le_log {i t : ℕ} (hi : 1 ≤ i) (hit : i ≤ t) :
    padicValNat 2 i ≤ Nat.log 2 t := by
  have := two_prime_fact
  have hdv : 2 ^ padicValNat 2 i ≤ i := Nat.le_of_dvd hi pow_padicValNat_dvd
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega)).mpr (hdv.trans hit)

private theorem div_pow_padicValNat_odd {m v : ℕ} (hm : 1 ≤ m) (hv : padicValNat 2 m = v) :
    (m / 2 ^ v) % 2 = 1 := by
  have := two_prime_fact
  have hnd : ¬ 2 ^ (v + 1) ∣ m := hv ▸ pow_succ_padicValNat_not_dvd (by omega)
  have hm_eq : 2 ^ v * (m / 2 ^ v) = m := Nat.mul_div_cancel' (hv ▸ pow_padicValNat_dvd)
  rw [← hm_eq, pow_succ] at hnd
  have h2 : ¬ 2 ∣ m / 2 ^ v := fun h => hnd (mul_dvd_mul_left (2 ^ v) h)
  omega

/-- **Dyadic valuation midpoint property (`[Shoup2000]`)**: between `1 ≤ A < B` with
`padicValNat 2 A = padicValNat 2 B`, there exists `A < C < B` with
`padicValNat 2 A < padicValNat 2 C`. -/
theorem shoup_fact1 {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B)
    (hv : padicValNat 2 A = padicValNat 2 B) :
    ∃ C, A < C ∧ C < B ∧ padicValNat 2 A < padicValNat 2 C := by
  have := two_prime_fact
  set v := padicValNat 2 A
  let a := A / 2 ^ v
  let b := B / 2 ^ v
  have hA_eq : 2 ^ v * a = A := Nat.mul_div_cancel' pow_padicValNat_dvd
  have hB_eq : 2 ^ v * b = B := Nat.mul_div_cancel' (hv ▸ pow_padicValNat_dvd)
  have hpow_pos : 0 < 2 ^ v := Nat.pow_pos (by decide)
  have ha_odd : a % 2 = 1 := div_pow_padicValNat_odd hA rfl
  have hb_odd : b % 2 = 1 := div_pow_padicValNat_odd (by omega) hv.symm
  have hab : a < b := by
    by_contra hge
    have : b ≤ a := Nat.le_of_not_lt hge
    have : 2 ^ v * b ≤ 2 ^ v * a := Nat.mul_le_mul_left _ this
    omega
  have ha1 : a + 1 < b := by omega
  refine ⟨2 ^ v * (a + 1), ?_, ?_, ?_⟩
  · rw [← hA_eq]; exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self a) hpow_pos
  · rw [← hB_eq]; exact Nat.mul_lt_mul_of_pos_left ha1 hpow_pos
  · have h2dvd : 2 ∣ a + 1 := by omega
    have hpow_dvd : 2 ^ (v + 1) ∣ 2 ^ v * (a + 1) := by
      rw [pow_succ]; exact mul_dvd_mul_left (2 ^ v) h2dvd
    have hC_ne : 2 ^ v * (a + 1) ≠ 0 := by positivity
    exact (padicValNat_dvd_iff_le hC_ne).mp hpow_dvd

/-- **Dyadic valuation lower-bit step (`[Shoup2000]`)**: between any `1 ≤ A < B` and
`ν < min (ν₂(A)) (ν₂(B))`, `C := A + 2 ^ ν` satisfies `A < C < B` and `padicValNat 2 C = ν`. -/
theorem shoup_fact2 {A B ν : ℕ} (_hA : 1 ≤ A) (hAB : A < B)
    (hν : ν < min (padicValNat 2 A) (padicValNat 2 B)) :
    ∃ C, A < C ∧ C < B ∧ padicValNat 2 C = ν := by
  have := two_prime_fact
  have hνA : ν + 1 ≤ padicValNat 2 A := Nat.lt_min.mp hν |>.1
  have hνB : ν + 1 ≤ padicValNat 2 B := Nat.lt_min.mp hν |>.2
  have hdvdA : 2 ^ (ν + 1) ∣ A := (padicValNat_dvd_iff_le (by omega)).mpr hνA
  have hdvdB : 2 ^ (ν + 1) ∣ B := (padicValNat_dvd_iff_le (by omega)).mpr hνB
  obtain ⟨qa, hqa⟩ := hdvdA
  obtain ⟨qb, hqb⟩ := hdvdB
  have hq : qa < qb := by
    by_contra hle
    have := Nat.mul_le_mul_left (2 ^ (ν + 1)) (Nat.le_of_not_lt hle)
    omega
  have hpow_pos : 0 < 2 ^ ν := Nat.pow_pos (by decide)
  have hstep : A + 2 ^ (ν + 1) ≤ B := by
    calc A + 2 ^ (ν + 1) = 2 ^ (ν + 1) * (qa + 1) := by rw [hqa, mul_add, mul_one]
      _ ≤ 2 ^ (ν + 1) * qb := Nat.mul_le_mul_left _ hq
      _ = B := hqb.symm
  have h2pow : 2 ^ (ν + 1) = 2 * 2 ^ ν := by rw [pow_succ']
  refine ⟨A + 2 ^ ν, by omega, by omega, ?_⟩
  have hC_eq : A + 2 ^ ν = 2 ^ ν * (2 * qa + 1) := by
    rw [hqa, pow_succ]; ring
  rw [hC_eq, padicValNat.mul (by positivity) (by omega)]
  have hodd : padicValNat 2 (2 * qa + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  rw [padicValNat.prime_pow, hodd, add_zero]

/-- Predicate testing whether `k` (`1 ≤ k ≤ iStar`) is the largest index `≤ iStar` with 2-adic
valuation equal to `padicValNat 2 k`. -/
@[expose] def shoupIsLastOcc (iStar k : ℕ) : Bool :=
  decide (1 ≤ k ∧ k ≤ iStar ∧ iStar < k + 2 ^ (padicValNat 2 k + 1))

/-- Explicit last index `≤ iStar` with `padicValNat 2 p = j` (valid when `1 ≤ iStar` and
`j ≤ Nat.log 2 iStar`). -/
@[expose] def shoupLastOcc (iStar j : ℕ) : ℕ :=
  let q := iStar / 2 ^ j
  2 ^ j * (if q % 2 = 1 then q else q - 1)

theorem shoupIsLastOcc_self {iStar : ℕ} (hi : 1 ≤ iStar) :
    shoupIsLastOcc iStar iStar = true := by
  simp only [shoupIsLastOcc, decide_eq_true_eq]
  exact ⟨hi, le_rfl, Nat.lt_add_of_pos_right (Nat.pow_pos (by decide))⟩

theorem shoupIsLastOcc_unique {iStar k m : ℕ} (hk : shoupIsLastOcc iStar k = true)
    (hkm : k ≤ m) (hmi : m ≤ iStar) (hv : padicValNat 2 m = padicValNat 2 k) : m = k := by
  have := two_prime_fact
  simp only [shoupIsLastOcc, decide_eq_true_eq] at hk
  rcases hk with ⟨hk1, _, hk_lt⟩
  set v := padicValNat 2 k
  let a := k / 2 ^ v
  let b := m / 2 ^ v
  have hk_eq : 2 ^ v * a = k := Nat.mul_div_cancel' pow_padicValNat_dvd
  have hm_eq : 2 ^ v * b = m := Nat.mul_div_cancel' (hv ▸ pow_padicValNat_dvd)
  have hpow_pos : 0 < 2 ^ v := Nat.pow_pos (by decide)
  have ha_odd : a % 2 = 1 := div_pow_padicValNat_odd hk1 rfl
  have hb_odd : b % 2 = 1 := div_pow_padicValNat_odd (by omega) hv
  have hbound : 2 ^ v * b < 2 ^ v * (a + 2) := by
    calc 2 ^ v * b = m := hm_eq
      _ ≤ iStar := hmi
      _ < k + 2 ^ (v + 1) := hk_lt
      _ = 2 ^ v * (a + 2) := by rw [← hk_eq, pow_succ]; ring
  have hba : a ≤ b := by
    by_contra hlt
    have : b < a := Nat.lt_of_not_le hlt
    have : 2 ^ v * b < 2 ^ v * a := Nat.mul_lt_mul_of_pos_left this hpow_pos
    omega
  have hlt2 : b < a + 2 := Nat.lt_of_mul_lt_mul_left hbound
  have hab : b = a := by omega
  rw [← hm_eq, ← hk_eq, hab]

theorem shoupLastOcc_ge {iStar k : ℕ} (hk : 1 ≤ k) (hki : k ≤ iStar) :
    k ≤ shoupLastOcc iStar (padicValNat 2 k) := by
  have := two_prime_fact
  set v := padicValNat 2 k
  set q := iStar / 2 ^ v
  have hk_eq : 2 ^ v * (k / 2 ^ v) = k := Nat.mul_div_cancel' pow_padicValNat_dvd
  have hka_odd : (k / 2 ^ v) % 2 = 1 := by
    have hnd : ¬ 2 ^ (v + 1) ∣ k := pow_succ_padicValNat_not_dvd (by omega)
    rw [← hk_eq, pow_succ] at hnd
    have h2 : ¬ 2 ∣ (k / 2 ^ v) := fun h => hnd (mul_dvd_mul_left (2 ^ v) h)
    omega
  have hkq : k / 2 ^ v ≤ q := Nat.div_le_div_right hki
  have hq_odd_or : k / 2 ^ v ≤ if q % 2 = 1 then q else q - 1 := by
    split_ifs with hq1
    · exact hkq
    · omega
  calc k = 2 ^ v * (k / 2 ^ v) := hk_eq.symm
    _ ≤ 2 ^ v * (if q % 2 = 1 then q else q - 1) := Nat.mul_le_mul_left _ hq_odd_or

theorem shoupLastOcc_le {iStar j : ℕ} : shoupLastOcc iStar j ≤ iStar := by
  dsimp only [shoupLastOcc]
  split_ifs
  · exact Nat.mul_div_le iStar (2 ^ j)
  · exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le iStar (2 ^ j))

theorem padicValNat_two_shoupLastOcc {iStar j : ℕ} (hi : 1 ≤ iStar)
    (hj : j ≤ Nat.log 2 iStar) : padicValNat 2 (shoupLastOcc iStar j) = j := by
  have := two_prime_fact
  have hpow_pos : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hpow_le : 2 ^ j ≤ iStar :=
    (Nat.pow_le_pow_right (by decide) hj).trans (Nat.pow_log_le_self 2 (by omega))
  have hq_pos : 1 ≤ iStar / 2 ^ j := Nat.div_pos hpow_le hpow_pos
  set q := iStar / 2 ^ j
  let oddQ := if q % 2 = 1 then q else q - 1
  have hodd_pos : 1 ≤ oddQ := by dsimp only [oddQ]; split_ifs <;> omega
  have hodd_mod : oddQ % 2 = 1 := by dsimp only [oddQ]; split_ifs <;> omega
  have hodd_not_dvd : ¬ 2 ∣ oddQ := Nat.dvd_iff_mod_eq_zero.not.mpr (by omega)
  dsimp only [shoupLastOcc]
  rw [padicValNat.mul hpow_pos.ne' (Nat.ne_of_gt hodd_pos), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd_not_dvd, add_zero]

theorem shoupIsLastOcc_shoupLastOcc {iStar j : ℕ} (hi : 1 ≤ iStar)
    (hj : j ≤ Nat.log 2 iStar) : shoupIsLastOcc iStar (shoupLastOcc iStar j) = true := by
  have hpow_pos : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hpow_le : 2 ^ j ≤ iStar :=
    (Nat.pow_le_pow_right (by decide) hj).trans (Nat.pow_log_le_self 2 (by omega))
  have hq_pos : 1 ≤ iStar / 2 ^ j := Nat.div_pos hpow_le hpow_pos
  set q := iStar / 2 ^ j
  let oddQ := if q % 2 = 1 then q else q - 1
  have hodd_pos : 1 ≤ oddQ := by dsimp only [oddQ]; split_ifs <;> omega
  have hodd_mod : oddQ % 2 = 1 := by dsimp only [oddQ]; split_ifs <;> omega
  have hp_pos : 1 ≤ shoupLastOcc iStar j := Nat.mul_pos hpow_pos hodd_pos
  have hv : padicValNat 2 (shoupLastOcc iStar j) = j := padicValNat_two_shoupLastOcc hi hj
  have hi_lt : iStar < shoupLastOcc iStar j + 2 ^ (j + 1) := by
    have hdiv : iStar < 2 ^ j * (q + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have hdm := Nat.div_add_mod iStar (2 ^ j)
      have hml := Nat.mod_lt iStar hpow_pos
      dsimp only [q]
      linarith
    have hq_le : q + 1 ≤ oddQ + 2 := by dsimp only [oddQ]; split_ifs <;> omega
    calc iStar < 2 ^ j * (q + 1) := hdiv
      _ ≤ 2 ^ j * (oddQ + 2) := Nat.mul_le_mul_left _ hq_le
      _ = shoupLastOcc iStar j + 2 ^ (j + 1) := by
        dsimp only [shoupLastOcc, oddQ]; rw [pow_succ]; ring
  simp only [shoupIsLastOcc, decide_eq_true_eq, hv]
  exact ⟨hp_pos, shoupLastOcc_le, hi_lt⟩

theorem shoupLastOcc_padicValNat_eq {iStar k : ℕ} (hk : shoupIsLastOcc iStar k = true) :
    shoupLastOcc iStar (padicValNat 2 k) = k := by
  have hk' := hk
  simp only [shoupIsLastOcc, decide_eq_true_eq] at hk'
  have hi : 1 ≤ iStar := by omega
  have hj : padicValNat 2 k ≤ Nat.log 2 iStar := padicValNat_two_le_log hk'.1 hk'.2.1
  exact shoupIsLastOcc_unique hk
    (shoupLastOcc_ge hk'.1 hk'.2.1) shoupLastOcc_le
    (padicValNat_two_shoupLastOcc hi hj)

/-- **Last-occurrence breakpoint monotonicity (`[Shoup2000]`)**: if `hi` is a last occurrence and
no index strictly between `lo` and `hi` is a last occurrence, then every `i ∈ (lo, hi)`
(`1 ≤ i`) has its own last
occurrence strictly above `hi`. -/
theorem shoupLastOcc_gt_between {iStar lo hi i : ℕ}
    (hhi_last : shoupIsLastOcc iStar hi = true)
    (hbetween : ∀ m, lo < m → m < hi → shoupIsLastOcc iStar m = false)
    (h1 : 1 ≤ i) (hlo : lo < i) (hhi : i < hi) :
    hi < shoupLastOcc iStar (padicValNat 2 i) := by
  have hhi_info := hhi_last
  simp only [shoupIsLastOcc, decide_eq_true_eq] at hhi_info
  have hi_le : i ≤ iStar := hhi.le.trans hhi_info.2.1
  let p' := shoupLastOcc iStar (padicValNat 2 i)
  have hp'_last : shoupIsLastOcc iStar p' = true :=
    shoupIsLastOcc_shoupLastOcc (by omega) (padicValNat_two_le_log h1 hi_le)
  have hp'_ge : i ≤ p' := shoupLastOcc_ge h1 hi_le
  have hp'_le_iStar : p' ≤ iStar := shoupLastOcc_le
  have hp'_ne : p' ≠ i := by
    intro heq
    have hf := hbetween i hlo hhi
    rw [← heq, hp'_last] at hf
    exact Bool.false_ne_true hf.symm
  have hp'_gt : i < p' := lt_of_le_of_ne hp'_ge hp'_ne.symm
  have hp'_not_lt : ¬ p' < hi := by
    intro hlt
    have hf := hbetween p' (hlo.trans hp'_gt) hlt
    rw [hp'_last] at hf
    exact Bool.false_ne_true hf.symm
  rcases eq_or_lt_of_le (not_lt.mp hp'_not_lt) with hpeq | hpgt
  · exfalso
    have hv_iB : padicValNat 2 i = padicValNat 2 hi := by
      have hp_val := padicValNat_two_shoupLastOcc (by omega : 1 ≤ iStar)
        (padicValNat_two_le_log h1 hi_le)
      change padicValNat 2 p' = _ at hp_val
      rw [← hp_val, hpeq]
    obtain ⟨C₀, hC₀_lt1, hC₀_lt2, hC₀_val⟩ := shoup_fact1 h1 hhi hv_iB
    let S := (Finset.Ioo i hi).filter fun c => padicValNat 2 i < padicValNat 2 c
    have hS_ne : S.Nonempty :=
      ⟨C₀, Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hC₀_lt1, hC₀_lt2⟩, hC₀_val⟩⟩
    obtain ⟨C, hC_mem, hC_max⟩ := S.exists_max_image (fun c => padicValNat 2 c) hS_ne
    have hC_lt : i < C ∧ C < hi := Finset.mem_Ioo.mp (Finset.mem_filter.mp hC_mem).1
    have hC_val_gt : padicValNat 2 i < padicValNat 2 C := (Finset.mem_filter.mp hC_mem).2
    have hC_not_last : shoupIsLastOcc iStar C = false :=
      hbetween C (hlo.trans hC_lt.1) hC_lt.2
    let D := shoupLastOcc iStar (padicValNat 2 C)
    have hD_last : shoupIsLastOcc iStar D = true :=
      shoupIsLastOcc_shoupLastOcc (by omega)
        (padicValNat_two_le_log (by omega) (hC_lt.2.le.trans hhi_info.2.1))
    have hD_val : padicValNat 2 D = padicValNat 2 C :=
      padicValNat_two_shoupLastOcc (by omega)
        (padicValNat_two_le_log (by omega) (hC_lt.2.le.trans hhi_info.2.1))
    have hD_ge : C ≤ D := shoupLastOcc_ge (by omega) (hC_lt.2.le.trans hhi_info.2.1)
    have hD_neC : D ≠ C := fun h => by
      rw [h, hC_not_last] at hD_last
      exact Bool.false_ne_true hD_last
    have hCD : C < D := lt_of_le_of_ne hD_ge hD_neC.symm
    have hBD : hi < D := by
      by_contra hle
      rcases eq_or_lt_of_le (not_lt.mp hle) with hDeq | hDlt
      · rw [hDeq, ← hv_iB] at hD_val
        omega
      · have hf := hbetween D (hlo.trans (hC_lt.1.trans hCD)) hDlt
        rw [hD_last] at hf
        exact Bool.false_ne_true hf.symm
    obtain ⟨E, hCE, hED, hE_val⟩ := shoup_fact1 (by omega) hCD hD_val.symm
    have hBE : hi < E := by
      by_contra hle
      rcases eq_or_lt_of_le (not_lt.mp hle) with hEeq | hElt
      · rw [hEeq, ← hv_iB] at hE_val
        omega
      · have hE_inS : E ∈ S := Finset.mem_filter.mpr
          ⟨Finset.mem_Ioo.mpr ⟨hC_lt.1.trans hCE, hElt⟩, hC_val_gt.trans hE_val⟩
        have hmaxE := hC_max E hE_inS
        omega
    have hmin_gt : padicValNat 2 hi < min (padicValNat 2 E) (padicValNat 2 D) :=
      lt_min (hv_iB ▸ hC_val_gt.trans hE_val) (hv_iB ▸ hD_val ▸ hC_val_gt)
    obtain ⟨F, hEF, hFD, hF_val⟩ := shoup_fact2 (by omega) hED hmin_gt
    have hBF : hi < F := hBE.trans hEF
    have hF_le : F ≤ iStar := hFD.le.trans shoupLastOcc_le
    have hFeq : F = hi := shoupIsLastOcc_unique hhi_last hBF.le hF_le hF_val
    omega
  · exact hpgt

/-! ### Polynomial-time certificates for `padicValNat 2` and `shoupIsLastOcc` -/

private def padicValStep (state : ℕ × ℕ) : ℕ × ℕ :=
  if decide (state.1 = 0) then state
  else if decide (state.1 % 2 = 0) then (state.1 / 2, state.2 + 1)
  else state

@[fun_prop]
theorem computableInPolyTime_padicValNat_two :
    ComputableInPolyTime (padicValNat 2) encUnary encUnary := by
  have := two_prime_fact
  have hstep : ComputableInPolyTime padicValStep (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by
    unfold padicValStep
    have h0 : ComputableInPolyTime (fun state : ℕ × ℕ => decide (state.1 = 0))
        (encPair encUnary encUnary) encBool :=
      ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.fst encUnary encUnary) (ComputableInPolyTime.const 0)
    have hmod : ComputableInPolyTime (fun state : ℕ × ℕ => decide (state.1 % 2 = 0))
        (encPair encUnary encUnary) encBool :=
      ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.unary_mod.comp
          ((ComputableInPolyTime.fst encUnary encUnary).prod (ComputableInPolyTime.const 2)))
        (ComputableInPolyTime.const 0)
    have hnext : ComputableInPolyTime (fun state : ℕ × ℕ => (state.1 / 2, state.2 + 1))
        (encPair encUnary encUnary) (encPair encUnary encUnary) := by
      fun_prop
    exact ComputableInPolyTime.ite_decide h0 ComputableInPolyTime.id'
      (ComputableInPolyTime.ite_decide hmod hnext ComputableInPolyTime.id')
  obtain ⟨hefficient, hspec⟩ := ComputableInPolyTime.iterate_spec (count := id)
    (init := fun n => (n, 0)) (encIn := encUnary) .id' (by fun_prop) hstep
    (fun n i state => state.1 + state.2 ≤ n ∧ (n = 0 → state = (0, 0)) ∧
      (0 < n → 0 < state.1 ∧ (state.1 % 2 = 1 ∨ state.1 + i ≤ n) ∧
        padicValNat 2 state.1 + state.2 = padicValNat 2 n))
    (fun n => by
      refine ⟨by simp, fun hn0 => by simp [hn0], fun hn => ?_⟩
      exact ⟨hn, Or.inr (by omega), by simp⟩)
    (fun n i state _ h => by
      dsimp only [padicValStep]
      by_cases h0 : state.1 = 0
      · have h0_b : decide (state.1 = 0) = true := decide_eq_true h0
        simp only [h0_b, ↓reduceIte]
        refine ⟨h.1, h.2.1, fun hn_pos => ?_⟩
        exact absurd h0 (h.2.2 hn_pos).1.ne'
      · have h0_b : decide (state.1 = 0) = false := decide_eq_false h0
        simp only [h0_b, Bool.false_eq_true, ↓reduceIte]
        have hpos : 0 < n := Nat.pos_of_ne_zero fun hn0 => h0 (congrArg Prod.fst (h.2.1 hn0))
        obtain ⟨hs1, hdisj, hval⟩ := h.2.2 hpos
        by_cases hmod : state.1 % 2 = 0
        · have hmod_b : decide (state.1 % 2 = 0) = true := decide_eq_true hmod
          simp only [hmod_b, ↓reduceIte]
          have hdiv_pos : 0 < state.1 / 2 := by omega
          have hdiv_eq : state.1 = 2 * (state.1 / 2) := by omega
          have hprog : state.1 + i ≤ n := hdisj.resolve_left (by omega)
          have hdiv_val : padicValNat 2 state.1 = padicValNat 2 (state.1 / 2) + 1 := by
            conv_lhs => rw [hdiv_eq, padicValNat.mul (by decide) (by omega), padicValNat_self,
              add_comm]
          refine ⟨by omega, fun hn0 => absurd hn0 hpos.ne', fun _ => ?_⟩
          refine ⟨hdiv_pos, Or.inr (by omega), ?_⟩
          rw [hdiv_val] at hval
          omega
        · have hmod_b : decide (state.1 % 2 = 0) = false := decide_eq_false hmod
          simp only [hmod_b, Bool.false_eq_true, ↓reduceIte]
          exact ⟨h.1, fun hn0 => absurd hn0 hpos.ne', fun _ => ⟨hs1, Or.inl (by omega), hval⟩⟩)
    (size := fun n => 2 * n + 2)
    (ComputableInPolyTime.polyBounded (show ComputableInPolyTime
      (fun n : ℕ => 2 * n + 2) encUnary encUnary from by fun_prop))
    (fun n i state _ h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
  have hresult (n : ℕ) : (padicValStep^[n] (n, 0)).2 = padicValNat 2 n := by
    have h := hspec n
    simp only [id_eq] at h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h.2.1 rfl]
      simp
    · obtain ⟨hs1, hdisj, hval⟩ := h.2.2 hn
      have hodd : (padicValStep^[n] (n, 0)).1 % 2 = 1 :=
        hdisj.resolve_right (by omega)
      have hnot_dvd : ¬ 2 ∣ (padicValStep^[n] (n, 0)).1 :=
        Nat.dvd_iff_mod_eq_zero.not.mpr (by omega)
      rw [padicValNat.eq_zero_of_not_dvd hnot_dvd, zero_add] at hval
      exact hval
  simpa only [Function.comp_def, id_eq, hresult] using hefficient.snd'

@[fun_prop]
theorem computableInPolyTime_shoupIsLastOcc {γ : Type} {encIn : γ ↪ List Bool}
    {iStar k : γ → ℕ}
    (hi : ComputableInPolyTime iStar encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun a => shoupIsLastOcc (iStar a) (k a)) encIn encBool := by
  have heq (a : γ) :
      shoupIsLastOcc (iStar a) (k a) =
        (decide (1 ≤ k a) && decide (k a ≤ iStar a) &&
          decide (iStar a < k a + 2 ^ (padicValNat 2 (k a) + 1))) := by
    simp [shoupIsLastOcc, Bool.and_assoc]
  have hpow : ComputableInPolyTime (fun a => 2 ^ (padicValNat 2 (k a) + 1)) encIn encNat :=
    ComputableInPolyTime.binary_two_pow.comp (by fun_prop)
  have hk_bin : ComputableInPolyTime k encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp hk
  have hi_bin : ComputableInPolyTime iStar encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp hi
  have hlt : ComputableInPolyTime (fun a => decide (iStar a < k a + 2 ^ (padicValNat 2 (k a) + 1)))
      encIn encBool :=
    ComputableInPolyTime.binary_lt' hi_bin (ComputableInPolyTime.binary_add' hk_bin hpow)
  have h1 : ComputableInPolyTime (fun a => decide (1 ≤ k a)) encIn encBool := by fun_prop
  have h2 : ComputableInPolyTime (fun a => decide (k a ≤ iStar a)) encIn encBool := by fun_prop
  have hall : ComputableInPolyTime
      (fun a => decide (1 ≤ k a) && decide (k a ≤ iStar a) &&
        decide (iStar a < k a + 2 ^ (padicValNat 2 (k a) + 1))) encIn encBool := by
    fun_prop
  exact funext heq ▸ hall

/-! ### Mask-count schedule and XOR-masked cascade (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7) -/

/-- Number `⌊log₂ t⌋ + 1` of `b`-bit XOR masks needed for a `t`-step Shoup cascade. -/
@[expose] def shoupMaskCount (t : ℕ) : ℕ := Nat.log 2 t + 1

/-- Total mask bit length `(⌊log₂ t⌋ + 1) * b` for `t` steps and chaining width `b`. -/
@[expose] def shoupMasksLen (b t : ℕ) : ℕ := shoupMaskCount t * b

@[fun_prop]
theorem computableInPolyTime_shoupMaskCount {γ : Type} {encIn : γ ↪ List Bool}
    {t : γ → ℕ} (ht : ComputableInPolyTime t encIn encUnary) :
    ComputableInPolyTime (fun a => shoupMaskCount (t a)) encIn encUnary := by
  unfold shoupMaskCount; fun_prop

@[fun_prop]
theorem computableInPolyTime_shoupMasksLen {γ : Type} {encIn : γ ↪ List Bool}
    {b t : γ → ℕ} (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary) :
    ComputableInPolyTime (fun a => shoupMasksLen (b a) (t a)) encIn encUnary := by
  unfold shoupMasksLen; fun_prop

/-- `s`-bit message chunk for step `i` (`1 ≤ i ≤ t`) after removing the initial `b`-bit block. -/
@[expose] def shoupChunk (b s i : ℕ) (x : List Bool) : List Bool :=
  BitString.listRow s (i - 1) (x.drop b)

@[simp]
theorem length_shoupChunk (b s i : ℕ) (x : List Bool) :
    (shoupChunk b s i x).length = s :=
  BitString.length_listRow _ _ _

/-- Input to `step` at step `i` (`1 ≤ i ≤ t`): `(state ⊕ M_{ν₂(i)}) ++ chunk_i(x)`. -/
@[expose] def shoupStepInput (b s : ℕ) (masks x : List Bool) (i : ℕ) (state : List Bool) :
    List Bool :=
  BitString.listXor b [state, BitString.listRow b (padicValNat 2 i) masks] ++
    shoupChunk b s i x

@[simp]
theorem length_shoupStepInput (b s : ℕ) (masks x : List Bool) (i : ℕ) (state : List Bool) :
    (shoupStepInput b s masks x i state).length = b + s := by
  simp [shoupStepInput]

/-- Chaining value `h_k` after `k` steps of Shoup's cascade under `step` and `masks`. -/
@[expose] def shoupState (b s : ℕ) (step : List Bool → List Bool) (masks x : List Bool) :
    ℕ → List Bool
  | 0 => BitString.listRow b 0 x
  | k + 1 => step (shoupStepInput b s masks x (k + 1) (shoupState b s step masks x k))

/-- Output of the `t`-step Shoup cascade. -/
@[expose] def shoupCascade (b s t : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) : List Bool :=
  shoupState b s step masks x t

theorem length_shoupState (b s : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x : List Bool) (k : ℕ) :
    (shoupState b s step masks x k).length = b := by
  cases k with
  | zero => simp [shoupState]
  | succ k => exact hstep _ (length_shoupStepInput _ _ _ _ _ _)

theorem length_shoupCascade (b s t : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x : List Bool) :
    (shoupCascade b s t step masks x).length = b :=
  length_shoupState b s step hstep masks x t

private def shoupIterStep (b s : ℕ) (step : List Bool → List Bool) (masks x : List Bool)
    (acc : ℕ × List Bool) : ℕ × List Bool :=
  let i := acc.1 + 1
  (i, step (shoupStepInput b s masks x i acc.2))

private theorem iterate_shoupIterStep (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (k : ℕ) :
    (shoupIterStep b s step masks x)^[k] (0, BitString.listRow b 0 x) =
      (k, shoupState b s step masks x k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

@[fun_prop]
theorem computableInPolyTime_shoupState {γ : Type} {encIn : γ ↪ List Bool}
    {b s t : γ → ℕ} {step : γ → List Bool → List Bool} {masks x : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupState (b a) (s a) (step a) (masks a) (x a) (t a))
      encIn encBits := by
  let par := fun a => (a, b a, s a, masks a, x a)
  let encPar := encPair encIn
    (encPair encUnary (encPair encUnary (encPair encBits encBits)))
  have hpar : ComputableInPolyTime par encIn encPar := by fun_prop
  let iterF : (γ × ℕ × ℕ × List Bool × List Bool) → ℕ × List Bool → ℕ × List Bool :=
    fun p acc => shoupIterStep p.2.1 p.2.2.1 (step p.1) p.2.2.2.1 p.2.2.2.2 acc
  have hiter_step : ComputableInPolyTime
      (fun q : (γ × ℕ × ℕ × List Bool × List Bool) × (ℕ × List Bool) => iterF q.1 q.2)
      (encPair encPar (encPair encUnary encBits)) (encPair encUnary encBits) := by
    unfold iterF shoupIterStep shoupStepInput shoupChunk
    fun_prop
  obtain ⟨heff, _⟩ := ComputableInPolyTime.iterateWith_spec hpar ht
    ((ComputableInPolyTime.const 0).prod
      (ComputableInPolyTime.bitsRowWithInput hb (.const 0) hx))
    hiter_step
    (fun a i acc => acc.1 = i ∧ acc.2.length = b a)
    (fun a => ⟨rfl, BitString.length_listRow _ _ _⟩)
    (fun a i acc _ ⟨hacc1, _⟩ => by
      dsimp only [iterF, shoupIterStep, par]
      exact ⟨by omega, hstep_len a _ (length_shoupStepInput _ _ _ _ _ _)⟩)
    (size := fun a => 2 * (t a + b a) + 4)
    (ComputableInPolyTime.polyBounded (show ComputableInPolyTime
      (fun a => 2 * (t a + b a) + 4) encIn encUnary from by fun_prop))
    (fun a i acc hi ⟨hacc1, hacc2⟩ => by
      simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, hacc2]
      omega)
  have hres (a : γ) :
      ((iterF (par a))^[t a] (0, BitString.listRow (b a) 0 (x a))).2 =
        shoupState (b a) (s a) (step a) (masks a) (x a) (t a) := by
    dsimp only [iterF, par]
    rw [iterate_shoupIterStep]
  exact funext hres ▸ (ComputableInPolyTime.snd encUnary encBits).comp heff

@[fun_prop]
theorem computableInPolyTime_shoupCascade {γ : Type} {encIn : γ ↪ List Bool}
    {b s t : γ → ℕ} {step : γ → List Bool → List Bool} {masks x : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupCascade (b a) (s a) (t a) (step a) (masks a) (x a))
      encIn encBits :=
  computableInPolyTime_shoupState hb hs ht hstep hstep_len hmasks hx

/-- Deterministic step-collision extraction from any equal-length collision on `shoupCascade`. -/
theorem exists_shoupCascade_step_collision {b s t L : ℕ}
    (hs_pos : 1 ≤ s) (hb_le : b ≤ L) (hL_le : L ≤ b + t * s)
    (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (masks x₀ x₁ : List Bool)
    (hx₀ : x₀.length = L) (hx₁ : x₁.length = L) (hne : x₀ ≠ x₁)
    (hcoll : shoupCascade b s t step masks x₀ = shoupCascade b s t step masks x₁) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ t ∧
      shoupStepInput b s masks x₀ i (shoupState b s step masks x₀ (i - 1)) ≠
        shoupStepInput b s masks x₁ i (shoupState b s step masks x₁ (i - 1)) ∧
      step (shoupStepInput b s masks x₀ i (shoupState b s step masks x₀ (i - 1))) =
        step (shoupStepInput b s masks x₁ i (shoupState b s step masks x₁ (i - 1))) := by
  by_contra hno
  push Not at hno
  have hback : ∀ d k, t - k = d → k ≤ t →
      shoupState b s step masks x₀ k = shoupState b s step masks x₁ k ∧
      ∀ i, k < i → i ≤ t →
        shoupChunk b s i x₀ = shoupChunk b s i x₁ := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro k hdk hk
      cases Nat.eq_or_lt_of_le hk with
      | inl hkt =>
        subst hkt
        exact ⟨hcoll, fun i hi1 hi2 => by omega⟩
      | inr hk_lt =>
        have hk1 : k + 1 ≤ t := hk_lt
        obtain ⟨hnext_state, hnext_chunks⟩ := ih (t - (k + 1)) (by omega) (k + 1) rfl hk1
        have hcoll_step :
            step (shoupStepInput b s masks x₀ (k + 1) (shoupState b s step masks x₀ k)) =
              step (shoupStepInput b s masks x₁ (k + 1) (shoupState b s step masks x₁ k)) :=
          hnext_state
        have hinp_eq :
            shoupStepInput b s masks x₀ (k + 1) (shoupState b s step masks x₀ k) =
              shoupStepInput b s masks x₁ (k + 1) (shoupState b s step masks x₁ k) := by
          have := hno (k + 1) (by omega) hk1
          exact not_ne_iff.mp fun hne_in => hcoll_step |> this hne_in
        have hlen_xor₀ : (BitString.listXor b
            [shoupState b s step masks x₀ k,
              BitString.listRow b (padicValNat 2 (k + 1)) masks]).length = b :=
          BitString.length_listXor _ _
        have hlen_xor₁ : (BitString.listXor b
            [shoupState b s step masks x₁ k,
              BitString.listRow b (padicValNat 2 (k + 1)) masks]).length = b :=
          BitString.length_listXor _ _
        have hsplit := List.append_inj hinp_eq (by rw [hlen_xor₀, hlen_xor₁])
        have hxor_eq := hsplit.1
        have hchunk_eq := hsplit.2
        have hstate_len₀ : (shoupState b s step masks x₀ k).length = b :=
          length_shoupState b s step hstep masks x₀ k
        have hstate_len₁ : (shoupState b s step masks x₁ k).length = b :=
          length_shoupState b s step hstep masks x₁ k
        have hstate_eq : shoupState b s step masks x₀ k = shoupState b s step masks x₁ k :=
          (BitString.listXor_pair_left_inj hstate_len₀ hstate_len₁
            (BitString.listRow b (padicValNat 2 (k + 1)) masks)).mp hxor_eq
        refine ⟨hstate_eq, fun i hi1 hi2 => ?_⟩
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi1) with rfl | hi_gt
        · exact hchunk_eq
        · exact hnext_chunks i hi_gt hi2
  obtain ⟨h0, hchunks⟩ := hback (t - 0) 0 rfl (Nat.zero_le t)
  have htake : x₀.take b = x₁.take b := by
    have htake0 : BitString.listRow b 0 x₀ = x₀.take b := by
      rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take]
      have hlen : b ≤ x₀.length := by omega
      rw [List.take_append_of_le_length hlen]
    have htake1 : BitString.listRow b 0 x₁ = x₁.take b := by
      rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take]
      have hlen : b ≤ x₁.length := by omega
      rw [List.take_append_of_le_length hlen]
    change BitString.listRow b 0 x₀ = BitString.listRow b 0 x₁ at h0
    rw [← htake0, ← htake1, h0]
  have hdrop : x₀.drop b = x₁.drop b := by
    apply List.ext_getElem (by simp [hx₀, hx₁])
    intro j hj₀ hj₁
    have hj_len : j < L - b := by rw [List.length_drop, hx₀] at hj₀; exact hj₀
    have hj_lt : j < t * s := by omega
    have hq_lt : j / s < t := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have hr_lt : j % s < s := Nat.mod_lt j hs_pos
    have hc := hchunks (j / s + 1) (Nat.succ_pos (j / s)) (Nat.succ_le_of_lt hq_lt)
    have hidx := congrArg (fun l => l.getD (j % s) false) hc
    have hget (x : List Bool) (hx : x.length = L) :
        (shoupChunk b s (j / s + 1) x).getD (j % s) false =
          (x.drop b)[j]'(by simp [hx]; omega) := by
      have hlen_drop : j < (x.drop b).length := by simp [hx]; omega
      dsimp only [shoupChunk]
      rw [Nat.add_sub_cancel, BitString.getD_listRow hr_lt]
      have hmul : j / s * s + j % s = j := Nat.div_add_mod' j s
      rw [hmul, List.getD_eq_getElem _ _ hlen_drop]
    rw [hget x₀ hx₀, hget x₁ hx₁] at hidx
    exact hidx
  exact hne (by rw [← List.take_append_drop b x₀, htake, hdrop, List.take_append_drop])

/-! ### Shoup XOR-mask reconstruction (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7, p. 30) -/

/-- Advance Shoup's cascade forward from step `lo` (`initH`) through steps `lo + 1, ..., hi`
(assuming `lo ≤ hi`). -/
def shoupAdvance (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (lo hi : ℕ) (initH : List Bool) : List Bool :=
  ((shoupIterStep b s step masks x)^[hi - lo] (lo, initH)).2

private theorem iterate_shoupIterStep_from (b s : ℕ) (step : List Bool → List Bool)
    (masks x : List Bool) (lo d : ℕ) :
    (shoupIterStep b s step masks x)^[d] (lo, shoupState b s step masks x lo) =
      (lo + d, shoupState b s step masks x (lo + d)) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem shoupAdvance_shoupState {b s : ℕ} (step : List Bool → List Bool)
    (masks x : List Bool) {lo hi : ℕ} (hlo : lo ≤ hi) :
    shoupAdvance b s step masks x lo hi (shoupState b s step masks x lo) =
      shoupState b s step masks x hi := by
  dsimp only [shoupAdvance]
  rw [iterate_shoupIterStep_from, Nat.add_sub_of_le hlo]

private theorem shoupAdvance_congr {b s : ℕ} (step : List Bool → List Bool)
    (m₁ m₂ x : List Bool) {lo hi : ℕ} (hlo : lo ≤ hi) (initH : List Bool)
    (hagree : ∀ i, lo < i → i ≤ hi →
      BitString.listRow b (padicValNat 2 i) m₁ = BitString.listRow b (padicValNat 2 i) m₂) :
    shoupAdvance b s step m₁ x lo hi initH = shoupAdvance b s step m₂ x lo hi initH := by
  have hd : ∀ d ≤ hi - lo,
      (shoupIterStep b s step m₁ x)^[d] (lo, initH) =
        (shoupIterStep b s step m₂ x)^[d] (lo, initH) := by
    intro d hd_le
    induction d with
    | zero => rfl
    | succ d ih =>
      have ih' := ih (Nat.le_of_succ_le hd_le)
      have hf2 : ((shoupIterStep b s step m₂ x)^[d] (lo, initH)).1 = lo + d := by
        clear hagree ih ih' hd_le
        induction d with
        | zero => rfl
        | succ d ihd => simp [Function.iterate_succ_apply', shoupIterStep, ihd]; omega
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih']
      dsimp only [shoupIterStep, shoupStepInput]
      rw [hf2, hagree _ (by omega) (by omega)]
  exact congrArg Prod.snd (hd (hi - lo) le_rfl)

@[fun_prop]
private theorem computableInPolyTime_shoupAdvance {γ : Type} {encIn : γ ↪ List Bool}
    {b s : γ → ℕ} {step : γ → List Bool → List Bool}
    {masks x : γ → List Bool} {lo hi : γ → ℕ} {initH : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hmasks : ComputableInPolyTime masks encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits)
    (hlo : ComputableInPolyTime lo encIn encUnary)
    (hhi : ComputableInPolyTime hi encIn encUnary)
    (hinit : ComputableInPolyTime initH encIn encBits)
    (hinit_len : ∀ a, (initH a).length = b a) :
    ComputableInPolyTime
      (fun a => shoupAdvance (b a) (s a) (step a) (masks a) (x a) (lo a) (hi a) (initH a))
      encIn encBits := by
  let par := fun a => (a, b a, s a, masks a, x a)
  let encPar := encPair encIn
    (encPair encUnary (encPair encUnary (encPair encBits encBits)))
  have hpar : ComputableInPolyTime par encIn encPar := by fun_prop
  let iterF : (γ × ℕ × ℕ × List Bool × List Bool) → ℕ × List Bool → ℕ × List Bool :=
    fun p acc => shoupIterStep p.2.1 p.2.2.1 (step p.1) p.2.2.2.1 p.2.2.2.2 acc
  have hiter_step : ComputableInPolyTime
      (fun q : (γ × ℕ × ℕ × List Bool × List Bool) × (ℕ × List Bool) => iterF q.1 q.2)
      (encPair encPar (encPair encUnary encBits)) (encPair encUnary encBits) := by
    unfold iterF shoupIterStep shoupStepInput shoupChunk
    fun_prop
  obtain ⟨heff, _⟩ := ComputableInPolyTime.iterateWith_spec hpar
    (ComputableInPolyTime.unary_sub' hhi hlo)
    (hlo.prod hinit) hiter_step
    (fun a i acc => acc.1 = lo a + i ∧ acc.2.length = b a)
    (fun a => ⟨(Nat.add_zero _).symm, hinit_len a⟩)
    (fun a i acc _ ⟨hacc1, _⟩ => by
      dsimp only [iterF, shoupIterStep, par]
      exact ⟨by omega, hstep_len a _ (length_shoupStepInput _ _ _ _ _ _)⟩)
    (size := fun a => 2 * (lo a + hi a + b a) + 4)
    (ComputableInPolyTime.polyBounded (show ComputableInPolyTime
      (fun a => 2 * (lo a + hi a + b a) + 4) encIn encUnary from by fun_prop))
    (fun a i acc hi_lt ⟨hacc1, hacc2⟩ => by
      simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, hacc2]
      omega)
  exact (ComputableInPolyTime.snd encUnary encBits).comp heff

private def shoupPackStep (b s t iStar : ℕ) (step : List Bool → List Bool) (x T : List Bool)
    (acc : ℕ × ℕ × List Bool × List Bool) : ℕ × ℕ × List Bool × List Bool :=
  let k := acc.1 - 1
  let activeOwner := acc.2.1
  let activeS := acc.2.2.1
  let masks := acc.2.2.2
  if decide (k = 0) || shoupIsLastOcc iStar k then
    let hk :=
      if decide (k = 0) then BitString.listRow b 0 x
      else step (BitString.listRow b (padicValNat 2 k) T ++ shoupChunk b s k x)
    let hEnd := shoupAdvance b s step masks x k (activeOwner - 1) hk
    let newMask := BitString.listXor b [hEnd, activeS]
    let newMasks := BitString.replaceRow b (shoupMaskCount t)
      (padicValNat 2 activeOwner) newMask masks
    let nextS := BitString.listRow b (padicValNat 2 k) T
    (k, k, nextS, newMasks)
  else
    (k, activeOwner, activeS, masks)

/-- Shoup's XOR-mask reconstruction algorithm (`[Shoup2000]`; `[HHRVW2020]` Lemma 5.7, p. 30):
given base step `step`, target message `x`, planted collision step `iStar` (`1 ≤ iStar ≤ t`),
and uniform random
block vector `T` of length `shoupMasksLen b t`, builds the `shoupMasksLen b t`-bit mask list `M`
satisfying both planted-input equality at `iStar` and exact uniformity. -/
def shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x T : List Bool) : List Bool :=
  let T0 := BitString.listRow (shoupMasksLen b t) 0 T
  let (_, _, _, masks) := (shoupPackStep b s t iStar step x T0)^[iStar]
    (iStar, iStar, BitString.listRow b (padicValNat 2 iStar) T0, T0)
  masks

private theorem length_replaceRow {width count j : ℕ} {x word : List Bool}
    (hx : x.length = width) :
    (BitString.replaceRow width count j x word).length = count * width := by
  unfold BitString.replaceRow
  rw [List.length_flatMap]
  have hsum : (List.range count).map
      (fun i => (if i = j then x else BitString.listRow width i word).length) =
      List.replicate count width := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    split_ifs <;> simp [hx]
  rw [hsum, List.sum_replicate, smul_eq_mul]

private theorem shoupPackMasks_spec (b s t iStar : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool) :
    let masks := shoupPackMasks b s t iStar step x T
    masks.length = shoupMasksLen b t ∧
      (∀ j, Nat.log 2 iStar < j → j < shoupMaskCount t →
        BitString.listRow b j masks = BitString.listRow b j T) ∧
      (∀ j ≤ Nat.log 2 iStar,
        let p := shoupLastOcc iStar j
        shoupState b s step masks x (p - 1) =
          BitString.listXor b [BitString.listRow b j masks, BitString.listRow b j T]) := by
  let T0 := BitString.listRow (shoupMasksLen b t) 0 T
  have hT0_len : T0.length = shoupMasksLen b t := BitString.length_listRow _ _ _
  have hT0_row (j : ℕ) (hj : j < shoupMaskCount t) :
      BitString.listRow b j T0 = BitString.listRow b j T := by
    apply List.ext_getElem (by simp)
    intro col hc1 hc2
    simp only [BitString.length_listRow] at hc1
    have hcol_bound : j * b + col < shoupMasksLen b t := by
      unfold shoupMasksLen
      calc j * b + col < j * b + b := by omega
        _ = (j + 1) * b := by ring
        _ ≤ shoupMaskCount t * b := Nat.mul_le_mul_right b hj
    rw [BitString.getElem_listRow hc1, BitString.getElem_listRow hc1,
      List.getD_eq_getElem _ _ (by dsimp only [T0]; simpa),
      show T0[j * b + col]'_ = (BitString.listRow (shoupMasksLen b t) 0 T)[j * b + col]'
        (by simpa using hcol_bound) from rfl,
      BitString.getElem_listRow hcol_bound, Nat.zero_mul, Nat.zero_add]
  let init := (iStar, iStar, BitString.listRow b (padicValNat 2 iStar) T0, T0)
  let segStart (lo : ℕ) : List Bool :=
    if lo = 0 then BitString.listRow b 0 x
    else step (BitString.listRow b (padicValNat 2 lo) T0 ++ shoupChunk b s lo x)
  let IsSeg (lo p bound : ℕ) : Prop :=
    bound ≤ lo ∧ lo < p ∧ p ≤ iStar ∧
    (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
    shoupIsLastOcc iStar p = true ∧
    ∀ m, lo < m → m < p → shoupIsLastOcc iStar m = false
  have hinv (m : ℕ) (hm : m ≤ iStar) :
      let st := (shoupPackStep b s t iStar step x T0)^[m] init
      st.1 = iStar - m ∧
      st.2.2.2.length = shoupMasksLen b t ∧
      (∀ j, Nat.log 2 iStar < j → j < shoupMaskCount t →
        BitString.listRow b j st.2.2.2 = BitString.listRow b j T0) ∧
      (if m < iStar then
        st.1 ≤ st.2.1 ∧ st.2.1 ≤ iStar ∧
        shoupIsLastOcc iStar st.2.1 = true ∧
        (∀ i', st.1 ≤ i' → i' < st.2.1 → shoupIsLastOcc iStar i' = false) ∧
        st.2.2.1 = BitString.listRow b (padicValNat 2 st.2.1) T0 ∧
        (∀ j, shoupLastOcc iStar j ≤ st.2.1 → j < shoupMaskCount t →
          BitString.listRow b j st.2.2.2 = BitString.listRow b j T0)
      else st.2.1 = 0) ∧
      (∀ lo p, IsSeg lo p (if m < iStar then st.2.1 else 0) →
        BitString.listRow b (padicValNat 2 p) st.2.2.2 =
          BitString.listXor b
            [shoupAdvance b s step st.2.2.2 x lo (p - 1) (segStart lo),
             BitString.listRow b (padicValNat 2 p) T0]) := by
    induction m with
    | zero =>
      dsimp only [Function.iterate_zero, id_eq, init]
      have hi0 : 0 < iStar := hi_pos
      refine ⟨by omega, hT0_len, fun j _ _ => rfl, ?_, ?_⟩
      · simp only [hi0, ↓reduceIte]
        exact ⟨le_rfl, le_rfl, shoupIsLastOcc_self hi_pos,
          fun _ h1 h2 => by omega, trivial, fun _ _ _ => trivial⟩
      · intro lo p hseg
        simp only [hi0, ↓reduceIte] at hseg
        rcases hseg with ⟨h1, h2, h3, _⟩
        omega
    | succ m ih =>
      have hm_le : m ≤ iStar := Nat.le_of_succ_le hm
      obtain ⟨hrem, hlen, hhi_j, hbranch, hsegs⟩ := ih hm_le
      have hm_lt : m < iStar := Nat.lt_of_succ_le hm
      simp only [hm_lt, ↓reduceIte] at hbranch hsegs
      obtain ⟨h_lt_own, h_own_le, h_own_last, h_no_between, hs_eq, h_untouched⟩ := hbranch
      rw [Function.iterate_succ_apply']
      set st := (shoupPackStep b s t iStar step x T0)^[m] init
      set k := st.1 - 1
      have hk_eq : k = iStar - (m + 1) := by dsimp only [k]; omega
      have hrem_pos : 1 ≤ st.1 := by omega
      by_cases htrig : (decide (k = 0) || shoupIsLastOcc iStar k) = true
      · -- Triggered at `k`: `k = 0 ∨ shoupIsLastOcc iStar k = true`
        have hk_trig : k = 0 ∨ shoupIsLastOcc iStar k = true := by
          simpa only [Bool.or_eq_true, decide_eq_true_eq] using htrig
        have hj0_le : padicValNat 2 st.2.1 ≤ Nat.log 2 iStar :=
          padicValNat_two_le_log (by omega) h_own_le
        have hj0_lt : padicValNat 2 st.2.1 < shoupMaskCount t :=
          lt_of_le_of_lt (hj0_le.trans (Nat.log_mono_right hit)) (Nat.lt_succ_self _)
        set hk := if decide (k = 0) then BitString.listRow b 0 x
          else step (BitString.listRow b (padicValNat 2 k) T0 ++ shoupChunk b s k x)
        have h_hk_eq : hk = segStart k := by
          dsimp only [hk, segStart]
          by_cases hk0 : k = 0 <;> simp [hk0]
        set hEnd := shoupAdvance b s step st.2.2.2 x k (st.2.1 - 1) hk
        set newMask := BitString.listXor b [hEnd, st.2.2.1]
        set newMasks := BitString.replaceRow b (shoupMaskCount t)
          (padicValNat 2 st.2.1) newMask st.2.2.2
        have hstep_pos :
            shoupPackStep b s t iStar step x T0 st =
              (k, k, BitString.listRow b (padicValNat 2 k) T0, newMasks) := by
          dsimp only [shoupPackStep]
          change (if (decide (k = 0) || shoupIsLastOcc iStar k) = true then _ else _) = _
          rw [ite_eq_left_iff.mpr (fun h => absurd htrig h)]
        rw [hstep_pos]
        have hnewMask_len : newMask.length = b := BitString.length_listXor _ _
        have hnewMasks_len : newMasks.length = shoupMasksLen b t := by
          dsimp only [shoupMasksLen]; exact length_replaceRow hnewMask_len
        have hrow_newMasks {j : ℕ} (hj : j < shoupMaskCount t) :
            BitString.listRow b j newMasks =
              if j = padicValNat 2 st.2.1 then newMask else BitString.listRow b j st.2.2.2 :=
          BitString.listRow_replaceRow hnewMask_len st.2.2.2 hj
        have h_row_lt_agree : ∀ j, j ≠ padicValNat 2 st.2.1 → j < shoupMaskCount t →
            BitString.listRow b j newMasks = BitString.listRow b j st.2.2.2 := by
          intro j hjne hjlt
          rw [hrow_newMasks hjlt]
          split_ifs with hjeq
          · exact False.elim (hjne hjeq)
          · rfl
        refine ⟨hk_eq, hnewMasks_len, ?_, ?_, ?_⟩
        · intro j hj_gt hj_lt
          have hjne : j ≠ padicValNat 2 st.2.1 := fun h => by omega
          rw [h_row_lt_agree j hjne hj_lt]
          exact hhi_j j hj_gt hj_lt
        · by_cases hm1_lt : m + 1 < iStar
          · simp only [hm1_lt, ↓reduceIte]
            have hk_pos : 1 ≤ k := by omega
            have hk_last : shoupIsLastOcc iStar k = true := hk_trig.resolve_left (by omega)
            refine ⟨le_rfl, by omega, hk_last,
              fun _ h1 h2 => by omega, trivial, ?_⟩
            intro j hlast_le hj_lt
            have hne_own : j ≠ padicValNat 2 st.2.1 := by
              intro hjeq
              have hown_eq := shoupLastOcc_padicValNat_eq h_own_last
              rw [hjeq, hown_eq] at hlast_le
              omega
            rw [h_row_lt_agree j hne_own hj_lt]
            exact h_untouched j (hlast_le.trans (by omega)) hj_lt
          · simp only [hm1_lt, ↓reduceIte]
            omega
        · intro lo p hseg
          have hbound_eq : (if m + 1 < iStar then k else 0) = k := by
            by_cases hlt : m + 1 < iStar
            · simp [hlt]
            · simp [hlt]; omega
          change IsSeg lo p (if m + 1 < iStar then k else 0) at hseg
          rw [hbound_eq] at hseg
          dsimp only
          rcases hseg with ⟨h_k_lo, h_lo_p, h_p_le, h_lo_cond, h_p_last, h_btw⟩
          rcases eq_or_lt_of_le h_k_lo with hlo_eq | hlo_gt
          · subst hlo_eq
            have hp_eq : p = st.2.1 := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hplt | hpgt
              · have := h_no_between p (by omega) hplt
                rw [h_p_last] at this; exact Bool.false_ne_true this.symm
              · have := h_btw st.2.1 (by omega) hpgt
                rw [h_own_last] at this; exact Bool.false_ne_true this.symm
            subst hp_eq
            rw [hrow_newMasks hj0_lt]
            simp only [↓reduceIte]
            dsimp only [newMask]
            have h_adv_eq :
                shoupAdvance b s step newMasks x k (st.2.1 - 1) hk =
                  shoupAdvance b s step st.2.2.2 x k (st.2.1 - 1) hk := by
              apply shoupAdvance_congr step newMasks st.2.2.2 x (by omega) hk
              intro i hi1 hi2
              have hv_i_le : padicValNat 2 i ≤ Nat.log 2 iStar :=
                padicValNat_two_le_log (by omega) (hi2.trans ((Nat.sub_le _ _).trans h_own_le))
              have hv_i_lt : padicValNat 2 i < shoupMaskCount t :=
                lt_of_le_of_lt (hv_i_le.trans (Nat.log_mono_right hit)) (Nat.lt_succ_self _)
              have hlast_gt : st.2.1 < shoupLastOcc iStar (padicValNat 2 i) :=
                shoupLastOcc_gt_between h_own_last
                  (fun m' h1 h2 => h_no_between m' (by omega) h2) (by omega) hi1 (by omega)
              have hjne : padicValNat 2 i ≠ padicValNat 2 st.2.1 := by
                intro hjeq
                have := shoupLastOcc_padicValNat_eq h_own_last
                rw [hjeq, this] at hlast_gt
                omega
              exact h_row_lt_agree _ hjne hv_i_lt
            dsimp only [hEnd]
            rw [← h_adv_eq, h_hk_eq, hs_eq]
          · have h_own_le_lo : st.2.1 ≤ lo := by
              by_contra hlt
              have hlo_lt_own : lo < st.2.1 := Nat.lt_of_not_le hlt
              rcases h_lo_cond with rfl | hlo_last
              · omega
              · have := h_no_between lo (by omega) hlo_lt_own
                rw [hlo_last] at this; exact Bool.false_ne_true this.symm
            have h_p_gt : st.2.1 < p := lt_of_le_of_lt h_own_le_lo h_lo_p
            have h_p_ne : padicValNat 2 p ≠ padicValNat 2 st.2.1 := by
              intro hjeq
              have h1 := shoupLastOcc_padicValNat_eq h_p_last
              have h2 := shoupLastOcc_padicValNat_eq h_own_last
              rw [hjeq, h2] at h1
              omega
            have h_p_lt_cnt : padicValNat 2 p < shoupMaskCount t :=
              lt_of_le_of_lt ((padicValNat_two_le_log (by omega) h_p_le).trans
                (Nat.log_mono_right hit)) (Nat.lt_succ_self _)
            rw [h_row_lt_agree _ h_p_ne h_p_lt_cnt]
            have h_prev := hsegs lo p ⟨h_own_le_lo, h_lo_p, h_p_le, h_lo_cond, h_p_last, h_btw⟩
            rw [h_prev]
            have h_adv_eq :
                shoupAdvance b s step st.2.2.2 x lo (p - 1) (segStart lo) =
                  shoupAdvance b s step newMasks x lo (p - 1) (segStart lo) := by
              apply shoupAdvance_congr step st.2.2.2 newMasks x (by omega) (segStart lo)
              intro i hi1 hi2
              have hv_i_lt : padicValNat 2 i < shoupMaskCount t :=
                lt_of_le_of_lt ((padicValNat_two_le_log (by omega)
                  (hi2.trans ((Nat.sub_le _ _).trans h_p_le))).trans (Nat.log_mono_right hit))
                  (Nat.lt_succ_self _)
              have hlast_gt : p < shoupLastOcc iStar (padicValNat 2 i) :=
                shoupLastOcc_gt_between h_p_last h_btw (by omega) hi1 (by omega)
              have hjne : padicValNat 2 i ≠ padicValNat 2 st.2.1 := by
                intro hjeq
                have := shoupLastOcc_padicValNat_eq h_own_last
                rw [hjeq, this] at hlast_gt
                omega
              exact (h_row_lt_agree _ hjne hv_i_lt).symm
            rw [h_adv_eq]
      · -- Not triggered at `k`: `1 ≤ k` and `shoupIsLastOcc iStar k = false`
        have htrig_f : (decide (k = 0) || shoupIsLastOcc iStar k) = false :=
          Bool.eq_false_iff.mpr htrig
        have hstep_neg :
            shoupPackStep b s t iStar step x T0 st = (k, st.2.1, st.2.2.1, st.2.2.2) := by
          dsimp only [shoupPackStep]
          change (if (decide (k = 0) || shoupIsLastOcc iStar k) = true then _ else _) = _
          rw [ite_eq_right_iff.mpr (fun h => absurd h htrig)]
        rw [hstep_neg]
        have hk_not0 : k ≠ 0 := fun h0 => htrig (by simp [h0])
        have hm1_lt : m + 1 < iStar := by omega
        have hk_not_last : shoupIsLastOcc iStar k = false := by
          rcases Bool.eq_false_or_eq_true (shoupIsLastOcc iStar k) with hs | hs
          · exact False.elim (htrig (by simp [hs]))
          · exact hs
        refine ⟨hk_eq, hlen, hhi_j, ?_, ?_⟩
        · simp only [hm1_lt, ↓reduceIte]
          refine ⟨by omega, h_own_le, h_own_last, fun i' hi1 hi2 => ?_, hs_eq, h_untouched⟩
          rcases eq_or_lt_of_le hi1 with rfl | hi_gt
          · exact hk_not_last
          · exact h_no_between i' (by omega) hi2
        · intro lo p hseg
          simp only [hm1_lt, ↓reduceIte] at hseg
          exact hsegs lo p hseg
  obtain ⟨_, hlen, hhi_j, _, hsegs⟩ := hinv iStar le_rfl
  set masks := shoupPackMasks b s t iStar step x T
  have hlen_masks : masks.length = shoupMasksLen b t := hlen
  have hhi_masks : ∀ j, Nat.log 2 iStar < j → j < shoupMaskCount t →
      BitString.listRow b j masks = BitString.listRow b j T := by
    intro j hj1 hj2
    dsimp only [masks, shoupPackMasks]
    rw [hhi_j j hj1 hj2, hT0_row j hj2]
  simp only [lt_irrefl, ↓reduceIte] at hsegs
  have hseg_masks : ∀ lo p, IsSeg lo p 0 →
      BitString.listRow b (padicValNat 2 p) masks =
        BitString.listXor b
          [shoupAdvance b s step masks x lo (p - 1) (segStart lo),
           BitString.listRow b (padicValNat 2 p) T0] :=
    hsegs
  have prevBreak : ∀ k, 0 < k →
      ∃ lo < k, (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
        (∀ m, lo < m → m < k → shoupIsLastOcc iStar m = false) := by
    intro k hk_pos
    let S := (Finset.range k).filter fun m => decide (m = 0 ∨ shoupIsLastOcc iStar m = true)
    have hS_ne : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_pos, by simp⟩⟩
    let lo := S.max' hS_ne
    have hlo_mem := Finset.max'_mem S hS_ne
    change lo ∈ S at hlo_mem
    dsimp only [S] at hlo_mem
    rw [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hlo_mem
    refine ⟨lo, hlo_mem.1, hlo_mem.2, fun m h1 h2 => ?_⟩
    by_contra hlast
    have hm_true : shoupIsLastOcc iStar m = true := Bool.eq_true_of_not_eq_false hlast
    have hm_mem : m ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, decide_eq_true_eq.mpr (Or.inr hm_true)⟩
    have hm_le : m ≤ lo := Finset.le_max' S m hm_mem
    omega
  have breakUniq : ∀ {lo₁ lo₂ u v}, lo₁ < u → lo₂ ≤ v → u = v + 1 →
      (lo₁ = 0 ∨ shoupIsLastOcc iStar lo₁ = true) →
      (lo₂ = 0 ∨ shoupIsLastOcc iStar lo₂ = true) →
      (∀ m, lo₁ < m → m < u → shoupIsLastOcc iStar m = false) →
      (∀ m, lo₂ < m → m ≤ v → shoupIsLastOcc iStar m = false) → lo₂ = lo₁ := by
    intro lo₁ lo₂ u v h1u h2v huv h1c h2c h1b h2b
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h2b lo₁ hlt (by omega)
      rcases h1c with h0 | hl
      · omega
      · rw [hl] at this; exact Bool.false_ne_true this.symm
    · have := h1b lo₂ hgt (by omega)
      rcases h2c with h0 | hl
      · omega
      · rw [hl] at this; exact Bool.false_ne_true this.symm
  have hmatch : ∀ k ≤ iStar,
      ∃ lo ≤ k, (lo = 0 ∨ shoupIsLastOcc iStar lo = true) ∧
        (∀ m, lo < m → m ≤ k → shoupIsLastOcc iStar m = false) ∧
        shoupState b s step masks x k = shoupAdvance b s step masks x lo k (segStart lo) := by
    intro k hk_le
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
      · refine ⟨0, le_rfl, Or.inl rfl, fun _ h1 h2 => by omega, ?_⟩
        dsimp only [shoupState, shoupAdvance, segStart]
        simp
      · obtain ⟨lo, hlo_lt, hlo_cond, hbtw⟩ := prevBreak k hk_pos
        obtain ⟨lo', hlo'_le, hlo'_cond, hbtw', hst'⟩ := ih (k - 1) (by omega) (by omega)
        have hlo_eq : lo' = lo := breakUniq hlo_lt hlo'_le (by omega) hlo_cond hlo'_cond hbtw hbtw'
        rw [hlo_eq] at hbtw' hst'
        by_cases hk_last : shoupIsLastOcc iStar k = true
        · have hseg_k : IsSeg lo k 0 := ⟨Nat.zero_le _, hlo_lt, hk_le, hlo_cond, hk_last, hbtw⟩
          have h_row_k := hseg_masks lo k hseg_k
          have h_xor_cancel :
              BitString.listXor b
                [shoupState b s step masks x (k - 1),
                 BitString.listRow b (padicValNat 2 k) masks] =
                BitString.listRow b (padicValNat 2 k) T0 := by
            rw [hst', h_row_k]
            exact BitString.listXor_pair_self_left_of_length _ (BitString.length_listRow _ _ _)
          refine ⟨k, le_rfl, Or.inr hk_last, fun _ h1 h2 => by omega, ?_⟩
          have hk_succ : k = (k - 1) + 1 := by omega
          conv_lhs => rw [hk_succ, shoupState]
          dsimp only [shoupStepInput, shoupAdvance]
          rw [← hk_succ, h_xor_cancel]
          simp [segStart, show k ≠ 0 by omega]
        · have hk_false : shoupIsLastOcc iStar k = false :=
            Bool.eq_false_of_not_eq_true hk_last
          refine ⟨lo, hlo_lt.le, hlo_cond, fun m h1 h2 => ?_, ?_⟩
          · rcases eq_or_lt_of_le h2 with rfl | hlt
            · exact hk_false
            · exact hbtw' m h1 (by omega)
          · have hk_succ : k = (k - 1) + 1 := by omega
            conv_lhs => rw [hk_succ, shoupState]
            rw [hst']
            dsimp only [shoupAdvance]
            have hsub : k - lo = (k - 1 - lo) + 1 := by omega
            rw [hsub, Function.iterate_succ_apply']
            have hfst : ((shoupIterStep b s step masks x)^[k - 1 - lo]
                (lo, segStart lo)).1 = k - 1 := by
              have hc : ∀ d, ((shoupIterStep b s step masks x)^[d] (lo, segStart lo)).1 =
                  lo + d := by
                intro d; induction d with
                | zero => rfl
                | succ d ihd => simp [Function.iterate_succ_apply', shoupIterStep, ihd]; omega
              rw [hc]; omega
            dsimp only [shoupIterStep]
            rw [hfst, ← hk_succ]
  refine ⟨hlen_masks, hhi_masks, fun j hj => ?_⟩
  let p := shoupLastOcc iStar j
  have hp_last : shoupIsLastOcc iStar p = true := shoupIsLastOcc_shoupLastOcc hi_pos hj
  have hp_info := hp_last
  simp only [shoupIsLastOcc, decide_eq_true_eq] at hp_info
  have hv_p : padicValNat 2 p = j := padicValNat_two_shoupLastOcc hi_pos hj
  have hj_lt : j < shoupMaskCount t :=
    lt_of_le_of_lt (hj.trans (Nat.log_mono_right hit)) (Nat.lt_succ_self _)
  obtain ⟨lo, hlo_lt, hlo_cond, hbtw⟩ := prevBreak p hp_info.1
  have hseg_p : IsSeg lo p 0 := ⟨Nat.zero_le _, hlo_lt, hp_info.2.1, hlo_cond, hp_last, hbtw⟩
  have h_row_p := hseg_masks lo p hseg_p
  have h_pm1_eq : shoupState b s step masks x (p - 1) =
      shoupAdvance b s step masks x lo (p - 1) (segStart lo) := by
    obtain ⟨lo', hlo'_le, hlo'_cond, hbtw', hst'⟩ := hmatch (p - 1) (by omega)
    have hlo_eq : lo' = lo := breakUniq hlo_lt hlo'_le (by omega) hlo_cond hlo'_cond hbtw hbtw'
    rw [hst', hlo_eq]
  change shoupState b s step masks x (p - 1) =
    BitString.listXor b [BitString.listRow b j masks, BitString.listRow b j T]
  rw [h_pm1_eq, ← hv_p, h_row_p, hv_p, hT0_row j hj_lt]
  have h_adv_len : (shoupAdvance b s step masks x lo (p - 1) (segStart lo)).length = b := by
    rw [← h_pm1_eq]; exact length_shoupState b s step hstep masks x (p - 1)
  rw [BitString.listXor_pair, BitString.ofList_listXor_pair, BitString.add_cancel_right,
    BitString.ofFn_ofList h_adv_len]

theorem length_shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x T : List Bool) :
    (shoupPackMasks b s t iStar step x T).length = shoupMasksLen b t := by
  have hinit : (BitString.listRow (shoupMasksLen b t) 0 T).length = shoupMasksLen b t :=
    BitString.length_listRow _ _ _
  suffices h : ∀ m acc, acc.2.2.2.length = shoupMasksLen b t →
      ((shoupPackStep b s t iStar step x
        (BitString.listRow (shoupMasksLen b t) 0 T))^[m] acc).2.2.2.length =
        shoupMasksLen b t from
    h iStar _ hinit
  intro m
  induction m with
  | zero => intro acc h; exact h
  | succ m ih =>
    intro acc h
    rw [Function.iterate_succ_apply]
    apply ih
    dsimp only [shoupPackStep]
    by_cases htrig : (decide (acc.1 - 1 = 0) || shoupIsLastOcc iStar (acc.1 - 1)) = true
    · simp only [htrig, ↓reduceIte]
      dsimp only [shoupMasksLen]
      exact length_replaceRow (BitString.length_listXor _ _)
    · have htrig_f : (decide (acc.1 - 1 = 0) || shoupIsLastOcc iStar (acc.1 - 1)) = false :=
        Bool.eq_false_iff.mpr htrig
      simp only [htrig_f, Bool.false_eq_true, ↓reduceIte]
      exact h

theorem shoupStepInput_shoupPackMasks {b s t iStar : ℕ}
    (step : List Bool → List Bool) (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool) :
    let masks := shoupPackMasks b s t iStar step x T
    shoupStepInput b s masks x iStar (shoupState b s step masks x (iStar - 1)) =
      BitString.listRow b (padicValNat 2 iStar) T ++ shoupChunk b s iStar x := by
  intro masks
  obtain ⟨_, _, hplanted⟩ := shoupPackMasks_spec b s t iStar step hstep hi_pos hit x T
  have hj_le : padicValNat 2 iStar ≤ Nat.log 2 iStar := padicValNat_two_le_log hi_pos le_rfl
  have hp := hplanted (padicValNat 2 iStar) hj_le
  rw [shoupLastOcc_padicValNat_eq (shoupIsLastOcc_self hi_pos)] at hp
  dsimp only [shoupStepInput]
  rw [hp]
  have h2 : (BitString.listRow b (padicValNat 2 iStar) T).length = b :=
    BitString.length_listRow _ _ _
  rw [BitString.listXor_pair, BitString.ofList_listXor_pair,
    add_comm (BitString.ofList b (BitString.listRow b (padicValNat 2 iStar) masks))
      (BitString.ofList b (BitString.listRow b (padicValNat 2 iStar) T)),
    BitString.add_cancel_right, BitString.ofFn_ofList h2]

private def shoupUnpackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x masks : List Bool) : List Bool :=
  (List.range (shoupMaskCount t)).flatMap fun j =>
    if decide (j ≤ Nat.log 2 iStar) then
      let p := shoupLastOcc iStar j
      BitString.listXor b
        [shoupState b s step masks x (p - 1), BitString.listRow b j masks]
    else
      BitString.listRow b j masks

private theorem length_shoupUnpackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (x masks : List Bool) :
    (shoupUnpackMasks b s t iStar step x masks).length = shoupMasksLen b t := by
  unfold shoupUnpackMasks shoupMasksLen
  rw [List.length_flatMap]
  have hsum : (List.range (shoupMaskCount t)).map (fun j =>
      (if decide (j ≤ Nat.log 2 iStar) then
        BitString.listXor b
          [shoupState b s step masks x (shoupLastOcc iStar j - 1), BitString.listRow b j masks]
      else BitString.listRow b j masks).length) =
      List.replicate (shoupMaskCount t) b := by
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    split_ifs <;> simp
  rw [hsum, List.sum_replicate, smul_eq_mul]

private theorem shoupUnpack_shoupPack {b s t iStar : ℕ}
    (step : List Bool → List Bool) (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x T : List Bool)
    (hT : T.length = shoupMasksLen b t) :
    shoupUnpackMasks b s t iStar step x (shoupPackMasks b s t iStar step x T) = T := by
  obtain ⟨hlen_m, hhi_m, hlo_m⟩ := shoupPackMasks_spec b s t iStar step hstep hi_pos hit x T
  set masks := shoupPackMasks b s t iStar step x T
  have hrow_eq (j : ℕ) (hj : j < shoupMaskCount t) :
      BitString.listRow b j (shoupUnpackMasks b s t iStar step x masks) =
        BitString.listRow b j T := by
    have hrow_unp := BitString.listRow_flatMap_append
      (width := b)
      (fun k =>
        if decide (k ≤ Nat.log 2 iStar) then
          BitString.listXor b
            [shoupState b s step masks x (shoupLastOcc iStar k - 1), BitString.listRow b k masks]
        else BitString.listRow b k masks)
      (List.range (shoupMaskCount t))
      (fun k _ => by split_ifs <;> simp) [] j (by simpa using hj)
    simp only [List.append_nil, List.getElem_range] at hrow_unp
    change BitString.listRow b j (shoupUnpackMasks b s t iStar step x masks) = _ at hrow_unp
    rw [hrow_unp]
    by_cases hle : j ≤ Nat.log 2 iStar
    · simp only [decide_eq_true hle, ↓reduceIte]
      rw [hlo_m j hle]
      have h2 : (BitString.listRow b j T).length = b := BitString.length_listRow _ _ _
      rw [BitString.listXor_pair, BitString.ofList_listXor_pair,
        add_comm (BitString.ofList b (BitString.listRow b j masks)),
        BitString.add_cancel_right, BitString.ofFn_ofList h2]
    · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hhi_m j (Nat.lt_of_not_ge hle) hj
  have hlen_unp : (shoupUnpackMasks b s t iStar step x masks).length = shoupMasksLen b t :=
    length_shoupUnpackMasks b s t iStar step x masks
  apply List.ext_getElem (hlen_unp.trans hT.symm)
  intro idx hidx_unp hidx_T
  rcases Nat.eq_zero_or_pos b with rfl | hb_pos
  · rw [hT, shoupMasksLen, mul_zero] at hidx_T
    exact absurd hidx_T (Nat.not_lt_zero idx)
  · have hj : idx / b < shoupMaskCount t := by
      have hidx_mul : idx < shoupMaskCount t * b := by
        rw [← shoupMasksLen, ← hT]
        exact hidx_T
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have hr : idx % b < b := Nat.mod_lt idx hb_pos
    have hdm : idx / b * b + idx % b = idx := Nat.div_add_mod' idx b
    have hidx_get := congrArg (fun l : List Bool => l.getD (idx % b) false) (hrow_eq (idx / b) hj)
    rw [BitString.getD_listRow hr, BitString.getD_listRow hr] at hidx_get
    simpa only [hdm, List.getD_eq_getElem _ _ hidx_unp, List.getD_eq_getElem _ _ hidx_T]
      using hidx_get

/-- Shoup's Figure 1 key-construction map preserves `BitString.uniformList (shoupMasksLen b t)`
whenever `1 ≤ iStar ≤ t`. -/
theorem uniformList_map_shoupPackMasks (b s t iStar : ℕ) (step : List Bool → List Bool)
    (hstep : ∀ w, w.length = b + s → (step w).length = b)
    (hi_pos : 1 ≤ iStar) (hit : iStar ≤ t) (x : List Bool) :
    (BitString.uniformList (shoupMasksLen b t)).map (shoupPackMasks b s t iStar step x) =
      BitString.uniformList (shoupMasksLen b t) := by
  let fFin : BitString (shoupMasksLen b t) → BitString (shoupMasksLen b t) :=
    fun T => BitString.ofList (shoupMasksLen b t) (shoupPackMasks b s t iStar step x (List.ofFn T))
  have hinj : Function.Injective fFin := by
    intro T₁ T₂ heq
    have hf1 := congrArg List.ofFn heq
    dsimp only [fFin] at hf1
    rw [BitString.ofFn_ofList (length_shoupPackMasks _ _ _ _ _ _ _),
      BitString.ofFn_ofList (length_shoupPackMasks _ _ _ _ _ _ _)] at hf1
    have hu := congrArg (shoupUnpackMasks b s t iStar step x) hf1
    rw [shoupUnpack_shoupPack step hstep hi_pos hit x _ List.length_ofFn,
      shoupUnpack_shoupPack step hstep hi_pos hit x _ List.length_ofFn] at hu
    exact List.ofFn_injective hu
  let e : BitString (shoupMasksLen b t) ≃ BitString (shoupMasksLen b t) :=
    Equiv.ofBijective fFin (Finite.injective_iff_bijective.mp hinj)
  have hcomp : shoupPackMasks b s t iStar step x ∘ List.ofFn = List.ofFn ∘ e := by
    funext T
    dsimp only [Function.comp_def, e, Equiv.ofBijective, fFin]
    exact (BitString.ofFn_ofList (length_shoupPackMasks _ _ _ _ _ _ _)).symm
  calc
    (BitString.uniformList (shoupMasksLen b t)).map (shoupPackMasks b s t iStar step x)
      = (PMF.uniformOfFintype (BitString (shoupMasksLen b t))).map
          (shoupPackMasks b s t iStar step x ∘ List.ofFn) := by
        rw [BitString.uniformList, PMF.map_comp]
    _ = (PMF.uniformOfFintype (BitString (shoupMasksLen b t))).map (List.ofFn ∘ e) := by rw [hcomp]
    _ = ((PMF.uniformOfFintype (BitString (shoupMasksLen b t))).map e).map List.ofFn := by
        rw [← PMF.map_comp]
    _ = BitString.uniformList (shoupMasksLen b t) := by
        rw [PMF.uniformOfFintype_map_equiv e, BitString.uniformList]

@[fun_prop]
theorem computableInPolyTime_shoupPackMasks {γ : Type} {encIn : γ ↪ List Bool}
    {b s t iStar : γ → ℕ} {step : γ → List Bool → List Bool} {x T : γ → List Bool}
    (hb : ComputableInPolyTime b encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (ht : ComputableInPolyTime t encIn encUnary)
    (hi : ComputableInPolyTime iStar encIn encUnary)
    (hstep : ComputableInPolyTime (fun p : γ × List Bool => step p.1 p.2)
      (encPair encIn encBits) encBits)
    (hstep_len : ∀ a w, w.length = b a + s a → (step a w).length = b a)
    (hx : ComputableInPolyTime x encIn encBits)
    (hT : ComputableInPolyTime T encIn encBits) :
    ComputableInPolyTime
      (fun a => shoupPackMasks (b a) (s a) (t a) (iStar a) (step a) (x a) (T a))
      encIn encBits := by
  let T0 (a : γ) : List Bool := BitString.listRow (shoupMasksLen (b a) (t a)) 0 (T a)
  have hT0 : ComputableInPolyTime T0 encIn encBits := by
    dsimp only [T0]; fun_prop
  let par (a : γ) := (a, iStar a, x a, T0 a)
  let encPar := encPair encIn (encPair encUnary (encPair encBits encBits))
  have hpar : ComputableInPolyTime par encIn encPar := by fun_prop
  let encAcc : (ℕ × ℕ × List Bool × List Bool) ↪ List Bool :=
    encPair encUnary (encPair encUnary (encPair encBits encBits))
  let iterF : (γ × ℕ × List Bool × List Bool) →
      (ℕ × ℕ × List Bool × List Bool) → (ℕ × ℕ × List Bool × List Bool) :=
    fun p acc => shoupPackStep (b p.1) (s p.1) (t p.1) p.2.1 (step p.1) p.2.2.1 p.2.2.2 acc
  have hiter_step : ComputableInPolyTime
      (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
        iterF q.1 q.2)
      (encPair encPar encAcc) encAcc := by
    have hq11 : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) => q.1.1)
        (encPair encPar encAcc) encIn := by fun_prop
    have hb' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) => b q.1.1)
        (encPair encPar encAcc) encUnary := hb.comp hq11
    have hs' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) => s q.1.1)
        (encPair encPar encAcc) encUnary := hs.comp hq11
    have ht' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) => t q.1.1)
        (encPair encPar encAcc) encUnary := ht.comp hq11
    let hi' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.1.2.1) (encPair encPar encAcc) encUnary := by fun_prop
    let hx' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.1.2.2.1) (encPair encPar encAcc) encBits := by fun_prop
    let hT' : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.1.2.2.2) (encPair encPar encAcc) encBits := by fun_prop
    let hk_idx : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.2.1 - 1) (encPair encPar encAcc) encUnary := by fun_prop
    let hown : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.2.2.1) (encPair encPar encAcc) encUnary := by fun_prop
    let hactS : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.2.2.2.1) (encPair encPar encAcc) encBits := by fun_prop
    let hmasks : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          q.2.2.2.2) (encPair encPar encAcc) encBits := by fun_prop
    let hstep' : ComputableInPolyTime
        (fun p : ((γ × ℕ × List Bool × List Bool) ×
            (ℕ × ℕ × List Bool × List Bool)) × List Bool =>
          step p.1.1.1 p.2)
        (encPair (encPair encPar encAcc) encBits) encBits :=
      hstep.comp (show ComputableInPolyTime
        (fun p : ((γ × ℕ × List Bool × List Bool) ×
            (ℕ × ℕ × List Bool × List Bool)) × List Bool =>
          (p.1.1.1, p.2))
        (encPair (encPair encPar encAcc) encBits) (encPair encIn encBits) from by fun_prop)
    let hstep'_len : ∀ (q : (γ × ℕ × List Bool × List Bool) ×
        (ℕ × ℕ × List Bool × List Bool)) w, w.length = b q.1.1 + s q.1.1 →
        (step q.1.1 w).length = b q.1.1 := fun q w hw => hstep_len q.1.1 w hw
    let hhk (q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool)) : List Bool :=
      if decide (q.2.1 - 1 = 0) then BitString.listRow (b q.1.1) 0 q.1.2.2.1
      else step q.1.1
        (BitString.listRow (b q.1.1) (padicValNat 2 (q.2.1 - 1)) q.1.2.2.2 ++
          shoupChunk (b q.1.1) (s q.1.1) (q.2.1 - 1) q.1.2.2.1)
    have hhk_poly : ComputableInPolyTime hhk (encPair encPar encAcc) encBits := by
      dsimp only [hhk, shoupChunk]
      exact ComputableInPolyTime.ite_decide (by fun_prop) (by fun_prop) (by fun_prop)
    have hhk_len : ∀ q, (hhk q).length = b q.1.1 := by
      intro q
      dsimp only [hhk]
      split_ifs
      · simp
      · exact hstep_len q.1.1 _ (by simp only [shoupChunk, List.length_append,
          BitString.length_listRow])
    have hadv : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          shoupAdvance (b q.1.1) (s q.1.1) (step q.1.1) q.2.2.2.2 q.1.2.2.1
            (q.2.1 - 1) (q.2.2.1 - 1) (hhk q))
        (encPair encPar encAcc) encBits :=
      computableInPolyTime_shoupAdvance hb' hs' hstep' hstep'_len hmasks hx'
        hk_idx (by fun_prop) hhk_poly hhk_len
    let hnewMask (q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool)) :=
      BitString.listXor (b q.1.1)
        [shoupAdvance (b q.1.1) (s q.1.1) (step q.1.1) q.2.2.2.2 q.1.2.2.1
          (q.2.1 - 1) (q.2.2.1 - 1) (hhk q), q.2.2.2.1]
    have hnewMask_poly : ComputableInPolyTime hnewMask (encPair encPar encAcc) encBits := by
      dsimp only [hnewMask]
      exact ComputableInPolyTime.bitsXorWithInput hb'
        (ComputableInPolyTime.cons' hadv
          (ComputableInPolyTime.cons' hactS (.const [])))
    have hrep_poly : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          BitString.replaceRow (b q.1.1) (shoupMaskCount (t q.1.1))
            (padicValNat 2 q.2.2.1) (hnewMask q) q.2.2.2.2)
        (encPair encPar encAcc) encBits :=
      computableInPolyTime_replaceRow hb' (computableInPolyTime_shoupMaskCount ht')
        (by fun_prop) hnewMask_poly hmasks
    have hbranch := (hk_idx.prod (hk_idx.prod ((by fun_prop : ComputableInPolyTime
      (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
        BitString.listRow (b q.1.1) (padicValNat 2 (q.2.1 - 1)) q.1.2.2.2)
      (encPair encPar encAcc) encBits).prod hrep_poly)))
    have hcond : ComputableInPolyTime
        (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
          decide (q.2.1 - 1 = 0) || shoupIsLastOcc q.1.2.1 (q.2.1 - 1))
        (encPair encPar encAcc) encBool := by fun_prop
    have helse := hk_idx.prod (hown.prod (hactS.prod hmasks))
    have h_ite := ComputableInPolyTime.ite' hcond hbranch helse
    have hfun : (fun q : (γ × ℕ × List Bool × List Bool) × (ℕ × ℕ × List Bool × List Bool) =>
        iterF q.1 q.2) = fun q =>
        if (decide (q.2.1 - 1 = 0) || shoupIsLastOcc q.1.2.1 (q.2.1 - 1)) = true then
          (q.2.1 - 1, q.2.1 - 1,
            BitString.listRow (b q.1.1) (padicValNat 2 (q.2.1 - 1)) q.1.2.2.2,
            BitString.replaceRow (b q.1.1) (shoupMaskCount (t q.1.1))
              (padicValNat 2 q.2.2.1) (hnewMask q) q.2.2.2.2)
        else (q.2.1 - 1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) := by
      funext q
      rfl
    exact hfun ▸ h_ite
  obtain ⟨heff, _⟩ := ComputableInPolyTime.iterateWith_spec hpar hi
    (hi.prod (hi.prod ((by fun_prop : ComputableInPolyTime
      (fun a => BitString.listRow (b a) (padicValNat 2 (iStar a)) (T0 a)) encIn encBits).prod hT0)))
    hiter_step
    (fun a _ acc => acc.1 ≤ iStar a ∧ acc.2.1 ≤ iStar a ∧
      acc.2.2.1.length = b a ∧ acc.2.2.2.length = shoupMasksLen (b a) (t a))
    (fun a => ⟨le_rfl, le_rfl, BitString.length_listRow _ _ _, BitString.length_listRow _ _ _⟩)
    (fun a _ acc _ ⟨h1, h2, h3, h4⟩ => by
      dsimp only [iterF, shoupPackStep, par]
      by_cases htrig : (decide (acc.1 - 1 = 0) || shoupIsLastOcc (iStar a) (acc.1 - 1)) = true
      · simp only [htrig, ↓reduceIte]
        refine ⟨by omega, by omega, BitString.length_listRow _ _ _, ?_⟩
        dsimp only [shoupMasksLen]
        exact length_replaceRow (BitString.length_listXor _ _)
      · simp only [htrig, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by omega, h2, h3, h4⟩)
    (size := fun a => 8 * (iStar a + b a + shoupMasksLen (b a) (t a)) + 20)
    (ComputableInPolyTime.polyBounded (show ComputableInPolyTime
      (fun a => 8 * (iStar a + b a + shoupMasksLen (b a) (t a)) + 20) encIn encUnary from
      by fun_prop))
    (fun a _ acc _ ⟨h1, h2, h3, h4⟩ => by
      simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate, h3, h4]
      omega)
  have hres (a : γ) :
      ((iterF (par a))^[iStar a]
        (iStar a, iStar a, BitString.listRow (b a) (padicValNat 2 (iStar a)) (T0 a), T0 a)).2.2.2 =
        shoupPackMasks (b a) (s a) (t a) (iStar a) (step a) (x a) (T a) := rfl
  exact funext hres ▸
    ((ComputableInPolyTime.snd encBits encBits).comp
      ((ComputableInPolyTime.snd encUnary (encPair encBits encBits)).comp
        ((ComputableInPolyTime.snd encUnary
          (encPair encUnary (encPair encBits encBits))).comp heff)))

/-! ### Standalone Shoup composition (`[Shoup2000]`, `[HHRVW2020]` Lemma 5.7) -/

open scoped NNReal ENNReal

/-- Total key bit-length `baseKeyLen n + (Nat.log 2 (t n) + 1) * outLen n` for `t n`-step Shoup
XOR-masking composition (`[Shoup2000]`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
@[expose]
def shoupComposeKeyLen (baseKeyLen outLen t : ℕ → ℕ) (n : ℕ) : ℕ :=
  baseKeyLen n + shoupMasksLen (outLen n) (t n)

/-- **`O(|y| log t)` key-length bound**: whenever `outLen n ≤ baseKeyLen n`, the composed key has
length at most `(Nat.log 2 (t n) + 2) * baseKeyLen n`. -/
theorem shoupComposeKeyLen_le {baseKeyLen outLen t : ℕ → ℕ} {n : ℕ}
    (hout_le : outLen n ≤ baseKeyLen n) :
    shoupComposeKeyLen baseKeyLen outLen t n ≤ (Nat.log 2 (t n) + 2) * baseKeyLen n := by
  dsimp only [shoupComposeKeyLen, shoupMasksLen, shoupMaskCount]
  have hmul := Nat.mul_le_mul_left (Nat.log 2 (t n) + 1) hout_le
  linarith

@[fun_prop]
theorem computableInPolyTime_shoupComposeKeyLen
    {γ : Type} {encIn : γ ↪ List Bool}
    {baseKeyLen outLen t : ℕ → ℕ} {f : γ → ℕ}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hf : ComputableInPolyTime f encIn encUnary) :
    ComputableInPolyTime (fun a => shoupComposeKeyLen baseKeyLen outLen t (f a))
      encIn encUnary := by
  unfold shoupComposeKeyLen
  have hb := hbase.comp hf
  have ho := hout.comp hf
  have htn := ht.comp hf
  fun_prop

/-- Composed evaluator applying `t n` steps of `shoupCascade` to base evaluator `h n key` where
`key := BitString.listRow (baseKeyLen n) 0 K` and `masks := K.drop (baseKeyLen n)`. -/
@[expose]
def shoupComposeEval (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (K x : List Bool) : List Bool :=
  shoupCascade (outLen n) (s n) (t n) (h n (BitString.listRow (baseKeyLen n) 0 K))
    (K.drop (baseKeyLen n)) x

@[simp]
theorem length_shoupComposeEval {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool} {n : ℕ} {K x : List Bool}
    (h_len : ∀ k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    (shoupComposeEval baseKeyLen outLen s t h n K x).length = outLen n :=
  length_shoupState (outLen n) (s n) (h n (BitString.listRow (baseKeyLen n) 0 K))
    (fun w => h_len _ w (BitString.length_listRow (baseKeyLen n) 0 K))
    (K.drop (baseKeyLen n)) x (t n)

@[fun_prop]
theorem computableInPolyTime_shoupComposeEval
    {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        shoupComposeEval baseKeyLen outLen s t h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits := by
  let hp := ComputableInPolyTime.id' (encIn := encKeyedInput encBits)
  let hn := hp.fst'
  let hK := hp.snd'.fst'
  let hx := hp.snd'.snd'
  let hkey : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      BitString.listRow (baseKeyLen p.1) 0 p.2.1) (encKeyedInput encBits) encBits := by
    have := hbase.comp hn
    fun_prop
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List Bool × List Bool) × List Bool =>
        h q.1.1 (BitString.listRow (baseKeyLen q.1.1) 0 q.1.2.1) q.2)
      (encPair (encKeyedInput encBits) encBits) encBits := by
    let qid := ComputableInPolyTime.id' (encIn := encPair (encKeyedInput encBits) encBits)
    exact hh.comp (qid.fst'.fst'.prod ((hkey.comp qid.fst').prod qid.snd'))
  have hstep_len : ∀ q : ℕ × List Bool × List Bool, ∀ w,
      w.length = outLen q.1 + s q.1 →
      (h q.1 (BitString.listRow (baseKeyLen q.1) 0 q.2.1) w).length = outLen q.1 :=
    fun q w hw => h_len q.1 _ w (BitString.length_listRow _ _ _) hw
  exact computableInPolyTime_shoupCascade (hout.comp hn) (hs.comp hn) (ht.comp hn) hstep
    hstep_len (ComputableInPolyTime.bitsDropWithInput hK (hbase.comp hn)) hx

private structure ShoupSavedState where
  iStar : ℕ
  x₀ : List Bool
  advState : List Bool
  T : List Bool

private enc_structure encShoupState : ShoupSavedState where
  iStar : encUnary,
  x₀ : encBits,
  advState : encBits,
  T : encBits

private def shoupStateDecoder : Decoder encShoupState :=
  (Decoder.unary.pair (Decoder.bits.pair (Decoder.bits.pair Decoder.bits))).map
    (fun (iStar, x₀, advState, T) => ⟨iStar, x₀, advState, T⟩)
    (fun s => (s.iStar, s.x₀, s.advState, s.T))
    (fun ⟨_, _, _, _⟩ => rfl)
    (fun _ => rfl)

/-- Reduction adversary turning a target collision finder on `shoupComposeEval` into a target
collision finder on the underlying shrinking compression function `h`, guessing the colliding step
`1 ≤ iStar ≤ t n` and reconstructing the `log n`-mask vector via `shoupPackMasks` (`[Shoup2000]`;
`[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
noncomputable def shoupComposeAdversary
    (baseKeyLen outLen s t : ℕ → ℕ)
    (h : ℕ → List Bool → List Bool → List Bool)
    (adversary : TargetCollisionFinder) : TargetCollisionFinder where
  choose n := do
    let rawSlot ← sampleDyadicIndex (t n)
    let choice ← adversary.choose n
    let T ← BitString.sampleList (shoupMasksLen (outLen n) (t n))
    let iStar := min (rawSlot + 1) (t n)
    let w₀ := BitString.listRow (outLen n) (padicValNat 2 iStar) T ++
      shoupChunk (outLen n) (s n) iStar choice.1
    return (w₀, encShoupState ⟨iStar, choice.1, choice.2, T⟩)
  find n savedState k := do
    let st := shoupStateDecoder.decode savedState
    let key := BitString.listRow (baseKeyLen n) 0 k
    let step := h n key
    let masks := shoupPackMasks (outLen n) (s n) (t n) st.iStar step st.x₀ st.T
    let x₁ ← adversary.find n st.advState (key ++ masks)
    let prev := shoupState (outLen n) (s n) step masks x₁ (st.iStar - 1)
    return shoupStepInput (outLen n) (s n) masks x₁ st.iStar prev

/-- `shoupComposeAdversary` is uniformly strict PPT whenever `adversary` is strict PPT and all
parameters and `h` are polynomial time. -/
theorem isPPT_shoupComposeAdversary
    {baseKeyLen outLen s t : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    {adversary : TargetCollisionFinder}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n)
    (ha : adversary.IsPPT) :
    (shoupComposeAdversary baseKeyLen outLen s t h adversary).IsPPT := by
  refine ⟨?_, ?_⟩
  · have hn_q := ComputableInPolyTime.fst encUnary encUnary
    have hraw := ComputableInPolyTime.snd encUnary encUnary
    have hmin_poly : ComputableInPolyTime
        (fun q : ℕ × ℕ => min (q.2 + 1) (t q.1))
        (encPair encUnary encUnary) encUnary := by
      have htq := ht.comp hn_q
      have hr1 : ComputableInPolyTime (fun q : ℕ × ℕ => q.2 + 1)
          (encPair encUnary encUnary) encUnary :=
        ComputableInPolyTime.unary_add.comp (hraw.prod (.const 1))
      fun_prop
    have hmLen : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (List Bool × List Bool) =>
          shoupMasksLen (outLen q.1.1) (t q.1.1))
        (encPair (encPair encUnary encUnary) (encPair encBits encBits)) encUnary := by
      have hn2 := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst
        (encPair encUnary encUnary) (encPair encBits encBits))
      have ho2 := hout.comp hn2
      have ht2 := ht.comp hn2
      fun_prop
    let encFin := encPair
      (encPair (encPair encUnary encUnary) (encPair encBits encBits)) encBits
    have hfin : ComputableInPolyTime
        (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
          let iStar := min (q.1.1.2 + 1) (t q.1.1.1)
          (BitString.listRow (outLen q.1.1.1) (padicValNat 2 iStar) q.2 ++
            shoupChunk (outLen q.1.1.1) (s q.1.1.1) iStar q.1.2.1,
           encShoupState ⟨iStar, q.1.2.1, q.1.2.2, q.2⟩))
        encFin (encPair encBits encBits) := by
      have hp0 := ComputableInPolyTime.fst
        (encPair (encPair encUnary encUnary) (encPair encBits encBits)) encBits
      have hq1 := (ComputableInPolyTime.fst (encPair encUnary encUnary)
        (encPair encBits encBits)).comp hp0
      have hqch := (ComputableInPolyTime.snd (encPair encUnary encUnary)
        (encPair encBits encBits)).comp hp0
      have hn3 := (ComputableInPolyTime.fst encUnary encUnary).comp hq1
      have hiS := hmin_poly.comp hq1
      have hx0 := (ComputableInPolyTime.fst encBits encBits).comp hqch
      have hst := (ComputableInPolyTime.snd encBits encBits).comp hqch
      have hT := ComputableInPolyTime.snd
        (encPair (encPair encUnary encUnary) (encPair encBits encBits)) encBits
      have ho3 := hout.comp hn3
      have hs3 := hs.comp hn3
      have hw0 : ComputableInPolyTime
          (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
            BitString.listRow (outLen q.1.1.1) (padicValNat 2 (min (q.1.1.2 + 1) (t q.1.1.1)))
              q.2 ++
            shoupChunk (outLen q.1.1.1) (s q.1.1.1) (min (q.1.1.2 + 1) (t q.1.1.1)) q.1.2.1)
          encFin encBits := by
        dsimp only [shoupChunk]
        fun_prop
      have hsE : ComputableInPolyTime
          (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
            encShoupState ⟨min (q.1.1.2 + 1) (t q.1.1.1), q.1.2.1, q.1.2.2, q.2⟩)
          encFin encBits :=
        (by fun_prop : ComputableInPolyTime
          (fun q : ((ℕ × ℕ) × (List Bool × List Bool)) × List Bool =>
            ShoupSavedState.mk (min (q.1.1.2 + 1) (t q.1.1.1)) q.1.2.1 q.1.2.2 q.2)
          encFin encShoupState).of_enc_eq fun _ => rfl
      exact hw0.prod hsE
    exact (isPPTOn_sampleDyadicIndex ht).bind_with
      ((ha.choose.preprocess hn_q).bind_with
        (hmLen.sampleList.bind_with hfin.isPPTOn))
  · let encP := encKeyedInput encBits
    have hp := ComputableInPolyTime.id' (encIn := encP)
    have hn := hp.fst'
    have hsaved := hp.snd'.fst'
    have hk := hp.snd'.snd'
    have hst : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => shoupStateDecoder.decode p.2.1)
        encP encShoupState := shoupStateDecoder.computableInPolyTime.comp hsaved
    have hiStar : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (shoupStateDecoder.decode p.2.1).iStar)
        encP encUnary := by fun_prop
    have hx₀ : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (shoupStateDecoder.decode p.2.1).x₀)
        encP encBits := by fun_prop
    have hadv : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (shoupStateDecoder.decode p.2.1).advState)
        encP encBits := by fun_prop
    have hT : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (shoupStateDecoder.decode p.2.1).T)
        encP encBits := by fun_prop
    have hkey : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => BitString.listRow (baseKeyLen p.1) 0 p.2.2)
        encP encBits :=
      ComputableInPolyTime.bitsRowWithInput (hbase.comp hn) (.const 0) hk
    have hstep : ComputableInPolyTime
        (fun q : (ℕ × List Bool × List Bool) × List Bool =>
          h q.1.1 (BitString.listRow (baseKeyLen q.1.1) 0 q.1.2.2) q.2)
        (encPair encP encBits) encBits := by
      let qid := ComputableInPolyTime.id' (encIn := encPair encP encBits)
      exact hh.comp ((hn.comp qid.fst').prod ((hkey.comp qid.fst').prod qid.snd'))
    have hstep_len : ∀ q : ℕ × List Bool × List Bool, ∀ w,
        w.length = outLen q.1 + s q.1 →
        (h q.1 (BitString.listRow (baseKeyLen q.1) 0 q.2.2) w).length = outLen q.1 :=
      fun q w hw => h_len q.1 _ w (BitString.length_listRow _ _ _) hw
    have hmasks : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          let st := shoupStateDecoder.decode p.2.1
          let step := h p.1 (BitString.listRow (baseKeyLen p.1) 0 p.2.2)
          shoupPackMasks (outLen p.1) (s p.1) (t p.1) st.iStar step st.x₀ st.T)
        encP encBits :=
      computableInPolyTime_shoupPackMasks (hout.comp hn) (hs.comp hn) (ht.comp hn)
        hiStar hstep hstep_len hx₀ hT
    have harg : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          let st := shoupStateDecoder.decode p.2.1
          let key := BitString.listRow (baseKeyLen p.1) 0 p.2.2
          let masks := shoupPackMasks (outLen p.1) (s p.1) (t p.1) st.iStar (h p.1 key) st.x₀ st.T
          (p.1, st.advState, key ++ masks))
        encP (encKeyedInput encBits) :=
      hn.prod (hadv.prod (ComputableInPolyTime.bitsAppend hkey hmasks))
    let encQ := encPair encP encBits
    have hq := ComputableInPolyTime.id' (encIn := encQ)
    have hqp := hq.fst'
    have hqx₁ := hq.snd'
    have hqn := hn.comp hqp
    have hqstep : ComputableInPolyTime
        (fun r : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
          h r.1.1.1 (BitString.listRow (baseKeyLen r.1.1.1) 0 r.1.1.2.2) r.2)
        (encPair encQ encBits) encBits := by
      let rid := ComputableInPolyTime.id' (encIn := encPair encQ encBits)
      exact hh.comp ((hqn.comp rid.fst').prod ((hkey.comp (hqp.comp rid.fst')).prod rid.snd'))
    have hqstep_len : ∀ r : (ℕ × List Bool × List Bool) × List Bool, ∀ w,
        w.length = outLen r.1.1 + s r.1.1 →
        (h r.1.1 (BitString.listRow (baseKeyLen r.1.1) 0 r.1.2.2) w).length = outLen r.1.1 :=
      fun r w hw => h_len r.1.1 _ w (BitString.length_listRow _ _ _) hw
    have hqst_prev : ComputableInPolyTime
        (fun r : (ℕ × List Bool × List Bool) × List Bool =>
          let st := shoupStateDecoder.decode r.1.2.1
          let key := BitString.listRow (baseKeyLen r.1.1) 0 r.1.2.2
          let step := h r.1.1 key
          let masks := shoupPackMasks (outLen r.1.1) (s r.1.1) (t r.1.1) st.iStar step st.x₀ st.T
          shoupState (outLen r.1.1) (s r.1.1) step masks r.2 (st.iStar - 1))
        encQ encBits :=
      computableInPolyTime_shoupState (hout.comp hqn) (hs.comp hqn)
        ((hiStar.comp hqp).unary_sub' (.const 1)) hqstep hqstep_len (hmasks.comp hqp) hqx₁
    have hret : ComputableInPolyTime
        (fun r : (ℕ × List Bool × List Bool) × List Bool =>
          let st := shoupStateDecoder.decode r.1.2.1
          let key := BitString.listRow (baseKeyLen r.1.1) 0 r.1.2.2
          let step := h r.1.1 key
          let masks := shoupPackMasks (outLen r.1.1) (s r.1.1) (t r.1.1) st.iStar step st.x₀ st.T
          let prev := shoupState (outLen r.1.1) (s r.1.1) step masks r.2 (st.iStar - 1)
          shoupStepInput (outLen r.1.1) (s r.1.1) masks r.2 st.iStar prev)
        encQ encBits := by
      have hoq := hout.comp hqn
      have hsq := hs.comp hqn
      have hmq := hmasks.comp hqp
      have hiq := hiStar.comp hqp
      dsimp only [shoupStepInput, shoupChunk]
      fun_prop
    exact (ha.find.preprocess harg).bind_with hret.isPPTOn

private noncomputable def shoupTargetDist (baseKeyLen outLen t : ℕ → ℕ)
    (adversary : TargetCollisionFinder) (n : ℕ) :
    PMF ((List Bool × List Bool) × List Bool × List Bool) := do
  let choice ← ProbComp.eval (adversary.choose n)
  let K ← BitString.uniformList (shoupComposeKeyLen baseKeyLen outLen t n)
  (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ => (choice, K, x₁)

/-- **Concrete `[Shoup2000]` / `[HHRVW2020]` Lemma 5.7 reduction**: the target-collision
advantage of `adversary` against `shoupComposeEval` on `L n`-bit inputs (`outLen n ≤ L n ≤
outLen n + t n * s n`) is at most `dyadicSize (t n)` times the target-collision advantage of
`shoupComposeAdversary` against `h` on `(outLen n + s n)`-bit inputs. -/
theorem succProbability_targetCollisionGame_shoupCompose_le
    {baseKeyLen outLen s t L : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (adversary : TargetCollisionFinder) (n : ℕ)
    (hs_pos : 1 ≤ s n)
    (hb_le : outLen n ≤ L n) (hL_le : L n ≤ outLen n + t n * s n)
    (h_len : ∀ k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (shoupComposeKeyLen baseKeyLen outLen t)
          (shoupComposeEval baseKeyLen outLen s t h)
          (fun m x => x.length == L m) adversary n)) ≤
      (dyadicSize (t n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (targetCollisionGame baseKeyLen h
              (fun m w => w.length == outLen m + s m)
              (shoupComposeAdversary baseKeyLen outLen s t h adversary) n)) := by
  let K₀ := baseKeyLen n
  let B := outLen n
  let S := s n
  let Tlen := t n
  let D := dyadicSize Tlen
  let validBase (m : ℕ) (w : List Bool) : Bool := w.length == outLen m + s m
  let validLong (m : ℕ) (x : List Bool) : Bool := x.length == L m
  let μ := shoupTargetDist baseKeyLen outLen t adversary n
  let winComp (tup : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    isCollision (shoupComposeEval baseKeyLen outLen s t h n) validLong n
      tup.2.1 tup.1.1 tup.2.2
  have hcomp_eq :
      ProbComp.eval
        (targetCollisionGame (shoupComposeKeyLen baseKeyLen outLen t)
          (shoupComposeEval baseKeyLen outLen s t h) validLong adversary n) =
        μ.map winComp := by
    simp only [targetCollisionGame, μ, shoupTargetDist, winComp, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.monad_bind_eq_bind, PMF.map,
      PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  let slotTrial (rawSlot : ℕ) : Game := do
    let iStar := min (rawSlot + 1) Tlen
    let choice ← ProbComp.eval (adversary.choose n)
    let T ← BitString.uniformList (shoupMasksLen B Tlen)
    let k ← BitString.uniformList K₀
    let step := h n (BitString.listRow K₀ 0 k)
    let masks := shoupPackMasks B S Tlen iStar step choice.1 T
    let x₁ ← ProbComp.eval (adversary.find n choice.2 (BitString.listRow K₀ 0 k ++ masks))
    let w₀ := BitString.listRow B (padicValNat 2 iStar) T ++ shoupChunk B S iStar choice.1
    let w₁ := shoupStepInput B S masks x₁ iStar (shoupState B S step masks x₁ (iStar - 1))
    PMF.pure (isCollision (h n) validBase n k w₀ w₁)
  have hred_eq :
      ProbComp.eval
        (targetCollisionGame baseKeyLen h validBase
          (shoupComposeAdversary baseKeyLen outLen s t h adversary) n) =
        (PMF.uniformOfFintype (Fin D)).bind fun a => slotTrial a.val := by
    dsimp only [targetCollisionGame, shoupComposeAdversary, slotTrial, K₀, B, S, Tlen, D]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleDyadicIndex,
      BitString.eval_sampleList, shoupStateDecoder.decode_enc, PMF.monad_bind_eq_bind,
      PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
  let Wi (rawSlot : ℕ) (tup : (List Bool × List Bool) × List Bool × List Bool) : Bool :=
    if rawSlot < Tlen then
      let iStar := rawSlot + 1
      let k := BitString.listRow K₀ 0 tup.2.1
      let masks := tup.2.1.drop K₀
      isCollision (h n) validBase n k
        (shoupStepInput B S masks tup.1.1 iStar
          (shoupState B S (h n k) masks tup.1.1 (iStar - 1)))
        (shoupStepInput B S masks tup.2.2 iStar
          (shoupState B S (h n k) masks tup.2.2 (iStar - 1)))
    else false
  have hslot_eq (rawSlot : ℕ) (hraw : rawSlot < Tlen) :
      slotTrial rawSlot = μ.map (Wi rawSlot) := by
    let iStar := rawSlot + 1
    have hi_pos : 1 ≤ iStar := Nat.succ_pos rawSlot
    have hi_le : iStar ≤ Tlen := hraw
    have hmin : min (rawSlot + 1) Tlen = iStar := Nat.min_eq_left hi_le
    dsimp only [slotTrial]
    simp only [hmin, PMF.monad_bind_eq_bind]
    have hrhs :
        PMF.map (Wi rawSlot) μ =
          (ProbComp.eval (adversary.choose n)).bind fun choice =>
            (BitString.uniformList (shoupComposeKeyLen baseKeyLen outLen t n)).bind fun K =>
              (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ =>
                Wi rawSlot (choice, K, x₁) := by
      simp only [μ, shoupTargetDist, PMF.map, PMF.monad_bind_eq_bind, PMF.bind_bind,
        PMF.pure_bind, Function.comp_def]
    rw [PMF.bind_congr_on_support _ _ _ fun choice _ =>
      PMF.bind_comm (BitString.uniformList (shoupMasksLen B Tlen)) (BitString.uniformList K₀) _,
      hrhs]
    refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
    have hinner :
        (BitString.uniformList K₀).bind (fun k =>
          (BitString.uniformList (shoupMasksLen B Tlen)).bind fun T =>
            let step := h n (BitString.listRow K₀ 0 k)
            let masks := shoupPackMasks B S Tlen iStar step choice.1 T
            (ProbComp.eval (adversary.find n choice.2 (BitString.listRow K₀ 0 k ++ masks))).bind
              fun x₁ =>
              let w₀ := BitString.listRow B (padicValNat 2 iStar) T ++
                shoupChunk B S iStar choice.1
              let w₁ := shoupStepInput B S masks x₁ iStar (shoupState B S step masks x₁ (iStar - 1))
              PMF.pure (isCollision (h n) validBase n k w₀ w₁)) =
        (BitString.uniformList (shoupComposeKeyLen baseKeyLen outLen t n)).bind fun K =>
          (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ =>
            Wi rawSlot (choice, K, x₁) := by
      have h_k : ∀ k ∈ (BitString.uniformList K₀).support,
          ((BitString.uniformList (shoupMasksLen B Tlen)).bind fun T =>
            let step := h n (BitString.listRow K₀ 0 k)
            let masks := shoupPackMasks B S Tlen iStar step choice.1 T
            (ProbComp.eval (adversary.find n choice.2 (BitString.listRow K₀ 0 k ++ masks))).bind
              fun x₁ =>
              let w₀ := BitString.listRow B (padicValNat 2 iStar) T ++
                shoupChunk B S iStar choice.1
              let w₁ := shoupStepInput B S masks x₁ iStar (shoupState B S step masks x₁ (iStar - 1))
              PMF.pure (isCollision (h n) validBase n k w₀ w₁)) =
          (BitString.uniformList (shoupMasksLen B Tlen)).bind fun masks =>
            (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).map fun x₁ =>
              isCollision (h n) validBase n k
                (shoupStepInput B S masks choice.1 iStar
                  (shoupState B S (h n k) masks choice.1 (iStar - 1)))
                (shoupStepInput B S masks x₁ iStar
                  (shoupState B S (h n k) masks x₁ (iStar - 1))) := by
        intro k hk_supp
        have hk_len : k.length = K₀ := BitString.length_of_mem_support_uniformList hk_supp
        have hrow_k : BitString.listRow K₀ 0 k = k := by
          rw [BitString.listRow_zero, BitString.ofFn_ofList hk_len]
        have hstep_len_k : ∀ w, w.length = B + S → (h n k w).length = B :=
          fun w hw => h_len k w hk_len hw
        have hstep_eq :
            (BitString.uniformList (shoupMasksLen B Tlen)).bind (fun T =>
              (ProbComp.eval (adversary.find n choice.2
                (k ++ shoupPackMasks B S Tlen iStar (h n k) choice.1 T))).bind fun x₁ =>
                PMF.pure (isCollision (h n) validBase n k
                  (shoupStepInput B S (shoupPackMasks B S Tlen iStar (h n k) choice.1 T)
                    choice.1 iStar
                    (shoupState B S (h n k) (shoupPackMasks B S Tlen iStar (h n k) choice.1 T)
                      choice.1 (iStar - 1)))
                  (shoupStepInput B S (shoupPackMasks B S Tlen iStar (h n k) choice.1 T) x₁ iStar
                    (shoupState B S (h n k) (shoupPackMasks B S Tlen iStar (h n k) choice.1 T) x₁
                      (iStar - 1))))) =
            ((BitString.uniformList (shoupMasksLen B Tlen)).map
              (shoupPackMasks B S Tlen iStar (h n k) choice.1)).bind fun masks =>
              (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).map fun x₁ =>
                isCollision (h n) validBase n k
                  (shoupStepInput B S masks choice.1 iStar
                    (shoupState B S (h n k) masks choice.1 (iStar - 1)))
                  (shoupStepInput B S masks x₁ iStar
                    (shoupState B S (h n k) masks x₁ (iStar - 1))) := by
          rw [PMF.bind_map]
          rfl
        refine (PMF.bind_congr_on_support _ _ _ fun T _ => ?_).trans
          (hstep_eq.trans ?_)
        · simp only [hrow_k]
          rw [shoupStepInput_shoupPackMasks (h n k) hstep_len_k hi_pos hi_le choice.1 T]
        · rw [uniformList_map_shoupPackMasks B S Tlen iStar (h n k) hstep_len_k hi_pos hi_le
            choice.1]
      refine (PMF.bind_congr_on_support _ _ _ h_k).trans ?_
      symm
      rw [show shoupComposeKeyLen baseKeyLen outLen t n = K₀ + shoupMasksLen B Tlen from rfl]
      have hK_split :
          ((BitString.uniformList (K₀ + shoupMasksLen B Tlen)).bind fun K =>
            (ProbComp.eval (adversary.find n choice.2 K)).map fun x₁ =>
              Wi rawSlot (choice, K, x₁)) =
            (BitString.uniformList (K₀ + shoupMasksLen B Tlen)).bind fun K =>
              (ProbComp.eval (adversary.find n choice.2 (K.take K₀ ++ K.drop K₀))).map
                fun x₁ => Wi rawSlot (choice, K.take K₀ ++ K.drop K₀, x₁) := by
        refine PMF.bind_congr_on_support _ _ _ fun K _ => ?_
        rw [List.take_append_drop]
      rw [hK_split, BitString.uniformList_bind_split K₀ (shoupMasksLen B Tlen)
        (fun k masks =>
          (ProbComp.eval (adversary.find n choice.2 (k ++ masks))).map fun x₁ =>
            Wi rawSlot (choice, k ++ masks, x₁))]
      refine PMF.bind_congr_on_support _ _ _ fun k hk_supp =>
        PMF.bind_congr_on_support _ _ _ fun masks _ => ?_
      have hk_len : k.length = K₀ := BitString.length_of_mem_support_uniformList hk_supp
      have hrow_km : BitString.listRow K₀ 0 (k ++ masks) = (k ++ masks).take K₀ := by
        rw [BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
          List.take_append_of_le_length (by simp [hk_len])]
      simp only [Wi, hraw, ↓reduceIte, List.drop_left' hk_len, hrow_km, List.take_left' hk_len]
      rfl
    exact hinner
  have hcover : ∀ tup ∈ μ.support, winComp tup = true → ∃ s : Fin D, Wi s.val tup = true := by
    intro tup htup hW
    simp only [μ, shoupTargetDist, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at htup
    obtain ⟨choice, _, K, hK, ⟨x₁, _, rfl⟩⟩ := htup
    obtain ⟨hx₀_v, hx₁_v, hne, hcol⟩ := isCollision_eq_true_iff.mp hW
    have hx₀_len : choice.1.length = L n := by simpa only [validLong, beq_iff_eq] using hx₀_v
    have hx₁_len : x₁.length = L n := by simpa only [validLong, beq_iff_eq] using hx₁_v
    dsimp only [shoupComposeEval] at hcol
    obtain ⟨i, hi_pos, hi_le, hw_ne, hw_col⟩ :=
      exists_shoupCascade_step_collision hs_pos hb_le hL_le
        (h n (BitString.listRow K₀ 0 K))
        (fun w => h_len _ w (BitString.length_listRow K₀ 0 K))
        (K.drop K₀) choice.1 x₁ hx₀_len hx₁_len hne hcol
    let rawSlot := i - 1
    have hraw_lt : rawSlot < Tlen := by dsimp only [rawSlot]; omega
    have hi_eq : rawSlot + 1 = i := by dsimp only [rawSlot]; omega
    refine ⟨⟨rawSlot, hraw_lt.trans (lt_dyadicSize Tlen)⟩, ?_⟩
    simp only [Wi, hraw_lt, ↓reduceIte, hi_eq, isCollision_eq_true_iff, validBase, beq_iff_eq,
      length_shoupStepInput, B, S, true_and]
    exact ⟨hw_ne, hw_col⟩
  obtain ⟨val, hval⟩ : ∃ val : ℕ → ℝ≥0∞, ∀ r, (slotTrial r) true = val r :=
    ⟨_, fun _ => rfl⟩
  have hsum_s : (μ.map winComp) true ≤ ∑ r : Fin D, val r.val := by
    have hmono :
        (μ.map winComp) true ≤
          (μ.map (fun tup => (List.range D).any (fun r => Wi r tup))) true := by
      refine PMF.map_true_mono μ fun tup htup hW => ?_
      obtain ⟨⟨r, hr⟩, hs⟩ := hcover tup htup hW
      exact List.any_eq_true.mpr ⟨r, List.mem_range.mpr hr, hs⟩
    refine (hmono.trans (PMF.map_any_range_true_le_sum μ D Wi)).trans ?_
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_le_sum fun r hr => ?_
    simp only [Finset.mem_range.mp hr, ↓reduceDIte, ← hval]
    by_cases hraw : r < Tlen
    · rw [hslot_eq r hraw]
    · have hWi : Wi r = fun _ => false := funext fun tup => by simp only [Wi, hraw, ↓reduceIte]
      rw [hWi]
      simp
  have : Nonempty (Fin D) := ⟨⟨0, dyadicSize_pos Tlen⟩⟩
  have hcard : (Fintype.card (Fin D) : ℝ≥0) = (D : ℝ≥0) := by
    simp only [Fintype.card_fin]
  have hpos : (0 : ℝ≥0) < D := by exact_mod_cast dyadicSize_pos Tlen
  rw [hcomp_eq, hred_eq, Game.succProbability_uniform, hcard, mul_div_cancel₀ _ hpos.ne']
  have hsum_val_eq :
      (∑ r : Fin D, Game.succProbability (slotTrial r.val)) =
        (∑ r : Fin D, val r.val).toNNReal := by
    rw [ENNReal.toNNReal_sum fun r _ => by rw [← hval]; exact PMF.apply_ne_top _ _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Game.succProbability, hval]
  rw [hsum_val_eq]
  have hsum_ne_top : (∑ r : Fin D, val r.val) ≠ ⊤ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr fun r _ => by rw [← hval]; exact (PMF.apply_ne_top _ _).lt_top)
  exact ENNReal.toNNReal_mono hsum_ne_top hsum_s

/-- **Asymptotic `[Shoup2000]` / `[HHRVW2020]` Lemma 5.7**: if `h` is target collision
resistant on `(outLen n + s n)`-bit inputs with `1 ≤ s n` and `outLen n ≤ L n ≤
outLen n + t n * s n`, then `shoupComposeEval` is target collision resistant on `L n`-bit inputs
with compact key length `baseKeyLen n + (Nat.log 2 (t n) + 1) * outLen n`. -/
theorem targetCollisionResistantOn_shoupCompose
    {baseKeyLen outLen s t L : ℕ → ℕ}
    {h : ℕ → List Bool → List Bool → List Bool}
    (hbase : ComputableInPolyTime baseKeyLen encUnary encUnary)
    (hout : ComputableInPolyTime outLen encUnary encUnary)
    (hs : ComputableInPolyTime s encUnary encUnary)
    (ht : ComputableInPolyTime t encUnary encUnary)
    (hh : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => h p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits)
    (hs_pos : ∀ n, 1 ≤ s n)
    (hb_le : ∀ n, outLen n ≤ L n) (hL_le : ∀ n, L n ≤ outLen n + t n * s n)
    (h_len : ∀ n k w, k.length = baseKeyLen n → w.length = outLen n + s n →
      (h n k w).length = outLen n)
    (hTCR : TargetCollisionResistantOn baseKeyLen h (fun m w => w.length == outLen m + s m)) :
    TargetCollisionResistantOn (shoupComposeKeyLen baseKeyLen outLen t)
      (shoupComposeEval baseKeyLen outLen s t h) (fun m x => x.length == L m) := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  have hred_ppt : (shoupComposeAdversary baseKeyLen outLen s t h adversary).IsPPT :=
    isPPT_shoupComposeAdversary hbase hout hs ht hh h_len hadversary
  have hneg := hTCR.negligible (shoupComposeAdversary baseKeyLen outLen s t h adversary) hred_ppt
  have hloss : PolynomiallyBounded (fun n => dyadicSize (t n)) :=
    dyadicSize_polynomiallyBounded.comp ht.polynomiallyBounded
  refine negligible_of_le (hneg.polynomiallyBounded_mul hloss) fun n => ?_
  exact succProbability_targetCollisionGame_shoupCompose_le adversary n
    (hs_pos n) (hb_le n) (hL_le n) (h_len n)

end Cslib.Crypto
