/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.Explicit
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Complexity.Foundations.Data.Nat.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The threshold of the explicit affine disperser

The explicit disperser on `N` bits is nonconstant on affine subspaces of dimension greater than
`explicitThreshold N`. With `ℓ = ⌊log₂ N⌋`, `L = ⌊ℓ / 3⌋` and `n`, `r`, `s`, `t` as in
`Cslib.AffineDisperser.explicitThreshold`, every term is at most a constant times `N / (ℓ + 1)`,
except `2 r (r + 1)`, which is small because `n` is large:

* the unread bits number `N - r n < n ≤ N / (ℓ + 1) ^ 2`, and `n t, ⌊n r / t⌋ ≤ N / (ℓ + 1)`;
* the subfield term is `r s ≤ N / (L + 1) ≤ 3 N / (ℓ + 1)`;
* either the greedy choice of primes stops within a factor `4 L` of its budget
  `N / (ℓ + 1) ^ 2`, and then `r < 2 (ℓ + 1) ^ 3`, or it takes every prime in `(L, 4 L]`, whose
  product is at least `4 ^ L / (4 L + 1) ^ (4 ⌊√L⌋ + 5) ≥ √(8 (ℓ + 1) N)` for large `N` by
  Chebyshev's bounds.

Hence `(ℓ + 1) * explicitThreshold N ≤ 6 N` for all large `N`
(`Cslib.AffineDisperser.eventually_explicitThreshold_le`), and the threshold is `O(N / log N)`.

## Main results

* `Cslib.AffineDisperser.eventually_explicitThreshold_le`:
  `(⌊log₂ N⌋ + 1) * explicitThreshold N ≤ 6 N` for all large `N`.
* `Cslib.AffineDisperser.eventually_explicitThreshold_lt`: `explicitThreshold N < N` for all large
  `N`, so the disperser theorem is not vacuous.
* `Cslib.AffineDisperser.isBigO_explicitThreshold`: `explicitThreshold N = O(N / log N)`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [P. L. Chebyshev, *Mémoire sur les nombres premiers*][Chebyshev1852]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Filter Explicit

/-- The Chebyshev factor is small: `64 (3 L + 3) (4 L + 1) ^ (8 ⌊√L⌋ + 10) ≤ 2 ^ L` for all large
`L`. -/
private theorem eventually_chebyshevFactor_le :
    ∀ᶠ L : ℕ in atTop, 64 * (3 * L + 3) * (4 * L + 1) ^ (8 * Nat.sqrt L + 10) ≤ 2 ^ L := by
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (Nat.eventually_mul_add_one_pow_le_pow 500 2 one_lt_two)
  obtain ⟨S, hS⟩ := eventually_atTop.1 (Nat.eventually_mul_add_one_pow_le_pow 384 2 one_lt_two)
  filter_upwards [eventually_ge_atTop ((10 * Q + S + 10) ^ 2)] with L hL
  set s := Nat.sqrt L
  have hs : 10 * Q + S + 10 ≤ s := Nat.le_sqrt'.2 hL
  have hsL : s ^ 2 ≤ L := Nat.sqrt_le' L
  have hLs : L < (s + 1) ^ 2 := Nat.lt_succ_sqrt' L
  set q := s / 10
  have hq : 10 * q ≤ s := Nat.mul_div_le s 10
  have hq' : s < 10 * (q + 1) := by omega
  have hqQ : Q ≤ q := by omega
  -- `4 L + 1 ≤ 5 (s + 1) ^ 2 ≤ 500 (q + 1) ^ 2 ≤ 2 ^ q`
  have h1 : 4 * L + 1 ≤ 2 ^ q := by
    have := hQ q hqQ
    nlinarith
  -- `64 (3 L + 3) ≤ 384 (s + 1) ^ 2 ≤ 2 ^ s`
  have h2 : 64 * (3 * L + 3) ≤ 2 ^ s := by
    have := hS s (by omega)
    nlinarith
  have h3 : s + q * (8 * s + 10) ≤ L := by nlinarith
  calc 64 * (3 * L + 3) * (4 * L + 1) ^ (8 * s + 10) ≤ 2 ^ s * (2 ^ q) ^ (8 * s + 10) :=
        Nat.mul_le_mul h2 (Nat.pow_le_pow_left h1 _)
    _ = 2 ^ (s + q * (8 * s + 10)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ L := Nat.pow_le_pow_right two_pos h3

/-- Decomposing `explicitThreshold N` into the budget `N / (⌊log₂ N⌋ + 1) ^ 2`, the block-count
term, the subfield term, and the symmetric-power terms. -/
private theorem explicitThreshold_le_add (N : ℕ) (hT1 : 1 ≤ N / (Nat.log 2 N + 1) ^ 2) :
    explicitThreshold N ≤ N / (Nat.log 2 N + 1) ^ 2 +
      2 * (numBlocks N * (numBlocks N + 1)) + N / (primeBound N + 1) +
      2 * (N / (Nat.log 2 N + 1)) := by
  set ℓ := Nat.log 2 N
  set L := primeBound N
  set T := N / (ℓ + 1) ^ 2
  have hT : T = N / (ℓ + 1) / (ℓ + 1) := by
    change N / (ℓ + 1) ^ 2 = _
    rw [Nat.div_div_eq_div_mul, sq]
  set n := fieldDegree N
  set r := numBlocks N
  have hr : r = N / n := rfl
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fieldDegree_ne_zero N)
  have hn : n = (selectBelow T (primesIoc L (4 * L))).prod := fieldDegree_eq_prod N
  have hnT : n ≤ T := hn ▸ prod_selectBelow_le hT1 _
  have hrn : r * n ≤ N := numBlocks_mul_le N
  -- the terms of the threshold
  have hwaste : N - r * n < n := by
    have h1 := Nat.mod_add_div' N n
    have h2 := Nat.mod_lt N hn0
    rw [hr]
    omega
  have hmax : r * max (r + 1) (subfieldExp N) ≤ r * (r + 1) + r * subfieldExp N := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (max_le (by omega) (by omega))
  have hrs : r * subfieldExp N ≤ N / (L + 1) :=
    (Nat.mul_div_le_mul_div_assoc r n (L + 1)).trans (Nat.div_le_div_right hrn)
  have hnt : n * symDegree N ≤ N / (ℓ + 1) :=
    calc n * symDegree N ≤ T * (ℓ + 1) := Nat.mul_le_mul hnT le_rfl
      _ ≤ N / (ℓ + 1) := hT ▸ Nat.div_mul_le_self _ _
  have hnrt : n * r / symDegree N ≤ N / (ℓ + 1) :=
    Nat.div_le_div_right (by rw [mul_comm]; exact hrn)
  change N - r * n + (r * max (r + 1) (subfieldExp N) + r * (r + 1) + n * symDegree N +
    n * r / symDegree N) ≤ _
  omega

/-- When every prime in `(primeBound N, 4 * primeBound N]` divides `fieldDegree N` and the
Chebyshev factor is at most `2 ^ primeBound N`, the block-count term satisfies
`4 * ((⌊log₂ N⌋ + 1) * (numBlocks N * (numBlocks N + 1))) ≤ N`. -/
private theorem four_mul_numBlocks_le_of_prod_le {N : ℕ}
    (hcheb : 64 * (3 * primeBound N + 3) *
      (4 * primeBound N + 1) ^ (8 * Nat.sqrt (primeBound N) + 10) ≤ 2 ^ primeBound N)
    (hP : (primesIoc (primeBound N) (4 * primeBound N)).prod ≤ fieldDegree N) :
    4 * ((Nat.log 2 N + 1) * (numBlocks N * (numBlocks N + 1))) ≤ N := by
  set ℓ := Nat.log 2 N
  set L := primeBound N
  have hL : L = ℓ / 3 := rfl
  set r := numBlocks N
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · simp [hr0]
  set P := (primesIoc L (4 * L)).prod
  have hPpos : 0 < P := List.prod_pos fun p hp => (mem_primesIoc.1 hp).2.2.pos
  have h16 : 16 ^ L ≤ (4 * L + 1) ^ (8 * Nat.sqrt L + 10) * P ^ 2 :=
    calc 16 ^ L = (4 ^ L) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ ((4 * L + 1) ^ (4 * Nat.sqrt L + 5) * P) ^ 2 :=
        Nat.pow_le_pow_left (four_pow_le_mul_prod_primesIoc L) 2
      _ = (4 * L + 1) ^ (8 * Nat.sqrt L + 10) * P ^ 2 := by
        rw [mul_pow, ← pow_mul]
        ring_nf
  have hP2 : 64 * (3 * L + 3) * 8 ^ L ≤ P ^ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ (by positivity : 0 < (4 * L + 1) ^ (8 * Nat.sqrt L + 10))
    calc (4 * L + 1) ^ (8 * Nat.sqrt L + 10) * (64 * (3 * L + 3) * 8 ^ L)
        = 64 * (3 * L + 3) * (4 * L + 1) ^ (8 * Nat.sqrt L + 10) * 8 ^ L := by ring
      _ ≤ 2 ^ L * 8 ^ L := Nat.mul_le_mul_right _ hcheb
      _ = 16 ^ L := by rw [← mul_pow]; norm_num
      _ ≤ _ := h16
  have h8L : N < 8 * 8 ^ L :=
    calc N < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self one_lt_two N
      _ ≤ 2 ^ (3 * L + 3) := Nat.pow_le_pow_right two_pos (by omega)
      _ = 8 * 8 ^ L := by rw [pow_add, pow_mul]; norm_num; ring
  have hNP : 8 * (ℓ + 1) * N ≤ P ^ 2 := by
    have : ℓ + 1 ≤ 3 * L + 3 := by omega
    nlinarith
  have hrP : r * P ≤ N := (Nat.mul_le_mul_left r hP).trans (numBlocks_mul_le N)
  have h8 : 8 * (ℓ + 1) * r ^ 2 ≤ N := by
    refine Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < P ^ 2)
    calc 8 * (ℓ + 1) * r ^ 2 * P ^ 2 = 8 * (ℓ + 1) * (r * P) ^ 2 := by ring
      _ ≤ 8 * (ℓ + 1) * N ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrP 2)
      _ = 8 * (ℓ + 1) * N * N := by ring
      _ ≤ P ^ 2 * N := Nat.mul_le_mul_right _ hNP
      _ = N * P ^ 2 := by ring
  nlinarith

/-- For all large `N`, the block-count term satisfies
`4 * ((⌊log₂ N⌋ + 1) * (numBlocks N * (numBlocks N + 1))) ≤ N`. -/
private theorem eventually_four_mul_numBlocks_le :
    ∀ᶠ N in atTop, 4 * ((Nat.log 2 N + 1) * (numBlocks N * (numBlocks N + 1))) ≤ N := by
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 (Nat.eventually_mul_add_one_pow_le_pow 16 7 one_lt_two)
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.1 eventually_chebyshevFactor_le
  filter_upwards [Nat.eventually_le_log (ℓ₁ + 3 * L₂ + 3) one_lt_two] with N hN
  set ℓ := Nat.log 2 N
  have hpow := hℓ₁ ℓ (by omega)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp [ℓ] at hN
  have hNℓ : 2 ^ ℓ ≤ N := Nat.pow_log_le_self 2 hN0
  set L := primeBound N
  have hL : L = ℓ / 3 := rfl
  set T := N / (ℓ + 1) ^ 2
  set n := fieldDegree N
  set r := numBlocks N
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fieldDegree_ne_zero N)
  have hn : n = (selectBelow T (primesIoc L (4 * L))).prod := fieldDegree_eq_prod N
  -- the number of blocks is small
  have hps : ∀ p ∈ primesIoc L (4 * L), 0 < p ∧ p ≤ 4 * L := fun p hp => by
    obtain ⟨-, h2, h3⟩ := mem_primesIoc.1 hp
    exact ⟨h3.pos, h2⟩
  rcases prod_le_or_lt_mul_prod_selectBelow T hps with hP | hTn
  · -- every prime in `(L, 4 L]` is chosen
    rw [← hn] at hP
    exact four_mul_numBlocks_le_of_prod_le (hL₂ L (by omega)) hP
  · -- the greedy choice stops within a factor `4 L` of its budget
    rw [← hn] at hTn
    have h1 : N < (ℓ + 1) ^ 2 * (T + 1) := Nat.lt_mul_div_succ N (by positivity)
    have h2 : N < (ℓ + 1) ^ 2 * (4 * L) * n :=
      calc N < (ℓ + 1) ^ 2 * (T + 1) := h1
        _ ≤ (ℓ + 1) ^ 2 * (4 * L * n) := Nat.mul_le_mul_left _ hTn
        _ = (ℓ + 1) ^ 2 * (4 * L) * n := by ring
    have hrlt : r < (ℓ + 1) ^ 2 * (4 * L) := (Nat.div_lt_iff_lt_mul hn0).2 h2
    have h4L : 4 * L ≤ 2 * (ℓ + 1) := by omega
    have hr1 : r + 1 ≤ 2 * (ℓ + 1) ^ 3 := by
      have : (ℓ + 1) ^ 2 * (4 * L) ≤ (ℓ + 1) ^ 2 * (2 * (ℓ + 1)) := Nat.mul_le_mul_left _ h4L
      have : (ℓ + 1) ^ 2 * (2 * (ℓ + 1)) = 2 * (ℓ + 1) ^ 3 := by ring
      omega
    calc 4 * ((ℓ + 1) * (r * (r + 1)))
        ≤ 4 * ((ℓ + 1) * (2 * (ℓ + 1) ^ 3 * (2 * (ℓ + 1) ^ 3))) := by
          gcongr
          omega
      _ = 16 * (ℓ + 1) ^ 7 := by ring
      _ ≤ 2 ^ ℓ := hpow
      _ ≤ N := hNℓ

/-- **The threshold is `O(N / log N)`**, with the explicit constant `6`:
`(⌊log₂ N⌋ + 1) * explicitThreshold N ≤ 6 N` for all large `N`. -/
theorem eventually_explicitThreshold_le :
    ∀ᶠ N in atTop, (Nat.log 2 N + 1) * explicitThreshold N ≤ 6 * N := by
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 (Nat.eventually_mul_add_one_pow_le_pow 1 2 one_lt_two)
  filter_upwards [eventually_four_mul_numBlocks_le,
    Nat.eventually_le_log (ℓ₁ + 1) one_lt_two] with N hkey hN
  set ℓ := Nat.log 2 N
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp [ℓ] at hN
  have hNℓ : 2 ^ ℓ ≤ N := Nat.pow_log_le_self 2 hN0
  have hsq : (ℓ + 1) ^ 2 ≤ 2 ^ ℓ := by simpa using hℓ₁ ℓ (by omega)
  set L := primeBound N
  have hL : L = ℓ / 3 := rfl
  set T := N / (ℓ + 1) ^ 2
  have hT : T = N / (ℓ + 1) / (ℓ + 1) := by
    change N / (ℓ + 1) ^ 2 = _
    rw [Nat.div_div_eq_div_mul, sq]
  have hT1 : 1 ≤ T := (Nat.one_le_div_iff (by positivity)).2 (hsq.trans hNℓ)
  have hthr := explicitThreshold_le_add N hT1
  set r := numBlocks N
  -- assembling the bound
  have hA : (ℓ + 1) * T ≤ N / (ℓ + 1) := hT ▸ Nat.mul_div_le _ _
  have hB : (ℓ + 1) * (N / (L + 1)) ≤ 3 * N :=
    calc (ℓ + 1) * (N / (L + 1)) ≤ 3 * (L + 1) * (N / (L + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 3 * ((L + 1) * (N / (L + 1))) := by ring
      _ ≤ 3 * N := Nat.mul_le_mul_left _ (Nat.mul_div_le N (L + 1))
  have hC : (ℓ + 1) * (N / (ℓ + 1)) ≤ N := Nat.mul_div_le N (ℓ + 1)
  have hD : N / (ℓ + 1) ≤ N / 2 := Nat.div_le_div_left (by omega) two_pos
  calc (ℓ + 1) * explicitThreshold N
      ≤ (ℓ + 1) * (T + 2 * (r * (r + 1)) + N / (L + 1) + 2 * (N / (ℓ + 1))) :=
        Nat.mul_le_mul_left _ hthr
    _ = (ℓ + 1) * T + 2 * ((ℓ + 1) * (r * (r + 1))) + (ℓ + 1) * (N / (L + 1)) +
        2 * ((ℓ + 1) * (N / (ℓ + 1))) := by ring
    _ ≤ 6 * N := by omega

/-- The disperser theorem is not vacuous: `explicitThreshold N < N` for all large `N`. -/
theorem eventually_explicitThreshold_lt : ∀ᶠ N in atTop, explicitThreshold N < N := by
  filter_upwards [eventually_explicitThreshold_le, Nat.eventually_le_log 6 one_lt_two,
    eventually_gt_atTop 0] with N h hℓ hN
  have : 7 * explicitThreshold N ≤ 6 * N := le_trans (Nat.mul_le_mul_right _ (by omega)) h
  omega

/-- **The threshold is `O(N / log N)`**. -/
theorem isBigO_explicitThreshold :
    (fun N : ℕ => (explicitThreshold N : ℝ)) =O[atTop] fun N => (N : ℝ) / Real.log N := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [eventually_explicitThreshold_le, eventually_ge_atTop 2] with N h hN2
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  -- `log N < (⌊log₂ N⌋ + 1) log 2 ≤ ⌊log₂ N⌋ + 1`
  have hlog : Real.log N ≤ Nat.log 2 N + 1 := by
    have h1 : (N : ℝ) < 2 ^ (Nat.log 2 N + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two N
    have h2 := Real.log_lt_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : Real.log 2 < 1 := by
      linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]
    have h4 : 0 < Real.log 2 := Real.log_pos one_lt_two
    push_cast at h2
    nlinarith
  have h' : ((Nat.log 2 N + 1 : ℕ) : ℝ) * explicitThreshold N ≤ 6 * N := by exact_mod_cast h
  push_cast at h'
  rw [← mul_div_assoc, le_div_iff₀ hlogpos]
  nlinarith [(Nat.cast_nonneg (explicitThreshold N) : (0 : ℝ) ≤ explicitThreshold N)]

end Cslib.AffineDisperser
