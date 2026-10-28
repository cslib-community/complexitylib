/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Weights
public import Complexity.Foundations.Data.Int.Residue
public import Complexity.Foundations.NumberTheory.PrimeWindow
public import Complexity.Foundations.RingTheory.CyclicIntRing
public import Mathlib.Data.Matrix.Mul

/-!
# Modular counts and prime selection for integer Exact Triangle

Let `S(a,b,c)` denote `weightSum`, `F(p)` the false-positive count and `Z₀` the zero count. A
minimum-count prime in `[sqrt D / 2, sqrt D)` also minimises false positives. For weights
bounded by `n^κ`, with `16 ≤ D ≤ n` and `1 ≤ κ`, a universal constant bounds its false positives
by `C * κ * n^3 * log n / sqrt D`. The prime count used here is proved for every admitted `D`.

## Main definitions

* `countZeroMod`, `falsePositiveCount`, `zeroCount`: counts of finite triples.
* `IsSelectedPrime`: a minimum-count prime in the specified window.
* `matP`, `matQ`: cyclic polynomial matrices encoding edge residues.

## Main results

* `countZeroMod_eq`: modular count is the sum of false positives and true zeros.
* `coeff_matP_mul_matQ`, `falsePositiveCount_add_zeroCount_eq_sum_coeff`: coefficient
  identities.
* `exists_isSelectedPrime`: the minimum exists.
* `Hashing.falsePositiveCount_le_const_mul`: the uniform false-positive bound.

This is a mathematical reduction step. No native program or charged running-time bound is
asserted. The supplied three matrices retain the existing `HasZeroTriangle` semantics.

## References

The modular reduction is part of [AlmanWilliams2026, Section 3].
Direct adaptation of [Anthropic's
Hashing.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Hashing.lean),
with the minimal count/selection definitions extracted from its `PaperStatements.lean`.
The declaration docstrings describe the Lean definitions and statements in local notation.
The source pin is
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

open Classical in
/-- Prime numbers in the half-open real interval `[sqrt D / 2, sqrt D)`.
-/
noncomputable def primesInRange (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun p => p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D

/-- Count vertex triples whose three edge weights have sum congruent to zero modulo `p`.
-/
def countZeroMod {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n =>
    weightSum wAB wBC wAC t.1 t.2.1 t.2.2 ≡ 0 [ZMOD (p : ℤ)]).card

/-- A prime in `primesInRange D` whose modular-zero count is minimal among all primes in that
window. Tied minima all satisfy this predicate.
-/
def IsSelectedPrime {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D p : ℕ) : Prop :=
  p ∈ primesInRange D ∧ ∀ q ∈ primesInRange D,
    countZeroMod wAB wBC wAC p ≤ countZeroMod wAB wBC wAC q

private theorem four_le_sqrt {D : ℕ} (hD : 16 ≤ D) : 4 ≤ Real.sqrt (D : ℝ) :=
  Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)

/-!
### The primes in the range -/

/-- Window membership is equivalent to primality and the two real endpoint inequalities. The
finite enumeration bound in `primesInRange` excludes no member of the interval.
-/
theorem mem_primesInRange {D p : ℕ} :
    p ∈ primesInRange D ↔ p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D := by
  unfold primesInRange
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- From `p < √D` we get `p ≤ p² < D`.
  have hsq : p ^ 2 < D := by exact_mod_cast (Real.lt_sqrt (Nat.cast_nonneg p)).1 h.2.2
  exact (Nat.le_self_pow two_ne_zero p).trans_lt hsq

/-- Characterize window membership using primality and integer-square inequalities, including the
closed lower and open upper endpoints.
-/
theorem mem_primesInRange_iff_sq {D p : ℕ} :
    p ∈ primesInRange D ↔ p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D := by
  rw [mem_primesInRange]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt0 : 0 ≤ Real.sqrt (D : ℝ) := Real.sqrt_nonneg _
  have hsqrt : (Real.sqrt (D : ℝ)) ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg D)
  constructor
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨hp, ?_, ?_⟩
    · have h : (D : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by nlinarith
      exact_mod_cast h
    · exact_mod_cast (Real.lt_sqrt hp0).1 hhi
  · rintro ⟨hp, hlo, hhi⟩
    refine ⟨hp, ?_, (Real.lt_sqrt hp0).2 (by exact_mod_cast hhi)⟩
    have h : (D : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by exact_mod_cast hlo
    nlinarith

/-- Enumerate the real prime window using a decidable filter of the integers below `D`.
-/
theorem primesInRange_eq_filter (D : ℕ) :
    primesInRange D = (Finset.range D).filter fun p => p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D := by
  ext p
  rw [mem_primesInRange_iff_sq, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨(Nat.le_self_pow two_ne_zero p).trans_lt h.2.2, h⟩, fun h => h.2⟩

/-- A number `r < p` is the sum of the residues of `u` and `v` in `{0, …, p − 1}`, reduced modulo
`p`, exactly if `u + v ≡ r`.
-/
private theorem eq_add_toNat_emod_iff {p r : ℕ} (hp : p ≠ 0) (hr : r < p) (u v : ℤ) :
    r = ((u % (p : ℤ)).toNat + (v % (p : ℤ)).toNat) % p ↔ u + v ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [← Int.natCast_inj, Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr),
    eq_comm]
  push_cast
  rw [Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    ← Int.add_emod]

/-!
### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

section Counting

variable {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ)

/-- A vertex triple has a nonzero integer weight sum that is congruent to zero modulo `p`.
-/
abbrev IsFalsePositive (p : ℕ) (t : Fin n × Fin n × Fin n) : Prop :=
  weightSum wAB wBC wAC t.1 t.2.1 t.2.2 ≠ 0 ∧ (p : ℤ) ∣ weightSum wAB wBC wAC t.1 t.2.1 t.2.2

/-- Count vertex triples satisfying `IsFalsePositive` for the supplied three weight matrices and
modulus.
-/
def falsePositiveCount (p : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => IsFalsePositive wAB wBC wAC p t).card

/-- Count vertex triples whose three supplied edge weights sum to zero as an integer.
-/
def zeroCount : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => weightSum wAB wBC wAC t.1 t.2.1 t.2.2 =
      0).card

/-- The zero-triple count is positive exactly when the supplied matrices satisfy
`HasZeroTriangle`.
-/
theorem zeroCount_pos_iff : 0 < zeroCount wAB wBC wAC ↔ HasZeroTriangle wAB wBC wAC := by
  classical
  simp only [zeroCount, Finset.card_pos, HasZeroTriangle]
  constructor
  · rintro ⟨⟨a, b, c⟩, h⟩
    exact ⟨a, b, c, (Finset.mem_filter.mp h).2⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨(a, b, c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- Partition the modular-zero triples into false positives and exact zero-sum triples. The
exact-zero count is independent of the modulus.
-/
theorem countZeroMod_eq (p : ℕ) : (countZeroMod wAB wBC wAC) p = (falsePositiveCount wAB wBC
    wAC) p + (zeroCount wAB wBC wAC) := by
  classical
  simp only [countZeroMod, falsePositiveCount, zeroCount, Finset.card_filter, ←
      Finset.sum_add_distrib]
  -- A triple with `p ∣ S(a,b,c)` is a zero triangle or a false positive, and not both.
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h0 : weightSum wAB wBC wAC t.1 t.2.1 t.2.2 = 0 <;>
    simp [IsFalsePositive, Int.modEq_zero_iff_dvd, h0]

/-- Encode the A–C weight at `(a,c)` as a power of the cyclic polynomial generator, with exponent
equal to its nonnegative residue modulo `p`.
-/
noncomputable def matP (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicIntRing p) :=
  Matrix.of fun a c => CyclicIntRing.x p ^ (wAC a c % (p : ℤ)).toNat

/-- Encode the B–C weight at `(b,c)` in matrix position `(c,b)`. This orientation makes the
product sum over the middle index `c`.
-/
noncomputable def matQ (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicIntRing p) :=
  Matrix.of fun c b => CyclicIntRing.x p ^ (wBC b c % (p : ℤ)).toNat

/-- For a nonzero modulus and a residue `r < p`, the coefficient of degree `r` in the cyclic
matrix product counts middle vertices whose two incident weights sum to `r` modulo `p`.
-/
theorem coeff_matP_mul_matQ {p : ℕ} (hp : p ≠ 0) (a b : Fin n) (r : ℕ) (hr : r < p) :
    CyclicIntRing.coeff hp r ((matP wAC p * matQ wBC p) a b) =
      ((Finset.univ.filter fun c : Fin n =>
        wAC a c + wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  -- `(PQ)[a,b]` is the sum over `c` of `x^(w(a,c) mod p + w(b,c) mod p)`, and the coefficient of
  -- `x^r` in each term is 1 or 0.
  rw [Matrix.mul_apply]
  simp only [matP, matQ, Matrix.of_apply, ← pow_add]
  rw [map_sum]
  simp only [CyclicIntRing.coeff_x_pow]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eq_add_toNat_emod_iff hp hr]

/-- Recover the total modular-zero count from the cyclic matrix product by summing, over `(a,b)`,
the coefficient at the residue of `-wAB a b`.
-/
theorem falsePositiveCount_add_zeroCount_eq_sum_coeff {p : ℕ} (hp : p ≠ 0) :
    (((falsePositiveCount wAB wBC wAC) p + (zeroCount wAB wBC wAC) : ℕ) : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n,
        CyclicIntRing.coeff hp ((-wAB a b) % (p : ℤ)).toNat ((matP wAC p * matQ wBC p) a b) := by
  classical
  rw [← countZeroMod_eq]
  unfold countZeroMod
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcast := Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) (-wAB a b)
  have hr : ((-wAB a b) % (p : ℤ)).toNat < p := Int.natMod_lt (m := -wAB a b) hp
  rw [(coeff_matP_mul_matQ wBC wAC) hp a b _ hr,
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `S(a,b,c) ≡ 0` says the same as `w(a,c) + w(b,c) ≡ -w(a,b)`, and `-w(a,b)` is congruent to its
  -- residue.
  have hres : (-wAB a b) % (p : ℤ) ≡ -wAB a b [ZMOD (p : ℤ)] := Int.mod_modEq _ _
  have hiff : weightSum wAB wBC wAC a b c ≡ 0 [ZMOD (p : ℤ)] ↔
      wAC a c + wBC b c ≡ ((((-wAB a b) % (p : ℤ)).toNat : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    rw [hcast, show wAC a c + wBC b c ≡ (-wAB a b) % (p : ℤ) [ZMOD (p : ℤ)] ↔
        wAC a c + wBC b c ≡ -wAB a b [ZMOD (p : ℤ)] from
      ⟨fun h => h.trans hres, fun h => h.trans hres.symm⟩,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd,
      show 0 - weightSum wAB wBC wAC a b c = -wAB a b - (wAC a c + wBC b c) by
        simp only [weightSum]; ring]
  simp only [hiff]

end Counting

/-- For `D ≥ 16`, the number of primes in `primesInRange D` is strictly less than `sqrt D`.
-/
theorem card_primesInRange_lt (D : ℕ) (hD : 16 ≤ D) :
    ((primesInRange D).card : ℝ) < Real.sqrt D := by
  have hpos : 0 < Real.sqrt D := by linarith [four_le_sqrt hD]
  -- The primes in the range are among the numbers `1, …, ⌈√D⌉ - 1`.
  have hsub : primesInRange D ⊆ Finset.Ico 1 ⌈Real.sqrt D⌉₊ := by
    intro p hp
    obtain ⟨hprime, -, hlt⟩ := mem_primesInRange.1 hp
    exact Finset.mem_Ico.2 ⟨hprime.one_lt.le, Nat.lt_ceil.2 hlt⟩
  have hcard : (primesInRange D).card + 1 ≤ ⌈Real.sqrt D⌉₊ := by
    have hle := Finset.card_le_card hsub
    have hone : 1 ≤ ⌈Real.sqrt D⌉₊ := Nat.one_le_ceil_iff.2 hpos
    rw [Nat.card_Ico] at hle
    omega
  have hcast : ((primesInRange D).card : ℝ) + 1 ≤ (⌈Real.sqrt D⌉₊ : ℝ) := by exact_mod_cast hcard
  linarith [Nat.ceil_lt_add_one hpos.le]

/-!
### Selecting the prime -/

section Selection

variable {n D p : ℕ} {κ : ℝ} (wAB wBC wAC : Fin n → Fin n → ℤ)

/-- For every `D ≥ 16` and every three supplied weight matrices, the prime window contains a
minimum of the modular-zero count.
-/
theorem exists_isSelectedPrime (D : ℕ) (hD : 16 ≤ D) : ∃ p, IsSelectedPrime wAB wBC wAC D p := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_prime_half_le_and_lt (Real.sqrt D) (four_le_sqrt hD)
  exact Finset.exists_min_image (primesInRange D) (countZeroMod wAB wBC wAC) ⟨q,
      mem_primesInRange.2 hq⟩

/-- A selected minimum of the modular-zero count also minimizes the false-positive count over the
same prime window.
-/
theorem IsSelectedPrime.falsePositiveCount_le {wAB wBC wAC : Fin n → Fin n → ℤ} (hp :
    IsSelectedPrime wAB wBC wAC D p) :
    ∀ q ∈ primesInRange D, (falsePositiveCount wAB wBC wAC) p ≤ (falsePositiveCount wAB wBC wAC)
        q := by
  intro q hq
  have h := hp.2 q hq
  rw [countZeroMod_eq, countZeroMod_eq] at h
  omega

/-!
### The bound on the number of false positives of the selected prime -/

open Classical in
/-- For a fixed nonzero-sum triple and edge weights bounded by `n^κ`, bound the number of window
primes accepting that triple by the base-`sqrt D / 2` logarithm of `3*n^κ`.
-/
theorem card_falsePositive_primes_le (hD : 16 ≤ D) (hT : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ))
    (t : Fin n × Fin n × Fin n) (ht : weightSum wAB wBC wAC t.1 t.2.1 t.2.2 ≠ 0) :
    (((primesInRange D).filter fun p => IsFalsePositive wAB wBC wAC p t).card : ℝ)
      ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  have hsqrt := four_le_sqrt hD
  set divisors := (primesInRange D).filter fun p => IsFalsePositive wAB wBC wAC p t
  have hmem : ∀ p ∈ divisors,
      p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℤ) ∣ weightSum wAB wBC wAC t.1 t.2.1 t.2.2 := by
    intro p hp
    obtain ⟨hrange, -, hdvd⟩ := Finset.mem_filter.1 hp
    obtain ⟨hprime, hge, -⟩ := mem_primesInRange.1 hrange
    exact ⟨hprime, hge, hdvd⟩
  -- The product of these primes divides `S(a,b,c)`, so it is at most `|S(a,b,c)| ≤ 3n^κ`.
  have hdvd : ∏ p ∈ divisors, p ∣ (weightSum wAB wBC wAC t.1 t.2.1 t.2.2).natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime)
      fun p hp => Int.natCast_dvd.1 (hmem p hp).2.2
  have hprod : ∏ p ∈ divisors, (p : ℝ) ≤ 3 * (n : ℝ) ^ κ :=
    calc ∏ p ∈ divisors, (p : ℝ) = ((∏ p ∈ divisors, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
      _ ≤ ((weightSum wAB wBC wAC t.1 t.2.1 t.2.2).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.2 ht) hdvd
      _ = ((|weightSum wAB wBC wAC t.1 t.2.1 t.2.2| : ℤ) : ℝ) := Nat.cast_natAbs _
      _ ≤ 3 * (n : ℝ) ^ κ := (abs_weightSum_le wAB wBC wAC) hT _ _ _
  -- Each of these primes is at least `√D/2`.
  have hpow : (Real.sqrt D / 2) ^ divisors.card ≤ ∏ p ∈ divisors, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by linarith) fun p hp => (hmem p hp).2.1
  have hY : 0 < 3 * (n : ℝ) ^ κ := lt_of_lt_of_le (by positivity) (hpow.trans hprod)
  rw [Real.le_logb_iff_rpow_le (by linarith) hY, Real.rpow_natCast]
  exact hpow.trans hprod

/-- Sum the per-triple prime-divisibility bound over all `n^3` triples. For `D ≥ 16`, `κ ≥ 1` and
edge weights bounded by `n^κ`, the sum of false-positive counts is at most `n^3 * logb (sqrt D /
2) (3*n^κ)`.
-/
theorem sum_falsePositiveCount_le (hD : 16 ≤ D) (hκ : 1 ≤ κ) (hT : WeightsBoundedBy wAB wBC wAC
    ((n : ℝ) ^ κ)) :
    ((∑ p ∈ primesInRange D, (falsePositiveCount wAB wBC wAC) p : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  classical
  have hsqrt := four_le_sqrt hD
  -- Count the pairs (prime, false positive of that prime) triple by triple.
  have hswap : ∑ p ∈ primesInRange D, (falsePositiveCount wAB wBC wAC) p = ∑ t : Fin n × Fin n ×
      Fin n,
      ((primesInRange D).filter fun p => IsFalsePositive wAB wBC wAC p t).card := by
    simp only [falsePositiveCount, Finset.card_filter]
    exact Finset.sum_comm
  have hterm : ∀ t : Fin n × Fin n × Fin n,
      (((primesInRange D).filter fun p => IsFalsePositive wAB wBC wAC p t).card : ℝ)
        ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
    intro t
    by_cases ht : weightSum wAB wBC wAC t.1 t.2.1 t.2.2 = 0
    · -- A zero triangle is a false positive of no prime.
      rw [Finset.filter_eq_empty_iff.2 fun p _ h => h.1 ht, Finset.card_empty, Nat.cast_zero]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fin.pos t.1
      have hpow : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn (by linarith)
      exact Real.logb_nonneg (by linarith) (by linarith)
    · -- Otherwise this is the bound of `card_falsePositive_primes_le` for this triple.
      convert (card_falsePositive_primes_le wAB wBC wAC) hD hT t ht
  rw [hswap, Nat.cast_sum]
  calc ∑ t : Fin n × Fin n × Fin n,
        (((primesInRange D).filter fun p => IsFalsePositive wAB wBC wAC p t).card : ℝ)
      ≤ ∑ _t : Fin n × Fin n × Fin n, Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Selection

/-- There is a universal positive `c` such that every window with `D ≥ 16` contains at least `c *
sqrt D / log D` primes. The proof uses the all-window counting form of Bertrand’s postulate from
`PrimeWindow`, with no prime-number-theorem assumption.
-/
theorem exists_le_card_primesInRange :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D →
      c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := Nat.exists_forall_mul_sqrt_div_log_le_card_primes
  exact ⟨c, hc, fun D hD => hcount D hD _
    fun _ hp hge hlt => mem_primesInRange.2 ⟨hp, hge, hlt⟩⟩

/-- Multiply the selected prime’s minimum false-positive count by the number of window primes to
obtain a bound by the sum of their false-positive counts.
-/
theorem IsSelectedPrime.falsePositiveCount_mul_card_le_sum {n D p : ℕ} {wAB wBC wAC : Fin n →
    Fin n → ℤ}
    (hp : IsSelectedPrime wAB wBC wAC D p) :
    (falsePositiveCount wAB wBC wAC) p * (primesInRange D).card ≤ ∑ q ∈ primesInRange D,
        (falsePositiveCount wAB wBC wAC) q := by
  rw [mul_comm, ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ hp.falsePositiveCount_le

/-- For `D ≥ 16`, compare `log D` with four times `log (sqrt D / 2)`.
-/
theorem log_le_four_mul_log_sqrt_div_two (D : ℕ) (hD : 16 ≤ D) :
    Real.log D ≤ 4 * Real.log (Real.sqrt D / 2) := by
  have hD16 : (16 : ℝ) ≤ D := by exact_mod_cast hD
  have hsqrt : 0 < Real.sqrt D := by linarith [four_le_sqrt hD]
  -- `log(√D/2) = (log D)/2 - log 2`, and `4 log 2 = log 16 ≤ log D`.
  have hlog16 : 4 * Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 4 ≤ D by linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  rw [Real.log_div hsqrt.ne' (by norm_num), Real.log_sqrt (by linarith)]
  linarith [hlog16]

/-- For `16 ≤ D ≤ n`, `κ ≥ 1` and edge weights bounded by `n^κ`, a positive pointwise prime-count
lower bound `c * sqrt D / log D` gives every selected prime at most `(4/c) * n^3 * log (3*n^κ) /
sqrt D` false positives.
-/
theorem falsePositiveCount_le_of_le_card_primesInRange {n D p : ℕ} {κ c : ℝ}
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hc : 0 < c)
    (hcard : c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ)) (hD : 16 ≤ D)
    (hDn : D ≤ n) (hκ : 1 ≤ κ) (hT : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ)) (hp :
        IsSelectedPrime wAB wBC wAC D p) :
    ((falsePositiveCount wAB wBC wAC) p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ)
        / Real.sqrt D) := by
  -- The quantities of the paper's sentence: `r = √D`, `Y = 3n^κ`, and the number of primes in the
  -- range.
  set r := Real.sqrt D
  set Y := 3 * (n : ℝ) ^ κ with hY
  set numPrimes := (primesInRange D).card
  have hr : 4 ≤ r := four_le_sqrt hD
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogD_pos : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogr_pos : 0 < Real.log (r / 2) := Real.log_pos (by linarith)
  have hlogY_nonneg : 0 ≤ Real.log Y := by
    have : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow (by linarith) (by linarith)
    exact Real.log_nonneg (by rw [hY]; linarith)
  -- The selected prime is at most average, after multiplying by the number of primes.
  -- False positives of all primes in the
  -- range add up to at most `n³ log_{r/2} Y`.
  have average : ((falsePositiveCount wAB wBC wAC) p : ℝ) * numPrimes ≤ (n : ℝ) ^ 3 * Real.logb
      (r / 2) Y :=
    le_trans (by exact_mod_cast hp.falsePositiveCount_mul_card_le_sum)
        ((sum_falsePositiveCount_le wAB wBC wAC) hD hκ hT)
  -- The base of the logarithm changes: `log_{r/2} Y ≤ 4 log Y / log D`.
  have hlogD_le : Real.log D ≤ 4 * Real.log (r / 2) := log_le_four_mul_log_sqrt_div_two D hD
  have changeBase : Real.logb (r / 2) Y ≤ 4 * Real.log Y / Real.log D := by
    rw [Real.logb, div_le_div_iff₀ hlogr_pos hlogD_pos]
    linarith [mul_le_mul_of_nonneg_left hlogD_le hlogY_nonneg]
  rw [show 4 / c * ((n : ℝ) ^ 3 * Real.log Y / r) = 4 * (n : ℝ) ^ 3 * Real.log Y / (c * r) by
    field_simp, le_div_iff₀ (by positivity)]
  calc ((falsePositiveCount wAB wBC wAC) p : ℝ) * (c * r) = (falsePositiveCount wAB wBC wAC) p *
      (c * (r / Real.log D)) * Real.log D := by field_simp
    _ ≤ (falsePositiveCount wAB wBC wAC) p * numPrimes * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * Real.logb (r / 2) Y * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * (4 * Real.log Y / Real.log D) * Real.log D := by gcongr
    _ = 4 * (n : ℝ) ^ 3 * Real.log Y := by field_simp

/-- There is a universal `C ≥ 1` such that, for `16 ≤ D ≤ n`, `κ ≥ 1` and edge weights bounded by
`n^κ`, every selected prime has at most `C * κ * n^3 * log n / sqrt D` false positives.
-/
theorem exists_falsePositiveCount_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n D p : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ κ → ∀ wAB wBC wAC : Fin n → Fin
        n → ℤ,
      WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ) → IsSelectedPrime wAB wBC wAC D p →
      ((falsePositiveCount wAB wBC wAC) p : ℝ) ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt
          D) := by
  obtain ⟨c, hc, hcard⟩ := exists_le_card_primesInRange
  refine ⟨max 1 (8 / c), le_max_left _ _, fun {n D p κ} hD hDn hκ wAB wBC wAC hT hp => ?_⟩
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- `log(3n^κ) = log 3 + κ log n ≤ 2κ log n`, because `3 ≤ n` and `κ ≥ 1`.
  have hlog : Real.log (3 * (n : ℝ) ^ κ) ≤ 2 * κ * Real.log n := by
    have hlog3 : Real.log 3 ≤ κ * Real.log n :=
      (Real.log_le_log (by norm_num) (by linarith)).trans (le_mul_of_one_le_left hlogn hκ)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
    linarith [hlog3]
  calc ((falsePositiveCount wAB wBC wAC) p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^
      κ) / Real.sqrt D) :=
        (falsePositiveCount_le_of_le_card_primesInRange wAB wBC wAC) hc (hcard D hD) hD hDn hκ hT hp
    _ ≤ 4 / c * ((n : ℝ) ^ 3 * (2 * κ * Real.log n) / Real.sqrt D) := by gcongr
    _ = 8 / c * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by ring
    _ ≤ max 1 (8 / c) * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
        gcongr
        exact le_max_right _ _

/-- A universal real constant witnessing `exists_falsePositiveCount_le`. It depends on none of the
input dimensions, weight matrices, exponent or selected prime, and is at least one.
-/
noncomputable def Hashing.falsePositiveConst : ℝ := Classical.choose exists_falsePositiveCount_le

/-- The universal false-positive constant `Hashing.falsePositiveConst` is at least one.
-/
theorem Hashing.one_le_falsePositiveConst : 1 ≤ Hashing.falsePositiveConst :=
  (Classical.choose_spec exists_falsePositiveCount_le).1

/-- For `16 ≤ D ≤ n`, `κ ≥ 1` and edge weights bounded by `n^κ`, bound every selected prime’s
false-positive count by `Hashing.falsePositiveConst * κ * n^3 * log n / sqrt D`.
-/
theorem Hashing.falsePositiveCount_le_const_mul {n D p : ℕ} {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n)
    (hκ : 1 ≤ κ) (wAB wBC wAC : Fin n → Fin n → ℤ) (hT : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ))
    (hp : IsSelectedPrime wAB wBC wAC D p) :
    ((falsePositiveCount wAB wBC wAC) p : ℝ) ≤ Hashing.falsePositiveConst * (κ * (n : ℝ) ^ 3 *
        Real.log n / Real.sqrt D) :=
  (Classical.choose_spec exists_falsePositiveCount_le).2 hD hDn hκ wAB wBC wAC hT hp

end Cslib.Algorithms.ExactTriangle
