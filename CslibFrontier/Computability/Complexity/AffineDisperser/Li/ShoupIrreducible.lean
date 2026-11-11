/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.AffineDisperser.BinaryPolynomial
public import CslibFrontier.Computability.Complexity.AffineDisperser.Coordinates
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Bits
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import CslibFrontier.Foundations.Combinatorics.AffineDisperser.AffineSubspace
import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Tactic.Linarith

/-!
# Shoup's deterministic irreducible polynomials and an unconditional `O(N^(4/5))` affine disperser

For every input length `N`, this module chooses an odd prime `q = primeDeg N ∈ (M, 2M]` with
`M = (max 2 (fifthRoot N)) ^ 3 ≈ N ^ (3 / 5)`, constructs an explicit irreducible polynomial
`shoupIrreducibleBits q : List Bool` of degree `q` over `𝔽₂` deterministically using Shoup's
algorithm [Shoup1990], and evaluates Ben-Sasson and Kopparty's `traceSym 1 r t` over the single
prime-degree field `𝔽_{2 ^ q}` (`r = ⌊N / q⌋`, `t = max 1 (fifthRoot N)`).

Because `𝔽_{2 ^ q}` (`q` prime) has only `𝔽₂` (`2 ^ 1` elements) as a proper subfield, applying
`Cslib.AffineDisperser.exists_traceSymBits_ne` yields an unconditional explicit affine disperser
`primeDisperser N : BitString N → Bool` for dimension `primeThreshold N + 1 = O(N ^ (4 / 5))`.

This implements Milestone 1 of Issue #4323 (replacing `O(N / log N)` with `O(N ^ (4 / 5))` in `P`
via Shoup's deterministic single-prime irreducible construction). Reducing the dimension threshold
further from `O(N ^ (4 / 5))` to `O(log N)` [Li2023] remains open.

## Main definitions

* `Cslib.AffineDisperser.Li.fifthRoot`, `primeThresholdBound`, `primeDeg`: single-prime parameter
  selection (`q ≈ N ^ (3 / 5)`).
* `Cslib.AffineDisperser.Li.ordTwoMod`, `qAdicValTwoPowSubOne`, `shoupCyclicFactor`,
  `shoupBeta`, `shoupPowers`, `shoupMinPolyMatrix`, `shoupIrreducibleBits`: Shoup's deterministic
  irreducible polynomial algorithm over `𝔽₂`.
* `Cslib.AffineDisperser.Li.primeMulTable`, `primeDisperserBits`, `primeDisperser`,
  `primeThreshold`: the single-prime affine disperser and its dimension threshold.

## Main results

* `Cslib.AffineDisperser.Li.irreducible_polyOfBits_shoupIrreducibleBits` and
  `Cslib.AffineDisperser.Li.natDegree_polyOfBits_shoupIrreducibleBits`: correctness of Shoup's
  irreducible polynomial of degree `q` for every odd prime `q`.
* `Cslib.AffineDisperser.Li.isAffineDisperser_primeDisperser`: `primeDisperser N` is an affine
  disperser for dimension `primeThreshold N + 1`.
* `Cslib.AffineDisperser.Li.eventually_primeThreshold_le` and
  `Cslib.AffineDisperser.Li.isBigO_primeThreshold`: `primeThreshold N = O(N ^ (4 / 5))`.

## References

* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

public section

namespace Cslib.AffineDisperser.Li

open Asymptotics BitString Filter Module Polynomial
open scoped Matrix

private theorem sum_fin_cast {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a = b)
    (f : ℕ → M) : ∑ i : Fin a, f i.1 = ∑ j : Fin b, f j.1 := by
  subst h
  rfl

private theorem polyOfBits_false_cons (p : List Bool) :
    polyOfBits (false :: p) = X * polyOfBits p := by
  rw [polyOfBits_cons, show bitEquiv.symm false = 0 by rfl, map_zero, zero_add]

/-! ### Antitone counting helper and parameter selection -/

private theorem countP_range_mono (P : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    (List.range m).countP P ≤ (List.range n).countP P := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [List.range_succ, List.countP_append]
    exact le_trans ih (Nat.le_add_right _ _)

private theorem countP_range_le_of_forall_false (P : ℕ → Bool) (n k : ℕ)
    (hfalse : ∀ j, k ≤ j → P j = false) :
    (List.range n).countP P ≤ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    by_cases hkn : k ≤ n
    · simp only [hfalse n hkn, Bool.false_eq_true, ↓reduceIte, add_zero]
      exact ih
    · have hle : (List.range n).countP P ≤ n := by
        simpa using (List.countP_le_length : (List.range n).countP P ≤ (List.range n).length)
      calc (List.range n).countP P + (if P n = true then 1 else 0)
          ≤ n + 1 := Nat.add_le_add hle (by split_ifs <;> omega)
        _ ≤ k := by omega

private theorem countP_range_true_lt {P : ℕ → Bool}
    (hanti : ∀ {a b}, a ≤ b → P b = true → P a = true) {n k : ℕ}
    (hk : k < (List.range n).countP P) : P k = true := by
  by_contra hnt
  have hfalse : ∀ j, k ≤ j → P j = false := by
    intro j hj
    cases hP : P j with
    | false => rfl
    | true => exact absurd (hanti hj hP) hnt
  exact absurd (countP_range_le_of_forall_false P n k hfalse) (not_le.mpr hk)

private theorem le_countP_range_of_forall_true (P : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n)
    (htrue : ∀ j < m, P j = true) :
    m ≤ (List.range n).countP P := by
  have hprefix : (List.range m).countP P = m := by
    clear hmn n
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton,
        ite_eq_left (htrue m (Nat.lt_succ_self m)), ih fun j hj => htrue j (by omega)]
  rw [← hprefix]
  exact countP_range_mono P hmn

/-- Floor fifth root `⌊N ^ (1 / 5)⌋`. -/
@[expose] def fifthRoot (N : ℕ) : ℕ :=
  (List.range N).countP fun m => decide ((m + 1) ^ 5 ≤ N)

/-- `fifthRoot N ≤ N`. -/
theorem fifthRoot_le (N : ℕ) : fifthRoot N ≤ N := by
  unfold fifthRoot
  simpa using (List.countP_le_length :
    (List.range N).countP (fun m => decide ((m + 1) ^ 5 ≤ N)) ≤ (List.range N).length)

/-- `fifthRoot N` is the exact floor fifth root `⌊N ^ (1 / 5)⌋`. -/
theorem fifthRoot_spec (N : ℕ) :
    (fifthRoot N) ^ 5 ≤ N ∧ N < (fifthRoot N + 1) ^ 5 := by
  set P : ℕ → Bool := fun m => decide ((m + 1) ^ 5 ≤ N)
  have hanti : ∀ {a b}, a ≤ b → P b = true → P a = true := by
    intro a b hab hb
    simp only [P, decide_eq_true_eq] at hb ⊢
    exact le_trans (Nat.pow_le_pow_left (by omega) 5) hb
  set r := fifthRoot N
  have hlow : r ^ 5 ≤ N := by
    cases hr : r with
    | zero => simp
    | succ k =>
      have hk : k < (List.range N).countP P := by
        change k < r
        rw [hr]
        exact Nat.lt_succ_self k
      have htrue := countP_range_true_lt hanti hk
      simpa [P] using htrue
  have hhigh : N < (r + 1) ^ 5 := by
    by_contra hle
    push Not at hle
    have hr1_le : r + 1 ≤ N :=
      le_trans (Nat.le_self_pow (by decide : 5 ≠ 0) (r + 1)) hle
    have hcount := le_countP_range_of_forall_true P hr1_le fun j hj => by
      simp only [P, decide_eq_true_eq]
      exact le_trans (Nat.pow_le_pow_left hj 5) hle
    change r + 1 ≤ r at hcount
    omega
  exact ⟨hlow, hhigh⟩

/-- Lower bound `M = (max 2 ⌊N ^ (1 / 5)⌋) ^ 3` on the field prime degree. -/
@[expose] def primeThresholdBound (N : ℕ) : ℕ :=
  (max 2 (fifthRoot N)) ^ 3

/-- The least prime in `(M, 2M]` where `M = primeThresholdBound N`. -/
@[expose] def primeDeg (N : ℕ) : ℕ :=
  let M := primeThresholdBound N
  (((List.range M).map fun i => M + 1 + i).find? Nat.Prime).getD (2 * M)

/-- `primeDeg N` is a prime in `(primeThresholdBound N, 2 * primeThresholdBound N]`. -/
theorem primeDeg_spec (N : ℕ) :
    (primeDeg N).Prime ∧ primeThresholdBound N < primeDeg N ∧
      primeDeg N ≤ 2 * primeThresholdBound N := by
  set M := primeThresholdBound N
  have hM_ge : 8 ≤ M := by
    have h2 : 2 ≤ max 2 (fifthRoot N) := le_max_left _ _
    calc 8 = 2 ^ 3 := by decide
      _ ≤ (max 2 (fifthRoot N)) ^ 3 := Nat.pow_le_pow_left h2 3
  obtain ⟨q, hqp, hMq, hq2M⟩ := Nat.exists_prime_lt_and_le_two_mul M (by omega)
  let L := (List.range M).map fun i => M + 1 + i
  have hq_mem : q ∈ L := by
    simp only [L, List.mem_map, List.mem_range]
    exact ⟨q - (M + 1), by omega, by omega⟩
  have hsome : (L.find? Nat.Prime).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨q, hq_mem, by simp [hqp]⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hp_mem : p ∈ L := List.mem_of_find?_eq_some hp
  have hp_prime : p.Prime := by simpa using List.find?_some hp
  simp only [L, List.mem_map, List.mem_range] at hp_mem
  obtain ⟨i, hi, rfl⟩ := hp_mem
  have hdeg : primeDeg N = M + 1 + i := by
    change (L.find? Nat.Prime).getD (2 * M) = M + 1 + i
    rw [hp, Option.getD_some]
  rw [hdeg]
  exact ⟨hp_prime, by omega, by omega⟩

/-- `9 ≤ primeDeg N` for every `N`. -/
theorem nine_le_primeDeg (N : ℕ) : 9 ≤ primeDeg N := by
  have hM : 8 ≤ primeThresholdBound N := by
    have h2 : 2 ≤ max 2 (fifthRoot N) := le_max_left _ _
    calc 8 = 2 ^ 3 := by decide
      _ ≤ (max 2 (fifthRoot N)) ^ 3 := Nat.pow_le_pow_left h2 3
  have := (primeDeg_spec N).2.1
  omega

/-- `3 ≤ primeDeg N` for every `N`. -/
theorem three_le_primeDeg (N : ℕ) : 3 ≤ primeDeg N :=
  le_trans (by decide) (nine_le_primeDeg N)

/-! ### Multiplicative order and `q`-adic valuation of `2 ^ m - 1` -/

/-- Multiplicative order of `2` modulo `q` (returning `0` when `q ≤ 2` or `Even q`). -/
@[expose] def ordTwoMod (q : ℕ) : ℕ :=
  (((List.range (q - 1)).find? fun i => 2 ^ (i + 1) % q == 1).map (· + 1)).getD 0

/-- `q`-adic valuation of `2 ^ m - 1` capped at `q` (`max {j ≤ q | q ^ j ∣ 2 ^ m - 1}`). -/
@[expose] def qAdicValTwoPowSubOne (q m : ℕ) : ℕ :=
  (List.range q).countP fun j => decide (2 ^ m % q ^ (j + 1) == 1)

private theorem dvd_two_pow_sub_one_iff_modEq {m M : ℕ} (hM : 1 < M) :
    M ∣ 2 ^ m - 1 ↔ 2 ^ m % M = 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  constructor
  · intro ⟨k, hk⟩
    have heq : 2 ^ m = M * k + 1 := by omega
    rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hM]
  · intro hmod
    have hdiv := Nat.div_add_mod (2 ^ m) M
    rw [hmod] at hdiv
    exact ⟨2 ^ m / M, by omega⟩

/-- `ordTwoMod q` equals the multiplicative order of `2` modulo an odd prime `q`. -/
theorem ordTwoMod_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    2 ≤ m ∧ m < q ∧ q ∣ 2 ^ m - 1 ∧ (∀ j, 0 < j → j < m → 2 ^ j % q ≠ 1) ∧
      m = orderOf (ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2
        omega)) := by
  have hndvd2 : ¬ 2 ∣ q := by
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2
    omega
  have hcop : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr hndvd2
  have : NeZero q := ⟨by omega⟩
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hcop
  set d := orderOf u
  have hu_pow : ∀ j : ℕ, 2 ^ j % q = 1 ↔ u ^ j = 1 := by
    intro j
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime,
      ← Nat.cast_pow]
    conv_rhs => rw [← Nat.cast_one (R := ZMod q)]
    rw [ZMod.natCast_eq_natCast_iff]
    conv_rhs => rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < q)]
  have hd_pos : 0 < d := orderOf_pos u
  have hd_dvd_phi : d ∣ q - 1 := by
    have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
    rw [← hcard]
    exact orderOf_dvd_card
  have hd_le : d ≤ q - 1 := Nat.le_of_dvd (by omega) hd_dvd_phi
  have hne1 : u ^ 1 ≠ 1 := by
    intro h1
    have := (hu_pow 1).mpr h1
    rw [pow_one, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hd_ge2 : 2 ≤ d := by
    rcases eq_or_ne d 1 with h1 | _
    · exfalso; apply hne1; rw [← h1]; exact pow_orderOf_eq_one u
    · omega
  let L := List.range (q - 1)
  have hfind_isSome : (L.find? fun i => 2 ^ (i + 1) % q == 1).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨d - 1, by simp [L]; omega, ?_⟩
    rw [beq_iff_eq, Nat.sub_add_cancel hd_pos, hu_pow]
    exact pow_orderOf_eq_one u
  obtain ⟨r, hr_eq⟩ := Option.isSome_iff_exists.mp hfind_isSome
  obtain ⟨hr_pred, k, hk_lt, hk_get, hk_min⟩ := List.find?_eq_some_iff_getElem.mp hr_eq
  simp only [L, List.length_range] at hk_lt
  simp only [L, List.getElem_range] at hk_get
  subst hk_get
  have hm_eq : ordTwoMod q = k + 1 := by
    simp only [ordTwoMod]
    change ((L.find? fun i => 2 ^ (i + 1) % q == 1).map (· + 1)).getD 0 = k + 1
    rw [hr_eq, Option.map_some, Option.getD_some]
  have hk_mod : 2 ^ (k + 1) % q = 1 := by simpa using hr_pred
  have hd_dvd_k : d ∣ k + 1 := orderOf_dvd_iff_pow_eq_one.mpr ((hu_pow _).mp hk_mod)
  have hk_le_d : k + 1 ≤ d := by
    by_contra hlt
    have hdm1_lt : d - 1 < k := by omega
    have hmin := hk_min (d - 1) hdm1_lt
    simp only [L, List.getElem_range, Nat.sub_add_cancel hd_pos] at hmin
    have h1 : 2 ^ d % q = 1 := (hu_pow d).mpr (pow_orderOf_eq_one u)
    simp [h1] at hmin
  have hk_eq_d : k + 1 = d := Nat.le_antisymm hk_le_d (Nat.le_of_dvd (by omega) hd_dvd_k)
  have hdvd_sub : q ∣ 2 ^ (k + 1) - 1 :=
    (dvd_two_pow_sub_one_iff_modEq (by omega : 1 < q)).mpr hk_mod
  have hlt_neq : ∀ j, 0 < j → j < k + 1 → 2 ^ j % q ≠ 1 := by
    intro j hj0 hj_lt hmod
    have hmin := hk_min (j - 1) (by omega)
    simp only [L, List.getElem_range, Nat.sub_add_cancel hj0] at hmin
    simp [hmod] at hmin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm_eq, hk_eq_d]; exact hd_ge2
  · rw [hm_eq, hk_eq_d]; exact lt_of_le_of_lt hd_le (Nat.sub_lt (by omega) zero_lt_one)
  · rwa [hm_eq]
  · intro j hj0 hj_lt
    rw [hm_eq] at hj_lt
    exact hlt_neq j hj0 hj_lt
  · rw [hm_eq, hk_eq_d]

/-- `qAdicValTwoPowSubOne q m` gives the exact `q`-adic valuation `k ≥ 1` dividing `2 ^ m - 1`. -/
theorem qAdicValTwoPowSubOne_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    1 ≤ k ∧ k < q ∧ q ^ k ∣ 2 ^ m - 1 ∧ ¬ q ^ (k + 1) ∣ 2 ^ m - 1 := by
  set m := ordTwoMod q
  set k := qAdicValTwoPowSubOne q m
  obtain ⟨hm2, hmq, hq_dvd, -, -⟩ := ordTwoMod_spec hq hq3
  set P : ℕ → Bool := fun j => decide (2 ^ m % q ^ (j + 1) == 1)
  have hanti : ∀ {a b}, a ≤ b → P b = true → P a = true := by
    intro a b hab hb
    simp only [P, decide_eq_true_eq, beq_iff_eq] at hb ⊢
    have hqa : 1 < q ^ (a + 1) := Nat.one_lt_pow (by omega) (by omega)
    have hqb : 1 < q ^ (b + 1) := Nat.one_lt_pow (by omega) (by omega)
    rw [← dvd_two_pow_sub_one_iff_modEq hqa]
    rw [← dvd_two_pow_sub_one_iff_modEq hqb] at hb
    exact dvd_trans (Nat.pow_dvd_pow q (by omega)) hb
  have hk_ge1 : 1 ≤ k := by
    refine le_countP_range_of_forall_true P (by omega) fun j hj => ?_
    have : j = 0 := by omega
    subst this
    simp only [P, decide_eq_true_eq, beq_iff_eq]
    have hq1 : 1 < q ^ (0 + 1) := by simp; omega
    rw [← dvd_two_pow_sub_one_iff_modEq hq1]
    simpa using hq_dvd
  have hk_lt : k < q := by
    by_contra hge
    have hk_q : q - 1 < k := by omega
    have hP := countP_range_true_lt hanti hk_q
    simp only [P, decide_eq_true_eq, beq_iff_eq, Nat.sub_add_cancel (by omega : 1 ≤ q)] at hP
    have hqq : 1 < q ^ q := Nat.one_lt_pow (by omega) (by omega)
    have hdvd := (dvd_two_pow_sub_one_iff_modEq hqq).mpr hP
    have hpos : 0 < 2 ^ m - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) one_lt_two)
    have hle1 : q ^ q ≤ 2 ^ m - 1 := Nat.le_of_dvd hpos hdvd
    have hle2 : 2 ^ m - 1 < 2 ^ q := lt_of_lt_of_le (Nat.sub_lt Nat.one_le_two_pow one_pos)
      (Nat.pow_le_pow_right two_pos hmq.le)
    have hle3 : 2 ^ q < q ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  have hk_dvd : q ^ k ∣ 2 ^ m - 1 := by
    have hlt_k : k - 1 < (List.range q).countP P := by
      change k - 1 < k
      omega
    have hP := countP_range_true_lt hanti hlt_k
    simp only [P, decide_eq_true_eq, beq_iff_eq, Nat.sub_add_cancel hk_ge1] at hP
    have hqk : 1 < q ^ k := Nat.one_lt_pow (a := q) (n := k) (by omega) (by omega)
    exact (dvd_two_pow_sub_one_iff_modEq (m := m) (M := q ^ k) hqk).mpr hP
  have hk1_ndvd : ¬ q ^ (k + 1) ∣ 2 ^ m - 1 := by
    intro hdvd
    have hP : ∀ j < k + 1, P j = true := by
      intro j hj
      simp only [P, decide_eq_true_eq, beq_iff_eq]
      have hqj : 1 < q ^ (j + 1) := Nat.one_lt_pow (by omega) (by omega)
      rw [← dvd_two_pow_sub_one_iff_modEq hqj]
      exact dvd_trans (Nat.pow_dvd_pow q (by omega)) hdvd
    have hcount := le_countP_range_of_forall_true P hk_lt hP
    change k + 1 ≤ k at hcount
    omega
  exact ⟨hk_ge1, hk_lt, hk_dvd, hk1_ndvd⟩

/-! ### Cyclotomic factor chain -/

/-- Step `k - 1` times from an irreducible factor of `Φ_q` to an irreducible factor of
`Φ_{q ^ max 1 k}` over `𝔽₂`. -/
@[expose] def shoupCyclicFactor (q k : ℕ) : List Bool :=
  (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[k - 1]
    (berlekampIrreducibleFactor (List.replicate q true))

private theorem polyOfBits_replicate_true_eq_cyclotomic {q : ℕ} (hq : q.Prime) :
    polyOfBits (List.replicate q true) = cyclotomic q (ZMod 2) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [cyclotomic_prime]
  ext i
  rw [coeff_polyOfBits, finsetSum_coeff]
  simp_rw [coeff_X_pow]
  by_cases hi : i < q
  · rw [Finset.sum_eq_single i]
    · have hi' : i < (List.replicate q true).length := by simp [hi]
      rw [List.getD_eq_getElem _ _ hi', List.getElem_replicate]
      simp [show bitEquiv.symm true = 1 by rfl]
    · intro j _ hj
      simp [hj.symm]
    · intro hm
      exact absurd (Finset.mem_range.mpr hi) hm
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hne : i ≠ j := by omega
    simp [hne]

private theorem cyclotomic_prime_pow_comp_X_pow {q j : ℕ} (hq : q.Prime) :
    (cyclotomic (q ^ (j + 1)) (ZMod 2)).comp (X ^ q) = cyclotomic (q ^ (j + 2)) (ZMod 2) := by
  have : Fact q.Prime := ⟨hq⟩
  have h1 : cyclotomic (q ^ (j + 1)) (ZMod 2) =
      (cyclotomic q (ZMod 2)).comp (X ^ (q ^ j)) := by
    rw [cyclotomic_prime_pow_eq_geom_sum hq, cyclotomic_prime, sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X_pow_comp]
  have h2 : cyclotomic (q ^ (j + 2)) (ZMod 2) =
      (cyclotomic q (ZMod 2)).comp (X ^ (q ^ (j + 1))) := by
    rw [cyclotomic_prime_pow_eq_geom_sum hq, cyclotomic_prime, sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [X_pow_comp]
  rw [h1, h2, comp_assoc, X_pow_comp, ← pow_mul, mul_comm q (q ^ j), ← pow_succ]

/-- Invariant for iterating Berlekamp factoring under `polyComposePow q` in Shoup's step. -/
theorem shoupCyclicFactor_iterate_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (s : ℕ) :
    let f := (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))
    polyTrim f = f ∧ polyOfBits f ∣ cyclotomic (q ^ (s + 1)) (ZMod 2) ∧
      Irreducible (polyOfBits f) ∧ 0 < (polyOfBits f).natDegree := by
  have hndvd2 : ∀ t : ℕ, ¬ 2 ∣ q ^ t := by
    intro t ht
    have h2q : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow ht
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q
    omega
  have hne2 : ∀ t : ℕ, NeZero ((q ^ t : ℕ) : ZMod 2) := fun t =>
    ⟨fun h => hndvd2 t ((CharP.cast_eq_zero_iff (ZMod 2) 2 (q ^ t)).mp h)⟩
  induction s with
  | zero =>
    simp only [Function.iterate_zero, id_eq, zero_add]
    have hrep := polyOfBits_replicate_true_eq_cyclotomic hq
    have hsq : Squarefree (polyOfBits (List.replicate q true)) := by
      rw [hrep]
      have : NeZero (q : ZMod 2) := by simpa only [pow_one] using hne2 1
      exact squarefree_cyclotomic q (ZMod 2)
    have hdeg : 0 < (polyOfBits (List.replicate q true)).natDegree := by
      rw [hrep, natDegree_cyclotomic, Nat.totient_prime hq]
      omega
    obtain ⟨hdvd, hirr, hdeg'⟩ := polyOfBits_berlekampIrreducibleFactor_dvd hsq hdeg
    rw [pow_one]
    exact ⟨polyTrim_berlekampIrreducibleFactor _, by rwa [hrep] at hdvd, hirr, hdeg'⟩
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨ht, hdvd, hirr, hdeg⟩ := ih
    set g := (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))
    have hdvd_comp :
        polyOfBits (polyComposePow q g) ∣ cyclotomic (q ^ (s + 2)) (ZMod 2) := by
      rw [polyOfBits_polyComposePow (by omega), ← cyclotomic_prime_pow_comp_X_pow hq]
      rcases hdvd with ⟨r, hr⟩
      exact ⟨r.comp (X ^ q), by rw [hr, mul_comp]⟩
    have hsq_comp : Squarefree (polyOfBits (polyComposePow q g)) := by
      have := hne2 (s + 2)
      exact Squarefree.squarefree_of_dvd hdvd_comp (squarefree_cyclotomic (q ^ (s + 2)) (ZMod 2))
    have hdeg_comp : 0 < (polyOfBits (polyComposePow q g)).natDegree := by
      rw [polyOfBits_polyComposePow (by omega), natDegree_comp, natDegree_X_pow]
      exact Nat.mul_pos hdeg (by omega)
    obtain ⟨hdvd', hirr', hdeg'⟩ := polyOfBits_berlekampIrreducibleFactor_dvd hsq_comp hdeg_comp
    exact ⟨polyTrim_berlekampIrreducibleFactor _, hdvd'.trans hdvd_comp, hirr', hdeg'⟩

/-- `shoupCyclicFactor q k` produces an irreducible factor of degree `m = ordTwoMod q` dividing
`cyclotomic (q ^ k) (ZMod 2)`, so its root generates `𝔽_{2 ^ m}` and has multiplicative order
`q ^ k`. -/
theorem shoupCyclicFactor_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    let f := shoupCyclicFactor q k
    polyTrim f = f ∧ polyOfBits f ∣ cyclotomic (q ^ k) (ZMod 2) ∧
      Irreducible (polyOfBits f) ∧ (polyOfBits f).natDegree = m ∧ f.length = m + 1 := by
  set m := ordTwoMod q
  set k := qAdicValTwoPowSubOne q m
  obtain ⟨hm2, hmq, -, -, hm_ord⟩ := ordTwoMod_spec hq hq3
  obtain ⟨hk1, -, hk_dvd, -⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨ht, hdvd, hirr, hdeg⟩ := shoupCyclicFactor_iterate_spec hq hq3 (k - 1)
  have hdef : shoupCyclicFactor q k =
      (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[k - 1]
        (berlekampIrreducibleFactor (List.replicate q true)) := rfl
  rw [← hdef, Nat.sub_add_cancel hk1] at hdvd
  rw [← hdef] at ht hirr hdeg
  have hndvd2 : ¬ 2 ∣ q ^ k := by
    intro ht'
    have h2q : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow ht'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (q ^ k) := Nat.prime_two.coprime_iff_not_dvd.mpr hndvd2
  have hnatDeg : (polyOfBits (shoupCyclicFactor q k)).natDegree =
      orderOf (ZMod.unitOfCoprime 2 hcop) := by
    have hcard : Fintype.card (ZMod 2) = 2 ^ 1 := by simp
    simpa only [pow_one] using
      Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (K := ZMod 2) (f := 1) hcard hcop
        hdvd hirr
  have hord_eq : orderOf (ZMod.unitOfCoprime 2 hcop) = m := by
    set u := ZMod.unitOfCoprime 2 hcop
    have hu_pow_m : u ^ m = 1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime,
        ← Nat.cast_pow]
      conv_rhs => rw [← Nat.cast_one (R := ZMod (q ^ k))]
      rw [ZMod.natCast_eq_natCast_iff]
      have hqk : 1 < q ^ k := Nat.one_lt_pow (Nat.ne_of_gt hk1) (by omega)
      have hmod := (dvd_two_pow_sub_one_iff_modEq (m := m) (M := q ^ k) hqk).mp hk_dvd
      exact hmod.trans (Nat.mod_eq_of_lt hqk).symm
    have hord_dvd_m : orderOf u ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hu_pow_m
    have hcop_q : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2
      omega
    have hm_dvd_ord : m ∣ orderOf u := by
      dsimp only [m]
      rw [hm_ord, orderOf_dvd_iff_pow_eq_one]
      have h1 : (u ^ orderOf u : (ZMod (q ^ k))ˣ) = 1 := pow_orderOf_eq_one u
      have h1' := congrArg (fun x : (ZMod (q ^ k))ˣ => (x : ZMod (q ^ k))) h1
      rw [Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime] at h1'
      have hmod1 : 2 ^ orderOf u ≡ 1 [MOD q ^ k] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
        exact h1'
      have hk_ne : k ≠ 0 := Nat.ne_of_gt hk1
      have hmod2 : 2 ^ orderOf u ≡ 1 [MOD q] :=
        hmod1.of_dvd (dvd_pow_self q hk_ne)
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime,
        ← Nat.cast_pow]
      conv_rhs => rw [← Nat.cast_one (R := ZMod q)]
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmod2
    exact Nat.dvd_antisymm hord_dvd_m hm_dvd_ord
  have hdeg_m : (polyOfBits (shoupCyclicFactor q k)).natDegree = m := hnatDeg.trans hord_eq
  have hf_ne : shoupCyclicFactor q k ≠ [] := by
    intro hnil
    rw [hnil, polyOfBits_nil, natDegree_zero] at hdeg_m
    omega
  have hlen : (shoupCyclicFactor q k).length = m + 1 := by
    have := natDegree_polyOfBits_of_polyTrim ht hf_ne
    have := List.length_pos_of_ne_nil hf_ne
    omega
  exact ⟨ht, hdvd, hirr, hdeg_m, hlen⟩

/-- Length bound along iterations of `shoupCyclicFactor`. -/
theorem length_shoupCyclicFactor_iterate_le {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) {s : ℕ}
    (hs : s ≤ qAdicValTwoPowSubOne q (ordTwoMod q) - 1) :
    ((fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))).length ≤ q := by
  set m := ordTwoMod q
  set k := qAdicValTwoPowSubOne q m
  obtain ⟨hm2, hmq, -, -, -⟩ := ordTwoMod_spec hq hq3
  obtain ⟨hk1, -, hk_dvd, -⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨ht, hdvd, hirr, hdeg_pos⟩ := shoupCyclicFactor_iterate_spec hq hq3 s
  set fs := (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
    (berlekampIrreducibleFactor (List.replicate q true))
  have hndvd2 : ¬ 2 ∣ q ^ (s + 1) := by
    intro h2
    have h2q := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (q ^ (s + 1)) := Nat.prime_two.coprime_iff_not_dvd.mpr hndvd2
  have hnatDeg : (polyOfBits fs).natDegree = orderOf (ZMod.unitOfCoprime 2 hcop) := by
    have hcard : Fintype.card (ZMod 2) = 2 ^ 1 := by simp
    simpa only [pow_one] using
      Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (K := ZMod 2) (f := 1) hcard hcop
        hdvd hirr
  set u := ZMod.unitOfCoprime 2 hcop
  have hsk : s + 1 ≤ k := by
    dsimp only [k, m] at hs ⊢
    omega
  have hpow_dvd : q ^ (s + 1) ∣ 2 ^ m - 1 :=
    dvd_trans (Nat.pow_dvd_pow q hsk) hk_dvd
  have hu_pow_m : u ^ m = 1 := by
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime,
      ← Nat.cast_pow]
    conv_rhs => rw [← Nat.cast_one (R := ZMod (q ^ (s + 1)))]
    rw [ZMod.natCast_eq_natCast_iff]
    have hqs : 1 < q ^ (s + 1) := Nat.one_lt_pow (Nat.succ_ne_zero s) (by omega)
    have hmod := (dvd_two_pow_sub_one_iff_modEq (m := m) (M := q ^ (s + 1)) hqs).mp hpow_dvd
    exact hmod.trans (Nat.mod_eq_of_lt hqs).symm
  have hord_dvd : orderOf u ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hu_pow_m
  have hdeg_le : (polyOfBits fs).natDegree ≤ m := by
    rw [hnatDeg]
    exact Nat.le_of_dvd (by omega) hord_dvd
  have hfs_ne : fs ≠ [] := by
    intro hnil
    rw [hnil, polyOfBits_nil, natDegree_zero] at hdeg_pos
    omega
  have := natDegree_polyOfBits_of_polyTrim ht hfs_ne
  omega

/-! ### Irreducibility of `Y ^ q - ζ` over `K = 𝔽₂[Z] / (f)` -/

private theorem irreducible_X_pow_sub_C_of_orderOf {q k m : ℕ} {f : (ZMod 2)[X]}
    (hq : q.Prime) (hq3 : 3 ≤ q) (hk1 : 1 ≤ k) (hirr : Irreducible f)
    (hdeg : f.natDegree = m)
    (hdvd : f ∣ cyclotomic (q ^ k) (ZMod 2))
    (hk1_ndvd : ¬ q ^ (k + 1) ∣ 2 ^ m - 1) :
    let : Fact (Irreducible f) := ⟨hirr⟩
    Irreducible (X ^ q - C (AdjoinRoot.root f)) := by
  have : Fact (Irreducible f) := ⟨hirr⟩
  set K := AdjoinRoot f
  set ζ : K := AdjoinRoot.root f
  set G : K[X] := X ^ q - C ζ
  let hpb := AdjoinRoot.powerBasis hirr.ne_zero
  have hfinK : finrank (ZMod 2) K = m := by
    rw [hpb.finrank]
    simp only [hpb, AdjoinRoot.powerBasis_dim, hdeg]
  have : Module.Finite (ZMod 2) K := hpb.finite
  have : Finite K := Module.finite_of_finite (ZMod 2)
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ m := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), ZMod.card, hfinK]
  have hndvd2 : ¬ 2 ∣ q ^ k := by
    intro ht
    have h2q : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow ht
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q
    omega
  have : NeZero ((q ^ k : ℕ) : K) := by
    refine ⟨fun h => ?_⟩
    have h0 : ((q ^ k : ℕ) : ZMod 2) = 0 :=
      (algebraMap (ZMod 2) K).injective (by rw [map_natCast, map_zero]; exact h)
    have hmod : (q ^ k : ℕ) ≡ 0 [MOD 2] :=
      (ZMod.natCast_eq_natCast_iff (q ^ k) 0 2).mp (by simpa using h0)
    exact hndvd2 (Nat.dvd_of_mod_eq_zero hmod)
  have hζ_prim : IsPrimitiveRoot ζ (q ^ k) := by
    have hroot : (cyclotomic (q ^ k) K).IsRoot ζ := by
      simpa [Polynomial.map_cyclotomic] using
        (AdjoinRoot.isRoot_root f).dvd (map_dvd (algebraMap (ZMod 2) K) hdvd)
    exact (Polynomial.isRoot_cyclotomic_iff).mp hroot
  have hζ_ord : orderOf ζ = q ^ k := hζ_prim.eq_orderOf.symm
  have hζ_ne : ζ ≠ 0 := hζ_prim.ne_zero (by positivity)
  have hG_monic : G.Monic := monic_X_pow_sub_C ζ (by omega)
  have hG_deg : G.natDegree = q := by
    dsimp only [G]
    rw [natDegree_X_pow_sub_C]
  have hG_ne : G ≠ 0 := hG_monic.ne_zero
  have hG_nu : ¬ IsUnit G := not_isUnit_of_natDegree_pos G (by rw [hG_deg]; omega)
  by_contra hnirr
  obtain ⟨g, hg_mem⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hG_ne hG_nu
  have hg_irr : Irreducible g := UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg_mem
  have hg_dvd : g ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
  have hg_deg_le : g.natDegree ≤ q := by
    rw [← hG_deg]
    exact natDegree_le_of_dvd hg_dvd hG_ne
  have hg_deg_lt : g.natDegree < q := by
    by_contra hge
    have hassoc : Associated g G :=
      associated_of_dvd_of_natDegree_le hg_dvd hG_ne (by omega)
    exact hnirr (hassoc.irreducible hg_irr)
  have hg_deg_pos : 0 < g.natDegree := hg_irr.natDegree_pos
  set d := g.natDegree
  have : Fact (Irreducible g) := ⟨hg_irr⟩
  set L₀ := AdjoinRoot g
  set θ : L₀ := AdjoinRoot.root g
  let hpb0 := AdjoinRoot.powerBasis hg_irr.ne_zero
  have hfin0 : finrank K L₀ = d := by
    rw [hpb0.finrank]
    simp only [hpb0, AdjoinRoot.powerBasis_dim]
    rfl
  have : Module.Finite K L₀ := hpb0.finite
  have hθ_pow : θ ^ q = algebraMap K L₀ ζ := by
    rcases hg_dvd with ⟨r, hr⟩
    have hev := congrArg (eval₂ (algebraMap K L₀) θ) hr
    have hg0 : g.eval₂ (algebraMap K L₀) θ = 0 := AdjoinRoot.eval₂_root g
    rw [eval₂_mul, hg0, zero_mul] at hev
    simp only [G, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hev
    exact hev
  set β : K := Algebra.norm K θ
  have hβ_pow : β ^ q = ζ ^ d := by
    rw [← map_pow, hθ_pow, Algebra.norm_algebraMap, hfin0]
  have hβ_ne : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : q ≠ 0)] at hβ_pow
    exact pow_ne_zero d hζ_ne hβ_pow.symm
  have hcop_dq : Nat.Coprime d q :=
    ((hq.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt hg_deg_pos hg_deg_lt)).symm
  obtain ⟨u, hu_lt, hu_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop_dq (by omega : 1 < q)
  set v := u * d / q
  have hud_eq : u * d = v * q + 1 := by
    have hmod_ud : (u * d) % q = 1 := by simpa [mul_comm] using hu_mod
    rw [mul_comm v q, ← hmod_ud]
    exact (Nat.div_add_mod (u * d) q).symm
  set η : K := β ^ u * (ζ ^ v)⁻¹
  have hη_ne : η ≠ 0 := mul_ne_zero (pow_ne_zero u hβ_ne) (inv_ne_zero (pow_ne_zero v hζ_ne))
  have hη_pow : η ^ q = ζ := by
    rw [mul_pow, ← pow_mul, mul_comm u q, pow_mul, hβ_pow, ← pow_mul, mul_comm d u, inv_pow,
      ← pow_mul, hud_eq, pow_add, pow_one, mul_right_comm (ζ ^ (v * q)) ζ,
      mul_inv_cancel₀ (pow_ne_zero (v * q) hζ_ne), one_mul]
  set ηu : Kˣ := Units.mk0 η hη_ne
  set ζu : Kˣ := Units.mk0 ζ hζ_ne
  have hηu_pow : ηu ^ q = ζu := Units.ext (by simp [ηu, ζu, hη_pow])
  have hζu_ord : orderOf ζu = q ^ k := by
    rw [← orderOf_injective (Units.coeHom K) Units.coeHom_injective]
    exact hζ_ord
  have hord_dvd1 : orderOf ηu ∣ q ^ (k + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_succ', pow_mul, hηu_pow, ← hζu_ord, pow_orderOf_eq_one]
  have hord_ndvd : ¬ orderOf ηu ∣ q ^ k := by
    intro hdvd_k
    have h1 : ηu ^ (q ^ k) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd_k
    have h2 : ζu ^ (q ^ (k - 1)) = 1 := by
      rw [← hηu_pow, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hk1]
      exact h1
    have hdvd_km1 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hζu_ord] at hdvd_km1
    have hle := Nat.le_of_dvd (by positivity) hdvd_km1
    have hlt := Nat.pow_lt_pow_right (by omega : 1 < q) (Nat.sub_lt hk1 zero_lt_one)
    omega
  have hord_eq : orderOf ηu = q ^ (k + 1) := by
    obtain ⟨j, hj_le, hj_eq⟩ := (Nat.dvd_prime_pow hq).mp hord_dvd1
    rw [hj_eq] at hord_ndvd ⊢
    rcases eq_or_lt_of_le hj_le with rfl | hj_lt
    · rfl
    · exfalso; exact hord_ndvd (Nat.pow_dvd_pow q (by omega))
  have hdvd_card : q ^ (k + 1) ∣ 2 ^ m - 1 := by
    have hcard_u : Fintype.card Kˣ = 2 ^ m - 1 := by
      rw [Fintype.card_units, hcardK]
    rw [← hord_eq, ← hcard_u]
    exact orderOf_dvd_card
  exact hk1_ndvd hdvd_card

/-! ### Explicit arithmetic in `L = K[Y] / (Y ^ q - Z)` and Shoup's irreducible polynomial -/

/-- Addition in `L = K[Y] / (Y ^ q - Z)`. -/
@[expose] def shoupLAdd (q : ℕ) (a b : List (List Bool)) : List (List Bool) :=
  (List.range q).map fun i => polyAdd (a.getD i []) (b.getD i [])

/-- Multiplication in `L = K[Y] / (Y ^ q - Z)` with modulus `f` for `K = 𝔽₂[Z] / (f)`. -/
@[expose] def shoupLMul (q : ℕ) (f : List Bool) (a b : List (List Bool)) : List (List Bool) :=
  (List.range q).map fun k =>
    let low := (List.range (k + 1)).foldl
      (fun acc i => polyAdd acc (polyMul (a.getD i []) (b.getD (k - i) []))) []
    let high := (List.range (q - 1 - k)).foldl
      (fun acc t =>
        let i := k + 1 + t
        polyAdd acc (polyMul (a.getD i []) (b.getD (q + k - i) []))) []
    polyMod (polyAdd low (false :: high)) f

/-- Frobenius power `a ^ (2 ^ q)` in `L = K[Y] / (Y ^ q - Z)`. -/
@[expose] def shoupLFrobQ (q : ℕ) (f : List Bool) (a : List (List Bool)) :
    List (List Bool) :=
  (fun x => shoupLMul q f x x)^[q] a

/-- Element `β = ∑_{s=0}^{m-1} Y ^ (2 ^ (s * q))` in `L`. -/
@[expose] def shoupBeta (q : ℕ) (f : List Bool) : List (List Bool) :=
  let m := f.length - 1
  let y := (List.range q).map fun i => if i == 1 then [true] else []
  ((List.range m).foldl
    (fun st _ => (shoupLAdd q st.1 st.2, shoupLFrobQ q f st.2))
    (List.replicate q [], y)).1

/-- Powers `[1, β, …, β ^ q]` in `L`. -/
@[expose] def shoupPowers (q : ℕ) (f : List Bool) (β : List (List Bool)) :
    List (List (List Bool)) :=
  let one := (List.range q).map fun i => if i == 0 then [true] else []
  ((List.range (q + 1)).foldl
    (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β)) ([], one)).1

/-- `(q * m) × (q + 1)` Boolean matrix whose columns are `[1, β, …, β ^ q]` in basis `{Z^j Y^i}`. -/
@[expose] def shoupMinPolyMatrix (q m : ℕ) (pows : List (List (List Bool))) :
    List (List Bool) :=
  (List.range (q * m)).map fun idx =>
    let i := idx / m
    let j := idx % m
    pows.map fun v => (v.getD i []).getD j false

/-- Deterministic Shoup algorithm returning an irreducible binary polynomial of degree `q`
over `𝔽₂` (for every odd prime `q`). -/
@[expose] def shoupIrreducibleBits (q : ℕ) : List Bool :=
  if q.Prime ∧ 3 ≤ q then
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    let f := shoupCyclicFactor q k
    let β := shoupBeta q f
    let pows := shoupPowers q f β
    kernelVecBits (q + 1) (shoupMinPolyMatrix q m pows)
  else []

section FieldInterpretation

private noncomputable def evalL {K L : Type*} [CommRing K] [CommRing L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) (q : ℕ)
    (v : List (List Bool)) : L :=
  ∑ i : Fin q, algebraMap K L ((polyOfBits (v.getD i.1 [])).aeval ζ) * y ^ i.1

private theorem evalL_shoupLAdd {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) (q : ℕ)
    (a b : List (List Bool)) :
    evalL ζ y q (shoupLAdd q a b) = evalL ζ y q a + evalL ζ y q b := by
  simp only [evalL, shoupLAdd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
    polyOfBits_polyAdd, map_add, map_add, add_mul]

private theorem evalL_shoupLMul {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq0 : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (a b : List (List Bool)) :
    evalL ζ y q (shoupLMul q f a b) = evalL ζ y q a * evalL ζ y q b := by
  have : NeZero q := ⟨hq0.ne'⟩
  have hmod : ∀ p : List Bool,
      (polyOfBits (polyMod p f)).aeval ζ = (polyOfBits p).aeval ζ := by
    intro p
    obtain ⟨hinv, -, -, -⟩ := polyOfBits_polyDivMod_spec (a := p) hf_ne
    have hev := congrArg (aeval ζ) hinv
    simp only [map_add, map_mul, hζ, mul_zero, zero_add] at hev
    exact hev
  have hfold_range : ∀ (n : ℕ) (g : ℕ → List Bool),
      (polyOfBits ((List.range n).foldl (fun acc x => polyAdd acc (g x)) [])).aeval ζ =
        ∑ x ∈ Finset.range n, (polyOfBits (g x)).aeval ζ := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        polyOfBits_polyAdd, map_add, ih, Finset.sum_range_succ]
  set T : ℕ → ℕ → L := fun i j =>
    algebraMap K L ((polyOfBits (polyMul (a.getD i []) (b.getD j []))).aeval ζ) * y ^ (i + j)
  have hprod : evalL ζ y q a * evalL ζ y q b = ∑ p : Fin q × Fin q, T p.1.1 p.2.1 := by
    rw [evalL, evalL, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [T, polyOfBits_polyMul, map_mul, pow_add]
    ring
  rw [hprod]
  let e : Fin q × Fin q ≃ Fin q × Fin q :=
    { toFun := fun p => (p.1, p.2 - p.1)
      invFun := fun p => (p.1, p.1 + p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.sum_comm, evalL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (shoupLMul q f a b).getD k.1 [] = _ from
    List.getD_eq_getElem _ _ (by simp [shoupLMul])]
  simp only [shoupLMul, List.getElem_map, List.getElem_range]
  rw [hmod, polyOfBits_polyAdd, map_add, polyOfBits_false_cons, map_mul, aeval_X,
    hfold_range, hfold_range, map_add, map_sum, map_mul, map_sum, add_mul,
    Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  have hadd_mod : ∀ i : Fin q, (i.1 + (k - i).1) % q = k.1 := fun i => by
    have h1 : ((k - i) + i).1 = k.1 := congrArg Fin.val (sub_add_cancel k i)
    rw [Fin.val_add, add_comm] at h1
    exact h1
  have hsub_le : ∀ i : Fin q, i.1 ≤ k.1 → (k - i).1 = k.1 - i.1 := fun i hi => by
    have hm := hadd_mod i
    by_cases hqle : i.1 + (k - i).1 < q
    · rw [Nat.mod_eq_of_lt hqle] at hm
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
  have hsub_gt : ∀ i : Fin q, ¬ i.1 ≤ k.1 → (k - i).1 = q + k.1 - i.1 := fun i hi => by
    have hm := hadd_mod i
    by_cases hqle : i.1 + (k - i).1 < q
    · rw [Nat.mod_eq_of_lt hqle] at hm
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
  have hlow_sum :
      (∑ i ∈ Finset.range (k.1 + 1),
          algebraMap K L ((polyOfBits (polyMul (a.getD i []) (b.getD (k.1 - i) []))).aeval ζ) *
            y ^ k.1) =
        ∑ i : Fin q, if i.1 ≤ k.1 then T i.1 (k - i).1 else 0 := by
    have hcongr :
        (∑ i : Fin q, if i.1 ≤ k.1 then T i.1 (k - i).1 else 0) =
          ∑ i : Fin q, if i.1 ≤ k.1 then T i.1 (k.1 - i.1) else 0 :=
      Finset.sum_congr rfl fun i _ => by
        split_ifs with hik
        · rw [hsub_le i hik]
        · rfl
    rw [hcongr, Fin.sum_univ_eq_sum_range (fun i => if i ≤ k.1 then T i (k.1 - i) else 0) q,
      ← Finset.sum_filter]
    symm
    refine Finset.sum_congr (by ext x; simp; omega) fun x hx => ?_
    have hle : x ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    simp only [T, Nat.add_sub_cancel' hle]
  have hhigh_sum :
      (∑ t ∈ Finset.range (q - 1 - k.1),
          algebraMap K L ζ * algebraMap K L
            ((polyOfBits (polyMul (a.getD (k.1 + 1 + t) [])
              (b.getD (q + k.1 - (k.1 + 1 + t)) []))).aeval ζ) * y ^ k.1) =
        ∑ i : Fin q, if ¬ i.1 ≤ k.1 then T i.1 (k - i).1 else 0 := by
    have hshift :
        (∑ t ∈ Finset.range (q - 1 - k.1),
            algebraMap K L ζ * algebraMap K L
              ((polyOfBits (polyMul (a.getD (k.1 + 1 + t) [])
                (b.getD (q + k.1 - (k.1 + 1 + t)) []))).aeval ζ) * y ^ k.1) =
          ∑ i : Fin q, if ¬ i.1 ≤ k.1 then
            algebraMap K L ((polyOfBits (polyMul (a.getD i.1 [])
              (b.getD (q + k.1 - i.1) []))).aeval ζ) * (algebraMap K L ζ * y ^ k.1)
          else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        if ¬ i ≤ k.1 then
          algebraMap K L ((polyOfBits (polyMul (a.getD i [])
            (b.getD (q + k.1 - i) []))).aeval ζ) * (algebraMap K L ζ * y ^ k.1)
        else 0) q]
      symm
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => i - (k.1 + 1)) (fun i hi => ?_) (fun a ha b hb heq => ?_)
        (fun t ht => ⟨k.1 + 1 + t, ?_⟩) (fun i hi => ?_)
      · rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_range]; omega
      · rw [Finset.mem_filter] at ha hb
        omega
      · rw [Finset.mem_range] at ht
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
      · rw [Finset.mem_filter] at hi
        rw [show k.1 + 1 + (i - (k.1 + 1)) = i by omega]
        ring
    rw [hshift]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hik
    · rfl
    · have hpow_wrap : y ^ (i.1 + (q + k.1 - i.1)) = algebraMap K L ζ * y ^ k.1 := by
        rw [show i.1 + (q + k.1 - i.1) = q + k.1 by omega, pow_add, hy]
      simp only [T, hsub_gt i hik, hpow_wrap]
  rw [hlow_sum, hhigh_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only [e]
  by_cases hik : i.1 ≤ k.1 <;> simp [hik]

private theorem evalL_shoupLFrobQ {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq0 : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (a : List (List Bool)) :
    evalL ζ y q (shoupLFrobQ q f a) = (evalL ζ y q a) ^ (2 ^ q) := by
  have hstep : ∀ s : ℕ,
      evalL ζ y q ((fun x => shoupLMul q f x x)^[s] a) = (evalL ζ y q a) ^ (2 ^ s) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Function.iterate_succ_apply', evalL_shoupLMul hq0 hf_ne hζ hy, ih, ← sq, ← pow_mul,
        ← pow_succ]
  exact hstep q

private theorem evalL_y {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) {q : ℕ} (hq : 2 ≤ q) :
    evalL ζ y q ((List.range q).map fun i => if i == 1 then [true] else []) = y := by
  rw [evalL, Finset.sum_eq_single ⟨1, by omega⟩]
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
    simp [show bitEquiv.symm true = 1 by rfl]
  · intro i _ hi
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    have hne : (i.1 == 1) = false := beq_false_of_ne (fun h => hi (Fin.ext h))
    simp [hne]
  · intro hm
    exact absurd (Finset.mem_univ (⟨1, by omega⟩ : Fin q)) hm

private theorem evalL_one {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) {q : ℕ} (hq : 0 < q) :
    evalL ζ y q ((List.range q).map fun i => if i == 0 then [true] else []) = 1 := by
  rw [evalL, Finset.sum_eq_single ⟨0, hq⟩]
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hq),
      List.getElem_map, List.getElem_range]
    simp [show bitEquiv.symm true = 1 by rfl]
  · intro i _ hi
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    have hne : (i.1 == 0) = false := beq_false_of_ne (fun h => hi (Fin.ext h))
    simp [hne]
  · intro hm
    exact absurd (Finset.mem_univ (⟨0, hq⟩ : Fin q)) hm

private theorem evalL_shoupBeta {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq : 2 ≤ q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ) :
    evalL ζ y q (shoupBeta q f) = ∑ s ∈ Finset.range (f.length - 1), y ^ (2 ^ (s * q)) := by
  set m := f.length - 1
  set yL := (List.range q).map fun i => if i == 1 then [true] else []
  have hinv : ∀ k : ℕ,
      let st := (List.range k).foldl
        (fun st _ => (shoupLAdd q st.1 st.2, shoupLFrobQ q f st.2))
        (List.replicate q [], yL)
      evalL ζ y q st.1 = (∑ s ∈ Finset.range k, y ^ (2 ^ (s * q))) ∧
        evalL ζ y q st.2 = y ^ (2 ^ (k * q)) := by
    intro k
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, zero_mul,
        pow_zero, pow_one]
      refine ⟨?_, evalL_y ζ y hq⟩
      rw [evalL]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [List.getD_eq_getElem (List.replicate q []) [] (by simp),
        List.getElem_replicate]
      simp [polyOfBits_nil]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨h1, h2⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [evalL_shoupLAdd, h1, h2, Finset.sum_range_succ]
      · rw [evalL_shoupLFrobQ (by omega) hf_ne hζ hy, h2, ← pow_mul, ← pow_add,
          Nat.succ_mul]
  exact (hinv m).1

private theorem shoupPowers_spec {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (β : List (List Bool)) :
    (shoupPowers q f β).length = q + 1 ∧
      ∀ c < q + 1, evalL ζ y q ((shoupPowers q f β).getD c []) = (evalL ζ y q β) ^ c := by
  set oneL := (List.range q).map fun i => if i == 0 then [true] else []
  have hinv : ∀ k : ℕ,
      let st := (List.range k).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β)) ([], oneL)
      st.1.length = k ∧ evalL ζ y q st.2 = (evalL ζ y q β) ^ k ∧
        ∀ c < k, evalL ζ y q (st.1.getD c []) = (evalL ζ y q β) ^ c := by
    intro k
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, List.length_nil, pow_zero]
      refine ⟨trivial, evalL_one ζ y hq, fun _ hc => by omega⟩
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only at ih ⊢
      set st := (List.range k).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β)) ([], oneL)
      obtain ⟨hlen, hcur, hprev⟩ := ih
      refine ⟨by simp [hlen], ?_, fun c hc => ?_⟩
      · rw [evalL_shoupLMul hq hf_ne hζ hy, hcur, pow_succ]
      · by_cases hck : c < k
        · rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getElem_append_left (by omega),
            ← List.getD_eq_getElem _ _ (by rw [hlen]; exact hck)]
          exact hprev c hck
        · have hce : c = k := by omega
          subst hce
          have hget_last : (st.1 ++ [st.2])[c]'(by simp [hlen]) = st.2 := by
            simp [hlen]
          rw [List.getD_eq_getElem _ _ (by simp [hlen]), hget_last, hcur]
  obtain ⟨h1, -, h3⟩ := hinv (q + 1)
  exact ⟨h1, h3⟩

private theorem shoupMinPolyMatrix_length (q m : ℕ) (pows : List (List (List Bool)))
    (hpows : pows.length = q + 1) :
    (shoupMinPolyMatrix q m pows).length = q * m ∧
      ∀ row ∈ shoupMinPolyMatrix q m pows, row.length = q + 1 := by
  refine ⟨by simp [shoupMinPolyMatrix], fun row hrow => ?_⟩
  simp only [shoupMinPolyMatrix, List.mem_map, List.mem_range] at hrow
  obtain ⟨idx, -, rfl⟩ := hrow
  simp [hpows]

private theorem two_pow_mod_pow_eq {q : ℕ} (hq : q.Prime) (s : ℕ) :
    2 ^ (s * q) % q = 2 ^ s % q := by
  have : Fact q.Prime := ⟨hq⟩
  have h2q : (2 : ZMod q) ^ q = 2 := ZMod.pow_card 2
  rw [← ZMod.natCast_eq_natCast_iff']
  calc ((2 ^ (s * q) : ℕ) : ZMod q)
      = ((2 : ZMod q) ^ q) ^ s := by rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm, pow_mul]
    _ = (2 : ZMod q) ^ s := by rw [h2q]
    _ = ((2 ^ s : ℕ) : ZMod q) := by rw [Nat.cast_pow, Nat.cast_ofNat]

private theorem dvd_of_two_pow_sub_one_dvd {d q : ℕ} (hd : 0 < d)
    (hdvd : 2 ^ d - 1 ∣ 2 ^ q - 1) : d ∣ q := by
  rw [Nat.dvd_iff_mod_eq_zero]
  set r := q % d
  set a := q / d
  have hr_lt : r < d := Nat.mod_lt q hd
  have hq_eq : q = d * a + r := (Nat.div_add_mod q d).symm
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have h2 : 2 ^ d - 1 ∣ 2 ^ (d * a) - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right d a)
  have hcong : 2 ^ q - 1 = 2 ^ r * (2 ^ (d * a) - 1) + (2 ^ r - 1) := by
    rw [hq_eq, pow_add, mul_comm (2 ^ (d * a)) (2 ^ r)]
    have hda : 1 ≤ 2 ^ (d * a) := Nat.one_le_two_pow
    have hr1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hle : 2 ^ r ≤ 2 ^ r * 2 ^ (d * a) := Nat.le_mul_of_pos_right _ hda
    rw [Nat.mul_sub, mul_one, ← Nat.add_sub_assoc hr1, Nat.sub_add_cancel hle]
  have hdvd_rem : 2 ^ d - 1 ∣ 2 ^ r - 1 := by
    rw [hcong] at hdvd
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h2 (2 ^ r))).mp hdvd
  have hlt_rem : 2 ^ r - 1 < 2 ^ d - 1 := by
    have hr1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hpow := Nat.pow_lt_pow_right one_lt_two hr_lt
    omega
  have hrem0 : 2 ^ r - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_rem hlt_rem
  have hpowr : 2 ^ r = 1 := by
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    omega
  by_contra hr0
  have hgt : 1 < 2 ^ r := Nat.one_lt_pow hr0 one_lt_two
  rw [hpowr] at hgt
  exact absurd hgt (by decide)

private theorem shoupMinPolyMatrix_getD_getD (q m : ℕ) (pows : List (List (List Bool)))
    {idx c : ℕ} (hidx : idx < q * m) (hc : c < pows.length) :
    ((shoupMinPolyMatrix q m pows).getD idx []).getD c false =
      ((pows.getD c []).getD (idx / m) []).getD (idx % m) false := by
  rw [shoupMinPolyMatrix]
  set rows := (List.range (q * m)).map fun i =>
    pows.map fun p => (p.getD (i / m) []).getD (i % m) false
  have hrows : rows.length = q * m := by simp [rows]
  rw [List.getD_eq_getElem rows [] (by omega)]
  dsimp only [rows]
  rw [List.getElem_map, List.getElem_range]
  set row := pows.map fun p => (p.getD (idx / m) []).getD (idx % m) false
  have hrow : row.length = pows.length := by simp [row]
  rw [List.getD_eq_getElem row false (by omega)]
  dsimp only [row]
  rw [List.getElem_map, ← List.getD_eq_getElem pows [] hc]

private theorem shoupMinPolyMatrix_mulVec_zero_iff {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] [Algebra (ZMod 2) L] [IsScalarTower (ZMod 2) K L]
    {q m : ℕ} (hm0 : 0 < m) (ζ : K) (y βL : L)
    (pbK : PowerBasis (ZMod 2) K) (pbL : PowerBasis K L)
    (hpbK_dim : pbK.dim = m) (hpbL_dim : pbL.dim = q)
    (hpbK_coe : ∀ idx : Fin pbK.dim, pbK.basis idx = ζ ^ idx.1)
    (hpbL_coe : ∀ idx : Fin pbL.dim, pbL.basis idx = y ^ idx.1)
    (pows : List (List (List Bool))) (hpows_len : pows.length = q + 1)
    (hpows_eval : ∀ c < q + 1, evalL ζ y q (pows.getD c []) = βL ^ c)
    (hpows_entry_len : ∀ c < q + 1, ∀ i < q, ((pows.getD c []).getD i []).length ≤ m)
    (v : Fin (q + 1) → ZMod 2) :
    rowsToZModMatrix (q * m) (q + 1) (shoupMinPolyMatrix q m pows) *ᵥ v = 0 ↔
      ∑ c : Fin (q + 1), v c • βL ^ c.1 = 0 := by
  have heq_sum :
      (∑ c : Fin (q + 1), v c • βL ^ c.1) =
        ∑ i : Fin q, algebraMap K L (∑ j : Fin m,
          (∑ c : Fin (q + 1), v c *
            bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)) • ζ ^ j.1) *
          y ^ i.1 := by
    have hc_expand : ∀ c : Fin (q + 1),
        v c • βL ^ c.1 =
          ∑ i : Fin q, algebraMap K L (∑ j : Fin m,
            (v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)) •
              ζ ^ j.1) * y ^ i.1 := by
      intro c
      rw [← hpows_eval c.1 c.2, evalL, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_mul_assoc, Algebra.smul_def (R := ZMod 2),
        IsScalarTower.algebraMap_apply (ZMod 2) K L, ← map_mul,
        ← Algebra.smul_def (R := ZMod 2)]
      refine congrArg (· * y ^ i.1) (congrArg (algebraMap K L) ?_)
      rw [aeval_polyOfBits, Finset.smul_sum]
      trans ∑ j ∈ Finset.range m,
          (v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j false)) • ζ ^ j
      · rw [← Finset.sum_subset (Finset.range_mono (hpows_entry_len c.1 c.2 i.1 i.2))]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]
        · intro j _ hj
          rw [Finset.mem_range, not_lt] at hj
          rw [List.getD_eq_default _ _ hj, bitEquiv_symm_false, mul_zero, zero_smul]
      · rw [Fin.sum_univ_eq_sum_range (fun j =>
          (v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j false)) • ζ ^ j) m]
    simp_rw [hc_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    refine congrArg (· * y ^ i.1) ?_
    rw [← map_sum, Finset.sum_comm]
    refine congrArg (algebraMap K L) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
  rw [heq_sum]
  have hliL := pbL.basis.linearIndependent
  have hliK := pbK.basis.linearIndependent
  have hvanish :
      (∑ i : Fin q, algebraMap K L (∑ j : Fin m,
          (∑ c : Fin (q + 1), v c *
            bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)) • ζ ^ j.1) *
          y ^ i.1 = 0) ↔
        ∀ (i : Fin q) (j : Fin m),
          (∑ c : Fin (q + 1), v c *
            bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)) = 0 := by
    constructor
    · intro h0 i j
      set coeffK : Fin pbL.dim → K := fun idx =>
        ∑ j' : Fin m, (∑ c : Fin (q + 1), v c *
          bitEquiv.symm (((pows.getD c.1 []).getD idx.1 []).getD j'.1 false)) • ζ ^ j'.1
      have h0' : ∑ idx : Fin pbL.dim, coeffK idx • pbL.basis idx = 0 := by
        rw [← h0]
        have hpb_rw :
            (∑ idx : Fin pbL.dim, coeffK idx • pbL.basis idx) =
              ∑ idx : Fin pbL.dim, algebraMap K L (∑ j' : Fin m,
                (∑ c : Fin (q + 1), v c *
                  bitEquiv.symm (((pows.getD c.1 []).getD idx.1 []).getD j'.1 false)) •
                    ζ ^ j'.1) *
                y ^ idx.1 :=
          Finset.sum_congr rfl fun idx _ => by rw [Algebra.smul_def, hpbL_coe idx]
        rw [hpb_rw]
        exact sum_fin_cast hpbL_dim fun idx => algebraMap K L (∑ j' : Fin m,
          (∑ c : Fin (q + 1), v c *
            bitEquiv.symm (((pows.getD c.1 []).getD idx []).getD j'.1 false)) • ζ ^ j'.1) *
          y ^ idx
      have hci := (linearIndependent_iff'.mp hliL Finset.univ coeffK h0')
        (Fin.cast hpbL_dim.symm i) (Finset.mem_univ _)
      set coeffZ : Fin pbK.dim → ZMod 2 := fun jidx =>
        ∑ c : Fin (q + 1), v c *
          bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD jidx.1 false)
      have hci' : ∑ jidx : Fin pbK.dim, coeffZ jidx • pbK.basis jidx = 0 := by
        rw [← hci]
        have hpbk_rw :
            (∑ jidx : Fin pbK.dim, coeffZ jidx • pbK.basis jidx) =
              ∑ jidx : Fin pbK.dim, (∑ c : Fin (q + 1), v c *
                bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD jidx.1 false)) •
                  ζ ^ jidx.1 :=
          Finset.sum_congr rfl fun jidx _ => by rw [hpbK_coe jidx]
        rw [hpbk_rw]
        exact sum_fin_cast hpbK_dim fun jidx => (∑ c : Fin (q + 1), v c *
          bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD jidx false)) • ζ ^ jidx
      exact (linearIndependent_iff'.mp hliK Finset.univ coeffZ hci')
        (Fin.cast hpbK_dim.symm j) (Finset.mem_univ _)
    · intro hall
      exact Finset.sum_eq_zero fun i _ => by
        rw [Finset.sum_eq_zero fun j _ => by rw [hall i j, zero_smul], map_zero, zero_mul]
  rw [hvanish]
  constructor
  · intro hmul i j
    have hidx : i.1 * m + j.1 < q * m := by nlinarith [i.2, j.2]
    have hrow := congrFun hmul ⟨i.1 * m + j.1, hidx⟩
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow
    rw [← hrow]
    refine Finset.sum_congr rfl fun c _ => ?_
    dsimp only [rowsToZModMatrix, bitsToZModVec]
    rw [shoupMinPolyMatrix_getD_getD q m pows hidx (by rw [hpows_len]; exact c.2)]
    have hdiv : (i.1 * m + j.1) / m = i.1 := by
      rw [mul_comm, Nat.mul_add_div hm0, Nat.div_eq_of_lt j.2, add_zero]
    have hmod : (i.1 * m + j.1) % m = j.1 := by
      rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
    rw [hdiv, hmod, mul_comm]
  · intro hall
    funext idx
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    have hi_lt : idx.1 / m < q := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.2 (mul_comm q m))
    have hj_lt : idx.1 % m < m := Nat.mod_lt _ hm0
    have hall' := hall ⟨idx.1 / m, hi_lt⟩ ⟨idx.1 % m, hj_lt⟩
    rw [← hall']
    refine Finset.sum_congr rfl fun c _ => ?_
    dsimp only [rowsToZModMatrix, bitsToZModVec]
    rw [shoupMinPolyMatrix_getD_getD q m pows idx.2 (by rw [hpows_len]; exact c.2), mul_comm]

private theorem shoupBeta_minpoly_natDegree {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] [Algebra (ZMod 2) L] [IsScalarTower (ZMod 2) K L]
    [Module.Finite (ZMod 2) L] [CharP L 2]
    {q m : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hm2 : 2 ≤ m)
    (hm_min : ∀ j, 0 < j → j < m → 2 ^ j % q ≠ 1)
    (ζ : K) (y : L) (f : List Bool) (hf_ne : polyOfBits f ≠ 0) (hf_len : f.length = m + 1)
    (hζ_root : (polyOfBits f).aeval ζ = 0) (hy_pow : y ^ q = algebraMap K L ζ)
    (hy_card : y ^ (2 ^ (m * q)) = y)
    (pbL : PowerBasis K L) (hpbL_dim : pbL.dim = q)
    (hpbL_coe : ∀ idx : Fin pbL.dim, pbL.basis idx = y ^ idx.1) :
    let βL : L := evalL ζ y q (shoupBeta q f)
    (∀ a : ZMod 2, βL ≠ algebraMap (ZMod 2) L a) ∧ (minpoly (ZMod 2) βL).natDegree = q := by
  set βbits := shoupBeta q f
  set βL : L := evalL ζ y q βbits
  have hβL_eq : βL = ∑ s ∈ Finset.range m, y ^ (2 ^ (s * q)) := by
    have hmlen : f.length - 1 = m := by rw [hf_len]; omega
    dsimp only [βL, βbits]
    rw [evalL_shoupBeta (by omega : 2 ≤ q) hf_ne hζ_root hy_pow, hmlen]
  have hβ_frob : βL ^ (2 ^ q) = βL := by
    rw [hβL_eq]
    have hpow_sum_n : ∀ n : ℕ, (∑ s ∈ Finset.range n, y ^ (2 ^ (s * q))) ^ (2 ^ q) =
        ∑ s ∈ Finset.range n, (y ^ (2 ^ (s * q))) ^ (2 ^ q) := fun n => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, add_pow_char_pow _ _ 2 q, ih, Finset.sum_range_succ]
    rw [hpow_sum_n m]
    have hm1 : 1 ≤ m := by omega
    rw [← Nat.sub_add_cancel hm1, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [zero_mul, pow_zero, pow_one, add_comm]
    congr 1
    · rw [← pow_mul, ← pow_add, show (m - 1) * q + q = m * q by
          calc (m - 1) * q + q = (m - 1 + 1) * q := by ring
            _ = m * q := by rw [Nat.sub_add_cancel hm1], hy_card]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [← pow_mul, ← pow_add, Nat.succ_mul]
  have hβ_notin : ∀ a : ZMod 2, βL ≠ algebraMap (ZMod 2) L a := by
    intro a heq
    set pbLB := pbL.basis
    have hcoeff_sum :
        ∀ (u : Fin q → K),
          pbLB.repr (∑ i : Fin q, algebraMap K L (u i) * y ^ i.1) ⟨1, by rw [hpbL_dim]; omega⟩ =
            u ⟨1, by omega⟩ := by
      intro u
      have heq' : (∑ i : Fin q, algebraMap K L (u i) * y ^ i.1) =
          ∑ i : Fin q, u i • pbLB (⟨i.1, by rw [hpbL_dim]; exact i.2⟩ : Fin pbL.dim) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, hpbL_coe]
      have hrepr :
          (∑ i : Fin q, u i • pbLB (⟨i.1, by rw [hpbL_dim]; exact i.2⟩ : Fin pbL.dim)) =
            ∑ j : Fin pbL.dim,
              u (⟨j.1, by rw [← hpbL_dim]; exact j.2⟩ : Fin q) • pbLB j :=
        Equiv.sum_comp
          { toFun := Fin.cast hpbL_dim.symm
            invFun := Fin.cast hpbL_dim
            left_inv := fun _ => Fin.ext rfl
            right_inv := fun _ => Fin.ext rfl }
          (fun j : Fin pbL.dim =>
            u (⟨j.1, by rw [← hpbL_dim]; exact j.2⟩ : Fin q) • pbLB j)
      have hlin : pbLB.repr (∑ j : Fin pbL.dim,
            u (⟨j.1, by rw [← hpbL_dim]; exact j.2⟩ : Fin q) • pbLB j) =
          ∑ j : Fin pbL.dim,
            u (⟨j.1, by rw [← hpbL_dim]; exact j.2⟩ : Fin q) • Finsupp.single j (1 : K) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Basis.repr_self]
      rw [heq', hrepr, hlin]
      change (Finsupp.applyAddHom (⟨1, by rw [hpbL_dim]; omega⟩ : Fin pbL.dim))
        (∑ j : Fin pbL.dim,
          u (⟨j.1, by rw [← hpbL_dim]; exact j.2⟩ : Fin q) • Finsupp.single j (1 : K)) = _
      rw [map_sum, Finset.sum_eq_single ⟨1, by rw [hpbL_dim]; omega⟩]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    have hy_decomp : ∀ s ∈ Finset.range m,
        y ^ (2 ^ (s * q)) =
          algebraMap K L (ζ ^ (2 ^ (s * q) / q)) *
            y ^ (2 ^ (s * q) % q) := by
      intro s _
      have hdiv := Nat.div_add_mod (2 ^ (s * q)) q
      nth_rw 1 [← hdiv]
      rw [pow_add, pow_mul, hy_pow, map_pow]
    have hLHS :
        pbLB.repr βL ⟨1, by rw [hpbL_dim]; omega⟩ = 1 := by
      have hβ_vec : βL = ∑ i : Fin q,
          algebraMap K L (∑ s ∈ Finset.range m,
            if 2 ^ (s * q) % q = i.1 then ζ ^ (2 ^ (s * q) / q) else 0) * y ^ i.1 := by
        rw [hβL_eq]
        trans ∑ s ∈ Finset.range m, ∑ i : Fin q,
            if 2 ^ (s * q) % q = i.1 then
              algebraMap K L (ζ ^ (2 ^ (s * q) / q)) * y ^ i.1
            else 0
        · refine Finset.sum_congr rfl fun s hs => ?_
          rw [hy_decomp s hs, Finset.sum_eq_single ⟨2 ^ (s * q) % q, Nat.mod_lt _ (by omega)⟩]
          · simp
          · intro i _ hi
            have hne : 2 ^ (s * q) % q ≠ i.1 := fun h => hi (Fin.ext h.symm)
            simp [hne]
          · intro hm
            exact absurd (Finset.mem_univ _) hm
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs <;> simp [map_zero]
      have hpick := hcoeff_sum (fun i : Fin q =>
        ∑ s ∈ Finset.range m, if 2 ^ (s * q) % q = i.1 then ζ ^ (2 ^ (s * q) / q) else 0)
      have hres : pbLB.repr βL ⟨1, by rw [hpbL_dim]; omega⟩ =
          ∑ s ∈ Finset.range m, if 2 ^ (s * q) % q = 1 then ζ ^ (2 ^ (s * q) / q) else 0 := by
        rw [hβ_vec]
        simpa [pbLB] using hpick
      rw [hres, Finset.sum_eq_single 0]
      · simp [Nat.mod_eq_of_lt (by omega : 1 < q), Nat.div_eq_of_lt (by omega : 1 < q)]
      · intro s hs hs0
        rw [Finset.mem_range] at hs
        rw [two_pow_mod_pow_eq hq s]
        have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
        simp [hm_min s hs_pos hs]
      · intro hm
        exact absurd (Finset.mem_range.mpr (by omega : 0 < m)) hm
    have hRHS :
        pbLB.repr (algebraMap (ZMod 2) L a) ⟨1, by rw [hpbL_dim]; omega⟩ = 0 := by
      have ha_eq : algebraMap (ZMod 2) L a =
          ∑ i : Fin q,
            algebraMap K L (if i.1 = 0 then algebraMap (ZMod 2) K a else 0) * y ^ i.1 := by
        rw [Finset.sum_eq_single ⟨0, by omega⟩]
        · simp [IsScalarTower.algebraMap_apply (ZMod 2) K L]
        · intro i _ hi
          have hne : i.1 ≠ 0 := fun h => hi (Fin.ext h)
          simp [hne]
        · intro hm
          exact absurd (Finset.mem_univ _) hm
      rw [ha_eq]
      have := hcoeff_sum (fun i : Fin q => if i.1 = 0 then algebraMap (ZMod 2) K a else 0)
      simpa [pbLB] using this
    rw [heq] at hLHS
    rw [hRHS] at hLHS
    exact one_ne_zero hLHS.symm
  have hβ_int : IsIntegral (ZMod 2) βL := IsIntegral.of_finite (ZMod 2) βL
  refine ⟨hβ_notin, ?_⟩
  let E := IntermediateField.adjoin (ZMod 2) ({βL} : Set L)
  set d := (minpoly (ZMod 2) βL).natDegree
  have hd_pos : 0 < d := minpoly.natDegree_pos hβ_int
  have hd_fin : finrank (ZMod 2) E = d := IntermediateField.adjoin.finrank hβ_int
  have : Module.Finite (ZMod 2) E := FiniteDimensional.of_finrank_pos (by omega)
  have : Finite E := Module.finite_of_finite (ZMod 2)
  classical
  let : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 2 ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := E), ZMod.card, hd_fin]
  let S_if : IntermediateField (ZMod 2) L :=
    { carrier := {x : L | x ^ (2 ^ q) = x}
      mul_mem' := fun hx hy => by
        change (_ * _) ^ _ = _
        rw [mul_pow, hx, hy]
      one_mem' := one_pow _
      add_mem' := fun hx hy => by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        change (_ + _) ^ _ = _
        rw [add_pow_char_pow _ _ 2 q, hx, hy]
      zero_mem' := zero_pow (by positivity)
      algebraMap_mem' := fun c => by
        change (algebraMap (ZMod 2) L c) ^ (2 ^ q) = _
        rw [← map_pow]
        congr 1
        fin_cases c
        · exact zero_pow (Nat.ne_of_gt (pow_pos two_pos q))
        · exact one_pow _
      inv_mem' := fun {x} hx => by
        change (x⁻¹) ^ (2 ^ q) = x⁻¹
        rw [inv_pow, hx] }
  have hE_le : E ≤ S_if :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_frob)
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hw_ord : orderOf w = 2 ^ d - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card,
      Fintype.card_units, hcardE]
  have hw_frob : (w : L) ^ (2 ^ q) = (w : L) := hE_le (w : E).2
  have hw_pow_sub : w ^ (2 ^ q - 1) = 1 := by
    apply Units.ext
    apply Subtype.ext
    have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hmul : (w : L) * (w : L) ^ (2 ^ q - 1) = (w : L) * 1 := by
      calc (w : L) * (w : L) ^ (2 ^ q - 1)
          = (w : L) ^ (1 + (2 ^ q - 1)) := by rw [pow_add, pow_one]
        _ = (w : L) ^ (2 ^ q) := by rw [Nat.add_sub_cancel' h1]
        _ = (w : L) := hw_frob
        _ = (w : L) * 1 := (mul_one _).symm
    exact mul_left_cancel₀ (fun h0 => w.ne_zero (Subtype.ext h0)) hmul
  have hdvd_pow : 2 ^ d - 1 ∣ 2 ^ q - 1 := by
    rw [← hw_ord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hw_pow_sub
  have hd_dvd_q : d ∣ q := dvd_of_two_pow_sub_one_dvd hd_pos hdvd_pow
  rcases hq.eq_one_or_self_of_dvd d hd_dvd_q with h1 | hq_eq
  · obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact absurd hc.symm (hβ_notin c)
  · exact hq_eq

private theorem shoupPowers_entry_length {q m : ℕ} (hm1 : 1 ≤ m) (f : List Bool)
    (hf_trim : polyTrim f = f) (hf_len : f.length = m + 1) (hf_ne : polyOfBits f ≠ 0)
    (β : List (List Bool)) :
    ∀ c < q + 1, ∀ i < q, (((shoupPowers q f β).getD c []).getD i []).length ≤ m := by
  have hshoupMul_len : ∀ a b, ∀ i < q, ((shoupLMul q f a b).getD i []).length ≤ m := by
    intro a b i hi
    dsimp only [shoupLMul]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
      List.getElem_map, List.getElem_range]
    obtain ⟨-, hlt, -, -⟩ := polyOfBits_polyDivMod_spec
      (a := polyAdd
        ((List.range (i + 1)).foldl
          (fun acc i_1 => polyAdd acc (polyMul (a.getD i_1 []) (b.getD (i - i_1) []))) [])
        (false :: (List.range (q - 1 - i)).foldl
          (fun acc t =>
            polyAdd acc (polyMul (a.getD (i + 1 + t) []) (b.getD (q + i - (i + 1 + t)) [])))
          []))
      hf_ne
    rw [hf_trim, hf_len] at hlt
    exact Nat.lt_succ_iff.mp hlt
  have hinv_len : ∀ n : ℕ,
      let st := (List.range n).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β))
        ([], (List.range q).map fun i => if i == 0 then [true] else [])
      (∀ i < q, (st.2.getD i []).length ≤ m) ∧
        (∀ c < st.1.length, ∀ i < q, ((st.1.getD c []).getD i []).length ≤ m) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i hi => ?_, fun c hc => by simp at hc⟩
      simp only [List.range_zero, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
        List.getElem_map, List.getElem_range]
      split_ifs <;> (simp; try omega)
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only at ih ⊢
      set st := (List.range n).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β))
        ([], (List.range q).map fun i => if i == 0 then [true] else [])
      obtain ⟨hcur, hprev⟩ := ih
      refine ⟨fun i hi => hshoupMul_len _ _ i hi, fun c hc i hi => ?_⟩
      simp only [List.length_append, List.length_singleton] at hc
      by_cases hcn : c < st.1.length
      · rw [List.getD_eq_getElem (st.1 ++ [st.2]) [] (by simp; omega),
          List.getElem_append_left hcn, ← List.getD_eq_getElem _ _ hcn]
        exact hprev c hcn i hi
      · have hce : c = st.1.length := by omega
        subst hce
        rw [List.getD_eq_getElem (st.1 ++ [st.2]) [] (by simp),
          List.getElem_append_right (le_refl st.1.length)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        exact hcur i hi
  intro c hc i hi
  have hpows_len : (shoupPowers q f β).length = q + 1 := by
    unfold shoupPowers
    have hfst : ∀ n : ℕ, ((List.range n).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β))
        ([], (List.range q).map fun i => if i == 0 then [true] else [])).1.length = n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih' =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.length_append, List.length_singleton, ih']
    exact hfst (q + 1)
  have hlen : c <
      ((List.range (q + 1)).foldl
        (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β))
        ([], (List.range q).map fun i => if i == 0 then [true] else [])).1.length := by
    change c < (shoupPowers q f β).length
    rw [hpows_len]
    exact hc
  exact (hinv_len (q + 1)).2 c hlen i hi

/-- Correctness of Shoup's deterministic algorithm: `shoupIrreducibleBits q` is trimmed and
represents an irreducible binary polynomial of degree `q`. -/
theorem shoupIrreducibleBits_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    Irreducible (polyOfBits (shoupIrreducibleBits q)) ∧
      (polyOfBits (shoupIrreducibleBits q)).natDegree = q ∧
      polyTrim (shoupIrreducibleBits q) = shoupIrreducibleBits q ∧
      (shoupIrreducibleBits q).length = q + 1 := by
  set m := ordTwoMod q
  set k := qAdicValTwoPowSubOne q m
  set f := shoupCyclicFactor q k
  obtain ⟨hm2, hmq, -, hm_min, -⟩ := ordTwoMod_spec hq hq3
  obtain ⟨hk1, -, hk_dvd, hk1_ndvd⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨hf_trim, hf_cyc, hf_irr, hf_deg, hf_len⟩ := shoupCyclicFactor_spec hq hq3
  have : Fact (Irreducible (polyOfBits f)) := ⟨hf_irr⟩
  set K := AdjoinRoot (polyOfBits f)
  set ζ : K := AdjoinRoot.root (polyOfBits f)
  set G : K[X] := X ^ q - C ζ
  have hG_irr : Irreducible G :=
    irreducible_X_pow_sub_C_of_orderOf hq hq3 hk1 hf_irr hf_deg hf_cyc hk1_ndvd
  have : Fact (Irreducible G) := ⟨hG_irr⟩
  set L := AdjoinRoot G
  set y : L := AdjoinRoot.root G
  have : IsScalarTower (ZMod 2) K L := inferInstance
  let pbK := AdjoinRoot.powerBasis hf_irr.ne_zero
  let pbL := AdjoinRoot.powerBasis hG_irr.ne_zero
  have hpbK_dim : pbK.dim = m := by
    rw [AdjoinRoot.powerBasis_dim]
    exact hf_deg
  have hG_deg : G.natDegree = q := by
    dsimp only [G]
    rw [natDegree_X_pow_sub_C]
  have hpbL_dim : pbL.dim = q := by
    simp only [pbL, AdjoinRoot.powerBasis_dim, hG_deg]
  have hfinK : finrank (ZMod 2) K = m := by rw [pbK.finrank, hpbK_dim]
  have hfinKL : finrank K L = q := by rw [pbL.finrank, hpbL_dim]
  have : Module.Finite (ZMod 2) K := pbK.finite
  have : Module.Finite K L := pbL.finite
  have : Module.Finite (ZMod 2) L := Module.Finite.trans K L
  have hfinL : finrank (ZMod 2) L = m * q := by
    rw [← Module.finrank_mul_finrank (ZMod 2) K L, hfinK, hfinKL]
  have : Finite L := Module.finite_of_finite (ZMod 2)
  let : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = 2 ^ (m * q) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := L), ZMod.card, hfinL]
  have hcharL : CharP L 2 := ⟨fun n => by
    rw [← map_natCast (algebraMap (ZMod 2) L), ← map_zero (algebraMap (ZMod 2) L),
      (algebraMap (ZMod 2) L).injective.eq_iff, CharP.cast_eq_zero_iff (ZMod 2) 2 n]⟩
  have hζ_root : (polyOfBits f).aeval ζ = 0 := by
    rw [show ζ = AdjoinRoot.root (polyOfBits f) from rfl, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self]
  have hy_pow : y ^ q = algebraMap K L ζ := by
    have hy0 := AdjoinRoot.eval₂_root G
    simp only [G, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hy0
    exact hy0
  set βbits := shoupBeta q f
  set βL : L := evalL ζ y q βbits
  have hy_card : y ^ (2 ^ (m * q)) = y := by
    rw [← hcardL]
    exact FiniteField.pow_card y
  have hmin_deg : (minpoly (ZMod 2) βL).natDegree = q :=
    (shoupBeta_minpoly_natDegree hq hq3 hm2 hm_min ζ y f hf_irr.ne_zero hf_len
      hζ_root hy_pow hy_card pbL hpbL_dim
      (fun idx => by rw [pbL.coe_basis, AdjoinRoot.powerBasis_gen])).2
  set pows := shoupPowers q f βbits
  obtain ⟨hpows_len, hpows_eval⟩ :=
    shoupPowers_spec (by omega : 0 < q) hf_irr.ne_zero hζ_root hy_pow βbits
  have hpows_entry_len : ∀ c < q + 1, ∀ i < q,
      ((pows.getD c []).getD i []).length ≤ m :=
    shoupPowers_entry_length (by omega : 1 ≤ m) f hf_trim hf_len hf_irr.ne_zero βbits
  set M := shoupMinPolyMatrix q m pows
  obtain ⟨hM_len, hM_mem⟩ := shoupMinPolyMatrix_length q m pows hpows_len
  have hmul_iff : ∀ v : Fin (q + 1) → ZMod 2,
      rowsToZModMatrix (q * m) (q + 1) M *ᵥ v = 0 ↔
        ∑ c : Fin (q + 1), v c • βL ^ c.1 = 0 :=
    shoupMinPolyMatrix_mulVec_zero_iff (by omega) ζ y βL pbK pbL hpbK_dim hpbL_dim
      (fun idx => by rw [pbK.coe_basis, AdjoinRoot.powerBasis_gen])
      (fun idx => by rw [pbL.coe_basis, AdjoinRoot.powerBasis_gen])
      pows hpows_len hpows_eval hpows_entry_len
  have hβ_int : IsIntegral (ZMod 2) βL := IsIntegral.of_finite (ZMod 2) βL
  set P := minpoly (ZMod 2) βL
  have hP_irr : Irreducible P := minpoly.irreducible hβ_int
  have hP_monic : P.Monic := minpoly.monic hβ_int
  let v0 : Fin (q + 1) → ZMod 2 := fun c => P.coeff c.1
  have hv0_ne : v0 ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨q, Nat.lt_succ_self q⟩
    simp only [v0, Pi.zero_apply, ← hmin_deg, hP_monic.coeff_natDegree] at this
    exact one_ne_zero this
  have hv0_mul : rowsToZModMatrix (q * m) (q + 1) M *ᵥ v0 = 0 := by
    rw [hmul_iff]
    have hev := minpoly.aeval (ZMod 2) βL
    change aeval βL P = 0 at hev
    rw [aeval_def, eval₂_eq_sum_range, hmin_deg, ← Fin.sum_univ_eq_sum_range] at hev
    convert hev using 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def]
  set kv := shoupIrreducibleBits q
  have hkv_eq : kv = kernelVecBits (q + 1) M := by
    change shoupIrreducibleBits q = kernelVecBits (q + 1) M
    simp only [shoupIrreducibleBits, hq, hq3, and_self, ↓reduceIte]
    rfl
  have hkv_any : kv.any id = true := by
    rw [hkv_eq]
    exact kernelVecBits_any_of_exists M hM_len hM_mem ⟨v0, hv0_ne, hv0_mul⟩
  have hkv_len : kv.length = q + 1 := by
    rw [hkv_eq]
    exact length_kernelVecBits (q + 1) M
  have hkv_ne0 : polyOfBits kv ≠ 0 := by
    rw [Ne, polyOfBits_eq_zero_iff]
    intro hall
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.mp hkv_any
    have : b = true := by simpa using hb'
    subst this
    exact Bool.true_eq_false.mp (hall true hb)
  have hkv_mul : rowsToZModMatrix (q * m) (q + 1) M *ᵥ bitsToZModVec (q + 1) kv = 0 := by
    rw [hkv_eq]
    exact mulVec_kernelVecBits M hM_len hM_mem
  have hkv_eval : (polyOfBits kv).aeval βL = 0 := by
    have hsum := (hmul_iff _).mp hkv_mul
    rw [aeval_polyOfBits, hkv_len, ← Fin.sum_univ_eq_sum_range]
    exact hsum
  have hP_dvd : P ∣ polyOfBits kv := minpoly.dvd (ZMod 2) βL hkv_eval
  have hkv_deg_le : (polyOfBits kv).natDegree ≤ q := by
    have hlt := degree_polyOfBits_lt kv
    rw [degree_eq_natDegree hkv_ne0, Nat.cast_lt] at hlt
    omega
  have hassoc : Associated P (polyOfBits kv) :=
    associated_of_dvd_of_natDegree_le hP_dvd hkv_ne0 (by rw [hmin_deg]; exact hkv_deg_le)
  have hkv_monic : (polyOfBits kv).Monic := by
    have hlc0 : (polyOfBits kv).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hkv_ne0
    rw [Polynomial.Monic, ← bitEquiv.symm_apply_apply (polyOfBits kv).leadingCoeff]
    cases hb : bitEquiv (polyOfBits kv).leadingCoeff
    · exfalso
      apply hlc0
      rw [← bitEquiv.symm_apply_apply (polyOfBits kv).leadingCoeff, hb]
      exact map_zero _
    · exact map_one _
  have hpoly_eq : polyOfBits kv = P := (eq_of_monic_of_associated hP_monic hkv_monic hassoc).symm
  have hkv_coeff_q : kv.getD q false = true := by
    have hcq : (polyOfBits kv).coeff q = 1 := by
      rw [hpoly_eq, ← hmin_deg, hP_monic.coeff_natDegree]
    rw [coeff_polyOfBits] at hcq
    cases hqb : kv.getD q false
    · rw [hqb, bitEquiv_symm_false] at hcq
      exact absurd hcq zero_ne_one
    · rfl
  have hkv_trim : polyTrim kv = kv := by
    have hdrop : kv = kv.dropLast ++ [true] := by
      have hne : kv ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hlast : kv.getLast hne = true := by
        rw [List.getLast_eq_getElem, ← List.getD_eq_getElem kv false (by omega)]
        simpa [hkv_len] using hkv_coeff_q
      conv_lhs => rw [← List.dropLast_append_getLast hne, hlast]
    rw [hdrop]
    exact polyTrim_append_true _
  refine ⟨?_, ?_, hkv_trim, hkv_len⟩
  · rw [hpoly_eq]; exact hP_irr
  · rw [hpoly_eq]; exact hmin_deg

end FieldInterpretation

/-- `polyOfBits (shoupIrreducibleBits q)` is irreducible for any odd prime `q`. -/
theorem irreducible_polyOfBits_shoupIrreducibleBits {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    Irreducible (polyOfBits (shoupIrreducibleBits q)) :=
  (shoupIrreducibleBits_spec hq hq3).1

/-- `(polyOfBits (shoupIrreducibleBits q)).natDegree = q` for any odd prime `q`. -/
theorem natDegree_polyOfBits_shoupIrreducibleBits {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (polyOfBits (shoupIrreducibleBits q)).natDegree = q :=
  (shoupIrreducibleBits_spec hq hq3).2.1

/-! ### Single-prime multiplication table and `O(N ^ (4 / 5))` affine disperser -/

/-- Symmetric-polynomial degree `t = max 1 ⌊N ^ (1 / 5)⌋` for the single-prime disperser. -/
@[expose] def primeSymDeg (N : ℕ) : ℕ := max 1 (fifthRoot N)

/-- Power-basis multiplication table for `𝔽₂[X] / (g)` (`q = g.length - 1`). Entry `(u, v)` stores
the reduced bit-list of `X ^ (u + v) mod g`. -/
@[expose] def primeMulTable (g : List Bool) : List (List (List Bool)) :=
  let q := g.length - 1
  let tab := powerTable g
  (List.range q).map fun u =>
    (List.range q).map fun v =>
      tab.getD (u + v) []

/-- Raw-bit evaluator for `primeDisperser` on a bit list of length `N`. -/
@[expose] def primeDisperserBits (N : ℕ) (x : List Bool) : Bool :=
  let q := primeDeg N
  let g := shoupIrreducibleBits q
  traceSymCoords (primeMulTable g) (N / q) (primeSymDeg N) x

/-- Unconditional explicit affine disperser for dimension `O(N ^ (4 / 5))`, evaluating
Ben-Sasson and Kopparty's `traceSym 1 r t` over `𝔽_{2 ^ q}` (`q = primeDeg N ≈ N ^ (3 / 5)`). -/
@[expose] def primeDisperser (N : ℕ) (x : BitString N) : Bool :=
  primeDisperserBits N (List.ofFn x)

/-- Explicit dimension threshold (`primeThreshold N + 1 = O(N ^ (4 / 5))`) at which
`primeDisperser N` is guaranteed to be an affine disperser. -/
@[expose] def primeThreshold (N : ℕ) : ℕ :=
  let q := primeDeg N
  let r := N / q
  let t := primeSymDeg N
  (N - r * q) + (r * (r + 1) + r * (r + 1) + q * t + q * r / t)

private theorem getLast_of_polyTrim_eq_self {g : List Bool} (ht : polyTrim g = g)
    (hne : g ≠ []) : g.getLast hne = true := by
  by_contra hnt
  have hf : g.getLast hne = false := Bool.eq_false_iff.mpr hnt
  have hdrop : g = g.dropLast ++ [false] := by
    conv_lhs => rw [← List.dropLast_append_getLast hne, hf]
  have hlen : (polyTrim g).length ≤ g.dropLast.length := by
    nth_rw 1 [hdrop]
    rw [polyTrim, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Bool.false_or, List.isEmpty_nil,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← polyTrim]
    exact length_polyTrim_le _
  rw [ht, List.length_dropLast] at hlen
  have := List.length_pos_of_ne_nil hne
  omega

/-- `primeMulTable g` satisfies `IsMulTable` for the power basis of `𝔽₂[X] / (polyOfBits g)`. -/
theorem primeMulTable_isMulTable {g : List Bool} {q : ℕ}
    [Fact (Irreducible (polyOfBits g))] (hdeg : (polyOfBits g).natDegree = q)
    (htrim : polyTrim g = g) (hlen : g.length = q + 1)
    (b : Basis (Fin q) (ZMod 2) (AdjoinRoot (polyOfBits g)))
    (hb : ∀ i : Fin q, b i = AdjoinRoot.root (polyOfBits g) ^ i.1) :
    IsMulTable b (primeMulTable g) := by
  set F := AdjoinRoot (polyOfBits g)
  set α : F := AdjoinRoot.root (polyOfBits g)
  have hne : g ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlast : g.getLast hne = true := getLast_of_polyTrim_eq_self htrim hne
  have hg_drop : g.dropLast ++ [true] = g := by
    conv_rhs => rw [← List.dropLast_append_getLast hne, hlast]
  have hg_drop_len : g.dropLast.length = q := by
    rw [List.length_dropLast, hlen]
    omega
  have hα : (polyOfBits (g.dropLast ++ [true])).aeval α = 0 := by
    rw [hg_drop, show α = AdjoinRoot.root (polyOfBits g) from rfl, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self]
  have hirr : Irreducible (polyOfBits g) := Fact.out
  have hdeg_pos : 0 < (polyOfBits g).natDegree := hirr.natDegree_pos
  unfold IsMulTable
  refine ⟨by simp [primeMulTable, hlen], fun u v => ?_⟩
  have htable_def : tableEntry (primeMulTable g) u.1 v.1 =
      (powerTable g).getD (u.1 + v.1) [] := by
    unfold tableEntry primeMulTable
    have hq_len : g.length - 1 = q := by omega
    rw [hq_len]
    set rows := (List.range q).map fun i =>
      (List.range q).map fun j => (powerTable g).getD (i + j) []
    have hrows : rows.length = q := by simp [rows]
    rw [List.getD_eq_getElem rows [] (by omega)]
    dsimp only [rows]
    rw [List.getElem_map, List.getElem_range]
    set row := (List.range q).map fun j => (powerTable g).getD (u.1 + j) []
    have hrow : row.length = q := by simp [row]
    rw [List.getD_eq_getElem row [] (by omega)]
    dsimp only [row]
    rw [List.getElem_map, List.getElem_range]
  have hp_eval : α ^ (u.1 + v.1) =
      ∑ d ∈ Finset.range g.dropLast.length,
        bitEquiv.symm (((powerTable g).getD (u.1 + v.1) []).getD d false) • α ^ d := by
    have hpt := pow_eq_sum_powerTable g.dropLast hα (e := u.1 + v.1) (by rw [hg_drop_len]; omega)
    simpa only [hg_drop] using hpt
  rw [hb u, hb v, ← pow_add, hp_eval, hg_drop_len, fieldOfBits, htable_def,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb i]

/-- `primeDisperser N` is an affine disperser for dimension `primeThreshold N + 1`. -/
theorem isAffineDisperser_primeDisperser (N : ℕ) :
    IsAffineDisperser (primeDisperser N) (primeThreshold N + 1) := by
  set q := primeDeg N
  have hq : q.Prime := (primeDeg_spec N).1
  have hq9 : 9 ≤ q := nine_le_primeDeg N
  have hq3 : 3 ≤ q := by omega
  set g := shoupIrreducibleBits q
  obtain ⟨hirr, hdeg, htrim, hlen⟩ := shoupIrreducibleBits_spec hq hq3
  have hirr_fact : Fact (Irreducible (polyOfBits g)) := ⟨hirr⟩
  let _ := hirr_fact
  set F := AdjoinRoot (polyOfBits g)
  set α : F := AdjoinRoot.root (polyOfBits g)
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have hpb_dim : pb.dim = q := by
    rw [AdjoinRoot.powerBasis_dim]
    exact hdeg
  let b : Basis (Fin q) (ZMod 2) F := pb.basis.reindex (finCongr hpb_dim)
  have hb : ∀ i : Fin q, b i = α ^ i.1 := fun i => by
    dsimp only [b]
    rw [Basis.reindex_apply, pb.coe_basis, AdjoinRoot.powerBasis_gen]
    rfl
  have hmul : IsMulTable b (primeMulTable g) :=
    primeMulTable_isMulTable hdeg htrim hlen b hb
  have ht : 0 < primeSymDeg N := by unfold primeSymDeg; omega
  have hrn : (N / q) * q ≤ N := Nat.div_mul_le_self N q
  have hfinF : Module.Finite (ZMod 2) F := pb.finite
  have : Finite F := Module.finite_of_finite (ZMod 2)
  have hfinrank : finrank (ZMod 2) F = q := by rw [pb.finrank, hpb_dim]
  have hsub : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ 1 := by
    intro K hK
    have hcard := Cslib.card_subfield_le_of_lt_prime (n := q) (L := q - 1) hfinrank
      (fun p hp hpq => by
        have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
        rw [hpeq]
        omega)
      K hK
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.div_self hq.pos] at hcard
  have hdisp : IsAffineDisperser
      (traceSymBits (1 : F) (N / q) (primeSymDeg N) b
        (blockPos (N := N) (r := N / q) (n := q) hrn))
      (primeThreshold N + 1) := by
    refine isAffineDisperser_of_forall_exists_ne fun V hV => ?_
    have hpos_inj : Function.Injective (blockPos (N := N) (r := N / q) (n := q) hrn) :=
      fun _ _ h => finProdFinEquiv.injective (Fin.ext (by
        have hv := congrArg Fin.val h
        rw [blockPos, blockPos] at hv
        exact hv))
    refine exists_traceSymBits_ne hfinrank hsub one_ne_zero ht b hpos_inj V ?_
    rw [hV]
    change (N - N / q * q) + (N / q * max (N / q + 1) 1 + N / q * (N / q + 1) +
        q * primeSymDeg N + q * (N / q) / primeSymDeg N) <
      (N - N / q * q) + (N / q * (N / q + 1) + N / q * (N / q + 1) +
        q * primeSymDeg N + q * (N / q) / primeSymDeg N) + 1
    rw [max_eq_left (Nat.le_add_left 1 _)]
    exact Nat.lt_succ_self _
  have heq_fn : primeDisperser N =
      traceSymBits (1 : F) (N / q) (primeSymDeg N) b
        (blockPos (N := N) (r := N / q) (n := q) hrn) := by
    funext x
    unfold primeDisperser primeDisperserBits
    rw [traceSymCoords_eq hmul ht hrn]
    congr 1
    exact ofList_ofFn x
  rw [heq_fn]
  exact hdisp

/-- For all sufficiently large `N`, `primeThreshold N + 1 ≤ 2148 * (fifthRoot N) ^ 4`. -/
theorem eventually_primeThreshold_le :
    ∀ᶠ N in atTop, primeThreshold N + 1 ≤ 2148 * (fifthRoot N) ^ 4 := by
  refine eventually_atTop.mpr ⟨32, fun N hN => ?_⟩
  set u := fifthRoot N
  have hu_pow : u ^ 5 ≤ N := (fifthRoot_spec N).1
  have hN_lt : N < (u + 1) ^ 5 := (fifthRoot_spec N).2
  have hu2 : 2 ≤ u := by
    by_contra hlt
    have hu1 : u + 1 ≤ 2 := by omega
    have h32 : (u + 1) ^ 5 ≤ 2 ^ 5 := Nat.pow_le_pow_left hu1 5
    omega
  have hbound : primeThresholdBound N = u ^ 3 := by
    change (max 2 u) ^ 3 = u ^ 3
    rw [max_eq_right hu2]
  have hsym : primeSymDeg N = u := by
    change max 1 u = u
    rw [max_eq_right (by omega : 1 ≤ u)]
  obtain ⟨_, hq_low, hq_high⟩ := primeDeg_spec N
  rw [hbound] at hq_low hq_high
  set q := primeDeg N
  set r := N / q
  have hN_ub : N ≤ 32 * u ^ 5 := by
    have hu1 : u + 1 ≤ 2 * u := by omega
    have hpow : (u + 1) ^ 5 ≤ (2 * u) ^ 5 := Nat.pow_le_pow_left hu1 5
    have h32u : (2 * u) ^ 5 = 32 * u ^ 5 := by ring
    omega
  have hr_ub : r ≤ 32 * u ^ 2 := by
    refine Nat.div_le_of_le_mul ?_
    calc N ≤ 32 * u ^ 5 := hN_ub
      _ = u ^ 3 * (32 * u ^ 2) := by ring
      _ ≤ q * (32 * u ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have hu_pos : 0 < u := by omega
  have hu2_pos : 1 ≤ u ^ 2 := Nat.pow_pos (n := 2) hu_pos
  have hr1_ub : r + 1 ≤ 33 * u ^ 2 := by nlinarith
  have hrr1_ub : r * (r + 1) ≤ 1056 * u ^ 4 := by
    calc r * (r + 1) ≤ (32 * u ^ 2) * (33 * u ^ 2) := Nat.mul_le_mul hr_ub hr1_ub
      _ = 1056 * u ^ 4 := by ring
  have hwaste : N - r * q < q := by
    have hdiv := Nat.div_add_mod N q
    have hmod := Nat.mod_lt N (by omega : 0 < q)
    change q * r + N % q = N at hdiv
    rw [mul_comm r q]
    omega
  have hq_u4 : q ≤ u ^ 4 := by
    calc q ≤ 2 * u ^ 3 := hq_high
      _ ≤ u * u ^ 3 := Nat.mul_le_mul_right _ hu2
      _ = u ^ 4 := by ring
  have hwaste_ub : N - r * q ≤ u ^ 4 := le_trans (by omega) hq_u4
  have hqt_ub : q * primeSymDeg N ≤ 2 * u ^ 4 := by
    rw [hsym]
    calc q * u ≤ (2 * u ^ 3) * u := Nat.mul_le_mul_right _ hq_high
      _ = 2 * u ^ 4 := by ring
  have hqr_t_ub : q * r / primeSymDeg N ≤ 32 * u ^ 4 := by
    rw [hsym]
    refine Nat.div_le_of_le_mul ?_
    have hqr_N : q * r ≤ N := Nat.mul_div_le N q
    calc q * r ≤ N := hqr_N
      _ ≤ 32 * u ^ 5 := hN_ub
      _ = u * (32 * u ^ 4) := by ring
  have h1_u4 : 1 ≤ u ^ 4 := Nat.pow_pos (n := 4) hu_pos
  change (N - r * q) + (r * (r + 1) + r * (r + 1) + q * primeSymDeg N +
      q * r / primeSymDeg N) + 1 ≤ 2148 * u ^ 4
  omega

/-- Real-valued bound `primeThreshold N + 1 ≤ 2148 * N ^ (4 / 5)` for all large `N`. -/
theorem eventually_primeThreshold_real_le :
    ∀ᶠ N in atTop, ((primeThreshold N + 1 : ℕ) : ℝ) ≤ 2148 * (N : ℝ) ^ ((4 : ℝ) / 5) := by
  filter_upwards [eventually_primeThreshold_le, eventually_ge_atTop 1] with N hle hN1
  have hu5 : ((fifthRoot N : ℝ)) ^ 5 ≤ (N : ℝ) := by
    exact_mod_cast (fifthRoot_spec N).1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hu0 : (0 : ℝ) ≤ fifthRoot N := Nat.cast_nonneg _
  have hu_le : (fifthRoot N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 5) := by
    calc (fifthRoot N : ℝ) = ((fifthRoot N : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hu0]
          norm_num
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow (pow_nonneg hu0 5) hu5 (by norm_num)
  have hu4_le : ((fifthRoot N : ℝ)) ^ 4 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := by
    calc ((fifthRoot N : ℝ)) ^ 4 ≤ ((N : ℝ) ^ ((1 : ℝ) / 5)) ^ 4 :=
          pow_le_pow_left₀ hu0 hu_le 4
      _ = (N : ℝ) ^ ((4 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
          norm_num
  have hleR : ((primeThreshold N + 1 : ℕ) : ℝ) ≤ 2148 * ((fifthRoot N : ℝ)) ^ 4 := by
    exact_mod_cast hle
  calc ((primeThreshold N + 1 : ℕ) : ℝ) ≤ 2148 * ((fifthRoot N : ℝ)) ^ 4 := hleR
    _ ≤ 2148 * (N : ℝ) ^ ((4 : ℝ) / 5) := by nlinarith

/-- Asymptotic threshold bound `primeThreshold N + 1 = O(N ^ (4 / 5))`. -/
theorem isBigO_primeThreshold :
    (fun N => ((primeThreshold N + 1 : ℕ) : ℝ)) =O[atTop] fun N => (N : ℝ) ^ ((4 : ℝ) / 5) := by
  refine IsBigO.of_bound 2148 ?_
  filter_upwards [eventually_primeThreshold_real_le, eventually_ge_atTop 1] with N hrhs _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.rpow_nonneg hN0 _)]
  exact hrhs

/-- `primeThreshold N + 1 < N` for all sufficiently large `N`. -/
theorem eventually_primeThreshold_lt : ∀ᶠ N in atTop, primeThreshold N + 1 < N := by
  filter_upwards [eventually_primeThreshold_le, eventually_ge_atTop (2149 ^ 5)] with N hle hN
  set u := fifthRoot N
  have hu_pow : u ^ 5 ≤ N := (fifthRoot_spec N).1
  have hN_lt : N < (u + 1) ^ 5 := (fifthRoot_spec N).2
  have hu2149 : 2149 ≤ u := by
    by_contra hlt
    have : u + 1 ≤ 2149 := by omega
    have : (u + 1) ^ 5 ≤ 2149 ^ 5 := Nat.pow_le_pow_left this 5
    omega
  have hlt_u : 2148 * u ^ 4 < u ^ 5 := by
    calc 2148 * u ^ 4 < 2149 * u ^ 4 := by
          nlinarith [Nat.pow_pos (n := 4) (by omega : 0 < u)]
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ hu2149
      _ = u ^ 5 := by ring
  exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt_u hu_pow)

end Cslib.AffineDisperser.Li
