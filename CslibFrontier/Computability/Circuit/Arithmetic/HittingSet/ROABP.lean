/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABPWeights
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution
public import CslibFrontier.Foundations.Data.MvPolynomial.WeightSubstitution
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.NumberTheory.Bertrand

/-!
# Quasipolynomial hitting sets for read-once oblivious branching programs

Over a field of characteristic zero there is an explicit set of points, of size
`(n δ w) ^ O(log n)`, on which no nonzero polynomial in `n` variables vanishes that is computed
by a read-once oblivious algebraic branching program of width `w` in some order of the
variables, with layers of degree at most `δ` (`isHittingSet_roabpHittingSet`). The set does not
depend on the order. This is Theorem 1 of Agrawal, Gurjar, Korwar and Saxena
[AgrawalGurjarKorwarSaxena2015] for univariate layers, in characteristic zero.

Compare `isHittingSet_anyOrderHittingSet_roabp`, a set of polynomial size for multilinear
polynomials computed by narrow programs in every order: here one order suffices and the degree
is arbitrary, at the price of a quasipolynomial size.

## Proof

Let `f = (∏ᵢ Mᵢ (xᵢ)) s t`. Its coefficient at a monomial `m` is the `(s, t)` entry of
`segmentCoeff M l m` (`coeff_roabpProd`). Some weight `c` of at most `⌈lg n⌉` levels isolates a
set of monomials among these matrices (`exists_isolating_weight`), so `f (τ ^ c i)` is a nonzero
univariate polynomial in `τ` (`MvPolynomial.aeval_X_pow_ne_zero_of_isolates`, Lemma 6 of the
source). Its degree is at most `n δ (B + p) ^ ⌈lg n⌉`, so it is nonzero at one of the first
values of `τ`. The hitting set consists of the points `(τ ^ c i)` over all weights `c` of at
most `⌈lg n⌉` levels with parameters below the prime `p = roabpPrime n w δ` and these values
of `τ`.

## Main definitions

* `roabpPrime`: the least prime above `2 n² w⁸ + δ`.
* `roabpHittingSet`: the hitting set.

## Main results

* `isHittingSet_roabpHittingSet`: [AgrawalGurjarKorwarSaxena2015, Theorem 1], for univariate
  layers, in characteristic zero.
* `card_roabpHittingSet_le`, `roabpPrime_le`: the size of the set.

## References

* [M. Agrawal, R. Gurjar, A. Korwar, N. Saxena, *Hitting-sets for ROABP and sum of
  set-multilinear circuits*][AgrawalGurjarKorwarSaxena2015], Theorem 1 and §3
-/

public section

open scoped Polynomial

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

/-- The least prime above `2 n² w⁸ + δ`. -/
noncomputable def roabpPrime (n w δ : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 * n * (w ^ 2) ^ 4 * n + δ + 1))

theorem roabpPrime_prime (n w δ : ℕ) : (roabpPrime n w δ).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 * n * (w ^ 2) ^ 4 * n + δ + 1))).2

theorem lt_roabpPrime (n w δ : ℕ) : 2 * n * (w ^ 2) ^ 4 * n + δ < roabpPrime n w δ :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 * n * (w ^ 2) ^ 4 * n + δ + 1))).1

/-- By Bertrand's postulate the prime is at most `2 (2 n² w⁸ + δ + 1)`. -/
theorem roabpPrime_le (n w δ : ℕ) :
    roabpPrime n w δ ≤ 2 * (2 * n * (w ^ 2) ^ 4 * n + δ + 1) := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul
    (2 * n * (w ^ 2) ^ 4 * n + δ + 1) (Nat.succ_ne_zero _)
  exact (Nat.find_min' _ ⟨hlt.le, hq⟩).trans hle

open scoped Classical in
/-- The lists of at most `L` parameters below `p`. -/
noncomputable def levelLists (p L : ℕ) : Finset (List ℕ) :=
  (range (L + 1)).biUnion fun k =>
    (Fintype.piFinset fun _ : Fin k => range p).image List.ofFn

theorem mem_levelLists {p L : ℕ} {a : List ℕ} (hlen : a.length ≤ L) (ha : ∀ x ∈ a, x < p) :
    a ∈ levelLists p L := by
  classical
  refine mem_biUnion.2 ⟨a.length, mem_range.2 (Nat.lt_succ_of_le hlen), mem_image.2
    ⟨fun i => a.get i, Fintype.mem_piFinset.2 fun i => mem_range.2 (ha _ (a.get_mem i)),
      List.ofFn_get a⟩⟩

theorem card_levelLists_le (p L : ℕ) (hp : 0 < p) : (levelLists p L).card ≤ (L + 1) * p ^ L := by
  classical
  refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ (p ^ L) fun k hk => ?_).trans_eq ?_)
  · refine card_image_le.trans ?_
    rw [Fintype.card_piFinset, prod_const, card_range, card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_right hp (Nat.lt_succ_iff.1 (mem_range.1 hk))
  · rw [card_range, smul_eq_mul]

variable (F : Type*) [Field F] (n w δ : ℕ)

open scoped Classical in
/-- The hitting set for read-once oblivious branching programs of width `w` in `n` variables
with layers of degree at most `δ`: the points `(τ ^ c i)` for the weights `c` of at most
`⌈lg n⌉` levels with parameters below `p = roabpPrime n w δ` and base `B = n δ p + 1`, and
`τ = 0, …, n δ (B + p) ^ ⌈lg n⌉`. -/
noncomputable def roabpHittingSet : Finset (Fin n → F) :=
  (levelLists (roabpPrime n w δ) (Nat.clog 2 n) ×ˢ
    range (n * δ * (n * δ * roabpPrime n w δ + 1 + roabpPrime n w δ) ^ Nat.clog 2 n + 1)).image
    fun x i => (x.2 : F) ^ levelWeight (roabpPrime n w δ) (n * δ * roabpPrime n w δ + 1) x.1 i

variable {F n w δ}

/-- The monomials of a branching program with layers of degree at most `δ` have individual
degree at most `δ` and only variables of the program. -/
private theorem support_roabpProd_subset {M : Fin n → Matrix (Fin w) (Fin w) F[X]}
    (hM : ∀ i s t, (M i s t).natDegree ≤ δ) {l : List (Fin n)} (hl : l.Nodup) (s t : Fin w) :
    (roabpProd M l s t).support ⊆ monomialsLE l δ := fun m hm => by
  have hm0 : ∀ i ∉ l, m i = 0 := fun i hi => by
    by_contra hne
    exact mem_support_iff.1 hm (coeff_roabpProd_eq_zero M l hi hne s t)
  refine mem_monomialsLE.2 ⟨fun i => ?_, hm0⟩
  by_contra hlt
  rw [not_le] at hlt
  have hil : i ∈ l := by
    by_contra hil
    rw [hm0 i hil] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  refine mem_support_iff.1 hm ?_
  rw [coeff_roabpProd M hl m hm0, List.prod_eq_zero (List.mem_map.2 ⟨i, hil, ?_⟩)]
  · rfl
  · ext s' t'
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hM i s' t').trans_lt hlt)

private theorem totalDegree_le_of_support_subset_monomialsLE {f : MvPolynomial (Fin n) F}
    {l : List (Fin n)} (hf : f.support ⊆ monomialsLE l δ) : f.totalDegree ≤ n * δ := by
  refine Finset.sup_le fun m hm => ?_
  have h := weight_le_of_mem_monomialsLE (c := fun _ => 1) (N := 1) (fun _ => le_rfl) (hf hm)
  rw [Finsupp.weight_apply] at h
  simpa using h

/-- **Quasipolynomial hitting sets for ROABPs in an unknown order**
([AgrawalGurjarKorwarSaxena2015], Theorem 1, for univariate layers, in characteristic zero).
`roabpHittingSet F n w δ` hits every polynomial in `n` variables computed by a read-once
oblivious branching program of width `w` in some order of the variables, with layers of degree
at most `δ`. -/
theorem isHittingSet_roabpHittingSet [CharZero F] :
    IsHittingSet (roabpHittingSet F n w δ) {f | IsROABP w δ f} := by
  classical
  rintro f ⟨l, M, s, t, hl, hM, rfl⟩ hf0
  set p := roabpPrime n w δ with hp
  have : Fact p.Prime := ⟨roabpPrime_prime n w δ⟩
  have hpp : 0 < p := (roabpPrime_prime n w δ).pos
  set B := n * δ * p + 1 with hB
  obtain ⟨a, hlen, hap, S, hiso⟩ := exists_isolating_weight (F := F) (p := p) (δ := δ)
    ((Nat.le_add_right _ δ).trans_lt (lt_roabpPrime n w δ))
    ((Nat.le_add_left δ _).trans_lt (lt_roabpPrime n w δ)) M hl
  set c := levelWeight (n := n) p B a with hc
  have hsupp := support_roabpProd_subset (F := F) hM hl s t
  have hne : aeval (fun i => (Polynomial.X : F[X]) ^ c i) (roabpProd M l s t) ≠ 0 :=
    aeval_X_pow_ne_zero_of_isolates hiso (Matrix.entryLinearMap F F s t) hsupp
      (fun m hm => coeff_roabpProd M hl m (mem_monomialsLE.1 hm).2 s t) hf0
  set N := n * δ * (B + p) ^ Nat.clog 2 n with hN
  have hcle : ∀ i, c i ≤ (B + p) ^ Nat.clog 2 n := fun i =>
    (levelWeight_le hpp (Nat.succ_pos _) a i).trans
      (Nat.pow_le_pow_right (Nat.succ_le_of_lt (Nat.add_pos_right _ hpp)) hlen)
  have hdeg : (aeval (fun i => (Polynomial.X : F[X]) ^ c i) (roabpProd M l s t)).natDegree <
      N + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_aeval_le_mul (k := (B + p) ^ Nat.clog 2 n)
      (fun i => ?_) _).trans (Nat.mul_le_mul_right _
        (totalDegree_le_of_support_subset_monomialsLE hsupp)))
    rw [Polynomial.natDegree_X_pow]
    exact hcle i
  by_contra hall
  refine hne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    ((range (N + 1)).image fun k : ℕ => (k : F)) ?_ ?_)
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    rw [eval_polynomial_aeval]
    by_contra hne'
    refine hall ⟨fun i => (k : F) ^ c i, mem_image.2 ⟨(a, k), mem_product.2
      ⟨mem_levelLists hlen hap, hk⟩, rfl⟩, ?_⟩
    simpa using hne'
  · rwa [card_image_of_injective _ Nat.cast_injective, card_range]

variable (F n w δ) in
/-- The hitting set has at most `(⌈lg n⌉ + 1) p ^ ⌈lg n⌉ (n δ (B + p) ^ ⌈lg n⌉ + 1)` points,
with `p = roabpPrime n w δ ≤ 2 (2 n² w⁸ + δ + 1)` and `B = n δ p + 1`: quasipolynomial in `n`,
`w` and `δ`. -/
theorem card_roabpHittingSet_le :
    (roabpHittingSet F n w δ).card ≤
      (Nat.clog 2 n + 1) * roabpPrime n w δ ^ Nat.clog 2 n *
        (n * δ * (n * δ * roabpPrime n w δ + 1 + roabpPrime n w δ) ^ Nat.clog 2 n + 1) := by
  classical
  refine card_image_le.trans ?_
  rw [card_product, card_range]
  exact Nat.mul_le_mul_right _ (card_levelLists_le _ _ (roabpPrime_prime n w δ).pos)

end Cslib.Circuits.Arithmetic
