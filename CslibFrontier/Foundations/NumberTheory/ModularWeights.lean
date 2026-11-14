/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finsupp.Weight

/-!
# Modular weights separating pairs of monomials

For a prime `p` and a residue `a`, the weight `i ↦ a ^ (i + 1) mod p` on `n` variables takes
values below `p`. Two different exponent vectors `m`, `m'` with entries below `p` get the same
weight modulo `p` only if `a` is a root of the nonzero polynomial
`∑ i, (m i - m' i) * X ^ (i + 1)` over `ZMod p`, which has at most `n` roots. So for a set of
fewer than `p / n` pairs of different exponent vectors, some `a < p` gives the two vectors of
every pair different weights.

This family of `p` candidate weights replaces Lemma 4 of [AgrawalGurjarKorwarSaxena2015], which
reduces the weight `i ↦ (δ + 1) ^ i` modulo many primes and counts primes with the prime number
theorem. Here one prime is enough, and the count is the bound on the number of roots of a
polynomial over a field.

## Main definitions

* `Cslib.modWeight`: the weight `i ↦ a ^ (i + 1) mod p`.

## Main results

* `Cslib.modWeight_lt`: the values of `modWeight p a` are below `p`.
* `Cslib.exists_modWeight_separating`: fewer than `p / n` pairs of different exponent vectors
  with entries at most `δ < p` are separated by one of the weights `modWeight p a`, `a < p`.

## References

* [AgrawalGurjarKorwarSaxena2015], Lemma 4 (replaced by the family above).
-/

public section

namespace Cslib

open Polynomial

variable {n : ℕ}

/-- The weight `i ↦ a ^ (i + 1) mod p` on `n` variables. -/
@[expose] def modWeight (p a : ℕ) (i : Fin n) : ℕ := a ^ (i.val + 1) % p

/-- The values of `modWeight p a` are below `p`. -/
theorem modWeight_lt {p : ℕ} (hp : 0 < p) (a : ℕ) (i : Fin n) : modWeight p a i < p :=
  Nat.mod_lt _ hp

/-- Modulo `p`, the weight of an exponent vector `m` for `modWeight p a` is
`∑ i, m i * a ^ (i + 1)`. -/
private theorem natCast_weight_modWeight (p a : ℕ) (m : Fin n →₀ ℕ) :
    ((Finsupp.weight (modWeight p a) m : ℕ) : ZMod p) =
      ∑ i, (m i : ZMod p) * (a : ZMod p) ^ (i.val + 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [modWeight]

/-- Let `p` be a prime and `P` a set of pairs of different exponent vectors on `n` variables with
entries at most `δ < p`. If `P.card * n < p`, then for some `a < p` the weight `modWeight p a`
gives different weights to the two exponent vectors of every pair in `P`. -/
theorem exists_modWeight_separating {p δ : ℕ} [Fact p.Prime] (hδ : δ < p)
    (P : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ)))
    (hP : ∀ x ∈ P, x.1 ≠ x.2 ∧ (∀ i, x.1 i ≤ δ) ∧ ∀ i, x.2 i ≤ δ) (hcard : P.card * n < p) :
    ∃ a < p, ∀ x ∈ P,
      Finsupp.weight (modWeight p a) x.1 ≠ Finsupp.weight (modWeight p a) x.2 := by
  classical
  let q : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) → (ZMod p)[X] := fun x =>
    ∑ i : Fin n, C ((x.1 i : ZMod p) - x.2 i) * X ^ (i.val + 1)
  have hq0 : ∀ x ∈ P, q x ≠ 0 := by
    intro x hx h0
    obtain ⟨hne, h1, h2⟩ := hP x hx
    obtain ⟨j, hj⟩ := DFunLike.ne_iff.1 hne
    have h := congrArg (fun r => r.coeff (j.val + 1)) h0
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow, add_left_inj, Fin.val_inj,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, coeff_zero, sub_eq_zero,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ((h1 j).trans_lt hδ),
      Nat.mod_eq_of_lt ((h2 j).trans_lt hδ)] at h
    exact hj h
  have hbad : (P.biUnion fun x => (q x).roots.toFinset).card <
      (Finset.univ : Finset (ZMod p)).card := by
    rw [Finset.card_univ, ZMod.card]
    refine (Finset.card_biUnion_le_card_mul _ _ n fun x _ => ?_).trans_lt hcard
    refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_C_mul_X_pow_le _ _).trans i.isLt
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  refine ⟨a.val, ZMod.val_lt a, fun x hx heq => ha (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)⟩
  have h := congrArg (Nat.cast : ℕ → ZMod p) heq
  rw [natCast_weight_modWeight, natCast_weight_modWeight, ZMod.natCast_zmod_val] at h
  rw [Multiset.mem_toFinset, mem_roots (hq0 x hx), IsRoot.def]
  simp [q, eval_finsetSum, sub_mul, h]

end Cslib
