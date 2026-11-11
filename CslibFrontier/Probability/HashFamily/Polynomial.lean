/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic

/-!
# Carter–Wegman polynomial evaluation

Over a finite field `F`, a message `m = (a₁, …, a_v)` of length at most `ℓ` is hashed with a key
`k ∈ F` by evaluating a polynomial at `k` [WegmanCarter1981]:

* `polyHash k m = k ^ v + a₁ k ^ (v - 1) + ⋯ + a_v`, Boneh and Shoup's `Hpoly`
  ([BonehShoup2023], Equation 7.3). It is `ℓ / |F|`-universal ([BonehShoup2023], Lemma 7.2).
* `xpolyHash k m = k * polyHash k m`, their `Hxpoly` ([BonehShoup2023], Equation 7.23). It is
  `(ℓ + 1) / |F|`-Δ-universal ([BonehShoup2023], Lemma 7.8), which is what the Carter–Wegman MAC
  needs.

The leading `k ^ v` lets messages of different lengths be compared: the message polynomials are
monic of degree `v`, so distinct messages give distinct polynomials, and the difference of two of
them has at most `ℓ` roots. Both functions are computed by Horner's rule.

## Main definitions

* `Cslib.Probability.polyHash`, `Cslib.Probability.xpolyHash`: polynomial evaluation hashes.

## Main results

* `Cslib.Probability.isUniversalHash_polyHash`: `polyHash` is `ℓ / |F|`-universal.
* `Cslib.Probability.isDeltaUniversalHash_xpolyHash`: `xpolyHash` is `(ℓ + 1) / |F|`-Δ-universal.

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.2.1 and 7.4.
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

variable {F : Type*} [Field F]

/-- Boneh and Shoup's `Hpoly` ([BonehShoup2023], Equation 7.3): hash the message
`(a₁, …, a_v)` with the key `k` to `k ^ v + a₁ k ^ (v - 1) + ⋯ + a_v`, by Horner's rule. -/
def polyHash (k : F) (m : List F) : F :=
  m.foldl (fun acc a => acc * k + a) 1

/-- Boneh and Shoup's `Hxpoly` ([BonehShoup2023], Equation 7.23): `k * polyHash k m`. -/
def xpolyHash (k : F) (m : List F) : F :=
  k * polyHash k m

open Polynomial

/-- The message polynomial `X ^ v + a₁ X ^ (v - 1) + ⋯ + a_v`. -/
private noncomputable def toPoly (m : List F) : F[X] :=
  m.foldl (fun p a => p * X + C a) 1

private theorem eval_foldl (k : F) (p : F[X]) (m : List F) :
    (m.foldl (fun p a => p * X + C a) p).eval k =
      m.foldl (fun acc a => acc * k + a) (p.eval k) := by
  induction m generalizing p with
  | nil => rfl
  | cons a m ih => simp only [List.foldl_cons, ih, eval_add, eval_mul, eval_X, eval_C]

private theorem eval_toPoly (k : F) (m : List F) : (toPoly m).eval k = polyHash k m := by
  rw [toPoly, eval_foldl, eval_one, polyHash]

private theorem toPoly_append_singleton (m : List F) (a : F) :
    toPoly (m ++ [a]) = toPoly m * X + C a := by
  rw [toPoly, List.foldl_append, List.foldl_cons, List.foldl_nil, toPoly]

/-- Message polynomials are monic, of degree the length of the message. -/
private theorem monic_toPoly (m : List F) :
    (toPoly m).Monic ∧ (toPoly m).natDegree = m.length := by
  induction m using List.reverseRecOn with
  | nil => exact ⟨monic_one, natDegree_one⟩
  | append_singleton m a ih =>
    obtain ⟨hmon, hdeg⟩ := ih
    have hmX : (toPoly m * X).Monic := hmon.mul monic_X
    have hdegX : (toPoly m * X).natDegree = m.length + 1 := by
      rw [natDegree_mul_X hmon.ne_zero, hdeg]
    have hlt : (C a).degree < (toPoly m * X).degree := by
      refine degree_C_le.trans_lt ?_
      rw [degree_eq_natDegree hmX.ne_zero, hdegX]
      exact_mod_cast Nat.succ_pos _
    rw [toPoly_append_singleton, List.length_append, List.length_singleton]
    exact ⟨hmX.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdegX]⟩

/-- Distinct messages have distinct polynomials. -/
private theorem toPoly_injective : Function.Injective (toPoly : List F → F[X]) := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
    intro m' h
    have hlen := (monic_toPoly m').2
    rw [← h, (monic_toPoly ([] : List F)).2] at hlen
    exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton m a ih =>
    intro m' h
    have hlen := (monic_toPoly m').2
    rw [← h, (monic_toPoly (m ++ [a])).2] at hlen
    obtain rfl | ⟨m'', a', rfl⟩ := List.eq_nil_or_concat m'
    · simp at hlen
    rw [List.concat_eq_append] at h ⊢
    rw [toPoly_append_singleton, toPoly_append_singleton] at h
    have ha : a = a' := by
      simpa using congrArg (coeff · 0) h
    subst ha
    rw [ih (mul_right_cancel₀ X_ne_zero (add_right_cancel h))]

/-- **`Hpoly` is `ℓ / |F|`-universal** ([BonehShoup2023], Lemma 7.2): two distinct messages of
length at most `ℓ` collide only at the roots of the nonzero difference of their polynomials. -/
theorem isUniversalHash_polyHash [Fintype F] (ℓ : ℕ) :
    IsUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => polyHash k m) (ℓ / Fintype.card F) := by
  classical
  exact IsUniversalHash.of_card_le fun m m' hm => by
    have hD : toPoly m.1 - toPoly m'.1 ≠ 0 :=
      sub_ne_zero.mpr (toPoly_injective.ne (Subtype.coe_injective.ne hm))
    calc (Finset.univ.filter fun k => polyHash k m.1 = polyHash k m'.1).card
        ≤ (toPoly m.1 - toPoly m'.1).roots.toFinset.card := by
          refine Finset.card_le_card fun k hk => ?_
          rw [Multiset.mem_toFinset, mem_roots hD, IsRoot.def, eval_sub, eval_toPoly,
            eval_toPoly, sub_eq_zero]
          exact (Finset.mem_filter.mp hk).2
      _ ≤ (toPoly m.1 - toPoly m'.1).roots.card := Multiset.toFinset_card_le _
      _ ≤ (toPoly m.1 - toPoly m'.1).natDegree := card_roots' _
      _ ≤ ℓ := (natDegree_sub_le _ _).trans <| max_le
          ((monic_toPoly m.1).2.trans_le m.2) ((monic_toPoly m'.1).2.trans_le m'.2)

/-- **`Hxpoly` is `(ℓ + 1) / |F|`-Δ-universal** ([BonehShoup2023], Lemma 7.8): a difference `d`
of the hashes of two distinct messages occurs only at the roots of the nonzero polynomial
`X (f - g) - d` of degree at most `ℓ + 1`. -/
theorem isDeltaUniversalHash_xpolyHash [Fintype F] (ℓ : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m)
      ((ℓ + 1) / Fintype.card F) := by
  classical
  have h : IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m)
      ((ℓ + 1 : ℕ) / Fintype.card F) := IsDeltaUniversalHash.of_card_le fun m m' hm d => by
    have hD : toPoly m.1 - toPoly m'.1 ≠ 0 :=
      sub_ne_zero.mpr (toPoly_injective.ne (Subtype.coe_injective.ne hm))
    have hdeg : (toPoly m.1 - toPoly m'.1).natDegree ≤ ℓ := (natDegree_sub_le _ _).trans <|
      max_le ((monic_toPoly m.1).2.trans_le m.2) ((monic_toPoly m'.1).2.trans_le m'.2)
    have hE : X * (toPoly m.1 - toPoly m'.1) - C d ≠ 0 := fun h0 => by
      have h1 := congrArg natDegree (sub_eq_zero.mp h0)
      rw [natDegree_X_mul hD, natDegree_C] at h1
      exact Nat.succ_ne_zero _ h1
    calc (Finset.univ.filter fun k => xpolyHash k m.1 - xpolyHash k m'.1 = d).card
        ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).roots.toFinset.card := by
          refine Finset.card_le_card fun k hk => ?_
          rw [Multiset.mem_toFinset, mem_roots hE, IsRoot.def, eval_sub, eval_mul, eval_X,
            eval_C, eval_sub, eval_toPoly, eval_toPoly, sub_eq_zero, mul_sub]
          exact (Finset.mem_filter.mp hk).2
      _ ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X * (toPoly m.1 - toPoly m'.1) - C d).natDegree := card_roots' _
      _ ≤ ℓ + 1 := (natDegree_sub_le _ _).trans <| max_le
          (by rw [natDegree_X_mul hD]; exact Nat.succ_le_succ hdeg)
          (by rw [natDegree_C]; exact Nat.zero_le _)
  push_cast at h
  exact h

end Cslib.Probability
