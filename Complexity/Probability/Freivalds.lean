/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.HashFamily
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.Pi
import Complexity.Probability.PMF.UniformBound

/-!
# Random-vector fingerprints of matrices

Freivalds' technique compares two matrices `M` and `N` through `M *ᵥ x` and `N *ᵥ x` for a
random vector `x`. This module proves the counting bound behind it. The coordinates of `x` are
drawn uniformly from a finite set `S` and encoded in the ring by `e : S → R`. If every nonzero
`d : R` makes `s ↦ d * e s` injective, distinct matrices agree on at most a `1/|S|` fraction of
the vectors, and on `k` independent vectors simultaneously with probability at most `1/|S|^k`.

The encoding hypothesis covers the two standard instances. `S = Bool` with `e` the `0`/`1`
indicator works over every ring, giving the bound `1/2` of `[MitzenmacherUpfal2017]`,
Theorem 1.4. Over a finite field, `e = id` gives `1/|F|`. `[MotwaniRaghavan1995]`, Section 7.1,
presents this technique as fingerprinting.

The proof fixes an entry `(i, j)` with `(M - N) i j ≠ 0`. Once the coordinates of `x` other
than `j` are fixed, at most one value of `x j` satisfies row `i` of `(M - N) *ᵥ x = 0`. This is
the argument of `[MitzenmacherUpfal2017]`, Theorem 1.4, stated here for rectangular matrices,
arbitrary encodings and an arbitrary non-unital ring.

## Main results

* `card_filter_mulVec_eq_mul_card_le`: `#{x | M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)} * |S| ≤ |S|^n`.
* `card_filter_forall_mulVec_eq_le`: the `k`-vector count
  `#{xs | ∀ t, M *ᵥ (e ∘ xs t) = N *ᵥ (e ∘ xs t)} * |S|^k ≤ |S|^(n*k)`.
* `toOuterMeasure_mulVec_eq_le`, `toOuterMeasure_forall_mulVec_eq_le`: the uniform-probability
  forms, at most `1/|S|` and `1/|S|^k`.
* `isUniversalHash_mulVec`: `M ↦ M *ᵥ (e ∘ x)` is a `1/|S|`-universal hash family on matrices
  with uniform seed `x`, in the sense of `IsUniversalHash`.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
* [R. Motwani and P. Raghavan, *Randomized Algorithms*][MotwaniRaghavan1995]
-/

public section

namespace Cslib.Probability

open scoped Matrix ENNReal

variable {m n κ S R : Type*} [Fintype n] [Fintype κ] [Fintype S] [DecidableEq n]
  [DecidableEq κ]

section Counting

variable [Fintype m] [NonUnitalNonAssocRing R] [DecidableEq R]

/-- Distinct matrices agree on at most a `1/|S|` fraction of the encoded vectors. -/
theorem card_filter_mulVec_eq_mul_card_le
    {e : S → R} (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s)
    {M N : Matrix m n R} (hMN : M ≠ N) :
    (Finset.univ.filter fun x : n → S => M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)).card * Fintype.card S ≤
      Fintype.card S ^ Fintype.card n := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, (M - N) i j ≠ 0 := by
    by_contra! h
    exact hMN (sub_eq_zero.mp (Matrix.ext h))
  set E := Finset.univ.filter fun x : n → S => M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)
  -- On `E`, the coordinates other than `j` determine the whole vector.
  have hinj : Set.InjOn (fun x : n → S => fun k : {k // k ≠ j} => x k) E := by
    intro x hx y hy hxy
    simp only [E, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
    have hrest : ∀ k, k ≠ j → x k = y k := fun k hk => congrFun hxy ⟨k, hk⟩
    have hrow : ∀ z : n → S, M *ᵥ (e ∘ z) = N *ᵥ (e ∘ z) →
        (M - N) i j * e (z j) + ∑ k ∈ Finset.univ.erase j, (M - N) i k * e (z k) = 0 := by
      intro z hz
      have h0 : ((M - N) *ᵥ (e ∘ z)) i = 0 := by
        rw [Matrix.sub_mulVec, Pi.sub_apply, hz, sub_self]
      rwa [Matrix.mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h0
    have hsum : ∑ k ∈ Finset.univ.erase j, (M - N) i k * e (x k) =
        ∑ k ∈ Finset.univ.erase j, (M - N) i k * e (y k) :=
      Finset.sum_congr rfl fun k hk => by rw [hrest k (Finset.ne_of_mem_erase hk)]
    have hx' := hrow x hx
    rw [hsum] at hx'
    have hxj : x j = y j := he _ hij (add_right_cancel (hx'.trans (hrow y hy).symm))
    funext k
    by_cases hk : k = j
    · subst hk; exact hxj
    · exact hrest k hk
  have hcard := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, Fintype.card_fun] at hcard
  calc E.card * Fintype.card S ≤ Fintype.card S ^ Fintype.card {k // k ≠ j} * Fintype.card S :=
        Nat.mul_le_mul_right _ hcard
    _ = Fintype.card S ^ Fintype.card n := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← pow_succ,
          Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨j⟩)]

/-- Distinct matrices agree on `card κ` independent encoded vectors for at most a
`1/|S|^(card κ)` fraction of the tuples. -/
theorem card_filter_forall_mulVec_eq_le
    {e : S → R} (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s)
    {M N : Matrix m n R} (hMN : M ≠ N) :
    (Finset.univ.filter fun xs : κ → n → S => ∀ t, M *ᵥ (e ∘ xs t) = N *ᵥ (e ∘ xs t)).card *
        Fintype.card S ^ Fintype.card κ ≤
      Fintype.card S ^ (Fintype.card n * Fintype.card κ) := by
  classical
  set E := Finset.univ.filter fun x : n → S => M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)
  have hpi : (Finset.univ.filter fun xs : κ → n → S => ∀ t, M *ᵥ (e ∘ xs t) = N *ᵥ (e ∘ xs t)) =
      Fintype.piFinset fun _ => E := by
    ext xs
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, ← mul_pow, pow_mul]
  exact Nat.pow_le_pow_left (card_filter_mulVec_eq_mul_card_le he hMN) _

end Counting

section Probability

variable [Finite m] [Nonempty S] [NonUnitalNonAssocRing R]

/-- Distinct matrices agree on a uniform encoded vector with probability at most `1/|S|`
(`[MitzenmacherUpfal2017]`, Theorem 1.4, for `S = Bool`). -/
theorem toOuterMeasure_mulVec_eq_le
    {e : S → R} (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s)
    {M N : Matrix m n R} (hMN : M ≠ N) :
    (PMF.uniformOfFintype (n → S)).toOuterMeasure {x | M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)} ≤
      (Fintype.card S : ℝ≥0∞)⁻¹ := by
  have := Fintype.ofFinite m
  classical
  rw [← one_div, ← Nat.cast_one]
  refine PMF.toOuterMeasure_uniformOfFintype_le_div (α := n → S)
    (P := fun x => M *ᵥ (e ∘ x) = N *ᵥ (e ∘ x)) (Fintype.card_pos (α := S)) ?_
  rw [one_mul, mul_comm, Fintype.card_fun]
  exact card_filter_mulVec_eq_mul_card_le he hMN

/-- Distinct matrices agree on all of `card κ` independent uniform encoded vectors with
probability at most `1/|S|^(card κ)`. -/
theorem toOuterMeasure_forall_mulVec_eq_le
    {e : S → R} (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s)
    {M N : Matrix m n R} (hMN : M ≠ N) :
    (PMF.uniformOfFintype (κ → n → S)).toOuterMeasure
        {xs | ∀ t, M *ᵥ (e ∘ xs t) = N *ᵥ (e ∘ xs t)} ≤
      ((Fintype.card S : ℝ≥0∞)⁻¹) ^ Fintype.card κ := by
  have := Fintype.ofFinite m
  classical
  rw [← ENNReal.inv_pow, ← one_div, ← Nat.cast_pow, ← Nat.cast_one]
  refine PMF.toOuterMeasure_uniformOfFintype_le_div (α := κ → n → S)
    (P := fun xs => ∀ t, M *ᵥ (e ∘ xs t) = N *ᵥ (e ∘ xs t))
    (pow_pos (Fintype.card_pos (α := S)) _) ?_
  rw [one_mul, mul_comm (Fintype.card S ^ Fintype.card κ), Fintype.card_fun, Fintype.card_fun,
    ← pow_mul]
  exact card_filter_forall_mulVec_eq_le he hMN

/-- Random-vector fingerprints form a `1/|S|`-universal hash family on matrices. -/
theorem isUniversalHash_mulVec
    {e : S → R} (he : ∀ d : R, d ≠ 0 → Function.Injective fun s => d * e s) :
    IsUniversalHash (PMF.uniformOfFintype (n → S)) (fun x (M : Matrix m n R) => M *ᵥ (e ∘ x))
      (Fintype.card S : ℝ≥0∞)⁻¹ :=
  fun _ _ hMN => toOuterMeasure_mulVec_eq_le he hMN

end Probability

/-- The `0`/`1` encoding of bits satisfies the encoding hypothesis over every ring. -/
theorem injective_mul_boolIndicator {R : Type*} [NonAssocRing R] (d : R) (hd : d ≠ 0) :
    Function.Injective fun b : Bool => d * if b then (1 : R) else 0 := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [eq_comm]

end Cslib.Probability
