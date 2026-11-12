/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.ApproximateCounting
public import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Approximate counting with relative error

Stockmeyer's estimate of the size of a set `S` from hashing (`hashEstimate`) is only accurate
within a constant factor: with high probability it lies between `#S / 16` and `8 #S`. Applied to
the Cartesian power `S ^ k`, whose size is `#S ^ k`, the same constant factor becomes the factor
`128 ^ (1 / k)` after taking a `k`-th root, so a large enough number `k` of copies gives an
estimate of `#S` with any prescribed relative error [Stockmeyer1983]. In integers: if
`s ^ k ≤ e ≤ c s ^ k` and `c p ^ k ≤ (p + 1) ^ k`, then the integer `k`-th root `⌊e ^ (1 / k)⌋` of
`e` lies between `s` and `(1 + 1 / p) s`, and `k = 7 p` copies suffice for the factor
`c = 128 = 2 ^ 7`, as `(1 + 1 / p) ^ p ≥ 2`.

The failure probability of the estimate is amplified by the majority votes inside it: answering
each of the `n + 1` questions by the majority of `12 (n + 1 + t)` trials makes the estimate fail
with probability at most `2 ^ (-t)`.

## Main definitions

* `Cslib.Probability.ApproximateCounting.relativeHashEstimate`: the estimate of `#S` from the
  `k`-th root of Stockmeyer's estimate of the size of `S ^ k`.

## Main results

* `Cslib.Probability.ApproximateCounting.le_nthRoot_and_mul_nthRoot_le`: an estimate of `s ^ k`
  within a factor `c ≤ (1 + 1 / p) ^ k` gives an estimate of `s` within relative error `1 / p`.
* `Cslib.Probability.ApproximateCounting.two_pow_mul_pow_le_add_one_pow`: `k = m p` copies make
  the factor `2 ^ m` at most `(1 + 1 / p) ^ k`.
* `Cslib.Probability.ApproximateCounting.dens_filter_not_hashEstimate_le`: Stockmeyer's estimate
  fails to lie between `#S / 16` and `8 #S` with probability at most `(n + 1) (8 / 9) ^ r`.
* `Cslib.Probability.ApproximateCounting.dens_filter_not_relativeHashEstimate_le`,
  `Cslib.Probability.ApproximateCounting.one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate`:
  the relative estimate lies between `#S` and `(1 + 1 / p) #S` except with probability at most
  `(n + 1) (8 / 9) ^ r`, and so with probability at least `1 - 2 ^ (-t)` for `r = 6 (n + 1 + t)`.
* In namespace Cslib.Probability.ApproximateCounting,
  `one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate` gives the same for a set of
  vectors in `(ZMod 2) ^ m`, with `7 p` copies and affine hash families.

## References

* [L. Stockmeyer, *The complexity of approximate counting*][Stockmeyer1983]
-/

@[expose] public section

namespace Cslib.Probability.ApproximateCounting

open Finset

/-! ### Roots of estimates of powers -/

section Roots

/-- **Relative error from an estimate of a power.** If `e` over-estimates `s ^ k` by at most a
factor `c`, that is `s ^ k ≤ e ≤ c s ^ k` with `k ≠ 0`, and `c ≤ (1 + 1 / p) ^ k`, then the
integer `k`-th root of `e` estimates `s` from above within the relative error `1 / p`:
`s ≤ ⌊e ^ (1 / k)⌋ ≤ (1 + 1 / p) s`. -/
theorem le_nthRoot_and_mul_nthRoot_le {k s e c p : ℕ} (hk : k ≠ 0) (hse : s ^ k ≤ e)
    (hes : e ≤ c * s ^ k) (hc : c * p ^ k ≤ (p + 1) ^ k) :
    s ≤ Nat.nthRoot k e ∧ p * Nat.nthRoot k e ≤ (p + 1) * s := by
  refine ⟨(Nat.le_nthRoot_iff hk).2 hse, ?_⟩
  rw [← Nat.pow_le_pow_iff_left hk, mul_pow, mul_pow]
  calc p ^ k * Nat.nthRoot k e ^ k ≤ p ^ k * (c * s ^ k) :=
        Nat.mul_le_mul_left _ ((Nat.pow_nthRoot_le (.inl hk)).trans hes)
    _ = c * p ^ k * s ^ k := by ring
    _ ≤ (p + 1) ^ k * s ^ k := Nat.mul_le_mul_right _ hc

/-- **Enough copies**: `(1 + 1 / p) ^ p ≥ 2`, so `(1 + 1 / p) ^ (m p) ≥ 2 ^ m`, that is
`2 ^ m p ^ (m p) ≤ (p + 1) ^ (m p)` for `p ≠ 0`. -/
theorem two_pow_mul_pow_le_add_one_pow (m : ℕ) {p : ℕ} (hp : p ≠ 0) :
    2 ^ m * p ^ (m * p) ≤ (p + 1) ^ (m * p) := by
  -- Bernoulli's inequality: `p ^ p + p ^ p ≤ (p + 1) ^ p`
  have h : 2 * p ^ p ≤ (p + 1) ^ p := by
    have := pow_add_mul_le_add_pow_of_sq_nonneg (R := ℕ) (a := p) (b := 1) (Nat.zero_le _)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) p
    rwa [mul_one, Nat.cast_id, mul_pow_sub_one hp, ← two_mul] at this
  rw [mul_comm m, pow_mul, pow_mul, ← mul_pow]
  exact Nat.pow_le_pow_left h m

end Roots

/-! ### Amplifying the success probability -/

/-- `(n + 1) (8 / 9) ^ (6 (n + 1 + t)) ≤ 2 ^ (-t)`, as `(n + 1) 2 ^ t ≤ 2 ^ (n + 1 + t)` and
`2 8 ^ 6 ≤ 9 ^ 6`. -/
private theorem natCast_add_one_mul_le_inv_two_pow (n t : ℕ) :
    ((n : ℚ≥0) + 1) * (8 / 9) ^ (6 * (n + 1 + t)) ≤ (2 ^ t)⁻¹ := by
  have key : (n + 1) * 2 ^ t * 8 ^ (6 * (n + 1 + t)) ≤ 9 ^ (6 * (n + 1 + t)) := by
    have hn : (n + 1) * 2 ^ t ≤ 2 ^ (n + 1 + t) := by
      rw [pow_add]
      exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    calc (n + 1) * 2 ^ t * 8 ^ (6 * (n + 1 + t))
        ≤ 2 ^ (n + 1 + t) * 8 ^ (6 * (n + 1 + t)) := Nat.mul_le_mul_right _ hn
      _ = (2 * 8 ^ 6) ^ (n + 1 + t) := by rw [mul_pow, pow_mul]
      _ ≤ (9 ^ 6) ^ (n + 1 + t) := Nat.pow_le_pow_left (by norm_num) _
      _ = 9 ^ (6 * (n + 1 + t)) := by rw [pow_mul]
  have key' := Nat.cast_le (α := ℚ≥0).2 key
  push_cast at key'
  rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity), ← div_eq_inv_mul,
    le_div_iff₀ (by positivity), mul_right_comm]
  exact key'

section Hashing

variable {ι : ℕ → Type*} [∀ j, Fintype (ι j)] {X : Type*} {Y : ℕ → Type*} [∀ j, Fintype (Y j)]
  [∀ j, DecidableEq (Y j)] {n r : ℕ}

/-- The relative estimate of `#S` from hashing: the integer `k`-th root of `16 E`, where `E` is
Stockmeyer's estimate (`hashEstimate`) of the size `#S ^ k` of the Cartesian power `S ^ k` from
the hash families `h j` on `k`-tuples, the targets `y j` and the seeds `ω`. The factor `16` makes
`16 E` an over-estimate of `#S ^ k` whenever `E` is at least `#S ^ k / 16`. -/
def relativeHashEstimate {k : ℕ} (h : ∀ j, ι j → (Fin k → X) → Y j) (y : ∀ j, Y j)
    (S : Finset X) (ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j) : ℕ :=
  Nat.nthRoot k (16 * hashEstimate h y (Fintype.piFinset fun _ => S) ω)

variable [∀ j, Nonempty (ι j)]

/-- **The failure probability of Stockmeyer's estimate**: if every `h j` is a pairwise independent
hash family into a set of `2 ^ j` elements, with seeds from a nonempty type `ι j`, and
`#S ≤ 2 ^ n`, then for `2 r` independent uniform seeds per level `j ≤ n`, the estimate from the
majority answers fails to lie between `#S / 16` and `8 #S` with probability at most
`(n + 1) (8 / 9) ^ r`. -/
theorem dens_filter_not_hashEstimate_le (h : ∀ j, ι j → X → Y j) (y : ∀ j, Y j) (S : Finset X)
    (hh : ∀ j, IsPairwiseIndependentHash (h j)) (hY : ∀ j, Fintype.card (Y j) = 2 ^ j)
    (hS : #S ≤ 2 ^ n) :
    dens {ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j |
      ¬ (hashEstimate h y S ω ≤ 8 * #S ∧ #S ≤ 16 * hashEstimate h y S ω)} ≤
      (n + 1) * (8 / 9) ^ r := by
  refine (dens_le_dens fun ω hω => ?_).trans (dens_filter_not_answersCorrect_le h y S hh hY)
  simp only [mem_filter, mem_univ, true_and] at hω ⊢
  exact fun ha => hω ⟨ha.estimate_le, ha.le_estimate hS⟩

omit [∀ j, Nonempty (ι j)] in
/-- **Approximate counting with relative error**: if every `h j` is a pairwise independent hash
family on `k`-tuples into a set of `2 ^ j` elements, `#S ^ k ≤ 2 ^ n`, and
`128 ≤ (1 + 1 / p) ^ k`, then for `2 r` independent uniform seeds per level `j ≤ n`, the relative
estimate fails to lie between `#S` and `(1 + 1 / p) #S` with probability at most
`(n + 1) (8 / 9) ^ r`. -/
theorem dens_filter_not_relativeHashEstimate_le {k p : ℕ} (h : ∀ j, ι j → (Fin k → X) → Y j)
    (y : ∀ j, Y j) (S : Finset X) (hh : ∀ j, IsPairwiseIndependentHash (h j))
    (hY : ∀ j, Fintype.card (Y j) = 2 ^ j) (hS : #S ^ k ≤ 2 ^ n)
    (hp : 128 * p ^ k ≤ (p + 1) ^ k) :
    dens {ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j |
      ¬ (#S ≤ relativeHashEstimate h y S ω ∧
        p * relativeHashEstimate h y S ω ≤ (p + 1) * #S)} ≤ (n + 1) * (8 / 9) ^ r := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hp
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    have : ∀ j, Nonempty (ι j) := fun j => (hh j).nonempty (fun _ => x) (y j)
    have hcard : #(Fintype.piFinset fun _ : Fin k => S) = #S ^ k := Fintype.card_piFinset_const S k
    refine (dens_le_dens fun ω hω => ?_).trans
      (dens_filter_not_hashEstimate_le h y _ hh hY (hcard ▸ hS))
    simp only [mem_filter, mem_univ, true_and, hcard] at hω ⊢
    refine fun ⟨hle, hge⟩ => hω (le_nthRoot_and_mul_nthRoot_le hk hge ?_ hp)
    rw [show 128 = 16 * 8 by norm_num, mul_assoc]
    exact Nat.mul_le_mul_left 16 hle
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hS0 : S = ∅ := eq_empty_of_isEmpty S
    subst hS0
    have hpi : (Fintype.piFinset fun _ : Fin k => (∅ : Finset X)) = ∅ :=
      card_eq_zero.mp (by rw [Fintype.card_piFinset_const, card_empty, zero_pow hk])
    have hest : ∀ ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j,
        relativeHashEstimate h y ∅ ω = 0 := fun ω => by
      have ha : ¬ hashAnswer h y ∅ ω 0 := by
        rintro ⟨_, hr⟩
        simp at hr
      have hhe : hashEstimate h y ∅ ω = 0 := by
        simp only [hashEstimate, estimate, ha, ↓reduceIte]
      simp only [relativeHashEstimate, hpi, hhe, mul_zero]
      by_contra hne
      have h0 := (Nat.le_nthRoot_iff hk).mp (Nat.one_le_iff_ne_zero.mpr hne)
      simp at h0
    have hemp : ({ω : ∀ j : Fin (n + 1), Fin (2 * r) → ι j |
        ¬ (#(∅ : Finset X) ≤ relativeHashEstimate h y ∅ ω ∧
          p * relativeHashEstimate h y ∅ ω ≤ (p + 1) * #(∅ : Finset X))} : Finset _) = ∅ := by
      ext ω
      simp [hest ω]
    rw [hemp, dens_empty]
    positivity

/-- **Approximate counting with relative error and small failure probability**: under the
hypotheses of `dens_filter_not_relativeHashEstimate_le` with nonempty seed types `ι j`, for
`12 (n + 1 + t)` independent uniform seeds per level `j ≤ n`, the relative estimate lies between
`#S` and `(1 + 1 / p) #S` with probability at least `1 - 2 ^ (-t)`; at least `3 / 4` for
`t = 2`. -/
theorem one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate {k p : ℕ}
    (h : ∀ j, ι j → (Fin k → X) → Y j) (y : ∀ j, Y j) (S : Finset X)
    (hh : ∀ j, IsPairwiseIndependentHash (h j)) (hY : ∀ j, Fintype.card (Y j) = 2 ^ j)
    (hS : #S ^ k ≤ 2 ^ n) (hp : 128 * p ^ k ≤ (p + 1) ^ k) (t : ℕ) :
    1 - (2 ^ t)⁻¹ ≤ dens {ω : ∀ j : Fin (n + 1), Fin (2 * (6 * (n + 1 + t))) → ι j |
      #S ≤ relativeHashEstimate h y S ω ∧ p * relativeHashEstimate h y S ω ≤ (p + 1) * #S} := by
  have hbad := (dens_filter_not_relativeHashEstimate_le (r := 6 * (n + 1 + t)) h y S hh hY hS
    hp).trans (natCast_add_one_mul_le_inv_two_pow n t)
  rw [tsub_le_iff_right, ← dens_univ (α := ∀ j : Fin (n + 1), Fin (2 * (6 * (n + 1 + t))) → ι j),
    ← dens_filter_add_dens_filter_not_eq_dens (s := univ)
      (fun ω => #S ≤ relativeHashEstimate h y S ω ∧
        p * relativeHashEstimate h y S ω ≤ (p + 1) * #S)]
  exact add_le_add_right hbad _

end Hashing

/-! ### Affine hash families -/

/-- **Approximate counting with affine hashes and relative error**: for a set `S` of vectors in
`(ZMod 2) ^ m` and a precision `p ≠ 0`, with `7 p` copies, the affine hash families
`x ↦ A x + b` into `(ZMod 2) ^ j` applied to `7 p`-tuples of vectors read as vectors in
`(ZMod 2) ^ (7 p × m)`, for the levels `j ≤ 7 p m`, target `0`, and `12 (7 p m + 1 + t)`
independent seeds per level, the relative estimate lies between `#S` and `(1 + 1 / p) #S` with
probability at least `1 - 2 ^ (-t)`. -/
theorem one_sub_inv_two_pow_le_dens_filter_affineRelativeHashEstimate {m p : ℕ} (hp : p ≠ 0)
    (t : ℕ) (S : Finset (Fin m → ZMod 2)) :
    1 - (2 ^ t)⁻¹ ≤ dens {ω : ∀ j : Fin (7 * p * m + 1), Fin (2 * (6 * (7 * p * m + 1 + t))) →
        Matrix (Fin j) (Fin (7 * p) × Fin m) (ZMod 2) × (Fin j → ZMod 2) |
      #S ≤ relativeHashEstimate (fun _ A x => affineHash A (Function.uncurry x)) (fun _ => 0) S ω ∧
        p * relativeHashEstimate (fun _ A x => affineHash A (Function.uncurry x)) (fun _ => 0) S ω
          ≤ (p + 1) * #S} := by
  have hh : ∀ j, IsPairwiseIndependentHash fun (A : Matrix (Fin j) (Fin (7 * p) × Fin m) (ZMod 2) ×
      (Fin j → ZMod 2)) (x : Fin (7 * p) → Fin m → ZMod 2) => affineHash A (Function.uncurry x) :=
    fun _ => isPairwiseIndependentHash_affineHash.comp Function.uncurry_injective
  have hY : ∀ j, Fintype.card (Fin j → ZMod 2) = 2 ^ j := fun j => by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hS : #S ^ (7 * p) ≤ 2 ^ (7 * p * m) := by
    have : #S ≤ 2 ^ m := by
      simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin] using card_le_univ S
    calc #S ^ (7 * p) ≤ (2 ^ m) ^ (7 * p) := Nat.pow_le_pow_left this _
      _ = 2 ^ (7 * p * m) := by rw [← pow_mul, mul_comm]
  have hp' : 128 * p ^ (7 * p) ≤ (p + 1) ^ (7 * p) := two_pow_mul_pow_le_add_one_pow 7 hp
  exact one_sub_inv_two_pow_le_dens_filter_relativeHashEstimate
    (ι := fun j => Matrix (Fin j) (Fin (7 * p) × Fin m) (ZMod 2) × (Fin j → ZMod 2))
    (Y := fun j => Fin j → ZMod 2) _ _ _ hh hY hS hp' t

end Cslib.Probability.ApproximateCounting
