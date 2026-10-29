/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Log

/-!
# Distinct-position 3SUM as a finite list of three-set problems

Adapted from Anthropic's [FromNumbers.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/ChanHe/FromNumbers.lean), at
`formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. The three-set predicate and magnitude
bound come from its [Definitions.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/ChanHe/Definitions.lean) (Definition 2.1 of [ChanHe2020]); the label,
splitting and multiplicity definitions come from `PaperStatements.lean`.

These elementary frontend steps are additions in that formalization, not the prime-modulus and
heavy-element recursion of [ChanHe2020, Theorem 5.1]. They preserve multiplicities at distinct
positions. No native preprocessing or charged running-time bound is proved here.

## Main definitions

* `HasThreeSetSolution`: zero-sum elements selected from three finite sets.
* `Bdd`: an absolute-value bound on a finite set of integers.
* `labelBits`: a sufficient number of binary label digits.
* `IsInput`, `inputs`: the frontend relation and its finite executable enumeration.

## Main results

* `threeSum_iff_exists_mem_inputs`: distinct-position correctness for the finite list.
* `length_inputs`: exactly `2 * labelBits (2U)^2 + 2` entries, counting repetitions.
* `IsInput.bounds`: the cardinality and magnitude bounds on each entry.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum

open Finset

/-- 3SUM on three sets (Definition 2.1 of [ChanHe2020]), without requiring equal sizes. -/
def HasThreeSetSolution (S₁ S₂ S₃ : Finset ℤ) : Prop :=
  ∃ a ∈ S₁, ∃ b ∈ S₂, ∃ c ∈ S₃, a + b + c = 0

/-- Every element of `S` has magnitude at most `U`. -/
def Bdd (U : ℕ) (S : Finset ℤ) : Prop := ∀ x ∈ S, |x| ≤ (U : ℤ)

/-- Passing to a subset preserves the magnitude bound. -/
theorem Bdd.mono {U : ℕ} {S T : Finset ℤ} (h : Bdd U S) (hT : T ⊆ S) : Bdd U T :=
  fun x hx => h x (hT hx)

/-- A three-set solution remains a solution when each set grows. -/
theorem HasThreeSetSolution.mono {S₁ S₂ S₃ T₁ T₂ T₃ : Finset ℤ}
    (h : HasThreeSetSolution S₁ S₂ S₃) (h₁ : S₁ ⊆ T₁) (h₂ : S₂ ⊆ T₂) (h₃ : S₃ ⊆ T₃) :
    HasThreeSetSolution T₁ T₂ T₃ :=
  let ⟨a, ha, b, hb, c, hc, hs⟩ := h
  ⟨a, h₁ ha, b, h₂ hb, c, h₃ hc, hs⟩

/-- The number of bits sufficient for all labels in `[0, 2U]`. -/
def labelBits (U : ℕ) : ℕ := Nat.log 2 (2 * U) + 1

/-- The label of an element of `[-U, U]`: its value shifted into `[0, 2U]`. -/
def lab (U : ℕ) (x : ℤ) : ℕ := (x + U).toNat

/-- The elements of `S` whose label has the binary digit `v` at position `β`. -/
def splitA (U β : ℕ) (v : Bool) (S : Finset ℤ) : Finset ℤ := {x ∈ S | (lab U x).testBit β = v}

/-- The elements of `S` whose label has the other digit, `!v`, at position `β`, and the digit `w` at
position `β'`. For fixed `β`, `β'` and `v` the three sets `splitA U β v S`,
`splitB U β β' v false S` and `splitB U β β' v true S` are pairwise disjoint. -/
def splitB (U β β' : ℕ) (v w : Bool) (S : Finset ℤ) : Finset ℤ :=
  {x ∈ S | (lab U x).testBit β = !v ∧ (lab U x).testBit β' = w}

/-- The numbers `2a`, for the values `a ≠ 0` that occur at two positions or more. -/
def twiceSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ :=
  ({a ∈ univ.image x | a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a}}).image fun a => 2 * a

/-- The set `{0}` if 0 occurs at three positions or more, and the empty set otherwise.  This is the
one place where the reduction decides a case by itself: 0 occurs at three positions exactly when
`0, 0, 0` is a solution. -/
def zeroSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ := if 3 ≤ #{i : Fin n | x i = 0} then {0} else ∅

section distinct

variable {U : ℕ} {S : Finset ℤ}

/-- On `[-U, U]` the label of `x` is `x + U`. -/
private theorem lab_cast {x : ℤ} (hx : |x| ≤ (U : ℤ)) : ((lab U x : ℕ) : ℤ) = x + U :=
  Int.toNat_of_nonneg (by have := (abs_le.mp hx).1; omega)

/-- The label of an element of `[-U, U]` has at most `labelBits U` binary digits. -/
private theorem lab_lt {x : ℤ} (hx : |x| ≤ (U : ℤ)) : lab U x < 2 ^ labelBits U := by
  have := lab_cast hx
  have := (abs_le.mp hx).2
  exact (by omega : lab U x ≤ 2 * U).trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

/-- The labels of two different elements of `[-U, U]` differ in one of their `labelBits U` lowest
binary
digits. -/
private theorem exists_testBit_lab_ne {x y : ℤ} (hx : |x| ≤ (U : ℤ)) (hy : |y| ≤ (U : ℤ))
    (hne : x ≠ y) : ∃ β < labelBits U, (lab U x).testBit β ≠ (lab U y).testBit β := by
  have hlab : lab U x ≠ lab U y := fun h => hne (by have := lab_cast hx; have := lab_cast hy; omega)
  obtain ⟨β, hβ⟩ := Nat.exists_testBit_ne_of_ne hlab
  -- from digit `labelBits U` on, all digits of both labels are 0
  refine ⟨β, lt_of_not_ge fun hΛ => hβ ?_, hβ⟩
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hΛ
  rw [Nat.testBit_eq_false_of_lt ((lab_lt hx).trans_le hpow),
    Nat.testBit_eq_false_of_lt ((lab_lt hy).trans_le hpow)]

/-- Let `x + y + z = 0` in `S`.  If the label of `x` differs from those of `y` and `z` in digit `β`,
and `y ≠ z`, then one of the three-set inputs obtained by splitting `S` has a solution. -/
private theorem exists_split_of_testBit (h : Bdd U S) {x y z : ℤ} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) {β : ℕ} (hβ : β < labelBits U) (hxy : (lab U y).testBit β = !(lab U x).testBit β)
    (hxz : (lab U z).testBit β = !(lab U x).testBit β) (hyz : y ≠ z) (hs : x + y + z = 0) :
    ∃ β < labelBits U, ∃ β' < labelBits U, ∃ v : Bool,
      HasThreeSetSolution (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true S) := by
  obtain ⟨β', hβ', hne⟩ := exists_testBit_lab_ne (h y hy) (h z hz) hyz
  refine ⟨β, hβ, β', hβ', (lab U x).testBit β, x, mem_filter.mpr ⟨hx, rfl⟩, ?_⟩
  cases hyβ' : (lab U y).testBit β'
  · exact ⟨y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩,
      z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩, hs⟩
  · exact ⟨z, mem_filter.mpr ⟨hz, hxz, by simpa [hyβ'] using hne.symm⟩,
      y, mem_filter.mpr ⟨hy, hxy, hyβ'⟩, by omega⟩

/-- A set has three distinct elements with sum 0 iff one of the `2 (labelBits U)²` three-set inputs,
obtained by splitting it by two binary digits, has a solution. -/
theorem distinct_iff_split (h : Bdd U S) :
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ↔
      ∃ β < labelBits U, ∃ β' < labelBits U, ∃ v : Bool,
        HasThreeSetSolution (splitA U β v S) (splitB U β β' v false S) (splitB U β β' v true
      S) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩
    obtain ⟨β, hβ, hbit⟩ := exists_testBit_lab_ne (h a ha) (h b hb) hab
    -- in digit `β` the third element agrees with `b` or with `a`
    by_cases hcb : (lab U c).testBit β = (lab U b).testBit β
    · exact exists_split_of_testBit h ha hb hc hβ (Bool.eq_not_of_ne hbit.symm)
        (hcb.trans (Bool.eq_not_of_ne hbit.symm)) hbc hs
    · exact exists_split_of_testBit h hb ha hc hβ (Bool.eq_not_of_ne hbit)
        (Bool.eq_not_of_ne hcb) hac (by omega)
  · rintro ⟨β, -, β', -, v, a, ha, b, hb, c, hc, hs⟩
    obtain ⟨haS, haβ⟩ := mem_filter.mp ha
    obtain ⟨hbS, hbβ, hbβ'⟩ := mem_filter.mp hb
    obtain ⟨hcS, hcβ, hcβ'⟩ := mem_filter.mp hc
    refine ⟨a, haS, b, hbS, c, hcS, ?_, ?_, ?_, hs⟩
    · rintro rfl
      simp [haβ] at hbβ
    · rintro rfl
      simp [hbβ'] at hcβ'
    · rintro rfl
      simp [haβ] at hcβ

end distinct

/-! ## Positions instead of values: solutions that repeat a value -/

section positions

variable {n : ℕ} {x : Fin n → ℤ}

/-- There is a solution that repeats a value: `a, a, -2a` with `a ≠ 0`, or `0, 0, 0`, at different
positions. -/
def Degenerate (x : Fin n → ℤ) : Prop :=
  (∃ a : ℤ, a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a} ∧ ∃ k, x k = -2 * a) ∨ 3 ≤ #{i : Fin n | x i = 0}

/-- A solution at three different positions, two of which hold the same value, repeats a value. -/
private theorem degenerate_of_eq {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : x i = x j) (hs : x i + x j + x k = 0) : Degenerate x := by
  by_cases h0 : x i = 0
  · exact .inr (two_lt_card.mpr ⟨i, by simpa using h0, j, by simpa using he ▸ h0,
      k, by simp only [mem_filter, mem_univ, true_and]; omega, hij, hik, hjk⟩)
  · exact .inl ⟨x i, h0, one_lt_card.mpr ⟨i, by simp, j, by simp [he], hij⟩, k, by omega⟩

/-- Three different positions with sum 0: either the three values are distinct, or the solution
repeats a value. -/
theorem threeSum_iff_distinct_or_degenerate (x : Fin n → ℤ) :
    HasSolution x ↔
      (∃ a ∈ univ.image x, ∃ b ∈ univ.image x, ∃ c ∈ univ.image x,
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a + b + c = 0) ∨ Degenerate x := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, hik, hs⟩
    by_cases hxij : x i = x j
    · exact .inr (degenerate_of_eq hij hik hjk hxij hs)
    by_cases hxjk : x j = x k
    · exact .inr (degenerate_of_eq hjk hij.symm hik.symm hxjk (by omega))
    by_cases hxik : x i = x k
    · exact .inr (degenerate_of_eq hik hij hjk.symm hxik (by omega))
    · exact .inl ⟨x i, by simp, x j, by simp, x k, by simp, hxij, hxjk, hxik, hs⟩
  · rintro (⟨a, ha, b, hb, c, hc, hab, hbc, hac, hs⟩ | ⟨a, ha0, h2, k, hk⟩ | h3)
    · obtain ⟨i, -, rfl⟩ := mem_image.mp ha
      obtain ⟨j, -, rfl⟩ := mem_image.mp hb
      obtain ⟨k, -, rfl⟩ := mem_image.mp hc
      exact ⟨i, j, k, fun e => hab (e ▸ rfl), fun e => hbc (e ▸ rfl), fun e => hac (e ▸ rfl), hs⟩
    · obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp h2
      simp only [mem_filter, mem_univ, true_and] at hi hj
      have hne : ∀ t : Fin n, x t = a → t ≠ k := by
        rintro t ht rfl
        omega
      exact ⟨i, j, k, hij, hne j hj, hne i hi, by omega⟩
    · obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := two_lt_card.mp h3
      simp only [mem_filter, mem_univ, true_and] at hi hj hk
      exact ⟨i, j, k, hij, hjk, hik, by omega⟩

/-- There is a solution that repeats a value iff one of two three-set inputs has a solution.  The
first input leaves the search for `-2a` to the reduction.  The second already contains the answer
for `0, 0, 0`; see `zeroSet`. -/
theorem degenerate_iff (x : Fin n → ℤ) :
    Degenerate x ↔
      HasThreeSetSolution (twiceSet x) {0} (univ.image x) ∨ HasThreeSetSolution (zeroSet x)
      {0} {0} := by
  refine or_congr ⟨?_, ?_⟩ ⟨fun h3 => ?_, ?_⟩
  · rintro ⟨a, ha0, h2, k, hk⟩
    obtain ⟨i, hi, -⟩ := one_lt_card.mp h2
    have ha : a ∈ univ.image x := mem_image.mpr ⟨i, mem_univ i, (mem_filter.mp hi).2⟩
    exact ⟨2 * a, mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, ha0, h2⟩, rfl⟩, 0, mem_singleton_self 0,
      x k, mem_image_of_mem x (mem_univ k), by omega⟩
  · rintro ⟨_, ha', b, hb, _, hc, hs⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
    obtain ⟨-, ha0, h2⟩ := mem_filter.mp ha
    obtain ⟨k, -, rfl⟩ := mem_image.mp hc
    rw [mem_singleton.mp hb] at hs
    exact ⟨a, ha0, h2, k, by omega⟩
  · rw [zeroSet, ite_eq_left h3]
    exact ⟨0, mem_singleton_self 0, 0, mem_singleton_self 0, 0, mem_singleton_self 0, rfl⟩
  · rintro ⟨a, ha, -⟩
    by_contra h3
    rw [zeroSet, ite_eq_right h3] at ha
    exact notMem_empty a ha

end positions




section inputs

variable {n U : ℕ} {x : Fin n → ℤ}

/-- The values of `x` are bounded by `2U`. -/
private theorem bdd_image (hx : ∀ i, |x i| ≤ (U : ℤ)) : Bdd (2 * U) (univ.image x) := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  exact (hx i).trans (by omega)

/-- The elements of `twiceSet x` are bounded by `2U`. -/
theorem bdd_twiceSet (hx : ∀ i, |x i| ≤ (U : ℤ)) : Bdd (2 * U) (twiceSet x) := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  obtain ⟨i, -, rfl⟩ := mem_image.mp (mem_filter.mp ha).1
  have := abs_le.mp (hx i)
  rw [abs_le]
  constructor <;> omega

/-- The set `{0}` is bounded by anything. -/
theorem bdd_zero (U : ℕ) : Bdd U {0} := by
  intro a ha
  rw [mem_singleton.mp ha, abs_zero]
  omega

/-- The set `zeroSet x` is bounded by anything. -/
theorem bdd_zeroSet (U : ℕ) (x : Fin n → ℤ) : Bdd U (zeroSet x) := by
  unfold zeroSet
  split_ifs
  · exact bdd_zero U
  · exact fun a ha => absurd ha (notMem_empty a)

/-- `n` numbers have at most `n` values. -/
private theorem card_image_univ_le (x : Fin n → ℤ) : #(univ.image x) ≤ n :=
  card_image_le.trans_eq (card_fin n)

/-- `twiceSet x` has at most `n` elements. -/
theorem card_twiceSet_le (x : Fin n → ℤ) : #(twiceSet x) ≤ n :=
  card_image_le.trans ((card_filter_le _ _).trans (card_image_univ_le x))

/-- `zeroSet x` has at most one element. -/
theorem card_zeroSet_le (x : Fin n → ℤ) : #(zeroSet x) ≤ 1 := by
  unfold zeroSet
  split_ifs <;> simp

/-- The three-set inputs of the frontend. -/
inductive IsInput (U : ℕ) (x : Fin n → ℤ) : Finset ℤ → Finset ℤ → Finset ℤ → Prop
  /-- The set of values, split by two binary digits: for the solutions with three distinct
  values. -/
  | split {β β' : ℕ} (hβ : β < labelBits (2 * U)) (hβ' : β' < labelBits (2 * U)) (v : Bool) :
    IsInput U x (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
      (splitB (2 * U) β β' v true (univ.image x))
  /-- For the solutions `a, a, -2a`. -/
  | twice : IsInput U x (twiceSet x) {0} (univ.image x)
  /-- For the solution `0, 0, 0`. -/
  | zero : IsInput U x (zeroSet x) {0} {0}

/-- A property holds for one of the three-set inputs iff it holds for one of the splittings or for
one of the two further inputs. -/
private theorem exists_isInput_iff (P : Finset ℤ → Finset ℤ → Finset ℤ → Prop) :
    (∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ P T₁ T₂ T₃) ↔
      (∃ β < labelBits (2 * U), ∃ β' < labelBits (2 * U), ∃ v : Bool,
        P (splitA (2 * U) β v (univ.image x)) (splitB (2 * U) β β' v false (univ.image x))
          (splitB (2 * U) β β' v true (univ.image x))) ∨
      P (twiceSet x) {0} (univ.image x) ∨ P (zeroSet x) {0} {0} := by
  constructor
  · rintro ⟨_, _, _, ⟨hβ, hβ', v⟩ | _ | _, h⟩
    · exact .inl ⟨_, hβ, _, hβ', v, h⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (⟨β, hβ, β', hβ', v, h⟩ | h | h)
    · exact ⟨_, _, _, .split hβ hβ' v, h⟩
    · exact ⟨_, _, _, .twice, h⟩
    · exact ⟨_, _, _, .zero, h⟩

/-- Three entries of `x` at different positions sum to 0 iff one of the three-set inputs has a
solution. -/
theorem threeSum_iff_exists_input (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    HasSolution x ↔ ∃ T₁ T₂ T₃, IsInput U x T₁ T₂ T₃ ∧ HasThreeSetSolution T₁ T₂ T₃ := by
  rw [threeSum_iff_distinct_or_degenerate, distinct_iff_split (bdd_image hx), degenerate_iff,
    exists_isInput_iff]

/-- Each frontend input consists of sets of at most `n` elements, bounded in magnitude by `2U`.
The hypothesis `1 ≤ n` accounts for the singleton `{0}` used by the repeated-value cases. -/
theorem IsInput.bounds (hn : 1 ≤ n) (hx : ∀ i, |x i| ≤ (U : ℤ)) {T₁ T₂ T₃ : Finset ℤ}
    (h : IsInput U x T₁ T₂ T₃) :
    #T₁ ≤ n ∧ #T₂ ≤ n ∧ #T₃ ≤ n ∧ Bdd (2 * U) T₁ ∧ Bdd (2 * U) T₂ ∧ Bdd (2 * U) T₃ := by
  have hb := bdd_image hx
  have hc := card_image_univ_le x
  have hc0 : #({0} : Finset ℤ) ≤ n := hn
  cases h with
  | split hβ hβ' v =>
    exact ⟨(card_filter_le _ _).trans hc, (card_filter_le _ _).trans hc,
      (card_filter_le _ _).trans hc, hb.mono (filter_subset _ _), hb.mono (filter_subset _ _),
      hb.mono (filter_subset _ _)⟩
  | twice => exact ⟨card_twiceSet_le x, hc0, hc, bdd_twiceSet hx, bdd_zero _, hb⟩
  | zero => exact ⟨(card_zeroSet_le x).trans hn, hc0, hc0, bdd_zeroSet _ x, bdd_zero _, bdd_zero _⟩

/-- Enumerate all binary-digit splits and the two repeated-value inputs. -/
def inputs (U : ℕ) (x : Fin n → ℤ) : List (Finset ℤ × Finset ℤ × Finset ℤ) :=
  ((List.range (labelBits (2 * U))).flatMap fun β =>
    (List.range (labelBits (2 * U))).flatMap fun β' => [false, true].map fun v =>
      (splitA (2 * U) β v (univ.image x), splitB (2 * U) β β' v false (univ.image x),
        splitB (2 * U) β β' v true (univ.image x))) ++
    [(twiceSet x, {0}, univ.image x), (zeroSet x, {0}, {0})]

/-- Membership in the executable list is exactly the frontend input relation. -/
theorem mem_inputs_iff {T₁ T₂ T₃ : Finset ℤ} :
    (T₁, T₂, T₃) ∈ inputs U x ↔ IsInput U x T₁ T₂ T₃ := by
  constructor
  · intro h
    simp only [inputs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ⟨β, hβ, β', hβ', v, -, h⟩ | h | h
    · cases h
      exact .split hβ hβ' v
    · cases h
      exact .twice
    · cases h
      exact .zero
  · intro h
    cases h with
    | split hβ hβ' v =>
      simp only [inputs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
      exact .inl ⟨_, hβ, _, hβ', v, by cases v <;> simp, rfl⟩
    | twice => simp [inputs]
    | zero => simp [inputs]

/-- The frontend enumerates exactly `2 (labelBits (2U))² + 2` inputs, counting repetitions. -/
theorem length_inputs (U : ℕ) (x : Fin n → ℤ) :
    (inputs U x).length = 2 * labelBits (2 * U) ^ 2 + 2 := by
  simp [inputs, List.length_flatMap, pow_two, Nat.mul_comm, Nat.mul_left_comm]

/-- Distinct-position 3SUM is equivalent to a yes-instance in the finite frontend list. -/
theorem threeSum_iff_exists_mem_inputs (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    HasSolution x ↔ ∃ T ∈ inputs U x, HasThreeSetSolution T.1 T.2.1 T.2.2 := by
  rw [threeSum_iff_exists_input hx]
  constructor
  · rintro ⟨T₁, T₂, T₃, hT, hs⟩
    exact ⟨(T₁, T₂, T₃), mem_inputs_iff.mpr hT, hs⟩
  · rintro ⟨⟨T₁, T₂, T₃⟩, hT, hs⟩
    exact ⟨T₁, T₂, T₃, mem_inputs_iff.mp hT, hs⟩


end inputs

end Cslib.Algorithms.ThreeSum
