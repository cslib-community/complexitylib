/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Probability.HashFamily.MultiplyShift
public import Complexity.Probability.KWiseIndependent.Coupling
public import Complexity.Probability.KWiseIndependent.Restriction
public import Complexity.Probability.KWiseIndependent.Trinomial
public import Complexity.Probability.PMF.Map
public import Complexity.Probability.Uniform
public import Complexity.Probability.UniversalHash

/-!
# Universe-reduced `k`-wise independent hashing via multiply-shift and trinomial polynomials

To hash a `w₀`-bit universe `Fin U` (`U ≤ 2 ^ w₀`) into `Fin (2 ^ b')` in $O(1)$ Word-RAM
instructions without any polynomial universe restriction $U \le n^c$, we compose two stages:

1. **Dietzfelbinger multiply-shift universe reduction** (`multiplyShiftReduced U w₀ (3 * b)`),
   which maps keys in `Fin U` into `Fin (2 ^ min w₀ (3 * b))` using a single `(w₀ - 1)`-bit
   odd-multiplier seed `α ∈ Fin (2 ^ (w₀ - 1))`
   [Dietzfelbinger et al.][DietzfelbingerHagerupKatajainenPenttonen1997].
2. **Degree-`< k` trinomial binary-field polynomial evaluation** (`trinomialPolyHash`), which maps
   the reduced key in `Fin (2 ^ min w₀ (3 * b))` into `Fin (2 ^ b')` using `k` field coefficients in
   `TrinomialField (reducedTrinomialStep w₀ b b')` [Vadhan, Section 3.5.5][Vadhan2012];
   [Wegman and Carter][WegmanCarter1981].

Whenever the reduction stage is injective on a key set `S : Finset (Fin U)`, the two-stage hash
family is exact `k`-wise independent on `S` (`isKWiseIndependentHash_reducedPolyHash_of_injOn`). By
2-universality of multiply-shift (`isUniversalHash_multiplyShift`) when `3 * b ≤ w₀` and exact
bijectivity of odd multiplication modulo `2 ^ w₀` when `w₀ < 3 * b`, the probability that a uniform
reduction seed `α` fails to be injective on `S` is at most
`(#S * (#S - 1) : ℝ≥0∞) / 2 ^ (3 * b) ≤ (#S ^ 2 : ℝ≥0∞) / 2 ^ (3 * b)`
(`toOuterMeasure_not_injOn_multiplyShiftReduced_le`).

## Main definitions

* `Cslib.Probability.multiplyShiftReduced`: Dietzfelbinger multiply-shift reduction from `Fin U` to
  `Fin (2 ^ min w₀ R)`.
* `Cslib.Probability.reducedTargetBits`, `Cslib.Probability.reducedTrinomialStep`,
  `Cslib.Probability.reducedTrinomialDeg`: trinomial field target bit-width, step, and degree
  parameters for reduced `min w₀ (3 * b)`-bit keys and `b'`-bit outputs.
* `Cslib.Probability.ReducedPolySeed`, `Cslib.Probability.reducedPolyHash`: two-stage seed type and
  hash family from `Fin U` to `Fin (2 ^ b')`.
* `Cslib.Probability.reducedGoodTop`: the finset of top-level multiply-shift seeds that are
  injective on a given finite key set `S`.

## Main results

* `Cslib.Probability.injective_multiplyShiftReduced_of_le`: when `w₀ ≤ R` and `U ≤ 2 ^ w₀`,
  `multiplyShiftReduced U w₀ R α` is injective on `Fin U` for every seed `α`.
* `Cslib.Probability.card_not_injOn_multiplyShiftReduced_le`,
  `Cslib.Probability.toOuterMeasure_not_injOn_multiplyShiftReduced_le`: union bound on the number
  and probability of reduction seeds that fail to be injective on `S : Finset (Fin U)`.
* `Cslib.Probability.isKWiseIndependentHash_reducedPolyHash_of_injOn`: for any fixed reduction seed
  `α` that is injective on `S`, the restricted polynomial family is `k`-wise independent on `S`.
* `Cslib.Probability.coupledWithin_reducedPolyHash_restrict`: for any `T : Finset (Fin U)` with
  `#T ≤ k`, the restriction of `reducedPolyHash` to `T` under a uniform seed is coupled within
  `(#T * (#T - 1) : ℝ≥0∞) / 2 ^ (3 * b)` of `PMF.uniformOfFintype (T → Fin (2 ^ b'))`.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm for
  the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5.5][Vadhan2012]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.Probability

open Finset Cslib.Probability.PMF
open scoped BigOperators ENNReal Cslib.Probability.PMF

/-! ## Multiply-shift universe reduction to `min w₀ R` bits -/

/-- For any `w₀ R a : ℕ`, `(a % 2 ^ w₀) / 2 ^ (w₀ - R) < 2 ^ min w₀ R`. -/
theorem mod_two_pow_div_lt_min (w₀ R a : ℕ) :
    a % 2 ^ w₀ / 2 ^ (w₀ - R) < 2 ^ min w₀ R := by
  rcases le_total w₀ R with hle | hle
  · rw [Nat.min_eq_left hle]
    exact (Nat.div_le_self _ _).trans_lt (Nat.mod_lt _ (by positivity))
  · rw [Nat.min_eq_right hle]
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, Nat.sub_add_cancel hle]
    exact Nat.mod_lt _ (by positivity)

/-- Dietzfelbinger multiply-shift hash mapping `u : Fin U` into `Fin (2 ^ min w₀ R)` for a seed
`α : Fin (2 ^ (w₀ - 1))`. -/
@[expose] def multiplyShiftReduced (U w₀ R : ℕ) (α : Fin (2 ^ (w₀ - 1))) (u : Fin U) :
    Fin (2 ^ min w₀ R) :=
  ⟨(2 * α.val + 1) * u.val % 2 ^ w₀ / 2 ^ (w₀ - R),
    mod_two_pow_div_lt_min w₀ R ((2 * α.val + 1) * u.val)⟩

@[simp]
theorem val_multiplyShiftReduced (U w₀ R : ℕ) (α : Fin (2 ^ (w₀ - 1))) (u : Fin U) :
    (multiplyShiftReduced U w₀ R α u).val =
      (2 * α.val + 1) * u.val % 2 ^ w₀ / 2 ^ (w₀ - R) :=
  rfl

/-- When `w₀ ≤ R` and `U ≤ 2 ^ w₀`, `multiplyShiftReduced U w₀ R α` is `(2 * α + 1) * u % 2 ^ w₀`,
which is injective on `Fin U` for every seed `α`. -/
theorem injective_multiplyShiftReduced_of_le {U w₀ R : ℕ} (hU : U ≤ 2 ^ w₀) (hle : w₀ ≤ R)
    (α : Fin (2 ^ (w₀ - 1))) :
    Function.Injective (multiplyShiftReduced U w₀ R α) := by
  intro x y hxy
  have hval : (2 * α.val + 1) * x.val % 2 ^ w₀ / 2 ^ (w₀ - R) =
      (2 * α.val + 1) * y.val % 2 ^ w₀ / 2 ^ (w₀ - R) :=
    congrArg Fin.val hxy
  have hsub : w₀ - R = 0 := Nat.sub_eq_zero_of_le hle
  rw [hsub, pow_zero, Nat.div_one, Nat.div_one] at hval
  have hodd : Odd (2 * α.val + 1) := odd_two_mul_add_one α.val
  have hcop : Nat.Coprime (2 ^ w₀) (2 * α.val + 1) :=
    Nat.Coprime.pow_left w₀ (Nat.coprime_comm.mp hodd.coprime_two_right)
  have hmod : (2 * α.val + 1) * x.val ≡ (2 * α.val + 1) * y.val [MOD 2 ^ w₀] := hval
  have hxy_mod : x.val ≡ y.val [MOD 2 ^ w₀] :=
    Nat.ModEq.cancel_left_of_coprime hcop hmod
  have hx_lt : x.val < 2 ^ w₀ := lt_of_lt_of_le x.isLt hU
  have hy_lt : y.val < 2 ^ w₀ := lt_of_lt_of_le y.isLt hU
  change x.val % 2 ^ w₀ = y.val % 2 ^ w₀ at hxy_mod
  rw [Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at hxy_mod
  exact Fin.ext hxy_mod

/-- For any distinct `x, y : Fin U` (`U ≤ 2 ^ w₀`, `0 < w₀`), the number of seeds
`α : Fin (2 ^ (w₀ - 1))` for which
`multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y`
is at most `2 ^ (w₀ - R)` when `R ≤ w₀`, and `0` when `w₀ < R`. -/
theorem card_multiplyShiftReduced_eq_le {U w₀ R : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {x y : Fin U} (hxy : x ≠ y) :
    #{α : Fin (2 ^ (w₀ - 1)) |
      multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} * 2 ^ R ≤ 2 ^ w₀ := by
  rcases le_or_gt R w₀ with hle | hlt
  · let x' : Fin (2 ^ w₀) := ⟨x.val, lt_of_lt_of_le x.isLt hU⟩
    let y' : Fin (2 ^ w₀) := ⟨y.val, lt_of_lt_of_le y.isLt hU⟩
    have hxy' : x' ≠ y' := by
      intro h
      apply hxy
      ext
      exact congrArg (Fin.val : Fin (2 ^ w₀) → ℕ) h
    have hcard : #{α : Fin (2 ^ (w₀ - 1)) |
        multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} ≤ 2 ^ (w₀ - R) := by
      have hsub : #{α : Fin (2 ^ (w₀ - 1)) |
          multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} =
        #{α : Fin (2 ^ (w₀ - 1)) |
          multiplyShift w₀ R α x' = multiplyShift w₀ R α y'} := by
        refine congrArg card (filter_congr fun α _ => ?_)
        exact Fin.ext_iff
      rw [hsub]
      exact card_filter_multiplyShift_eq_le hw₀ hle hxy'
    calc
      #{α : Fin (2 ^ (w₀ - 1)) |
          multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} * 2 ^ R
        ≤ 2 ^ (w₀ - R) * 2 ^ R := Nat.mul_le_mul_right (2 ^ R) hcard
      _ = 2 ^ w₀ := by rw [← pow_add, Nat.sub_add_cancel hle]
  · have hemp : ({α : Fin (2 ^ (w₀ - 1)) |
        multiplyShiftReduced U w₀ R α x = multiplyShiftReduced U w₀ R α y} :
        Finset (Fin (2 ^ (w₀ - 1)))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro α _ hcoll
      exact hxy (injective_multiplyShiftReduced_of_le hU (le_of_lt hlt) α hcoll)
    rw [hemp, card_empty, zero_mul]
    exact Nat.zero_le _

/-- Finset of top-level multiply-shift seeds `α : Fin (2 ^ (w₀ - 1))` that are injective on
`S : Finset (Fin U)`. -/
@[expose] noncomputable def reducedGoodTop (U w₀ R : ℕ) (S : Finset (Fin U)) :
    Finset (Fin (2 ^ (w₀ - 1))) :=
  open Classical in
  univ.filter fun α => Set.InjOn (multiplyShiftReduced U w₀ R α) (S : Set (Fin U))

theorem mem_reducedGoodTop {U w₀ R : ℕ} {S : Finset (Fin U)} {α : Fin (2 ^ (w₀ - 1))} :
    α ∈ reducedGoodTop U w₀ R S ↔
      Set.InjOn (multiplyShiftReduced U w₀ R α) (S : Set (Fin U)) := by
  simp only [reducedGoodTop, mem_filter, mem_univ, true_and]

/-- **Counting union bound on non-injective multiply-shift seeds**:
for any `S : Finset (Fin U)` (`U ≤ 2 ^ w₀`, `0 < w₀`), the number of seeds
`α : Fin (2 ^ (w₀ - 1))` on which `multiplyShiftReduced U w₀ R α` fails to be injective on `S`
satisfies `#(univ \ reducedGoodTop U w₀ R S) * 2 ^ R ≤ (#S * (#S - 1)) * 2 ^ (w₀ - 1)`. -/
theorem card_not_injOn_multiplyShiftReduced_le {U w₀ R : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    (S : Finset (Fin U)) :
    #(univ \ reducedGoodTop U w₀ R S) * 2 ^ R ≤ (#S * (#S - 1)) * 2 ^ (w₀ - 1) := by
  classical
  -- Each non-injective seed collides on some strictly ordered pair of distinct keys of `S`.
  let pairs := (S ×ˢ S).filter fun p : Fin U × Fin U => p.1 < p.2
  have hsub : univ \ reducedGoodTop U w₀ R S ⊆
      pairs.biUnion (fun p => univ.filter fun α : Fin (2 ^ (w₀ - 1)) =>
        multiplyShiftReduced U w₀ R α p.1 = multiplyShiftReduced U w₀ R α p.2) := by
    intro α hα
    rw [mem_sdiff, mem_reducedGoodTop] at hα
    have hnot : ¬ Set.InjOn (multiplyShiftReduced U w₀ R α) (S : Set (Fin U)) := hα.2
    rw [Set.InjOn] at hnot
    push Not at hnot
    obtain ⟨x, hx, y, hy, hcoll, hne⟩ := hnot
    rw [mem_biUnion]
    rcases hne.lt_or_gt with hlt | hgt
    · refine ⟨(x, y), ?_, ?_⟩
      · simp only [pairs, mem_filter, mem_product]
        exact ⟨⟨hx, hy⟩, hlt⟩
      · simp only [mem_filter, mem_univ, true_and, hcoll]
    · refine ⟨(y, x), ?_, ?_⟩
      · simp only [pairs, mem_filter, mem_product]
        exact ⟨⟨hy, hx⟩, hgt⟩
      · simp only [mem_filter, mem_univ, true_and, hcoll.symm]
  -- There are `#S.choose 2` such pairs, and `2 * n.choose 2 = n * (n - 1)`.
  have hcard_pairs : 2 * #pairs = #S * (#S - 1) := by
    rw [card_product_filter_lt, Nat.choose_two_right,
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _)]
  have hpow_w₀ : 2 ^ w₀ = 2 * 2 ^ (w₀ - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hw₀, pow_succ']
  calc
    #(univ \ reducedGoodTop U w₀ R S) * 2 ^ R
      ≤ (#(pairs.biUnion fun p => univ.filter fun α : Fin (2 ^ (w₀ - 1)) =>
          multiplyShiftReduced U w₀ R α p.1 = multiplyShiftReduced U w₀ R α p.2)) * 2 ^ R :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ p ∈ pairs, #{α : Fin (2 ^ (w₀ - 1)) |
          multiplyShiftReduced U w₀ R α p.1 = multiplyShiftReduced U w₀ R α p.2}) * 2 ^ R :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ p ∈ pairs, #{α : Fin (2 ^ (w₀ - 1)) |
          multiplyShiftReduced U w₀ R α p.1 = multiplyShiftReduced U w₀ R α p.2} * 2 ^ R :=
        sum_mul _ _ _
    _ ≤ ∑ _p ∈ pairs, 2 ^ w₀ := by
        refine sum_le_sum fun p hp => ?_
        simp only [pairs, mem_filter] at hp
        exact card_multiplyShiftReduced_eq_le hw₀ hU hp.2.ne
    _ = #pairs * 2 ^ w₀ := by rw [sum_const, smul_eq_mul]
    _ = (2 * #pairs) * 2 ^ (w₀ - 1) := by rw [hpow_w₀]; ring
    _ = (#S * (#S - 1)) * 2 ^ (w₀ - 1) := by rw [hcard_pairs]

/-- **Probability bound on non-injective multiply-shift seeds**:
under a uniform seed `α ← PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))`, the probability that
`multiplyShiftReduced U w₀ R α` fails to be injective on `S : Finset (Fin U)` is at most
`(#S * (#S - 1) : ℝ≥0∞) / 2 ^ R`. -/
theorem toOuterMeasure_not_injOn_multiplyShiftReduced_le {U w₀ R : ℕ} (hw₀ : 0 < w₀)
    (hU : U ≤ 2 ^ w₀) (S : Finset (Fin U)) :
    (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))).toOuterMeasure
      {α | ¬ Set.InjOn (multiplyShiftReduced U w₀ R α) (S : Set (Fin U))} ≤
      ((#S * (#S - 1) : ℕ) : ℝ≥0∞) / 2 ^ R := by
  classical
  have hset : {α : Fin (2 ^ (w₀ - 1)) |
      ¬ Set.InjOn (multiplyShiftReduced U w₀ R α) (S : Set (Fin U))} =
      ((univ \ reducedGoodTop U w₀ R S : Finset (Fin (2 ^ (w₀ - 1)))) :
        Set (Fin (2 ^ (w₀ - 1)))) := by
    ext α
    simp only [Set.mem_ofPred_eq, mem_coe, mem_sdiff, mem_univ, mem_reducedGoodTop, true_and]
  rw [hset, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, sum_const, nsmul_eq_mul,
    ← div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]
  have hcard := card_not_injOn_multiplyShiftReduced_le (R := R) hw₀ hU S
  have hcast : ((#(univ \ reducedGoodTop U w₀ R S) : ℝ≥0∞) * (2 ^ R : ℝ≥0∞)) ≤
      ((#S * (#S - 1) : ℕ) : ℝ≥0∞) * (2 ^ (w₀ - 1) : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hpow_ne_zero : (2 ^ (w₀ - 1) : ℝ≥0∞) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ (w₀ - 1) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hR_ne_zero : (2 ^ R : ℝ≥0∞) ≠ 0 := by positivity
  have hR_ne_top : (2 ^ R : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [ENNReal.div_le_iff_le_mul (Or.inl hpow_ne_zero) (Or.inl hpow_ne_top)]
  calc (#(univ \ reducedGoodTop U w₀ R S) : ℝ≥0∞)
      = (#(univ \ reducedGoodTop U w₀ R S) : ℝ≥0∞) * (2 ^ R : ℝ≥0∞) / (2 ^ R : ℝ≥0∞) :=
        (ENNReal.mul_div_cancel_right hR_ne_zero hR_ne_top).symm
    _ ≤ ((#S * (#S - 1) : ℕ) : ℝ≥0∞) * (2 ^ (w₀ - 1) : ℝ≥0∞) / (2 ^ R : ℝ≥0∞) :=
        ENNReal.div_le_div_right hcast _
    _ = ((#S * (#S - 1) : ℕ) : ℝ≥0∞) / (2 ^ R : ℝ≥0∞) * (2 ^ (w₀ - 1) : ℝ≥0∞) := by
        rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]

/-! ## Two-stage reduced trinomial polynomial hash family -/

/-- Target bit-width `max (min w₀ (3 * b)) (max b' 1)` for the trinomial field stage. -/
@[expose] def reducedTargetBits (w₀ b b' : ℕ) : ℕ :=
  max (min w₀ (3 * b)) (max b' 1)

/-- Trinomial step parameter `t = trinomialStepAux (reducedTargetBits w₀ b b')` for the
second-stage polynomial hash over reduced `min w₀ (3 * b)`-bit keys and `b'`-bit outputs. -/
@[expose] def reducedTrinomialStep (w₀ b b' : ℕ) : ℕ :=
  trinomialStepAux (reducedTargetBits w₀ b b')

/-- Trinomial field degree `q = 2 * 3 ^ reducedTrinomialStep w₀ b b'`. -/
abbrev reducedTrinomialDeg (w₀ b b' : ℕ) : ℕ :=
  2 * 3 ^ reducedTrinomialStep w₀ b b'

/-- The reduced key bit-width `min w₀ (3 * b)` is at most `reducedTrinomialDeg w₀ b b'`. -/
theorem min_le_reducedTrinomialDeg (w₀ b b' : ℕ) :
    min w₀ (3 * b) ≤ 2 * 3 ^ reducedTrinomialStep w₀ b b' :=
  (le_max_left _ _).trans (le_two_mul_three_pow_trinomialStepAux (reducedTargetBits w₀ b b'))

/-- The reduced key universe `2 ^ min w₀ (3 * b)` fits in `2 ^ reducedTrinomialDeg w₀ b b'`. -/
theorem two_pow_min_le_two_pow_reducedTrinomialDeg (w₀ b b' : ℕ) :
    2 ^ min w₀ (3 * b) ≤ 2 ^ (2 * 3 ^ reducedTrinomialStep w₀ b b') :=
  Nat.pow_le_pow_right two_pos (min_le_reducedTrinomialDeg w₀ b b')

/-- The output bit-width `b'` is at most `reducedTrinomialDeg w₀ b b'`. -/
theorem le_reducedTrinomialDeg (w₀ b b' : ℕ) :
    b' ≤ 2 * 3 ^ reducedTrinomialStep w₀ b b' :=
  ((le_max_left b' 1).trans (le_max_right _ _)).trans
    (le_two_mul_three_pow_trinomialStepAux (reducedTargetBits w₀ b b'))

/-- Top-level seed type `Fin (2 ^ (w₀ - 1))` for the multiply-shift reduction stage. -/
abbrev ReducedTopSeed (w₀ : ℕ) : Type :=
  Fin (2 ^ (w₀ - 1))

/-- Bottom-level seed type `Fin k → Fin (2 ^ reducedTrinomialDeg w₀ b b')` for the `k`-wise
independent trinomial polynomial stage. -/
abbrev ReducedBotSeed (w₀ b b' k : ℕ) : Type :=
  Fin k → Fin (2 ^ reducedTrinomialDeg w₀ b b')

/-- Combined seed type `ReducedTopSeed w₀ × ReducedBotSeed w₀ b b' k` for the two-stage reduced
polynomial hash family. -/
abbrev ReducedPolySeed (w₀ b b' k : ℕ) : Type :=
  ReducedTopSeed w₀ × ReducedBotSeed w₀ b b' k

/-- Two-stage hash family `reducedPolyHash U w₀ b b' k` mapping `u : Fin U` to `Fin (2 ^ b')`:
first reduces `u` to `min w₀ (3 * b)` bits via `multiplyShiftReduced U w₀ (3 * b) θ.1`, then
evaluates the degree-`< k` trinomial polynomial hash with coefficients `θ.2`. -/
@[expose] noncomputable def reducedPolyHash (U w₀ b b' k : ℕ) (θ : ReducedPolySeed w₀ b b' k)
    (u : Fin U) : Fin (2 ^ b') :=
  trinomialPolyHash (reducedTrinomialStep w₀ b b') k (2 ^ min w₀ (3 * b)) b' θ.2
    (multiplyShiftReduced U w₀ (3 * b) θ.1 u)

/-- **Conditional `k`-wise independence on any key set where the reduction is injective**:
for any `S : Finset (Fin U)` and any reduction seed `α : ReducedTopSeed w₀` that is injective on
`S` (`Set.InjOn (multiplyShiftReduced U w₀ (3 * b) α) S`), the restricted bottom-seed family
`fun (β : ReducedBotSeed w₀ b b' k) (u : S) => reducedPolyHash U w₀ b b' k (α, β) u.val` is exact
`k`-wise independent (`IsKWiseIndependentHash k`). -/
theorem isKWiseIndependentHash_reducedPolyHash_of_injOn {U w₀ b b' k : ℕ}
    {S : Finset (Fin U)} {α : ReducedTopSeed w₀}
    (hinj : Set.InjOn (multiplyShiftReduced U w₀ (3 * b) α) (S : Set (Fin U))) :
    IsKWiseIndependentHash k
      (fun (β : ReducedBotSeed w₀ b b' k) (u : S) => reducedPolyHash U w₀ b b' k (α, β) u.val) := by
  have hg : Function.Injective (fun u : S => multiplyShiftReduced U w₀ (3 * b) α u.val) :=
    fun u₁ u₂ h => Subtype.ext (hinj u₁.property u₂.property h)
  have htr : IsKWiseIndependentHash k
      (trinomialPolyHash (reducedTrinomialStep w₀ b b') k (2 ^ min w₀ (3 * b)) b') :=
    isKWiseIndependentHash_trinomialPolyHash
      (t := reducedTrinomialStep w₀ b b') (k := k) (U := 2 ^ min w₀ (3 * b)) (M := b')
      (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b')
      (le_reducedTrinomialDeg w₀ b b')
  have hcomp := IsKWiseIndependentHash.comp htr hg
  exact hcomp

/-- For any `α ∈ reducedGoodTop U w₀ (3 * b) T`, the restriction of `reducedPolyHash` to `T`
(`#T ≤ k`) under a uniform bottom seed is `PMF.uniformOfFintype (T → Fin (2 ^ b'))`. -/
theorem map_restrict_reducedPolyHash_eq_uniform_of_injOn {U w₀ b b' k : ℕ}
    {T : Finset (Fin U)} (hT : #T ≤ k) {α : ReducedTopSeed w₀}
    (hinj : Set.InjOn (multiplyShiftReduced U w₀ (3 * b) α) (T : Set (Fin U))) :
    (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
      (fun β => T.restrict (reducedPolyHash U w₀ b b' k (α, β))) =
      PMF.uniformOfFintype (T → Fin (2 ^ b')) := by
  classical
  ext y
  have hk := isKWiseIndependentHash_reducedPolyHash_of_injOn (b' := b') (k := k) hinj
  have hcard : (univ : Finset T).card ≤ k := by
    rwa [card_univ, Fintype.card_coe]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_uniformOfFintype_map_apply]
  have hfilter :
      (univ.filter fun β : ReducedBotSeed w₀ b b' k =>
        T.restrict (reducedPolyHash U w₀ b b' k (α, β)) = y) =
      (univ.filter fun β : ReducedBotSeed w₀ b b' k =>
        (univ : Finset T).restrict (fun u : T => reducedPolyHash U w₀ b b' k (α, β) u.val) =
          fun u => y u.val) := by
    ext β
    simp only [mem_filter, mem_univ, true_and, funext_iff, Subtype.forall, restrict, forall_const]
  have hdens :
      ({β : ReducedBotSeed w₀ b b' k |
        T.restrict (reducedPolyHash U w₀ b b' k (α, β)) = y} : Finset _).dens =
      ({β : ReducedBotSeed w₀ b b' k |
        (univ : Finset T).restrict (fun u : T => reducedPolyHash U w₀ b b' k (α, β) u.val) =
          fun u => y u.val} : Finset _).dens := by
    congr 1
  rw [hdens, hk.dens_filter_restrict_eq hcard (fun u => y u.val)]
  simp [Fintype.card_pi]

/-- **High-probability `k`-wise independence coupling (`coupledWithin_reducedPolyHash_restrict`)**:
for any `T : Finset (Fin U)` with `#T ≤ k` (`0 < w₀`, `U ≤ 2 ^ w₀`), the restriction of
`reducedPolyHash U w₀ b b' k θ` to `T` under a uniform seed
`θ ← PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k)` is coupled within
`(#T * (#T - 1) : ℝ≥0∞) / 2 ^ (3 * b)` of `PMF.uniformOfFintype (T → Fin (2 ^ b'))`. -/
theorem coupledWithin_reducedPolyHash_restrict {U w₀ b b' k : ℕ}
    (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀) {T : Finset (Fin U)} (hT : #T ≤ k) :
    PMF.CoupledWithin
      ((PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k)).map
        (fun θ => T.restrict (reducedPolyHash U w₀ b b' k θ)))
      (PMF.uniformOfFintype (T → Fin (2 ^ b')))
      (((#T * (#T - 1) : ℕ) : ℝ≥0∞) / 2 ^ (3 * b)) := by
  classical
  let G := reducedGoodTop U w₀ (3 * b) T
  have hprod :
      (PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k)).map
        (fun θ => T.restrict (reducedPolyHash U w₀ b b' k θ)) =
      (PMF.uniformOfFintype (ReducedTopSeed w₀)).bind fun α =>
        (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => T.restrict (reducedPolyHash U w₀ b b' k (α, β))) := by
    rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
    refine congrArg ((PMF.uniformOfFintype (ReducedTopSeed w₀)).bind ·) (funext fun α => ?_)
    simp only [PMF.map_comp, Function.comp_def]
  rw [hprod]
  have hcpl : PMF.CoupledWithin
      ((PMF.uniformOfFintype (ReducedTopSeed w₀)).bind fun α =>
        (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => T.restrict (reducedPolyHash U w₀ b b' k (α, β))))
      (PMF.uniformOfFintype (T → Fin (2 ^ b')))
      ((PMF.uniformOfFintype (ReducedTopSeed w₀)).toOuterMeasure
        (G : Set (ReducedTopSeed w₀))ᶜ) := by
    refine PMF.CoupledWithin.bind_of_eq_on (G : Set (ReducedTopSeed w₀)) fun α _ hα => ?_
    exact map_restrict_reducedPolyHash_eq_uniform_of_injOn hT (mem_reducedGoodTop.mp hα)
  refine hcpl.mono ?_
  have hcompl : ((G : Set (ReducedTopSeed w₀))ᶜ : Set (ReducedTopSeed w₀)) =
      {α | ¬ Set.InjOn (multiplyShiftReduced U w₀ (3 * b) α) (T : Set (Fin U))} := by
    ext α
    simp only [G, Set.mem_compl_iff, mem_coe, mem_reducedGoodTop, Set.mem_ofPred_eq]
  rw [hcompl]
  exact toOuterMeasure_not_injOn_multiplyShiftReduced_le hw₀ hU T

end Cslib.Probability
