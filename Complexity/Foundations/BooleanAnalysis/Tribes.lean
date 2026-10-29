/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Probability.Resilience
import Complexity.Foundations.Data.BitString.Agree

/-!
# The Tribes function

The *Tribes* function `Tribes_{w,s}` (`Cslib.BitString.tribes`) on `s * w` bits is the `OR` of `s`
`AND`s of `w` bits each, on disjoint *tribes* of bits [O'Donnell, Definition 2.7][ODonnell2014],
introduced by Ben-Or and Linial. It is monotone (`Cslib.BitString.monotone_tribes`) and true with
probability `1 - (1 - 2 ^ (-w)) ^ s` (`Cslib.BitString.expect_bitVal_tribes`)
[O'Donnell, Fact 4.10][ODonnell2014].

O'Donnell takes `s` largest with this probability at most `1 / 2`
[O'Donnell, Definition 4.11][ODonnell2014]. For such `s` we show that the probability is within
`2 ^ (-w)` of `1 / 2` (`Cslib.BitString.abs_expect_bitVal_tribes_sub_half_le`); this explicit bound
is ours. O'Donnell's asymptotic statements, that then `2 ^ w = (n / ln n) (1 + o(1))` for
`n = s w` with bias `1 / 2 - O(log n / n)` and that each bit has influence `(ln n / n) (1 ± o(1))`
[O'Donnell, Propositions 4.12 and 4.13][ODonnell2014], are not formalized.

A coalition `Q` leaves Tribes undetermined only if some tribe meets `Q` and is all `true` outside
`Q`. A union bound over these tribes bounds the influence of `Q` by `2 ^ (|Q| - w)`
(`Cslib.BitString.coalitionInfluence_tribes_le`), so Tribes is `(q, 2 ^ (q - w))`-resilient
(`Cslib.BitString.isResilient_tribes`); the bound and its proof are ours. It is useful only for
`q < w`, about `log n`: one whole tribe of `w` bits already has influence
`(1 - 2 ^ (-w)) ^ (s - 1)`, about `1 / 2` for the `s` above, so Tribes is not
`(q, O(q log n / n))`-resilient [O'Donnell, Section 9.6][ODonnell2014].

## Main definitions

* `Cslib.BitString.tribes`: the Tribes function `Tribes_{w,s}`.

## Main results

* `Cslib.BitString.monotone_tribes`: Tribes is monotone.
* `Cslib.BitString.expect_bitVal_tribes`: the probability that Tribes is true.
* `Cslib.BitString.abs_expect_bitVal_tribes_sub_half_le`: Tribes is nearly balanced.
* `Cslib.BitString.expect_ite_forall_mem_eq`: a set of `k` uniformly random bits takes a given
  value with probability `2 ^ (-k)`.
* `Cslib.BitString.coalitionInfluence_tribes_le`, `Cslib.BitString.isResilient_tribes`: the
  influence of coalitions on Tribes.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

/-! ### Uniformly random bits -/

/-- The bits of a set `S` of uniformly random bits are all equal to `b` with probability
`2 ^ (-|S|)`, for any decision procedure of the event. -/
theorem expect_ite_forall_mem_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (b : Bool) [DecidablePred fun x : ι → Bool => ∀ i ∈ S, x i = b] :
    𝔼 x : ι → Bool, (if ∀ i ∈ S, x i = b then (1 : ℝ) else 0) = 2⁻¹ ^ #S := by
  have hcard : #{x : ι → Bool | ∀ i ∈ S, x i = b} = 2 ^ #Sᶜ := by
    rw [← card_filter_forall_notMem_eq Sᶜ fun _ => b]
    refine congrArg card (filter_congr fun x _ => ?_)
    simp only [mem_compl, not_not]
  have hS : #S ≤ Fintype.card ι := card_le_univ S
  rw [expect_eq_sum_div_card, sum_boole, hcard, card_compl, card_univ, Fintype.card_fun,
    Fintype.card_bool]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hS
  rw [hm, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, pow_add, inv_pow,
    mul_comm, ← div_div, div_self (by positivity), one_div]

/-! ### The function -/

variable {w s : ℕ}

/-- **Tribes** `Tribes_{w,s}` [O'Donnell, Definition 2.7][ODonnell2014]: on `s * w` bits, the `OR`
of `s` `AND`s of `w` bits each, the `i`-th bit of the `j`-th tribe being bit
`finProdFinEquiv (j, i)`. The value `true` is O'Donnell's `True`, which he writes `-1`. -/
@[expose] def tribes (w s : ℕ) (x : BitString (s * w)) : Bool :=
  decide (∃ j : Fin s, ∀ i : Fin w, x (finProdFinEquiv (j, i)) = true)

/-- Tribes is true exactly when some tribe is all `true`. -/
theorem tribes_eq_true_iff {x : BitString (s * w)} :
    tribes w s x = true ↔ ∃ j : Fin s, ∀ i : Fin w, x (finProdFinEquiv (j, i)) = true :=
  decide_eq_true_iff

/-- **Tribes is monotone.** -/
theorem monotone_tribes (w s : ℕ) : Monotone (tribes w s) := fun x y hxy => by
  cases hx : tribes w s x
  · exact Bool.false_le _
  · obtain ⟨j, hj⟩ := tribes_eq_true_iff.1 hx
    refine (tribes_eq_true_iff.2 ⟨j, fun i => ?_⟩).ge
    have h := hxy (finProdFinEquiv (j, i))
    rw [hj i] at h
    exact le_antisymm (Bool.le_true _) h

/-! ### The probability of `true` -/

/-- Strings of `s * w` bits as `s` blocks of `w` bits. -/
private def blocks (w s : ℕ) : (Fin s → Fin w → Bool) ≃ BitString (s * w) :=
  (Equiv.curry (Fin s) (Fin w) Bool).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl Bool))

private theorem blocks_apply (y : Fin s → Fin w → Bool) (j : Fin s) (i : Fin w) :
    blocks w s y (finProdFinEquiv (j, i)) = y j i := by
  simp [blocks]

/-- Tribes on blocks, as `1 - ∏ⱼ (1 - ∏ᵢ yⱼᵢ)`. -/
private theorem bitVal_tribes_blocks (y : Fin s → Fin w → Bool) :
    bitVal ℝ (tribes w s (blocks w s y)) = 1 - ∏ j, (1 - ∏ i, bitVal ℝ (y j i)) := by
  have hp (j : Fin s) : ∏ i, bitVal ℝ (y j i) = if ∀ i, y j i = true then 1 else 0 := by
    by_cases h : ∀ i, y j i = true
    · rw [ite_eq_left h]
      exact prod_eq_one fun i _ => by rw [h i, bitVal_true]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.1 h
      exact prod_eq_zero (mem_univ i) (by rw [Bool.not_eq_true] at hi; rw [hi, bitVal_false])
  simp only [tribes, blocks_apply, hp]
  by_cases h : ∃ j, ∀ i, y j i = true
  · obtain ⟨j, hj⟩ := h
    rw [decide_eq_true ⟨j, hj⟩, bitVal_true,
      prod_eq_zero (mem_univ j) (by rw [ite_eq_left hj, sub_self]), sub_zero]
  · rw [decide_eq_false h, bitVal_false,
      prod_eq_one fun j _ => by rw [ite_eq_right fun hj => h ⟨j, hj⟩, sub_zero], sub_self]

/-- Over all block strings, `∏ⱼ (1 - ∏ᵢ yⱼᵢ)` sums to `(2 ^ w - 1) ^ s`. -/
private theorem sum_prod_one_sub_prod (w s : ℕ) :
    ∑ y : Fin s → Fin w → Bool, ∏ j, (1 - ∏ i, bitVal ℝ (y j i)) = (2 ^ w - 1) ^ s := by
  have hs := Fintype.prod_sum fun (_ : Fin s) (z : Fin w → Bool) => 1 - ∏ i, bitVal ℝ (z i)
  have hw := Fintype.prod_sum fun (_ : Fin w) (b : Bool) => bitVal ℝ b
  beta_reduce at hs hw
  rw [← hs, sum_sub_distrib, ← hw]
  simp only [Fintype.sum_bool, bitVal_true, bitVal_false, add_zero, prod_const_one, sum_const,
    card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_pow, Nat.cast_ofNat, prod_const]

/-- **The probability that Tribes is true** [O'Donnell, Fact 4.10][ODonnell2014]:
`Pr[Tribes_{w,s} = True] = 1 - (1 - 2 ^ (-w)) ^ s`. -/
theorem expect_bitVal_tribes (w s : ℕ) :
    𝔼 x, bitVal ℝ (tribes w s x) = 1 - (1 - 2⁻¹ ^ w) ^ s := by
  rw [Fintype.expect_equiv (blocks w s).symm _ (fun y => bitVal ℝ (tribes w s (blocks w s y)))
    fun x => by rw [Equiv.apply_symm_apply]]
  simp only [bitVal_tribes_blocks]
  rw [expect_sub_distrib, Fintype.expect_const, expect_eq_sum_div_card, sum_prod_one_sub_prod,
    card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← div_pow, sub_div,
    div_self (by positivity), inv_pow, one_div]

/-- **Tribes is nearly balanced**, our explicit form of
[O'Donnell, Proposition 4.12, last statement][ODonnell2014]: if `s` is largest with
`(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, that is, `Tribes_{w,s}` is true with probability at most `1 / 2`
[O'Donnell, Definition 4.11][ODonnell2014], then the probability is within `2 ^ (-w)` of `1 / 2`.
The bound is ours; O'Donnell states `1 / 2 - O(log n / n)` for `n = s w`. -/
theorem abs_expect_bitVal_tribes_sub_half_le
    (h₁ : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (h₂ : (1 - (2⁻¹ : ℝ) ^ w) ^ (s + 1) < 1 / 2) :
    |𝔼 x, bitVal ℝ (tribes w s x) - 1 / 2| ≤ 2⁻¹ ^ w := by
  rw [expect_bitVal_tribes]
  have hb : 0 ≤ (2⁻¹ : ℝ) ^ w := by positivity
  have hb1 : (2⁻¹ : ℝ) ^ w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : (1 - (2⁻¹ : ℝ) ^ w) ^ s ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right ha hb
  rw [pow_succ] at h₂
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Coalitions -/

/-- The `j`-th tribe. -/
private def tribe (w : ℕ) (j : Fin s) : Finset (Fin (s * w)) :=
  univ.map ⟨fun i => finProdFinEquiv (j, i), fun _ _ h => by simpa using h⟩

private theorem mem_tribe {j : Fin s} {k : Fin (s * w)} :
    k ∈ tribe w j ↔ (finProdFinEquiv.symm k).1 = j := by
  rw [tribe, mem_map]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j, i))
  · rintro rfl
    exact ⟨(finProdFinEquiv.symm k).2, mem_univ _, finProdFinEquiv.apply_symm_apply k⟩

private theorem card_tribe (j : Fin s) : #(tribe w j) = w := by
  rw [tribe, card_map, card_univ, Fintype.card_fin]

/-- Tribes is true exactly when some tribe is all `true`, with tribes as sets. -/
private theorem tribes_eq_true_iff_tribe {x : BitString (s * w)} :
    tribes w s x = true ↔ ∃ j : Fin s, ∀ k ∈ tribe w j, x k = true := by
  rw [tribes_eq_true_iff]
  refine exists_congr fun j => ⟨fun h k hk => ?_, fun h i => h _ (mem_map_of_mem _ (mem_univ i))⟩
  obtain ⟨i, -, rfl⟩ := mem_map.1 hk
  exact h i

/-- The tribes partition the bits, so their intersections with `Q` have total size `|Q|`. -/
private theorem sum_card_tribe_inter (Q : Finset (Fin (s * w))) :
    ∑ j, #(tribe w j ∩ Q) = #Q := by
  rw [card_eq_sum_card_fiberwise (f := fun k => (finProdFinEquiv.symm k).1) (t := univ)
    fun _ _ => mem_coe.2 (mem_univ _)]
  refine sum_congr rfl fun j _ => congrArg card ?_
  ext k
  rw [mem_inter, mem_filter, mem_tribe, and_comm]

/-- If Tribes is undetermined at `x` by the bits outside `Q`, some tribe meets `Q` and is all
`true` outside `Q`. -/
private theorem exists_tribe_of_isUndetermined {Q : Finset (Fin (s * w))} {x : BitString (s * w)}
    (h : IsUndetermined Q (tribes w s) x) :
    ∃ j, (tribe w j ∩ Q).Nonempty ∧ ∀ k ∈ tribe w j \ Q, x k = true := by
  rw [isUndetermined_iff_of_monotone (monotone_tribes w s), tribes_eq_true_iff_tribe,
    ← Bool.not_eq_true, tribes_eq_true_iff_tribe] at h
  obtain ⟨⟨j, hj⟩, h0⟩ := h
  have hx : ∀ k ∈ tribe w j \ Q, x k = true := fun k hk => by
    rw [← piecewise_eq_of_notMem Q (fun _ => true) x (mem_sdiff.1 hk).2]
    exact hj k (mem_sdiff.1 hk).1
  refine ⟨j, ?_, hx⟩
  by_contra hne
  refine h0 ⟨j, fun k hk => ?_⟩
  have hkQ : k ∉ Q := fun hkQ => hne ⟨k, mem_inter.2 ⟨hk, hkQ⟩⟩
  rw [piecewise_eq_of_notMem _ _ _ hkQ]
  exact hx k (mem_sdiff.2 ⟨hk, hkQ⟩)

/-- For numbers `a j ≥ 1`, `∑ 2 ^ a j ≤ 2 ^ ∑ a j`. -/
private theorem sum_two_pow_le_two_pow_sum {α : Type*} (J : Finset α) (a : α → ℕ)
    (ha : ∀ j ∈ J, 1 ≤ a j) : ∑ j ∈ J, 2 ^ a j ≤ 2 ^ ∑ j ∈ J, a j := by
  classical
  induction J using Finset.induction with
  | empty => simp
  | insert j J hj ih =>
    rw [sum_insert hj, sum_insert hj, pow_add]
    have ih := ih fun i hi => ha i (mem_insert_of_mem hi)
    have h1 : 2 ^ 1 ≤ 2 ^ a j := Nat.pow_le_pow_right two_pos (ha j (mem_insert_self j J))
    rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · have h2 : 2 ^ 1 ≤ 2 ^ ∑ i ∈ J, a i := Nat.pow_le_pow_right two_pos
        ((ha i (mem_insert_of_mem hi)).trans (single_le_sum (fun _ _ => Nat.zero_le _) hi))
      rw [pow_one] at h1 h2
      nlinarith

/-- **The influence of a coalition on Tribes**, our union bound: a coalition `Q` has influence at
most `2 ^ (|Q| - w)` on `Tribes_{w,s}`. -/
theorem coalitionInfluence_tribes_le (Q : Finset (Fin (s * w))) :
    coalitionInfluence (Probability.PMF.uniformOfFintype _) Q (tribes w s) ≤ 2 ^ #Q / 2 ^ w := by
  set J := ({j | (tribe w j ∩ Q).Nonempty} : Finset (Fin s))
  have key (m a : ℕ) (h : m + a = w) : (2⁻¹ : ℝ) ^ m = 2 ^ a / 2 ^ w := by
    rw [← h, pow_add, inv_pow, mul_comm, ← div_div, div_self (by positivity), one_div]
  rw [coalitionInfluence_uniformOfFintype]
  calc 𝔼 x, (if IsUndetermined Q (tribes w s) x then (1 : ℝ) else 0)
      ≤ 𝔼 x : BitString (s * w), ∑ j ∈ J, if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ) else 0 :=
        expect_le_expect fun x _ => by
          by_cases h : IsUndetermined Q (tribes w s) x
          · obtain ⟨j, hj, hx⟩ := exists_tribe_of_isUndetermined h
            rw [ite_eq_left h]
            refine (single_le_sum (f := fun j => if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ)
              else 0) (fun j _ => by split_ifs <;> norm_num) (mem_filter.2 ⟨mem_univ j, hj⟩)).trans'
              ?_
            rw [ite_eq_left hx]
          · rw [ite_eq_right h]
            exact sum_nonneg fun j _ => by split_ifs <;> norm_num
    _ = ∑ j ∈ J, 𝔼 x : BitString (s * w),
          if ∀ k ∈ tribe w j \ Q, x k = true then (1 : ℝ) else 0 := expect_sum_comm _ _ _
    _ = ∑ j ∈ J, (2 : ℝ) ^ #(tribe w j ∩ Q) / 2 ^ w := sum_congr rfl fun j _ => by
        exact (expect_ite_forall_mem_eq (tribe w j \ Q) true).trans
          (key _ _ ((card_sdiff_add_card_inter _ _).trans (card_tribe j)))
    _ ≤ 2 ^ #Q / 2 ^ w := by
        rw [← sum_div]
        gcongr
        have hN : ∑ j ∈ J, 2 ^ #(tribe w j ∩ Q) ≤ 2 ^ #Q :=
          (sum_two_pow_le_two_pow_sum J _ fun j hj => (mem_filter.1 hj).2.card_pos).trans
            (Nat.pow_le_pow_right two_pos ((sum_le_sum_of_subset (subset_univ J)).trans_eq
              (sum_card_tribe_inter Q)))
        exact_mod_cast hN

/-- **Tribes is resilient against small coalitions**, our bound: `Tribes_{w,s}` is
`(q, 2 ^ (q - w))`-resilient [Chattopadhyay–Zuckerman, Definition 1.7][ChattopadhyayZuckerman2019].
This is useful only for `q < w`; Tribes is not `(q, O(q log n / n))`-resilient for `q ≥ w`
[O'Donnell, Section 9.6][ODonnell2014]. -/
theorem isResilient_tribes (w s q : ℕ) : IsResilient q (2 ^ q / 2 ^ w) (tribes w s) :=
  fun Q hQ => hQ ▸ coalitionInfluence_tribes_le Q

end Cslib.BitString
