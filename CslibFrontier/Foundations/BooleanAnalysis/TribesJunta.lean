/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.TribesInfluence
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Hamming

/-!
# Tribes is far from every small junta

Every Boolean function `g` on the `n = s w` bits of the nearly balanced Tribes function
`Tribes_{w,s}`, `s = tribesSize w`, that depends only on a set `J` of at most `3 n / 4` coordinates
is `1 / 256`-far from Tribes (`Cslib.BitString.one_div_256_le_hammingDist_tribes_div`). This is
[O'Donnell, Exercise 4.15][ODonnell2014], which asks for some universal constant `ε₀ > 0`; the
constant `1 / 256` and the following proof are ours.

At least a quarter of the tribes, say the set `T`, have a coordinate `c j` outside `J`. For
`j ∈ T`, consider the event that the other bits of tribe `j` are `true`, every other tribe of `T`
has a `false` bit off its free coordinate, and every tribe outside `T` has a `false` bit. On it,
Tribes is the bit `c j`; flipping that bit keeps the event and `g`, and flips Tribes, so `g`
disagrees with Tribes on half of it. The events for distinct tribes of `T` are disjoint, and each
has probability `2 ^ (-(w - 1)) (1 - 2 ^ (-(w - 1))) ^ (|T| - 1) (1 - 2 ^ (-w)) ^ (s - |T|)` by the
independence of the tribes (`Cslib.BitString.expect_prod_tribe`). Bernoulli's inequality and
`2 ^ (w - 1) ≤ s ≤ 4 |T|`, `s < 2 ^ w` bound the total disagreement below by `1 / 256`.

Since Tribes has total influence at most `2 w` (`Cslib.BitString.totalInfluence_tribes_le`), this
shows that the exponential junta size in Friedgut's junta theorem is necessary
[O'Donnell, Exercise 9.26][ODonnell2014] [Friedgut1998]: for every `K ≥ 4` there is a Boolean
function of total influence at most `K` that is `1 / 256`-close to no function of at most
`(3 / 16) 2 ^ (K / 2)` coordinates
(`Cslib.BitString.exists_totalInfluence_le_lt_card_of_dependsOn`), against the
`3 · 2 ^ (8 K / ε)` coordinates of
`Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`. The explicit
constants are ours.

## Main results

* `Cslib.BitString.one_div_256_le_hammingDist_tribes_div`: Tribes is `1 / 256`-far from every
  function of at most `3 n / 4` of its `n` coordinates.
* `Cslib.BitString.exists_totalInfluence_le_lt_card_of_dependsOn`: the exponential junta size in
  Friedgut's junta theorem is necessary.

## References

* [E. Friedgut, *Boolean functions with low average sensitivity depend on few
  coordinates*][Friedgut1998]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {w s : ℕ}

/-- **The pivotal-flip pairing**: if a weight `P` and a function `g` are unchanged by flipping the
coordinate `k`, while `f` flips wherever `P` is nonzero, then `f` and `g` disagree on exactly half
of the `P`-mass. -/
private theorem two_mul_expect_mul_ite_ne_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : (ι → Bool) → ℝ) (f g : (ι → Bool) → Bool) (k : ι)
    (hP : ∀ x, P (update x k (!x k)) = P x) (hg : ∀ x, g (update x k (!x k)) = g x)
    (hf : ∀ x, P x ≠ 0 → f (update x k (!x k)) = !f x) :
    2 * 𝔼 x, P x * (if f x ≠ g x then 1 else 0) = 𝔼 x, P x := by
  let σ (x : ι → Bool) := update x k (!x k)
  have hinv : Involutive σ := fun x => by simp [σ]
  have he := Fintype.expect_equiv (hinv.toPerm σ)
    (fun x => P (σ x) * (if f (σ x) ≠ g (σ x) then (1 : ℝ) else 0))
    (fun x => P x * (if f x ≠ g x then (1 : ℝ) else 0)) (fun _ => rfl)
  have hpt (x : ι → Bool) : P (σ x) * (if f (σ x) ≠ g (σ x) then (1 : ℝ) else 0) =
      P x - P x * (if f x ≠ g x then 1 else 0) := by
    simp only [σ, hP, hg]
    by_cases h0 : P x = 0
    · simp [h0]
    · rw [hf x h0]
      cases f x <;> cases g x <;> simp
  simp only [hpt, expect_sub_distrib] at he
  linarith

section Junta

variable {J : Finset (Fin (s * w))}

/-- The tribes not entirely inside `J`. -/
private def looseTribes (w : ℕ) (J : Finset (Fin (s * w))) : Finset (Fin s) :=
  univ.filter fun j => ∃ i, finProdFinEquiv (j, i) ∉ J

/-- If `J` has at most `3 / 4` of the coordinates, then at least a quarter of the tribes are not
inside `J`. -/
private theorem le_four_mul_card_looseTribes (hw : 0 < w) (hJ : 4 * #J ≤ 3 * (s * w)) :
    s ≤ 4 * #(looseTribes w J) := by
  set T := looseTribes w J with hT
  set U : Finset (Fin s) := univ.filter fun j => ¬ ∃ i, finProdFinEquiv (j, i) ∉ J with hU
  have hTU : #T + #U = s := by
    rw [hT, looseTribes, hU, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hUJ : #U * w ≤ #J := by
    have : (U ×ˢ (univ : Finset (Fin w))).map finProdFinEquiv.toEmbedding ⊆ J := by
      intro k hk
      simp only [mem_map, mem_product, mem_univ, and_true, Equiv.coe_toEmbedding] at hk
      obtain ⟨⟨j, i⟩, hj, rfl⟩ := hk
      simp only [hU, mem_filter, mem_univ, true_and, not_exists, not_not] at hj
      exact hj i
    have := card_le_card this
    simpa [card_product] using this
  have h3 : #U * w ≤ 3 * #T * w := by nlinarith
  have h4 : #U ≤ 3 * #T := Nat.le_of_mul_le_mul_right h3 hw
  omega

/-- The per-tribe factors of the event that bit `c j` of tribe `j` is pivotal: the other bits of
tribe `j` are `true`, each other tribe of `T` has a `false` bit off its own free bit, and each tribe
outside `T` has a `false` bit. -/
private def pivFactor (T : Finset (Fin s)) (c : Fin s → Fin w) (j j' : Fin s)
    (z : Fin w → Bool) : ℝ :=
  if j' = j then (if ∀ i ∈ univ.erase (c j), z i = true then 1 else 0)
  else if j' ∈ T then (if ∃ i ∈ univ.erase (c j'), z i = false then 1 else 0)
  else (if ∃ i ∈ univ, z i = false then 1 else 0)

/-- The indicator of the event that bit `c j` of tribe `j` is pivotal. -/
private def pivWeight (T : Finset (Fin s)) (c : Fin s → Fin w) (j : Fin s)
    (x : BitString (s * w)) : ℝ :=
  ∏ j', pivFactor T c j j' (fun i => x (finProdFinEquiv (j', i)))

variable {T : Finset (Fin s)} {c : Fin s → Fin w}

private theorem pivFactor_nonneg (j j' : Fin s) (z : Fin w → Bool) :
    0 ≤ pivFactor T c j j' z := by
  unfold pivFactor
  split_ifs <;> norm_num

private theorem pivFactor_le_one (j j' : Fin s) (z : Fin w → Bool) :
    pivFactor T c j j' z ≤ 1 := by
  unfold pivFactor
  split_ifs <;> norm_num

private theorem pivWeight_le_one (j : Fin s) (x : BitString (s * w)) : pivWeight T c j x ≤ 1 :=
  prod_le_one₀ (fun _ _ => pivFactor_nonneg ..) fun _ _ => pivFactor_le_one ..

private theorem pivWeight_ne_zero_self {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) : ∀ i ≠ c j, x (finProdFinEquiv (j, i)) = true := by
  have := prod_ne_zero_iff.1 hx j (mem_univ _)
  simp only [pivFactor, ite_true, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
    mem_erase, mem_univ, and_true] at this
  exact this

private theorem pivWeight_ne_zero_other {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) {j' : Fin s} (hj' : j' ≠ j) :
    ∃ i, x (finProdFinEquiv (j', i)) = false := by
  have := prod_ne_zero_iff.1 hx j' (mem_univ _)
  simp only [pivFactor, hj', ite_false] at this
  split_ifs at this with h1 h2 h2
  · obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, hi⟩
  · exact absurd rfl this
  · obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, hi⟩
  · exact absurd rfl this

/-- The pivotality events of distinct tribes of `T` are disjoint. -/
private theorem pivWeight_eq_zero_of_ne {j₁ j₂ : Fin s} (hj₁ : j₁ ∈ T) (hj : j₂ ≠ j₁)
    {x : BitString (s * w)} (hx : pivWeight T c j₁ x ≠ 0) : pivWeight T c j₂ x = 0 := by
  by_contra hx₂
  have h1 := pivWeight_ne_zero_self hx
  have h2 := prod_ne_zero_iff.1 hx₂ j₁ (mem_univ _)
  simp only [pivFactor, Ne.symm hj, hj₁, ite_false, ite_true, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, not_not, mem_erase, mem_univ, and_true] at h2
  obtain ⟨i, hi, hxi⟩ := h2
  exact Bool.false_ne_true (hxi.symm.trans (h1 i hi))

/-- Setting the free bit of tribe `j` keeps its pivotality event. -/
private theorem pivWeight_update (j : Fin s) (x : BitString (s * w)) (b : Bool) :
    pivWeight T c j (update x (finProdFinEquiv (j, c j)) b) = pivWeight T c j x := by
  refine prod_congr rfl fun j' _ => ?_
  by_cases hj' : j' = j
  · subst hj'
    simp only [pivFactor, ite_true]
    have hiff : (∀ i ∈ univ.erase (c j'),
        update x (finProdFinEquiv (j', c j')) b (finProdFinEquiv (j', i)) = true) ↔
          ∀ i ∈ univ.erase (c j'), x (finProdFinEquiv (j', i)) = true := by
      refine forall₂_congr fun i hi => ?_
      rw [update_of_ne]
      intro h
      exact ne_of_mem_erase hi (by simpa using finProdFinEquiv.injective h)
    simp only [hiff]
  · have hfun : (fun i => update x (finProdFinEquiv (j, c j)) b (finProdFinEquiv (j', i))) =
        fun i => x (finProdFinEquiv (j', i)) := by
      funext i
      rw [update_of_ne]
      intro h
      exact hj' (by simpa using congrArg Prod.fst (finProdFinEquiv.injective h))
    rw [hfun]

/-- On its pivotality event, Tribes is the free bit of tribe `j`. -/
private theorem tribes_eq_of_pivWeight_ne_zero {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) : tribes w s x = x (finProdFinEquiv (j, c j)) := by
  rw [tribes]
  cases hb : x (finProdFinEquiv (j, c j))
  · refine decide_eq_false ?_
    rintro ⟨j', hj'⟩
    by_cases hjj : j' = j
    · subst hjj
      exact Bool.false_ne_true (hb.symm.trans (hj' (c j')))
    · obtain ⟨i, hi⟩ := pivWeight_ne_zero_other hx hjj
      exact Bool.false_ne_true (hi.symm.trans (hj' i))
  · refine decide_eq_true ⟨j, fun i => ?_⟩
    by_cases hi : i = c j
    · rw [hi, hb]
    · exact pivWeight_ne_zero_self hx i hi

/-- The probability of the pivotality event of a tribe of `T`. -/
private theorem expect_pivWeight {j : Fin s} (hj : j ∈ T) :
    𝔼 x, pivWeight T c j x =
      2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) := by
  unfold pivWeight
  rw [expect_prod_tribe, ← mul_prod_erase univ _ (mem_univ j),
    ← prod_filter_mul_prod_filter_not _ (· ∈ T)]
  have e0 : 𝔼 z, pivFactor T c j j z = 2⁻¹ ^ (w - 1) := by
    simp only [pivFactor, ite_true]
    rw [expect_ite_forall_mem_eq, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have e1 : ∀ j' ∈ (univ.erase j).filter (· ∈ T),
      𝔼 z, pivFactor T c j j' z = 1 - 2⁻¹ ^ (w - 1) := by
    intro j' hj'
    simp only [mem_filter, mem_erase, mem_univ, and_true] at hj'
    simp only [pivFactor, hj'.1, hj'.2, ite_false, ite_true]
    rw [expect_ite_exists_mem_eq, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have e2 : ∀ j' ∈ (univ.erase j).filter (· ∉ T),
      𝔼 z, pivFactor T c j j' z = 1 - 2⁻¹ ^ w := by
    intro j' hj'
    simp only [mem_filter, mem_erase, mem_univ, and_true] at hj'
    simp only [pivFactor, hj'.1, hj'.2, ite_false]
    rw [expect_ite_exists_mem_eq, card_univ, Fintype.card_fin]
  have c1 : #((univ.erase j).filter (· ∈ T)) = #T - 1 := by
    have : (univ.erase j).filter (· ∈ T) = T.erase j := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true]
    rw [this, card_erase_of_mem hj]
  have c2 : #((univ.erase j).filter (· ∉ T)) = s - #T := by
    have : (univ.erase j).filter (· ∉ T) = Tᶜ := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_compl]
      exact ⟨fun h => h.2, fun h => ⟨fun hk => h (hk ▸ hj), h⟩⟩
    rw [this, card_compl, Fintype.card_fin]
  rw [e0, prod_congr rfl e1, prod_congr rfl e2, prod_const, prod_const, c1, c2]

/-- A function of the coordinates `J` disagrees with Tribes on half of each pivotality event of a
tribe of `T` whose free bit is outside `J`, and these events are disjoint. -/
private theorem card_mul_le_hammingDist_tribes_div {g : BitString (s * w) → Bool}
    (hc : ∀ j ∈ T, finProdFinEquiv (j, c j) ∉ J) (hg : DependsOn g (J : Set (Fin (s * w)))) :
    #T * (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) / 2) ≤
      (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) := by
  have hhalf (j : Fin s) (hj : j ∈ T) :
      2 * 𝔼 x, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) =
        𝔼 x, pivWeight T c j x := by
    refine two_mul_expect_mul_ite_ne_eq (pivWeight T c j) (tribes w s) g
      (finProdFinEquiv (j, c j)) (fun x => pivWeight_update j x _) (fun x => ?_)
      (fun x hx => ?_)
    · refine hg fun k hk => ?_
      rw [update_of_ne]
      rintro rfl
      exact hc j hj hk
    · rw [tribes_eq_of_pivWeight_ne_zero (by rwa [pivWeight_update]),
        tribes_eq_of_pivWeight_ne_zero hx, update_self]
  have hdist : (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) =
      𝔼 x, (if tribes w s x ≠ g x then (1 : ℝ) else 0) := by
    rw [← hammingDist_div_eq_expect]
    simp
  rw [hdist]
  calc (#T : ℝ) *
        (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) / 2)
      = ∑ j ∈ T, 𝔼 x, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun j hj => ?_
        have := hhalf j hj
        rw [expect_pivWeight hj] at this
        linarith
    _ = 𝔼 x, ∑ j ∈ T, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) :=
        (expect_sum_comm ..).symm
    _ ≤ 𝔼 x, (if tribes w s x ≠ g x then (1 : ℝ) else 0) := by
        refine expect_le_expect fun x _ => ?_
        have hD : (0 : ℝ) ≤ if tribes w s x ≠ g x then 1 else 0 := by split_ifs <;> norm_num
        by_cases hx : ∃ j ∈ T, pivWeight T c j x ≠ 0
        · obtain ⟨j, hj, hjx⟩ := hx
          rw [sum_eq_single_of_mem j hj fun j' _ hj' => by
            rw [pivWeight_eq_zero_of_ne hj hj' hjx, zero_mul]]
          exact mul_le_of_le_one_left hD (pivWeight_le_one j x)
        · simp only [not_exists, not_and, not_not] at hx
          rw [sum_eq_zero fun j hj => by rw [hx j hj, zero_mul]]
          exact hD

/-- The numerical estimate: with `2 ^ (w - 1) ≤ s ≤ 4 t`, `t ≤ s < 2 ^ w` and
`(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, the disagreement bound is at least `1 / 256`. -/
private theorem one_div_256_le_card_mul (hw : 1 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s) (hs₂ : s < 2 ^ w)
    (hq : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) {t : ℕ} (ht : s ≤ 4 * t) (hts : t ≤ s) :
    (1 / 256 : ℝ) ≤
      t * (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t)) / 2) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 2⁻¹ ^ (w - 1) := ⟨_, rfl⟩
  rw [← hy]
  have hy0 : 0 ≤ y := hy ▸ by positivity
  have hy1 : y ≤ 1 := hy ▸ pow_le_one₀ (by norm_num) (by norm_num)
  have hq0 : 0 ≤ 1 - (2⁻¹ : ℝ) ^ w := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  have hq1 : 1 - (2⁻¹ : ℝ) ^ w ≤ 1 := sub_le_self _ (by positivity)
  have hA : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ (s - t) :=
    hq.trans (pow_le_pow_of_le_one hq0 hq1 (Nat.sub_le _ _))
  have hB : 1 / 4 ≤ t * y := by
    have h2 : (2 : ℝ) ^ (w - 1) ≤ 4 * t := by exact_mod_cast hs₁.trans ht
    rw [hy, inv_pow, le_mul_inv_iff₀ (by positivity)]
    linarith
  have hC : 1 / 16 ≤ (1 - y) ^ (t - 1) := by
    rcases Nat.lt_or_ge w 2 with hw2 | hw2
    · have hw1 : w = 1 := by omega
      subst hw1
      have : t - 1 = 0 := by
        norm_num at hs₂
        omega
      rw [this, pow_zero]
      norm_num
    · obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, n₀ = 2 ^ (w - 2) := ⟨_, rfl⟩
      have hny : (n₀ : ℝ) * y = 1 / 2 := by
        rw [hy, hn₀, Nat.cast_pow, Nat.cast_ofNat, inv_pow, ← div_eq_mul_inv,
          div_eq_iff (by positivity), show w - 1 = w - 2 + 1 by omega, pow_succ]
        ring
      -- Bernoulli's inequality
      have hpow : 1 / 2 ≤ (1 - y) ^ n₀ := by
        have := one_add_mul_le_pow (a := -y) (by linarith) n₀
        rw [← sub_eq_add_neg] at this
        linarith
      have hTn : t - 1 ≤ 4 * n₀ := by
        have : 2 ^ w = 2 ^ (w - 2) * 2 ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hw2]
        omega
      calc (1 / 16 : ℝ) = (1 / 2) ^ 4 := by norm_num
        _ ≤ ((1 - y) ^ n₀) ^ 4 := pow_le_pow_left₀ (by norm_num) hpow 4
        _ = (1 - y) ^ (4 * n₀) := by rw [← pow_mul, mul_comm]
        _ ≤ (1 - y) ^ (t - 1) := pow_le_pow_of_le_one (by linarith) (by linarith) hTn
  have hB0 : 0 ≤ (t : ℝ) * y := mul_nonneg (Nat.cast_nonneg _) hy0
  have hC0 : 0 ≤ (1 - y) ^ (t - 1) := pow_nonneg (by linarith) _
  calc (1 / 256 : ℝ) = (1 / 4) * (1 / 16) * (1 / 2) / 2 := by norm_num
    _ ≤ (t * y) * (1 - y) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t) / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      exact mul_le_mul (mul_le_mul hB hC (by norm_num) hB0) hA (by norm_num) (mul_nonneg hB0 hC0)
    _ = t * (y * ((1 - y) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t)) / 2) := by ring

/-- The junta-distance bound for every nearly balanced number `s` of tribes. -/
private theorem one_div_256_le_hammingDist_tribes_div_of {g : BitString (s * w) → Bool}
    (hw : 1 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s) (hs₂ : s < 2 ^ w)
    (hq : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (hJ : 4 * #J ≤ 3 * (s * w))
    (hg : DependsOn g (J : Set (Fin (s * w)))) :
    1 / 256 ≤ (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) := by
  have hc : ∀ j ∈ looseTribes w J, ∃ i, finProdFinEquiv (j, i) ∉ J := fun j hj => by
    simpa [looseTribes] using hj
  have : Nonempty (Fin w) := ⟨⟨0, hw⟩⟩
  choose! c hc using hc
  have hts : #(looseTribes w J) ≤ s := by simpa using card_le_univ (looseTribes w J)
  exact (one_div_256_le_card_mul hw hs₁ hs₂ hq (le_four_mul_card_looseTribes hw hJ) hts).trans
    (card_mul_le_hammingDist_tribes_div hc hg)

end Junta

/-- **Tribes is far from every `(3 / 4) n`-junta** [O'Donnell, Exercise 4.15][ODonnell2014]: on
`n = s w` bits with `s = tribesSize w` and `w ≥ 1`, every Boolean function that depends only on a
set `J` of at most `3 n / 4` coordinates disagrees with Tribes on at least a `1 / 256` fraction of
the inputs. O'Donnell asks for some universal constant; the constant `1 / 256` and its proof are
ours. -/
theorem one_div_256_le_hammingDist_tribes_div {J : Finset (Fin (tribesSize w * w))}
    {g : BitString (tribesSize w * w) → Bool} (hw : 1 ≤ w)
    (hJ : 4 * #J ≤ 3 * (tribesSize w * w))
    (hg : DependsOn g (J : Set (Fin (tribesSize w * w)))) :
    1 / 256 ≤ (hammingDist (tribes w (tribesSize w)) g : ℝ) / 2 ^ (tribesSize w * w) :=
  one_div_256_le_hammingDist_tribes_div_of hw (two_pow_sub_one_le_tribesSize hw)
    (tribesSize_lt_two_pow w) (one_div_two_le_pow_tribesSize w) hJ hg

/-- **The exponential in Friedgut's junta theorem is necessary**
[O'Donnell, Exercise 9.26][ODonnell2014] [Friedgut1998]: for every `K ≥ 4` there is a Boolean
function of total influence at most `K` such that every function of a set `J` of coordinates that
is `1 / 256`-close to it has `|J| > (3 / 16) 2 ^ (K / 2)`. The witness is the nearly balanced
Tribes with `w = ⌊K / 2⌋`. Compare the upper bound `3 · 2 ^ (8 K / ε)` of
`Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`. The explicit
constants are ours. -/
theorem exists_totalInfluence_le_lt_card_of_dependsOn {K : ℝ} (hK : 4 ≤ K) :
    ∃ (n : ℕ) (f : BitString n → Bool), totalInfluence (fun x => signVal (f x)) ≤ K ∧
      ∀ (J : Finset (Fin n)) (g : BitString n → Bool), DependsOn g (J : Set (Fin n)) →
        (hammingDist f g : ℝ) / 2 ^ n < 1 / 256 → 3 / 16 * (2 : ℝ) ^ (K / 2) < #J := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ, w = ⌊K / 2⌋₊ := ⟨_, rfl⟩
  have hw1 : (w : ℝ) ≤ K / 2 := hw ▸ Nat.floor_le (by linarith)
  have hw2 : K / 2 < w + 1 := hw ▸ Nat.lt_floor_add_one _
  have hw2' : 2 ≤ w := by
    rw [hw]
    exact Nat.le_floor (by norm_num; linarith)
  refine ⟨tribesSize w * w, tribes w (tribesSize w), ?_, fun J g hg hdist => ?_⟩
  · exact (totalInfluence_tribes_le w).trans (by linarith)
  · by_contra hJ
    push Not at hJ
    refine absurd (one_div_256_le_hammingDist_tribes_div (by omega) ?_ hg) (not_le.2 hdist)
    have hs₁ : 2 ^ (w - 1) ≤ tribesSize w := two_pow_sub_one_le_tribesSize (by omega)
    have h1 : (2 : ℝ) ^ (K / 2) ≤ 2 ^ ((w : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hw2.le
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at h1
    have hpow : (2 : ℝ) ^ w = 2 * 2 ^ (w - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hs₁' : (2 : ℝ) ^ (w - 1) ≤ tribesSize w := by exact_mod_cast hs₁
    have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw2'
    have : (4 * #J : ℝ) ≤ 3 * (tribesSize w * w) := by nlinarith
    exact_mod_cast this

end Cslib.BitString
