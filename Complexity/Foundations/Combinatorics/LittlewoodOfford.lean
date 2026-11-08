/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.CentralBinomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Erdős–Littlewood–Offord anti-concentration inequality

This module formalizes Erdős's Sperner-antichain proof of the Littlewood–Offord anti-concentration
inequality for Boolean linear forms `∑ i : ι, a i * (w i).toNat`, together with the real central
binomial upper bound `(m.choose (m / 2) : ℝ) ≤ 2 ^ m / √(m + 1)` and the reciprocal
square-root rank sum bound `∑ i ∈ S, 1 / √(#{j ∈ S | |a i| ≤ |a j|}) ≤ 2 * √(#S)` used in the
Kane–Williams random restriction lemmas for linear threshold functions (Milestone 3 of
[#2347](https://github.com/cslib-community/complexitylib/issues/2347)).

The primary source is [Erdos1945], Theorem 1, printed p. 898: for `n` real coefficients of
absolute value at least one, at most `n.choose (n / 2)` sign sums lie in an open interval of
length two. For `δ > 0`, put `ε i = 2 * (w i).toNat - 1` and `x i = a i / δ`; then
`∑ i, ε i * x i = (2 * ∑ i, a i * (w i).toNat - ∑ i, a i) / δ`.
Thus an open interval of width `δ` for Boolean sums corresponds to an open interval of length
two for sign sums. The Lean statement uses the more general condition that every pair of
accepted sums differs by less than `δ`, proved by the same Sperner argument. This includes
half-open intervals `[t, t + δ)`: each pair has distance less than `δ`, although their diameter
is `δ`. Subset versions fix the complementary coordinates and count the resulting fibers.

## References

* [P. Erdős, *On a lemma of Littlewood and Offord*][Erdos1945], Theorem 1, p. 898.
-/

@[expose] public section

namespace Cslib.Combinatorics.LittlewoodOfford

open Finset Real

/-! ### Central binomial upper bound over `ℝ` -/

/-- Over `ℝ`, `(m.choose (m / 2) : ℝ) ≤ (2 : ℝ) ^ m / Real.sqrt (m + 1)` for all `m : ℕ`. -/
theorem choose_half_le_two_pow_div_sqrt (m : ℕ) :
    (m.choose (m / 2) : ℝ) ≤ (2 : ℝ) ^ m / Real.sqrt (m + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have hsq : ((m.choose (m / 2) : ℝ) * Real.sqrt (m + 1)) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm m 2, pow_mul]
    norm_num
    exact_mod_cast Cslib.choose_half_sq_mul_le m
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at this

/-! ### Erdős–Littlewood–Offord anti-concentration via Sperner's theorem -/

/-- Sign-normalized subset equivalence `(ι → Bool) ≃ Finset ι` sending `w` to the set of
coordinates `i` where `w i` aligns with the sign of `a i` (`w i = decide (0 ≤ a i)`). -/
noncomputable def signNormalizedSetEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (ι → Bool) ≃ Finset ι where
  toFun w := univ.filter fun i => w i == decide (0 ≤ a i)
  invFun T i := if i ∈ T then decide (0 ≤ a i) else !decide (0 ≤ a i)
  left_inv w := by
    funext i; simp only [mem_filter, mem_univ, true_and]
    cases w i <;> cases decide (0 ≤ a i) <;> rfl
  right_inv T := by
    ext i; simp only [mem_filter, mem_univ, true_and]
    by_cases hi : i ∈ T <;> simp [hi]

/-- Under `signNormalizedSetEquiv a`, the Boolean linear form `∑ i, a i * (w i).toNat` decomposes
into `(∑ i with a i < 0, a i) + ∑ i ∈ signNormalizedSetEquiv a w, |a i|`. -/
theorem sum_bool_eq_neg_sum_add_sum_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (w : ι → Bool) :
    (∑ i : ι, a i * (w i).toNat) =
      (∑ i : ι, if a i < 0 then a i else 0) +
        ∑ i ∈ signNormalizedSetEquiv a w, |a i| := by
  rw [signNormalizedSetEquiv, Equiv.coe_fn_mk, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases ha : 0 ≤ a i
  · have hnot : ¬ (a i < 0) := not_lt.mpr ha
    cases w i <;> simp [ha, hnot, abs_of_nonneg ha]
  · have hlt : a i < 0 := not_le.mp ha
    cases w i <;> simp [ha, hlt, abs_of_neg hlt]

/-- **Full-support Erdős–Littlewood–Offord inequality**: if `|a i| ≥ δ` for all `i : ι` and `P` has
the property that every pair of its points differs by less than `δ`
(`∀ x y, P x → P y → |x - y| < δ`), then at most
`(Fintype.card ι).choose (Fintype.card ι / 2)` Boolean vectors `w : ι → Bool` satisfy
`P (∑ i, a i * (w i).toNat)`. -/
theorem card_filter_sum_bool_le_choose_of_forall_le_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) {δ : ℝ} (P : ℝ → Prop) [DecidablePred P]
    (hδ : ∀ i : ι, δ ≤ |a i|) (hP : ∀ x y, P x → P y → |x - y| < δ) :
    #{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  let c₀ : ℝ := ∑ i : ι, if a i < 0 then a i else 0
  let 𝒜 : Finset (Finset ι) := univ.filter fun T : Finset ι => P (c₀ + ∑ i ∈ T, |a i|)
  have hcard : #{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} = #𝒜 := by
    rw [← card_map (signNormalizedSetEquiv a).toEmbedding]
    congr 1; ext T
    simp only [𝒜, mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rwa [sum_bool_eq_neg_sum_add_sum_abs] at hw
    · intro hT
      refine ⟨(signNormalizedSetEquiv a).symm T, ?_, (signNormalizedSetEquiv a).apply_symm_apply T⟩
      rwa [sum_bool_eq_neg_sum_add_sum_abs, (signNormalizedSetEquiv a).apply_symm_apply]
  rw [hcard]
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜) := by
    intro T₁ hT₁ T₂ hT₂ hne hsub
    simp only [𝒜, mem_coe, mem_filter, mem_univ, true_and] at hT₁ hT₂
    obtain ⟨i₀, hi₀T₂, hi₀T₁⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hsub hne)
    have hdiff : δ ≤ (c₀ + ∑ i ∈ T₂, |a i|) - (c₀ + ∑ i ∈ T₁, |a i|) := by
      have hsplit : (∑ i ∈ T₂, |a i|) = (∑ i ∈ T₁, |a i|) + ∑ i ∈ T₂ \ T₁, |a i| := by
        rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hsub]
      have hi₀_le : |a i₀| ≤ ∑ i ∈ T₂ \ T₁, |a i| :=
        single_le_sum (fun i _ => abs_nonneg (a i)) (mem_sdiff.mpr ⟨hi₀T₂, hi₀T₁⟩)
      linarith [hδ i₀]
    have hlt := (le_abs_self _).trans_lt (hP _ _ hT₂ hT₁)
    linarith
  exact hanti.sperner

/-- **Erdős–Littlewood–Offord inequality on a subset `S : Finset ι`**: if `|a i| ≥ δ` for all
`i ∈ S` and every pair of points satisfying `P` differs by less than `δ`, then at most
`2 ^ (Fintype.card ι - #S) * (#S).choose (#S / 2)` Boolean vectors `w : ι → Bool` satisfy
`P (∑ i, a i * (w i).toNat)`. -/
theorem card_filter_sum_bool_le_of_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (S : Finset ι) {δ : ℝ} (P : ℝ → Prop) [DecidablePred P]
    (hδ : ∀ i ∈ S, δ ≤ |a i|) (hP : ∀ x y, P x → P y → |x - y| < δ) :
    #{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} ≤
      2 ^ (Fintype.card ι - #S) * (#S).choose (#S / 2) := by
  let e := Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ => Bool)
  have hsum (w : ι → Bool) :
      (∑ i : ι, a i * (w i).toNat) =
        (∑ i : {i // i ∈ S}, a i.1 * ((e w).1 i).toNat) +
          (∑ i : {i // i ∉ S}, a i.1 * ((e w).2 i).toNat) := by
    rw [← sum_add_sum_compl S (fun i => a i * (w i).toNat),
      Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => a i * (w i).toNat),
      Finset.sum_subtype Sᶜ (fun _ => mem_compl) (fun i => a i * (w i).toNat)]
    rfl
  have hbij : #{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} =
      ∑ v : {i // i ∉ S} → Bool,
        #{u : {i // i ∈ S} → Bool |
          P ((∑ i : {i // i ∈ S}, a i.1 * (u i).toNat) +
            (∑ i : {i // i ∉ S}, a i.1 * (v i).toNat))} := by
    simp only [card_filter, hsum]
    rw [e.sum_comp (fun p : ({i // i ∈ S} → Bool) × ({i // i ∉ S} → Bool) =>
      if P ((∑ i : {i // i ∈ S}, a i.1 * (p.1 i).toNat) +
        (∑ i : {i // i ∉ S}, a i.1 * (p.2 i).toNat)) then 1 else 0),
      Fintype.sum_prod_type_right]
  rw [hbij]
  refine (sum_le_sum (g := fun _ => (#S).choose (#S / 2)) fun v _ => ?_).trans_eq ?_
  · let c_v := ∑ i : {i // i ∉ S}, a i.1 * (v i).toNat
    have hfiber := card_filter_sum_bool_le_choose_of_forall_le_abs
      (fun i : {i // i ∈ S} => a i.1) (fun x => P (x + c_v))
      (fun i => hδ i.1 i.2)
      (fun x y hx hy => by simpa [add_sub_add_right_eq_sub] using hP (x + c_v) (y + c_v) hx hy)
    simpa [Fintype.card_coe] using hfiber
  · rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
      Fintype.card_coe, smul_eq_mul]

/-- **Quantitative Erdős–Littlewood–Offord bound over `ℝ`**: if `|a i| ≥ δ` for all `i ∈ S` and
every pair of points satisfying `P` differs by less than `δ`, then
`(#{w : ι → Bool | P (∑ i, a i * (w i).toNat)} : ℝ) ≤
  (2 : ℝ) ^ Fintype.card ι / Real.sqrt (#S + 1)`. -/
theorem card_filter_sum_bool_le_two_pow_div_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (S : Finset ι) {δ : ℝ} (P : ℝ → Prop) [DecidablePred P]
    (hδ : ∀ i ∈ S, δ ≤ |a i|) (hP : ∀ x y, P x → P y → |x - y| < δ) :
    (#{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι / Real.sqrt (#S + 1) := by
  have hnat := card_filter_sum_bool_le_of_subset a S P hδ hP
  have hreal : (#{w : ι → Bool | P (∑ i : ι, a i * (w i).toNat)} : ℝ) ≤
      (2 : ℝ) ^ (Fintype.card ι - #S) * ((#S).choose (#S / 2) : ℝ) := by
    exact_mod_cast hnat
  refine hreal.trans ?_
  have hchoose := choose_half_le_two_pow_div_sqrt #S
  have hpow : (2 : ℝ) ^ (Fintype.card ι - #S) * (2 : ℝ) ^ #S = (2 : ℝ) ^ Fintype.card ι := by
    rw [← pow_add, Nat.sub_add_cancel (card_le_univ S)]
  calc (2 : ℝ) ^ (Fintype.card ι - #S) * ((#S).choose (#S / 2) : ℝ)
      ≤ (2 : ℝ) ^ (Fintype.card ι - #S) * ((2 : ℝ) ^ #S / Real.sqrt (#S + 1)) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ = (2 : ℝ) ^ Fintype.card ι / Real.sqrt (#S + 1) := by rw [← mul_div_assoc, hpow]

/-- **Half-open interval Littlewood–Offord bound**: for any half-open interval `[c, c + δ)` with
`|a i| ≥ δ` for all `i ∈ S`,
`(#{w : ι → Bool | c ≤ ∑ i, a i * (w i).toNat ∧ ∑ i, a i * (w i).toNat < c + δ} : ℝ) ≤
  (2 : ℝ) ^ Fintype.card ι / Real.sqrt (#S + 1)`. -/
theorem card_filter_sum_bool_Ico_le_two_pow_div_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (S : Finset ι) (c : ℝ) {δ : ℝ}
    (hδ : ∀ i ∈ S, δ ≤ |a i|) :
    (#{w : ι → Bool | c ≤ ∑ i : ι, a i * (w i).toNat ∧ ∑ i : ι, a i * (w i).toNat < c + δ} : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι / Real.sqrt (#S + 1) :=
  card_filter_sum_bool_le_two_pow_div_sqrt a S (fun x => c ≤ x ∧ x < c + δ) hδ
    (fun x y hx hy => by rw [abs_lt]; constructor <;> linarith)

/-- Covering a half-open interval `[c₀ - ∑ i ∈ T, δ i, c₀)` by `#T` half-open subintervals of
lengths `δ i`: if every half-open interval `[c, c + δ i)` for `i ∈ T` contains at most `M i`
elements of `univ : Finset α`, then `[c₀ - ∑ i ∈ T, δ i, c₀)` contains at most `∑ i ∈ T, M i`
elements. -/
theorem card_filter_Ico_sum_le {α ι : Type*} [Fintype α]
    (g : α → ℝ) (T : Finset ι) (δ M : ι → ℝ)
    (hM : ∀ i ∈ T, ∀ c : ℝ, (#{x : α | c ≤ g x ∧ g x < c + δ i} : ℝ) ≤ M i) (c₀ : ℝ) :
    (#{x : α | c₀ - (∑ i ∈ T, δ i) ≤ g x ∧ g x < c₀} : ℝ) ≤ ∑ i ∈ T, M i := by
  classical
  induction T using Finset.induction_on generalizing c₀ with
  | empty =>
    rw [filter_false_of_mem (fun x _ => by simp [sum_empty]),
      card_empty, Nat.cast_zero, sum_empty]
  | @insert i₀ s hi₀ ih =>
    rw [sum_insert hi₀, sum_insert hi₀]
    have hsub :
        univ.filter (fun x : α => c₀ - (δ i₀ + ∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀) ⊆
          univ.filter (fun x : α => c₀ - δ i₀ ≤ g x ∧ g x < c₀) ∪
            univ.filter (fun x : α => (c₀ - δ i₀) - (∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀ - δ i₀) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
      by_cases h : c₀ - δ i₀ ≤ g x
      · exact Or.inl ⟨h, hx.2⟩
      · exact Or.inr ⟨by linarith [hx.1], not_le.mp h⟩
    have hcard_nat :
        #{x : α | c₀ - (δ i₀ + ∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀} ≤
          #{x : α | c₀ - δ i₀ ≤ g x ∧ g x < c₀} +
            #{x : α | (c₀ - δ i₀) - (∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀ - δ i₀} :=
      (card_le_card hsub).trans (card_union_le _ _)
    have hcard_real :
        (#{x : α | c₀ - (δ i₀ + ∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀} : ℝ) ≤
          (#{x : α | c₀ - δ i₀ ≤ g x ∧ g x < c₀} : ℝ) +
            (#{x : α | (c₀ - δ i₀) - (∑ i ∈ s, δ i) ≤ g x ∧ g x < c₀ - δ i₀} : ℝ) := by
      exact_mod_cast hcard_nat
    have hhead : (#{x : α | c₀ - δ i₀ ≤ g x ∧ g x < c₀} : ℝ) ≤ M i₀ := by
      simpa [sub_add_cancel] using hM i₀ (mem_insert_self i₀ s) (c₀ - δ i₀)
    have htail := ih (fun i hi => hM i (mem_insert_of_mem hi)) (c₀ - δ i₀)
    linarith

/-! ### Reciprocal square-root rank sum bound -/

/-- For every `n ≥ 1`, `1 / Real.sqrt n + 2 * Real.sqrt (n - 1 : ℕ) ≤ 2 * Real.sqrt n`. -/
theorem one_div_sqrt_add_two_mul_sqrt_sub_one_le {n : ℕ} (hn : 1 ≤ n) :
    1 / Real.sqrt n + 2 * Real.sqrt (n - 1 : ℕ) ≤ 2 * Real.sqrt n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hcast]
  have hdiff : (Real.sqrt n - Real.sqrt (n - 1)) * (Real.sqrt n + Real.sqrt (n - 1)) = 1 := by
    rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by linarith)]
    ring
  have hle : 1 ≤ (Real.sqrt n - Real.sqrt (n - 1)) * (2 * Real.sqrt n) := by
    have hsub_nonneg : 0 ≤ Real.sqrt n - Real.sqrt (n - 1) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hsum_le : Real.sqrt n + Real.sqrt (n - 1) ≤ 2 * Real.sqrt n := by
      linarith [Real.sqrt_le_sqrt (by linarith : (n : ℝ) - 1 ≤ n)]
    calc 1 = (Real.sqrt n - Real.sqrt (n - 1)) * (Real.sqrt n + Real.sqrt (n - 1)) := hdiff.symm
      _ ≤ (Real.sqrt n - Real.sqrt (n - 1)) * (2 * Real.sqrt n) := by gcongr
  have hdiv : 1 / Real.sqrt n ≤ 2 * Real.sqrt n - 2 * Real.sqrt (n - 1) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- **Reciprocal square-root rank sum bound**: for any finite set `S : Finset ι` and weights
`a : ι → ℝ`, summing `1 / √(#{j ∈ S | |a i| ≤ |a j|})` over `i ∈ S` is at most `2 * √(#S)`. -/
theorem sum_one_div_sqrt_card_ge_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ S, (1 : ℝ) / Real.sqrt (#{j ∈ S | |a i| ≤ |a j|})) ≤ 2 * Real.sqrt #S := by
  classical
  induction hn : #S generalizing S with
  | zero =>
    rw [card_eq_zero.mp hn, sum_empty, Nat.cast_zero, Real.sqrt_zero, mul_zero]
  | succ m ih =>
    have hne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨i₀, hi₀S, hmin⟩ := S.exists_min_image (fun i => |a i|) hne
    rw [← add_sum_erase _ _ hi₀S]
    have hcard_i₀ : #{j ∈ S | |a i₀| ≤ |a j|} = m + 1 := by
      rw [filter_true_of_mem (fun j hj => hmin j hj), hn]
    have hmono :
        (∑ i ∈ S.erase i₀, (1 : ℝ) / Real.sqrt (#{j ∈ S | |a i| ≤ |a j|})) ≤
          ∑ i ∈ S.erase i₀, (1 : ℝ) / Real.sqrt (#{j ∈ S.erase i₀ | |a i| ≤ |a j|}) := by
      refine sum_le_sum fun i hi => ?_
      have hi_mem : i ∈ {j ∈ S.erase i₀ | |a i| ≤ |a j|} :=
        mem_filter.mpr ⟨hi, le_rfl⟩
      have hpos : 0 < (#{j ∈ S.erase i₀ | |a i| ≤ |a j|} : ℝ) :=
        Nat.cast_pos.mpr (card_pos.mpr ⟨i, hi_mem⟩)
      have hsub : {j ∈ S.erase i₀ | |a i| ≤ |a j|} ⊆ {j ∈ S | |a i| ≤ |a j|} :=
        filter_subset_filter _ (erase_subset i₀ S)
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos)
        (Real.sqrt_le_sqrt (Nat.cast_le.mpr (card_le_card hsub)))
    have herase_card : #(S.erase i₀) = m := by rw [card_erase_of_mem hi₀S, hn]; rfl
    have hih := ih (S.erase i₀) herase_card
    have hstep : 1 / Real.sqrt (m + 1 : ℕ) + 2 * Real.sqrt (m : ℕ) ≤ 2 * Real.sqrt (m + 1 : ℕ) := by
      simpa using one_div_sqrt_add_two_mul_sqrt_sub_one_le (by omega : 1 ≤ m + 1)
    rw [hcard_i₀]
    linarith

/-! ### Block-partition live sets and marginal frequencies -/

/-- For any coordinate `j₀ : κ` and target value `t₀ : τ`, the number of functions `σ : κ → τ`
with `σ j₀ = t₀` times `Fintype.card τ` equals `Fintype.card (κ → τ)`. -/
theorem card_filter_eval_eq {κ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]
    (j₀ : κ) (t₀ : τ) :
    #{σ : κ → τ | σ j₀ = t₀} * Fintype.card τ = Fintype.card (κ → τ) := by
  have hfiber (t : τ) : #{σ : κ → τ | σ j₀ = t} = #{σ : κ → τ | σ j₀ = t₀} := by
    let e : (κ → τ) ≃ (κ → τ) :=
      Equiv.piCongrRight fun j => if j = j₀ then Equiv.swap t t₀ else Equiv.refl τ
    rw [← card_map e.toEmbedding]
    congr 1; ext σ
    simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨σ', hσ', rfl⟩
      simp [e, Equiv.piCongrRight, hσ']
    · intro hσ
      refine ⟨e.symm σ, ?_, e.apply_symm_apply σ⟩
      have hsymm : (e.symm σ) j₀ = Equiv.swap t t₀ (σ j₀) := by
        simp [e, Equiv.piCongrRight]
      rw [hsymm, hσ, Equiv.swap_apply_right]
  have hsum : (∑ t : τ, #{σ : κ → τ | σ j₀ = t}) = Fintype.card (κ → τ) := by
    rw [← card_univ]
    exact (card_eq_sum_card_fiberwise (f := fun σ : κ → τ => σ j₀)
      (fun σ _ => mem_univ (σ j₀))).symm
  rw [← hsum, sum_congr rfl fun t _ => hfiber t, sum_const, card_univ, smul_eq_mul, mul_comm]

/-- For any distinct coordinates `j₁ ≠ j₂` in `κ` and target values `t₁, t₂ : τ`, the number of
functions `σ : κ → τ` with `σ j₁ = t₁ ∧ σ j₂ = t₂` times `(Fintype.card τ) ^ 2` equals
`Fintype.card (κ → τ)`. -/
theorem card_filter_eval_eq_and_eval_eq {κ τ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] {j₁ j₂ : κ} (hne : j₁ ≠ j₂) (t₁ t₂ : τ) :
    #{σ : κ → τ | σ j₁ = t₁ ∧ σ j₂ = t₂} * (Fintype.card τ) ^ 2 = Fintype.card (κ → τ) := by
  have hfiber (p : τ × τ) :
      #{σ : κ → τ | σ j₁ = p.1 ∧ σ j₂ = p.2} = #{σ : κ → τ | σ j₁ = t₁ ∧ σ j₂ = t₂} := by
    let e : (κ → τ) ≃ (κ → τ) :=
      Equiv.piCongrRight fun j =>
        if j = j₁ then Equiv.swap p.1 t₁
        else if j = j₂ then Equiv.swap p.2 t₂
        else Equiv.refl τ
    rw [← card_map e.toEmbedding]
    congr 1; ext σ
    simp only [mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨σ', ⟨h1, h2⟩, rfl⟩
      simp [e, Equiv.piCongrRight, Ne.symm hne, h1, h2]
    · rintro ⟨h1, h2⟩
      refine ⟨e.symm σ, ?_, e.apply_symm_apply σ⟩
      have hs1 : (e.symm σ) j₁ = Equiv.swap p.1 t₁ (σ j₁) := by
        simp [e, Equiv.piCongrRight]
      have hs2 : (e.symm σ) j₂ = Equiv.swap p.2 t₂ (σ j₂) := by
        simp [e, Equiv.piCongrRight, Ne.symm hne]
      rw [hs1, hs2, h1, h2, Equiv.swap_apply_right, Equiv.swap_apply_right]
      exact ⟨rfl, rfl⟩
  have hsum : (∑ p : τ × τ, #{σ : κ → τ | (σ j₁, σ j₂) = p}) = Fintype.card (κ → τ) := by
    rw [← card_univ]
    exact (card_eq_sum_card_fiberwise (f := fun σ : κ → τ => (σ j₁, σ j₂))
      (fun σ _ => mem_univ (σ j₁, σ j₂))).symm
  rw [← hsum]
  simp only [Prod.ext_iff]
  rw [sum_congr rfl fun p _ => hfiber p, sum_const, card_univ, Fintype.card_prod, smul_eq_mul, sq,
    mul_comm]

/-- The live coordinate set `{blockVar j (σ j) | j : κ}` obtained by selecting one element
`σ j : τ` from each block `j : κ`. -/
def blockLiveSet {κ τ ι : Type*} [Fintype κ] [DecidableEq ι] (blockVar : κ → τ → ι)
    (σ : κ → τ) : Finset ι :=
  univ.image fun j : κ => blockVar j (σ j)

@[simp]
theorem mem_blockLiveSet {κ τ ι : Type*} [Fintype κ] [DecidableEq ι] (blockVar : κ → τ → ι)
    (σ : κ → τ) (i : ι) :
    i ∈ blockLiveSet blockVar σ ↔ ∃ j : κ, blockVar j (σ j) = i := by
  simp [blockLiveSet]

/-- When `blockVar : κ → τ → ι` is injective across blocks and slots, each coordinate `i : ι`
belongs to `blockLiveSet blockVar σ` for at most `(1 / |τ|) * |κ → τ|` choices of `σ : κ → τ`. -/
theorem card_mem_blockLiveSet_le {κ τ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq ι] (blockVar : κ → τ → ι)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂) (i : ι) :
    (#{σ : κ → τ | i ∈ blockLiveSet blockVar σ} : ℝ) ≤
      (1 / (Fintype.card τ : ℝ)) * (Fintype.card (κ → τ) : ℝ) := by
  classical
  by_cases hex : ∃ j₀ t₀, blockVar j₀ t₀ = i
  · rcases hex with ⟨j₀, t₀, rfl⟩
    have htau_pos : (0 : ℝ) < (Fintype.card τ : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨t₀⟩)
    have hfilter :
        (univ.filter fun σ : κ → τ => blockVar j₀ t₀ ∈ blockLiveSet blockVar σ) =
          (univ.filter fun σ : κ → τ => σ j₀ = t₀) := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_blockLiveSet]
      refine ⟨fun ⟨j, hj⟩ => ?_, fun h => ⟨j₀, by rw [h]⟩⟩
      rcases hinj j (σ j) j₀ t₀ hj with ⟨rfl, h⟩
      exact h
    rw [hfilter, one_div_mul_eq_div, le_div_iff₀ htau_pos]
    exact_mod_cast (card_filter_eval_eq j₀ t₀).le
  · push Not at hex
    have hempty : (univ.filter fun σ : κ → τ => i ∈ blockLiveSet blockVar σ) = ∅ := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_blockLiveSet, notMem_empty, iff_false,
        not_exists]
      intro j
      exact hex j (σ j)
    rw [hempty, card_empty, Nat.cast_zero]
    positivity

/-- When `blockVar : κ → τ → ι` is injective across blocks and slots, any two distinct coordinates
`i₁ ≠ i₂` jointly belong to `blockLiveSet blockVar σ` for at most `(1 / |τ|) ^ 2 * |κ → τ|`
choices of `σ : κ → τ`. -/
theorem card_mem_and_mem_blockLiveSet_le {κ τ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq ι] (blockVar : κ → τ → ι)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂)
    {i₁ i₂ : ι} (hne : i₁ ≠ i₂) :
    (#{σ : κ → τ | i₁ ∈ blockLiveSet blockVar σ ∧ i₂ ∈ blockLiveSet blockVar σ} : ℝ) ≤
      (1 / (Fintype.card τ : ℝ)) ^ 2 * (Fintype.card (κ → τ) : ℝ) := by
  classical
  by_cases hex : (∃ j₁ t₁, blockVar j₁ t₁ = i₁) ∧ (∃ j₂ t₂, blockVar j₂ t₂ = i₂)
  · rcases hex with ⟨⟨j₁, t₁, rfl⟩, ⟨j₂, t₂, rfl⟩⟩
    have htau_pos : (0 : ℝ) < (Fintype.card τ : ℝ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨t₁⟩)
    by_cases hj : j₁ = j₂
    · subst hj
      have ht : t₁ ≠ t₂ := fun h => hne (by rw [h])
      have hempty :
          (univ.filter fun σ : κ → τ =>
            blockVar j₁ t₁ ∈ blockLiveSet blockVar σ ∧
              blockVar j₁ t₂ ∈ blockLiveSet blockVar σ) = ∅ := by
        ext σ
        simp only [mem_filter, mem_univ, true_and, mem_blockLiveSet, notMem_empty, iff_false]
        rintro ⟨⟨j', hj'⟩, ⟨j'', hj''⟩⟩
        rcases hinj j' (σ j') j₁ t₁ hj' with ⟨rfl, h1⟩
        rcases hinj j'' (σ j'') j' t₂ hj'' with ⟨rfl, h2⟩
        exact ht (h1.symm.trans h2)
      rw [hempty, card_empty, Nat.cast_zero]
      positivity
    · have hfilter :
          (univ.filter fun σ : κ → τ =>
            blockVar j₁ t₁ ∈ blockLiveSet blockVar σ ∧
              blockVar j₂ t₂ ∈ blockLiveSet blockVar σ) =
          (univ.filter fun σ : κ → τ => σ j₁ = t₁ ∧ σ j₂ = t₂) := by
        ext σ
        simp only [mem_filter, mem_univ, true_and, mem_blockLiveSet]
        refine ⟨fun ⟨⟨j', hj'⟩, ⟨j'', hj''⟩⟩ => ?_,
          fun ⟨h1, h2⟩ => ⟨⟨j₁, by rw [h1]⟩, ⟨j₂, by rw [h2]⟩⟩⟩
        rcases hinj j' (σ j') j₁ t₁ hj' with ⟨rfl, h1⟩
        rcases hinj j'' (σ j'') j₂ t₂ hj'' with ⟨rfl, h2⟩
        exact ⟨h1, h2⟩
      rw [hfilter, one_div_pow, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      exact_mod_cast (card_filter_eval_eq_and_eval_eq hj t₁ t₂).le
  · have hempty :
        (univ.filter fun σ : κ → τ =>
          i₁ ∈ blockLiveSet blockVar σ ∧ i₂ ∈ blockLiveSet blockVar σ) = ∅ := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_blockLiveSet, notMem_empty, iff_false]
      rintro ⟨⟨j₁, rfl⟩, ⟨j₂, rfl⟩⟩
      exact hex ⟨⟨j₁, σ j₁, rfl⟩, ⟨j₂, σ j₂, rfl⟩⟩
    rw [hempty, card_empty, Nat.cast_zero]
    positivity

end Cslib.Combinatorics.LittlewoodOfford
