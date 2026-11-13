/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Distinct values of random tuples and functions fixed on a set

Two counting facts behind the moment bound of [ChukhinKulikovMihajlinSmal2026], Lemma 6.4
(printed p. 16; PDF p. 17).

* **Distinct values.** For a uniform tuple `w` of `L` values from a set of size `N`, the
  expectation of `2^{-|{w_r}|}` is at most `∏_{r < L} (1 + r/N)/2`
  (`sum_half_pow_card_image_le`). Revealing the values one by one, the next value repeats an
  earlier one with probability at most `r/N`, and otherwise halves the weight.
  `prod_one_add_div_le_exp` bounds the product by `2^{-L} exp(L²/(2N))`.
* **Functions fixed on a set.** If any two Boolean functions with a property agree on a set `J`,
  at most `2^{N - |J|}` functions have it (`card_filter_le_two_pow_card_sub`).

## Main results

* `Finset.sum_half_pow_card_image_le`: the average of `2^{-|{w_r}|}`.
* `Finset.prod_one_add_div_le_exp`: `∏_{r < L} (1 + r/N) ≤ exp(L²/(2N))`.
* `Finset.card_filter_le_two_pow_card_sub`: functions determined on a set.
-/

public section

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The average of `2^{-|distinct values|}`.** Summing `(1/2)^{|{w_r}|}` over all tuples
`w : Fin L → α` gives at most `|α|^L ∏_{r < L} (1 + r/|α|)/2`. -/
theorem sum_half_pow_card_image_le (L : ℕ) :
    ∑ w : Fin L → α, ((1 : ℝ) / 2) ^ (univ.image w).card ≤
      (Fintype.card α : ℝ) ^ L * ∏ r ∈ range L, ((1 + (r : ℝ) / Fintype.card α) / 2) := by
  induction L with
  | zero => simp
  | succ L ih =>
    set N : ℝ := (Fintype.card α : ℝ)
    rcases isEmpty_or_nonempty α with hα | hα
    · simp [N, Fintype.card_eq_zero]
    have hN : 0 < N := Nat.cast_pos.2 Fintype.card_pos
    -- Split off the first value.
    have hsplit : ∑ w : Fin (L + 1) → α, ((1 : ℝ) / 2) ^ (univ.image w).card =
        ∑ w : Fin L → α, ∑ a : α, ((1 : ℝ) / 2) ^ (insert a (univ.image w)).card := by
      rw [← (Fin.consEquiv fun _ : Fin (L + 1) => α).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => ?_
      congr 2
      ext x
      simp [Fin.consEquiv, Fin.exists_fin_succ, eq_comm]
    -- For a fixed tail with image `I`, the new value repeats with weight `|I|`.
    have hinner (I : Finset α) (hI : I.card ≤ L) :
        ∑ a : α, ((1 : ℝ) / 2) ^ (insert a I).card ≤
          ((1 : ℝ) / 2) ^ I.card * ((N + L) / 2) := by
      have hc : ((univ.filter fun a => a ∉ I).card : ℝ) = N - I.card := by
        rw [filter_not, card_sdiff_of_subset (filter_subset _ _), filter_mem_eq_inter, univ_inter,
          card_univ, Nat.cast_sub (card_le_univ I)]
      have h1 : ∑ a ∈ univ.filter (· ∈ I), ((1 : ℝ) / 2) ^ (insert a I).card =
          (I.card : ℝ) * (1 / 2) ^ I.card := by
        rw [sum_congr rfl fun a ha => by rw [insert_eq_of_mem (mem_filter.1 ha).2], sum_const,
          nsmul_eq_mul, filter_mem_eq_inter, univ_inter]
      have h2 : ∑ a ∈ univ.filter (· ∉ I), ((1 : ℝ) / 2) ^ (insert a I).card =
          (N - I.card) * (1 / 2) ^ (I.card + 1) := by
        rw [sum_congr rfl fun a ha => by rw [card_insert_of_notMem (mem_filter.1 ha).2],
          sum_const, nsmul_eq_mul, hc]
      rw [← sum_filter_add_sum_filter_not univ (· ∈ I), h1, h2, pow_succ]
      have hI' : (I.card : ℝ) ≤ L := by exact_mod_cast hI
      have hp : (0 : ℝ) < (1 / 2) ^ I.card := by positivity
      nlinarith
    rw [hsplit, prod_range_succ, pow_succ]
    calc ∑ w : Fin L → α, ∑ a : α, ((1 : ℝ) / 2) ^ (insert a (univ.image w)).card
        ≤ ∑ w : Fin L → α, ((1 : ℝ) / 2) ^ (univ.image w).card * ((N + L) / 2) :=
          sum_le_sum fun w _ => hinner _ ((card_image_le).trans (by simp))
      _ = (∑ w : Fin L → α, ((1 : ℝ) / 2) ^ (univ.image w).card) * ((N + L) / 2) := by
          rw [sum_mul]
      _ ≤ (N ^ L * ∏ r ∈ range L, ((1 + r / N) / 2)) * ((N + L) / 2) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
      _ = N ^ L * N * ((∏ r ∈ range L, ((1 + r / N) / 2)) * ((1 + L / N) / 2)) := by
          field_simp

/-- `∏_{r < L} (1 + r/N) ≤ exp(L²/(2N))` for `N > 0`. -/
theorem prod_one_add_div_le_exp (L : ℕ) {N : ℝ} (hN : 0 < N) :
    ∏ r ∈ range L, (1 + (r : ℝ) / N) ≤ Real.exp ((L : ℝ) ^ 2 / (2 * N)) := by
  refine (Real.prod_one_add_le_exp_sum _ fun r => by positivity).trans
    (Real.exp_le_exp.2 ?_)
  rw [← sum_div]
  have h := sum_range_id_mul_two L
  have h2 : (∑ r ∈ range L, (r : ℝ)) * 2 ≤ (L : ℝ) ^ 2 := by
    have : ((∑ r ∈ range L, r : ℕ) : ℝ) * 2 = (L * (L - 1) : ℕ) := by exact_mod_cast h
    push_cast at this
    rw [this]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · simp [hL]
    · rw [Nat.cast_sub hL]
      push_cast
      nlinarith
  rw [div_le_div_iff₀ hN (by positivity)]
  nlinarith

/-- **Functions fixed on a set.** If any two Boolean functions with a property `P` agree on `J`,
then at most `2^{|α| - |J|}` functions have `P`. -/
theorem card_filter_le_two_pow_card_sub (J : Finset α) (P : (α → Bool) → Prop) [DecidablePred P]
    (h : ∀ g g', P g → P g' → ∀ x ∈ J, g x = g' x) :
    (univ.filter P).card ≤ 2 ^ (Fintype.card α - J.card) := by
  have hinj : Set.InjOn (fun (g : α → Bool) (x : {x // x ∉ J}) => g x) (univ.filter P) := by
    intro g hg g' hg' hgg'
    funext x
    by_cases hx : x ∈ J
    · exact h g g' (mem_filter.1 hg).2 (mem_filter.1 hg').2 x hx
    · exact congrFun hgg' ⟨x, hx⟩
  calc (univ.filter P).card ≤ (univ : Finset ({x // x ∉ J} → Bool)).card :=
        card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj
    _ = 2 ^ (Fintype.card α - J.card) := by
        rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
          Fintype.card_coe]

end Finset
