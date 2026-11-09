/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hitting a spread family with a random set

Let `x₀, x₁, …` be subsets of a finite type `U`, and let `y` be a uniformly random subset of `U`.
The events `xₖ ⊆ y` are increasing, and two of them are independent when the sets are disjoint.
Janson's inequality bounds the probability that `y` contains no `xₖ`
[Alon and Spencer, Chapter 8][AlonSpencer2016]. We prove a deterministic, greedy form of it.
Suppose each `xₖ` overlaps the earlier sets only a little:
`∑_{j < k, xⱼ ∩ xₖ ≠ ∅} 2 ^ (-#(xⱼ \ xₖ)) ≤ 1 / 2`. Then the fraction of subsets that contain no
`xₖ` is at most `∏ₖ (1 - 2 ^ (-#xₖ - 1))` (`Cslib.card_filter_forall_not_subset_le`). The
proof conditions on the sets that are disjoint from `xₖ`, which are independent of the event
`xₖ ⊆ y`. It bounds the other overlaps with the Harris–Kleitman inequality, since the family of
subsets avoiding the earlier sets is a lower set.

Forbidding arbitrary patterns, rather than the all-ones pattern, leaves at most as many subsets:
`Cslib.card_filter_avoidsPatterns_le` turns the forbidden patterns `y ∩ xₖ = βₖ` into
`xₖ ⊆ y`, one element at a time [Mertz and Pitassi, Claim 2.3][MertzPitassi2020].

A family `X` of `N`-element sets is `r`-*spread* when every nonempty `T` lies in at most
`#X / r ^ #T` of its members. A greedy choice finds `K` members of such a family with small
overlaps whenever `K ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2` (`Cslib.exists_seq_overlap_le_of_spread`).
So few subsets avoid every pattern on a spread family
(`Cslib.card_filter_avoidsPatterns_le_of_spread`).
This replaces the spread (robust sunflower) lemma in the proof of the full-range lemma of
query-to-communication lifting [Mertz and Pitassi, Lemma 3.2][MertzPitassi2020], at the cost of a
larger spread. The greedy form and its use there are original to this library.

## Main results

* `Cslib.card_filter_forall_not_subset_le`: the greedy Janson bound.
* `Cslib.card_filter_avoidsPatterns_le`: forbidding the all-ones patterns is the worst case.
* `Cslib.exists_seq_overlap_le_of_spread`: spread families contain long sequences with small
  overlaps.
* `Cslib.card_filter_avoidsPatterns_le_of_spread`: few subsets avoid every pattern on a spread
  family.

## References

* [N. Alon and J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [I. Mertz and T. Pitassi, *Lifting: As Easy As 1, 2, 3*][MertzPitassi2020]
-/

@[expose] public section

namespace Cslib

open Finset

variable {U : Type*} [DecidableEq U]

/-! ### Independence from the elements of a set -/

/-- If membership in `D` ignores the elements of `s`, then exactly a `2 ^ (-#s)` fraction of `D`
contains `s`. -/
theorem card_filter_subset_mul_two_pow {s : Finset U} {D : Finset (Finset U)}
    (hD : ∀ y, y ∈ D ↔ y \ s ∈ D) : #(D.filter (s ⊆ ·)) * 2 ^ #s = #D := by
  rw [← card_powerset, ← card_product]
  refine card_nbij' (fun p => p.1 \ s ∪ p.2) (fun y => (y ∪ s, y ∩ s)) ?_ ?_ ?_ ?_
  · rintro ⟨y, z⟩ h
    simp only [coe_product, coe_filter, coe_powerset, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at h
    simp only [mem_coe]
    rw [hD, show (y \ s ∪ z) \ s = y \ s by
      ext a; simp only [mem_sdiff, mem_union]; have := @h.2 a; tauto, ← hD]
    exact h.1.1
  · intro y hy
    simp only [mem_coe] at hy
    simp only [coe_product, coe_filter, coe_powerset, Set.mem_prod, Set.mem_ofPred_eq]
    refine ⟨⟨?_, subset_union_right⟩, inter_subset_right⟩
    rw [hD, show (y ∪ s) \ s = y \ s by ext a; simp only [mem_sdiff, mem_union]; tauto, ← hD]
    exact hy
  · rintro ⟨y, z⟩ h
    simp only [coe_product, coe_filter, coe_powerset, Set.mem_prod, Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]
    constructor
    · ext a; simp only [mem_union, mem_sdiff]; have := @h.1.2 a; have := @h.2 a; tauto
    · ext a; simp only [mem_inter, mem_union, mem_sdiff]; have := @h.2 a; tauto
  · intro y _
    ext a; simp only [mem_union, mem_sdiff, mem_inter]; tauto

variable [Fintype U]

/-- Exactly `2 ^ (#U - #s)` subsets of `U` contain `s`. -/
theorem card_filter_subset_univ_mul_two_pow (s : Finset U) :
    #((univ : Finset (Finset U)).filter (s ⊆ ·)) * 2 ^ #s = 2 ^ Fintype.card U := by
  rw [card_filter_subset_mul_two_pow (by simp), card_univ, Fintype.card_finset]

/-! ### The greedy Janson bound -/

/-- The subsets of `U` that contain none of `x 0, …, x (K - 1)`. -/
noncomputable abbrev avoiders (x : ℕ → Finset U) (K : ℕ) : Finset (Finset U) :=
  univ.filter fun y => ∀ k < K, ¬ x k ⊆ y

/-- The step of the greedy Janson bound: if `x K` overlaps the earlier sets only a little, then at
least a `2 ^ (-#(x K) - 1)` fraction of the subsets avoiding the earlier sets contain `x K`. -/
theorem card_avoiders_mul_le_card_filter (x : ℕ → Finset U) (K : ℕ)
    (hK : ∑ j ∈ (range K).filter (fun j => ¬ Disjoint (x j) (x K)),
      (1 / 2 : ℝ) ^ #(x j \ x K) ≤ 1 / 2) :
    (#(avoiders x K) : ℝ) * (1 / 2) ^ (#(x K) + 1) ≤
      #((avoiders x K).filter (x K ⊆ ·)) := by
  set s := x K
  set C := (range K).filter (fun j => ¬ Disjoint (x j) s)
  set D : Finset (Finset U) := univ.filter fun y => ∀ j < K, Disjoint (x j) s → ¬ x j ⊆ y
  have hAD : avoiders x K ⊆ D := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, D] at hy ⊢
    exact fun j hj _ => hy j hj
  have hD : ∀ y, y ∈ D ↔ y \ s ∈ D := by
    intro y
    simp only [mem_filter, mem_univ, true_and, D]
    refine forall₂_congr fun j _ => imp_congr_right fun hj => not_congr ?_
    rw [subset_sdiff]
    exact (and_iff_left hj).symm
  have hDlow : IsLowerSet (D : Set (Finset U)) := by
    intro a b hba ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, D] at ha ⊢
    exact fun j hj hjs hsub => ha j hj hjs (hsub.trans hba)
  -- the fraction of `D` containing `s`
  have hDs : (#(D.filter (s ⊆ ·)) : ℝ) = #D * (1 / 2) ^ #s := by
    have := card_filter_subset_mul_two_pow hD
    rw [one_div, inv_pow, ← div_eq_mul_inv, eq_div_iff (by positivity)]
    exact_mod_cast this
  -- the overlapping pairs, by Harris–Kleitman
  have hpair : ∀ j ∈ C, (#(D ∩ univ.filter (s ∪ x j ⊆ ·)) : ℝ) ≤
      #D * (1 / 2) ^ #s * (1 / 2) ^ #(x j \ s) := by
    intro j _
    have hup : IsUpperSet ((univ.filter (s ∪ x j ⊆ ·) : Finset (Finset U)) : Set (Finset U)) := by
      intro a b hab ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      exact ha.trans hab
    have hHK := hDlow.card_inter_le_finset hup
    have hcnt := card_filter_subset_univ_mul_two_pow (s ∪ x j)
    have hunion : #(s ∪ x j) = #s + #(x j \ s) := by
      rw [← card_union_of_disjoint disjoint_sdiff, union_sdiff_self_eq_union]
    rw [hunion] at hcnt
    have h2 : (0 : ℝ) < 2 ^ Fintype.card U := by positivity
    have hHK' : (2 : ℝ) ^ Fintype.card U * #(D ∩ univ.filter (s ∪ x j ⊆ ·)) ≤
        #D * #((univ : Finset (Finset U)).filter (s ∪ x j ⊆ ·)) := by exact_mod_cast hHK
    have hcnt' : (#((univ : Finset (Finset U)).filter (s ∪ x j ⊆ ·)) : ℝ) * 2 ^ (#s + #(x j \ s))
        = 2 ^ Fintype.card U := by exact_mod_cast hcnt
    have hpow : (1 / 2 : ℝ) ^ #s * (1 / 2) ^ #(x j \ s) * 2 ^ (#s + #(x j \ s)) = 1 := by
      rw [← pow_add, ← mul_pow]; norm_num
    have hb : (#((univ : Finset (Finset U)).filter (s ∪ x j ⊆ ·)) : ℝ) =
        2 ^ Fintype.card U * ((1 / 2) ^ #s * (1 / 2) ^ #(x j \ s)) := by
      rw [← hcnt']
      linear_combination (-(#((univ : Finset (Finset U)).filter (s ∪ x j ⊆ ·)) : ℝ)) * hpow
    rw [hb] at hHK'
    refine le_of_mul_le_mul_left ?_ h2
    calc (2 : ℝ) ^ Fintype.card U * #(D ∩ univ.filter (s ∪ x j ⊆ ·)) ≤ _ := hHK'
      _ = _ := by ring
  -- the subsets of `D` containing `s` either avoid all earlier sets or contain an overlapping one
  have hcover : D.filter (s ⊆ ·) ⊆
      (avoiders x K).filter (s ⊆ ·) ∪ C.biUnion fun j => D ∩ univ.filter (s ∪ x j ⊆ ·) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, D] at hy
    by_cases hA : ∀ k < K, ¬ x k ⊆ y
    · exact mem_union_left _ (by simp only [mem_filter, mem_univ, true_and]; exact ⟨hA, hy.2⟩)
    · push Not at hA
      obtain ⟨k, hk, hsub⟩ := hA
      have hdisj : ¬ Disjoint (x k) s := fun h => hy.1 k hk h hsub
      refine mem_union_right _ (mem_biUnion.mpr ⟨k, ?_, ?_⟩)
      · simp only [mem_filter, mem_range, C]; exact ⟨hk, hdisj⟩
      · simp only [mem_inter, mem_filter, mem_univ, true_and, D]
        exact ⟨hy.1, union_subset hy.2 hsub⟩
  have hcard := card_le_card hcover
  have hcard' : (#(D.filter (s ⊆ ·)) : ℝ) ≤ (#((avoiders x K).filter (s ⊆ ·)) : ℝ) +
      ∑ j ∈ C, (#D : ℝ) * (1 / 2) ^ #s * (1 / 2) ^ #(x j \ s) := by
    refine (Nat.cast_le.mpr hcard).trans ?_
    refine (Nat.cast_le.mpr (card_union_le _ _)).trans ?_
    push_cast
    gcongr
    refine (Nat.cast_le.mpr card_biUnion_le).trans ?_
    push_cast
    exact sum_le_sum hpair
  rw [← mul_sum, hDs] at hcard'
  have hAD' : (#(avoiders x K) : ℝ) ≤ #D := by exact_mod_cast card_le_card hAD
  have hpos : (0 : ℝ) ≤ #D * (1 / 2) ^ #s := by positivity
  have hle : (#D : ℝ) * (1 / 2) ^ #s * (1 / 2) ≤ #((avoiders x K).filter (s ⊆ ·)) := by
    nlinarith [mul_le_mul_of_nonneg_left hK hpos]
  calc (#(avoiders x K) : ℝ) * (1 / 2) ^ (#s + 1)
      = #(avoiders x K) * (1 / 2) ^ #s * (1 / 2) := by rw [pow_succ, mul_assoc]
    _ ≤ #D * (1 / 2) ^ #s * (1 / 2) := by gcongr
    _ ≤ _ := hle

/-- **The greedy Janson bound.** If each `x k` overlaps the earlier sets only a little, at most a
`∏ₖ (1 - 2 ^ (-#(x k) - 1))` fraction of the subsets of `U` contain none of
`x 0, …, x (K - 1)`. -/
theorem card_filter_forall_not_subset_le (x : ℕ → Finset U) (K : ℕ)
    (hx : ∀ k < K, ∑ j ∈ (range k).filter (fun j => ¬ Disjoint (x j) (x k)),
      (1 / 2 : ℝ) ^ #(x j \ x k) ≤ 1 / 2) :
    (#((univ : Finset (Finset U)).filter fun y => ∀ k < K, ¬ x k ⊆ y) : ℝ) ≤
      2 ^ Fintype.card U * ∏ k ∈ range K, (1 - (1 / 2 : ℝ) ^ (#(x k) + 1)) := by
  induction K with
  | zero => simp [Fintype.card_finset]
  | succ K ih =>
    have hstep := card_avoiders_mul_le_card_filter x K (hx K (Nat.lt_succ_self K))
    have hsplit : avoiders x (K + 1) = (avoiders x K).filter (¬ x K ⊆ ·) := by
      ext y
      simp only [mem_filter, mem_univ, true_and, Nat.lt_succ_iff_lt_or_eq]
      constructor
      · intro h; exact ⟨fun k hk => h k (Or.inl hk), h K (Or.inr rfl)⟩
      · rintro ⟨h, hK⟩ k (hk | rfl)
        · exact h k hk
        · exact hK
    have hsum := card_filter_add_card_filter_not (s := avoiders x K) (x K ⊆ ·)
    have hfac : (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ (#(x K) + 1) := by
      rw [sub_nonneg]; exact pow_le_one₀ (by norm_num) (by norm_num)
    have ih' := ih fun k hk => hx k (Nat.lt_succ_of_lt hk)
    change (#(avoiders x (K + 1)) : ℝ) ≤ _
    rw [hsplit, prod_range_succ, ← mul_assoc]
    have hsum' : (#((avoiders x K).filter (x K ⊆ ·)) : ℝ) +
        #((avoiders x K).filter (¬ x K ⊆ ·)) = #(avoiders x K) := by exact_mod_cast hsum
    calc (#((avoiders x K).filter (¬ x K ⊆ ·)) : ℝ)
        ≤ #(avoiders x K) * (1 - (1 / 2 : ℝ) ^ (#(x K) + 1)) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right ih' hfac

/-! ### Forbidding arbitrary patterns -/

section Patterns

variable {ι : Type*}

/-- `y` avoids the pattern `β i` on `s i` for every `i ∈ I`: each `s i` has an element whose
membership in `y` differs from `β i`. -/
def AvoidsPatterns (I : Finset ι) (s : ι → Finset U) (β : ι → U → Bool) (y : Finset U) : Prop :=
  ∀ i ∈ I, ∃ u ∈ s i, decide (u ∈ y) ≠ β i u

instance (I : Finset ι) (s : ι → Finset U) (β : ι → U → Bool) :
    DecidablePred (AvoidsPatterns I s β) := fun _ => by
  unfold AvoidsPatterns; infer_instance

/-- Splitting the subsets of `U` by whether they contain `u`. -/
theorem card_filter_eq_add_card_filter_insert (u : U) (P : Finset U → Prop) [DecidablePred P] :
    #((univ : Finset (Finset U)).filter P) =
      #((univ : Finset (Finset U)).filter fun y => u ∉ y ∧ P y) +
        #((univ : Finset (Finset U)).filter fun y => u ∉ y ∧ P (insert u y)) := by
  rw [← card_filter_add_card_filter_not (s := univ.filter P) (u ∉ ·), filter_filter,
    filter_filter]
  congr 1
  · congr 1; ext y; simp only [mem_filter, mem_univ, true_and]; tauto
  · refine card_nbij' (fun y => y.erase u) (fun y => insert u y) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not] at hy ⊢
      exact ⟨notMem_erase u y, by rw [insert_erase hy.2]; exact hy.1⟩
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not] at hy ⊢
      exact ⟨hy.2, mem_insert_self u y⟩
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not] at hy
      exact insert_erase hy.2
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy
      exact erase_insert hy.1

/-- Changing every pattern to `true` at one element does not decrease the number of subsets
avoiding the patterns [Mertz and Pitassi, Claim 2.3][MertzPitassi2020]. -/
theorem card_filter_avoidsPatterns_le_update (I : Finset ι) (s : ι → Finset U)
    (β : ι → U → Bool) (u : U) :
    #((univ : Finset (Finset U)).filter (AvoidsPatterns I s β)) ≤
      #((univ : Finset (Finset U)).filter
        (AvoidsPatterns I s fun i v => if v = u then true else β i v)) := by
  set β' : ι → U → Bool := fun i v => if v = u then true else β i v
  rw [card_filter_eq_add_card_filter_insert u (AvoidsPatterns I s β),
    card_filter_eq_add_card_filter_insert u (AvoidsPatterns I s β')]
  -- a witness other than `u` keeps working
  have hmove : ∀ {y y' : Finset U} {i v}, v ≠ u → (v ∈ y ↔ v ∈ y') →
      decide (v ∈ y) ≠ β i v → decide (v ∈ y') ≠ β' i v := by
    intro y y' i v hv hyy' h
    simp only [β', hv, ite_false]
    rwa [← decide_eq_decide.mpr hyy']
  -- (1) avoiding the old patterns, with or without `u`, gives the new ones without `u`
  have h1 : ∀ y : Finset U, u ∉ y →
      (AvoidsPatterns I s β y ∨ AvoidsPatterns I s β (insert u y)) →
        AvoidsPatterns I s β' y := by
    intro y hu h i hi
    by_cases hus : u ∈ s i
    · exact ⟨u, hus, by simp [β', hu]⟩
    · rcases h with h | h
      · obtain ⟨v, hv, hne⟩ := h i hi
        have hvu : v ≠ u := fun e => hus (e ▸ hv)
        exact ⟨v, hv, hmove hvu Iff.rfl hne⟩
      · obtain ⟨v, hv, hne⟩ := h i hi
        have hvu : v ≠ u := fun e => hus (e ▸ hv)
        exact ⟨v, hv, hmove hvu (by simp [hvu]) hne⟩
  -- (2) avoiding the old patterns both with and without `u` gives the new ones with `u`
  have h2 : ∀ y : Finset U, u ∉ y →
      (AvoidsPatterns I s β y ∧ AvoidsPatterns I s β (insert u y)) →
        AvoidsPatterns I s β' (insert u y) := by
    intro y hu ⟨ha, hb⟩ i hi
    obtain ⟨v₁, hv₁, hne₁⟩ := ha i hi
    obtain ⟨v₂, hv₂, hne₂⟩ := hb i hi
    by_cases h₁ : v₁ = u
    · by_cases h₂ : v₂ = u
      · rw [h₁] at hne₁
        rw [h₂] at hne₂
        simp only [hu, decide_false, mem_insert_self, decide_true] at hne₁ hne₂
        cases h : β i u <;> simp_all
      · exact ⟨v₂, hv₂, hmove h₂ Iff.rfl hne₂⟩
    · exact ⟨v₁, hv₁, hmove h₁ (by simp [h₁]) hne₁⟩
  have key : ∀ y ∈ (univ : Finset (Finset U)).filter (u ∉ ·),
      (if AvoidsPatterns I s β y then 1 else 0) +
        (if AvoidsPatterns I s β (insert u y) then 1 else 0) ≤
      (if AvoidsPatterns I s β' y then 1 else 0) +
        (if AvoidsPatterns I s β' (insert u y) then 1 else 0) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    have := h1 y hy
    have := h2 y hy
    split_ifs <;> simp_all
  have := sum_le_sum key
  rw [sum_add_distrib, sum_add_distrib] at this
  simp only [sum_boole, Nat.cast_id, filter_filter] at this
  convert this using 2

/-- **Monotonization.** Forbidding the all-ones patterns is the worst case: at most as many
subsets of `U` avoid arbitrary patterns `β i` on the sets `s i` as contain none of the `s i`
[Mertz and Pitassi, Claim 2.3][MertzPitassi2020]. -/
theorem card_filter_avoidsPatterns_le (I : Finset ι) (s : ι → Finset U) (β : ι → U → Bool) :
    #((univ : Finset (Finset U)).filter (AvoidsPatterns I s β)) ≤
      #((univ : Finset (Finset U)).filter fun y => ∀ i ∈ I, ¬ s i ⊆ y) := by
  have key : ∀ V : Finset U, #((univ : Finset (Finset U)).filter (AvoidsPatterns I s β)) ≤
      #((univ : Finset (Finset U)).filter
        (AvoidsPatterns I s fun i v => if v ∈ V then true else β i v)) := by
    intro V
    induction V using Finset.induction_on with
    | empty => simp
    | insert u V _ ih =>
      refine ih.trans ((card_filter_avoidsPatterns_le_update I s _ u).trans_eq ?_)
      have hβ : (fun i v => if v = u then true else if v ∈ V then true else β i v) =
          fun i v => if v ∈ insert u V then true else β i v := by
        funext i v
        by_cases hv : v = u <;> simp [hv]
      rw [hβ]
  refine (key univ).trans_eq ?_
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, AvoidsPatterns, ite_true, ne_eq, decide_eq_true_eq,
    not_subset]

end Patterns

/-! ### Spread families -/

section Spread

variable {X : Finset (Finset U)} {N : ℕ} {r : ℝ}

omit [Fintype U] in
/-- A spread family of `N`-element sets overlaps a fixed `N`-element set `t` only a little: the
members meeting `t` have total weight `∑ 2 ^ (-#(t \ y)) ≤ #X 2 ^ (-N) ((1 + 2 / r) ^ N - 1)`. -/
theorem sum_filter_not_disjoint_le_of_spread (hr : 0 < r)
    (hspread : ∀ T : Finset U, T.Nonempty → (#(X.filter (T ⊆ ·)) : ℝ) * r ^ #T ≤ #X)
    {t : Finset U} (ht : #t = N) :
    ∑ y ∈ X.filter (fun y => ¬ Disjoint t y), (1 / 2 : ℝ) ^ #(t \ y) ≤
      #X * (1 / 2) ^ N * ((1 + 2 / r) ^ N - 1) := by
  set g : Finset U → ℝ := fun T => if T.Nonempty then (1 / 2 : ℝ) ^ (N - #T) else 0
  have hg : ∀ y, (if ¬ Disjoint t y then (1 / 2 : ℝ) ^ #(t \ y) else 0) = g (t ∩ y) := by
    intro y
    simp only [g, not_disjoint_iff_nonempty_inter, card_sdiff, inter_comm y t, ht]
  rw [sum_filter, sum_congr rfl fun y _ => hg y]
  rw [← sum_fiberwise_of_maps_to (g := fun y => t ∩ y) (t := t.powerset)
    (fun y _ => mem_powerset.mpr inter_subset_left)]
  have hfib : ∀ T ∈ t.powerset, ∑ y ∈ X with t ∩ y = T, g (t ∩ y) ≤
      if T.Nonempty then #X * ((1 / r) ^ #T * (1 / 2) ^ (N - #T)) else 0 := by
    intro T _
    rw [sum_congr rfl fun y hy => by rw [(mem_filter.mp hy).2], sum_const, nsmul_eq_mul]
    simp only [g]
    split_ifs with hT
    · have hsub : X.filter (fun y => t ∩ y = T) ⊆ X.filter (T ⊆ ·) := by
        intro y hy
        simp only [mem_filter] at hy ⊢
        exact ⟨hy.1, hy.2 ▸ inter_subset_right⟩
      have h1 := hspread T hT
      have hc : (#(X.filter fun y => t ∩ y = T) : ℝ) ≤ #X * (1 / r) ^ #T := by
        have hc' : (#(X.filter fun y => t ∩ y = T) : ℝ) ≤ #(X.filter (T ⊆ ·)) := by
          exact_mod_cast card_le_card hsub
        rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        exact (mul_le_mul_of_nonneg_right hc' (by positivity)).trans h1
      calc (#(X.filter fun y => t ∩ y = T) : ℝ) * (1 / 2) ^ (N - #T)
          ≤ #X * (1 / r) ^ #T * (1 / 2) ^ (N - #T) := by gcongr
        _ = _ := by ring
    · simp
  refine (sum_le_sum hfib).trans_eq ?_
  rw [← sum_filter, show t.powerset.filter (fun T => T.Nonempty) = t.powerset.erase ∅ by
    ext T; simp [nonempty_iff_ne_empty, and_comm], ← mul_sum,
    sum_erase_eq_sub (empty_mem_powerset t)]
  have hbin := sum_pow_mul_eq_add_pow (1 / r) (1 / 2 : ℝ) t
  rw [ht] at hbin
  rw [hbin]
  simp only [card_empty, pow_zero, one_mul, Nat.sub_zero]
  have : (1 / r + 1 / 2 : ℝ) ^ N = (1 / 2) ^ N * (1 + 2 / r) ^ N := by
    rw [← mul_pow]; congr 1; field_simp; ring
  rw [this]
  ring

omit [Fintype U] in
/-- **Greedy choice.** An `r`-spread family of `N`-element sets contains `K` members with small
overlaps whenever `K ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2`. -/
theorem exists_seq_overlap_le_of_spread (hr : 0 < r)
    (hspread : ∀ T : Finset U, T.Nonempty → (#(X.filter (T ⊆ ·)) : ℝ) * r ^ #T ≤ #X)
    (hN : ∀ x ∈ X, #x = N) (hX : X.Nonempty) {K : ℕ}
    (hK : K * ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2) :
    ∃ x : ℕ → Finset U, (∀ k < K, x k ∈ X) ∧
      ∀ k < K, ∑ j ∈ (range k).filter (fun j => ¬ Disjoint (x j) (x k)),
        (1 / 2 : ℝ) ^ #(x j \ x k) ≤ 1 / 2 := by
  have hgrow : (0 : ℝ) ≤ (1 + 2 / r) ^ N - 1 := by
    rw [sub_nonneg]; exact one_le_pow₀ (by linarith [div_pos two_pos hr])
  induction K with
  | zero => exact ⟨fun _ => hX.choose, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨x, hxX, hx⟩ := ih (le_trans (by gcongr; simp) hK)
    -- some member of `X` overlaps `x 0, …, x (K - 1)` only a little
    have hsum : ∑ y ∈ X, ∑ j ∈ (range K).filter (fun j => ¬ Disjoint (x j) y),
        (1 / 2 : ℝ) ^ #(x j \ y) ≤ ∑ _y ∈ X, (1 / 2 : ℝ) := by
      simp_rw [sum_filter]
      rw [sum_comm]
      simp_rw [← sum_filter]
      calc ∑ j ∈ range K, ∑ y ∈ X.filter (fun y => ¬ Disjoint (x j) y),
            (1 / 2 : ℝ) ^ #(x j \ y)
          ≤ ∑ _j ∈ range K, #X * (1 / 2) ^ N * ((1 + 2 / r) ^ N - 1) := by
            refine sum_le_sum fun j hj => ?_
            exact sum_filter_not_disjoint_le_of_spread hr hspread
              (hN _ (hxX j (mem_range.mp hj)))
        _ ≤ _ := by
            rw [sum_const, sum_const, card_range, nsmul_eq_mul, nsmul_eq_mul]
            have hK' : ((K : ℝ) + 1) * ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2 := by
              exact_mod_cast hK
            have h2N : (1 / 2 : ℝ) ^ N * 2 ^ N = 1 := by rw [← mul_pow]; norm_num
            have hXpos : (0 : ℝ) ≤ #X := by positivity
            have hhalf : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hK' (mul_nonneg hXpos hhalf),
              mul_nonneg (mul_nonneg hXpos hhalf) hgrow]
    obtain ⟨y, hyX, hy⟩ := exists_le_of_sum_le hX hsum
    refine ⟨fun k => if k < K then x k else y, fun k hk => ?_, fun k hk => ?_⟩
    · by_cases hkK : k < K
      · simp only [hkK, ite_true]; exact hxX k hkK
      · simp only [hkK, ite_false]; exact hyX
    · have hfix : ∀ j < k, (if j < K then x j else y) = x j := fun j hj => by
        have : j < K := by omega
        simp [this]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkK | rfl
      · simp only [hkK, ite_true]
        rw [filter_congr fun j hj => by rw [hfix j (mem_range.mp hj)],
          sum_congr rfl fun j hj => by rw [hfix j (mem_range.mp (mem_filter.mp hj).1)]]
        exact hx k hkK
      · simp only [lt_irrefl, ite_false]
        rw [filter_congr fun j hj => by rw [hfix j (mem_range.mp hj)],
          sum_congr rfl fun j hj => by rw [hfix j (mem_range.mp (mem_filter.mp hj).1)]]
        exact hy

/-- **Few subsets avoid every pattern on a spread family.** If `X` is an `r`-spread family of
`N`-element sets and `K ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2`, then at most a
`(1 - 2 ^ (-N - 1)) ^ K` fraction of the subsets `y` of `U` avoid the pattern `β x` on every
`x ∈ X`. -/
theorem card_filter_avoidsPatterns_le_of_spread (hr : 0 < r)
    (hspread : ∀ T : Finset U, T.Nonempty → (#(X.filter (T ⊆ ·)) : ℝ) * r ^ #T ≤ #X)
    (hN : ∀ x ∈ X, #x = N) (hX : X.Nonempty) {K : ℕ}
    (hK : K * ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2) (β : Finset U → U → Bool) :
    (#((univ : Finset (Finset U)).filter (AvoidsPatterns X id β)) : ℝ) ≤
      2 ^ Fintype.card U * (1 - (1 / 2 : ℝ) ^ (N + 1)) ^ K := by
  obtain ⟨x, hxX, hx⟩ := exists_seq_overlap_le_of_spread hr hspread hN hX hK
  have hmono := card_filter_avoidsPatterns_le X id β
  have hsub : ((univ : Finset (Finset U)).filter fun y => ∀ i ∈ X, ¬ id i ⊆ y) ⊆
      (univ : Finset (Finset U)).filter fun y => ∀ k < K, ¬ x k ⊆ y := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and, id] at hy ⊢
    exact fun k hk => hy _ (hxX k hk)
  have hjanson := card_filter_forall_not_subset_le x K hx
  rw [prod_congr rfl fun k hk => by rw [hN _ (hxX k (mem_range.mp hk))], prod_const,
    card_range] at hjanson
  have h2 := card_le_card hsub
  have h3 : #((univ : Finset (Finset U)).filter (AvoidsPatterns X id β)) ≤
      #((univ : Finset (Finset U)).filter fun y => ∀ k < K, ¬ x k ⊆ y) :=
    hmono.trans (by convert h2)
  refine le_trans ?_ hjanson
  exact_mod_cast h3

omit [DecidableEq U] [Fintype U] in
/-- `(1 + a) ^ N ≤ 1 + 2 a N` when `0 ≤ a` and `a N ≤ 1 / 2`. -/
theorem one_add_pow_le_one_add_two_mul {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (h : a * N ≤ 1 / 2) :
    (1 + a) ^ N ≤ 1 + 2 * a * N := by
  have key : ∀ k : ℕ, (1 + a) ^ k * (1 - a * k) ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hpos : (0 : ℝ) ≤ (1 + a) ^ k := by positivity
      push_cast
      have : (1 + a) * (1 - a * (k + 1)) ≤ 1 - a * k := by nlinarith [sq_nonneg a]
      calc (1 + a) ^ (k + 1) * (1 - a * (k + 1)) = (1 + a) ^ k * ((1 + a) * (1 - a * (k + 1))) := by
            ring
        _ ≤ (1 + a) ^ k * (1 - a * k) := mul_le_mul_of_nonneg_left this hpos
        _ ≤ 1 := ih
  have hk := key N
  have hpos : (0 : ℝ) ≤ (1 + a) ^ N := by positivity
  have haN : 0 ≤ a * N := by positivity
  have hP : (1 + a) ^ N ≤ 2 := by nlinarith
  nlinarith

/-- **Few subsets avoid every pattern on a spread family**, in exponential form: if `X` is an
`r`-spread family of `N`-element sets with `16 N (D + 1) ≤ r`, then at most a `2 ^ (-D - 1)`
fraction of the subsets of `U` avoid the pattern `β x` on every `x ∈ X`. -/
theorem card_filter_avoidsPatterns_mul_two_pow_le_of_spread (hr : 0 < r)
    (hspread : ∀ T : Finset U, T.Nonempty → (#(X.filter (T ⊆ ·)) : ℝ) * r ^ #T ≤ #X)
    (hN : ∀ x ∈ X, #x = N) (hX : X.Nonempty) {D : ℕ} (hD : 16 * N * (D + 1) ≤ r)
    (β : Finset U → U → Bool) :
    (#((univ : Finset (Finset U)).filter (AvoidsPatterns X id β)) : ℝ) * 2 ^ (D + 1) ≤
      2 ^ Fintype.card U := by
  set K := 2 ^ (N + 1) * (D + 1)
  have hD1 : (1 : ℝ) ≤ D + 1 := by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hNr : 2 / r * N ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr]
    nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hgrow := one_add_pow_le_one_add_two_mul (by positivity) hNr
  have hK : (K : ℝ) * ((1 + 2 / r) ^ N - 1) ≤ 2 ^ N / 2 := by
    have hK0 : (0 : ℝ) ≤ K := by positivity
    calc (K : ℝ) * ((1 + 2 / r) ^ N - 1) ≤ K * (2 * (2 / r) * N) := by gcongr; linarith
      _ = 2 ^ N * (8 * N * (D + 1) / r) := by
          simp only [K]; push_cast; rw [pow_succ]; field_simp; ring
      _ ≤ 2 ^ N * (1 / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ hr]; linarith
      _ = 2 ^ N / 2 := by ring
  have hmain := card_filter_avoidsPatterns_le_of_spread hr hspread hN hX hK β
  have hhalf : (1 - (1 / 2 : ℝ) ^ (N + 1)) ^ K ≤ (1 / 2) ^ (D + 1) := by
    have h1 : (1 - (1 / 2 : ℝ) ^ (N + 1)) ^ (2 ^ (N + 1)) ≤ 1 / 2 := by
      have := Real.one_sub_div_pow_le_exp_neg (n := 2 ^ (N + 1)) (t := 1)
        (by exact_mod_cast Nat.one_le_two_pow)
      rw [one_div_pow, one_div] at *
      push_cast at this
      refine this.trans ?_
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) h2
    simp only [K, pow_mul]
    exact pow_le_pow_left₀ (by
      have : (1 / 2 : ℝ) ^ (N + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact pow_nonneg (by linarith) _) h1 _
  calc (#((univ : Finset (Finset U)).filter (AvoidsPatterns X id β)) : ℝ) * 2 ^ (D + 1)
      ≤ 2 ^ Fintype.card U * (1 / 2) ^ (D + 1) * 2 ^ (D + 1) := by
        gcongr
        exact hmain.trans (mul_le_mul_of_nonneg_left hhalf (by positivity))
    _ = 2 ^ Fintype.card U := by rw [mul_assoc, ← mul_pow]; norm_num

end Spread

end Cslib
