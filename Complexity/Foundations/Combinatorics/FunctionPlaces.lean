/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Counting functions by constrained positions

## Main results

* `Finset.card_pi_places_card`: count functions by the positions with a property.
* `Finset.card_places_card`: binomial count without pointwise constraints.

## References

Adapted selectively from
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product that takes the value `a` on `S` and `b` elsewhere. -/
theorem prod_ite_mem_const {M : Type*} [CommMonoid M] (S : Finset ι) (a b : M) :
    (∏ i, if i ∈ S then a else b) = a ^ #S * b ^ (Fintype.card ι - #S) := by
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff, card_compl]

/-- A product with the factors `1` on `S ∩ Q`, `0` on `S \ Q`, `c` on `Q \ S` and `1` elsewhere: it
is `0` unless `S ⊆ Q`. -/
theorem prod_ite_ite_subset {M : Type*} [CommMonoidWithZero M] (Q S : Finset ι) (c : M) :
    (∏ i, if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
      = if S ⊆ Q then c ^ (#Q - #S) else 0 := by
  split_ifs with h
  · have hterm : ∀ i, (if i ∈ S then (if i ∈ Q then 1 else 0) else (if i ∈ Q then c else 1))
        = if i ∈ Q \ S then c else 1 := fun i => by
      by_cases hS : i ∈ S
      · simp [hS, h hS]
      · simp [hS]
    simp_rw [hterm]
    rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset h]
  · obtain ⟨i, hiS, hiQ⟩ := not_subset.mp h
    exact prod_eq_zero (mem_univ i) (by simp [hiS, hiQ])

/-- A product with the factor `0` on `T \ S` and `1` elsewhere: it is `0` unless `T ⊆ S`. -/
theorem prod_ite_ite_superset {M : Type*} [CommMonoidWithZero M] (T S : Finset ι) :
    (∏ i, if i ∈ S then 1 else (if i ∈ T then 0 else 1)) = if T ⊆ S then (1 : M) else 0 := by
  split_ifs with h
  · refine prod_eq_one fun i _ => ?_
    by_cases hS : i ∈ S
    · simp [hS]
    · have hT : i ∉ T := fun hT => hS (h hT)
      simp [hS, hT]
  · obtain ⟨i, hiT, hiS⟩ := not_subset.mp h
    exact prod_eq_zero (mem_univ i) (by simp [hiS, hiT])

/-- The number of sets of `k` elements inside `Q`, each counted `c` times. -/
theorem sum_powersetCard_ite_subset (Q : Finset ι) (k c : ℕ) :
    (∑ S ∈ powersetCard k (univ : Finset ι), if S ⊆ Q then c else 0) = (#Q).choose k * c := by
  rw [← sum_filter, sum_const, smul_eq_mul, ← card_powersetCard]
  congr 2
  ext S
  simp [mem_powersetCard, and_comm]

/-- The number of sets of `k` elements that contain `T`: choose the complement outside `T`. -/
theorem card_powersetCard_superset (T : Finset ι) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    #{S ∈ powersetCard k (univ : Finset ι) | T ⊆ S} =
      (Fintype.card ι - #T).choose (Fintype.card ι - k) := by
  rw [← card_compl, ← card_powersetCard]
  refine card_bij' (fun S _ => Sᶜ) (fun S _ => Sᶜ) ?_ ?_ (fun _ _ => compl_compl _)
    (fun _ _ => compl_compl _)
  · intro S hS
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hS
    simp [mem_powersetCard, hS.1, hS.2, card_compl]
  · intro S hS
    simp only [mem_powersetCard] at hS
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, card_compl, hS.2]
    exact ⟨by omega, by rw [← compl_subset_compl, compl_compl]; exact hS.1⟩

/-! ## Functions by the set of places with a property -/

variable {α : Type*} [Fintype α]

/-- Count the functions satisfying `f i ∈ A i` and having property `p` exactly on `S` by
multiplying the permitted choices at each position. -/
theorem card_pi_places_eq [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (S : Finset ι) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ ({i | p (f i)} : Finset ι) = S} =
      ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  have hmem (i : ι) (x : α) : (x ∈ if i ∈ S then {a ∈ A i | p a} else {a ∈ A i | ¬ p a}) ↔
      x ∈ A i ∧ (p x ↔ i ∈ S) := by
    split_ifs with hi <;> simp [hi]
  simp_rw [← apply_ite Finset.card, ← Fintype.card_piFinset]
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hmem, forall_and,
    Finset.ext_iff]

/-- Partition the functions satisfying `f i ∈ A i` and having property `p` at exactly `k`
positions by their size-`k` set of such positions, and sum the corresponding products of
choice counts. -/
theorem card_pi_places_card [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (k : ℕ) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ #{i | p (f i)} = k} =
      ∑ S ∈ powersetCard k (univ : Finset ι),
        ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  rw [card_eq_sum_card_fiberwise (f := fun f : ι → α => ({i | p (f i)} : Finset ι))
    (t := powersetCard k (univ : Finset ι))
    fun f hf => mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hf).2.2⟩)]
  refine sum_congr rfl fun S hS => ?_
  rw [← card_pi_places_eq, filter_filter]
  exact congrArg card (filter_congr fun f _ =>
    ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ (mem_powersetCard.1 hS).2⟩, h.2⟩⟩)

/-- The number of functions `ι → α` that have `p` at exactly `k` places. -/
theorem card_places_card (p : α → Prop) [DecidablePred p] (k : ℕ) :
    #{f : ι → α | #{i | p (f i)} = k} =
      (Fintype.card ι).choose k * (#{a | p a} ^ k * #{a | ¬ p a} ^ (Fintype.card ι - k)) := by
  classical
  have h := card_pi_places_card (ι := ι) (fun _ => (univ : Finset α)) p k
  simp only [mem_univ, implies_true, true_and] at h
  rw [h, sum_congr rfl fun S hS => by
    rw [prod_ite_mem_const, (mem_powersetCard.1 hS).2], sum_const, card_powersetCard, card_univ,
    smul_eq_mul]

end Finset
