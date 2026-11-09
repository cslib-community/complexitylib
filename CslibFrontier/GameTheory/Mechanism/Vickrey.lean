/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.CriticalBid
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# The Vickrey (second-price) auction

A single item is sold to the highest bidder, ties being broken in favour of the smallest index;
the winner pays the highest bid among the other bidders (`0` if there are none) and losers pay
nothing ([Vickrey1961]; [Roughgarden2013CS364A], Lecture 2). We prove Roughgarden's Theorem 5.1
(Lecture 2), items (1) and (2): the auction is DSIC and individually rational (Claims 4.1 and 4.2),
and on nonnegative bids it maximizes the reported welfare `∑ᵢ bᵢ xᵢ` over 0-1 allocations with at
most one winner. Item (3), linear running time, is not formalized here.

The proof goes through the critical-bid mechanism: the Vickrey allocation is a threshold rule
whose critical bid is the highest other bid. Consequently the Vickrey payment is Myerson's payment
(Lecture 3, §6: "Myerson's Lemma regenerates the Vickrey auction as a special case").

## Main definitions

* `SingleParameter.Vickrey.Wins`: `i` has a highest bid and every smaller index bids strictly
  less.
* `SingleParameter.Vickrey.highestOtherBid`: `max(0, maxⱼ≠ᵢ bⱼ)`.
* `SingleParameter.Vickrey.mechanism`: the Vickrey auction.
* `SingleParameter.Vickrey.singleItemFeasible`: 0-1 allocations with at most one winner.

## Main results

* `SingleParameter.Vickrey.mechanism_isDSIC`, `SingleParameter.Vickrey.mechanism_isIR`:
  [Roughgarden2013CS364A], Lecture 2, Claims 4.1 and 4.2.
* `SingleParameter.Vickrey.isWelfareMaximizing_allocation`: Lecture 2, Theorem 5.1 (2).
* `SingleParameter.Vickrey.mechanism_payment_eq_myersonPayment`: the second-price payment is
  Myerson's payment for the highest-bidder allocation rule.
* `SingleParameter.Vickrey.mechanism_isNormalized`: a zero bid pays zero.
* `SingleParameter.Vickrey.exists_wins`, `SingleParameter.Vickrey.Wins.unique`: with at least one
  bidder there is exactly one winner.
* `SingleParameter.Vickrey.wins_comp_iff`, `SingleParameter.Vickrey.allocation_comp`: the winner
  does not change when all bids are transformed by the same strictly increasing map.

## References

* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
-/

public section

namespace Cslib.GameTheory.SingleParameter.Vickrey

variable {ι : Type*} [LinearOrder ι]

/-- Bidder `i` wins the Vickrey auction on bids `b`: no bid exceeds `bᵢ`, and bidders with a
smaller index bid strictly less (ties go to the smallest index). -/
@[expose] def Wins (b : ι → ℝ) (i : ι) : Prop := ∀ j, j ≠ i → b j ≤ b i ∧ (j < i → b j < b i)

open Classical in
/-- The Vickrey allocation rule: the winner gets the item. -/
@[expose] noncomputable def allocation (b : ι → ℝ) (i : ι) : ℝ := if Wins b i then 1 else 0

/-- Feasible allocations of a single item: 0-1 vectors with at most one winner. -/
@[expose] def singleItemFeasible [Fintype ι] : Set (ι → ℝ) :=
  {y | (∀ i, y i = 0 ∨ y i = 1) ∧ ∑ i, y i ≤ 1}

/-- The winner is unique. -/
theorem Wins.unique {b : ι → ℝ} {i j : ι} (hi : Wins b i) (hj : Wins b j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := (hj i hne).2 h
    have h2 := (hi j (Ne.symm hne)).1
    linarith
  · have h1 := (hi j (Ne.symm hne)).2 h
    have h2 := (hj i hne).1
    linarith

theorem allocation_eq_one_iff {b : ι → ℝ} {i : ι} : allocation b i = 1 ↔ Wins b i := by
  unfold allocation
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

theorem allocation_binary (b : ι → ℝ) (i : ι) : allocation b i = 0 ∨ allocation b i = 1 := by
  unfold allocation
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem isBinary_allocation : IsBinary (allocation (ι := ι)) :=
  fun b _ i => allocation_binary b i

theorem allocation_eq_zero_iff {b : ι → ℝ} {i : ι} : allocation b i = 0 ↔ ¬ Wins b i := by
  unfold allocation
  split_ifs with h
  · exact iff_of_false one_ne_zero (not_not_intro h)
  · exact iff_of_true rfl h

/-- Raising the winner's bid keeps it the winner. -/
theorem Wins.update_of_le {b : ι → ℝ} {i : ι} {z z' : ℝ} (h : Wins (Function.update b i z) i)
    (hzz' : z ≤ z') : Wins (Function.update b i z') i := by
  intro j hj
  have := h j hj
  rw [Function.update_self, Function.update_of_ne hj] at this ⊢
  exact ⟨this.1.trans hzz', fun hlt => (this.2 hlt).trans_le hzz'⟩

/-- Winning is invariant under a strictly increasing transformation of all bids. -/
theorem wins_comp_iff {φ : ℝ → ℝ} (hφ : StrictMono φ) {b : ι → ℝ} {i : ι} :
    Wins (fun j => φ (b j)) i ↔ Wins b i := by
  refine forall_congr' fun j => imp_congr_right fun _ => ?_
  rw [hφ.le_iff_le, hφ.lt_iff_lt]

/-- The highest-bidder allocation is invariant under a strictly increasing transformation of all
bids. -/
theorem allocation_comp {φ : ℝ → ℝ} (hφ : StrictMono φ) (b : ι → ℝ) (i : ι) :
    allocation (fun j => φ (b j)) i = allocation b i := by
  by_cases h : Wins b i
  · rw [allocation_eq_one_iff.2 h, allocation_eq_one_iff.2 ((wins_comp_iff hφ).2 h)]
  · rw [allocation_eq_zero_iff.2 h, allocation_eq_zero_iff.2 (mt (wins_comp_iff hφ).1 h)]

/-- With a single bidder, that bidder always wins. -/
theorem wins_of_subsingleton [Subsingleton ι] (b : ι → ℝ) (i : ι) : Wins b i :=
  fun j hj => absurd (Subsingleton.elim j i) hj

/-- The highest-bidder allocation rule is monotone. -/
theorem isMonotone_allocation : IsMonotone (allocation (ι := ι)) := by
  intro i b _ z _ z' _ hzz'
  change allocation (Function.update b i z) i ≤ allocation (Function.update b i z') i
  by_cases h : Wins (Function.update b i z) i
  · rw [allocation_eq_one_iff.2 h, allocation_eq_one_iff.2 (h.update_of_le hzz')]
  · rw [allocation_eq_zero_iff.2 h]
    rcases allocation_binary (Function.update b i z') i with h0 | h1
    · rw [h0]
    · rw [h1]
      exact zero_le_one

private theorem allocation_eq_zero_of_wins {b : ι → ℝ} {i j : ι} (hi : Wins b i) (hj : j ≠ i) :
    allocation b j = 0 := by
  rcases allocation_binary b j with h0 | h1
  · exact h0
  · exact absurd ((allocation_eq_one_iff.1 h1).unique hi) hj

/-- With at least one bidder, some bidder wins: the smallest index among the highest bidders. -/
theorem exists_wins [Finite ι] [Nonempty ι] (b : ι → ℝ) : ∃ i, Wins b i := by
  have := Fintype.ofFinite ι
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
  set S := Finset.univ.filter fun j => b j = b i0 with hSdef
  have hS : S.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hmem := Finset.min'_mem S hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨S.min' hS, fun j _ => ⟨?_, fun hlt => ?_⟩⟩
  · rw [hmem]
    exact hi0 j (Finset.mem_univ j)
  · rw [hmem]
    refine (hi0 j (Finset.mem_univ j)).lt_of_ne fun h => ?_
    have : S.min' hS ≤ j := Finset.min'_le S j (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    exact absurd hlt (not_lt.2 this)

variable [Fintype ι]

/-- The highest bid among the bidders other than `i`, or `0` if it is negative or there are no
other bidders. -/
noncomputable def highestOtherBid (b : ι → ℝ) (i : ι) : ℝ :=
  (Finset.univ.erase i).fold max 0 b

/-- The Vickrey auction: the winner pays the highest other bid. -/
@[expose] noncomputable def mechanism : Mechanism ι where
  allocation := allocation
  payment b i := highestOtherBid b i * allocation b i

theorem le_highestOtherBid {b : ι → ℝ} {i j : ι} (hj : j ≠ i) : b j ≤ highestOtherBid b i :=
  (Finset.le_fold_max _).2 (Or.inr ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩, le_rfl⟩)

theorem highestOtherBid_nonneg (b : ι → ℝ) (i : ι) : 0 ≤ highestOtherBid b i :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem highestOtherBid_le_iff {b : ι → ℝ} {i : ι} {c : ℝ} :
    highestOtherBid b i ≤ c ↔ 0 ≤ c ∧ ∀ j, j ≠ i → b j ≤ c := by
  simp only [highestOtherBid, Finset.fold_max_le, Finset.mem_erase, Finset.mem_univ, and_true]

/-- The highest other bid does not depend on `i`'s own bid. -/
@[simp]
theorem highestOtherBid_update (b : ι → ℝ) (i : ι) (z : ℝ) :
    highestOtherBid (Function.update b i z) i = highestOtherBid b i :=
  Finset.fold_congr fun _ hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _

/-- Bidding above the highest other bid wins. -/
theorem wins_update_of_lt {b : ι → ℝ} {i : ι} {z : ℝ} (h : highestOtherBid b i < z) :
    Wins (Function.update b i z) i := by
  intro j hj
  rw [Function.update_self, Function.update_of_ne hj]
  have := le_highestOtherBid (b := b) hj
  exact ⟨by linarith, fun _ => by linarith⟩

/-- A winning nonnegative bid is at least the highest other bid. -/
theorem highestOtherBid_le_of_wins {b : ι → ℝ} {i : ι} {z : ℝ} (hz : 0 ≤ z)
    (h : Wins (Function.update b i z) i) : highestOtherBid b i ≤ z := by
  refine highestOtherBid_le_iff.2 ⟨hz, fun j hj => ?_⟩
  have := (h j hj).1
  rwa [Function.update_self, Function.update_of_ne hj] at this

theorem threshold_allocation (b : ι → ℝ) (i : ι) :
    (∀ z, highestOtherBid b i < z → allocation (Function.update b i z) i = 1) ∧
      ∀ z, 0 ≤ z → allocation (Function.update b i z) i = 1 → highestOtherBid b i ≤ z :=
  ⟨fun _ hz => allocation_eq_one_iff.2 (wins_update_of_lt hz),
    fun _ hz h => highestOtherBid_le_of_wins hz (allocation_eq_one_iff.1 h)⟩

/-- The critical bid in the Vickrey auction is the highest other bid. -/
theorem criticalBid_allocation (b : ι → ℝ) (i : ι) :
    criticalBid allocation b i = highestOtherBid b i :=
  criticalBid_eq_of_threshold (highestOtherBid_nonneg b i) (threshold_allocation b i).1
    (threshold_allocation b i).2

/-- The Vickrey auction is the critical-bid mechanism of the highest-bidder rule. -/
theorem criticalBidMechanism_allocation :
    criticalBidMechanism (allocation (ι := ι)) = mechanism := by
  simp only [criticalBidMechanism, mechanism, criticalBid_allocation]

/-- **Vickrey's auction is DSIC** ([Roughgarden2013CS364A], Lecture 2, Claim 4.1). -/
theorem mechanism_isDSIC : (mechanism (ι := ι)).IsDSIC := by
  rw [← criticalBidMechanism_allocation]
  exact criticalBidMechanism_isDSIC isMonotone_allocation isBinary_allocation

/-- **Vickrey's auction is individually rational** ([Roughgarden2013CS364A], Lecture 2,
Claim 4.2). -/
theorem mechanism_isIR : (mechanism (ι := ι)).IsIR := by
  rw [← criticalBidMechanism_allocation]
  exact criticalBidMechanism_isIR isBinary_allocation

/-- The second-price payment is Myerson's payment for the highest-bidder allocation rule
([Roughgarden2013CS364A], Lecture 3, §6). -/
theorem mechanism_payment_eq_myersonPayment {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    mechanism.payment b i = myersonPayment allocation b i := by
  rw [← criticalBidMechanism_allocation]
  exact criticalBid_mul_eq_myersonPayment isMonotone_allocation isBinary_allocation hb i

/-- In the Vickrey auction a zero bid pays zero. -/
theorem mechanism_isNormalized : (mechanism (ι := ι)).IsNormalized := by
  intro i b hb
  rw [mechanism_payment_eq_myersonPayment (update_nonneg hb i le_rfl)]
  exact myerson_isNormalized _ i b hb

theorem allocation_mem_singleItemFeasible (b : ι → ℝ) :
    allocation b ∈ singleItemFeasible := by
  refine ⟨allocation_binary b, ?_⟩
  by_cases h : ∃ i, Wins b i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i (fun j _ hj => allocation_eq_zero_of_wins hi hj)
      (fun h => absurd (Finset.mem_univ i) h), allocation_eq_one_iff.2 hi]
  · push Not at h
    have : ∀ j, allocation b j = 0 := fun j => allocation_eq_zero_iff.2 (h j)
    simp only [this, Finset.sum_const_zero, zero_le_one]

/-- **Vickrey's auction maximizes welfare** ([Roughgarden2013CS364A], Lecture 2,
Theorem 5.1 (2)): on nonnegative bids, giving the item to the winner maximizes `∑ᵢ bᵢ xᵢ` over
all 0-1 allocations with at most one winner. -/
theorem isWelfareMaximizing_allocation :
    IsWelfareMaximizing (singleItemFeasible (ι := ι)) allocation := by
  intro b hb
  refine ⟨allocation_mem_singleItemFeasible b, fun y hy => ?_⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, le_refl]
  obtain ⟨i, hi⟩ := exists_wins b
  have hsum : ∑ j, b j * allocation b j = b i := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [allocation_eq_zero_of_wins hi hj, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), allocation_eq_one_iff.2 hi, mul_one]
  rw [hsum]
  have hy0 : ∀ j, 0 ≤ y j := fun j => by
    rcases hy.1 j with h | h <;> rw [h]
    exact zero_le_one
  have hle : ∀ j, b j ≤ b i := fun j => by
    rcases eq_or_ne j i with rfl | hj
    · exact le_rfl
    · exact (hi j hj).1
  calc ∑ j, b j * y j ≤ ∑ j, b i * y j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (hy0 j)
    _ = b i * ∑ j, y j := by rw [Finset.mul_sum]
    _ ≤ b i * 1 := mul_le_mul_of_nonneg_left hy.2 (hb i)
    _ = b i := mul_one _

end Cslib.GameTheory.SingleParameter.Vickrey
