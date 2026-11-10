/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Mechanism.Myerson
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Critical bids

For a monotone *0-1* allocation rule, a bidder's allocation curve `xᵢ(·, b₋ᵢ)` is `0` up to a
breakpoint and `1` after it. Myerson's payment is then the *critical bid*, the lowest bid with
which the bidder would still win ([Roughgarden2013CS364A], Lecture 4, §1.3). We define the critical
bid as an infimum, prove directly that charging winners their critical bid is DSIC, individually
rational and normalized, and deduce from Myerson's uniqueness theorem that it equals Myerson's
integral payment.

## Main definitions

* `SingleParameter.IsBinary`: on nonnegative bid profiles every allocation is `0` or `1`.
* `SingleParameter.criticalBid`: `inf {z ≥ 0 | xᵢ(z, b₋ᵢ) = 1}`.
* `SingleParameter.criticalBidMechanism`: winners pay their critical bid, losers pay nothing.

## Main results

* `SingleParameter.criticalBidMechanism_isDSIC`, `SingleParameter.criticalBidMechanism_isIR`,
  `SingleParameter.criticalBidMechanism_isNormalized`: the critical-bid mechanism of a monotone
  0-1 rule is DSIC, individually rational and normalized.
* `SingleParameter.criticalBid_mul_eq_myersonPayment`: the critical-bid payment is Myerson's
  payment ([Roughgarden2013CS364A], Lecture 4, (2) and §1.3).
* `SingleParameter.criticalBid_eq_of_threshold`, `SingleParameter.isMonotone_of_threshold`: a
  0-1 rule that awards bidder `i` above a threshold `t ≥ 0` and only at bids `≥ t` is monotone with
  critical bid `t`.
* `SingleParameter.Mechanism.IsDSIC.congr`, `SingleParameter.Mechanism.IsIR.congr`: the properties
  only depend on the rules on nonnegative bid profiles.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
-/

public section

namespace Cslib.GameTheory.SingleParameter

variable {ι : Type*}

/-- A *0-1* allocation rule: on nonnegative bid profiles every bidder either wins (`1`) or loses
(`0`). -/
@[expose] def IsBinary (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ b, 0 ≤ b → ∀ i, x b i = 0 ∨ x b i = 1

/-- DSIC depends only on the rules on nonnegative bid profiles. -/
theorem Mechanism.IsDSIC.congr [DecidableEq ι] {M N : Mechanism ι} (hM : M.IsDSIC)
    (h : ∀ b, 0 ≤ b → M.allocation b = N.allocation b ∧ M.payment b = N.payment b) :
    N.IsDSIC := by
  intro i b v hb hv
  have := hM i b v hb hv
  simp only [Mechanism.utility] at this ⊢
  rwa [(h b hb).1, (h b hb).2, (h _ (update_nonneg hb i hv)).1,
    (h _ (update_nonneg hb i hv)).2] at this

/-- Individual rationality depends only on the rules on nonnegative bid profiles. -/
theorem Mechanism.IsIR.congr {M N : Mechanism ι} (hM : M.IsIR)
    (h : ∀ b, 0 ≤ b → M.allocation b = N.allocation b ∧ M.payment b = N.payment b) :
    N.IsIR := by
  intro i b hb
  have := hM i b hb
  simp only [Mechanism.utility] at this ⊢
  rwa [(h b hb).1, (h b hb).2] at this

variable [DecidableEq ι]

/-- The *critical bid* of bidder `i` against the bids `b₋ᵢ` of the others: the infimum of the
nonnegative bids with which `i` wins. It is `0` if `i` never wins; then `i` is never charged it. -/
@[expose] noncomputable def criticalBid (x : (ι → ℝ) → ι → ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  sInf {z : ℝ | 0 ≤ z ∧ x (Function.update b i z) i = 1}

/-- The critical-bid mechanism: a bidder pays its critical bid if it wins and nothing otherwise
([Roughgarden2013CS364A], Lecture 4, §1.3). -/
@[expose] noncomputable def criticalBidMechanism (x : (ι → ℝ) → ι → ℝ) : Mechanism ι :=
  ⟨x, fun b i => criticalBid x b i * x b i⟩

/-- The critical bid of `i` does not depend on `i`'s own bid. -/
@[simp]
theorem criticalBid_update (x : (ι → ℝ) → ι → ℝ) (b : ι → ℝ) (i : ι) (z : ℝ) :
    criticalBid x (Function.update b i z) i = criticalBid x b i := by
  simp only [criticalBid, Function.update_idem]

theorem criticalBid_nonneg (x : (ι → ℝ) → ι → ℝ) (b : ι → ℝ) (i : ι) :
    0 ≤ criticalBid x b i :=
  Real.sInf_nonneg fun _ hz => hz.1

/-- A winning nonnegative bid is at least the critical bid. -/
theorem criticalBid_le {x : (ι → ℝ) → ι → ℝ} {b : ι → ℝ} {i : ι} {z : ℝ} (hz : 0 ≤ z)
    (h : x (Function.update b i z) i = 1) : criticalBid x b i ≤ z := by
  unfold criticalBid
  exact csInf_le ⟨0, fun _ hw => hw.1⟩ ⟨hz, h⟩

/-- For a monotone 0-1 rule under which `i` can win at all, every bid above the critical bid
wins. -/
theorem eq_one_of_criticalBid_lt {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x) (hbin : IsBinary x)
    {b : ι → ℝ} (hb : 0 ≤ b) {i : ι} {w z : ℝ} (hw : 0 ≤ w)
    (hwin : x (Function.update b i w) i = 1) (hz : 0 ≤ z) (hlt : criticalBid x b i < z) :
    x (Function.update b i z) i = 1 := by
  have hne : {z : ℝ | 0 ≤ z ∧ x (Function.update b i z) i = 1}.Nonempty := ⟨w, hw, hwin⟩
  obtain ⟨w, ⟨hw0, hw1⟩, hwz⟩ := exists_lt_of_csInf_lt hne hlt
  have hmono : x (Function.update b i w) i ≤ x (Function.update b i z) i :=
    hx i b hb hw0 hz hwz.le
  rcases hbin _ (update_nonneg hb i hz) i with h0 | h1
  · rw [hw1, h0] at hmono
    norm_num at hmono
  · exact h1

/-- The critical-bid mechanism of a monotone 0-1 allocation rule is DSIC. A bidder who wins by
bidding truthfully pays at most its value; a bidder who loses has value at most its critical bid,
so winning by overbidding would cost at least its value. -/
theorem criticalBidMechanism_isDSIC {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x)
    (hbin : IsBinary x) : (criticalBidMechanism x).IsDSIC := by
  intro i b v hb hv
  simp only [Mechanism.utility, criticalBidMechanism, criticalBid_update]
  have hbu : Function.update b i (b i) = b := Function.update_eq_self i b
  rcases hbin b hb i with ha | ha <;> rcases hbin _ (update_nonneg hb i hv) i with ha' | ha'
  · rw [ha, ha']
  · rw [ha, ha']
    have := criticalBid_le hv ha'
    linarith
  · rw [ha, ha']
    by_contra hcon
    have hlt : criticalBid x b i < v := by linarith
    have := eq_one_of_criticalBid_lt hx hbin hb (hb i) (by rw [hbu]; exact ha) hv hlt
    rw [ha'] at this
    norm_num at this
  · rw [ha, ha']

/-- The critical-bid mechanism of a 0-1 allocation rule is individually rational. -/
theorem criticalBidMechanism_isIR {x : (ι → ℝ) → ι → ℝ} (hbin : IsBinary x) :
    (criticalBidMechanism x).IsIR := by
  intro i b hb
  simp only [Mechanism.utility, criticalBidMechanism]
  rcases hbin b hb i with ha | ha
  · rw [ha, mul_zero, mul_zero, sub_zero]
  · have := criticalBid_le (x := x) (hb i) (by rw [Function.update_eq_self]; exact ha)
    rw [ha]
    linarith

/-- In the critical-bid mechanism a zero bid pays zero. -/
theorem criticalBidMechanism_isNormalized {x : (ι → ℝ) → ι → ℝ} (hbin : IsBinary x) :
    (criticalBidMechanism x).IsNormalized := by
  intro i b hb
  simp only [criticalBidMechanism, criticalBid_update]
  rcases hbin _ (update_nonneg hb i le_rfl) i with ha | ha
  · rw [ha, mul_zero]
  · have h1 := criticalBid_le le_rfl ha
    have h2 := criticalBid_nonneg x b i
    rw [ha, mul_one]
    linarith

/-- For a monotone 0-1 allocation rule, Myerson's payment is the critical bid of a winner and `0`
for a loser ([Roughgarden2013CS364A], Lecture 4, §1.3), by uniqueness in Myerson's Lemma. -/
theorem criticalBid_mul_eq_myersonPayment {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x)
    (hbin : IsBinary x) {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    criticalBid x b i * x b i = myersonPayment x b i :=
  (criticalBidMechanism_isDSIC hx hbin).payment_eq_myersonPayment
    (criticalBidMechanism_isNormalized hbin) i hb

/-- If bidder `i` wins at every bid above `t ≥ 0` and only at bids at least `t`, then `t` is its
critical bid. -/
theorem criticalBid_eq_of_threshold {x : (ι → ℝ) → ι → ℝ} {b : ι → ℝ} {i : ι} {t : ℝ}
    (ht : 0 ≤ t) (hlt : ∀ z, t < z → x (Function.update b i z) i = 1)
    (hle : ∀ z, 0 ≤ z → x (Function.update b i z) i = 1 → t ≤ z) :
    criticalBid x b i = t := by
  apply le_antisymm
  · rw [← csInf_Ioi (a := t)]
    exact csInf_le_csInf ⟨0, fun _ hw => hw.1⟩ Set.nonempty_Ioi
      fun z hz => ⟨ht.trans (le_of_lt hz), hlt z hz⟩
  · exact le_csInf ⟨t + 1, by linarith, hlt _ (by linarith)⟩ fun z hz => hle z hz.1 hz.2

/-- A 0-1 rule given by thresholds is monotone. -/
theorem isMonotone_of_threshold {x : (ι → ℝ) → ι → ℝ} (hbin : IsBinary x)
    (h : ∀ i b, 0 ≤ b → ∃ t, (∀ z, t < z → x (Function.update b i z) i = 1) ∧
      ∀ z, 0 ≤ z → x (Function.update b i z) i = 1 → t ≤ z) : IsMonotone x := by
  intro i b hb z hz z' hz' hzz'
  obtain ⟨t, hlt, hle⟩ := h i b hb
  change x (Function.update b i z) i ≤ x (Function.update b i z') i
  rcases hbin _ (update_nonneg hb i hz) i with h0 | h1
  · rw [h0]
    rcases hbin _ (update_nonneg hb i hz') i with h0' | h1'
    · rw [h0']
    · rw [h1']
      exact zero_le_one
  · rcases hzz'.lt_or_eq with hlt' | rfl
    · rw [h1, hlt z' (lt_of_le_of_lt (hle z hz h1) hlt')]
    · exact le_rfl

end Cslib.GameTheory.SingleParameter
