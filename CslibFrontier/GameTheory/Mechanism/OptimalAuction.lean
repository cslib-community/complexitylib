/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Revenue
public import CslibFrontier.GameTheory.Mechanism.Vickrey
import Mathlib.Tactic.Linarith

/-!
# Myerson's optimal auction

Bidders' valuations are independent, drawn from regular distributions with densities. Myerson's
optimal auction maximizes virtual welfare pointwise and charges Myerson's payments. Among all DSIC,
individually rational mechanisms with feasible allocations, it has the largest expected revenue
([Roughgarden2013CS364A], Lecture 5, §3; [Myerson1981]).

The argument has three steps.

1. Expected revenue is at most expected virtual welfare
   (`Mechanism.IsDSIC.integral_sum_payment_le`). This holds with equality for normalized
   mechanisms, in particular for Myerson's payments.
2. A pointwise virtual-welfare maximizer has the largest expected virtual welfare among feasible
   allocation rules.
3. If every distribution is regular, a virtual-welfare maximizer is monotone, whatever the
   tie-breaking (`IsVirtualWelfareMaximizing.isMonotone`). This is the exchange argument for
   welfare maximization, with `φᵢ` in place of the identity. By Myerson's Lemma the maximizer with
   Myerson's payments is then DSIC.

For a single item and i.i.d. regular bidders, the virtual-welfare maximizer awards the item to the
highest bidder if that bidder's virtual valuation is nonnegative
(`Vickrey.isVirtualWelfareMaximizing_reserveAllocation`). The reserve price
`r = inf {v ≥ 0 | φ(v) ≥ 0}` is `φ⁻¹(0)` when `φ` is continuous with a zero. The Myerson payment is
`max(r, highest other bid)`, so this is the Vickrey auction with reserve price `r`
(`Vickrey.myersonPayment_reserveAllocation`, Lecture 5, §3.1). For the uniform distribution on
`[0, 1]` the reserve price is `1/2`.

The optimality theorem takes the measurability of the virtual-welfare maximizer as a hypothesis.
For the single-item rule it is proved (`Vickrey.measurable_reserveAllocation`). Optimality is among
DSIC mechanisms. The stronger optimality among Bayesian incentive-compatible mechanisms (Lecture 5,
§3.2) and ironing for irregular distributions are not covered.

## Main definitions

* `SingleParameter.IsVirtualWelfareMaximizing`: an allocation rule that maximizes
  `∑ᵢ φᵢ(bᵢ) yᵢ` over a feasible set at every nonnegative bid profile.
* `SingleParameter.IsReserveThreshold`, `SingleParameter.reservePrice`: the reserve price of a
  virtual valuation.
* `SingleParameter.Vickrey.reserveAllocation`: highest bidder wins if its virtual valuation is
  nonnegative.

## Main results

* `SingleParameter.IsVirtualWelfareMaximizing.isMonotone`: under regularity, virtual-welfare
  maximization is monotone.
* `SingleParameter.myerson_isDSIC_of_isVirtualWelfareMaximizing`: Myerson's optimal auction is
  DSIC.
* `SingleParameter.integral_sum_payment_le_myerson`: **Myerson's optimal auction theorem**.
* `SingleParameter.Vickrey.integral_sum_payment_le_reserve`: for a single item and i.i.d. regular
  bidders, the Vickrey auction with virtual-value reserve is optimal.
* `SingleParameter.Vickrey.myersonPayment_reserveAllocation`: its payments are
  `max(r, highest other bid)`.
* `SingleParameter.Vickrey.integral_sum_payment_le_secondPriceReserve`: the same optimality stated
  directly for the second-price auction with reserve price `r`.
* `SingleParameter.IsRegular.isReserveThreshold`: a regular distribution has a reserve price.
* `SingleParameter.reservePrice_uniform`: the reserve price for the uniform distribution on
  `[0, 1]` is `1/2`.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

variable {ι : Type*}

/-! ### Virtual-welfare maximization -/

/-- `x` maximizes **virtual welfare** `∑ᵢ φᵢ(bᵢ) yᵢ` over the feasible allocations `X` at every
nonnegative bid profile ([Roughgarden2013CS364A], Lecture 5, §3.1). Ties may be broken
arbitrarily. -/
@[expose] def IsVirtualWelfareMaximizing [Fintype ι] (φ : ι → ℝ → ℝ) (X : Set (ι → ℝ))
    (x : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ b, 0 ≤ b → x b ∈ X ∧ ∀ y ∈ X, ∑ i, φ i (b i) * y i ≤ ∑ i, φ i (b i) * x b i

private theorem sum_update_weight [Fintype ι] [DecidableEq ι] (φ : ι → ℝ → ℝ) (b y : ι → ℝ)
    (i : ι) (z : ℝ) :
    ∑ j, φ j (Function.update b i z j) * y j =
      φ i z * y i + ∑ j ∈ Finset.univ.erase i, φ j (b j) * y j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Virtual-welfare maximization is monotone** when every `φᵢ` is strictly increasing on
`[0, ∞)`, whatever the tie-breaking ([Roughgarden2013CS364A], Lecture 5, §3.1). Comparing the
optimality of `x(z, b₋ᵢ)` and of `x(z', b₋ᵢ)` against each other gives
`(φᵢ(z') − φᵢ(z))(xᵢ(z', b₋ᵢ) − xᵢ(z, b₋ᵢ)) ≥ 0`. -/
theorem IsVirtualWelfareMaximizing.isMonotone [Fintype ι] [DecidableEq ι] {φ : ι → ℝ → ℝ}
    {X : Set (ι → ℝ)} {x : (ι → ℝ) → ι → ℝ} (hx : IsVirtualWelfareMaximizing φ X x)
    (hφ : ∀ i, StrictMonoOn (φ i) (Ici 0)) : IsMonotone x := by
  intro i b hb z hz z' hz' hzz'
  change x (Function.update b i z) i ≤ x (Function.update b i z') i
  rcases hzz'.lt_or_eq with hlt | rfl
  · have h1 := (hx _ (update_nonneg hb i hz)).2 _ (hx _ (update_nonneg hb i hz')).1
    have h2 := (hx _ (update_nonneg hb i hz')).2 _ (hx _ (update_nonneg hb i hz)).1
    simp only [sum_update_weight φ b _ i] at h1 h2
    have hφlt := hφ i hz hz' hlt
    by_contra hcon
    have := lt_of_not_ge hcon
    nlinarith
  · exact le_rfl

/-- **Myerson's optimal auction is DSIC**: under regularity, a virtual-welfare maximizer is
monotone, so Myerson's payments make it DSIC. -/
theorem myerson_isDSIC_of_isVirtualWelfareMaximizing [Fintype ι] [DecidableEq ι]
    {φ : ι → ℝ → ℝ} {X : Set (ι → ℝ)} {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing φ X x) (hφ : ∀ i, StrictMonoOn (φ i) (Ici 0)) :
    (myerson x).IsDSIC :=
  myerson_isDSIC (hx.isMonotone hφ)

/-- Myerson's optimal auction is individually rational when feasible allocations are
nonnegative. -/
theorem myerson_isIR_of_isVirtualWelfareMaximizing [Fintype ι] [DecidableEq ι]
    {φ : ι → ℝ → ℝ} {X : Set (ι → ℝ)} {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing φ X x) (hX : ∀ y ∈ X, 0 ≤ y) : (myerson x).IsIR :=
  myerson_isIR fun b hb => hX _ (hx b hb).1

/-! ### Optimality -/

section Optimality

variable [Fintype ι] [DecidableEq ι] {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
  {f : ι → ℝ → NNReal} {h : ι → ℝ}

/-- **Myerson's optimal auction theorem** ([Roughgarden2013CS364A], Lecture 5, §3.1;
[Myerson1981]).

Setting: valuations are independent; bidder `i`'s valuation has density `f i` on `[0, h i]`. The
feasible allocations `X` lie in `[0, 1]^ι`, and `x` is a measurable rule that maximizes virtual
welfare over `X` at every nonnegative profile.

Conclusion: every DSIC, individually rational mechanism `M` whose allocations are measurable and
feasible on nonnegative profiles has expected revenue at most that of Myerson's mechanism
`myerson x`. Under regularity `myerson x` is itself DSIC
(`myerson_isDSIC_of_isVirtualWelfareMaximizing`) and individually rational
(`myerson_isIR_of_isVirtualWelfareMaximizing`). The inequality itself does not use regularity. -/
theorem integral_sum_payment_le_myerson (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    {X : Set (ι → ℝ)} (hX : ∀ y ∈ X, ∀ i, 0 ≤ y i ∧ y i ≤ 1) {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing (fun i => virtualValue (μ i) (f i)) X x)
    (hxm : ∀ i, Measurable fun v => x v i) {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ X) (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤ ∫ v, ∑ i, (myerson x).payment v i ∂Measure.pi μ := by
  have hbound : ∀ y ∈ X, ∀ i, |y i| ≤ 1 := fun y hy i => by
    rw [abs_of_nonneg (hX y hy i).1]
    exact (hX y hy i).2
  have hMB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 := fun v hv => hbound _ (hMX v hv)
  have hxB : ∀ v, 0 ≤ v → ∀ i, |x v i| ≤ 1 := fun v hv => hbound _ (hx v hv).1
  refine (hM.integral_sum_payment_le hIR hμ hMm hMB).trans ?_
  change _ ≤ ∫ v, ∑ i, myersonPayment x v i ∂Measure.pi μ
  rw [integral_sum_myersonPayment_eq hμ hxm hxB]
  refine integral_mono_ae
    (integrable_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hMm i) fun v hv =>
      hMB v hv i)
    (integrable_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hxm i) fun v hv =>
      hxB v hv i) ?_
  filter_upwards [ae_nonneg hμ] with v hv
  exact (hx v hv).2 _ (hMX v hv)

end Optimality

/-! ### Reserve prices -/

/-- `r ≥ 0` is a **reserve threshold** for `φ` if every bid above `r` has nonnegative virtual
valuation and every nonnegative bid with nonnegative virtual valuation is at least `r`. For a
continuous, strictly increasing `φ` with a zero, `r = φ⁻¹(0)` ([Roughgarden2013CS364A], Lecture 5,
§3.1). The definition also covers a discontinuous `φ` that jumps over `0`. -/
@[expose] def IsReserveThreshold (φ : ℝ → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ (∀ v, r < v → 0 ≤ φ v) ∧ ∀ v, 0 ≤ v → 0 ≤ φ v → r ≤ v

/-- A reserve threshold is unique. -/
theorem IsReserveThreshold.unique {φ : ℝ → ℝ} {r r' : ℝ} (hr : IsReserveThreshold φ r)
    (hr' : IsReserveThreshold φ r') : r = r' := by
  have key : ∀ {s s' : ℝ}, IsReserveThreshold φ s → IsReserveThreshold φ s' → s ≤ s' := by
    intro s s' hs hs'
    by_contra hcon
    have hlt : s' < s := lt_of_not_ge hcon
    have h1 : s' < (s' + s) / 2 := by linarith
    have h2 : (s' + s) / 2 < s := by linarith
    have := hs.2.2 _ (hs'.1.trans h1.le) (hs'.2.1 _ h1)
    linarith
  exact le_antisymm (key hr hr') (key hr' hr)

/-- The **reserve price** for `φ`: the infimum of the nonnegative bids with nonnegative virtual
valuation. -/
noncomputable def reservePrice (φ : ℝ → ℝ) : ℝ :=
  sInf {v | 0 ≤ v ∧ 0 ≤ φ v}

/-- If `φ` is nondecreasing on `[0, ∞)` and nonnegative somewhere there, `reservePrice φ` is its
reserve threshold. No continuity is needed. -/
theorem isReserveThreshold_reservePrice {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Ici 0))
    (hne : ∃ v, 0 ≤ v ∧ 0 ≤ φ v) : IsReserveThreshold φ (reservePrice φ) := by
  have hbdd : BddBelow {v : ℝ | 0 ≤ v ∧ 0 ≤ φ v} := ⟨0, fun _ hv => hv.1⟩
  refine ⟨le_csInf hne fun _ hv => hv.1, fun v hv => ?_, fun v hv0 hv => csInf_le hbdd ⟨hv0, hv⟩⟩
  obtain ⟨w, hw, hwv⟩ := exists_lt_of_csInf_lt (s := {v : ℝ | 0 ≤ v ∧ 0 ≤ φ v}) hne hv
  exact hw.2.trans (hφ hw.1 (hw.1.trans hwv.le) hwv.le)

/-- With a density on `[0, h]`, the virtual valuation is nonnegative somewhere on `[0, ∞)`: it is
the identity above `h`. -/
theorem HasValueDensity.exists_virtualValue_nonneg {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}
    (hμ : HasValueDensity μ f h) : ∃ v, 0 ≤ v ∧ 0 ≤ virtualValue μ f v :=
  ⟨max h 0, le_max_right _ _, by
    rw [hμ.virtualValue_eq_self (le_max_left _ _)]
    exact le_max_right _ _⟩

/-- A regular distribution with a density has a reserve threshold, its reserve price. -/
theorem IsRegular.isReserveThreshold {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}
    (hreg : IsRegular μ f h) (hμ : HasValueDensity μ f h) :
    IsReserveThreshold (virtualValue μ f) (reservePrice (virtualValue μ f)) :=
  isReserveThreshold_reservePrice (hreg.strictMonoOn_Ici hμ).monotoneOn
    hμ.exists_virtualValue_nonneg

/-- For the uniform distribution on `[0, 1]`, the reserve threshold is `1/2`
([Roughgarden2013CS364A], Lecture 5, §3.1). -/
theorem isReserveThreshold_uniform :
    IsReserveThreshold (virtualValue (volume.restrict (Icc 0 1)) (fun _ => 1)) (1 / 2) := by
  have hφ : ∀ v : ℝ, 0 ≤ v →
      (0 ≤ virtualValue (volume.restrict (Icc 0 1)) (fun _ => 1) v ↔ 1 / 2 ≤ v) := by
    intro v hv
    rcases le_total v 1 with hv1 | hv1
    · rw [virtualValue_uniform ⟨hv, hv1⟩]
      constructor <;> intro _ <;> linarith
    · rw [hasValueDensity_uniform.virtualValue_eq_self hv1]
      constructor <;> intro _ <;> linarith
  exact ⟨by norm_num, fun v hv => (hφ v (by linarith)).2 hv.le, fun v hv0 hv => (hφ v hv0).1 hv⟩

/-- The reserve price for the uniform distribution on `[0, 1]` is `1/2`. -/
theorem reservePrice_uniform :
    reservePrice (virtualValue (volume.restrict (Icc 0 1)) (fun _ => 1)) = 1 / 2 :=
  (isRegular_uniform.isReserveThreshold hasValueDensity_uniform).unique isReserveThreshold_uniform

/-! ### A single item: the Vickrey auction with a reserve price -/

namespace Vickrey

variable [LinearOrder ι]

open Classical in
/-- The single-item virtual-welfare maximizer for a common virtual valuation `φ`: the highest
bidder (ties to the smallest index) wins, provided its virtual valuation is nonnegative. -/
@[expose] noncomputable def reserveAllocation (φ : ℝ → ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  if Wins b i ∧ 0 ≤ φ (b i) then 1 else 0

theorem reserveAllocation_binary (φ : ℝ → ℝ) (b : ι → ℝ) (i : ι) :
    reserveAllocation φ b i = 0 ∨ reserveAllocation φ b i = 1 := by
  unfold reserveAllocation
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem reserveAllocation_eq_one_iff {φ : ℝ → ℝ} {b : ι → ℝ} {i : ι} :
    reserveAllocation φ b i = 1 ↔ Wins b i ∧ 0 ≤ φ (b i) := by
  unfold reserveAllocation
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

theorem reserveAllocation_eq_zero_iff {φ : ℝ → ℝ} {b : ι → ℝ} {i : ι} :
    reserveAllocation φ b i = 0 ↔ ¬ (Wins b i ∧ 0 ≤ φ (b i)) := by
  unfold reserveAllocation
  split_ifs with h
  · exact iff_of_false one_ne_zero (not_not_intro h)
  · exact iff_of_true rfl h

theorem reserveAllocation_nonneg (φ : ℝ → ℝ) (b : ι → ℝ) (i : ι) :
    0 ≤ reserveAllocation φ b i := by
  rcases reserveAllocation_binary φ b i with h | h
  · rw [h]
  · rw [h]
    exact zero_le_one

theorem isBinary_reserveAllocation (φ : ℝ → ℝ) : IsBinary (reserveAllocation (ι := ι) φ) :=
  fun b _ i => reserveAllocation_binary φ b i

/-- The reserve rule awards the item only to the Vickrey winner. -/
theorem reserveAllocation_le_allocation (φ : ℝ → ℝ) (b : ι → ℝ) (i : ι) :
    reserveAllocation φ b i ≤ allocation b i := by
  rcases reserveAllocation_binary φ b i with h | h
  · rw [h]
    rcases allocation_binary b i with h' | h'
    · rw [h']
    · rw [h']
      exact zero_le_one
  · have : allocation b i = 1 := allocation_eq_one_iff.2 (reserveAllocation_eq_one_iff.1 h).1
    rw [h, this]

/-- The reserve rule is monotone when `φ` is nondecreasing on `[0, ∞)`. -/
theorem isMonotone_reserveAllocation {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Ici 0)) :
    IsMonotone (reserveAllocation (ι := ι) φ) := by
  intro i b _ z hz z' hz' hzz'
  change reserveAllocation φ (Function.update b i z) i ≤
    reserveAllocation φ (Function.update b i z') i
  rcases reserveAllocation_binary φ (Function.update b i z) i with h | h
  · rw [h]
    exact reserveAllocation_nonneg φ _ i
  · obtain ⟨hW, h0⟩ := reserveAllocation_eq_one_iff.1 h
    rw [Function.update_self] at h0
    have h' : reserveAllocation φ (Function.update b i z') i = 1 := by
      refine reserveAllocation_eq_one_iff.2 ⟨hW.update_of_le hzz', ?_⟩
      rw [Function.update_self]
      exact h0.trans (hφ hz hz' hzz')
    rw [h, h']

/-- The set of bid profiles at which bidder `i` wins is measurable. -/
theorem measurableSet_wins [Countable ι] (i : ι) : MeasurableSet {b : ι → ℝ | Wins b i} :=
  (Measurable.forall fun j => Measurable.imp measurable_const <|
    (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)).mem.and <|
      Measurable.imp measurable_const
        (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)).mem).setOf

/-- The Vickrey allocation is measurable in the bid profile. -/
theorem measurable_allocation [Countable ι] (i : ι) :
    Measurable fun b : ι → ℝ => allocation b i := by
  unfold allocation
  exact Measurable.ite (measurableSet_wins i) measurable_const measurable_const

/-- The reserve rule is measurable in the bid profile. -/
theorem measurable_reserveAllocation [Countable ι] {φ : ℝ → ℝ} (hφ : Measurable φ) (i : ι) :
    Measurable fun b : ι → ℝ => reserveAllocation φ b i := by
  have hR : MeasurableSet {b : ι → ℝ | 0 ≤ φ (b i)} :=
    measurableSet_le measurable_const (hφ.comp (measurable_pi_apply i))
  unfold reserveAllocation
  exact Measurable.ite ((measurableSet_wins i).inter hR) measurable_const measurable_const

variable [Fintype ι]

theorem reserveAllocation_mem_singleItemFeasible (φ : ℝ → ℝ) (b : ι → ℝ) :
    reserveAllocation φ b ∈ singleItemFeasible :=
  ⟨reserveAllocation_binary φ b,
    (Finset.sum_le_sum fun i _ => reserveAllocation_le_allocation φ b i).trans
      (allocation_mem_singleItemFeasible b).2⟩

/-- For i.i.d. bidders with a common virtual valuation `φ`, nondecreasing on `[0, ∞)`, awarding the
item to the highest bidder when its virtual valuation is nonnegative maximizes virtual welfare
([Roughgarden2013CS364A], Lecture 5, §3.1). -/
theorem isVirtualWelfareMaximizing_reserveAllocation {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Ici 0)) :
    IsVirtualWelfareMaximizing (fun _ => φ) singleItemFeasible (reserveAllocation (ι := ι) φ) := by
  intro b hb
  refine ⟨reserveAllocation_mem_singleItemFeasible φ b, fun y hy => ?_⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, le_refl]
  obtain ⟨w, hw⟩ := exists_wins b
  have hle : ∀ j, φ (b j) ≤ max 0 (φ (b w)) := fun j => by
    by_cases hj : j = w
    · rw [hj]
      exact le_max_right _ _
    · exact (hφ (hb j) (hb w) (hw j hj).1).trans (le_max_right _ _)
  have hy0 : ∀ j, 0 ≤ y j := fun j => by
    rcases hy.1 j with h | h
    · rw [h]
    · rw [h]
      exact zero_le_one
  have hL : ∑ j, φ (b j) * y j ≤ max 0 (φ (b w)) :=
    calc ∑ j, φ (b j) * y j ≤ ∑ j, max 0 (φ (b w)) * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (hy0 j)
      _ = max 0 (φ (b w)) * ∑ j, y j := by rw [Finset.mul_sum]
      _ ≤ max 0 (φ (b w)) * 1 := mul_le_mul_of_nonneg_left hy.2 (le_max_left _ _)
      _ = max 0 (φ (b w)) := mul_one _
  have hoff : ∀ j, j ≠ w → reserveAllocation φ b j = 0 := fun j hj => by
    rcases reserveAllocation_binary φ b j with h | h
    · exact h
    · exact absurd ((reserveAllocation_eq_one_iff.1 h).1.unique hw) hj
  have hR : ∑ j, φ (b j) * reserveAllocation φ b j = max 0 (φ (b w)) := by
    rw [Finset.sum_eq_single w (fun j _ hj => by rw [hoff j hj, mul_zero])
      (fun hw' => absurd (Finset.mem_univ w) hw')]
    by_cases h0 : 0 ≤ φ (b w)
    · rw [reserveAllocation_eq_one_iff.2 ⟨hw, h0⟩, mul_one, max_eq_right h0]
    · have : reserveAllocation φ b w = 0 := by
        rcases reserveAllocation_binary φ b w with h | h
        · exact h
        · exact absurd (reserveAllocation_eq_one_iff.1 h).2 h0
      rw [this, mul_zero, max_eq_left (le_of_not_ge h0)]
  rw [hR]
  exact hL

/-- **Myerson's optimal single-item auction** ([Roughgarden2013CS364A], Lecture 5, §3.1).

Setting: bidders are i.i.d. with a regular distribution `μ` that has density `f` on `[0, h]`.

Conclusion: every DSIC, individually rational single-item mechanism has expected revenue at most
that of awarding the item to the highest bidder when its virtual valuation is nonnegative, and
charging Myerson's payments. By `myersonPayment_reserveAllocation` and
`IsRegular.isReserveThreshold` this is the Vickrey auction with reserve price
`reservePrice (virtualValue μ f)`. -/
theorem integral_sum_payment_le_reserve {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal}
    {h : ℝ} (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h) {M : Mechanism ι}
    (hM : M.IsDSIC) (hIR : M.IsIR) (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi (fun _ : ι => μ) ≤
      ∫ v, ∑ i, (myerson (reserveAllocation (virtualValue μ f))).payment v i
        ∂Measure.pi (fun _ : ι => μ) :=
  integral_sum_payment_le_myerson (fun _ => hμ)
    (fun y hy i => by rcases hy.1 i with h | h <;> rw [h] <;> norm_num)
    (isVirtualWelfareMaximizing_reserveAllocation (hreg.strictMonoOn_Ici hμ).monotoneOn)
    (fun i => measurable_reserveAllocation hμ.measurable_virtualValue i) hM hIR hMX hMm

/-- With reserve threshold `r`, bidder `i`'s critical bid is `max(r, highest other bid)`. -/
theorem criticalBid_reserveAllocation {φ : ℝ → ℝ} {r : ℝ} (hr : IsReserveThreshold φ r)
    (b : ι → ℝ) (i : ι) :
    criticalBid (reserveAllocation φ) b i = max r (highestOtherBid b i) := by
  refine criticalBid_eq_of_threshold (le_max_of_le_left hr.1) (fun z hz => ?_) fun z hz h => ?_
  · refine reserveAllocation_eq_one_iff.2 ⟨wins_update_of_lt ((le_max_right _ _).trans_lt hz), ?_⟩
    rw [Function.update_self]
    exact hr.2.1 z ((le_max_left _ _).trans_lt hz)
  · obtain ⟨hW, h0⟩ := reserveAllocation_eq_one_iff.1 h
    rw [Function.update_self] at h0
    exact max_le (hr.2.2 z hz h0) (highestOtherBid_le_of_wins hz hW)

/-- **The optimal single-item auction is the Vickrey auction with reserve price `r`**
([Roughgarden2013CS364A], Lecture 5, §3.1). If `r` is a reserve threshold for `φ`, the winner pays
`max(r, highest other bid)` and losers pay nothing. -/
theorem myersonPayment_reserveAllocation {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Ici 0)) {r : ℝ}
    (hr : IsReserveThreshold φ r) {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    myersonPayment (reserveAllocation φ) b i = max r (highestOtherBid b i) *
      reserveAllocation φ b i := by
  rw [← criticalBid_mul_eq_myersonPayment (isMonotone_reserveAllocation hφ)
    (isBinary_reserveAllocation φ) hb i, criticalBid_reserveAllocation hr]

/-- **The second-price auction with reserve price `r` is optimal** ([Roughgarden2013CS364A],
Lecture 5, §3.1). Bidders are i.i.d. with a regular distribution `μ` that has density `f` on
`[0, h]`, and `r = reservePrice (virtualValue μ f)`. Every DSIC, individually rational
single-item mechanism has expected revenue at most that of selling to the highest bidder, if its
bid has nonnegative virtual valuation, at price `max(r, highest other bid)`. -/
theorem integral_sum_payment_le_secondPriceReserve {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → NNReal} {h : ℝ} (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h)
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi (fun _ : ι => μ) ≤
      ∫ v, ∑ i, max (reservePrice (virtualValue μ f)) (highestOtherBid v i) *
        reserveAllocation (virtualValue μ f) v i ∂Measure.pi (fun _ : ι => μ) := by
  refine (integral_sum_payment_le_reserve hμ hreg hM hIR hMX hMm).trans_eq (integral_congr_ae ?_)
  filter_upwards [ae_nonneg fun _ : ι => hμ] with v hv
  exact Finset.sum_congr rfl fun i _ => myersonPayment_reserveAllocation
    (hreg.strictMonoOn_Ici hμ).monotoneOn (hreg.isReserveThreshold hμ) hv i

end Vickrey

end Cslib.GameTheory.SingleParameter
