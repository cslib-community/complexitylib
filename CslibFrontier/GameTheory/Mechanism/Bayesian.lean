/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Revenue
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith

/-!
# Bayes–Nash equilibrium and revenue equivalence

A sealed-bid mechanism `M : SingleParameter.Mechanism ι` is played by bidders with independent
private valuations: bidder `i`'s valuation is drawn from `μ i`, a distribution on `[0, h i]`, and
bidder `i` bids `β i v` when its valuation is `v`. This is the *independent single-dimensional
game* of [Hartline2021], Chapter 2, §2.4, with linear utility `v · x − p` (Definition 2.4.1).

From bidder `i`'s interim point of view (its own valuation known, the others drawn from the
prior and bidding according to `β`), a bid `z` wins `i` the expected allocation
`x̃ᵢ(z) = E_{v₋ᵢ}[xᵢ(z, β₋ᵢ(v₋ᵢ))]` and costs the expected payment `p̃ᵢ(z)`
(`Mechanism.interimAllocation`, `Mechanism.interimPayment`); Hartline writes `xᵢ(vᵢ) = x̃ᵢ(βᵢ(vᵢ))`
and `pᵢ(vᵢ) = p̃ᵢ(βᵢ(vᵢ))` for the interim rules indexed by values (§2.4). Both expectations are
integrals over the product prior `Measure.pi μ` in which coordinate `i` is overwritten; when the
`μ j` are probability measures this is the expectation over `v₋ᵢ`.

## Conventions

* **Support.** Types range over `[0, h i]`, the support of `HasValueDensity (μ i) (f i) (h i)`.
  The equilibrium condition is required for *every* type in `[0, h i]`, not only almost every one.
* **Deviations.** As in `Mechanism.IsDSIC`, legal bids are the nonnegative reals: strategies must
  prescribe a nonnegative bid to every type in the support, and a type may deviate to any bid
  `z ≥ 0`, inside or outside the range of its strategy.
* **Integrability.** The interim rules are Bochner integrals, which are `0` when the integrand is
  not integrable. The characterization below is purely about the interim rules and needs no
  integrability; the revenue formulas assume integrable payments and measurable, bounded
  allocations, as in `CslibFrontier.GameTheory.Mechanism.Revenue`.

## Main definitions

* `SingleParameter.Mechanism.interimAllocation`, `SingleParameter.Mechanism.interimPayment`: the
  interim rules `x̃ᵢ(z)`, `p̃ᵢ(z)` at bid `z`.
* `SingleParameter.Mechanism.IsBayesNash M μ h β`: `β` is a Bayes–Nash equilibrium
  ([Hartline2021], Definition 2.3.2).

## Main results

* `SingleParameter.IsTruthfulOn.payment_eq`, `SingleParameter.isTruthfulOn_of_payment_eq`: on an
  interval `[0, h]`, the one-dimensional incentive constraints `SingleParameter.IsTruthfulOn` hold
  if and only if `X` is monotone and `P(v) = P(0) + v X(v) − ∫₀ᵛ X` (monotonicity is
  `SingleParameter.IsTruthfulOn.monotoneOn`). This is Myerson's lemma for one interim curve; the
  proof reuses the DSIC machinery of `CslibFrontier.GameTheory.Mechanism.Myerson` through a
  one-bidder
  mechanism.
* `SingleParameter.Mechanism.IsBayesNash.monotoneOn`,
  `SingleParameter.Mechanism.IsBayesNash.interimPayment_eq`: **characterization of Bayes–Nash
  equilibrium** ([Hartline2021], Theorem 2.5.1, "only if"): each interim allocation rule
  `xᵢ` is monotone on `[0, hᵢ]` and `pᵢ(v) = pᵢ(0) + v xᵢ(v) − ∫₀ᵛ xᵢ`.
* `SingleParameter.Mechanism.isBayesNash_iff`: the converse (Theorem 2.5.1, "if"). Hartline assumes
  the strategies are onto the bid space; we assume instead that every legal bid is weakly
  dominated, for each type, by the bid of some type in the support. Onto strategies satisfy this
  with equality, and it also covers strategies that are not onto, such as the first-price
  equilibrium (compare [Hartline2021], Example 2.8.1 (v)(b)).
* `SingleParameter.Mechanism.IsBayesNash.integral_payment_eq_integral_interimAllocation`,
  `SingleParameter.Mechanism.IsBayesNash.integral_sum_payment_eq`: in a Bayes–Nash equilibrium
  bidder `i`'s expected payment is `pᵢ(0) + E[φᵢ(vᵢ) xᵢ(vᵢ)]` for its interim allocation rule `xᵢ`,
  and the expected revenue is `∑ᵢ pᵢ(0) + E[∑ᵢ φᵢ(vᵢ) xᵢ(β(v))]`, where `φᵢ` is the virtual
  valuation ([Myerson1981]; the Bayes–Nash form of [Roughgarden2013CS364A], Lecture 5, eq. (6)).
* `SingleParameter.Mechanism.IsBayesNash.integral_sum_payment_eq_of_interimAllocation_ae_eq`:
  **revenue equivalence** ([Hartline2021], Corollary 2.7.1): two Bayes–Nash equilibria, of possibly
  different mechanisms, with almost everywhere equal interim allocation rules and equal payments
  of the zero types have the same expected revenue.
  `SingleParameter.Mechanism.IsBayesNash.integral_sum_payment_eq_of_allocation_ae_eq` is the ex
  post form, assuming almost surely equal ex post allocations.
* `SingleParameter.Mechanism.IsBayesNash.interimPayment_eq_of_interimAllocation_eq`: the interim
  form, bidder by bidder (§2.7: "each agent has the same expected payment").

The first-price auction, whose uniform equilibrium is a client of this API, is in
`CslibFrontier.GameTheory.Mechanism.FirstPrice`.

## References

* [J. D. Hartline, *Mechanism Design and Approximation*][Hartline2021]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

/-- The value of `Set.projIcc 0 h hh z` at a point `z ∈ [0, h]` is `z`. -/
private theorem coe_projIcc_of_mem {h : ℝ} (hh : 0 ≤ h) {z : ℝ} (hz : z ∈ Icc 0 h) :
    (projIcc 0 h hh z : ℝ) = z := by
  rw [projIcc_of_mem hh hz]

/-- The one-bidder mechanism that runs the curves `X`, `P` on the bid projected to `[0, h]`. Above
`h` it is constant, so a type `v > h` behaves like the type `h`. -/
private noncomputable def clampMechanism (X P : ℝ → ℝ) {h : ℝ} (hh : 0 ≤ h) : Mechanism Unit :=
  ⟨fun b _ => X (projIcc 0 h hh (b ())), fun b _ => P (projIcc 0 h hh (b ()))⟩

private theorem clampMechanism_isDSIC {X P : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hT : IsTruthfulOn X P (Icc 0 h)) : (clampMechanism X P hh).IsDSIC := by
  intro i b v _ hv
  simp only [Mechanism.utility, clampMechanism, Function.update_self]
  have hw : (projIcc 0 h hh (b ()) : ℝ) ∈ Icc 0 h := Subtype.prop _
  by_cases hvh : v ≤ h
  · rw [coe_projIcc_of_mem hh ⟨hv, hvh⟩]
    exact hT v ⟨hv, hvh⟩ _ hw
  · have hhv : h ≤ v := le_of_not_ge hvh
    rw [projIcc_of_right_le hh hhv]
    have h1 := hT h ⟨hh, le_rfl⟩ _ hw
    have h2 := hT.monotoneOn hw ⟨hh, le_rfl⟩ hw.2
    nlinarith

/-- **Payment identity on an interval.** Incentive compatibility on `[0, h]` determines the payment
curve from the allocation curve and `P(0)`: `P(v) = P(0) + v X(v) − ∫₀ᵛ X`. -/
theorem IsTruthfulOn.payment_eq {X P : ℝ → ℝ} {h : ℝ} (hT : IsTruthfulOn X P (Icc 0 h))
    {v : ℝ} (hv : v ∈ Icc 0 h) :
    P v = P 0 + (v * X v - ∫ z in (0 : ℝ)..v, X z) := by
  have hh : 0 ≤ h := hv.1.trans hv.2
  have := (clampMechanism_isDSIC hh hT).payment_eq () (b := fun _ => v) (fun _ => hv.1)
  simp only [clampMechanism, myersonPayment, Function.update_self] at this
  rw [coe_projIcc_of_mem hh hv, coe_projIcc_of_mem hh ⟨le_rfl, hh⟩] at this
  rw [this]
  congr 2
  refine intervalIntegral.integral_congr fun z hz => ?_
  rw [uIcc_of_le hv.1] at hz
  rw [coe_projIcc_of_mem hh ⟨hz.1, hz.2.trans hv.2⟩]

/-- **Sufficiency on an interval.** A monotone allocation curve on `[0, h]` with the payments of the
payment identity is incentive compatible on `[0, h]`. -/
theorem isTruthfulOn_of_payment_eq {X P : ℝ → ℝ} {h : ℝ} (hX : MonotoneOn X (Icc 0 h))
    (hP : ∀ v ∈ Icc 0 h, P v = P 0 + (v * X v - ∫ z in (0 : ℝ)..v, X z)) :
    IsTruthfulOn X P (Icc 0 h) := by
  intro v hv w hw
  have hh : 0 ≤ h := hv.1.trans hv.2
  set g := fun z => X (projIcc 0 h hh z)
  have hg : Monotone g := fun a b hab =>
    hX (Subtype.prop _) (Subtype.prop _) (monotone_projIcc hh hab)
  have hD := myerson_isDSIC (x := fun b (_ : Unit) => g (b ()))
    (fun _ b _ => hg.monotoneOn _) () (fun _ => w) v (fun _ => hw.1) hv.1
  simp only [Mechanism.utility, myerson, myersonPayment, Function.update_self] at hD
  have hint : ∀ u ∈ Icc 0 h, ∫ z in (0 : ℝ)..u, g z = ∫ z in (0 : ℝ)..u, X z := by
    intro u hu
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hu.1] at hz
    simp only [g]
    rw [coe_projIcc_of_mem hh ⟨hz.1, hz.2.trans hu.2⟩]
  simp only [g, coe_projIcc_of_mem hh hv, coe_projIcc_of_mem hh hw, hint v hv, hint w hw] at hD
  rw [hP v hv, hP w hw]
  linarith

/-! ### Bayes–Nash equilibrium -/

namespace Mechanism

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **interim allocation** `x̃ᵢ(z)` of bidder `i` at bid `z` ([Hartline2021], §2.4): the
expected allocation of `i` when it bids `z` and every other bidder `j` bids `β j (v j)` with
`v ∼ Measure.pi μ`. -/
@[expose] noncomputable def interimAllocation (M : Mechanism ι) (μ : ι → Measure ℝ) (β : ι → ℝ → ℝ)
    (i : ι) (z : ℝ) : ℝ :=
  ∫ v, M.allocation (Function.update (fun j => β j (v j)) i z) i ∂Measure.pi μ

/-- The **interim payment** `p̃ᵢ(z)` of bidder `i` at bid `z` ([Hartline2021], §2.4): the expected
payment of `i` when it bids `z` and every other bidder `j` bids `β j (v j)` with
`v ∼ Measure.pi μ`. -/
@[expose] noncomputable def interimPayment (M : Mechanism ι) (μ : ι → Measure ℝ) (β : ι → ℝ → ℝ)
    (i : ι) (z : ℝ) : ℝ :=
  ∫ v, M.payment (Function.update (fun j => β j (v j)) i z) i ∂Measure.pi μ

/-- The strategy profile `β` is a **Bayes–Nash equilibrium** of `M` for the independent prior
`μ` with supports `[0, h i]` ([Hartline2021], Definition 2.3.2, for independent
single-dimensional games and stated through the interim rules of §2.4). For every bidder `i` and
every type `v ∈ [0, h i]`: the prescribed bid `β i v` is legal (nonnegative), and no legal bid
`z ≥ 0` gives `v` a higher interim utility `v x̃ᵢ(z) − p̃ᵢ(z)`. Deviations to bids outside the range
of `β i` are allowed.

The definition does not itself tie `h i` to `μ i`: `h i` is meant to be the support bound of `μ i`,
and the `μ i` are meant to be probability measures, as the revenue results assume
(`HasValueDensity`). Otherwise the condition can be vacuous: if `h i < 0` it constrains no type of
`i`, and if `μ j = 0` for some `j` all interim rules are `0`. -/
@[expose] def IsBayesNash (M : Mechanism ι) (μ : ι → Measure ℝ) (h : ι → ℝ) (β : ι → ℝ → ℝ) :
    Prop :=
  ∀ i, ∀ v ∈ Icc 0 (h i), 0 ≤ β i v ∧ ∀ z, 0 ≤ z →
    v * M.interimAllocation μ β i z - M.interimPayment μ β i z ≤
      v * M.interimAllocation μ β i (β i v) - M.interimPayment μ β i (β i v)

variable {M : Mechanism ι} {μ : ι → Measure ℝ} {h : ι → ℝ} {β : ι → ℝ → ℝ}

theorem IsBayesNash.nonneg (hM : M.IsBayesNash μ h β) {i : ι} {v : ℝ} (hv : v ∈ Icc 0 (h i)) :
    0 ≤ β i v :=
  (hM i v hv).1

/-- In a Bayes–Nash equilibrium the interim rules indexed by values, `xᵢ = x̃ᵢ ∘ βᵢ` and
`pᵢ = p̃ᵢ ∘ βᵢ`, are incentive compatible on the support. -/
theorem IsBayesNash.isTruthfulOn (hM : M.IsBayesNash μ h β) (i : ι) :
    IsTruthfulOn (fun v => M.interimAllocation μ β i (β i v))
      (fun v => M.interimPayment μ β i (β i v)) (Icc 0 (h i)) :=
  fun v hv _ hw => (hM i v hv).2 _ (hM.nonneg hw)

/-- **Bayes–Nash equilibrium, monotonicity** ([Hartline2021], Theorem 2.5.1 (i)): each interim
allocation rule `xᵢ(v) = x̃ᵢ(βᵢ(v))` is nondecreasing on `[0, hᵢ]`. -/
theorem IsBayesNash.monotoneOn (hM : M.IsBayesNash μ h β) (i : ι) :
    MonotoneOn (fun v => M.interimAllocation μ β i (β i v)) (Icc 0 (h i)) :=
  (hM.isTruthfulOn i).monotoneOn

/-- **Bayes–Nash equilibrium, payment identity** ([Hartline2021], Theorem 2.5.1 (ii)):
`pᵢ(v) = pᵢ(0) + v xᵢ(v) − ∫₀ᵛ xᵢ(z) dz` for every type `v ∈ [0, hᵢ]`. -/
theorem IsBayesNash.interimPayment_eq (hM : M.IsBayesNash μ h β) {i : ι} {v : ℝ}
    (hv : v ∈ Icc 0 (h i)) :
    M.interimPayment μ β i (β i v) = M.interimPayment μ β i (β i 0) +
      (v * M.interimAllocation μ β i (β i v) -
        ∫ z in (0 : ℝ)..v, M.interimAllocation μ β i (β i z)) :=
  (hM.isTruthfulOn i).payment_eq hv

/-- A strategy profile is a Bayes–Nash equilibrium iff it prescribes legal bids, the interim rules
indexed by values are incentive compatible on the support, and every legal bid is weakly dominated,
for each type, by the bid of some type in the support. The last condition replaces Hartline's
assumption that strategies are onto ([Hartline2021], Proposition 2.4.1). -/
theorem isBayesNash_iff_isTruthfulOn :
    M.IsBayesNash μ h β ↔ ∀ i,
      (∀ v ∈ Icc 0 (h i), 0 ≤ β i v) ∧
      IsTruthfulOn (fun v => M.interimAllocation μ β i (β i v))
        (fun v => M.interimPayment μ β i (β i v)) (Icc 0 (h i)) ∧
      ∀ v ∈ Icc 0 (h i), ∀ z, 0 ≤ z → ∃ w ∈ Icc 0 (h i),
        v * M.interimAllocation μ β i z - M.interimPayment μ β i z ≤
          v * M.interimAllocation μ β i (β i w) - M.interimPayment μ β i (β i w) := by
  refine ⟨fun hM i => ⟨fun v hv => hM.nonneg hv, hM.isTruthfulOn i,
    fun v hv z hz => ⟨v, hv, (hM i v hv).2 z hz⟩⟩, fun H i v hv => ⟨(H i).1 v hv, fun z hz => ?_⟩⟩
  obtain ⟨w, hw, hle⟩ := (H i).2.2 v hv z hz
  exact hle.trans ((H i).2.1 v hv w hw)

/-- **Characterization of Bayes–Nash equilibrium** ([Hartline2021], Theorem 2.5.1, both
directions): a strategy profile prescribing legal bids is a Bayes–Nash equilibrium iff each
interim allocation rule is monotone on the support, the payment identity holds, and every legal bid
is weakly dominated by the bid of some type in the support. Hartline's converse assumes onto
strategies, which satisfy the domination condition with equality. -/
theorem isBayesNash_iff :
    M.IsBayesNash μ h β ↔ ∀ i,
      (∀ v ∈ Icc 0 (h i), 0 ≤ β i v) ∧
      MonotoneOn (fun v => M.interimAllocation μ β i (β i v)) (Icc 0 (h i)) ∧
      (∀ v ∈ Icc 0 (h i), M.interimPayment μ β i (β i v) = M.interimPayment μ β i (β i 0) +
        (v * M.interimAllocation μ β i (β i v) -
          ∫ z in (0 : ℝ)..v, M.interimAllocation μ β i (β i z))) ∧
      ∀ v ∈ Icc 0 (h i), ∀ z, 0 ≤ z → ∃ w ∈ Icc 0 (h i),
        v * M.interimAllocation μ β i z - M.interimPayment μ β i z ≤
          v * M.interimAllocation μ β i (β i w) - M.interimPayment μ β i (β i w) := by
  rw [isBayesNash_iff_isTruthfulOn]
  refine forall_congr' fun i => and_congr_right fun _ => ?_
  refine ⟨fun ⟨hT, hD⟩ => ⟨hT.monotoneOn, fun _ hv => hT.payment_eq hv, hD⟩,
    fun ⟨hX, hP, hD⟩ => ⟨isTruthfulOn_of_payment_eq hX hP, hD⟩⟩

/-! ### Revenue -/

omit [Fintype ι] in
private theorem update_comp (β : ι → ℝ → ℝ) (v : ι → ℝ) (i : ι) (z : ℝ) :
    Function.update (fun j => β j (v j)) i (β i z) =
      fun j => β j (Function.update v i z j) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

variable [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal}

/-- Bidder `i`'s expected payment is the expectation of its interim payment `pᵢ(vᵢ)` over its own
valuation (Fubini over coordinate `i`). -/
theorem integral_payment_eq_integral_interimPayment (M : Mechanism ι) (β : ι → ℝ → ℝ) (i : ι)
    (hp : Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ)) :
    ∫ v, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      ∫ z, M.interimPayment μ β i (β i z) ∂μ i := by
  rw [← integral_integral_update_swap μ hp i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [interimPayment, update_comp]

private theorem integrable_interimPayment (M : Mechanism ι) (β : ι → ℝ → ℝ) (i : ι)
    (hp : Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ)) :
    Integrable (fun z => M.interimPayment μ β i (β i z)) (μ i) := by
  have hΦ := measurePreserving_update μ i
  have := (hΦ.integrable_comp_of_integrable hp).integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, interimPayment, update_comp]

private theorem integrable_virtualValue_mul_comp (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hM : M.IsBayesNash μ h β) (i : ι)
    (hx : Measurable fun v : ι → ℝ => M.allocation (fun j => β j (v j)) i) {B : ℝ}
    (hB : ∀ b, 0 ≤ b → |M.allocation b i| ≤ B) :
    Integrable (fun v => virtualValue (μ i) (f i) (v i) * M.allocation (fun j => β j (v j)) i)
      (Measure.pi μ) := by
  have hφ : Integrable (fun v : ι → ℝ => virtualValue (μ i) (f i) (v i)) (Measure.pi μ) :=
    integrable_comp_eval (hμ i).integrable_virtualValue
  refine Integrable.mono' (hφ.norm.mul_const B)
    (((hμ i).measurable_virtualValue.comp (measurable_pi_apply i)).mul hx).aestronglyMeasurable ?_
  filter_upwards [ae_mem_box hμ] with v hv
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB _ fun j => hM.nonneg (hv j)) (norm_nonneg _)

/-- **Expected payment in a Bayes–Nash equilibrium, interim form.** Bidder `i`'s expected payment is
the payment `pᵢ(0)` of its zero type plus `E[φᵢ(vᵢ) xᵢ(vᵢ)]`, where `xᵢ(v) = x̃ᵢ(βᵢ(v))` is its
interim allocation rule. This is the payment identity integrated against the prior, followed by the
one-dimensional revenue identity `HasValueDensity.integral_payment_eq_integral_virtualValue_mul`. -/
theorem IsBayesNash.integral_payment_eq_integral_interimAllocation
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) (hM : M.IsBayesNash μ h β) (i : ι)
    (hp : Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ)) {B : ℝ}
    (hB : ∀ b, 0 ≤ b → |M.allocation b i| ≤ B) :
    ∫ v, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      M.interimPayment μ β i (β i 0) +
        ∫ z, virtualValue (μ i) (f i) z * M.interimAllocation μ β i (β i z) ∂μ i := by
  have hh : 0 ≤ h i := by
    obtain ⟨v, hv⟩ := ((hμ i).ae_mem).exists
    exact hv.1.trans hv.2
  set g := fun z => M.interimAllocation μ β i (β i (projIcc 0 (h i) hh z)) with hgdef
  have hg : Monotone g := fun a b hab =>
    hM.monotoneOn i (Subtype.prop _) (Subtype.prop _) (monotone_projIcc hh hab)
  have hgB : ∀ z ∈ Icc 0 (h i), |g z| ≤ B := by
    intro z _
    have hc : (projIcc 0 (h i) hh z : ℝ) ∈ Icc 0 (h i) := Subtype.prop _
    simp only [hgdef, interimAllocation]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const ?_).trans_eq (by rw [probReal_univ, mul_one])
    filter_upwards [ae_mem_box hμ] with v hv
    rw [Real.norm_eq_abs]
    refine hB _ fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact hM.nonneg hc
    · rw [Function.update_of_ne hj]
      exact hM.nonneg (hv j)
  have hgI : ∀ z ∈ Icc 0 (h i), ∫ t in (0 : ℝ)..z, g t =
      ∫ t in (0 : ℝ)..z, M.interimAllocation μ β i (β i t) := by
    intro z hz
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hz.1] at ht
    simp only [hgdef, coe_projIcc_of_mem hh ⟨ht.1, ht.2.trans hz.2⟩]
  have key := (hμ i).integral_payment_eq_integral_virtualValue_mul hg.measurable hgB
  have hPint := integrable_interimPayment M β i hp
  have hPae : (fun z => M.interimPayment μ β i (β i z)) =ᵐ[μ i]
      fun z => M.interimPayment μ β i (β i 0) + (z * g z - ∫ t in (0 : ℝ)..z, g t) := by
    filter_upwards [(hμ i).ae_mem] with z hz
    rw [hM.interimPayment_eq hz, hgI z hz]
    simp only [hgdef, coe_projIcc_of_mem hh hz]
  have hQint : Integrable (fun z => z * g z - ∫ t in (0 : ℝ)..z, g t) (μ i) := by
    refine (hPint.sub (integrable_const (M.interimPayment μ β i (β i 0)))).congr ?_
    filter_upwards [hPae] with z hz
    rw [Pi.sub_apply, hz, add_sub_cancel_left]
  rw [integral_payment_eq_integral_interimPayment M β i hp, integral_congr_ae hPae,
    integral_add (integrable_const _) hQint, integral_const, probReal_univ, one_smul, key]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(hμ i).ae_mem] with z hz
  simp only [hgdef, coe_projIcc_of_mem hh hz]

/-- **Expected payment in a Bayes–Nash equilibrium.** Bidder `i`'s expected payment is the payment
`pᵢ(0)` of its zero type plus its expected virtual surplus `E[φᵢ(vᵢ) xᵢ(β(v))]` under the ex post
allocation. -/
theorem IsBayesNash.integral_payment_eq (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hM : M.IsBayesNash μ h β) (i : ι)
    (hp : Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ))
    (hx : Measurable fun v : ι → ℝ => M.allocation (fun j => β j (v j)) i) {B : ℝ}
    (hB : ∀ b, 0 ≤ b → |M.allocation b i| ≤ B) :
    ∫ v, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      M.interimPayment μ β i (β i 0) +
        ∫ v, virtualValue (μ i) (f i) (v i) * M.allocation (fun j => β j (v j)) i
          ∂Measure.pi μ := by
  rw [hM.integral_payment_eq_integral_interimAllocation hμ i hp hB,
    ← integral_integral_update_swap μ (integrable_virtualValue_mul_comp hμ hM i hx hB) i]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.update_self, update_comp, interimAllocation]
  rw [integral_const_mul]

/-- **Expected revenue in a Bayes–Nash equilibrium** ([Myerson1981]; compare
[Roughgarden2013CS364A], Lecture 5, eq. (6), for DSIC mechanisms): the expected revenue is the total
payment `∑ᵢ pᵢ(0)` of the zero types plus the expected virtual welfare `E[∑ᵢ φᵢ(vᵢ) xᵢ(β(v))]` of
the equilibrium allocation. -/
theorem IsBayesNash.integral_sum_payment_eq (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hM : M.IsBayesNash μ h β)
    (hp : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ))
    (hx : ∀ i, Measurable fun v : ι → ℝ => M.allocation (fun j => β j (v j)) i) {B : ℝ}
    (hB : ∀ b, 0 ≤ b → ∀ i, |M.allocation b i| ≤ B) :
    ∫ v, ∑ i, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      ∑ i, M.interimPayment μ β i (β i 0) +
        ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * M.allocation (fun j => β j (v j)) i
          ∂Measure.pi μ := by
  rw [integral_finsetSum _ fun i _ => hp i, integral_finsetSum _ fun i _ =>
    integrable_virtualValue_mul_comp hμ hM i (hx i) fun b hb => hB b hb i, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hM.integral_payment_eq hμ i (hp i) (hx i)
    fun b hb => hB b hb i

/-- **Revenue equivalence, ex post form** ([Hartline2021], Corollary 2.7.1). Two Bayes–Nash
equilibria, possibly of different mechanisms, whose ex post allocations agree almost surely and
whose zero types make the same interim payments, have the same expected revenue. Hartline states
it for zero types paying zero. Almost sure equality of the ex post allocations is stronger than
Hartline's "same BNE allocation", which is about interim allocation rules; that reading is
`IsBayesNash.integral_sum_payment_eq_of_interimAllocation_ae_eq`. -/
theorem IsBayesNash.integral_sum_payment_eq_of_allocation_ae_eq {M' : Mechanism ι}
    {β' : ι → ℝ → ℝ} (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hM : M.IsBayesNash μ h β) (hM' : M'.IsBayesNash μ h β')
    (hp : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ))
    (hp' : ∀ i, Integrable (fun v => M'.payment (fun j => β' j (v j)) i) (Measure.pi μ))
    (hx : ∀ i, Measurable fun v : ι → ℝ => M.allocation (fun j => β j (v j)) i)
    (hx' : ∀ i, Measurable fun v : ι → ℝ => M'.allocation (fun j => β' j (v j)) i) {B B' : ℝ}
    (hB : ∀ b, 0 ≤ b → ∀ i, |M.allocation b i| ≤ B)
    (hB' : ∀ b, 0 ≤ b → ∀ i, |M'.allocation b i| ≤ B')
    (hxx : ∀ᵐ v ∂Measure.pi μ, ∀ i,
      M.allocation (fun j => β j (v j)) i = M'.allocation (fun j => β' j (v j)) i)
    (h0 : ∀ i, M.interimPayment μ β i (β i 0) = M'.interimPayment μ β' i (β' i 0)) :
    ∫ v, ∑ i, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      ∫ v, ∑ i, M'.payment (fun j => β' j (v j)) i ∂Measure.pi μ := by
  rw [hM.integral_sum_payment_eq hμ hp hx hB, hM'.integral_sum_payment_eq hμ hp' hx' hB',
    Finset.sum_congr rfl fun i _ => h0 i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hxx] with v hv
  exact Finset.sum_congr rfl fun i _ => by rw [hv i]

/-- **Revenue equivalence** ([Hartline2021], Corollary 2.7.1). Two Bayes–Nash equilibria, possibly
of different mechanisms, whose interim allocation rules `xᵢ(v) = x̃ᵢ(βᵢ(v))` agree for almost every
type of every bidder and whose zero types make the same interim payments have the same expected
revenue. Hartline states it for zero types paying zero. Unlike the ex post form
`IsBayesNash.integral_sum_payment_eq_of_allocation_ae_eq`, it needs no measurability of the ex post
allocations. -/
theorem IsBayesNash.integral_sum_payment_eq_of_interimAllocation_ae_eq {M' : Mechanism ι}
    {β' : ι → ℝ → ℝ} (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hM : M.IsBayesNash μ h β) (hM' : M'.IsBayesNash μ h β')
    (hp : ∀ i, Integrable (fun v => M.payment (fun j => β j (v j)) i) (Measure.pi μ))
    (hp' : ∀ i, Integrable (fun v => M'.payment (fun j => β' j (v j)) i) (Measure.pi μ))
    {B B' : ℝ} (hB : ∀ b, 0 ≤ b → ∀ i, |M.allocation b i| ≤ B)
    (hB' : ∀ b, 0 ≤ b → ∀ i, |M'.allocation b i| ≤ B')
    (hxx : ∀ i, ∀ᵐ z ∂μ i,
      M.interimAllocation μ β i (β i z) = M'.interimAllocation μ β' i (β' i z))
    (h0 : ∀ i, M.interimPayment μ β i (β i 0) = M'.interimPayment μ β' i (β' i 0)) :
    ∫ v, ∑ i, M.payment (fun j => β j (v j)) i ∂Measure.pi μ =
      ∫ v, ∑ i, M'.payment (fun j => β' j (v j)) i ∂Measure.pi μ := by
  rw [integral_finsetSum _ fun i _ => hp i, integral_finsetSum _ fun i _ => hp' i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hM.integral_payment_eq_integral_interimAllocation hμ i (hp i) fun b hb => hB b hb i,
    hM'.integral_payment_eq_integral_interimAllocation hμ i (hp' i) fun b hb => hB' b hb i, h0 i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hxx i] with z hz
  rw [hz]

omit [∀ i, IsProbabilityMeasure (μ i)] in
/-- **Interim revenue equivalence** ([Hartline2021], §2.7): in two Bayes–Nash equilibria with the
same interim allocation rule for bidder `i` and the same payment for its zero type, every type of
`i` makes the same interim payment. -/
theorem IsBayesNash.interimPayment_eq_of_interimAllocation_eq {M' : Mechanism ι}
    {β' : ι → ℝ → ℝ} (hM : M.IsBayesNash μ h β) (hM' : M'.IsBayesNash μ h β') {i : ι}
    (hxx : ∀ v ∈ Icc 0 (h i),
      M.interimAllocation μ β i (β i v) = M'.interimAllocation μ β' i (β' i v))
    (h0 : M.interimPayment μ β i (β i 0) = M'.interimPayment μ β' i (β' i 0)) {v : ℝ}
    (hv : v ∈ Icc 0 (h i)) :
    M.interimPayment μ β i (β i v) = M'.interimPayment μ β' i (β' i v) := by
  rw [hM.interimPayment_eq hv, hM'.interimPayment_eq hv, h0, hxx v hv,
    intervalIntegral.integral_congr fun z hz => hxx z ?_]
  rw [uIcc_of_le hv.1] at hz
  exact ⟨hz.1, hz.2.trans hv.2⟩

end Mechanism

end Cslib.GameTheory.SingleParameter
