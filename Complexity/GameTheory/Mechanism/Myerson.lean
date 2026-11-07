/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.GameTheory.Mechanism.SingleParameter
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Myerson's Lemma

Myerson's Lemma characterizes DSIC mechanisms in single-parameter environments
([Roughgarden2013CS364A], Lecture 3, Theorem 4.3; [Myerson1981]):

* (a) an allocation rule is implementable if and only if it is monotone;
* (b) for a monotone allocation rule there is exactly one payment rule making it DSIC with a
  bidder who bids `0` paying `0`;
* (c) that payment rule is `pᵢ(b) = bᵢ xᵢ(b) − ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`.

We prove the lemma for arbitrary monotone allocation rules, not only piecewise-constant or
differentiable ones: the integral is Mathlib's interval integral, and monotone functions are
interval integrable. Roughgarden states the formula as `∫₀^{bᵢ} z · x'ᵢ(z, b₋ᵢ) dz`
(Lecture 3, (7)), or as a sum over jumps for piecewise-constant rules (Lecture 3, (6)); the form
used here is the integration-by-parts version, which needs no differentiability.

The uniqueness proof makes Roughgarden's limiting argument precise. DSIC gives the payment
difference sandwich `z (x(y) − x(z)) ≤ p(y) − p(z) ≤ y (x(y) − x(z))` (Lecture 3, (4)); in terms
of the truthful utility `u(v) = v x(v) − p(v)` and the integral `I(v) = ∫₀^v x`, both `u(y) − u(z)`
and `I(y) − I(z)` lie in `[(y − z) x(z), (y − z) x(y)]`. Summing over a uniform partition of
`[0, b]` into `N` pieces bounds `|(u − I)(b) − (u − I)(0)|` by `b (x(b) − x(0)) / N`, so `u − I` is
constant on `[0, b]`.

## Main definitions

* `SingleParameter.myersonPayment`: the payment formula `bᵢ xᵢ(b) − ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`.
* `SingleParameter.myerson`: the mechanism pairing an allocation rule with this payment rule.

## Main results

* `SingleParameter.Mechanism.IsDSIC.payment_eq`: the payment identity: every DSIC payment rule is
  `pᵢ(b) = pᵢ(0, b₋ᵢ) + myersonPayment x b i` on nonnegative bid profiles.
* `SingleParameter.myerson_isDSIC`: monotone allocation rules are DSIC with Myerson's payments.
* `SingleParameter.isImplementable_iff_isMonotone`: Myerson's Lemma (a).
* `SingleParameter.Mechanism.IsDSIC.payment_eq_myersonPayment`: Myerson's Lemma (b) and (c).
* `SingleParameter.myerson_isNormalized`, `SingleParameter.utility_myerson`,
  `SingleParameter.myerson_isIR`, `SingleParameter.myersonPayment_nonneg`,
  `SingleParameter.myersonPayment_le`: the Myerson mechanism is normalized, and a truthful
  bidder's utility is `∫₀^{bᵢ} xᵢ`, so the mechanism is individually rational when allocations are
  nonnegative. For monotone rules `0 ≤ pᵢ(b)`, and `pᵢ(b) ≤ bᵢ xᵢ(b)` when a zero bid gets a
  nonnegative allocation (Lecture 3, (1)).

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
-/

open MeasureTheory intervalIntegral Filter Topology

public section

namespace Cslib.GameTheory.SingleParameter

variable {ι : Type*} [DecidableEq ι]

/-- **Myerson's payment formula** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (c)):
`pᵢ(b) = bᵢ xᵢ(b) − ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`. -/
@[expose] noncomputable def myersonPayment (x : (ι → ℝ) → ι → ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  b i * x b i - ∫ z in (0 : ℝ)..b i, x (Function.update b i z) i

/-- The mechanism pairing the allocation rule `x` with Myerson's payment formula. -/
@[expose] noncomputable def myerson (x : (ι → ℝ) → ι → ℝ) : Mechanism ι := ⟨x, myersonPayment x⟩

/-! ### The one-dimensional argument -/

/-- If `|φ y − φ z| ≤ (y − z)(f y − f z)` whenever `a ≤ z ≤ y ≤ b`, then `φ b = φ a`: summing
over a uniform partition of `[a, b]` into `N` pieces telescopes to
`|φ b − φ a| ≤ (b − a)(f b − f a) / N`. -/
private theorem eq_of_abs_sub_le_mul_sub {φ f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ z y, a ≤ z → z ≤ y → y ≤ b → |φ y - φ z| ≤ (y - z) * (f y - f z)) :
    φ b = φ a := by
  have key : ∀ N : ℕ, 0 < N → |φ b - φ a| ≤ (b - a) * (f b - f a) / N := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    set d := (b - a) / N with hd
    have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.2 hab) hNpos.le
    let t : ℕ → ℝ := fun k => a + k * d
    have ht0 : t 0 = a := by simp only [t, Nat.cast_zero, zero_mul, add_zero]
    have htN : t N = b := by simp only [t, d]; field_simp; ring
    have hstep : ∀ k, t (k + 1) - t k = d := by intro k; simp only [t]; push_cast; ring
    have hbounds : ∀ k, k < N → a ≤ t k ∧ t k ≤ t (k + 1) ∧ t (k + 1) ≤ b := by
      intro k hk
      refine ⟨?_, ?_, ?_⟩
      · have : (0 : ℝ) ≤ k * d := mul_nonneg (Nat.cast_nonneg k) hd0
        simp only [t]; linarith
      · linarith [hstep k]
      · have hk' : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
        have : ((k + 1 : ℕ) : ℝ) * d ≤ N * d := mul_le_mul_of_nonneg_right hk' hd0
        rw [← htN]; simp only [t]; linarith
    calc |φ b - φ a| = |∑ k ∈ Finset.range N, (φ (t (k + 1)) - φ (t k))| := by
          rw [Finset.sum_range_sub (fun k => φ (t k)), ht0, htN]
      _ ≤ ∑ k ∈ Finset.range N, |φ (t (k + 1)) - φ (t k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, d * (f (t (k + 1)) - f (t k)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨h1, h2, h3⟩ := hbounds k (Finset.mem_range.1 hk)
          have := h _ _ h1 h2 h3
          rwa [hstep k] at this
      _ = d * (f b - f a) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => f (t k)), ht0, htN]
      _ = (b - a) * (f b - f a) / N := by simp only [d]; ring
  have hlim : Tendsto (fun N : ℕ => (b - a) * (f b - f a) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hle : |φ b - φ a| ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => key N hN⟩)
  have := abs_nonpos_iff.1 hle
  linarith

/-- One bidder's truthfulness constraints along its own bid, with the others' bids fixed. -/
private def Truthful (x p : ℝ → ℝ) : Prop :=
  ∀ v z, 0 ≤ v → 0 ≤ z → v * x z - p z ≤ v * x v - p v

private theorem intervalIntegrable_of_monotoneOn {x : ℝ → ℝ} (hx : MonotoneOn x (Set.Ici 0))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable x volume a b :=
  (hx.mono fun c (hc : c ∈ Set.uIcc a b) => le_trans (le_inf ha hb) hc.1).intervalIntegrable

/-- For `x` monotone on `[0, ∞)` and `0 ≤ z ≤ y`, `(y − z) x(z) ≤ ∫_z^y x ≤ (y − z) x(y)`. -/
private theorem integral_bounds_of_monotoneOn {x : ℝ → ℝ} (hx : MonotoneOn x (Set.Ici 0))
    {z y : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) :
    (y - z) * x z ≤ ∫ t in z..y, x t ∧ ∫ t in z..y, x t ≤ (y - z) * x y := by
  have hy : 0 ≤ y := hz.trans hzy
  have hint := intervalIntegrable_of_monotoneOn hx hz hy
  constructor
  · have := integral_mono_on hzy intervalIntegrable_const hint
      (fun t ht => hx hz (hz.trans ht.1) ht.1)
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  · have := integral_mono_on hzy hint intervalIntegrable_const
      (fun t ht => hx (hz.trans ht.1) hy ht.2)
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this

private theorem integral_split {x : ℝ → ℝ} (hx : MonotoneOn x (Set.Ici 0)) {z y : ℝ}
    (hz : 0 ≤ z) (hy : 0 ≤ y) :
    ∫ t in (0 : ℝ)..y, x t = (∫ t in (0 : ℝ)..z, x t) + ∫ t in z..y, x t :=
  (integral_add_adjacent_intervals (intervalIntegrable_of_monotoneOn hx le_rfl hz)
    (intervalIntegrable_of_monotoneOn hx hz hy)).symm

/-- Uniqueness in one dimension: truthfulness forces `p(b) = p(0) + b x(b) − ∫₀^b x`. -/
private theorem payment_eq_of_truthful {x p : ℝ → ℝ} (hx : MonotoneOn x (Set.Ici 0))
    (h : Truthful x p) {b : ℝ} (hb : 0 ≤ b) :
    p b = p 0 + (b * x b - ∫ t in (0 : ℝ)..b, x t) := by
  set φ : ℝ → ℝ := fun v => (v * x v - p v) - ∫ t in (0 : ℝ)..v, x t with hφ
  have hconst : φ b = φ 0 := by
    refine eq_of_abs_sub_le_mul_sub (f := x) hb fun z y hz hzy _ => ?_
    have hy : 0 ≤ y := hz.trans hzy
    have h1 := h y z hy hz
    have h2 := h z y hz hy
    obtain ⟨hI1, hI2⟩ := integral_bounds_of_monotoneOn hx hz hzy
    simp only [hφ]
    rw [integral_split hx hz hy, abs_le]
    constructor <;> nlinarith
  simp only [hφ, intervalIntegral.integral_same, zero_mul, zero_sub, sub_zero] at hconst
  linarith

/-- Sufficiency in one dimension: Myerson's payments make a monotone curve truthful. -/
private theorem truthful_of_payment_eq {x p : ℝ → ℝ} (hx : MonotoneOn x (Set.Ici 0))
    (hp : ∀ b, 0 ≤ b → p b = p 0 + (b * x b - ∫ t in (0 : ℝ)..b, x t)) : Truthful x p := by
  intro v z hv hz
  rw [hp v hv, hp z hz, integral_split hx hz hv]
  rcases le_total z v with hzv | hvz
  · obtain ⟨h1, -⟩ := integral_bounds_of_monotoneOn hx hz hzv
    nlinarith
  · obtain ⟨-, h2⟩ := integral_bounds_of_monotoneOn hx hv hvz
    have := integral_symm (f := x) (μ := volume) v z
    nlinarith

/-! ### Myerson's Lemma -/

/-- **Payment identity.** Every DSIC payment rule agrees with Myerson's formula up to the payment
`pᵢ(0, b₋ᵢ)` of a zero bid: `pᵢ(b) = pᵢ(0, b₋ᵢ) + bᵢ xᵢ(b) − ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz` on every
nonnegative bid profile. -/
theorem Mechanism.IsDSIC.payment_eq {M : Mechanism ι} (hM : M.IsDSIC) (i : ι) {b : ι → ℝ}
    (hb : 0 ≤ b) :
    M.payment b i = M.payment (Function.update b i 0) i + myersonPayment M.allocation b i := by
  have := payment_eq_of_truthful (hM.isMonotone i b hb)
    (fun v z hv hz => hM.utility_update_le i hb hv hz) (hb i)
  simpa only [Function.update_eq_self, myersonPayment] using this

/-- **Myerson's Lemma, sufficiency** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (a), "if",
and (c)): a monotone allocation rule is DSIC with Myerson's payments. The proof is the "proof by
picture" of Lecture 3, Figure 2, for arbitrary monotone rules. -/
theorem myerson_isDSIC {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x) : (myerson x).IsDSIC := by
  intro i b v hb hv
  have hT : Truthful (fun z => x (Function.update b i z) i)
      (fun z => myersonPayment x (Function.update b i z) i) := by
    refine truthful_of_payment_eq (hx i b hb) fun c _ => ?_
    simp only [myersonPayment, Function.update_idem, Function.update_self,
      intervalIntegral.integral_same, zero_mul, sub_zero, zero_add]
  have := hT v (b i) hv (hb i)
  simpa only [myerson, Mechanism.utility, Function.update_eq_self] using this

/-- **Myerson's Lemma (a)** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (a)): an allocation
rule is implementable if and only if it is monotone. -/
theorem isImplementable_iff_isMonotone {x : (ι → ℝ) → ι → ℝ} :
    IsImplementable x ↔ IsMonotone x :=
  ⟨IsImplementable.isMonotone, fun hx => ⟨myersonPayment x, myerson_isDSIC hx⟩⟩

/-- **Myerson's Lemma (b), (c)** ([Roughgarden2013CS364A], Lecture 3, Theorem 4.3 (b), (c)): a
DSIC mechanism in which a zero bid pays zero charges exactly Myerson's payments on every
nonnegative bid profile. Together with `myerson_isDSIC` and `myerson_isNormalized`, the payment
rule extending a monotone allocation rule to a normalized DSIC mechanism is unique. -/
theorem Mechanism.IsDSIC.payment_eq_myersonPayment {M : Mechanism ι} (hM : M.IsDSIC)
    (hN : M.IsNormalized) (i : ι) {b : ι → ℝ} (hb : 0 ≤ b) :
    M.payment b i = myersonPayment M.allocation b i := by
  rw [hM.payment_eq i hb, hN i b hb, zero_add]

/-- Myerson's payments charge a zero bid nothing. -/
theorem myerson_isNormalized (x : (ι → ℝ) → ι → ℝ) : (myerson x).IsNormalized := by
  intro i b _
  simp only [myerson, myersonPayment, Function.update_self, zero_mul,
    intervalIntegral.integral_same, sub_zero]

/-- Under Myerson's payments a truthful bidder's utility is the area `∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz` under
its allocation curve. -/
theorem utility_myerson (x : (ι → ℝ) → ι → ℝ) (i : ι) (b : ι → ℝ) :
    (myerson x).utility i (b i) b = ∫ z in (0 : ℝ)..b i, x (Function.update b i z) i := by
  simp only [Mechanism.utility, myerson, myersonPayment]
  ring

/-- With nonnegative allocations, Myerson's mechanism is individually rational. -/
theorem myerson_isIR {x : (ι → ℝ) → ι → ℝ} (hx0 : ∀ b, 0 ≤ b → 0 ≤ x b) :
    (myerson x).IsIR := by
  intro i b hb
  rw [utility_myerson]
  exact intervalIntegral.integral_nonneg (hb i) fun z hz =>
    hx0 _ (update_nonneg hb i hz.1) i

/-- For a monotone allocation rule, Myerson's payments are nonnegative
([Roughgarden2013CS364A], Lecture 3, (1)). -/
theorem myersonPayment_nonneg {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x) {b : ι → ℝ}
    (hb : 0 ≤ b) (i : ι) : 0 ≤ myersonPayment x b i := by
  have h2 := (integral_bounds_of_monotoneOn (hx i b hb) le_rfl (hb i)).2
  rw [Function.update_eq_self, sub_zero] at h2
  simp only [myersonPayment]
  linarith

/-- For a monotone allocation rule, Myerson's payments never exceed the bid times the allocation
([Roughgarden2013CS364A], Lecture 3, (1)), when a zero bid gets a nonnegative allocation. -/
theorem myersonPayment_le {x : (ι → ℝ) → ι → ℝ} (hx : IsMonotone x) {b : ι → ℝ}
    (hb : 0 ≤ b) (i : ι) (hx0 : 0 ≤ x (Function.update b i 0) i) :
    myersonPayment x b i ≤ b i * x b i := by
  have h1 := (integral_bounds_of_monotoneOn (hx i b hb) le_rfl (hb i)).1
  have := mul_nonneg (hb i) hx0
  simp only [sub_zero] at h1
  simp only [myersonPayment]
  linarith

end Cslib.GameTheory.SingleParameter
