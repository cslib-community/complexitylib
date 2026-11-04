/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import Complexity.Foundations.Probability.HierarchyChildError
public import Complexity.Foundations.Probability.RootMetric.FiniteError
import Mathlib.Analysis.MeanInequalities

/-!
# Rooted lower-child errors on their own request domains

Finite fourth-moment payments for bounded normalized children on one full environment.
The positive cost charges only actual left support. Right requests reset their source to
that midpoint, so errors outside the midpoint source cannot enter this payment.
These original finite estimates do not construct a recursive approximate evaluator.
-/
public section
open Finset Cslib
open scoped BigOperators
noncomputable section
namespace Matrix.HierarchyParams.HierarchyTask
attribute [local instance] Classical.propDecidable

private lemma sum_fourth_le {I : Type*} (S : Finset I) (f : I → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) {B : ℝ} (hb : ∀ i ∈ S, f i ^ 4 ≤ B) :
    (∑ i ∈ S, f i) ^ 4 ≤ (#S : ℝ) ^ 4 * B := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S (f := f) (p := 4) (by norm_num) hf
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat] at h
  apply h.trans
  calc
    (#S : ℝ) ^ 3 * ∑ i ∈ S, f i ^ 4 ≤ (#S : ℝ) ^ 3 * ∑ _i ∈ S, B :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by positivity)
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

variable {k : ℕ} {Role Symbol V Ω : Type*} [Fintype V] [Fintype Ω]
  (channels : Role → ℝ → List Symbol → Ω → V → Prop)
  [∀ role rate suffix σ v, Decidable (channels role rate suffix σ v)]

/-- A pointwise fourth-power payment. Each error hypothesis is used only on the domain
where that child is actually called. In particular the reset right source is `z`, and the
left terminal is `z`; no off-source right error is requested. The union-support guard in
`positiveChildError` is essential here. -/
theorem positiveChildError_fourth_le (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : CorrectionRowTask.Channel Role (List Symbol)) (b CA CB : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V)
    {ED EL ER : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hD : |estimated (rawRequests l bin t source midpoint endpoint b).direct x y -
      canonical (rawRequests l bin t source midpoint endpoint b).direct x y| ^ 4 ≤ ED)
    (hL : ∀ z, |estimated (rawRequests l bin t source midpoint endpoint b).left x z -
      canonical (rawRequests l bin t source midpoint endpoint b).left x z| ^ 4 ≤ EL)
    (hR : ∀ z, estimated (rawRequests l bin t source midpoint endpoint b).left x z ≠ 0 ∨
      canonical (rawRequests l bin t source midpoint endpoint b).left x z ≠ 0 →
      |estimated (rawRequests l bin t source midpoint endpoint b).right z y -
        canonical (rawRequests l bin t source midpoint endpoint b).right z y| ^ 4 ≤ ER) :
    let R := rawRequests l bin t source midpoint endpoint b
    positiveChildError channels l bin t source midpoint endpoint b CA CB
        estimated canonical x y ^ 4 ≤
      8 * (|b * usageRatio channels endpoint R.direct y| ^ 4 * ED +
        |b * usageRatio channels endpoint R.right y *
          (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| ^ 4 *
          (Fintype.card V : ℝ) ^ 4 * (8 * (CA ^ 4 * ER + CB ^ 4 * EL))) := by
  let R := rawRequests l bin t source midpoint endpoint b
  let S := univ.filter (fun z => estimated R.left x z ≠ 0 ∨ canonical R.left x z ≠ 0)
  let f := fun z => CA * |estimated R.right z y - canonical R.right z y| +
    |estimated R.left x z - canonical R.left x z| * CB
  have hf : ∀ z ∈ S, 0 ≤ f z := by intros; dsimp only [f]; positivity
  have hp : ∀ z ∈ S, f z ^ 4 ≤ 8 * (CA ^ 4 * ER + CB ^ 4 * EL) := by
    intro z hz
    have hr := hR z (mem_filter.mp hz).2
    have hl := hL z
    have ha := add_pow_le
      (mul_nonneg hCA (abs_nonneg (estimated R.right z y - canonical R.right z y)))
      (mul_nonneg (abs_nonneg (estimated R.left x z - canonical R.left x z)) hCB) 4
    norm_num only [Nat.reduceSub, Nat.reducePow] at ha
    apply ha.trans
    simp only [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (mul_le_mul_of_nonneg_left hr (by positivity))
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (pow_nonneg hCB 4))
  have hs := sum_fourth_le S f hf hp
  have hB : 0 ≤ 8 * (CA ^ 4 * ER + CB ^ 4 * EL) := by positivity
  have hcard : (#S : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_card (filter_subset _ _)
  have hs' := hs.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hcard 4) hB)
  dsimp only [positiveChildError]
  change (_ + _ * ∑ z ∈ S, f z) ^ 4 ≤ _
  have ha := add_pow_le
    (a := |b * usageRatio channels endpoint R.direct y| *
      |estimated R.direct x y - canonical R.direct x y|)
    (b := |b * usageRatio channels endpoint R.right y *
      (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| * ∑ z ∈ S, f z)
    (by positivity) (by positivity) 4
  norm_num only [Nat.reduceSub, Nat.reducePow] at ha
  apply ha.trans
  simp only [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add (mul_le_mul_of_nonneg_left hD (by positivity))
    (by nlinarith only [mul_le_mul_of_nonneg_left hs' (show 0 ≤
      |b * usageRatio channels endpoint R.right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| ^ 4 by positivity)])

end Matrix.HierarchyParams.HierarchyTask


namespace Matrix.HierarchyParams.HierarchyTask
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {Role Symbol V Ω : Type*} [Fintype V] [Fintype Ω]
  (channels : Role → ℝ → List Symbol → Ω → V → Prop)
  [∀ role rate suffix σ v, Decidable (channels role rate suffix σ v)]

/-- Lower requests whose errors enter the finite residual: three positive requests per
bin and the endpoint negative at bin zero once, even when the positive bin set is empty. -/
@[expose] def residualErrorCalls (bins : Finset ℕ) (l : ℕ)
    (source midpoint terminal : CorrectionRowTask.Channel Role (List Symbol)) (b : ℕ → ℝ) :
    Finset (ℕ × Request k Role Symbol) :=
  (bins.biUnion fun i =>
    let r := rawRequests (k := k) l i .residual source midpoint terminal (b i)
    {(i, r.direct), (i, r.left), (i, r.right)}) ∪
  {(0, ⟨correctionAtomTask l false (Fin.last k), source,
    {terminal with rate := midpoint.rate},
    {terminal with rate := min terminal.rate midpoint.rate}⟩)}

/-- Actual conditional cost shared by the mean, common-envelope and output clients.
It sums positive bins and adds the special negative error once. -/
@[expose] def conditionalChildCost (bins : Finset ℕ) (l : ℕ)
    (source midpoint terminal : CorrectionRowTask.Channel Role (List Symbol))
    (b : ℕ → ℝ) (CA CB : ℝ)
    (estimated canonical : ℕ → Ω → Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  rowSliceMean (fun σ x => source.retains channels σ x)
    (fun σ y => terminal.retains channels σ y) (fun σ x y =>
      (∑ i ∈ bins, positiveChildError channels l i .residual source midpoint terminal
        (b i) CA CB (estimated i σ) (canonical i σ) x y) +
      negativeChildError channels l 0 .residual source midpoint terminal (b 0)
        (estimated 0 σ) (canonical 0 σ) x y) x y

/-- Literal finite importance and midpoint-density payment. The coarse bound uses the
sum of fourth powers over every endpoint to bound each coefficient. It pays a fourth
power of the positive-bin count and of the vertex width; no bin/rate factor is hidden. -/
@[expose] def residualCostCoefficient (bins : Finset ℕ) (l : ℕ)
    (source midpoint terminal : CorrectionRowTask.Channel Role (List Symbol))
    (b : ℕ → ℝ) (CA CB : ℝ) : ℝ :=
  let positive := fun i =>
    let r := rawRequests (k := k) l i .residual source midpoint terminal (b i)
    8 * ((∑ y : V, |b i * usageRatio channels terminal r.direct y| ^ 4) +
      8 * (Fintype.card V : ℝ) ^ 4 * (CA ^ 4 + CB ^ 4) *
        ∑ y : V, |b i * usageRatio channels terminal r.right y *
          (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| ^ 4)
  let negative : Request k Role Symbol :=
    ⟨correctionAtomTask l false (Fin.last k), source,
      {terminal with rate := midpoint.rate},
      {terminal with rate := min terminal.rate midpoint.rate}⟩
  8 * ((#bins : ℝ) ^ 4 * ∑ i ∈ bins, positive i +
    ∑ y : V, |midpoint.rate * usageRatio channels terminal negative y| ^ 4)

/-- Pointwise algebra for a shared, environment-dependent error envelope. The envelope
will be integrated, rather than bounded separately at every environment atom. -/
private theorem residualChildCost_fourth_le
    (bins : Finset ℕ) (l : ℕ)
    (source midpoint terminal : CorrectionRowTask.Channel Role (List Symbol))
    (b : ℕ → ℝ) {CA CB : ℝ} (q : Ω → ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hq : ∀ σ, 0 ≤ q σ)
    (estimated canonical : ℕ → Ω → Request k Role Symbol → Matrix V V ℝ)
    (hoff : ∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      ∀ σ x y, ¬ r.usage.retains channels σ y →
        estimated i σ r x y = 0 ∧ canonical i σ r x y = 0)
    (herror : ∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      ∀ σ x y, r.source.retains channels σ x →
        |estimated i σ r x y - canonical i σ r x y| ^ 4 ≤ q σ) :
    ∀ σ x y, source.retains channels σ x →
      |(∑ i ∈ bins, positiveChildError channels l i .residual source midpoint terminal
          (b i) CA CB (estimated i σ) (canonical i σ) x y) +
        negativeChildError channels l 0 .residual source midpoint terminal (b 0)
          (estimated 0 σ) (canonical 0 σ) x y| ^ 4 ≤
        residualCostCoefficient (k := k) channels bins l source midpoint terminal b CA CB *
          q σ := by
  let r := fun i => rawRequests (k := k) l i .residual source midpoint terminal (b i)
  let neg : Request k Role Symbol :=
    ⟨correctionAtomTask l false (Fin.last k), source,
      {terminal with rate := midpoint.rate},
      {terminal with rate := min terminal.rate midpoint.rate}⟩
  let coeff := fun i => 8 * ((∑ y : V, |b i * usageRatio channels terminal (r i).direct y| ^ 4) +
    8 * (Fintype.card V : ℝ) ^ 4 * (CA ^ 4 + CB ^ 4) *
      ∑ y : V, |b i * usageRatio channels terminal (r i).right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| ^ 4)
  let cost := fun σ x y => (∑ i ∈ bins, positiveChildError channels l i .residual
    source midpoint terminal (b i) CA CB (estimated i σ) (canonical i σ) x y) +
    negativeChildError channels l 0 .residual source midpoint terminal (b 0)
      (estimated 0 σ) (canonical 0 σ) x y
  have hcall (i : ℕ) (hi : i ∈ bins) (a : Request k Role Symbol)
      (ha : a ∈ [(r i).direct, (r i).left, (r i).right]) :
      (i, a) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [residualErrorCalls, mem_union, mem_biUnion]
    left
    refine ⟨i, hi, ?_⟩
    rcases ha with rfl | rfl | rfl <;> simp only [r, mem_insert, mem_singleton, true_or, or_true]
  have hn : (0, neg) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b := by
    simp only [residualErrorCalls, mem_union, mem_singleton]
    exact Or.inr rfl
  have hpos (σ : Ω) (x y : V) (hx : source.retains channels σ x) (i : ℕ) (hi : i ∈ bins) :
      positiveChildError channels l i .residual source midpoint terminal (b i) CA CB
        (estimated i σ) (canonical i σ) x y ^ 4 ≤ coeff i * (q σ) := by
    have hqσ := hq σ
    have hd := hcall i hi (r i).direct (by simp)
    have hl := hcall i hi (r i).left (by simp)
    have hr := hcall i hi (r i).right (by simp)
    have hleft (z : V) : |estimated i σ (r i).left x z - canonical i σ (r i).left x z| ^ 4 ≤
        q σ := by
      by_cases hz : midpoint.retains channels σ z
      · exact herror i _ hl σ x z hx
      · have h := hoff i _ hl σ x z hz
        simp only [h.1, h.2, sub_self, abs_zero, zero_pow (by decide : 4 ≠ 0)]
        exact (hq σ)
    have hright (z : V) (hz : estimated i σ (r i).left x z ≠ 0 ∨
        canonical i σ (r i).left x z ≠ 0) :
        |estimated i σ (r i).right z y - canonical i σ (r i).right z y| ^ 4 ≤ (q σ) := by
      have hm : midpoint.retains channels σ z := by
        by_contra hm
        have h := hoff i _ hl σ x z hm
        rcases hz with hz | hz
        · exact hz h.1
        · exact hz h.2
      exact herror i _ hr σ z y hm
    have hp := positiveChildError_fourth_le channels l i .residual source midpoint terminal
      (b i) CA CB (estimated i σ) (canonical i σ) x y hCA hCB (hq σ) (hq σ)
      (herror i _ hd σ x y hx) hleft hright
    dsimp only at hp
    have hdc : |b i * usageRatio channels terminal (r i).direct y| ^ 4 ≤
        ∑ w : V, |b i * usageRatio channels terminal (r i).direct w| ^ 4 :=
      single_le_sum (f := fun w : V => |b i * usageRatio channels terminal (r i).direct w| ^ 4)
        (fun _ _ => by positivity) (mem_univ y)
    have hpc : |b i * usageRatio channels terminal (r i).right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| ^ 4 ≤
        ∑ w : V, |b i * usageRatio channels terminal (r i).right w *
          (midpoint.rate / (dens {σ | midpoint.retains channels σ w} : ℝ))| ^ 4 :=
      single_le_sum (f := fun w : V => |b i * usageRatio channels terminal (r i).right w *
          (midpoint.rate / (dens {σ | midpoint.retains channels σ w} : ℝ))| ^ 4)
        (fun _ _ => by positivity) (mem_univ y)
    apply hp.trans
    dsimp only [coeff]
    nlinarith only [mul_le_mul_of_nonneg_right hdc (hq σ),
      mul_le_mul_of_nonneg_right hpc
        (show 0 ≤ (Fintype.card V : ℝ) ^ 4 * (8 * (CA ^ 4 * (q σ) + CB ^ 4 * (q σ))) by positivity)]
  have hpoint (σ : Ω) (x y : V) (hx : source.retains channels σ x) :
      |cost σ x y| ^ 4 ≤
        residualCostCoefficient (k := k) channels bins l source midpoint terminal b CA CB *
          q σ := by
    have hqσ := hq σ
    have hc : ∀ i ∈ bins, 0 ≤ positiveChildError channels l i .residual
        source midpoint terminal (b i) CA CB (estimated i σ) (canonical i σ) x y := by
      intros
      unfold positiveChildError
      positivity
    have hcoeff : ∀ i ∈ bins, coeff i ≤ ∑ j ∈ bins, coeff j :=
      fun i hi => single_le_sum (fun j _ => by dsimp only [coeff]; positivity) hi
    have hs := sum_fourth_le bins (fun i => positiveChildError channels l i .residual
      source midpoint terminal (b i) CA CB (estimated i σ) (canonical i σ) x y) hc
      (fun i hi => (hpos σ x y hx i hi).trans (mul_le_mul_of_nonneg_right (hcoeff i hi) (hq σ)))
    have he := herror 0 neg hn σ x y hx
    have hnc : |midpoint.rate * usageRatio channels terminal neg y| ^ 4 ≤
        ∑ w : V, |midpoint.rate * usageRatio channels terminal neg w| ^ 4 :=
      single_le_sum (f := fun w : V => |midpoint.rate * usageRatio channels terminal neg w| ^ 4)
        (fun _ _ => by positivity) (mem_univ y)
    have hn0 : 0 ≤ negativeChildError channels l 0 .residual source midpoint terminal (b 0)
        (estimated 0 σ) (canonical 0 σ) x y := by
      simp only [negativeChildError, rawRequests]
      positivity
    have hn4 : negativeChildError channels l 0 .residual source midpoint terminal (b 0)
        (estimated 0 σ) (canonical 0 σ) x y ^ 4 ≤
        (∑ w : V, |midpoint.rate * usageRatio channels terminal neg w| ^ 4) * (q σ) := by
      change (|midpoint.rate * usageRatio channels terminal neg y| *
        |estimated 0 σ neg x y - canonical 0 σ neg x y|) ^ 4 ≤ _
      rw [mul_pow]
      exact mul_le_mul hnc he (by positivity) (by positivity)
    have ha := add_pow_le (sum_nonneg hc) hn0 4
    norm_num only [Nat.reduceSub, Nat.reducePow] at ha
    dsimp only [cost]
    rw [abs_of_nonneg (add_nonneg (sum_nonneg hc) hn0)]
    apply ha.trans
    dsimp only [residualCostCoefficient]
    change _ ≤ 8 * ((#bins : ℝ) ^ 4 * ∑ i ∈ bins, coeff i + _) * (q σ)
    nlinarith only [hs, hn4]
  exact hpoint

end Matrix.HierarchyParams.HierarchyTask

namespace Matrix.HierarchyParams.HierarchyTask
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {Role Symbol V Ω : Type*} [Fintype V] [Fintype Ω]
  (channels : Role → ℝ → List Symbol → Ω → V → Prop)
  [∀ role rate suffix σ v, Decidable (channels role rate suffix σ v)]

/-- Sufficient explicit accuracy allocation from rooted moments on each called child's
own source/usage domain. The ordinary conversion is applied only to bounded nonnegative
normalized outputs. All finite vertex, bin, importance and midpoint-density costs
are displayed. The negative request is included once by `residualErrorCalls`.

Expectations and finite sums stay integrated on the full shared environment. No independence
or minimum atom probability is used. Recursive accuracy and parameter growth remain open. -/
theorem conditionalChildCost_le_of_root_budgets
    (bins : Finset ℕ) (l : ℕ)
    (source midpoint terminal : CorrectionRowTask.Channel Role (List Symbol))
    (b : ℕ → ℝ) {CA CB B N u δ : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hN : 0 < N) (hu : 0 < u) (hδ : 0 ≤ δ)
    (estimated canonical : ℕ → Ω → Request k Role Symbol → Matrix V V ℝ)
    (hsource : ∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      0 < r.source.rate)
    (hrange : ∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      ∀ σ x y, estimated i σ r x y ∈ Set.Icc 0 B ∧ canonical i σ r x y ∈ Set.Icc 0 B)
    (hoff : ∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      ∀ σ x y, ¬ r.usage.retains channels σ y →
        estimated i σ r x y = 0 ∧ canonical i σ r x y = 0) :
    let scale := (Fintype.card V : ℝ) ^ 2 / (N * u) *
      residualCostCoefficient (k := k) channels bins l source midpoint terminal b CA CB
    (∀ i r, (i, r) ∈ residualErrorCalls (k := k) bins l source midpoint terminal b →
      rootDistPow 4 N r.source.rate
        (fun σ x => r.source.retains channels σ x)
        (fun σ y => r.usage.retains channels σ y)
        (fun σ => estimated i σ r) (fun σ => canonical i σ r) ≤
      (δ / (1 + scale)) /
        (1 + (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * (N * r.source.rate)) /
        (1 + #(residualErrorCalls (k := k) bins l source midpoint terminal b))) →
    rowNormPow 4 N u (fun σ x => source.retains channels σ x)
      (fun σ y => terminal.retains channels σ y)
      (fun _ => conditionalChildCost channels bins l source midpoint terminal b CA CB
        estimated canonical) ≤ δ := by
  intro scale hroot
  let calls := residualErrorCalls (k := k) bins l source midpoint terminal b
  let entry := fun (a : ℕ × Request k Role Symbol) (σ : Ω) =>
    ∑ x ∈ ({x | a.2.source.retains channels σ x} : Finset V),
      ∑ y ∈ ({y | a.2.usage.retains channels σ y} : Finset V),
        |estimated a.1 σ a.2 x y - canonical a.1 σ a.2 x y| ^ 4
  let q := fun σ => ∑ a ∈ calls, entry a σ
  let c := (4 * B ^ ((3 : ℝ) / 4)) ^ 4
  let budget := δ / (1 + scale)
  have hs : 0 ≤ scale := by dsimp only [scale, residualCostCoefficient]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hb : 0 ≤ budget := by dsimp only [budget]; positivity
  have he0 (a : ℕ × Request k Role Symbol) (σ : Ω) : 0 ≤ entry a σ :=
    sum_nonneg fun x _ => sum_nonneg fun y _ => by positivity
  have hq (σ : Ω) : 0 ≤ q σ := sum_nonneg fun a _ => he0 a σ
  have hentry (i : ℕ) (r : Request k Role Symbol) (hr : (i, r) ∈ calls)
      (σ : Ω) (x y : V) (hx : r.source.retains channels σ x) :
      |estimated i σ r x y - canonical i σ r x y| ^ 4 ≤ q σ := by
    by_cases hy : r.usage.retains channels σ y
    · have hy' : y ∈ ({y | r.usage.retains channels σ y} : Finset V) := by simpa using hy
      have hx' : x ∈ ({x | r.source.retains channels σ x} : Finset V) := by simpa using hx
      have hrow : |estimated i σ r x y - canonical i σ r x y| ^ 4 ≤
          ∑ w ∈ ({w | r.usage.retains channels σ w} : Finset V),
            |estimated i σ r x w - canonical i σ r x w| ^ 4 :=
        single_le_sum (f := fun w => |estimated i σ r x w - canonical i σ r x w| ^ 4)
          (fun _ _ => by positivity) hy'
      have htable : (∑ w ∈ ({w | r.usage.retains channels σ w} : Finset V),
          |estimated i σ r x w - canonical i σ r x w| ^ 4) ≤ entry (i, r) σ :=
        single_le_sum (f := fun v =>
          ∑ w ∈ ({w | r.usage.retains channels σ w} : Finset V),
            |estimated i σ r v w - canonical i σ r v w| ^ 4)
          (fun _ _ => sum_nonneg fun _ _ => by positivity) hx'
      exact hrow.trans (htable.trans (single_le_sum (fun a _ => he0 a σ) hr))
    · rw [(hoff i r hr σ x y hy).1, (hoff i r hr σ x y hy).2, sub_self, abs_zero,
        zero_pow (by decide : 4 ≠ 0)]
      exact hq σ
  have hmoment (a : ℕ × Request k Role Symbol) (ha : a ∈ calls) :
      (𝔼 σ, entry a σ) ≤ budget / (1 + #calls) := by
    have hNu := mul_pos hN (hsource a.1 a.2 ha)
    have hconv := rowNormPow_sub_le_rootDistPow (s := 4)
      (X := fun σ x => a.2.source.retains channels σ x)
      (Y := fun σ y => a.2.usage.retains channels σ y)
      (H := fun σ => estimated a.1 σ a.2) (H' := fun σ => canonical a.1 σ a.2)
      (by decide) hNu.le
      (fun σ x y _ _ => (hrange a.1 a.2 ha σ x y).1)
      (fun σ x y _ _ => (hrange a.1 a.2 ha σ x y).2)
    norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hconv
    have heq : (𝔼 σ, entry a σ) = (N * a.2.source.rate) *
        rowNormPow 4 N a.2.source.rate
          (fun σ x => a.2.source.retains channels σ x)
          (fun σ y => a.2.usage.retains channels σ y)
          (fun σ x y => estimated a.1 σ a.2 x y - canonical a.1 σ a.2 x y) := by
      simp only [rowNormPow, entry, ← mul_assoc, mul_inv_cancel₀ hNu.ne', one_mul]
    rw [heq]
    apply (mul_le_mul_of_nonneg_left hconv hNu.le).trans
    rw [← mul_assoc]
    apply (mul_le_mul_of_nonneg_left (hroot a.1 a.2 ha) (mul_nonneg hNu.le hc)).trans
    change (N * a.2.source.rate) * c *
      (budget / (1 + c * (N * a.2.source.rate)) / (1 + #calls)) ≤ _
    have hd : 0 < 1 + c * (N * a.2.source.rate) := by positivity
    have hd' : (N * a.2.source.rate) * c *
        (budget / (1 + c * (N * a.2.source.rate))) ≤ budget := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      nlinarith
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hd' (show (0 : ℝ) ≤ 1 + #calls by positivity)
  have hmean : (𝔼 σ, q σ) ≤ budget := by
    calc
      _ = ∑ a ∈ calls, 𝔼 σ, entry a σ := by
        dsimp only [q]
        rw [expect_sum_comm]
      _ ≤ ∑ _a ∈ calls, budget / (1 + #calls) := sum_le_sum hmoment
      _ ≤ budget := by
        simp only [sum_const, nsmul_eq_mul]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith
  let cost := fun σ x y =>
    (∑ i ∈ bins, positiveChildError channels l i .residual source midpoint terminal
      (b i) CA CB (estimated i σ) (canonical i σ) x y) +
    negativeChildError channels l 0 .residual source midpoint terminal (b 0)
      (estimated 0 σ) (canonical 0 σ) x y
  have hpoint := residualChildCost_fourth_le channels bins l source midpoint terminal b q
    hCA hCB hq estimated canonical hoff hentry
  have hcoef : 0 ≤ residualCostCoefficient (k := k) channels bins l source midpoint terminal b
      CA CB := by unfold residualCostCoefficient; positivity
  apply (rowNormPow_sliceMean_fourth_le (mul_pos hN hu).le
    (fun σ x => source.retains channels σ x) (fun σ y => terminal.retains channels σ y)
    cost).trans
  apply (rowNormPow_fourth_le_expect_envelope (mul_pos hN hu).le
    (fun σ x => source.retains channels σ x) (fun σ y => terminal.retains channels σ y)
    cost (fun σ => residualCostCoefficient (k := k) channels bins l source midpoint terminal b
      CA CB * q σ) (fun σ => mul_nonneg hcoef (hq σ))
    (fun σ x y hx _ => hpoint σ x y hx)).trans
  rw [← mul_expect, ← mul_assoc]
  change scale * (𝔼 σ, q σ) ≤ δ
  apply (mul_le_mul_of_nonneg_left hmean hs).trans
  dsimp only [budget]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end Matrix.HierarchyParams.HierarchyTask
