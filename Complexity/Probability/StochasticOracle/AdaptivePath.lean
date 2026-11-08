/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveSelection
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Infinite response law for adaptive selection

`responseMeasure` constructs the full-history response process used in
[Wang2027], Theorem 5 and Appendix A.5 (PDF pp. 12, 16), from finite conditional
response tables. Histories are newest first, as in `AdaptiveSelection`.
The trajectory coordinates are responses, including auxiliary bill information;
they are not independent progress indicators.

`responseMeasure_condDistrib` identifies the conditional next-response law given
all preceding responses. It is an almost-everywhere statement on the actual prefix
law, including zero-probability histories without conditioning on null events.
`integral_responseHistory` identifies every finite cylinder expectation with
the finite accounting recursion. `ae_eventually_complete` transfers the summable
reach bounds to almost-sure eventual retained completion under the all-history
productivity envelope. `totalBill_integrable_le` constructs the actual total bill and
proves almost-sure finiteness, real integrability and the infinite expectation bound.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {Ω : Type*}

/-- Newest-first history after the first `n` responses of an infinite trajectory. -/
@[expose] def responseHistory (ω : ℕ → Ω) (n : ℕ) : List Ω :=
  (List.ofFn fun i : Fin n => ω i).reverse

/-- Decode all coordinates of a finite prefix into a newest-first history. -/
@[expose] def prefixHistory (n : ℕ) (x : (i : Finset.Iic n) → Ω) : List Ω :=
  (List.ofFn fun i : Fin (n + 1) => x ⟨i, by simpa using Nat.le_of_lt_succ i.isLt⟩).reverse

/-- The finite-prefix decoder agrees with the infinite-path observable. -/
theorem prefixHistory_restrict (ω : ℕ → Ω) (n : ℕ) :
    prefixHistory n (frestrictLe n ω) = responseHistory ω (n + 1) := rfl

/-- The next response is prepended, matching the finite execution convention. -/
theorem responseHistory_succ (ω : ℕ → Ω) (n : ℕ) :
    responseHistory ω (n + 1) = ω n :: responseHistory ω n := by
  simp only [responseHistory, List.ofFn_succ_last, List.reverse_append,
    List.reverse_singleton, Fin.val_last, Fin.val_castSucc, List.singleton_append]

variable [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The conditional response kernel reads the entire prefix, including auxiliary
response information. Discreteness makes every finite-history table measurable. -/
@[expose] def responseKernel
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Ω) Ω where
  toFun x := (law (prefixHistory n x)).toPMF.toMeasure
  measurable' := measurable_of_finite _

instance responseKernel_isMarkovKernel
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    IsMarkovKernel (responseKernel law n) :=
  ⟨fun x => by
    change IsProbabilityMeasure (law (prefixHistory n x)).toPMF.toMeasure
    infer_instance⟩

/-- Actual infinite response law, with first response sampled from `law []` and
subsequent responses from the table at their full newest-first history. -/
@[expose] def responseMeasure
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) :
    Measure (ℕ → Ω) :=
  Kernel.trajMeasure (law []).toPMF.toMeasure (responseKernel law)

instance responseMeasure_isProbabilityMeasure
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) :
    IsProbabilityMeasure (responseMeasure law) := by
  unfold responseMeasure
  infer_instance

/-- Consistent finite truncations: the joint law of a prefix and the next
response is obtained by applying the specified full-history kernel to that prefix.
This is a measure identity, without positivity requirements on individual histories. -/
theorem responseMeasure_prefix_joint
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    (responseMeasure law).map (frestrictLe n) ⊗ₘ responseKernel law n =
      (responseMeasure law).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- The infinite process has the specified conditional response law, almost
surely under its actual finite-prefix law. No independence is assumed. -/
theorem responseMeasure_condDistrib [StandardBorelSpace Ω] [Nonempty Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    condDistrib (fun ω : ℕ → Ω => ω (n + 1)) (frestrictLe n)
        (responseMeasure law) =ᵐ[(responseMeasure law).map (frestrictLe n)]
      responseKernel law n :=
  Kernel.condDistrib_trajMeasure

/-- Cylinder tower identity for the actual response process. The observable may
use every previous response and the next response, including its billed cost. -/
theorem integral_responseMeasure_step
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (n : ℕ) (f : ((i : Finset.Iic n) → Ω) → Ω → ℝ) :
    (∫ ω, f (frestrictLe n ω) (ω (n + 1)) ∂responseMeasure law) =
      ∫ x, (law (prefixHistory n x)).mean (f x)
        ∂(responseMeasure law).map (frestrictLe n) := by
  have hf : Integrable (Function.uncurry f)
      ((responseMeasure law).map (frestrictLe n) ⊗ₘ responseKernel law n) :=
    Integrable.of_finite
  change (∫ ω, Function.uncurry f (frestrictLe n ω, ω (n + 1))
    ∂responseMeasure law) = _
  rw [← MeasureTheory.integral_map (φ := fun ω : ℕ → Ω =>
      (frestrictLe n ω, ω (n + 1))) (by fun_prop)
    (measurable_of_finite (Function.uncurry f)).aestronglyMeasurable,
    ← responseMeasure_prefix_joint law n, Measure.integral_compProd hf]
  congr 1
  funext x
  change (∫ y, f x y ∂(law (prefixHistory n x)).toPMF.toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [Cslib.Optimization.OneConstraint.Distribution.toPMF_real,
    smul_eq_mul, Cslib.Optimization.OneConstraint.Distribution.mean]

/-- Tower identity in the newest-first history convention used by the finite
execution, for arbitrary finite-history observables. -/
theorem integral_responseHistory_succ
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (n : ℕ) (f : List Ω → ℝ) :
    (∫ ω, f (responseHistory ω (n + 2)) ∂responseMeasure law) =
      ∫ ω, (law (responseHistory ω (n + 1))).mean
        (fun y => f (y :: responseHistory ω (n + 1))) ∂responseMeasure law := by
  have ht := integral_responseMeasure_step law n
    (fun x y => f (y :: prefixHistory n x))
  rw [MeasureTheory.integral_map (by fun_prop)
    (measurable_of_finite _).aestronglyMeasurable] at ht
  simpa only [prefixHistory_restrict, responseHistory_succ] using ht

private theorem responseMeasure_prefix_zero
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) :
    (responseMeasure law).map (frestrictLe 0) =
      (law []).toPMF.toMeasure.map (MeasurableEquiv.piUnique _).symm := by
  rw [responseMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
private theorem historyExpectation_succ_right
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law f (n + 1) h =
      historyExpectation law (fun h => (law h).mean (fun y => f (y :: h))) n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change ((law h).mean fun x => historyExpectation law f (n + 1) (x :: h)) = _
    simp only [ih]
    rfl

/-- Every finite-history real observable under the constructed infinite process
has exactly the finite conditional-table expectation. No bound on bills or
productivity, and no independence assumption, is needed for this identity. -/
theorem integral_responseHistory
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f : List Ω → ℝ) (n : ℕ) :
    (∫ ω, f (responseHistory ω n) ∂responseMeasure law) =
      historyExpectation law f n [] := by
  induction n using Nat.twoStepInduction generalizing f with
  | zero => simp [responseHistory, historyExpectation]
  | one =>
    have he := responseMeasure_prefix_zero law
    have hm := MeasureTheory.integral_map (μ := responseMeasure law)
      (φ := frestrictLe 0) (f := fun x => f (prefixHistory 0 x))
      (by fun_prop) (measurable_of_finite _).aestronglyMeasurable
    rw [he, MeasureTheory.integral_map (by fun_prop)
      (measurable_of_finite _).aestronglyMeasurable, PMF.integral_eq_sum] at hm
    simpa [prefixHistory, responseHistory, historyExpectation,
      Cslib.Optimization.OneConstraint.Distribution.mean] using hm.symm
  | more n _ ih =>
    rw [integral_responseHistory_succ,
      ih (fun h => (law h).mean (fun y => f (y :: h)))]
    exact (historyExpectation_succ_right law f (n + 1) []).symm

omit [Fintype Ω] in
/-- Finite-history observables are measurable cylinders, even when their table on
all lists has no regularity assumption. -/
theorem measurable_responseHistory [Finite Ω] (n : ℕ) (f : List Ω → ℝ) :
    Measurable (fun ω : ℕ → Ω => f (responseHistory ω n)) := by
  have hm : Measurable (fun ω : ℕ → Ω => fun i : Fin n => ω i) := by fun_prop
  exact (measurable_of_finite (fun x : Fin n → Ω =>
    f (List.ofFn x).reverse)).comp hm

/-- Under the positive all-history productivity envelope, the actual infinite
retained-set execution is eventually complete almost surely. This transfers the
finite reach series through the cylinder law and Borel--Cantelli; it assumes no
termination or total-cost integrability premise. The all-history envelope is
stronger than the reachable selected-history condition in [Wang2027], Appendix A.5. -/
theorem ae_eventually_complete {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {E J : Type*} [DecidableEq E] [DecidableEq J]
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    ∀ᵐ ω ∂responseMeasure law, ∀ᶠ n in Filter.atTop,
      I.covered (selected I ρ proposal (responseHistory ω n)) = I.ground := by
  classical
  let s : ℕ → Set (ℕ → Ω) := fun n =>
    {ω | I.covered (selected I ρ proposal (responseHistory ω n)) ≠ I.ground}
  have he (n : ℕ) : responseMeasure law (s n) = ENNReal.ofReal
      (historyExpectation law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n []) := by
    have hm := measurable_responseHistory n
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)
    have hs : MeasurableSet (s n) := by
      have : s n = (fun ω => (if I.covered (selected I ρ proposal
          (responseHistory ω n)) = I.ground then (0 : ℝ) else 1)) ⁻¹' {1} := by
        ext ω
        simp only [s, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        split_ifs <;> simp_all
      rw [this]
      exact hm (measurableSet_singleton 1)
    have hi := integral_indicator_one (μ := responseMeasure law) hs
    have hid : (s n).indicator (1 : (ℕ → Ω) → ℝ) =
        (fun ω => if I.covered (selected I ρ proposal (responseHistory ω n)) =
          I.ground then 0 else 1) := by
      funext ω
      simp [s, Set.indicator]
    rw [hid] at hi
    change (∫ ω, (fun h => if I.covered (selected I ρ proposal h) = I.ground
      then (0 : ℝ) else 1) (responseHistory ω n) ∂responseMeasure law) = _ at hi
    rw [integral_responseHistory law
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) n] at hi
    rw [hi, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hs := (summable_noncompletion I ρ proposal law a r hr p hp0 hp).tsum_ofReal_ne_top
  simp only [← he] at hs
  filter_upwards [ae_eventually_notMem hs] with ω hω
  simpa only [s, Set.mem_ofPred_eq, not_not] using hω

/-- Stop response-dependent charges once the retained family covers the ground. -/
@[expose] def stoppedBill {E J : Type*} [DecidableEq E] [DecidableEq J]
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (charge : List Ω → Ω → ℝ)
    (h : List Ω) (x : Ω) : ℝ :=
  if I.covered (selected I ρ proposal h) = I.ground then 0 else charge h x

/-- Actual nonnegative extended total bill: the monotone limit of accrued bills.
For nonnegative charges this retains infinity on divergent trajectories. -/
@[expose] def totalBill (bill : List Ω → Ω → ℝ) (ω : ℕ → Ω) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (accruedBill bill (responseHistory ω n))

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The accrued bill is the partial sum of the actual response-dependent charges,
with the pre-response history used at each turn. -/
theorem accruedBill_responseHistory (bill : List Ω → Ω → ℝ) (ω : ℕ → Ω) (n : ℕ) :
    accruedBill bill (responseHistory ω n) =
      ∑ t ∈ Finset.range n, bill (responseHistory ω t) (ω t) := by
  induction n with
  | zero => simp [responseHistory, accruedBill]
  | succ n ih => rw [responseHistory_succ, accruedBill, ih, Finset.sum_range_succ]

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The extended total is exactly the nonnegative series of actual turn charges. -/
theorem totalBill_eq_tsum (bill : List Ω → Ω → ℝ) (hbn : ∀ h x, 0 ≤ bill h x)
    (ω : ℕ → Ω) :
    totalBill bill ω = ∑' t, ENNReal.ofReal (bill (responseHistory ω t) (ω t)) := by
  simp only [totalBill, accruedBill_responseHistory, ENNReal.tsum_eq_iSup_nat]
  congr 1
  funext n
  exact ENNReal.ofReal_sum_of_nonneg fun t _ => hbn _ _

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
private theorem accruedBill_nonneg (bill : List Ω → Ω → ℝ)
    (hb : ∀ h x, 0 ≤ bill h x) (h : List Ω) : 0 ≤ accruedBill bill h := by
  induction h with
  | nil => exact le_refl 0
  | cons x h ih => exact add_nonneg ih (hb h x)

/-- Each finite cylinder bill is integrable, without a global bill bound. -/
theorem integrable_accruedBill
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (bill : List Ω → Ω → ℝ) (n : ℕ) :
    Integrable (fun ω => accruedBill bill (responseHistory ω n)) (responseMeasure law) := by
  let g : (Fin n → Ω) → ℝ := fun x => accruedBill bill (List.ofFn x).reverse
  have hg : Integrable g ((responseMeasure law).map
      (fun ω : ℕ → Ω => fun i : Fin n => ω i)) := Integrable.of_finite
  exact hg.comp_measurable (by fun_prop)

omit [Fintype Ω] in
/-- The extended total is a measurable observable of the actual response path. -/
theorem measurable_totalBill [Finite Ω] (bill : List Ω → Ω → ℝ) : Measurable (totalBill bill) :=
  Measurable.iSup fun n => (measurable_responseHistory n (accruedBill bill)).ennreal_ofReal

/-- Monotone convergence transfers the finite conditional cost bound to the actual
infinite total bill. Nonnegativity and the conditional envelope are explicit;
neither integrability, termination nor a total-cost bound is assumed. For stopped
execution pass `stoppedBill I ρ proposal charge`, which is pointwise zero after
completion. The all-history productivity envelope remains stronger than the
reachable selected-batch condition of [Wang2027], Appendix A.5 (PDF p. 16). -/
theorem totalBill_integrable_le {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {E J : Type*}
    [DecidableEq E] [DecidableEq J]
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hbn : ∀ h x, 0 ≤ bill h x)
    (hb : ∀ h, (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    (∀ᵐ ω ∂responseMeasure law, totalBill bill ω < ⊤) ∧
    Integrable (fun ω => (totalBill bill ω).toReal) (responseMeasure law) ∧
    (∫ ω, (totalBill bill ω).toReal ∂responseMeasure law) ≤ c * ((r : ℝ) / p) := by
  have hm := measurable_totalBill bill
  have hmono : Monotone (fun n => fun ω : ℕ → Ω =>
      ENNReal.ofReal (accruedBill bill (responseHistory ω n))) := by
    apply monotone_nat_of_le_succ
    intro n ω
    apply ENNReal.ofReal_le_ofReal
    rw [responseHistory_succ, accruedBill]
    exact le_add_of_nonneg_right (hbn _ _)
  have hbound : (∫⁻ ω, totalBill bill ω ∂responseMeasure law) ≤
      ENNReal.ofReal (c * ((r : ℝ) / p)) := by
    change (∫⁻ ω, ⨆ n, ENNReal.ofReal (accruedBill bill (responseHistory ω n))
      ∂responseMeasure law) ≤ _
    rw [lintegral_iSup (fun n =>
      (measurable_responseHistory n (accruedBill bill)).ennreal_ofReal) hmono]
    apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_accruedBill law bill n)
      (Filter.Eventually.of_forall fun ω => accruedBill_nonneg bill hbn _),
      integral_responseHistory]
    exact ENNReal.ofReal_le_ofReal
      (accruedBill_le_mean I ρ proposal law a r n hr p hp0 hp bill c hc hb)
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hae := ae_lt_top hm hfinite
  refine ⟨hae, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hae]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (mul_nonneg hc (div_nonneg (Nat.cast_nonneg r) p.2.1))] at h

end Cslib.Probability.StochasticOracle.AdaptiveSelection
