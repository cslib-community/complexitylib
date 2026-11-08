/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptivePath

/-!
# Adaptive bounds on supported histories

The envelopes in [Wang2027], Theorem 5 (PDF p. 12), Appendix A.5 (p. 16),
apply only when a turn is reached. `Reachable` records positive conditional
response probabilities along the actual transcript. Zero-weight summands are
removed directly: no modification of the actual response law is necessary.

## Main results

* `binomial_le_completion_reachable`: actual completion from supported-history envelopes.
* `totalBill_integrable_le_reachable`: actual infinite stopped cost from those envelopes.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open Cslib.Optimization.OneConstraint Finset MeasureTheory PartialCover
open scoped ENNReal

variable {Ω : Type} [Fintype Ω]

/-- A transcript with positive probability, obtained by supported responses from
its initial empty history. Lists are newest first. -/
inductive Reachable (law : List Ω → Distribution Ω ℝ) : List Ω → Prop
  | nil : Reachable law []
  | cons {h : List Ω} {x : Ω} : Reachable law h → 0 < (law h).weight x →
      Reachable law (x :: h)

/-- Null branches contribute zero to expectation, so observable bounds are needed
only at supported transcripts. The actual law is left unchanged. -/
theorem historyExpectation_mono_reachable (law : List Ω → Distribution Ω ℝ)
    (f g : List Ω → ℝ) (hfg : ∀ h, Reachable law h → f h ≤ g h)
    (n : ℕ) (h : List Ω) (hh : Reachable law h) :
    historyExpectation law f n h ≤ historyExpectation law g n h := by
  induction n generalizing h with
  | zero => exact hfg h hh
  | succ n ih =>
    apply sum_le_sum
    intro x _
    by_cases hx : (law h).weight x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left
        (ih _ (.cons hh (lt_of_le_of_ne ((law h).nonneg x) (Ne.symm hx))))
        ((law h).nonneg x)

/-- The lower count comparison needs its conditional bound only at supported
histories. This also permits arbitrary kernels on null transcripts. -/
theorem le_progressExpectation_reachable (law : List Ω → Distribution Ω ℝ)
    (b : List Ω → Ω → Bool) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hprob : ∀ h, Reachable law h → p ≤ (law h).mean (fun x => if b h x then 1 else 0))
    (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) (h : List Ω) (hh : Reachable law h) (k : ℕ) :
    bernoulliExpectation p f n k ≤ progressExpectation law b f n h k := by
  induction n generalizing h k with
  | zero => exact le_rfl
  | succ n ih =>
    have hm := bernoulliExpectation_mono p hp hp' f hf n
    have hb : (fun x => bernoulliExpectation p f n (k + if b h x then 1 else 0)) =
        (fun x => bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (if b h x then 1 else 0)) := by
      funext x
      split_ifs <;> simp
    calc
      _ ≤ bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (law h).mean (fun x => if b h x then 1 else 0) := by
        simp only [bernoulliExpectation]
        nlinarith [mul_le_mul_of_nonneg_left (hprob h hh)
          (sub_nonneg.mpr (hm (Nat.le_succ k)))]
      _ = (law h).mean (fun x => bernoulliExpectation p f n
          (k + if b h x then 1 else 0)) := by
        rw [hb, Distribution.mean_add, Distribution.mean_const, Distribution.mean_mul]
      _ ≤ _ := by
        apply sum_le_sum
        intro x _
        by_cases hx : (law h).weight x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left
            (ih _ (.cons hh (lt_of_le_of_ne ((law h).nonneg x) (Ne.symm hx))) _)
            ((law h).nonneg x)

/-- Supported finite transcripts occur almost surely under the original infinite
response law. Hence excluded histories are genuinely null cylinders, not an
extra restriction on the sampled process. -/
theorem ae_responseHistory_reachable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (law : List Ω → Distribution Ω ℝ) :
    ∀ᵐ ω ∂responseMeasure law, ∀ n, Reachable law (responseHistory ω n) := by
  classical
  apply ae_all_iff.mpr
  intro n
  let f : List Ω → ℝ := fun h => if Reachable law h then 0 else 1
  have he : historyExpectation law f n [] = 0 := by
    apply le_antisymm
    · have hm := historyExpectation_mono_reachable law f (fun _ => 0)
        (by intro h hh; simp [f, hh]) n [] .nil
      simpa only [historyExpectation_const] using hm
    · have hm := historyExpectation_mono law (fun _ => 0) f
        (by intro h; dsimp only [f]; split_ifs <;> norm_num) n []
      simpa only [historyExpectation_const] using hm
  have hi : Integrable (fun ω => f (responseHistory ω n)) (responseMeasure law) := by
    have hg : Integrable (fun x : Fin n → Ω => f (List.ofFn x).reverse)
        ((responseMeasure law).map (fun ω : ℕ → Ω => fun i : Fin n => ω i)) :=
      Integrable.of_finite
    exact hg.comp_measurable (by fun_prop)
  have hz : (∫ ω, f (responseHistory ω n) ∂responseMeasure law) = 0 := by
    rw [integral_responseHistory, he]
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun ω => show 0 ≤ f (responseHistory ω n) by
      dsimp only [f]; split_ifs <;> norm_num) hi).mp hz
  filter_upwards [hae] with ω hω
  by_contra hn
  simp [f, hn] at hω

/-- Explicit finite disintegration: first sample the selected batch, then its
response, retaining both in the transcript. Randomized selection is allowed. -/
@[expose] def selectedBatchLaw {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) : Distribution (B × R) ℝ :=
  (select h).bind fun b => (respond h b).map (fun x => (b, x))

/-- The joint response table factors into actual selected-batch mass and its
conditional response mass; this is proved from the constructed law. -/
theorem selectedBatchLaw_weight {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) (b : B) (x : R) :
    (selectedBatchLaw select respond h).weight (b, x) =
      (select h).weight b * (respond h b).weight x := by
  classical
  simp [selectedBatchLaw, Distribution.bind, Distribution.map, ite_and, mul_ite]

/-- Conditioning the joint table on a positive-probability selected batch recovers
its specified response table. Null batches require no division or condition. -/
theorem selectedBatchLaw_conditional {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) (b : B) (hb : 0 < (select h).weight b) (x : R) :
    (selectedBatchLaw select respond h).weight (b, x) / (select h).weight b =
      (respond h b).weight x := by
  rw [selectedBatchLaw_weight]
  exact mul_div_cancel_left₀ _ (ne_of_gt hb)

/-- Tower identity conditional on the actual selected batch, including null
batches. This derives the response law by composition rather than postulating it. -/
theorem selectedBatchLaw_mean {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) (f : B × R → ℝ) :
    (selectedBatchLaw select respond h).mean f =
      (select h).mean (fun b => (respond h b).mean (fun x => f (b, x))) := by
  simp only [selectedBatchLaw, Distribution.mean_bind, Distribution.mean_map,
    Function.comp_def]

/-- Batchwise lower bounds need only hold for batches selected with positive
conditional probability. No hypothesis on null batches is needed. -/
theorem selectedBatchLaw_mean_lower {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) (f : B × R → ℝ) (c : ℝ)
    (hc : ∀ b, 0 < (select h).weight b →
      c ≤ (respond h b).mean (fun x => f (b, x))) :
    c ≤ (selectedBatchLaw select respond h).mean f := by
  rw [selectedBatchLaw_mean, ← (select h).mean_const c]
  apply sum_le_sum
  intro b _
  by_cases hb : (select h).weight b = 0
  · simp [hb]
  · exact mul_le_mul_of_nonneg_left
      (hc b (lt_of_le_of_ne ((select h).nonneg b) (Ne.symm hb))) ((select h).nonneg b)

/-- The corresponding upper envelope for costs follows from the same actual
selected-batch tower, again ignoring null batches. -/
theorem selectedBatchLaw_mean_upper {B R : Type} [Fintype B] [Fintype R]
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (h : List (B × R)) (f : B × R → ℝ) (c : ℝ)
    (hc : ∀ b, 0 < (select h).weight b →
      (respond h b).mean (fun x => f (b, x)) ≤ c) :
    (selectedBatchLaw select respond h).mean f ≤ c := by
  rw [selectedBatchLaw_mean, ← (select h).mean_const c]
  apply sum_le_sum
  intro b _
  by_cases hb : (select h).weight b = 0
  · simp [hb]
  · exact mul_le_mul_of_nonneg_left
      (hc b (lt_of_le_of_ne ((select h).nonneg b) (Ne.symm hb))) ((select h).nonneg b)

variable {E J : Type*} [DecidableEq E] [DecidableEq J]

/-- Actual retained completion under a productivity envelope only on positive
probability histories. After completion productivity is automatically one. -/
theorem binomial_le_completion_reachable
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (law : List Ω → Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    (∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p) ≤
      historyExpectation law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) n [] := by
  have hc : ∀ h, (if r ≤ count (productive I ρ proposal a) h then (1 : ℝ) else 0) ≤
      (if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) := by
    intro h
    by_cases hh : r ≤ count (productive I ρ proposal a) h
    · have hd := count_completes I ρ proposal a h (hr.trans (Nat.mul_le_mul_left a hh))
      simp [hh, hd]
    · simp only [hh, ite_false]
      split_ifs <;> norm_num
  have hm := historyExpectation_mono law _ _ hc n []
  rw [historyExpectation_count law (productive I ρ proposal a)
    (fun k => if r ≤ k then 1 else 0) n []] at hm
  have ht := le_progressExpectation_reachable law (productive I ρ proposal a)
    p p.2.1 p.2.2 (by
      intro h hh
      by_cases hc : I.covered (selected I ρ proposal h) = I.ground
      · have hz : residual I ρ proposal h = 0 := by simp [residual, hc]
        have hx (x : Ω) : productive I ρ proposal a h x = true := by
          simp only [productive, decide_eq_true_eq]
          have := residual_mono I ρ proposal h x
          omega
        simpa only [hx, ite_true, Distribution.mean_const] using p.2.2
      · exact hp h hh hc) (fun k => if r ≤ k then 1 else 0) (by
      intro i j hij
      dsimp only
      split_ifs <;> norm_num; omega) n [] .nil 0
  rw [bernoulliExpectation_eq_integral] at ht
  simpa [count] using ht.trans hm

/-- Reachable-history version of `reach_le_binomial_complement`. -/
theorem reach_le_binomial_complement_reachable {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r t : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    historyExpectation law
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) t [] ≤
      1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p := by
  have hb := binomial_le_completion_reachable I ρ proposal law a r t hr p hp
  have he : (fun h =>
      (if I.covered (selected I ρ proposal h) = I.ground then (0 : ℝ) else 1) +
      (if I.covered (selected I ρ proposal h) = I.ground then (1 : ℝ) else 0)) =
      (fun _ => 1) := by
    funext h
    split_ifs <;> norm_num
  have hs := historyExpectation_add law
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) t []
  rw [he, historyExpectation_const] at hs
  linarith

/-- Reachable-history version of `stoppedCost_le_binomial_sum`. -/
theorem stoppedCost_le_binomial_sum_reachable {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, Reachable law h → bill h ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    executionCost law bill n [] ≤
      ∑ t ∈ Finset.range n, c *
        (1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p) := by
  rw [executionCost_eq_sum]
  apply Finset.sum_le_sum
  intro t _
  apply (historyExpectation_mono_reachable law bill
    (fun h => c * (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1))
    hb t [] .nil).trans
  rw [historyExpectation_mul]
  exact mul_le_mul_of_nonneg_left
    (reach_le_binomial_complement_reachable I ρ proposal law a r t hr p hp) hc

/-- Reachable-history version of `accruedBill_le_binomial_sum`. -/
theorem accruedBill_le_binomial_sum_reachable {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, Reachable law h → (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    historyExpectation law (accruedBill bill) n [] ≤
      ∑ t ∈ Finset.range n, c *
        (1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p) := by
  rw [historyExpectation_accruedBill, accruedBill, zero_add]
  exact stoppedCost_le_binomial_sum_reachable I ρ proposal law a r n hr p hp _ c hc hb

/-- Reachable-history version of `accruedBill_le_mean`. -/
theorem accruedBill_le_mean_reachable {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, Reachable law h → (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    historyExpectation law (accruedBill bill) n [] ≤ c * ((r : ℝ) / p) := by
  apply (accruedBill_le_binomial_sum_reachable I ρ proposal law a r n hr p hp bill c hc hb).trans
  simp only [← binomialFailure_eq_complement, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_binomialFailure_le p hp0 n r) hc

/-- Actual noncompletion remains summable under supported-history envelopes. -/
theorem summable_noncompletion_reachable {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    Summable (fun t => historyExpectation law
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) t []) := by
  apply (summable_binomialFailure p hp0 r).of_nonneg_of_le
  · intro t
    have hm := historyExpectation_mono law (fun _ => 0)
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)
      (fun h => by split_ifs <;> norm_num) t []
    simpa only [historyExpectation_const] using hm
  · intro t
    rw [binomialFailure_eq_complement]
    exact reach_le_binomial_complement_reachable I ρ proposal law a r t hr p hp

/-- Actual infinite total-cost bound with envelopes only on supported histories.
No equality to a replacement process or target integrability premise is needed. -/
theorem totalBill_integrable_le_reachable {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {E J : Type*}
    [DecidableEq E] [DecidableEq J]
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hbn : ∀ h x, 0 ≤ bill h x)
    (hb : ∀ h, Reachable law h → (law h).mean (bill h) ≤ c *
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
      (Filter.Eventually.of_forall fun ω => by
        change 0 ≤ accruedBill bill (responseHistory ω n)
        rw [accruedBill_responseHistory]
        exact Finset.sum_nonneg fun t _ => hbn _ _),
      integral_responseHistory]
    exact ENNReal.ofReal_le_ofReal
      (accruedBill_le_mean_reachable I ρ proposal law a r n hr p hp0 hp bill c hc hb)
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hae := ae_lt_top hm hfinite
  refine ⟨hae, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hae]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (mul_nonneg hc (div_nonneg (Nat.cast_nonneg r) p.2.1))] at h


/-- Source-form stopped billing: the raw conditional charge bound is required
only on supported histories at which another turn is issued. -/
theorem totalStoppedBill_integrable_le_reachable
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (law : List Ω → Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (p : ℝ) ≤ (law h).mean (fun x => if productive I ρ proposal a h x then 1 else 0))
    (charge : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hn : ∀ h x, 0 ≤ charge h x)
    (hb : ∀ h, Reachable law h → I.covered (selected I ρ proposal h) ≠ I.ground →
      (law h).mean (charge h) ≤ c) :
    let bill := stoppedBill I ρ proposal charge
    (∀ᵐ ω ∂responseMeasure law, totalBill bill ω < ⊤) ∧
    Integrable (fun ω => (totalBill bill ω).toReal) (responseMeasure law) ∧
    (∫ ω, (totalBill bill ω).toReal ∂responseMeasure law) ≤ c * ((r : ℝ) / p) := by
  apply totalBill_integrable_le_reachable I ρ proposal law a r hr p hp0 hp _ c hc
  · intro h x
    simp only [stoppedBill]
    split_ifs
    · exact le_refl 0
    · exact hn h x
  · intro h hh
    by_cases hd : I.covered (selected I ρ proposal h) = I.ground
    · simp [Distribution.mean, stoppedBill, hd]
    · simpa only [Distribution.mean, stoppedBill, hd, ite_false, mul_one]
        using hb h hh hd

/-- Composition with actual selected-batch envelopes. Selection may be randomized;
conditions on null histories and zero-probability selected batches are absent.
Responses retain the selected batch in the full history. -/
theorem selectedBatch_totalStoppedBill {B R : Type} [Fintype B] [Fintype R]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List (B × R) → B × R → List (Finset J))
    (select : List (B × R) → Distribution B ℝ)
    (respond : List (B × R) → B → Distribution R ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable (selectedBatchLaw select respond) h →
      I.covered (selected I ρ proposal h) ≠ I.ground → ∀ b, 0 < (select h).weight b →
      (p : ℝ) ≤ (respond h b).mean
        (fun x => if productive I ρ proposal a h (b, x) then 1 else 0))
    (charge : List (B × R) → B × R → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hn : ∀ h x, 0 ≤ charge h x)
    (hb : ∀ h, Reachable (selectedBatchLaw select respond) h →
      I.covered (selected I ρ proposal h) ≠ I.ground → ∀ b, 0 < (select h).weight b →
      (respond h b).mean (fun x => charge h (b, x)) ≤ c) :
    let law := selectedBatchLaw select respond
    let bill := stoppedBill I ρ proposal charge
    (∀ᵐ ω ∂responseMeasure law, totalBill bill ω < ⊤) ∧
    Integrable (fun ω => (totalBill bill ω).toReal) (responseMeasure law) ∧
    (∫ ω, (totalBill bill ω).toReal ∂responseMeasure law) ≤ c * ((r : ℝ) / p) := by
  apply totalStoppedBill_integrable_le_reachable I ρ proposal _ a r hr p hp0
    (fun h hh hd => selectedBatchLaw_mean_lower select respond h _ _ (hp h hh hd))
    charge c hc hn
  exact fun h hh hd => selectedBatchLaw_mean_upper select respond h _ _ (hb h hh hd)

/-- Actual a.s. eventual completion under supported, issued-turn envelopes. -/
theorem ae_eventually_complete_reachable {Ω : Type} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {E J : Type*} [DecidableEq E] [DecidableEq J]
    (I : PartialCover.Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, Reachable law h →
      I.covered (selected I ρ proposal h) ≠ I.ground → (p : ℝ) ≤ (law h).mean
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
  have hs := (summable_noncompletion_reachable I ρ proposal law a r hr p hp0 hp).tsum_ofReal_ne_top
  simp only [← he] at hs
  filter_upwards [ae_eventually_notMem hs] with ω hω
  simpa only [s, Set.mem_ofPred_eq, not_not] using hω

end Cslib.Probability.StochasticOracle.AdaptiveSelection
