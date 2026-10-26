/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
public import Complexity.Computability.DecisionTree.Leaves
public import Complexity.Foundations.Data.BitString.CoverCoding

/-!
# Scalar query-activity run capacity

When every gate of a weighted threshold program `p` reads the original inputs along a single
direction `w : Fin n → ℝ` (`∀ j, ∃ c : ℝ, inputWeight p j = c • w`), fixing the restricted
input-reading transcript `transcript p x` turns every gate condition into a half-line condition on
the weighted sum `weightedSum w x = ∑ i, w i * (x i).toNat`. Consequently, the fibers of
`transcript p` (and of the full gate evaluation `p.eval interpretation`) are order-convex along
`weightedSum w` (`eval_eq_of_weightedSum_between`, `transcript_eq_of_weightedSum_between`).

Extending the evaluation from the finite set of realized scalar scores to all of `ℝ` produces a
one-dimensional step function `scalarEval p w : ℝ → (Fin g → Bool)` whose level sets are indexed
by the monotone count of transcripts realized up to `t`. This yields at most
`(attainableTranscripts p).card` pieces (`piecesAtMost_scalarEval`, `piecesAtMost_scalarTranscript`,
`piecesAtMost_scalarReadout`) and at most `(attainableTranscripts p).card - 1` changes
(`changesAtMost_scalarReadout`), bounding the length of any score-ordered alternating run of
outputs by `(attainableTranscripts p).card` and hence by the Hamming-ball sums at `inputActivity p`
and `gateActivity p` (Theorem 4.1 of `[ThresholdCircuitRepresentations2026]`). Combining this
one-dimensional representation with the multilevel rectangle-free capacity bound gives the scalar
activity lower bounds for two-sided `K`-rectangle-free functions (Corollary 4.2). Cover's
enumerative coding for weight-bounded words (Theorem 4.3) is in
`Complexity.Foundations.Data.BitString.CoverCoding`.

Conversely, a supplied ordered class index on the Boolean cube can be computed by real threshold
comparisons along `weightedSum w` with the exact ordered-tree capacity
(`exists_scalarComparisonTree_iff`). Scores may tie within a class; distinct ordered classes must
have strictly separated scores. Relabelling integer queries preserves the tree shape, depth and
true-answer energy. This supplies the real-score tree, not the subsequent compilation into a
fixed number of native input-reading circuit stages.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.leInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarRep`: inputs with scalar score at most `t` and a
  canonical representative input for `t`.
* `Cslib.Circuits.Boolean.WeightedThreshold.scalarEval`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarTranscript`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarReadout`: extension of gate evaluation,
  input-reading transcripts, and readouts to `ℝ` along `weightedSum w`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_weightedSum_between`,
  `Cslib.Circuits.Boolean.WeightedThreshold.transcript_eq_of_weightedSum_between`: order-convexity
  of gate evaluations and transcripts along `weightedSum w`.
* `Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarTranscript`,
  `Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarReadout`,
  `Cslib.Circuits.Boolean.WeightedThreshold.changesAtMost_scalarReadout`: piece and change bounds
  in terms of `(attainableTranscripts p).card` (Theorem 4.1).
* `Cslib.Circuits.Boolean.WeightedThreshold.length_le_card_attainableTranscripts_of_isChain`,
  `Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_of_isChain`,
  `Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_gateActivity_of_isChain`:
  alternating-run capacity bounds along `weightedSum w`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_card_attainableTranscripts_of_direction`,
  `WeightedThreshold.two_pow_lt_mul_max_card_attainableTranscripts_of_direction`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_of_direction`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_gateActivity_of_direction`:
  rectangle-free scalar activity bounds (Corollary 4.2).
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_scalarComparisonTree_iff`: real threshold trees
  realizing a supplied ordered class index, with exact structural leaf count and bounded depth
  and true-answer energy.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ}

/-! ### Section 4.1: Order-convexity of scalar-direction transcripts and run capacity -/

private theorem sum_inputWeight_eq_mul_weightedSum {p : Program signature n g} {w : Fin n → ℝ}
    {j : Fin g} {c : ℝ} (hc : inputWeight p j = c • w) (x : Fin n → Bool) :
    (∑ i : Fin n, inputWeight p j i * (x i).toNat) = c * weightedSum w x := by
  have hfun := fun i => congrFun hc i
  simp only [Pi.smul_apply, smul_eq_mul] at hfun
  simp only [weightedSum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hfun i, mul_assoc]

/-- **Order-convexity of gate evaluations along a scalar direction**: if every gate's input weight
vector is a multiple of `w`, `weightedSum w x₁ ≤ weightedSum w x₂ ≤ weightedSum w x₃`, and
`transcript p x₁ = transcript p x₃`, then `p.eval interpretation x₂ = p.eval interpretation x₁`. -/
theorem eval_eq_of_weightedSum_between (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ x₃ : Fin n → Bool}
    (h₁₂ : weightedSum w x₁ ≤ weightedSum w x₂)
    (h₂₃ : weightedSum w x₂ ≤ weightedSum w x₃)
    (htr : transcript p x₁ = transcript p x₃) :
    p.eval interpretation x₂ = p.eval interpretation x₁ := by
  have heval₁₃ : p.eval interpretation x₁ = p.eval interpretation x₃ :=
    eval_eq_of_transcript_eq p htr
  funext j
  induction j using Fin.strong_induction_on with
  | h j ih =>
    obtain ⟨c, hc⟩ := hw j
    have hgate₁ := eval_gate_eq p x₁ j
    have hgate₂ := eval_gate_eq p x₂ j
    have hgate₃ := eval_gate_eq p x₃ j
    rw [sum_inputWeight_eq_mul_weightedSum hc] at hgate₁ hgate₂ hgate₃
    have hsum₂₁ : (∑ k : Fin g, gateWeight p j k * (p.eval interpretation x₂ k).toNat) =
        ∑ k : Fin g, gateWeight p j k * (p.eval interpretation x₁ k).toNat := by
      refine sum_congr rfl fun k _ => ?_
      by_cases hkj : k < j
      · rw [ih k hkj]
      · rw [gateWeight_eq_zero_of_le p j k (le_of_not_gt hkj)]
        ring
    have hsum₃₁ : (∑ k : Fin g, gateWeight p j k * (p.eval interpretation x₃ k).toNat) =
        ∑ k : Fin g, gateWeight p j k * (p.eval interpretation x₁ k).toNat := by
      rw [heval₁₃]
    rw [hsum₂₁] at hgate₂
    rw [hsum₃₁] at hgate₃
    have hj₁₃ : p.eval interpretation x₁ j = p.eval interpretation x₃ j :=
      congrFun heval₁₃ j
    rw [hgate₁, hgate₃] at hj₁₃
    rw [hgate₂, hgate₁, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff] at hj₁₃
    rcases le_total 0 c with hc0 | hc0
    · have hle₁₂ : c * weightedSum w x₁ ≤ c * weightedSum w x₂ :=
        mul_le_mul_of_nonneg_left h₁₂ hc0
      have hle₂₃ : c * weightedSum w x₂ ≤ c * weightedSum w x₃ :=
        mul_le_mul_of_nonneg_left h₂₃ hc0
      exact ⟨fun h₂ => hj₁₃.mpr (by linarith), fun h₁ => by linarith⟩
    · have hle₂₁ : c * weightedSum w x₂ ≤ c * weightedSum w x₁ :=
        mul_le_mul_of_nonpos_left h₁₂ hc0
      have hle₃₂ : c * weightedSum w x₃ ≤ c * weightedSum w x₂ :=
        mul_le_mul_of_nonpos_left h₂₃ hc0
      exact ⟨fun h₂ => by linarith, fun h₁ => by linarith [hj₁₃.mp h₁]⟩

/-- **Order-convexity of input-reading transcripts along a scalar direction**. -/
theorem transcript_eq_of_weightedSum_between (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ x₃ : Fin n → Bool}
    (h₁₂ : weightedSum w x₁ ≤ weightedSum w x₂)
    (h₂₃ : weightedSum w x₂ ≤ weightedSum w x₃)
    (htr : transcript p x₁ = transcript p x₃) :
    transcript p x₂ = transcript p x₁ := by
  funext j
  exact congrFun (eval_eq_of_weightedSum_between p w hw h₁₂ h₂₃ htr) j.val

/-- Inputs with equal scalar score have identical gate evaluations. -/
theorem eval_eq_of_weightedSum_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ : Fin n → Bool} (h : weightedSum w x₁ = weightedSum w x₂) :
    p.eval interpretation x₁ = p.eval interpretation x₂ := by
  funext j
  induction j using Fin.strong_induction_on with
  | h j ih =>
    obtain ⟨c, hc⟩ := hw j
    rw [eval_gate_eq, eval_gate_eq, sum_inputWeight_eq_mul_weightedSum hc,
      sum_inputWeight_eq_mul_weightedSum hc, h]
    congr 3
    refine sum_congr rfl fun k _ => ?_
    by_cases hkj : k < j
    · rw [ih k hkj]
    · rw [gateWeight_eq_zero_of_le p j k (le_of_not_gt hkj)]
      ring

/-- Inputs with equal scalar score have identical input-reading transcripts. -/
private theorem transcript_eq_of_weightedSum_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ : Fin n → Bool} (h : weightedSum w x₁ = weightedSum w x₂) :
    transcript p x₁ = transcript p x₂ := by
  funext j
  exact congrFun (eval_eq_of_weightedSum_eq p w hw h) j.val

/-- The set of attainable transcripts is always nonempty. -/
theorem attainableTranscripts_nonempty (p : Program signature n g) :
    (attainableTranscripts p).Nonempty := by
  classical
  exact ⟨transcript p (fun _ => false), mem_image_of_mem _ (mem_univ _)⟩

/-- The number of attainable transcripts of `p` is positive. -/
theorem card_attainableTranscripts_pos (p : Program signature n g) :
    0 < (attainableTranscripts p).card :=
  (attainableTranscripts_nonempty p).card_pos

/-- Boolean inputs with scalar score at most `t`. -/
noncomputable def leInputs (w : Fin n → ℝ) (t : ℝ) : Finset (Fin n → Bool) :=
  univ.filter fun x => weightedSum w x ≤ t

open scoped Classical in
/-- Input-reading transcripts realized by inputs with scalar score at most `t`. -/
private noncomputable def leTranscripts (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    Finset (inputGates p → Bool) :=
  (leInputs w t).image (transcript p)

private theorem leInputs_subset {w : Fin n → ℝ} {t t' : ℝ} (htt' : t ≤ t') :
    leInputs w t ⊆ leInputs w t' := by
  intro x hx
  simp only [leInputs, mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.trans htt'

private theorem leTranscripts_subset {p : Program signature n g} {w : Fin n → ℝ} {t t' : ℝ}
    (htt' : t ≤ t') :
    leTranscripts p w t ⊆ leTranscripts p w t' := by
  classical
  exact image_subset_image (leInputs_subset htt')

private theorem leTranscripts_subset_attainableTranscripts (p : Program signature n g)
    (w : Fin n → ℝ) (t : ℝ) :
    leTranscripts p w t ⊆ attainableTranscripts p := by
  classical
  exact image_subset_image (subset_univ _)

private theorem card_leTranscripts_le (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    (leTranscripts p w t).card ≤ (attainableTranscripts p).card :=
  card_le_card (leTranscripts_subset_attainableTranscripts p w t)

/-- Representative input at scalar threshold `t`: an input in `leInputs w t` maximizing
`weightedSum w` when `leInputs w t` is nonempty, and a global minimizer of `weightedSum w`
otherwise. -/
noncomputable def scalarRep (w : Fin n → ℝ) (t : ℝ) : Fin n → Bool :=
  if h : (leInputs w t).Nonempty then
    (exists_max_image (leInputs w t) (weightedSum w) h).choose
  else
    (exists_min_image (univ : Finset (Fin n → Bool)) (weightedSum w)
      ⟨fun _ => false, mem_univ _⟩).choose

/-- One-dimensional extension of gate evaluation along `weightedSum w`. -/
noncomputable def scalarEval (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    Fin g → Bool :=
  p.eval interpretation (scalarRep w t)

/-- One-dimensional extension of the input-reading transcript along `weightedSum w`. -/
noncomputable def scalarTranscript (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    inputGates p → Bool :=
  transcript p (scalarRep w t)

/-- One-dimensional extension of a gate readout along `weightedSum w`. -/
noncomputable def scalarReadout {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (readout : (Fin g → Bool) → β) (t : ℝ) : β :=
  readout (scalarEval p w t)

private theorem scalarRep_mem_of_nonempty {w : Fin n → ℝ} {t : ℝ}
    (h : (leInputs w t).Nonempty) :
    scalarRep w t ∈ leInputs w t := by
  simp only [scalarRep, h, ↓reduceDIte]
  exact (exists_max_image (leInputs w t) (weightedSum w) h).choose_spec.1

private theorem le_weightedSum_scalarRep_of_mem {w : Fin n → ℝ} {t : ℝ} {x : Fin n → Bool}
    (hx : x ∈ leInputs w t) :
    weightedSum w x ≤ weightedSum w (scalarRep w t) := by
  have h : (leInputs w t).Nonempty := ⟨x, hx⟩
  simp only [scalarRep, h, ↓reduceDIte]
  exact (exists_max_image (leInputs w t) (weightedSum w) h).choose_spec.2 x hx

private theorem weightedSum_scalarRep_eq (w : Fin n → ℝ) (x : Fin n → Bool) :
    weightedSum w (scalarRep w (weightedSum w x)) = weightedSum w x := by
  have hx : x ∈ leInputs w (weightedSum w x) := by simp [leInputs]
  have hrep := scalarRep_mem_of_nonempty ⟨x, hx⟩
  simp only [leInputs, mem_filter, mem_univ, true_and] at hrep
  exact le_antisymm hrep (le_weightedSum_scalarRep_of_mem hx)

/-- Evaluating `scalarEval p w` at `weightedSum w x` recovers `p.eval interpretation x`. -/
@[simp] theorem scalarEval_weightedSum (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) (x : Fin n → Bool) :
    scalarEval p w (weightedSum w x) = p.eval interpretation x :=
  eval_eq_of_weightedSum_eq p w hw (weightedSum_scalarRep_eq w x)

/-- Evaluating `scalarTranscript p w` at `weightedSum w x` recovers `transcript p x`. -/
@[simp] theorem scalarTranscript_weightedSum (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) (x : Fin n → Bool) :
    scalarTranscript p w (weightedSum w x) = transcript p x :=
  transcript_eq_of_weightedSum_eq p w hw (weightedSum_scalarRep_eq w x)

/-- Evaluating `scalarReadout p w readout` at `weightedSum w x` recovers
`readout (p.eval interpretation x)`. -/
@[simp] theorem scalarReadout_weightedSum {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) (x : Fin n → Bool) :
    scalarReadout p w readout (weightedSum w x) = readout (p.eval interpretation x) := by
  rw [scalarReadout, scalarEval_weightedSum p w hw x]

private theorem scalarEval_eq_of_le_of_rank_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) {t t' : ℝ} (htt' : t ≤ t')
    (hcard : (leTranscripts p w t).card - 1 = (leTranscripts p w t').card - 1) :
    scalarEval p w t = scalarEval p w t' := by
  classical
  let xmin := (exists_min_image (univ : Finset (Fin n → Bool)) (weightedSum w)
    ⟨fun _ => false, mem_univ _⟩).choose
  have hxmin : ∀ x : Fin n → Bool, weightedSum w xmin ≤ weightedSum w x := fun x =>
    (exists_min_image (univ : Finset (Fin n → Bool)) (weightedSum w)
      ⟨fun _ => false, mem_univ _⟩).choose_spec.2 x (mem_univ x)
  have hsub : leTranscripts p w t ⊆ leTranscripts p w t' := leTranscripts_subset htt'
  by_cases h1 : (leTranscripts p w t').card ≤ 1
  · have hval : ∀ s : ℝ, (leTranscripts p w s).card ≤ 1 →
        scalarEval p w s = p.eval interpretation xmin := by
      intro s hs
      by_cases hne : (leInputs w s).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hne
        have hxmin_mem : xmin ∈ leInputs w s := by
          simp only [leInputs, mem_filter, mem_univ, true_and] at hx₀ ⊢
          exact (hxmin x₀).trans hx₀
        have hrep_mem : scalarRep w s ∈ leInputs w s := scalarRep_mem_of_nonempty ⟨x₀, hx₀⟩
        have htr_eq : transcript p (scalarRep w s) = transcript p xmin :=
          card_le_one.mp hs _ (mem_image_of_mem _ hrep_mem) _ (mem_image_of_mem _ hxmin_mem)
        exact eval_eq_of_transcript_eq p htr_eq
      · unfold scalarEval scalarRep
        rw [dite_eq_right hne]
    have ht1 : (leTranscripts p w t).card ≤ 1 := (card_le_card hsub).trans h1
    rw [hval t ht1, hval t' h1]
  · have hcard_eq : (leTranscripts p w t).card = (leTranscripts p w t').card := by omega
    have htr_set_eq : leTranscripts p w t = leTranscripts p w t' :=
      eq_of_subset_of_card_le hsub hcard_eq.ge
    have hne_tr : (leTranscripts p w t).Nonempty := card_pos.mp (by omega)
    obtain ⟨_, hx_tr⟩ := hne_tr
    obtain ⟨x₀, hx₀, -⟩ := mem_image.mp hx_tr
    have hne : (leInputs w t).Nonempty := ⟨x₀, hx₀⟩
    have hne' : (leInputs w t').Nonempty := hne.mono (leInputs_subset htt')
    have hrep_t : scalarRep w t ∈ leInputs w t := scalarRep_mem_of_nonempty hne
    have hrep_t' : scalarRep w t' ∈ leInputs w t' := scalarRep_mem_of_nonempty hne'
    have hmem_tr' : transcript p (scalarRep w t') ∈ leTranscripts p w t := by
      rw [htr_set_eq]
      exact mem_image_of_mem _ hrep_t'
    obtain ⟨x₁, hx₁, htr₁⟩ := mem_image.mp hmem_tr'
    have h₁₂ : weightedSum w x₁ ≤ weightedSum w (scalarRep w t) :=
      le_weightedSum_scalarRep_of_mem hx₁
    have h₂₃ : weightedSum w (scalarRep w t) ≤ weightedSum w (scalarRep w t') :=
      le_weightedSum_scalarRep_of_mem (leInputs_subset htt' hrep_t)
    unfold scalarEval
    exact (eval_eq_of_weightedSum_between p w hw h₁₂ h₂₃ htr₁).trans
      (eval_eq_of_transcript_eq p htr₁)

/-- **Theorem 4.1 (Piece bound for scalar-direction gate evaluation)**: when every gate reads
inputs along `w`, `scalarEval p w` has at most `(attainableTranscripts p).card` pieces on `ℝ`. -/
theorem piecesAtMost_scalarEval (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) :
    PiecesAtMost (scalarEval p w) (attainableTranscripts p).card := by
  classical
  refine ⟨fun t => (leTranscripts p w t).card - 1, ?_, ?_, ?_⟩
  · intro t t' htt'
    exact Nat.sub_le_sub_right (card_le_card (leTranscripts_subset htt')) 1
  · intro t
    dsimp only
    have hpos := card_attainableTranscripts_pos p
    have hle := card_leTranscripts_le p w t
    omega
  · intro t t' heq
    rcases le_total t t' with htt' | ht't
    · exact scalarEval_eq_of_le_of_rank_eq p w hw htt' heq
    · exact (scalarEval_eq_of_le_of_rank_eq p w hw ht't heq.symm).symm

/-- **Theorem 4.1 (Piece bound for scalar-direction transcripts)**: `scalarTranscript p w` has at
most `(attainableTranscripts p).card` pieces on `ℝ`. -/
theorem piecesAtMost_scalarTranscript (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) :
    PiecesAtMost (scalarTranscript p w) (attainableTranscripts p).card :=
  (piecesAtMost_scalarEval p w hw).comp (fun z (j : inputGates p) => z j)

/-- **Theorem 4.1 (Piece bound for scalar-direction readouts)**: for any readout of the gate
values, `scalarReadout p w readout` has at most `(attainableTranscripts p).card` pieces on `ℝ`. -/
theorem piecesAtMost_scalarReadout {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) :
    PiecesAtMost (scalarReadout p w readout) (attainableTranscripts p).card :=
  (piecesAtMost_scalarEval p w hw).comp readout

/-- **Theorem 4.1 (Change bound for scalar-direction readouts)**: `scalarReadout p w readout`
changes at most `(attainableTranscripts p).card - 1` times along `ℝ`. -/
theorem changesAtMost_scalarReadout {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) :
    ChangesAtMost (scalarReadout p w readout) ((attainableTranscripts p).card - 1) :=
  (piecesAtMost_scalarReadout p w hw readout).changesAtMost

/-- **Theorem 4.1 (Alternating-run capacity bound)**: if `xs : List (Fin n → Bool)` has
nondecreasing scalar scores along `w` and alternating readout values, then
`xs.length ≤ (attainableTranscripts p).card`. -/
theorem length_le_card_attainableTranscripts_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (weightedSum w)).IsChain (· ≤ ·))
    (halt : (xs.map fun x => readout (p.eval interpretation x)).IsChain (· ≠ ·)) :
    xs.length ≤ (attainableTranscripts p).card := by
  have hpos := card_attainableTranscripts_pos p
  have hmap : (xs.map (weightedSum w)).map (scalarReadout p w readout) =
      xs.map fun x => readout (p.eval interpretation x) := by
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    exact scalarReadout_weightedSum p w hw readout x
  have hlen := (changesAtMost_scalarReadout p w hw readout).length_le_succ_of_isChain
    hmono (hmap.symm ▸ halt)
  rw [List.length_map] at hlen
  omega

/-- **Theorem 4.1 (Input-activity run capacity bound)**: any score-ordered list of inputs with
alternating readout values has length at most `∑ j ∈ range (inputActivity p + 1), q.choose j`. -/
theorem length_le_sum_choose_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (weightedSum w)).IsChain (· ≤ ·))
    (halt : (xs.map fun x => readout (p.eval interpretation x)).IsChain (· ≠ ·)) :
    xs.length ≤ ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  (length_le_card_attainableTranscripts_of_isChain p w hw readout hmono halt).trans
    (card_attainableTranscripts_le_sum_choose p)

/-- **Theorem 4.1 (Gate-activity run capacity bound)**: any score-ordered list of inputs with
alternating readout values has length at most `∑ j ∈ range (gateActivity p + 1), g.choose j`. -/
theorem length_le_sum_choose_gateActivity_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (weightedSum w)).IsChain (· ≤ ·))
    (halt : (xs.map fun x => readout (p.eval interpretation x)).IsChain (· ≠ ·)) :
    xs.length ≤ ∑ j ∈ range (gateActivity p + 1), g.choose j :=
  (length_le_card_attainableTranscripts_of_isChain p w hw readout hmono halt).trans
    (card_attainableTranscripts_le_sum_choose_gateActivity p)

/-! ### Section 4.2: Scalar activity for two-sided rectangle-free functions -/

/-- **Corollary 4.2 (Sharp attainable-transcript capacity bound)**: if a single-direction threshold
program computes a two-sided `K`-rectangle-free Boolean function `f`, then
`2 ^ n < 4 * K ^ 2 * max 1 (4 * ((attainableTranscripts p).card - 1))`. -/
theorem two_pow_lt_mul_max_card_attainableTranscripts_of_direction
    (p : Program signature n g) (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * max 1 (4 * ((attainableTranscripts p).card - 1)) := by
  refine two_pow_lt_of_multilevel w (scalarReadout p w readout)
    (changesAtMost_scalarReadout p w hw readout) (fun x => ?_) hf
  rw [← hreadout x, ← scalarReadout_weightedSum p w hw readout x]

/-- **Corollary 4.2 (Attainable-transcript capacity bound)**: if a single-direction threshold
program computes a two-sided `K`-rectangle-free Boolean function `f`, then
`2 ^ n < 16 * K ^ 2 * (attainableTranscripts p).card`. -/
theorem two_pow_lt_mul_card_attainableTranscripts_of_direction
    (p : Program signature n g) (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * (attainableTranscripts p).card := by
  have h := two_pow_lt_mul_max_card_attainableTranscripts_of_direction p readout w hw hreadout hf
  have hpos := card_attainableTranscripts_pos p
  have hmax : max 1 (4 * ((attainableTranscripts p).card - 1)) ≤
      4 * (attainableTranscripts p).card := by omega
  calc 2 ^ n < 4 * K ^ 2 * max 1 (4 * ((attainableTranscripts p).card - 1)) := h
    _ ≤ 4 * K ^ 2 * (4 * (attainableTranscripts p).card) := Nat.mul_le_mul_left _ hmax
    _ = 16 * K ^ 2 * (attainableTranscripts p).card := by ring

/-- **Corollary 4.2 (Input-activity capacity bound)**: if a single-direction threshold program
computes a two-sided `K`-rectangle-free Boolean function `f`, then
`2 ^ n < 16 * K ^ 2 * ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j`. -/
theorem two_pow_lt_mul_sum_choose_of_direction
    (p : Program signature n g) (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  (two_pow_lt_mul_card_attainableTranscripts_of_direction p readout w hw hreadout hf).trans_le
    (Nat.mul_le_mul_left _ (card_attainableTranscripts_le_sum_choose p))

/-- **Corollary 4.2 (Gate-activity capacity bound)**: if a single-direction threshold program
computes a two-sided `K`-rectangle-free Boolean function `f`, then
`2 ^ n < 16 * K ^ 2 * ∑ j ∈ range (gateActivity p + 1), g.choose j`. -/
theorem two_pow_lt_mul_sum_choose_gateActivity_of_direction
    (p : Program signature n g) (readout : (Fin g → Bool) → Bool) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * ∑ j ∈ range (gateActivity p + 1), g.choose j :=
  (two_pow_lt_mul_card_attainableTranscripts_of_direction p readout w hw hreadout hf).trans_le
    (Nat.mul_le_mul_left _ (card_attainableTranscripts_le_sum_choose_gateActivity p))

/-- Single-output circuit form of `two_pow_lt_mul_sum_choose_of_direction`. -/
theorem circuit_two_pow_lt_mul_sum_choose_of_direction (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (w : Fin n → ℝ)
    (hw : ∀ j : Fin c.size, ∃ a : ℝ, inputWeight c.program j = a • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 *
      ∑ j ∈ range (inputActivity c.program + 1), (inputGates c.program).card.choose j := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_mul_sum_choose_of_direction c.program (fun z => z gate) w hw ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-- Single-output circuit form of `two_pow_lt_mul_sum_choose_gateActivity_of_direction`. -/
theorem circuit_two_pow_lt_mul_sum_choose_gateActivity_of_direction (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) (w : Fin n → ℝ)
    (hw : ∀ j : Fin c.size, ∃ a : ℝ, inputWeight c.program j = a • w)
    {f : Cslib.BooleanFunction n} {K : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 16 * K ^ 2 * ∑ j ∈ range (gateActivity c.program + 1), c.size.choose j := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_mul_sum_choose_gateActivity_of_direction c.program (fun z => z gate) w hw ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

/-! ### Real-score realization of ordered class indices -/

private theorem exists_scalarThreshold (w : Fin n → ℝ)
    (index : (Fin n → Bool) → ℕ)
    (horder : ∀ x y, index x < index y → weightedSum w x < weightedSum w y) (k : ℕ) :
    ∃ θ : ℝ, ∀ x, θ ≤ weightedSum w x ↔ k ≤ index x := by
  classical
  let upper : Finset (Fin n → Bool) := univ.filter fun x => k ≤ index x
  by_cases hupper : upper.Nonempty
  · obtain ⟨y, hy, hmin⟩ := exists_min_image upper (weightedSum w) hupper
    refine ⟨weightedSum w y, fun x => ⟨?_, ?_⟩⟩
    · intro hs
      by_contra hx
      have hxy : index x < index y :=
        lt_of_lt_of_le (Nat.lt_of_not_ge hx) (mem_filter.mp hy).2
      exact (not_lt_of_ge hs) (horder x y hxy)
    · intro hx
      exact hmin x (mem_filter.mpr ⟨mem_univ _, hx⟩)
  · obtain ⟨y, -, hmax⟩ := exists_max_image (univ : Finset (Fin n → Bool))
      (weightedSum w) ⟨fun _ => false, mem_univ _⟩
    refine ⟨weightedSum w y + 1, fun x => ?_⟩
    have hscore : ¬weightedSum w y + 1 ≤ weightedSum w x := by
      have hxmax := hmax x (mem_univ x)
      linarith
    have hindex : ¬k ≤ index x := fun hx =>
      hupper ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
    exact iff_of_false hscore hindex

open scoped Classical in
/-- **Real-score realization of ordered query-activity capacity.** Suppose `index` labels
ordered score classes by natural numbers below `L`: whenever one label is smaller than another,
every score in the first class is strictly below every score in the second. There is a tree of
real comparisons `θ ≤ weightedSum w x`, with exactly `L` structural leaves, depth at most `q`,
and true-answer energy at most `e`, returning `index x` on every input, exactly when
`0 < L ≤ ballSize q e`.

Scores may tie within a class. If every index below `L` occurs, every counted leaf is reachable;
otherwise the exact structural leaf count can include unreachable leaves. No minimality of the
supplied class partition is asserted. This is the real-score realization step in the proof of
Theorem 4.1 of [ThresholdCircuitRepresentations2026], not the native circuit compiler. -/
theorem exists_scalarComparisonTree_iff (w : Fin n → ℝ)
    (index : (Fin n → Bool) → ℕ) (q e L : ℕ)
    (hbound : ∀ x, index x < L)
    (horder : ∀ x y, index x < index y → weightedSum w x < weightedSum w y) :
    (∃ t : DecisionTree ℝ ℕ, t.leafCount = L ∧ t.depth ≤ q ∧ t.energy ≤ e ∧
      ∀ x, t.eval (fun θ => decide (θ ≤ weightedSum w x)) = index x) ↔
      0 < L ∧ L ≤ ballSize q e := by
  classical
  constructor
  · rintro ⟨t, hcount, hdepth, henergy, _⟩
    constructor
    · simpa only [hcount] using t.leafCount_pos
    · simpa only [hcount, ballSize] using
        t.leafCount_le_sum_choose_of_energy_le henergy hdepth
  · intro hcap
    obtain ⟨t, hcount, hdepth, henergy, heval⟩ :=
      (DecisionTree.exists_orderedComparisonTree_iff q e L 0).mpr hcap
    choose θ hθ using fun k => exists_scalarThreshold w index horder k
    refine ⟨t.mapQueries θ, ?_, ?_, ?_, ?_⟩
    · simpa only [DecisionTree.leafCount_mapQueries] using hcount
    · simpa only [DecisionTree.depth_mapQueries] using hdepth
    · simpa only [DecisionTree.energy_mapQueries] using henergy
    · intro x
      rw [DecisionTree.eval_mapQueries]
      have horacle : (fun s => decide (s ≤ weightedSum w x)) ∘ θ =
          fun k => decide (k ≤ index x) := by
        funext k
        simp only [Function.comp_apply, hθ]
      rw [horacle]
      simpa only [zero_add] using heval (index x) (hbound x)

end Cslib.Circuits.Boolean.WeightedThreshold
