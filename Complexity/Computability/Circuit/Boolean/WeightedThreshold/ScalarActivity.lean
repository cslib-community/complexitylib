/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Activity
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit
public import Complexity.Foundations.Data.BitString.CoverCoding

/-!
# Scalar query-activity run capacity

When every gate of a weighted threshold program `p` reads the original inputs along a single
direction `w : Fin n → ℝ` (`∀ j, ∃ c : ℝ, inputWeight p j = c • w`), fixing the restricted
input-reading transcript `transcript p x` turns every gate condition into a half-line condition on
the scalar score `scalarScore w x = ∑ i, w i * (x i).toNat`. Consequently, the fibers of
`transcript p` (and of the full gate evaluation `p.eval interpretation`) are order-convex along
`scalarScore w` (`eval_eq_of_scalarScore_between`, `transcript_eq_of_scalarScore_between`).

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

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.scalarScore`: directional projection
  `∑ i, w i * (x i).toNat`.
* `Cslib.Circuits.Boolean.WeightedThreshold.leInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarRep`: inputs with scalar score at most `t` and a
  canonical representative input for `t`.
* `Cslib.Circuits.Boolean.WeightedThreshold.scalarEval`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarTranscript`,
  `Cslib.Circuits.Boolean.WeightedThreshold.scalarReadout`: extension of gate evaluation,
  input-reading transcripts, and readouts to `ℝ` along `scalarScore w`.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_scalarScore_between`,
  `Cslib.Circuits.Boolean.WeightedThreshold.transcript_eq_of_scalarScore_between`: order-convexity
  of gate evaluations and transcripts along `scalarScore w`.
* `Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarTranscript`,
  `Cslib.Circuits.Boolean.WeightedThreshold.piecesAtMost_scalarReadout`,
  `Cslib.Circuits.Boolean.WeightedThreshold.changesAtMost_scalarReadout`: piece and change bounds
  in terms of `(attainableTranscripts p).card` (Theorem 4.1).
* `Cslib.Circuits.Boolean.WeightedThreshold.length_le_card_attainableTranscripts_of_isChain`,
  `Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_of_isChain`,
  `Cslib.Circuits.Boolean.WeightedThreshold.length_le_sum_choose_gateActivity_of_isChain`:
  alternating-run capacity bounds along `scalarScore w`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_card_attainableTranscripts_of_direction`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_of_direction`,
  `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_mul_sum_choose_gateActivity_of_direction`:
  rectangle-free scalar activity bounds (Corollary 4.2).

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ}

/-! ### Section 4.1: Order-convexity of scalar-direction transcripts and run capacity -/

/-- The scalar score `∑ i, w i * (x i).toNat` of a Boolean input `x` along direction `w`. -/
def scalarScore (w : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, w i * (x i).toNat

private theorem sum_inputWeight_eq_mul_scalarScore {p : Program signature n g} {w : Fin n → ℝ}
    {j : Fin g} {c : ℝ} (hc : inputWeight p j = c • w) (x : Fin n → Bool) :
    (∑ i : Fin n, inputWeight p j i * (x i).toNat) = c * scalarScore w x := by
  have hfun := fun i => congrFun hc i
  simp only [Pi.smul_apply, smul_eq_mul] at hfun
  simp only [scalarScore, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hfun i, mul_assoc]

/-- **Order-convexity of gate evaluations along a scalar direction**: if every gate's input weight
vector is a multiple of `w`, `scalarScore w x₁ ≤ scalarScore w x₂ ≤ scalarScore w x₃`, and
`transcript p x₁ = transcript p x₃`, then `p.eval interpretation x₂ = p.eval interpretation x₁`. -/
theorem eval_eq_of_scalarScore_between (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ x₃ : Fin n → Bool}
    (h₁₂ : scalarScore w x₁ ≤ scalarScore w x₂)
    (h₂₃ : scalarScore w x₂ ≤ scalarScore w x₃)
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
    rw [sum_inputWeight_eq_mul_scalarScore hc] at hgate₁ hgate₂ hgate₃
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
    · have hle₁₂ : c * scalarScore w x₁ ≤ c * scalarScore w x₂ :=
        mul_le_mul_of_nonneg_left h₁₂ hc0
      have hle₂₃ : c * scalarScore w x₂ ≤ c * scalarScore w x₃ :=
        mul_le_mul_of_nonneg_left h₂₃ hc0
      exact ⟨fun h₂ => hj₁₃.mpr (by linarith), fun h₁ => by linarith⟩
    · have hle₂₁ : c * scalarScore w x₂ ≤ c * scalarScore w x₁ :=
        mul_le_mul_of_nonpos_left h₁₂ hc0
      have hle₃₂ : c * scalarScore w x₃ ≤ c * scalarScore w x₂ :=
        mul_le_mul_of_nonpos_left h₂₃ hc0
      exact ⟨fun h₂ => by linarith, fun h₁ => by linarith [hj₁₃.mp h₁]⟩

/-- **Order-convexity of input-reading transcripts along a scalar direction**. -/
theorem transcript_eq_of_scalarScore_between (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ x₃ : Fin n → Bool}
    (h₁₂ : scalarScore w x₁ ≤ scalarScore w x₂)
    (h₂₃ : scalarScore w x₂ ≤ scalarScore w x₃)
    (htr : transcript p x₁ = transcript p x₃) :
    transcript p x₂ = transcript p x₁ := by
  funext j
  exact congrFun (eval_eq_of_scalarScore_between p w hw h₁₂ h₂₃ htr) j.val

/-- Inputs with equal scalar score have identical gate evaluations. -/
theorem eval_eq_of_scalarScore_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ : Fin n → Bool} (h : scalarScore w x₁ = scalarScore w x₂) :
    p.eval interpretation x₁ = p.eval interpretation x₂ := by
  funext j
  induction j using Fin.strong_induction_on with
  | h j ih =>
    obtain ⟨c, hc⟩ := hw j
    rw [eval_gate_eq, eval_gate_eq, sum_inputWeight_eq_mul_scalarScore hc,
      sum_inputWeight_eq_mul_scalarScore hc, h]
    congr 3
    refine sum_congr rfl fun k _ => ?_
    by_cases hkj : k < j
    · rw [ih k hkj]
    · rw [gateWeight_eq_zero_of_le p j k (le_of_not_gt hkj)]
      ring

/-- Inputs with equal scalar score have identical input-reading transcripts. -/
private theorem transcript_eq_of_scalarScore_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    {x₁ x₂ : Fin n → Bool} (h : scalarScore w x₁ = scalarScore w x₂) :
    transcript p x₁ = transcript p x₂ := by
  funext j
  exact congrFun (eval_eq_of_scalarScore_eq p w hw h) j.val

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
  univ.filter fun x => scalarScore w x ≤ t

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
`scalarScore w` when `leInputs w t` is nonempty, and a global minimizer of `scalarScore w`
otherwise. -/
noncomputable def scalarRep (w : Fin n → ℝ) (t : ℝ) : Fin n → Bool :=
  if h : (leInputs w t).Nonempty then
    (exists_max_image (leInputs w t) (scalarScore w) h).choose
  else
    (exists_min_image (univ : Finset (Fin n → Bool)) (scalarScore w)
      ⟨fun _ => false, mem_univ _⟩).choose

/-- One-dimensional extension of gate evaluation along `scalarScore w`. -/
noncomputable def scalarEval (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    Fin g → Bool :=
  p.eval interpretation (scalarRep w t)

/-- One-dimensional extension of the input-reading transcript along `scalarScore w`. -/
noncomputable def scalarTranscript (p : Program signature n g) (w : Fin n → ℝ) (t : ℝ) :
    inputGates p → Bool :=
  transcript p (scalarRep w t)

/-- One-dimensional extension of a gate readout along `scalarScore w`. -/
noncomputable def scalarReadout {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (readout : (Fin g → Bool) → β) (t : ℝ) : β :=
  readout (scalarEval p w t)

private theorem scalarRep_mem_of_nonempty {w : Fin n → ℝ} {t : ℝ}
    (h : (leInputs w t).Nonempty) :
    scalarRep w t ∈ leInputs w t := by
  simp only [scalarRep, h, ↓reduceDIte]
  exact (exists_max_image (leInputs w t) (scalarScore w) h).choose_spec.1

private theorem le_scalarScore_scalarRep_of_mem {w : Fin n → ℝ} {t : ℝ} {x : Fin n → Bool}
    (hx : x ∈ leInputs w t) :
    scalarScore w x ≤ scalarScore w (scalarRep w t) := by
  have h : (leInputs w t).Nonempty := ⟨x, hx⟩
  simp only [scalarRep, h, ↓reduceDIte]
  exact (exists_max_image (leInputs w t) (scalarScore w) h).choose_spec.2 x hx

private theorem scalarScore_scalarRep_eq (w : Fin n → ℝ) (x : Fin n → Bool) :
    scalarScore w (scalarRep w (scalarScore w x)) = scalarScore w x := by
  have hx : x ∈ leInputs w (scalarScore w x) := by simp [leInputs]
  have hrep := scalarRep_mem_of_nonempty ⟨x, hx⟩
  simp only [leInputs, mem_filter, mem_univ, true_and] at hrep
  exact le_antisymm hrep (le_scalarScore_scalarRep_of_mem hx)

/-- Evaluating `scalarEval p w` at `scalarScore w x` recovers `p.eval interpretation x`. -/
@[simp]
theorem scalarEval_scalarScore (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) (x : Fin n → Bool) :
    scalarEval p w (scalarScore w x) = p.eval interpretation x :=
  eval_eq_of_scalarScore_eq p w hw (scalarScore_scalarRep_eq w x)

/-- Evaluating `scalarTranscript p w` at `scalarScore w x` recovers `transcript p x`. -/
@[simp]
theorem scalarTranscript_scalarScore (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) (x : Fin n → Bool) :
    scalarTranscript p w (scalarScore w x) = transcript p x :=
  transcript_eq_of_scalarScore_eq p w hw (scalarScore_scalarRep_eq w x)

/-- Evaluating `scalarReadout p w readout` at `scalarScore w x` recovers
`readout (p.eval interpretation x)`. -/
@[simp]
theorem scalarReadout_scalarScore {β : Type*} (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) (x : Fin n → Bool) :
    scalarReadout p w readout (scalarScore w x) = readout (p.eval interpretation x) := by
  simp [scalarReadout, scalarEval_scalarScore p w hw x]

private theorem scalarEval_eq_of_le_of_rank_eq (p : Program signature n g) (w : Fin n → ℝ)
    (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w) {t t' : ℝ} (htt' : t ≤ t')
    (hcard : (leTranscripts p w t).card - 1 = (leTranscripts p w t').card - 1) :
    scalarEval p w t = scalarEval p w t' := by
  classical
  let xmin := (exists_min_image (univ : Finset (Fin n → Bool)) (scalarScore w)
    ⟨fun _ => false, mem_univ _⟩).choose
  have hxmin : ∀ x : Fin n → Bool, scalarScore w xmin ≤ scalarScore w x := fun x =>
    (exists_min_image (univ : Finset (Fin n → Bool)) (scalarScore w)
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
    have h₁₂ : scalarScore w x₁ ≤ scalarScore w (scalarRep w t) :=
      le_scalarScore_scalarRep_of_mem hx₁
    have h₂₃ : scalarScore w (scalarRep w t) ≤ scalarScore w (scalarRep w t') :=
      le_scalarScore_scalarRep_of_mem (leInputs_subset htt' hrep_t)
    unfold scalarEval
    exact (eval_eq_of_scalarScore_between p w hw h₁₂ h₂₃ htr₁).trans
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

private theorem isChain_le_getElem {α : Type*} [Preorder α] {ts : List α}
    (hmono : ts.IsChain (· ≤ ·)) {i j : ℕ} (hi : i < ts.length) (hj : j < ts.length)
    (hij : i ≤ j) :
    ts[i] ≤ ts[j] := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · have hj' : j < ts.length := by omega
      exact (ih hj' (by omega)).trans (List.isChain_iff_getElem.mp hmono j hj)

/-- Any ordered list `ts` along which `Φ` alternates between consecutive elements has length at
most `T + 1` whenever `ChangesAtMost Φ T`. -/
private theorem length_le_succ_of_changesAtMost_of_isChain {α β : Type*} [Preorder α] {Φ : α → β}
    {T : ℕ}
    (hΦ : ChangesAtMost Φ T) {ts : List α} (hmono : ts.IsChain (· ≤ ·))
    (halt : (ts.map Φ).IsChain (· ≠ ·)) :
    ts.length ≤ T + 1 := by
  rcases Nat.eq_zero_or_pos ts.length with h0 | hpos
  · omega
  · let z : ℕ → α := fun i => ts[min i (ts.length - 1)]'(by omega)
    have hz : Monotone z := fun i j hij =>
      isChain_le_getElem hmono (by omega) (by omega) (min_le_min_right _ hij)
    have hchg : ∀ i ∈ range (ts.length - 1), Φ (z i) ≠ Φ (z (i + 1)) := by
      intro i hi
      have hi' : i + 1 < ts.length := by
        rw [mem_range] at hi
        omega
      have h1 : min i (ts.length - 1) = i := by omega
      have h2 : min (i + 1) (ts.length - 1) = i + 1 := by omega
      have hne := List.isChain_iff_getElem.mp halt i (by simpa using hi')
      simpa [z, h1, h2] using hne
    have hcard := hΦ z hz (range (ts.length - 1)) hchg
    rw [card_range] at hcard
    omega

/-- **Theorem 4.1 (Alternating-run capacity bound)**: if `xs : List (Fin n → Bool)` has
nondecreasing scalar scores along `w` and alternating readout values, then
`xs.length ≤ (attainableTranscripts p).card`. -/
theorem length_le_card_attainableTranscripts_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (scalarScore w)).IsChain (· ≤ ·))
    (halt : (xs.map fun x => readout (p.eval interpretation x)).IsChain (· ≠ ·)) :
    xs.length ≤ (attainableTranscripts p).card := by
  have hpos := card_attainableTranscripts_pos p
  have hmap : (xs.map (scalarScore w)).map (scalarReadout p w readout) =
      xs.map fun x => readout (p.eval interpretation x) := by
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    exact scalarReadout_scalarScore p w hw readout x
  have hlen := length_le_succ_of_changesAtMost_of_isChain
    (changesAtMost_scalarReadout p w hw readout) hmono (hmap.symm ▸ halt)
  rw [List.length_map] at hlen
  omega

/-- **Theorem 4.1 (Input-activity run capacity bound)**: any score-ordered list of inputs with
alternating readout values has length at most `∑ j ∈ range (inputActivity p + 1), q.choose j`. -/
theorem length_le_sum_choose_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (scalarScore w)).IsChain (· ≤ ·))
    (halt : (xs.map fun x => readout (p.eval interpretation x)).IsChain (· ≠ ·)) :
    xs.length ≤ ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  (length_le_card_attainableTranscripts_of_isChain p w hw readout hmono halt).trans
    (card_attainableTranscripts_le_sum_choose p)

/-- **Theorem 4.1 (Gate-activity run capacity bound)**: any score-ordered list of inputs with
alternating readout values has length at most `∑ j ∈ range (gateActivity p + 1), g.choose j`. -/
theorem length_le_sum_choose_gateActivity_of_isChain {β : Type*} (p : Program signature n g)
    (w : Fin n → ℝ) (hw : ∀ j : Fin g, ∃ c : ℝ, inputWeight p j = c • w)
    (readout : (Fin g → Bool) → β) {xs : List (Fin n → Bool)}
    (hmono : (xs.map (scalarScore w)).IsChain (· ≤ ·))
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
  rw [← hreadout x, ← scalarReadout_scalarScore p w hw readout x, scalarScore]

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

end Cslib.Circuits.Boolean.WeightedThreshold
