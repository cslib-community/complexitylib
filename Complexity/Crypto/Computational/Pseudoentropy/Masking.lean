/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Entropy
public import Complexity.Crypto.Computational.Prediction
public import Complexity.Crypto.Computational.Hybrid.Sequence
public import Complexity.Crypto.Computational.Pseudoentropy.Boosting.Sampling
import Complexity.Probability.PMF.Event
import Complexity.Languages.Probabilistic.Notation
import Complexity.Tactic.PPT

/-!
# Fresh masks for a pseudoentropy pair

A mask coin chooses whether to replace a label by a fresh fair bit. Conditional on any
deterministic observation, the resulting label has at least as much entropy as the average
replacement probability. This remains true when the mask probability depends on the original
input and label.

Every occurrence draws a fresh mask, including repeated inputs. The executable boosting weights
provide such coins exactly, so their density is a lower bound on the masked label's conditional
entropy. The sampler and its strict PPT certificate use the usual programming combinators.

The distinguishing-to-prediction reduction then samples a random coordinate and supplies a trial
bit at that coordinate. Its weighted prediction bias is exactly the complete sequence gap divided
by the dyadic coordinate range. The target observation is its only target-dependent input; labels
and masks are computed only on fresh surrounding samples.

## Main definitions

* `Cslib.Crypto.Pseudoentropy.maskBit`, `.maskedSample`: replace labels using fresh mask coins.
* `Cslib.Crypto.Pseudoentropy.maskedSequencePredictor`: prediction from a sequence distinguisher.

## Main results

* `Cslib.Crypto.Pseudoentropy.maskedSample_entropy_ge`: mask density lower-bounds label entropy.
* `Cslib.Crypto.Pseudoentropy.maskedSequence_prediction_gap`: the exact weighted prediction gap.
* `Cslib.Crypto.Pseudoentropy.isPPTOn_maskedSequencePredictor`: the complete strict PPT reduction.

## References

* [Holenstein, Section 5, Games 3–5][Holenstein2006]. The fresh soft-mask coin replaces the set
  indicator in that experiment; [Holenstein, Section 2.1.1][Holenstein2005] discusses measures.

Adapted from Crypto/Computational/Pseudoentropy/Masking.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. These are ingredients of the subsequent extraction
and learning arguments, not a complete pseudorandomness theorem.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Probability.PMF BitString Turing.MultiTapeTM

/-- Replace a label by a fresh fair bit when the supplied mask accepts. -/
noncomputable def maskBit (mask : ProbComp Bool) (truth : Bool) : ProbComp Bool := do
  let replace ← mask
  if replace then ProbComp.uniform Bool else pure truth

/-- Sample an observation and a label with a fresh input-dependent randomization mask. -/
noncomputable def maskedSample {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) : ProbComp (β × Bool) := do
  let x ← source
  (observe x, ·) <$> maskBit (mask x) (truth x)

/-- The mask's law is an ordinary mixture of a fair bit and the original label. -/
theorem eval_maskBit (mask : ProbComp Bool) (truth : Bool) :
    ProbComp.eval (maskBit mask truth) = (ProbComp.eval mask).bind
      (fun replace => if replace then PMF.uniformOfFintype Bool else PMF.pure truth) := by
  unfold maskBit
  rw [ProbComp.eval_bind]
  congr 1
  funext replace
  cases replace <;> simp [ProbComp.eval_uniform]

/-- The original label remains with probability `1 - maskProbability / 2`. -/
theorem eval_maskBit_apply (mask : ProbComp Bool) (truth bit : Bool) :
    (ProbComp.eval (maskBit mask truth) bit).toReal =
      if bit = truth then 1 - Pr[mask] / 2 else Pr[mask] / 2 := by
  have hmass := toReal_true_add_toReal_false (ProbComp.eval mask)
  rw [eval_maskBit, bind_apply_toReal]
  cases truth <;> cases bit <;>
    norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply] <;> linarith

/-- A fresh replacement contributes one bit of conditional randomness whenever the mask accepts. -/
theorem entropy_maskBit_ge (mask : ProbComp Bool) (truth : Bool) :
    Pr[mask] ≤ entropy (ProbComp.eval (maskBit mask truth)) := by
  rw [eval_maskBit]
  have h := sum_mul_entropy_le_entropy_bind (ProbComp.eval mask)
    (fun replace => if replace then PMF.uniformOfFintype Bool else PMF.pure truth)
  simpa using h

/-- The masked pair reveals the original observation and averages the pointwise masked laws. -/
theorem eval_maskedSample {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) :
    ProbComp.eval (maskedSample source observe truth mask) =
      (ProbComp.eval source).bind
        (fun x => (ProbComp.eval (maskBit (mask x) (truth x))).map (observe x, ·)) := by
  simp only [maskedSample, ProbComp.eval_bind, ProbComp.eval_map]

/-- Hiding all but a deterministic observation leaves at least the average mask probability
in conditional label entropy. In particular, mask probabilities may depend on hidden labels. -/
theorem maskedSample_entropy_ge {α β : Type} [Fintype α] [Finite β] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) :
    (∑ x, (ProbComp.eval source x).toReal * Pr[mask x]) ≤
      conditionalEntropy (ProbComp.eval (maskedSample source observe truth mask)) := by
  rw [eval_maskedSample]
  exact (Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (entropy_maskBit_ge (mask x) (truth x)) ENNReal.toReal_nonneg)).trans
      (conditionalEntropy_observe_ge (ProbComp.eval source)
        (fun x => ProbComp.eval (maskBit (mask x) (truth x))) observe)

/-- The entropy available from executable boosting masks is at least their exact soft density. -/
theorem maskedSample_weight_entropy_ge {α β : Type} [Fintype α] [Finite β]
    (source : ProbComp α) (observe : α → β) (truth : α → Bool) (votes : α → List Bool)
    (bound numerator threshold : ℕ) :
    Boosting.density (ProbComp.eval source) (numerator / dyadicSize bound)
      (fun x => listVoteMargin (votes x) (truth x) - threshold) ≤
        conditionalEntropy (ProbComp.eval (maskedSample source observe truth (fun x =>
          Boosting.sampleWeight bound numerator threshold (votes x) (truth x)))) := by
  simpa only [Boosting.eval_sampleWeight_true, Boosting.density] using
    maskedSample_entropy_ge source observe truth
      (fun x => Boosting.sampleWeight bound numerator threshold (votes x) (truth x))

/-- Distinguishing a real label from its masked version gives prediction bias weighted by the
mask probability. The predictor itself receives only the test, not the mask or hidden label. -/
theorem maskBit_prediction_gap (test : Bool → ProbComp Bool) (mask : ProbComp Bool)
    (truth : Bool) :
    Pr[test truth] - Pr[maskBit mask truth >>= test] =
      Pr[mask] *
        (Pr[(fun guess => guess == truth) <$> bitPredictor test] - 1 / 2) := by
  rw [ProbComp.probability_bind, bitPredictor_bias]
  simp only [Fintype.sum_bool, eval_maskBit_apply]
  cases truth <;> norm_num <;> ring

/-- The exact masked distinguishing gap is the source-averaged weighted prediction bias.
Only the observation is passed to the predictor; the mask may depend on the entire source. -/
theorem maskedSample_prediction_gap {α β : Type} [Fintype α] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool)
    (test : β → Bool → ProbComp Bool) :
    Pr[source >>= fun x => test (observe x) (truth x)] -
        Pr[maskedSample source observe truth mask >>= fun pair => test pair.1 pair.2] =
      ∑ x, (ProbComp.eval source x).toReal * Pr[mask x] *
        (Pr[(fun guess => guess == truth x) <$> bitPredictor (test (observe x))] -
          1 / 2) := by
  simp only [maskedSample, bind_assoc, bind_map_left]
  rw [ProbComp.probability_bind, ProbComp.probability_bind, ← Finset.sum_sub_distrib]
  simp only [← mul_sub, maskBit_prediction_gap, mul_assoc]

/-- A certified mask and an efficiently supplied label give a strict PPT randomized label. -/
@[program_certificate]
theorem isPPTOn_maskBit {α : Type} {input : α ↪ List Bool} {mask : α → ProbComp Bool}
    {truth : α → Bool} (hmask : IsPPTOn input encBool mask)
    (htruth : ComputableInPolyTime truth input encBool) :
    IsPPTOn input encBool (fun a => maskBit (mask a) (truth a)) := by
  unfold maskBit
  ppt

/-- Masked sampling composes a certified source, observation, label, and mask. All callbacks may
capture the original input, and all intermediate encodings are charged. -/
@[program_certificate]
theorem isPPTOn_maskedSample {α β γ : Type} {input : α ↪ List Bool}
    {sample : β ↪ List Bool} {output : γ ↪ List Bool} {source : α → ProbComp β}
    {observe : α → β → γ} {truth : α → β → Bool} {mask : α → β → ProbComp Bool}
    (hsource : IsPPTOn input sample source)
    (hobserve : ComputableInPolyTime (fun pair : α × β => observe pair.1 pair.2)
      (encPair input sample) output)
    (htruth : ComputableInPolyTime (fun pair : α × β => truth pair.1 pair.2)
      (encPair input sample) encBool)
    (hmask : IsPPTOn (encPair input sample) encBool (fun pair => mask pair.1 pair.2)) :
    IsPPTOn input (encPair output encBool)
      (fun a => maskedSample (source a) (observe a) (truth a) (mask a)) := by
  unfold maskedSample
  ppt

/-- Predict from one public observation by simulating a random-coordinate masked hybrid.
Hidden labels and masks are computed only on independently generated surrounding samples. -/
noncomputable def maskedSequencePredictor {α β : Type} (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) (count : ℕ)
    (test : List (β × Bool) → ProbComp Bool) (observation : β) : ProbComp Bool :=
  bitPredictor (fun trial => sequenceTest (maskedSample source observe truth mask)
    ((fun x => (observe x, truth x)) <$> source) count test (observation, trial))

/-- A sequence distinguisher gives one predictor whose mask-weighted bias equals the complete
distinguishing gap divided by the dyadic coordinate range. This allows arbitrary finite sources,
arbitrary observations, hidden-label-dependent masks, and zero repetitions. -/
theorem maskedSequence_prediction_gap {α β : Type} [Fintype α] (source : ProbComp α)
    (observe : α → β) (truth : α → Bool) (mask : α → ProbComp Bool) (count : ℕ)
    (test : List (β × Bool) → ProbComp Bool) :
    Pr[OracleComp.replicate count ((fun x => (observe x, truth x)) <$> source)
        >>= test] -
      Pr[OracleComp.replicate count (maskedSample source observe truth mask)
        >>= test] =
      (dyadicSize count : ℝ) * ∑ x,
        (ProbComp.eval source x).toReal * Pr[mask x] *
          (Pr[(fun guess => guess == truth x) <$>
            maskedSequencePredictor source observe truth mask count test (observe x)] - 1 / 2) := by
  have hgap := sequenceTest_gap (maskedSample source observe truth mask)
    ((fun x => (observe x, truth x)) <$> source) count test
  simp only [Game.coe_succProbability] at hgap
  rw [hgap]
  unfold maskedSequencePredictor
  congr 1
  simpa only [bind_map_left] using maskedSample_prediction_gap source observe truth mask
    (fun observation trial => sequenceTest (maskedSample source observe truth mask)
      ((fun x => (observe x, truth x)) <$> source) count test (observation, trial))

/-- The complete masked-coordinate prediction reduction is strict PPT whenever its source,
observation, labels, masks, test, and repetition count have certificates. -/
@[program_certificate hsource]
theorem isPPTOn_maskedSequencePredictor {Param α β : Type} {input : Param ↪ List Bool}
    {sample : α ↪ List Bool} {output : β ↪ List Bool} {source : Param → ProbComp α}
    {observe : Param → α → β} {truth : Param → α → Bool} {mask : Param → α → ProbComp Bool}
    {count : Param → ℕ} {test : Param → List (β × Bool) → ProbComp Bool}
    {observation : Param → β}
    (hsource : IsPPTOn input sample source)
    (hobserve : ComputableInPolyTime (fun pair : Param × α => observe pair.1 pair.2)
      (encPair input sample) output)
    (htruth : ComputableInPolyTime (fun pair : Param × α => truth pair.1 pair.2)
      (encPair input sample) encBool)
    (hmask : IsPPTOn (encPair input sample) encBool (fun pair => mask pair.1 pair.2))
    (hcount : ComputableInPolyTime count input encUnary)
    (htest : IsPPTOn (encPair input (encList (encPair output encBool))) encBool
      (fun pair => test pair.1 pair.2))
    (hobservation : ComputableInPolyTime observation input output) :
    IsPPTOn input encBool (fun a => maskedSequencePredictor (source a) (observe a)
      (truth a) (mask a) (count a) (test a) (observation a)) := by
  have hmasked := isPPTOn_maskedSample hsource hobserve htruth hmask
  have horiginal : IsPPTOn input (encPair output encBool)
      (fun a => (fun x => (observe a x, truth a x)) <$> source a) := by ppt
  unfold maskedSequencePredictor
  ppt

end Cslib.Crypto.Pseudoentropy
