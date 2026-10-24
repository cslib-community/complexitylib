/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold

/-!
# Activity and attainable threshold transcripts

The number of attainable input-reading transcripts is bounded by a Hamming ball at the
worst-case input-reading activity, or at the worst-case Hamming distance from any fixed baseline
activation pattern. Projecting the full gate valuations gives a second bound using the total gate
count and maximum activity (or distance from a baseline) across all gates. Both bounds use the
same finite-image counting lemma.

The resulting exact binomial sum is an upper bound on the number of patterns. Lower bounds for
a computed function also require a representation theorem, such as the comparison-tree compiler.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.attainableTranscripts`: the realized transcripts.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivity`: maximum input-reading activity.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateActivity`: maximum activity across all gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputActivityFrom`: maximum Hamming distance of the
  restricted transcript from a fixed baseline pattern.
* `Cslib.Circuits.Boolean.WeightedThreshold.gateActivityFrom`: maximum Hamming distance of the
  full gate valuation from a fixed baseline pattern.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose`: the exact
  Hamming-ball bound for attainable patterns.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_attainableTranscripts_le_sum_choose_gateActivity`:
  the bound using activity across all gates.
* `card_attainableTranscripts_le_sum_choose_inputActivityFrom`: the shifted-baseline Hamming-ball
  bound on input-reading gates.
* `card_attainableTranscripts_le_sum_choose_gateActivityFrom`: the shifted-baseline Hamming-ball
  bound across all gates.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Theorem 3.2 and Section 3.1]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset BitString

variable {n g : ℕ}

/-- The restricted activation transcripts realized by Boolean inputs. -/
noncomputable def attainableTranscripts (p : Program signature n g) :
    Finset (inputGates p → Bool) :=
  univ.image (transcript p)

/-- The maximum number of active input-reading gates on one input. -/
noncomputable def inputActivity (p : Program signature n g) : ℕ :=
  univ.sup fun x => weight (transcript p x)

/-- The maximum number of active gates on one input, including gates without direct inputs. -/
noncomputable def gateActivity (p : Program signature n g) : ℕ :=
  univ.sup fun x => weight (p.eval interpretation x)

/-- The maximum Hamming distance of the restricted activation transcript from a fixed baseline
pattern `v`. -/
noncomputable def inputActivityFrom (p : Program signature n g)
    (v : inputGates p → Bool) : ℕ :=
  univ.sup fun x => hammingDist (transcript p x) v

/-- The maximum Hamming distance of the full gate valuation from a fixed baseline pattern `v`. -/
noncomputable def gateActivityFrom (p : Program signature n g) (v : Fin g → Bool) : ℕ :=
  univ.sup fun x => hammingDist (p.eval interpretation x) v

@[simp]
theorem mem_attainableTranscripts (p : Program signature n g) (z : inputGates p → Bool) :
    z ∈ attainableTranscripts p ↔ ∃ x, transcript p x = z := by
  classical
  simp [attainableTranscripts]

/-- An activity bound is exactly a uniform bound on the weight of the restricted transcripts. -/
theorem inputActivity_le_iff (p : Program signature n g) {e : ℕ} :
    inputActivity p ≤ e ↔ ∀ x, weight (transcript p x) ≤ e := by
  simp [inputActivity, Finset.sup_le_iff]

/-- A bound on total activity is exactly a uniform bound on complete gate valuations. -/
theorem gateActivity_le_iff (p : Program signature n g) {e : ℕ} :
    gateActivity p ≤ e ↔ ∀ x, weight (p.eval interpretation x) ≤ e := by
  simp [gateActivity, Finset.sup_le_iff]

/-- A shifted-baseline input-reading activity bound is a uniform Hamming-distance bound on
restricted transcripts. -/
theorem inputActivityFrom_le_iff (p : Program signature n g) (v : inputGates p → Bool) {e : ℕ} :
    inputActivityFrom p v ≤ e ↔ ∀ x, hammingDist (transcript p x) v ≤ e := by
  simp [inputActivityFrom, Finset.sup_le_iff]

/-- A shifted-baseline total activity bound is a uniform Hamming-distance bound on complete gate
valuations. -/
theorem gateActivityFrom_le_iff (p : Program signature n g) (v : Fin g → Bool) {e : ℕ} :
    gateActivityFrom p v ≤ e ↔ ∀ x, hammingDist (p.eval interpretation x) v ≤ e := by
  simp [gateActivityFrom, Finset.sup_le_iff]

/-- At the all-false baseline, shifted-baseline input-reading activity equals `inputActivity`. -/
@[simp]
theorem inputActivityFrom_zero (p : Program signature n g) :
    inputActivityFrom p 0 = inputActivity p := by
  simp only [inputActivityFrom, inputActivity, hammingDist_eq_weight_add, add_zero]

/-- At the all-false baseline, shifted-baseline total activity equals `gateActivity`. -/
@[simp]
theorem gateActivityFrom_zero (p : Program signature n g) :
    gateActivityFrom p 0 = gateActivity p := by
  simp only [gateActivityFrom, gateActivity, hammingDist_eq_weight_add, add_zero]

/-- Total gate activity never exceeds the number of gates. -/
theorem gateActivity_le (p : Program signature n g) : gateActivity p ≤ g := by
  apply (gateActivity_le_iff p).mpr
  intro x
  exact weight_le_length (p.eval interpretation x)

/-- Restricting to the input-reading gates cannot increase activity. -/
theorem inputActivity_le_gateActivity (p : Program signature n g) :
    inputActivity p ≤ gateActivity p := by
  apply (inputActivity_le_iff p).mpr
  intro x
  exact (weight_comp_le (p.eval interpretation x)
    (f := fun i : inputGates p => i.val) Subtype.val_injective).trans
      ((gateActivity_le_iff p).mp le_rfl x)

/-- Input-reading activity never exceeds the number of input-reading gates. -/
theorem inputActivity_le_card (p : Program signature n g) :
    inputActivity p ≤ (inputGates p).card := by
  apply (inputActivity_le_iff p).mpr
  intro x
  simpa only [Fintype.card_coe] using weight_le (transcript p x)

/-- Every realized transcript lies in the Hamming ball specified by any uniform activity bound.
The bound also permits a radius larger than the number of input-reading gates. -/
theorem card_attainableTranscripts_le_sum_choose_of_le (p : Program signature n g) {e : ℕ}
    (he : inputActivity p ≤ e) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (e + 1), (inputGates p).card.choose j := by
  classical
  simpa only [attainableTranscripts, Fintype.card_coe] using
    card_image_le_sum_choose univ (transcript p)
    (fun x _ => (inputActivity_le_iff p).mp he x)

/-- Attainable patterns are bounded by the exact binomial sum at worst-case activity. -/
theorem card_attainableTranscripts_le_sum_choose (p : Program signature n g) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (inputActivity p + 1), (inputGates p).card.choose j :=
  card_attainableTranscripts_le_sum_choose_of_le p le_rfl

/-- Projecting full gate valuations cannot create additional restricted transcripts, so total
gate activity gives a Hamming-ball bound using the total number of gates. -/
theorem card_attainableTranscripts_le_sum_choose_gateActivity (p : Program signature n g) :
    (attainableTranscripts p).card ≤ ∑ j ∈ range (gateActivity p + 1), g.choose j := by
  classical
  calc
    _ = ((univ.image (p.eval interpretation)).image
        fun z => fun i : inputGates p => z i).card := by
      simp only [attainableTranscripts, image_image]
      rfl
    _ ≤ (univ.image (p.eval interpretation)).card := card_image_le
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using card_image_le_sum_choose univ
        (p.eval interpretation) (fun x _ => (gateActivity_le_iff p).mp le_rfl x)

/-- Every realized transcript lies in the Hamming ball of radius `e` around any fixed baseline `v`
whenever `inputActivityFrom p v ≤ e`. -/
private theorem card_attainableTranscripts_le_sum_choose_of_inputActivityFrom_le
    (p : Program signature n g) (v : inputGates p → Bool) {e : ℕ}
    (he : inputActivityFrom p v ≤ e) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (e + 1), (inputGates p).card.choose j := by
  classical
  have hshift : attainableTranscripts p =
      (univ.image fun x => transcript p x + v).image (· + v) := by
    rw [attainableTranscripts, image_image]
    refine image_congr fun x _ => funext fun i => ?_
    change transcript p x i = (transcript p x i + v i) + v i
    cases transcript p x i <;> cases v i <;> rfl
  calc
    (attainableTranscripts p).card
      = ((univ.image fun x => transcript p x + v).image (· + v)).card :=
        congrArg card hshift
    _ ≤ (univ.image fun x => transcript p x + v).card := card_image_le
    _ ≤ ∑ j ∈ range (e + 1), (inputGates p).card.choose j := by
      simpa only [Fintype.card_coe] using card_image_le_sum_choose univ
        (fun x => transcript p x + v) fun x _ => by
          rw [← hammingDist_eq_weight_add]
          exact (inputActivityFrom_le_iff p v).mp he x

/-- Attainable patterns are bounded by the exact binomial sum at the worst-case distance from any
fixed baseline on input-reading gates. -/
theorem card_attainableTranscripts_le_sum_choose_inputActivityFrom
    (p : Program signature n g) (v : inputGates p → Bool) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (inputActivityFrom p v + 1), (inputGates p).card.choose j :=
  card_attainableTranscripts_le_sum_choose_of_inputActivityFrom_le p v le_rfl

/-- Projecting shifted gate valuations bounds attainable patterns by the binomial sum at the
worst-case distance from any fixed baseline across all gates. -/
theorem card_attainableTranscripts_le_sum_choose_gateActivityFrom
    (p : Program signature n g) (v : Fin g → Bool) :
    (attainableTranscripts p).card ≤
      ∑ j ∈ range (gateActivityFrom p v + 1), g.choose j := by
  classical
  have hshift : attainableTranscripts p =
      (univ.image fun x => p.eval interpretation x + v).image
        fun z (i : inputGates p) => z i + v i := by
    rw [attainableTranscripts, image_image]
    refine image_congr fun x _ => funext fun i => ?_
    change p.eval interpretation x i.val = (p.eval interpretation x i.val + v i.val) + v i.val
    cases p.eval interpretation x i.val <;> cases v i.val <;> rfl
  calc
    (attainableTranscripts p).card
      = ((univ.image fun x => p.eval interpretation x + v).image
          fun z (i : inputGates p) => z i + v i).card :=
        congrArg card hshift
    _ ≤ (univ.image fun x => p.eval interpretation x + v).card := card_image_le
    _ ≤ ∑ j ∈ range (gateActivityFrom p v + 1), g.choose j := by
      simpa only [Fintype.card_fin] using card_image_le_sum_choose univ
        (fun x => p.eval interpretation x + v) fun x _ => by
          rw [← hammingDist_eq_weight_add]
          exact (gateActivityFrom_le_iff p v).mp le_rfl x

end Cslib.Circuits.Boolean.WeightedThreshold
