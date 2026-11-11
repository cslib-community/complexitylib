/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.Entropy
import CslibFrontier.Probability.PMF.Event

/-!
# Conditional information in independent samples

Conditional information content averages to conditional Shannon entropy. If every positive
joint mass is at least `2 ^ (-bound)`, then each sample's conditional information lies between
zero and `bound`. Hoeffding's inequality therefore controls the lower tail of its sum.

## Main results

* `Cslib.Probability.PMF.uniform_map_mass_ge`: a supported image has at least one seed's mass.
* `Cslib.Probability.PMF.surprisal_pi`: information adds across independent coordinates.
* `Cslib.Probability.PMF.pi_sum_conditionalSurprisal_le`: concentration of conditional information.
* `Cslib.Probability.PMF.pi_conditional_mass_gt`: the corresponding conditional-mass tail bound.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, Proposition 1 and Lemma 2.
  We use a bounded-information variant for deterministic images of uniform finite seeds.
  Its loss depends on the seed length rather than Proposition 1's sharper alphabet-size bound.
  Smoothing and leftover hashing are separate steps.

Adapted from Probability/EntropyConcentration.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.

-/

@[expose] public section

namespace Cslib.Probability.PMF

/-- Every observable image of a uniform finite seed has probability at least one over the seed
space size, equivalently `2 ^ (-log₂(card Seed))`. -/
theorem uniform_map_mass_ge {Seed Output : Type*} [Fintype Seed] [Nonempty Seed]
    (f : Seed → Output) (output : Output)
    (houtput : output ∈ ((PMF.uniformOfFintype Seed).map f).support) :
    (2 : ℝ) ^ (-Real.logb 2 (Fintype.card Seed)) ≤
      (((PMF.uniformOfFintype Seed).map f) output).toReal := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_logb (by norm_num)
    (by norm_num) (by exact_mod_cast Fintype.card_pos (α := Seed))]
  obtain ⟨seed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp houtput
  simpa only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) (le_map_apply (PMF.uniformOfFintype Seed) f seed)

variable {ι : Type*} [Fintype ι] {α β : ι → Type*}
  [∀ i, Finite (α i)] [∀ i, Finite (β i)]

/-- Information content adds across independent coordinates on the product's support. -/
theorem surprisal_pi (p : ∀ i, PMF (α i)) (outcome : ∀ i, α i)
    (houtcome : outcome ∈ (pi p).support) :
    surprisal (pi p) outcome = ∑ i, surprisal (p i) (outcome i) := by
  classical
  have hpositive (i : ι) : (p i (outcome i)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(mem_support_pi_iff p outcome).mp houtcome i,
      PMF.apply_ne_top _ _⟩
  simp only [surprisal, pi_apply, ENNReal.toReal_prod,
    Real.logb_prod _ _ (fun i _ => hpositive i), Finset.sum_neg_distrib]

/-- Independent conditional information concentrates around the sum of conditional entropies.
Only outcomes in the support need a probability lower bound. -/
theorem pi_sum_conditionalSurprisal_le (joint : ∀ i, PMF (α i × β i))
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hmass : ∀ i pair, pair ∈ (joint i).support →
      (2 : ℝ) ^ (-bound) ≤ (joint i pair).toReal) (hε : 0 ≤ ε) :
    ((pi joint).toOuterMeasure {outcome |
      ∑ i, surprisal (conditionalSnd (joint i) (outcome i).1) (outcome i).2 ≤
        (∑ i, conditionalEntropy (joint i)) - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  let (i : ι) := Fintype.ofFinite (α i)
  let (i : ι) := Fintype.ofFinite (β i)
  have hscore (i : ι) (pair : α i × β i) (hpair : pair ∈ (joint i).support) :
      surprisal (conditionalSnd (joint i) pair.1) pair.2 ∈ Set.Icc 0 bound := by
    refine ⟨surprisal_nonneg _ _, surprisal_le_of_mass_ge _ _ ?_⟩
    exact (hmass i pair hpair).trans (ENNReal.toReal_mono (PMF.apply_ne_top _ _)
      (apply_le_conditionalSnd (joint i) pair.1 pair.2))
  simpa only [← conditionalEntropy_eq_sum_surprisal] using
    pi_sum_le_mean_sub joint
      (fun i pair => surprisal (conditionalSnd (joint i) pair.1) pair.2) hbound hscore hε

/-- Except with exponentially small probability, the conditional mass of an independent tuple
is at most `2 ^ (-(sum of conditional entropies - ε))`. All observations are revealed together;
null observation tuples do not affect the bound. -/
theorem pi_conditional_mass_gt (joint : ∀ i, PMF (α i × β i))
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hmass : ∀ i pair, pair ∈ (joint i).support →
      (2 : ℝ) ^ (-bound) ≤ (joint i pair).toReal) (hε : 0 ≤ ε) :
    let repeated := (pi joint).map
      (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2))
    (repeated.toOuterMeasure {pair |
      (2 : ℝ) ^ (-((∑ i, conditionalEntropy (joint i)) - ε)) <
        (conditionalSnd repeated pair.1 pair.2).toReal}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) := by
  dsimp only
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
    ((pi joint).toOuterMeasure_mono ?_))
    (pi_sum_conditionalSurprisal_le joint hbound hmass hε)
  rintro outcome ⟨hlarge, houtcome⟩
  have hobserved : (fun i => (outcome i).1) ∈
      (pi (fun i => (joint i).map Prod.fst)).support := by
    rw [pi_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨outcome, houtcome, rfl⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    conditionalSnd_pi_joint joint _ hobserved] at hlarge
  have hconditional : (fun i => (outcome i).2) ∈
      (pi (fun i => conditionalSnd (joint i) (outcome i).1)).support := by
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp
      ((Real.rpow_pos_of_pos (by norm_num) _).trans hlarge)).1
  have h := (surprisal_le_iff_mass_ge _ _ hconditional).mpr hlarge.le
  simpa only [Set.mem_ofPred_eq, surprisal_pi _ _ hconditional] using h

end Cslib.Probability.PMF
