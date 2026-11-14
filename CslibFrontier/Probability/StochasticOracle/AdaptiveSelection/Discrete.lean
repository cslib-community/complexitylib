/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection
public import CslibFrontier.Probability.PMF.SequentialHistory
public import CslibFrontier.Probability.StochasticDomination.SequentialSupport
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Retained coverage for arbitrary discrete response laws

The finite-horizon probability step of [Wang2027], Theorem 5(1), PDF p. 12
and Appendix A.5, PDF p. 16, for an arbitrary PMF response type. The response
can contain unbounded raw data or invoice metadata. The conditional productivity
envelope is imposed only at supported, incomplete histories of the actual law.

The retained family is computed by `selected`, so coverage follows from the
existing deterministic residual-count invariant, rather than being an input.
This module does not assert cost, latency or native compilation bounds.

## Main results

* `incompletion_le_binomial_discrete`: actual failure probability is bounded by a binomial tail.
* `binomial_le_completion_discrete`: the complementary retained-coverage probability bound.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open PartialCover MeasureTheory
open scoped ENNReal
variable {E J Ω : Type*} [DecidableEq E] [DecidableEq J]

/-- Use a newest-first conditional law in the chronological sequential process. -/
@[expose] def responseStep (law : List Ω → PMF Ω) (t : ℕ) (h : Fin t → Ω) : PMF Ω :=
  law (PMF.seqHistory h)

/-- The chronological comparison count equals the actual newest-first transcript count. -/
theorem seqCount_eq_count (b : List Ω → Ω → Bool) (n : ℕ) (h : Fin n → Ω) :
    PMF.seqCount (fun _ h => {x | b (PMF.seqHistory h) x = true}) n h =
      count b (PMF.seqHistory h) := by
  classical
  induction n with
  | zero => simp [count]
  | succ n ih =>
    conv_lhs => rw [← Fin.snoc_init_self h]
    conv_rhs => rw [← Fin.snoc_init_self h]
    rw [PMF.seqCount_snoc, PMF.seqHistory_snoc, count, ih]
    simp only [Set.mem_ofPred_eq]
    split_ifs <;> rfl

/-- Actual retained noncompletion is bounded by the binomial lower tail, with
no finite-alphabet restriction. Only reached incomplete prefixes need the
conditional productivity envelope. -/
theorem incompletion_le_binomial_discrete
    (I : Instance E J) (ρ : ℝ) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (p : ℝ) ≤ ((law (PMF.seqHistory h)).toOuterMeasure
        {x | productive I ρ proposal a (PMF.seqHistory h) x = true}).toReal) :
    ((PMF.seqProcess (responseStep law) n).toOuterMeasure
      {h | I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground}).toReal ≤
      (ProbabilityTheory.binomial n p).real (Set.Iio r) := by
  classical
  let event := fun (t : ℕ) (h : Fin t → Ω) =>
    {x | productive I ρ proposal a (PMF.seqHistory h) x = true}
  have ht := PMF.seqCount_active_toReal_Iio_le_of_support
    (responseStep law) event n r p (by
      intro t ht h hh _
      by_cases hc : I.covered (selected I ρ proposal (PMF.seqHistory h)) = I.ground
      · have he : event t h = Set.univ := by
          ext x
          simp only [event, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          exact productive_of_complete I ρ proposal a _ hc x
        rw [he, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)]
        simpa using p.2.2
      · exact hp t ht h hh hc)
  refine le_trans ?_ ht
  rw [PMF.toOuterMeasure_map_apply]
  apply ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
  apply measure_mono
  intro h hh
  change PMF.seqCount event n h < r
  rw [seqCount_eq_count]
  by_contra hn
  exact hh (count_completes I ρ proposal a _
    (hr.trans (Nat.mul_le_mul_left a (Nat.le_of_not_gt hn))))

/-- The complementary retained-coverage guarantee for arbitrary discrete response
laws. The local dual certificate is already supplied pathwise by `selected_bound`. -/
theorem binomial_le_completion_discrete
    (I : Instance E J) (ρ : ℝ) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ t, t < n → ∀ h : Fin t → Ω,
      h ∈ (PMF.seqProcess (responseStep law) t).support →
      I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground →
      (p : ℝ) ≤ ((law (PMF.seqHistory h)).toOuterMeasure
        {x | productive I ρ proposal a (PMF.seqHistory h) x = true}).toReal) :
    1 - (ProbabilityTheory.binomial n p).real (Set.Iio r) ≤
      ((PMF.seqProcess (responseStep law) n).toOuterMeasure
        {h | I.covered (selected I ρ proposal (PMF.seqHistory h)) = I.ground}).toReal := by
  have hb := incompletion_le_binomial_discrete I ρ proposal law a r n hr p hp
  have hc := PMF.toOuterMeasure_toReal_add_compl (PMF.seqProcess (responseStep law) n)
    {h | I.covered (selected I ρ proposal (PMF.seqHistory h)) = I.ground}
  change _ + ((PMF.seqProcess (responseStep law) n).toOuterMeasure
    {h | I.covered (selected I ρ proposal (PMF.seqHistory h)) ≠ I.ground}).toReal = 1 at hc
  linarith

end Cslib.Probability.StochasticOracle.AdaptiveSelection
