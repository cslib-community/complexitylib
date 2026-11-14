/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Optimum
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic

/-!
# Choosing a retained family separately from complete oracle proposals

The raw response proposes a singleton of weight one followed by a full cover of
weight two. With unit dual prices, processing both accepts the singleton and then
rejects the full cover against the remaining dual charge. The upper policy instead
chooses only the full cover. Its provenance is checked against both raw proposals,
and the token infimum uses that complete decoder for every competing policy.
-/

-- This module checks public APIs through private fixtures and anonymous examples.
set_option linter.privateModule false

public section
noncomputable section
namespace CslibFrontierTests.ChosenRetention
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory
open scoped ENNReal

private def two : Instance (Fin 2) (Fin 2) where
  ground := Finset.univ
  sets j := if j = 0 then {0} else Finset.univ
  sets_subset := by intro j; exact Finset.subset_univ _
  weight j := if j = 0 then 1 else 2
  weight_nonneg := by intro j; split_ifs <;> norm_num
  dual _ := 1
  dual_nonneg := by simp
  dual_feasible := by intro j; fin_cases j <;> norm_num [Finset.univ_fin2]

private def raw (_ : List (Record Unit Unit)) (_ _ : Unit) : List (Finset (Fin 2)) := [{0}, {1}]
private def kept (_ : List (Record Unit Unit)) (_ _ : Unit) : List (Finset (Fin 2)) := [{1}]
private def select (_ : List (Record Unit Unit)) : PMF Unit := PMF.pure ()
private def respond (_ : List (Record Unit Unit)) (_ : Unit) : PMF Unit := PMF.pure ()
private def charge (_ : List (Record Unit Unit)) (_ _ : Unit) : ℝ := 2
private def duration (_ : List (Record Unit Unit)) (_ _ : Unit) : ℝ := 1
private def allowed (_ : List (Record Unit Unit) → PMF (Option Unit))
    (_ : List (Record Unit Unit) → PMF (Finset (Fin 2))) : Prop := True

private theorem raw_selected :
    selected two 1 (recordProposals raw) [some ((), ())] = {0} := by
  norm_num [selected, recordProposals, raw, Instance.retain, Instance.Certified,
    Instance.covered, Instance.cost, two, Finset.univ_fin2]; decide

example : two.covered (selected two 1 (recordProposals raw) [some ((), ())]) ≠ two.ground := by
  rw [raw_selected]
  norm_num [Instance.covered, two, Finset.univ_fin2]; decide

private theorem valid : ProposalsValid (recordProposals raw) (recordProposals kept)
    (Discrete.retainingLaw two 1 kept select respond) 1 := by
  intro t ht h hh x hx
  have he : t = 0 := by omega
  subst t
  simp only [PMF.seqHistory_zero]
  cases x with
  | none => simp [recordProposals, proposedSets]
  | some z =>
    rcases z with ⟨⟨⟩, ⟨⟩⟩
    simp [recordProposals, proposedSets, raw, kept]

private theorem upper : Discrete.UpperBounds two 1 kept select respond charge duration
    1 2 1 2 1 where
  charge_nonneg := by intros; norm_num [charge]
  progress := by
    intro t ht h hh hc b hb
    have he : t = 0 := by omega
    subst t
    rcases b with ⟨⟩
    norm_num [PMF.seqHistory_zero, respond, PMF.toOuterMeasure_pure_apply, productive,
      AdaptiveSelection.residual, selected, recordProposals, kept, Instance.retain,
      Instance.Certified, Instance.covered, Instance.cost, two, Finset.univ_fin2]
  cost := by intros; norm_num [respond, charge, PMF.pure_apply, tsum_fintype]
  time := by intros; constructor <;> norm_num [duration]

private theorem lower (choose : List (Record Unit Unit) → PMF (Option Unit))
    (output : List (Record Unit Unit) → PMF (Finset (Fin 2)))
    (hA : Discrete.Admissible two raw choose respond output duration 1 1 1) :
    Discrete.LowerBounds two raw choose respond output charge duration 1 2 1 2 1 1 where
  charge_nonneg := by intros; norm_num [charge]
  progress := by intros; exact PMF.toOuterMeasure_toReal_le_one _ _
  coverage := by
    intro t ht h hh hs b hb x hx
    simpa using Finset.card_le_card (Finset.subset_univ
      (revealed two (recordProposals raw) (some (b, x) :: PMF.seqHistory h) \
        revealed two (recordProposals raw) (PMF.seqHistory h)))
  cost := by intros; norm_num [respond, charge, PMF.pure_apply, tsum_fintype]
  provenance := hA

-- A legitimate chosen-retention witness supplies the exact optimum for the
-- complete raw-proposal problem, even though processing raw proposals fails.
example : Discrete.optimalCost two raw respond charge duration allowed 1 1 1 1 = 2 := by
  have hs := Discrete.optimalCost_sandwich two raw respond charge duration allowed kept select
    1 2 1 2 1 (by norm_num [two])
    (by
      intro k hk
      have he : k = 0 := by omega
      subst k
      norm_num [two])
    (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1)
    (by norm_num) (by norm_num) 2 2 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      have he : Set.Iio (1 : ℕ) = {0} := by ext x; simp
      rw [he, ProbabilityTheory.binomial_real_singleton]
      norm_num)
    trivial
    (Discrete.retaining_admissible_of_valid two 1 1 raw kept select respond duration 1 valid)
    upper (fun choose output _ hA => lower choose output hA)
  norm_num [ENNReal.ofReal_div_of_pos] at hs
  exact le_antisymm (hs.2.1.trans hs.2.2) hs.1

-- Compatibility allows candidates received earlier to be retained on a later response.
example :
    let all : List Unit → Unit → List (Finset (Fin 2)) :=
      fun h _ => if h = [] then [{1}] else []
    let retained : List Unit → Unit → List (Finset (Fin 2)) :=
      fun h _ => if h = [] then [] else [{1}]
    ProposalsValid all retained (fun _ => PMF.pure ()) 2 := by
  intro all retained t ht h hh x hx
  have ht' : t = 0 ∨ t = 1 := by omega
  rcases ht' with rfl | rfl
  · simp [PMF.seqHistory_zero, all, retained]
  · have he : PMF.seqHistory h = [()] := by simp [PMF.seqHistory_one]
    rw [he]
    simp [all, retained, proposedSets]

end CslibFrontierTests.ChosenRetention
