/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Discrete
public import CslibFrontier.Probability.StochasticOracle.AdaptiveReachable
public import CslibFrontier.Probability.FiniteTable.Support
import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.HistoryExpectation
import CslibFrontier.Probability.StochasticDomination.SequentialUpper
import CslibFrontier.Probability.PMF.SequentialPrefix
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Exact finite-table sequential execution

Finite conditional-table history expectations are precisely expectations under
the chronological sequential PMF process. Its supported tuples correspond to
reachable newest-first transcripts, including state-dependent and null branches.

## Main results

* `historyExpectation_eq_sum_seqProcess`, `historyExpectation_indicator_eq_seqProcess`:
  exact observable and event semantics.
* `reachable_seqHistory_iff_mem_support`: exact correspondence of positive paths.
* `count_tail_le_binomial`: reuse of the supported sequential upper comparison.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open Cslib.Optimization.OneConstraint MeasureTheory
open scoped ENNReal
section Expectations
variable {Ω : Type*} [Fintype Ω]

/-- The table recurrence is the actual sequential PMF expectation, with exact
newest-first transcript decoding and arbitrary real observables. -/
theorem historyExpectation_eq_sum_seqProcess
    (law : List Ω → Distribution Ω ℝ) (f : List Ω → ℝ) (n : ℕ) :
    historyExpectation law f n [] =
      ∑ h : Fin n → Ω,
        (PMF.seqProcess (responseStep (fun h => (law h).toPMF)) n h).toReal *
          f (PMF.seqHistory h) := by
  classical
  induction n generalizing f with
  | zero =>
    simp [historyExpectation, PMF.seqProcess, PMF.pure_apply,
      Subsingleton.elim (default : Fin 0 → Ω) Fin.elim0]
  | succ n ih =>
    rw [historyExpectation_succ_right, ih, PMF.seqProcess, PMF.sum_bind_mul]
    apply Finset.sum_congr rfl
    intro h _
    rw [PMF.sum_map_mul]
    simp only [PMF.seqHistory_snoc, responseStep, Distribution.toPMF_real, Distribution.mean]

/-- A finite history-event expectation equals its actual sequential event probability. -/
theorem historyExpectation_indicator_eq_seqProcess
    (law : List Ω → Distribution Ω ℝ) (event : Set (List Ω)) [DecidablePred (· ∈ event)] (n : ℕ) :
    historyExpectation law (fun h => if h ∈ event then 1 else 0) n [] =
      ((PMF.seqProcess (responseStep (fun h => (law h).toPMF)) n).toOuterMeasure
        {h | PMF.seqHistory h ∈ event}).toReal := by
  classical
  rw [historyExpectation_eq_sum_seqProcess, PMF.toOuterMeasure_apply_toReal]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hx : PMF.seqHistory h ∈ event <;> simp [hx]

end Expectations

section Reachability
variable {Ω : Type} [Fintype Ω]

/-- Supported chronological tuples are exactly the reachable finite-table
transcripts; null response branches create no spurious executions. -/
theorem reachable_seqHistory_iff_mem_support
    (law : List Ω → Distribution Ω ℝ) (n : ℕ) (h : Fin n → Ω) :
    Reachable law (PMF.seqHistory h) ↔
      h ∈ (PMF.seqProcess (responseStep (fun h => (law h).toPMF)) n).support := by
  induction n with
  | zero =>
    simp only [PMF.seqHistory_zero, PMF.seqProcess, PMF.support_pure, Set.mem_singleton_iff]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => .nil⟩
  | succ n ih =>
    obtain ⟨g, x, rfl⟩ : ∃ g x, h = Fin.snoc g x :=
      ⟨Fin.init h, h (Fin.last n), (Fin.snoc_init_self h).symm⟩
    rw [PMF.seqHistory_snoc, PMF.mem_support_seqProcess_snoc]
    simp only [responseStep, Distribution.mem_support_toPMF]
    constructor
    · intro hh
      cases hh with
      | cons hg hx => exact ⟨(ih g).mp hg, hx⟩
    · rintro ⟨hg, hx⟩
      exact .cons ((ih g).mpr hg) hx

/-- Finite-table history counts inherit the supported-prefix binomial upper
comparison directly from their exact PMF interpretation. -/
theorem count_tail_le_binomial
    (law : List Ω → Distribution Ω ℝ) (b : List Ω → Ω → Bool)
    (n r : ℕ) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, Reachable law h → (law h).mean (fun x => if b h x then 1 else 0) ≤ p) :
    historyExpectation law (fun h => if r ≤ count b h then (1 : ℝ) else 0) n [] ≤
      (ProbabilityTheory.binomial n p).real (Set.Ici r) := by
  classical
  have hb := PMF.seqCount_toReal_Ici_le_of_support
    (responseStep (fun h => (law h).toPMF))
    (fun _ h => {x | b (PMF.seqHistory h) x = true}) n r p (by
      intro t ht h hh
      have hr := (reachable_seqHistory_iff_mem_support law t h).mpr hh
      change ((law (PMF.seqHistory h)).toPMF.toOuterMeasure
        {x | b (PMF.seqHistory h) x = true}).toReal ≤ p
      rw [← Distribution.mean_bool_eq_toPMF]
      exact hp _ hr)
  rw [PMF.toOuterMeasure_map_apply] at hb
  have he := historyExpectation_indicator_eq_seqProcess law {h | r ≤ count b h} n
  simp only [Set.mem_ofPred_eq] at he
  rw [he]
  simpa only [Set.preimage, Set.mem_Ici, seqCount_eq_count] using hb

end Reachability

end Cslib.Probability.StochasticOracle.AdaptiveSelection
