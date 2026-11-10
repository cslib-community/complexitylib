/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverRisk
public import CslibFrontier.Probability.FiniteTableOfPMF
public import CslibFrontier.Probability.PMF.Disintegration
public import CslibFrontier.Probability.PMF.StoppedProcess
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Exact disintegration of correlated batch responses

The posterior kernels are constructed from the actual joint experiment, with
arbitrary discrete hidden state and metadata. Histories contain precisely the
returned original families, not independent replacement samples. Null histories
use the prior, as in the existing posterior API. [Wang2027], Theorem 4, PDF pp. 9–11.

## Main definitions

* `history`, `kernel`: actual response history and its derived conditional law.

## Main results

* `history_law`: the constructed kernels reproduce the actual complete history law.
* `retention_law`: local retention on the actual joint sample has the existing risk-law semantics.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.Disintegration
open Cslib.Optimization.OneConstraint
open Instance
variable {S J E : Type} [Fintype J] [DecidableEq J] [DecidableEq E]

/-- Earlier processed families, newest first. The joint sample is never resampled. -/
@[expose] def history (response : ℕ → S → Finset J) : ℕ → S → List (Finset J)
  | 0, _ => []
  | n + 1, s => response n s :: history response n s

omit [Fintype J] [DecidableEq J] in
/-- Actual history length, including empty/failed returned families. -/
theorem history_length (response : ℕ → S → Finset J) (n : ℕ) (s : S) :
    (history response n s).length = n := by induction n <;> simp [history, *]

omit [Fintype J] [DecidableEq J] in
/-- Chronological readback of the actual history is exactly its indexed responses. -/
theorem history_reverse (response : ℕ → S → Finset J) (n : ℕ) (s : S) :
    (history response n s).reverse = List.ofFn (fun i : Fin n => response i.val s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [history, List.reverse_cons, ih, List.ofFn_succ_last]
    rfl

/-- Source conditional response law extracted from the complete original experiment.
No conditional-law equality or representation certificate is an argument. -/
@[expose] def kernel (μ : PMF S) (response : ℕ → S → Finset J) : ResponseKernel J :=
  fun h => Distribution.ofPMF
    ((PMF.posterior μ (history response h.length) h).map (response h.length))

/-- One history transition under the constructed conditional kernel. -/
@[expose] def next (μ : PMF S) (response : ℕ → S → Finset J) (h : List (Finset J)) :
    PMF (List (Finset J)) := ((kernel μ response h).toPMF).map fun P => P :: h

omit [DecidableEq J] in
/-- The actual complete response history law is recovered, including correlation,
unbounded hidden metadata and harmless completion at null histories. -/
theorem history_law (μ : PMF S) (response : ℕ → S → Finset J) (n : ℕ) :
    ObservedProcess.stateLaw (next μ response) n [] = μ.map (history response n) := by
  induction n with
  | zero => exact (PMF.map_const μ ([] : List (Finset J))).symm
  | succ n ih =>
    rw [ObservedProcess.stateLaw, ih]
    trans (μ.map (history response n)).bind fun h =>
      (PMF.posterior μ (history response n) h).bind fun s =>
        PMF.pure (response n s :: h)
    · apply PMF.bind_congr_on_support
      intro h hh
      obtain ⟨s, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
      simp only [next, kernel, history_length, Distribution.toPMF_ofPMF, PMF.map_comp]
      rfl
    · rw [PMF.posterior_bind]
      rfl

/-- Retention after the observed history, processed in the original chronological order. -/
@[expose] def retained (I : Instance E J) (ρ : ℝ) (h : List (Finset J)) : Finset J :=
  I.retain ρ ∅ h.reverse

omit [Fintype J] in
/-- Appending one actual response executes exactly the original local test. -/
theorem retained_cons (I : Instance E J) (ρ : ℝ) (h : List (Finset J)) (P : Finset J) :
    retained I ρ (P :: h) = I.step ρ (retained I ρ h) P := by
  -- Unfold both local-test presentations through their semireducible instance arguments.
  set_option backward.isDefEq.respectTransparency false in
    simp [retained, List.reverse_cons, I.retain_append, Instance.retain, Instance.step]

private theorem law_history (I : Instance E J) (ρ : ℝ) (μ : PMF S)
    (response : ℕ → S → Finset J) (vs : List (Finset E)) (h : List (Finset J)) :
    (I.law ρ (kernel μ response) h (retained I ρ h) vs).toPMF =
      (ObservedProcess.stateLaw (next μ response) vs.length h).map (retained I ρ) := by
  induction vs generalizing h with
  | nil => simp [Instance.law, ObservedProcess.stateLaw, Distribution.toPMF_pure]
  | cons V vs ih =>
    rw [Instance.law, Distribution.toPMF_bind, List.length_cons,
      StoppedProcess.stateLaw_succ_left, next, PMF.bind_map, PMF.map_bind]
    apply PMF.bind_congr_on_support
    intro P _
    rw [← retained_cons, ih]
    simp only [Function.comp_def]

/-- The exact realized retained family has the existing source risk law. This
identity is proved from the original joint experiment, not supplied as a premise. -/
theorem retention_law (I : Instance E J) (ρ : ℝ) (μ : PMF S)
    (response : ℕ → S → Finset J) (vs : List (Finset E)) :
    (I.law ρ (kernel μ response) [] ∅ vs).toPMF =
      μ.map (fun s => retained I ρ (history response vs.length s)) := by
  have h := law_history I ρ μ response vs []
  simpa only [retained, List.reverse_nil, Instance.retain, history_law, PMF.map_comp,
    Function.comp_def] using h

omit [DecidableEq J] in
/-- Finite source event probabilities agree with their actual PMF Boolean mass. -/
theorem event_eq_map (w : Distribution (Finset J) ℝ) (A : Finset J → Prop)
    [DecidablePred A] : event w A = ((w.toPMF.map fun P => decide (A P)) true).toReal := by
  classical
  have h := Distribution.toPMF_real (w.map fun P => decide (A P)) true
  rw [Distribution.toPMF_map] at h
  simpa [event, Distribution.mean, Distribution.map, mul_ite] using h.symm

/-- Source risk bound for the actual joint response experiment. The sole stochastic
premise is the source local-certification/coverage envelope at reachable histories,
under the conditional kernels constructed from this very experiment. -/
theorem risk_bound (I : Instance E J) (ρ : ℝ) (μ : PMF S)
    (response : ℕ → S → Finset J) (vs : List (Finset E)) {p : ℝ}
    (hp : 0 ≤ p) (hpone : p ≤ 1)
    (had : I.Admissible ρ p (kernel μ response) [] ∅ vs) :
    max 0 (1 - ∑ e ∈ I.ground, (1 - p) ^ chances e vs) ≤
      ((μ.map fun s => decide (I.covered (retained I ρ (history response vs.length s)) =
        I.ground ∧ I.cost (retained I ρ (history response vs.length s)) ≤
          ρ * ∑ e ∈ I.ground, I.dual e)) true).toReal := by
  classical
  have h := I.certified_completion_bound ρ hp hpone (kernel μ response) vs had
  rw [event_eq_map, retention_law, PMF.map_comp] at h
  exact h

end Cslib.Probability.StochasticOracle.PartialCover.Disintegration
