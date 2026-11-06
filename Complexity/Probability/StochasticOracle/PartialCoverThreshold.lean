/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.PartialCoverGreedy
import Mathlib.Data.Nat.Find

/-!
# Exact rational repetition thresholds

For rational failure probabilities and budgets, the logarithmic repetition
threshold of [Wang2027], Theorem 4 (Section 5, PDF pp. 10–11), can be evaluated
by searching exact rational powers. This includes equality at an integral
logarithmic threshold, where approximate real logarithms need special care.
The search is executable; no binary time or space bound is claimed.

## Main results

* `rationalRepetitions_eq`: exact agreement with the real-log ceiling convention.
* `pow_le_iff_rationalRepetitions_le`: minimality of the computed threshold.
* `rationalBatch_execution`: emitted-call pathwise billing and parallel deadline.
* `rationalBatch_joint_execution`: certified success and resource caps in one finite law.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover.Instance

/-- A positive rational failure probability below one eventually meets any positive budget. -/
theorem exists_rational_power (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) : ∃ n : ℕ, q ^ n ≤ δ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqoner : (q : ℝ) < 1 := by exact_mod_cast hqone
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine ⟨repetitions q δ, ?_⟩
  have h := (pow_le_iff_repetitions_le hqr hqoner hδr (repetitions q δ)).mpr le_rfl
  exact_mod_cast h

/-- Exact search for the least repetition count meeting a rational failure budget.
The proofs justify termination and are erased when evaluating the search. -/
@[expose] def rationalRepetitions (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) : ℕ := Nat.find (exists_rational_power q δ hq hqone hδ)

/-- Search minimality, including budgets at least one (which give zero calls). -/
theorem pow_le_iff_rationalRepetitions_le (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (n : ℕ) :
    q ^ n ≤ δ ↔ rationalRepetitions q δ hq hqone hδ ≤ n := by
  constructor
  · intro hn
    exact Nat.find_min' (exists_rational_power q δ hq hqone hδ) hn
  · intro hn
    exact (pow_le_pow_of_le_one hq.le hqone.le hn).trans
      (Nat.find_spec (exists_rational_power q δ hq hqone hδ))

/-- The executable rational search agrees exactly with the source's real logarithms. -/
theorem rationalRepetitions_eq (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) :
    rationalRepetitions q δ hq hqone hδ = repetitions (q : ℝ) (δ : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqoner : (q : ℝ) < 1 := by exact_mod_cast hqone
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  apply Nat.le_antisymm
  · apply (pow_le_iff_rationalRepetitions_le q δ hq hqone hδ _).mp
    have h := (pow_le_iff_repetitions_le hqr hqoner hδr (repetitions q δ)).mpr le_rfl
    exact_mod_cast h
  · apply (pow_le_iff_repetitions_le hqr hqoner hδr _).mp
    have h := (pow_le_iff_rationalRepetitions_le q δ hq hqone hδ
      (rationalRepetitions q δ hq hqone hδ)).mpr le_rfl
    exact_mod_cast h

end Cslib.Probability.StochasticOracle.PartialCover.Instance

namespace Cslib.Algorithms.Lean.Multicover
open Cslib.Probability.StochasticOracle.PartialCover.Instance

/-- Greedy selection with exact executable rational threshold evaluation. -/
@[expose] def rationalBatch {E : Type} [DecidableEq E] [Fintype E]
    (as : List (Oracle E)) (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) :
    List (Oracle E) := batch as (rationalRepetitions q δ hq hqone hδ)

/-- The rational implementation emits exactly the batch analyzed with real logarithms.
For the source sufficient demand use the rational budget `(1-η)/n`. -/
theorem rationalBatch_eq {E : Type} [DecidableEq E] [Fintype E]
    (as : List (Oracle E)) (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) :
    rationalBatch as q δ hq hqone hδ = batch as (repetitions (q : ℝ) (δ : ℝ)) := by
  rw [rationalBatch, rationalRepetitions_eq]

/-- Pathwise billing and parallel deadline for the actual rational-threshold output.
All calls are issued together. `tokens` and `latency` may depend arbitrarily on
an outcome, including the responses; only individual call caps are assumed.
Taking `Ω` to be a full-measure subset gives the source's almost-sure statement.
This does not charge local computation against the oracle deadline. -/
theorem rationalBatch_execution {E Ω : Type} [DecidableEq E] [Fintype E]
    (as : List (Oracle E)) (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ)
    (D : ℝ)
    (tokens latency : Fin (rationalBatch as q δ hq hqone hδ).length → Ω → ℝ)
    (cutoff : Oracle E → ℝ)
    (htokens : ∀ i ω, tokens i ω ≤
      ((rationalBatch as q δ hq hqone hδ).get i).cost)
    (hlatency : ∀ i ω, latency i ω ≤
      cutoff ((rationalBatch as q δ hq hqone hδ).get i))
    (hdeadline : ∀ a ∈ as, cutoff a ≤ D) :
    ∀ ω, (∑ i, tokens i ω) ≤
        (bill (batch as (repetitions (q : ℝ) (δ : ℝ))) : ℝ) ∧
      ∀ i, latency i ω ≤ D := by
  intro ω
  have hsub : ∀ a ∈ rationalBatch as q δ hq hqone hδ, a ∈ as := by
    intro a ha
    exact mem_run as _ _ ha
  constructor
  · calc
      (∑ i, tokens i ω) ≤ ∑ i,
          (((rationalBatch as q δ hq hqone hδ).get i).cost : ℝ) :=
        Finset.sum_le_sum fun i _ => htokens i ω
      _ = (bill (rationalBatch as q δ hq hqone hδ) : ℝ) := by
        rw [← List.sum_ofFn]
        have h := List.ofFn_getElem_eq_map
          (rationalBatch as q δ hq hqone hδ) (fun a : Oracle E => (a.cost : ℝ))
        simpa only [List.get_eq_getElem, bill, Rat.cast_list_sum, List.map_map,
          Function.comp_def] using
          congrArg List.sum h
      _ = _ := by rw [rationalBatch_eq]
  · intro i
    exact (hlatency i ω).trans (hdeadline _ (hsub _ (List.get_mem _ _)))

open Cslib.Probability.StochasticOracle
open Cslib.Optimization.OneConstraint

/-- Joint finite response/resource execution for the computed greedy batch.
The resource kernel may depend on the retained output, so no independence is
assumed. All calls start together and are billed even on failure; local
computation is outside `D`. The finite resource alphabet is an explicit model
restriction, not a native sampler or a binary runtime certificate. -/
theorem rationalBatch_joint_execution {E J R : Type}
    [DecidableEq E] [Fintype E] [DecidableEq J] [Fintype J] [Fintype R]
    (I : PartialCover.Instance E J) (hground : I.ground = Finset.univ)
    (hU : I.ground.Nonempty) (as : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible)
    (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ)
    (ρ D : ℝ) (K : ResponseKernel J)
    (L : Finset J → Distribution R ℝ)
    (tokens latency : Fin (rationalBatch as q (δ / Fintype.card E) hq hqone
      (div_pos hδ (by
          have hc := hU.card_pos
          rw [hground, Finset.card_univ] at hc
          exact_mod_cast hc))).length → Finset J → R → ℝ)
    (cutoff : Oracle E → ℝ)
    (htokens : ∀ i P r, tokens i P r ≤
      ((rationalBatch as q (δ / Fintype.card E) hq hqone
        (div_pos hδ (by
          have hc := hU.card_pos
          rw [hground, Finset.card_univ] at hc
          exact_mod_cast hc))).get i).cost)
    (hlatency : ∀ i P r, latency i P r ≤ cutoff
      ((rationalBatch as q (δ / Fintype.card E) hq hqone
        (div_pos hδ (by
          have hc := hU.card_pos
          rw [hground, Finset.card_univ] at hc
          exact_mod_cast hc))).get i))
    (hdeadline : ∀ a ∈ as, cutoff a ≤ D)
    (had : I.Admissible ρ (1-(q : ℝ)) K [] ∅
      ((batch as (repetitions (q : ℝ) ((δ : ℝ) / Fintype.card E))).map Oracle.eligible)) :
    let calls := batch as (repetitions (q : ℝ) ((δ : ℝ) / Fintype.card E))
    let joint := (I.law ρ K [] ∅ (calls.map Oracle.eligible)).bind
      (fun P => (L P).map (fun r => (P, r)))
    1 - (δ : ℝ) ≤ joint.mean (fun x => if
      I.covered x.1 = I.ground ∧ I.cost x.1 ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
      (∑ i, tokens i x.1 x.2) ≤ (bill calls : ℝ) ∧
      (∀ i, latency i x.1 x.2 ≤ D) then 1 else 0) := by
  classical
  have hn : (0 : ℚ) < Fintype.card E := by
    have hc := hU.card_pos
    rw [hground, Finset.card_univ] at hc
    exact_mod_cast hc
  have hcaps := rationalBatch_execution as q (δ / Fintype.card E) hq hqone
    (div_pos hδ hn) D (fun i (x : Finset J × R) => tokens i x.1 x.2)
    (fun i (x : Finset J × R) => latency i x.1 x.2) cutoff
    (fun i x => htokens i x.1 x.2) (fun i x => hlatency i x.1 x.2) hdeadline
  have hcast : ((δ / Fintype.card E : ℚ) : ℝ) = (δ : ℝ) / Fintype.card E := by
    push_cast
    rfl
  simp only [hcast] at hcaps
  dsimp only
  rw [Distribution.mean_bind]
  simp only [Distribution.mean_map, Function.comp_def]
  simp_rw [show ∀ P r, (∑ i, tokens i P r) ≤
    (bill (batch as (repetitions (q : ℝ) ((δ : ℝ) / Fintype.card E))) : ℝ) from
      fun P r => (hcaps (P, r)).1]
  simp_rw [show ∀ P r, (∀ i, latency i P r ≤ D) from fun P r => (hcaps (P, r)).2]
  simp only [implies_true, and_true, Distribution.mean_const]
  have hs := greedy_certified_completion I hground hU as hcover
    (ρ := ρ) (p := 1-(q : ℝ)) (δ := (δ : ℝ))
    (sub_pos.mpr (by exact_mod_cast hqone))
    (sub_lt_self 1 (by exact_mod_cast hq))
    (by exact_mod_cast hδ) K
  simp only [sub_sub_cancel] at hs
  convert hs had using 1
  congr 1
  funext P
  split_ifs <;> rfl

end Cslib.Algorithms.Lean.Multicover
