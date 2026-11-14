/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.FiniteTable
import CslibFrontierTests.StochasticOracleDiscreteRetention
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Adaptive batch selection with unbounded response-dependent invoices

Two singleton obligations require separate batches. The selector queries the
first uncovered obligation, using the actual retained family. A geometric zero
response supplies that batch's singleton; other responses supply nothing.
Invoices are `x + 1` and physical duration is one. Completion halts the policy.
-/

noncomputable section
namespace CslibFrontierTests.DiscreteBatches
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover SelectionPolicy MeasureTheory
open scoped ENNReal

private def toy : Instance (Fin 2) (Fin 2) where
  ground := Finset.univ
  sets := fun j => {j}
  sets_subset := by simp
  weight := fun _ => 1
  weight_nonneg := by simp
  dual := fun _ => 1
  dual_nonneg := by simp
  dual_feasible := by simp

private def propose (_ : List (Record (Fin 2) ℕ)) (b : Fin 2) (x : ℕ) :
    List (Finset (Fin 2)) := if x = 0 then [{b}] else []

private def chosen (h : List (Record (Fin 2) ℕ)) : Fin 2 :=
  if 0 ∈ selected toy 1 (recordProposals propose) h then 1 else 0

private def select (h : List (Record (Fin 2) ℕ)) : PMF (Fin 2) := PMF.pure (chosen h)
private def respond (_ : List (Record (Fin 2) ℕ)) (_ : Fin 2) : PMF ℕ := DiscreteRetention.law []
private def charge (_ : List (Record (Fin 2) ℕ)) (_ : Fin 2) (x : ℕ) : ℝ :=
  DiscreteRetention.charge [] x
private def duration (_ : List (Record (Fin 2) ℕ)) (_ : Fin 2) (_ : ℕ) : ℝ := 1

private theorem covered_eq (C : Finset (Fin 2)) : toy.covered C = C := by
  simp [Instance.covered, toy]

private theorem chosen_missing (h : List (Record (Fin 2) ℕ))
    (hc : toy.covered (selected toy 1 (recordProposals propose) h) ≠ toy.ground) :
    chosen h ∉ selected toy 1 (recordProposals propose) h := by
  rw [covered_eq] at hc
  unfold chosen
  split_ifs with hz
  · intro ho
    apply hc
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    fin_cases i <;> assumption
  · exact hz

private theorem selected_zero (h : List (Record (Fin 2) ℕ)) (b : Fin 2)
    (hb : b ∉ selected toy 1 (recordProposals propose) h) :
    selected toy 1 (recordProposals propose) (some (b, 0) :: h) =
      insert b (selected toy 1 (recordProposals propose) h) := by
  have hc : toy.Certified 1 (selected toy 1 (recordProposals propose) h) {b} := by
    unfold Instance.Certified
    rw [covered_eq, covered_eq]
    rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.mpr hb)]
    simp [Instance.cost, show toy.weight b = 1 from rfl, show toy.dual b = 1 from rfl]
  rw [selected, recordProposals_some, propose, ite_eq_left rfl, Instance.retain,
    ite_eq_left hc, Instance.retain]
  ext i
  simp

private theorem productive_zero (h : List (Record (Fin 2) ℕ))
    (hc : toy.covered (selected toy 1 (recordProposals propose) h) ≠ toy.ground) :
    productive toy 1 (recordProposals propose) 1 h (some (chosen h, 0)) = true := by
  have hb := chosen_missing h hc
  have hm : chosen h ∈ toy.ground \ toy.covered (selected toy 1 (recordProposals propose) h) := by
    rw [covered_eq]
    exact Finset.mem_sdiff.mpr ⟨by simp [toy], hb⟩
  have he : toy.ground \ toy.covered
      (insert (chosen h) (selected toy 1 (recordProposals propose) h)) =
      (toy.ground \ toy.covered (selected toy 1 (recordProposals propose) h)).erase (chosen h) := by
    ext i
    simp only [covered_eq, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    tauto
  simp only [productive, decide_eq_true_eq]
  change (toy.ground \ toy.covered (selected toy 1 (recordProposals propose)
    (some (chosen h, 0) :: h))).card ≤
      (toy.ground \ toy.covered (selected toy 1 (recordProposals propose) h)).card - 1
  rw [selected_zero h _ hb, he, Finset.card_erase_of_mem hm]

private theorem envelopes (u : ℕ) :
    Discrete.UpperBounds toy 1 propose select respond charge duration u 1
      DiscreteRetention.half 2 1 where
  charge_nonneg := by intro h b x; dsimp [charge, DiscreteRetention.charge]; positivity
  progress := by
    intro t ht h hh hc b hb
    have he : b = chosen (PMF.seqHistory h) := by simpa [select] using hb
    subst b
    have hm : (respond (PMF.seqHistory h) (chosen (PMF.seqHistory h))).toOuterMeasure {0} ≤
        (respond (PMF.seqHistory h) (chosen (PMF.seqHistory h))).toOuterMeasure
          {x | productive toy 1 (recordProposals propose) 1
            (PMF.seqHistory h) (some (chosen (PMF.seqHistory h), x)) = true} := by
      apply measure_mono
      intro x hx
      have hx' : x = 0 := hx
      subst x
      exact productive_zero _ hc
    apply le_trans _ (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) hm)
    rw [PMF.toOuterMeasure_apply_singleton]
    change (DiscreteRetention.half : ℝ) ≤ (DiscreteRetention.law [] 0).toReal
    rw [DiscreteRetention.law_apply]
    norm_num [DiscreteRetention.half]
  cost := by
    intro t ht h hh hc b hb
    simpa [respond, charge] using (DiscreteRetention.charge_mean []).le
  time := by
    intro t ht h hh hc b hb x hx
    norm_num [duration]

-- Batch choice changes with the actual residual obligation, rather than a clock.
example : chosen [] = 0 ∧ chosen [some (0, 0)] = 1 := by
  have hs := selected_zero [] 0 (by simp [selected])
  constructor
  · simp [chosen, selected]
  · unfold chosen
    rw [hs]
    simp [selected]

-- The law's actual unbounded records retain the response-dependent invoice.
example (N : ℕ) : ∃ z ∈ (Discrete.retainingLaw toy 1 propose select respond []).support,
    (N : ℝ) < recordResource charge [] z := by
  refine ⟨some (0, N + 1), ?_, ?_⟩
  · have hc : toy.covered (selected toy 1 (recordProposals propose) []) ≠ toy.ground := by
      rw [selected, covered_eq]
      intro he
      have hn := congrArg Finset.card he
      norm_num [toy] at hn
    simp only [Discrete.retainingLaw_eq, List.not_mem_nil, false_or, ite_eq_right hc]
    simp only [select, chosen, selected, Finset.notMem_empty, PMF.pure_bind]
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨N + 1, ne_of_gt (DiscreteRetention.law_pos _), rfl⟩
  · simp only [recordResource_some, charge, DiscreteRetention.charge, Nat.cast_add, Nat.cast_one]
    linarith

-- The returned family, its dual certificate and actual physical deadline are joint.
example (u : ℕ) :
    1 - (ProbabilityTheory.binomial u DiscreteRetention.half).real (Set.Iio 2) ≤
      ((PMF.seqProcess (responseStep (Discrete.retainingLaw toy 1 propose select respond))
        u).toOuterMeasure {h |
          toy.covered (selected toy 1 (recordProposals propose) (PMF.seqHistory h)) = toy.ground ∧
          toy.cost (selected toy 1 (recordProposals propose) (PMF.seqHistory h)) ≤
            ∑ e ∈ toy.ground, toy.dual e ∧
          accruedBill (recordResource duration) (PMF.seqHistory h) ≤ u}).toReal := by
  simpa only [CertifiedOutput, one_mul, mul_one] using Discrete.certified_success toy 1
    propose select respond
    charge duration u 1 2 (by norm_num [toy]) DiscreteRetention.half 2 1 u
    (by norm_num) (by norm_num) (envelopes u)

-- Actual raw invoices stop with the policy, yielding the two-success envelope.
example (u : ℕ) :
    (∑' h, PMF.seqProcess (responseStep (Discrete.retainingLaw toy 1 propose select respond)) u h *
      ENNReal.ofReal (accruedBill (recordResource charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (2 * min (u : ℝ) 4) := by
  have hb := Discrete.cost_le_mean toy 1 propose select respond charge duration u 1 2
    (by norm_num [toy]) DiscreteRetention.half (by norm_num [DiscreteRetention.half])
    2 1 (by norm_num) (envelopes u)
  norm_num [DiscreteRetention.half] at hb ⊢
  exact hb

end CslibFrontierTests.DiscreteBatches
