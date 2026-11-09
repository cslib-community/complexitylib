/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveStopping
public import CslibFrontier.Probability.StochasticOracle.AdaptiveLowerCost

/-!
# Arbitrary randomized selection-only policies

Finite-alphabet semantic policies for [Wang2027], Theorem 5(2), PDF p. 12,
Appendix A.5, p. 16. The oracle is fixed while policies choose history-dependent
randomized batches, may halt early, and randomize their final output. `none` is an
absorbing halt record. Selection-only output may use every proposed set, including
locally uncertified proposals. No local retention rule is imposed on this class.

This is a behavioral finite-kernel model, not an encoded PTM realization theorem.

## Main definitions

* `Oracle`, `Policy`, `Admissible`: fixed environment, arbitrary behavioral policies and provenance.
* `LowerBounds`, `UniversalBounds`: local supported contracts and universal quantification.

## Main results

* `conditional_means`: derive issued/progress/token conditional accounting from batch envelopes.
* `success_le_count_tail`: derive the revealed-progress bridge for arbitrary supported output.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open Cslib.Optimization.OneConstraint AdaptiveSelection PartialCover Finset MeasureTheory

variable {B R J E : Type} [Fintype B] [Fintype R] [Fintype J]
  [DecidableEq J] [DecidableEq E]

/-- Full records retain the chosen batch and its response; `none` is a halt. -/
abbrev Record (B R : Type) := Option (B × R)

/-- Fixed history-dependent oracle, shared by all competing policies. -/
structure Oracle (B R J : Type) [Fintype R] where
  /-- Response law after selecting a batch. -/
  respond : List (Record B R) → B → Distribution R ℝ
  /-- All valid proposals, irrespective of later local certification. -/
  proposed : List (Record B R) → B → R → List (Finset J)
  /-- Actual response-dependent token charge. -/
  charge : List (Record B R) → B → R → ℝ
  /-- Actual response-dependent physical latency. -/
  duration : List (Record B R) → B → R → ℝ
  /-- Token charges are nonnegative. -/
  charge_nonneg : ∀ h b x, 0 ≤ charge h b x
  /-- Physical latencies are nonnegative. -/
  duration_nonneg : ∀ h b x, 0 ≤ duration h b x

/-- An arbitrary adaptive randomized behavioral policy and terminal output kernel.
Admissibility is separate: output may not fabricate sets that were never proposed. -/
structure Policy (B R J : Type) [Fintype B] [Fintype J] where
  /-- Select a batch or halt, conditional on the full record history. -/
  choose : List (Record B R) → Distribution (Option B) ℝ
  /-- Randomized final extraction from buffered proposals. -/
  output : List (Record B R) → Distribution (Finset J) ℝ

open scoped Classical in
/-- Draw a selected batch and then its actual response. After a halt there is no
further oracle call or information: every later record is the same halt token. -/
@[expose] def law (O : Oracle B R J) (π : Policy B R J) (h : List (Record B R)) :
    Distribution (Record B R) ℝ :=
  if none ∈ h then Distribution.pure none else
    (π.choose h).bind fun b => match b with
      | none => Distribution.pure none
      | some b => (O.respond h b).map (fun x => some (b, x))

/-- Proposal decoder for the existing revealed-set and comparison APIs. -/
@[expose] def proposals (O : Oracle B R J) (h : List (Record B R)) :
    Record B R → List (Finset J)
  | none => []
  | some (b, x) => O.proposed h b x

/-- Token billing stops with the actual policy, independently of retained coverage. -/
@[expose] def bill (O : Oracle B R J) (h : List (Record B R)) : Record B R → ℝ
  | none => 0
  | some (b, x) => O.charge h b x

/-- Physical latency of a call record; halt records take no oracle latency. -/
@[expose] def latency (O : Oracle B R J) (h : List (Record B R)) : Record B R → ℝ
  | none => 0
  | some (b, x) => O.duration h b x

/-- Whether a record is an issued call, rather than a halt token. -/
@[expose] def issued (_ : List (Record B R)) (x : Record B R) : Bool := x.isSome

/-- Every proposed set is available for buffering and final extraction. -/
@[expose] def available (O : Oracle B R J) : List (Record B R) → Finset J
  | [] => ∅
  | x :: h => (proposals O h x).foldr (· ∪ ·) ∅ ∪ available O h

/-- Selection-only admissibility constrains only supported transcripts and outputs.
It permits arbitrary output extraction and no local dual-certification requirement. -/
@[expose] def Admissible (O : Oracle B R J) (π : Policy B R J) : Prop :=
  ∀ h, Reachable (law O π) h → ∀ C, 0 < (π.output h).weight C → C ⊆ available O h

/-- Deadline-and-turn feasibility of a policy run: every supported transcript at
its finite decision budget has finished its issued calls by D. Halt records cost
no physical time. For a finite alphabet this is the a.s. physical deadline condition. -/
@[expose] def DeadlineFeasible (O : Oracle B R J) (π : Policy B R J) (D : ℝ) (u : ℕ) : Prop :=
  ∀ h, Reachable (law O π) h → h.length = u → accruedBill (latency O) h ≤ D

/-- Actual success probability conditional on the terminal transcript, including
randomized output, full coverage, its certificate, and physical availability by D. -/
@[expose] def success (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (ρ D : ℝ) (h : List (Record B R)) : ℝ :=
  (π.output h).mean fun C =>
    if I.covered C = I.ground ∧ I.cost C ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
      accruedBill (latency O) h ≤ D then 1 else 0

/-- Actual probability of randomized certified output by D after at most u calls.
The history law is constructed from the policy and the fixed oracle. -/
@[expose] def successProbability (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (ρ D : ℝ) (u : ℕ) : ℝ :=
  historyExpectation (law O π) (success O π I ρ D) u []

/-- Expected actual policy token bill, including early halt. -/
@[expose] def expectedCost (O : Oracle B R J) (π : Policy B R J) (u : ℕ) : ℝ :=
  historyExpectation (law O π) (accruedBill (bill O)) u []

omit [DecidableEq J] in
/-- The actual finite response mean disintegrates into the policy selection and
conditional oracle response. Halt branches contribute their actual payoff. -/
theorem law_mean (O : Oracle B R J) (π : Policy B R J) (h : List (Record B R))
    (f : Record B R → ℝ) (hh : none ∉ h) :
    (law O π h).mean f = (π.choose h).mean (fun b => match b with
      | none => f none
      | some b => (O.respond h b).mean (fun x => f (some (b, x)))) := by
  simp only [law, hh, ite_false, Distribution.mean_bind]
  congr 1
  funext b
  cases b <;> simp [Distribution.mean_pure, Distribution.mean_map, Function.comp_def]

omit [DecidableEq J] in
/-- Supported call records have a positive selected-batch mass and response mass. -/
theorem law_weight_call (O : Oracle B R J) (π : Policy B R J)
    (h : List (Record B R)) (hh : none ∉ h) (b : B) (x : R) :
    (law O π h).weight (some (b, x)) = (π.choose h).weight (some b) * (O.respond h b).weight x := by
  classical
  simp [law, hh, Distribution.bind, Distribution.map, Distribution.pure, ite_and, mul_ite,
    Fintype.sum_option]

omit [DecidableEq J] in
/-- A supported call cannot occur after a halt. -/
theorem active_of_call (O : Oracle B R J) (π : Policy B R J)
    (h : List (Record B R)) (b : B) (x : R)
    (hx : 0 < (law O π h).weight (some (b, x))) : none ∉ h := by
  intro hh
  simp [law, hh, Distribution.pure] at hx

omit [Fintype B] [Fintype J] in
/-- Revealed coverage includes all buffered proposals, not only retained ones. -/
theorem covered_available (O : Oracle B R J) (I : Instance E J) (h : List (Record B R)) :
    I.covered (available O h) = revealed I (proposals O) h := by
  induction h with
  | nil => simp [available, revealed, Instance.covered]
  | cons x h ih =>
    simpa only [available, revealed, Instance.covered_union] using
      (congrArg (fun C => I.covered ((proposals O h x).foldr (· ∪ ·) ∅) ∪ C) ih)

/-- Source per-selected-batch lower limitations for one arbitrary policy. All
conditions concern positive-mass selections at supported histories before halt. -/
structure LowerBounds (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b : ℕ) (p c ℓ : ℝ) : Prop where
  /-- Revealed progress counts all proposals, including unretained sets. -/
  progress : ∀ h, Reachable (law O π) h → none ∉ h → ∀ a,
    0 < (π.choose h).weight (some a) →
      (O.respond h a).mean (fun x =>
        if reveals I (proposals O) h (some (a, x)) then 1 else 0) ≤ p
  /-- No supported call can reveal more than b new elements. -/
  coverage : ∀ h, Reachable (law O π) h → none ∉ h → ∀ a,
    0 < (π.choose h).weight (some a) → ∀ x, 0 < (O.respond h a).weight x →
      (revealed I (proposals O) (some (a, x) :: h) \ revealed I (proposals O) h).card ≤ b
  /-- Uniform conditional expected token-cost lower bound per issued batch. -/
  cost : ∀ h, Reachable (law O π) h → none ∉ h → ∀ a,
    0 < (π.choose h).weight (some a) → c ≤ (O.respond h a).mean (O.charge h a)
  /-- Physical latency lower bound almost surely for each selected batch. -/
  time : ∀ h, Reachable (law O π) h → none ∉ h → ∀ a,
    0 < (π.choose h).weight (some a) → ∀ x, 0 < (O.respond h a).weight x → ℓ ≤ O.duration h a x

/-- Universal quantification over the actual policy class, not over retention
algorithms alone. This predicate contains only the source's local envelopes. -/
@[expose] def UniversalBounds (O : Oracle B R J) (I : Instance E J) (b : ℕ) (p c ℓ : ℝ) : Prop :=
  ∀ π : Policy B R J, Admissible O π → LowerBounds O π I b p c ℓ

omit [Fintype B] [Fintype J] in
theorem reveals_none (O : Oracle B R J) (I : Instance E J)
    (h : List (Record B R)) : reveals I (proposals O) h none = false := by
  simp [reveals, revealed, proposals, Instance.covered]

/-- Local source envelopes give the actual conditional unnormalized progress/cost
inequalities, including randomized halt decisions. No division on null selections. -/
theorem conditional_means (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b : ℕ) (p c ℓ : ℝ) (H : LowerBounds O π I b p c ℓ)
    (h : List (Record B R)) (hh : Reachable (law O π) h) :
    (law O π h).mean (fun x => if reveals I (proposals O) h x then 1 else 0) ≤
        p * (law O π h).mean (fun x => if issued h x then 1 else 0) ∧
      c * (law O π h).mean (fun x => if issued h x then 1 else 0) ≤
        (law O π h).mean (bill O h) := by
  classical
  by_cases hs : none ∈ h
  · simp [law, hs, Distribution.mean_pure, reveals_none, issued, bill]
  · have hi : (law O π h).mean (fun x => if issued h x then (1 : ℝ) else 0) =
        (π.choose h).mean (fun a => if a.isSome then 1 else 0) := by
      rw [law_mean O π h _ hs]
      congr 1
      funext a
      cases a <;> simp [issued, Distribution.mean_const]
    rw [hi, law_mean O π h _ hs, law_mean O π h _ hs]
    constructor
    · simp only [Distribution.mean, Finset.mul_sum]
      apply sum_le_sum
      intro a _
      cases a with
      | none => simp [reveals_none]
      | some a =>
        by_cases ha : (π.choose h).weight (some a) = 0
        · simp [ha]
        · have hb := H.progress h hh hs a
            (lt_of_le_of_ne ((π.choose h).nonneg _) (Ne.symm ha))
          simpa only [Option.isSome_some, ite_true, mul_one, mul_comm p, Distribution.mean]
            using mul_le_mul_of_nonneg_left hb ((π.choose h).nonneg (some a))
    · simp only [Distribution.mean, Finset.mul_sum]
      apply sum_le_sum
      intro a _
      cases a with
      | none => simp [bill]
      | some a =>
        by_cases ha : (π.choose h).weight (some a) = 0
        · simp [ha]
        · have hb := H.cost h hh hs a
            (lt_of_le_of_ne ((π.choose h).nonneg _) (Ne.symm ha))
          simpa only [bill, Option.isSome_some, ite_true, mul_one, mul_comm c, Distribution.mean]
            using mul_le_mul_of_nonneg_left hb ((π.choose h).nonneg (some a))

/-- The source revealed-size cap is only needed on supported response branches. -/
theorem revealed_card_le_supported (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (b : ℕ) (p c ℓ : ℝ) (H : LowerBounds O π I b p c ℓ)
    (h : List (Record B R)) (hh : Reachable (law O π) h) :
    (revealed I (proposals O) h).card ≤ b * count (reveals I (proposals O)) h := by
  induction hh with
  | nil => simp [revealed, count]
  | @cons h x hh hx ih =>
    have hm : revealed I (proposals O) h ⊆ revealed I (proposals O) (x :: h) :=
      subset_union_right
    have he := card_sdiff_add_card_eq_card hm
    have hcap : (revealed I (proposals O) (x :: h) \ revealed I (proposals O) h).card ≤ b := by
      cases x with
      | none => simp [revealed, proposals, Instance.covered]
      | some z =>
        rcases z with ⟨a, x⟩
        have hs := active_of_call O π h a x hx
        rw [law_weight_call O π h hs] at hx
        exact H.coverage h hh hs a
          (pos_of_mul_pos_left hx ((O.respond h a).nonneg x)) x
          (pos_of_mul_pos_right hx ((π.choose h).nonneg (some a)))
    by_cases hr : reveals I (proposals O) h x = true
    · simp only [count, hr, ite_true, Nat.mul_add, Nat.mul_one]
      omega
    · have hz : (revealed I (proposals O) (x :: h) \ revealed I (proposals O) h).card = 0 := by
        simpa only [reveals, decide_eq_true_eq, not_nonempty_iff_eq_empty, card_eq_zero] using hr
      simpa only [count, hr, Bool.false_eq_true, ite_false, Nat.add_zero] using
        (show (revealed I (proposals O) (x :: h)).card ≤
          b * count (reveals I (proposals O)) h by omega)

/-- Selection-only successful output forces the required number of revealed-progress
turns, derived from actual proposals rather than an assumed count bridge. -/
theorem success_le_count_tail (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (hA : Admissible O π) (b r : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (p c ℓ ρ D : ℝ) (H : LowerBounds O π I b p c ℓ)
    (h : List (Record B R)) (hh : Reachable (law O π) h) :
    success O π I ρ D h ≤ if r ≤ count (reveals I (proposals O)) h then 1 else 0 := by
  classical
  rw [success, ← (π.output h).mean_const
    (if r ≤ count (reveals I (proposals O)) h then (1 : ℝ) else 0)]
  apply sum_le_sum
  intro C _
  by_cases hw : (π.output h).weight C = 0
  · simp [hw]
  · apply mul_le_mul_of_nonneg_left _ ((π.output h).nonneg C)
    dsimp only
    by_cases hs : I.covered C = I.ground ∧ I.cost C ≤ ρ * ∑ e ∈ I.ground, I.dual e ∧
        accruedBill (latency O) h ≤ D
    · have hsub := hA h hh C (lt_of_le_of_ne ((π.output h).nonneg C) (Ne.symm hw))
      have hc : I.ground ⊆ revealed I (proposals O) h := by
        rw [← covered_available O I, ← hs.1]
        exact Finset.biUnion_subset_biUnion_of_subset_left I.sets hsub
      have hb := (card_le_card hc).trans (revealed_card_le_supported O π I b p c ℓ H h hh)
      have ht : r ≤ count (reveals I (proposals O)) h := by
        by_contra ht
        have hn := hr _ (Nat.lt_of_not_ge ht)
        omega
      simp [hs, ht]
    · simp only [hs, ite_false]
      split_ifs <;> norm_num

omit [Fintype B] [Fintype R] in
/-- Real accrued indicator charges are the actual integer progress counts. -/
theorem accrued_indicator_eq_count (f : List (Record B R) → Record B R → Bool)
    (h : List (Record B R)) :
    accruedBill (fun h x => if f h x then (1 : ℝ) else 0) h = count f h := by
  induction h with
  | nil => simp [accruedBill, count]
  | cons x h ih =>
    simp only [accruedBill, count, ih, Nat.cast_add]
    split_ifs <;> simp

omit [DecidableEq J] in
/-- Randomized certified-output success is an actual probability in [0,1]. -/
theorem success_bounds (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (ρ D : ℝ) (h : List (Record B R)) : 0 ≤ success O π I ρ D h ∧ success O π I ρ D h ≤ 1 := by
  classical
  constructor
  · apply sum_nonneg
    intro C _
    exact mul_nonneg ((π.output h).nonneg C) (by dsimp only; split_ifs <;> norm_num)
  · calc
      _ ≤ (π.output h).mean (fun _ => 1) := by
        apply sum_le_sum
        intro C _
        apply mul_le_mul_of_nonneg_left _ ((π.output h).nonneg C)
        dsimp only
        split_ifs <;> norm_num
      _ = 1 := Distribution.mean_const (π.output h) 1

omit [DecidableEq J] in
/-- A transcript that exceeds D cannot report deadline success, regardless of the
randomized output kernel or any buffered proposals. -/
theorem success_eq_zero_of_late (O : Oracle B R J) (π : Policy B R J) (I : Instance E J)
    (ρ D : ℝ) (h : List (Record B R)) (hh : ¬accruedBill (latency O) h ≤ D) :
    success O π I ρ D h = 0 := by
  classical
  simp [success, Distribution.mean, hh]

end Cslib.Probability.StochasticOracle.SelectionPolicy
