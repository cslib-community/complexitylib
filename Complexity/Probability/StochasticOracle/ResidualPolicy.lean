/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.ResidualCover
public import Complexity.Probability.FiniteTable
import Mathlib.Tactic

/-!
# Universal one- and two-turn residual policies

[Wang2027], Theorem 6 and proof, PDF p. 13. Each opportunity is usable once;
batches are concurrent and each nonempty batch takes one physical turn. The sole
random oracle answer is the full-support missing-block index of the near cover.
It is decoded from the actual residual by `decode_near_residual`.

Policies randomize their first batch, their response-dependent second batch, and
their final selection-only extraction. First batches containing both the near cover
and specialists are included. These are arbitrary finite behavioral kernels on the
complete response observations. An encoded-PTM representation/realization theorem
is not supplied here.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ResidualCover
open Finset Cslib.Optimization.OneConstraint PartialCover
variable {z : ℕ} {T : Fin z → Block}

/-- The available opportunities: near cover (`none`) and one specialist per block. -/
abbrev Call (z : ℕ) := Option (Fin z)
/-- A concurrent batch, with no repeated opportunity inside it. -/
abbrev Batch (z : ℕ) := Finset (Call z)

/-- Positive source probability law and opportunity token costs. -/
structure Parameters (z : ℕ) where
  /-- Distribution of the missing block. -/
  missing : Distribution (Fin z) ℝ
  /-- Every possible residual has positive probability. -/
  full_support : ∀ j, 0 < missing.weight j
  /-- Near-cover opportunity cost. -/
  nearCost : ℝ
  /-- Positive near-cover cost. -/
  near_pos : 0 < nearCost
  /-- Specialist opportunity costs. -/
  specialistCost : Fin z → ℝ
  /-- Positive specialist costs. -/
  specialist_pos : ∀ j, 0 < specialistCost j

variable (P : Parameters z)

/-- Actual batch charge: every issued call is billed, including concurrent calls. -/
@[expose] def batchCost (A : Batch z) : ℝ :=
  (if none ∈ A then P.nearCost else 0) + ∑ j : Fin z, if some j ∈ A then P.specialistCost j else 0

open scoped Classical in
/-- The first response distinguishes a near-cover residual only if that call was
actually issued. Specialist answers are deterministic for the fixed constructed instance. -/
@[expose] def reply (A : Batch z) : Distribution (Option (Fin z)) ℝ :=
  if none ∈ A then P.missing.map some else Distribution.pure none

/-- Blocks covered by actual responses, including every issued specialist and the
near-cover answer if present. -/
@[expose] def received (A : Batch z) (r : Option (Fin z)) : Finset (Fin z) :=
  univ.filter (fun j => some j ∈ A) ∪ r.elim ∅ (fun j => univ.erase j)

/-- General one-turn randomized selection and final extraction. -/
structure OnePolicy (T : Fin z → Block) where
  /-- Arbitrary randomized concurrent batch. -/
  first : Distribution (Batch z) ℝ
  /-- Arbitrary randomized extraction from the observed response. -/
  output : Batch z → Option (Fin z) → Distribution (Finset (Candidate T)) ℝ

/-- General two-turn behavioral policy, allowing arbitrary private randomization
through conditional tables and all specialist/near-cover first-batch mixtures. -/
structure TwoPolicy (T : Fin z → Block) where
  /-- First batch, possibly empty. -/
  first : Distribution (Batch z) ℝ
  /-- Second batch can depend on the first batch and the complete first response. -/
  second : Batch z → Option (Fin z) → Distribution (Batch z) ℝ
  /-- Final randomized extraction sees both actual responses. -/
  output : Batch z → Option (Fin z) → Batch z → Option (Fin z) →
    Distribution (Finset (Candidate T)) ℝ

/-- Actual one-turn response/output distribution, not a supplied terminal law. -/
@[expose] def OnePolicy.run (π : OnePolicy T) :
    Distribution (Batch z × Option (Fin z) × Finset (Candidate T)) ℝ :=
  π.first.bind fun A => (reply P A).bind fun r => (π.output A r).map fun C => (A, r, C)

/-- Actual two-turn distribution: future selections cannot inspect a near-cover
answer that has not yet been sampled. -/
@[expose] def TwoPolicy.run (π : TwoPolicy T) :
    Distribution (Batch z × Option (Fin z) × Batch z × Option (Fin z) × Finset (Candidate T)) ℝ :=
  π.first.bind fun A => (reply P A).bind fun r => (π.second A r).bind fun B =>
    (reply P B).bind fun s => (π.output A r B s).map fun C => (A, r, B, s, C)

/-- One-turn selection-only provenance, only on supported branches. -/
@[expose] def OnePolicy.Admissible (π : OnePolicy T) : Prop :=
  ∀ A r C, 0 < π.first.weight A → 0 < (reply P A).weight r →
    0 < (π.output A r).weight C → C ⊆ payload T (received A r)

/-- No opportunity reuse and selection-only final output; no retention algorithm
or desired coverage/optimality condition is a field. -/
@[expose] def TwoPolicy.Admissible (π : TwoPolicy T) : Prop :=
  ∀ A r B, 0 < π.first.weight A → 0 < (reply P A).weight r →
    0 < (π.second A r).weight B → Disjoint A B ∧
      ∀ s C, 0 < (reply P B).weight s → 0 < (π.output A r B s).weight C →
        C ⊆ payload T (received A r ∪ received B s)

open scoped Classical in
/-- Returning an actual optimal cover is checked against the constructed WSC
instance and the independently proved weight-one optimum. -/
@[expose] def optimalOutput (hz : 0 < z) (C : Finset (Candidate T)) : ℝ :=
  if (coverInstance T hz).covered C = (coverInstance T hz).ground ∧
    (coverInstance T hz).cost C = 1 then 1 else 0

/-- The success test is equivalent to actual optimality among all integral
covers of the constructed instance. The optimum value is derived from the
construction, rather than an input certificate or a supplied optimum premise. -/
theorem optimalOutput_eq_one_iff (hz : 0 < z) (C : Finset (Candidate T)) :
    optimalOutput hz C = 1 ↔
      (coverInstance T hz).covered C = (coverInstance T hz).ground ∧
      ∀ D, (coverInstance T hz).covered D = (coverInstance T hz).ground →
        (coverInstance T hz).cost C ≤ (coverInstance T hz).cost D := by
  classical
  have he : optimalOutput hz C = 1 ↔
      (coverInstance T hz).covered C = (coverInstance T hz).ground ∧
      (coverInstance T hz).cost C = 1 := by
    simp [optimalOutput]
  rw [he]
  constructor
  · rintro ⟨hC, hc⟩
    refine ⟨hC, fun D hD => ?_⟩
    rw [hc]
    exact (primal_optimum T hz).2.2 D hD
  · rintro ⟨hC, hmin⟩
    refine ⟨hC, le_antisymm ?_ ((primal_optimum T hz).2.2 C hC)⟩
    have h := hmin (payload T univ) (primal_optimum T hz).1
    rwa [(primal_optimum T hz).2.1] at h

/-- Actual probability of optimal output after one physical batch. -/
@[expose] def OnePolicy.success (π : OnePolicy T) (hz : 0 < z) : ℝ :=
  (π.run P).mean (fun (_, _, C) => optimalOutput (T := T) hz C)
/-- Actual expected issued token cost in one turn. -/
@[expose] def OnePolicy.cost (π : OnePolicy T) : ℝ := (π.run P).mean (fun t => batchCost P t.1)
/-- Actual probability of optimal output within two physical batches. -/
@[expose] def TwoPolicy.success (π : TwoPolicy T) (hz : 0 < z) : ℝ :=
  (π.run P).mean (fun (_, _, _, _, C) => optimalOutput (T := T) hz C)
/-- Actual expected token cost, including both concurrent batches. -/
@[expose] def TwoPolicy.cost (π : TwoPolicy T) : ℝ :=
  (π.run P).mean (fun (A, _, B, _, _) => batchCost P A + batchCost P B)

private theorem bind_pos {α β : Type} [Fintype α] [Fintype β]
    (w : Distribution α ℝ) (k : α → Distribution β ℝ) (a : α) (b : β)
    (ha : 0 < w.weight a) (hb : 0 < (k a).weight b) : 0 < (w.bind k).weight b := by
  have h := (Distribution.mem_support_bind w k b).mpr
    ⟨a, mem_filter.mpr ⟨mem_univ a, ha⟩, mem_filter.mpr ⟨mem_univ b, hb⟩⟩
  exact (mem_filter.mp h).2

private theorem map_pos {α β : Type} [Fintype α] [Fintype β]
    (w : Distribution α ℝ) (f : α → β) (a : α) (ha : 0 < w.weight a) :
    0 < (w.map f).weight (f a) := by
  have h := (Distribution.mem_support_map w f (f a)).mpr
    ⟨a, mem_filter.mpr ⟨mem_univ a, ha⟩, rfl⟩
  exact (mem_filter.mp h).2

/-- Sure actual output forces every supported received-block collection to cover
all blocks. The coverage bridge follows from provenance and the constructed instance. -/
theorem OnePolicy.received_all (π : OnePolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1)
    (A : Batch z) (r : Option (Fin z)) (ha : 0 < π.first.weight A) (hr : 0 < (reply P A).weight r) :
    received A r = univ := by
  classical
  obtain ⟨C, hC⟩ := (π.output A r).support_nonempty
  have hc : 0 < (π.output A r).weight C := (mem_filter.mp hC).2
  have ht : 0 < (π.run P).weight (A, r, C) := by
    unfold OnePolicy.run
    apply bind_pos π.first _ A _ ha
    apply bind_pos (reply P A) _ r _ hr
    exact map_pos (π.output A r) (fun C => (A, r, C)) C hc
  have ho := (Distribution.mean_eq_iff_of_le (π.run P) _ 1
    (fun t _ => by dsimp only [optimalOutput]; split_ifs <;> norm_num)).mp hS
      (A, r, C) (by simp [Distribution.support, ht])
  have hcover : (coverInstance T hz).covered C = (coverInstance T hz).ground := by
    have hp : (coverInstance T hz).covered C = (coverInstance T hz).ground ∧
        (coverInstance T hz).cost C = 1 := by
      simpa only [optimalOutput, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using ho
    exact hp.1
  apply (payload_covers_iff T hz _).mp
  apply Subset.antisymm ((coverInstance T hz).covered_subset _)
  rw [← hcover]
  exact biUnion_subset_biUnion_of_subset_left _ (hA A r C ha hr hc)

/-- The same provenance bridge for every supported two-turn branch, including
mixed first batches and randomized final extraction. -/
theorem TwoPolicy.received_all (π : TwoPolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1)
    (A B : Batch z) (r s : Option (Fin z)) (ha : 0 < π.first.weight A)
    (hr : 0 < (reply P A).weight r) (hb : 0 < (π.second A r).weight B)
    (hs : 0 < (reply P B).weight s) : received A r ∪ received B s = univ := by
  classical
  obtain ⟨C, hC⟩ := (π.output A r B s).support_nonempty
  have hc : 0 < (π.output A r B s).weight C := (mem_filter.mp hC).2
  have ht : 0 < (π.run P).weight (A, r, B, s, C) := by
    unfold TwoPolicy.run
    apply bind_pos π.first _ A _ ha
    apply bind_pos (reply P A) _ r _ hr
    apply bind_pos (π.second A r) _ B _ hb
    apply bind_pos (reply P B) _ s _ hs
    exact map_pos (π.output A r B s) (fun C => (A, r, B, s, C)) C hc
  have ho := (Distribution.mean_eq_iff_of_le (π.run P) _ 1
    (fun t _ => by dsimp only [optimalOutput]; split_ifs <;> norm_num)).mp hS
      (A, r, B, s, C) (by simp [Distribution.support, ht])
  have hcover : (coverInstance T hz).covered C = (coverInstance T hz).ground := by
    have hp : (coverInstance T hz).covered C = (coverInstance T hz).ground ∧
        (coverInstance T hz).cost C = 1 := by
      simpa only [optimalOutput, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using ho
    exact hp.1
  apply (payload_covers_iff T hz _).mp
  apply Subset.antisymm ((coverInstance T hz).covered_subset _)
  rw [← hcover]
  exact biUnion_subset_biUnion_of_subset_left _ ((hA A r B ha hr hb).2 s C hs hc)

private theorem mean_lower {α : Type} [Fintype α] (w : Distribution α ℝ)
    (f : α → ℝ) (m : ℝ) (hm : ∀ a, 0 < w.weight a → m ≤ f a) : m ≤ w.mean f := by
  obtain ⟨a, ha, h⟩ := w.exists_support_le_mean f
  exact (hm a (mem_filter.mp ha).2).trans h

private theorem batchCost_nonneg (A : Batch z) : 0 ≤ batchCost P A := by
  classical
  unfold batchCost
  apply add_nonneg
  · split_ifs <;> linarith [P.near_pos]
  · exact sum_nonneg fun j _ => by split_ifs <;> linarith [P.specialist_pos j]

private theorem specialist_le_batch (A : Batch z) (j : Fin z) (hj : some j ∈ A) :
    P.specialistCost j ≤ batchCost P A := by
  classical
  have he := single_le_sum (fun k (_ : k ∈ (univ : Finset (Fin z))) =>
    show 0 ≤ if some k ∈ A then P.specialistCost k else 0 by
      split_ifs <;> linarith [P.specialist_pos k]) (mem_univ j)
  rw [ite_eq_left hj] at he
  unfold batchCost
  split_ifs <;> linarith [P.near_pos]

/-- Actual one-turn cost reduces to its randomized first-batch charge. -/
theorem OnePolicy.cost_eq (π : OnePolicy T) : π.cost P = π.first.mean (batchCost P) := by
  simp [OnePolicy.cost, OnePolicy.run, Distribution.mean_bind, Distribution.mean_map,
    Function.comp_def, Distribution.mean_const]

/-- Actual two-turn cost is the history-conditional tower sum. -/
theorem TwoPolicy.cost_eq (π : TwoPolicy T) : π.cost P = π.first.mean
    (fun A => batchCost P A + (reply P A).mean (fun r => (π.second A r).mean (batchCost P))) := by
  simp [TwoPolicy.cost, TwoPolicy.run, Distribution.mean_bind, Distribution.mean_map,
    Function.comp_def, Distribution.mean_const, Distribution.mean_add]

/-- Probability-one one-turn completion forces every specialist in each supported
first batch, despite arbitrary initial and output randomization. -/
theorem OnePolicy.all_specialists (π : OnePolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1) (A : Batch z)
    (ha : 0 < π.first.weight A) (j : Fin z) : some j ∈ A := by
  classical
  by_contra hj
  by_cases hn : none ∈ A
  · have hr : 0 < (reply P A).weight (some j) := by
      simp only [reply, hn, ite_true]
      exact map_pos P.missing some j (P.full_support j)
    have he := π.received_all P hz hA hS A (some j) ha hr
    have hm : j ∈ received A (some j) := he ▸ mem_univ j
    simp [received, hj] at hm
  · have hr : 0 < (reply P A).weight none := by simp [reply, hn, Distribution.pure]
    have he := π.received_all P hz hA hS A none ha hr
    have hm : j ∈ received A none := he ▸ mem_univ j
    simp [received, hj] at hm

/-- Derived universal one-turn minimum lower bound. -/
theorem OnePolicy.lower_cost (π : OnePolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1) :
    (∑ j, P.specialistCost j) ≤ π.cost P := by
  classical
  rw [OnePolicy.cost_eq]
  apply mean_lower
  intro A ha
  have hs := π.all_specialists P hz hA hS A ha
  simp only [batchCost, hs, ite_true]
  split_ifs <;> linarith [P.near_pos]

private theorem combined_cost (A B : Batch z) (h : ∀ j, some j ∈ A ∨ some j ∈ B) :
    (∑ j, P.specialistCost j) ≤ batchCost P A + batchCost P B := by
  classical
  have hs : (∑ j, P.specialistCost j) ≤
      (∑ j, if some j ∈ A then P.specialistCost j else 0) +
      (∑ j, if some j ∈ B then P.specialistCost j else 0) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro j _
    have hj := h j
    split_ifs <;> simp_all; linarith [P.specialist_pos j]
  have ha : 0 ≤ if none ∈ A then P.nearCost else 0 := by split_ifs <;> linarith [P.near_pos]
  have hb : 0 ≤ if none ∈ B then P.nearCost else 0 := by split_ifs <;> linarith [P.near_pos]
  unfold batchCost
  linarith

/-- If no near cover was sampled in turn one, a turn-two near-cover response
cannot guide another simultaneous call. Every specialist is therefore necessary. -/
theorem TwoPolicy.no_near_first (π : TwoPolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1) (A : Batch z)
    (ha : 0 < π.first.weight A) (hn : none ∉ A) :
    (∑ j, P.specialistCost j) ≤ batchCost P A +
      (reply P A).mean (fun r => (π.second A r).mean (batchCost P)) := by
  classical
  have hr : 0 < (reply P A).weight none := by simp [reply, hn, Distribution.pure]
  rw [reply, ite_eq_right hn, Distribution.mean_pure]
  have hb : (∑ j, P.specialistCost j) - batchCost P A ≤
      (π.second A none).mean (batchCost P) := by
    apply mean_lower
    intro B hB
    have hall : ∀ j, some j ∈ A ∨ some j ∈ B := by
      intro j
      by_contra hj
      have hjA : some j ∉ A := by tauto
      have hjB : some j ∉ B := by tauto
      by_cases hnB : none ∈ B
      · have hs : 0 < (reply P B).weight (some j) := by
          simp only [reply, hnB, ite_true]
          exact map_pos P.missing some j (P.full_support j)
        have he := π.received_all P hz hA hS A B none (some j) ha hr hB hs
        have hm : j ∈ received A none ∪ received B (some j) := he ▸ mem_univ j
        simp [received, hjA, hjB] at hm
      · have hs : 0 < (reply P B).weight none := by simp [reply, hnB, Distribution.pure]
        have he := π.received_all P hz hA hS A B none none ha hr hB hs
        have hm : j ∈ received A none ∪ received B none := he ▸ mem_univ j
        simp [received, hjA, hjB] at hm
    linarith [combined_cost P A B hall]
  linarith

/-- If the first batch includes the near cover and any specialist subset A, each
still-missing residual forces its own turn-two specialist. No reuse is essential. -/
theorem TwoPolicy.near_first (π : TwoPolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1) (A : Batch z)
    (ha : 0 < π.first.weight A) (hn : none ∈ A) :
    P.nearCost + P.missing.mean P.specialistCost ≤ batchCost P A +
      (reply P A).mean (fun r => (π.second A r).mean (batchCost P)) := by
  classical
  have hnext (j : Fin z) : (if some j ∈ A then (0 : ℝ) else P.specialistCost j) ≤
      (π.second A (some j)).mean (batchCost P) := by
    apply mean_lower
    intro B hB
    by_cases hj : some j ∈ A
    · simp only [hj, ite_true]
      exact batchCost_nonneg P B
    · simp only [hj, ite_false]
      have hr : 0 < (reply P A).weight (some j) := by
        simp only [reply, hn, ite_true]
        exact map_pos P.missing some j (P.full_support j)
      have hdis := (hA A (some j) B ha hr hB).1
      have hnB : none ∉ B := fun h => (disjoint_left.mp hdis) hn h
      have hs : 0 < (reply P B).weight none := by simp [reply, hnB, Distribution.pure]
      have he := π.received_all P hz hA hS A B (some j) none ha hr hB hs
      have hm : j ∈ received A (some j) ∪ received B none := he ▸ mem_univ j
      have hjB : some j ∈ B := by simpa [received, hj] using hm
      exact specialist_le_batch P B j hjB
  have havg : P.missing.mean (fun j => if some j ∈ A then 0 else P.specialistCost j) ≤
      (reply P A).mean (fun r => (π.second A r).mean (batchCost P)) := by
    rw [reply, ite_eq_left hn, Distribution.mean_map]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hnext j) (P.missing.nonneg j)
  have hpre : P.missing.mean (fun j => if some j ∈ A then P.specialistCost j else 0) ≤
      ∑ j, if some j ∈ A then P.specialistCost j else 0 := by
    apply sum_le_sum
    intro j _
    have hp : P.missing.weight j ≤ 1 := by
      have hh := single_le_sum (fun k _ => P.missing.nonneg k) (mem_univ j)
      rwa [P.missing.total] at hh
    by_cases hj : some j ∈ A
    · simp only [hj, ite_true]
      exact mul_le_of_le_one_left (P.specialist_pos j).le hp
    · simp [hj]
  have hsplit : P.missing.mean P.specialistCost =
      P.missing.mean (fun j => if some j ∈ A then P.specialistCost j else 0) +
      P.missing.mean (fun j => if some j ∈ A then 0 else P.specialistCost j) := by
    rw [← Distribution.mean_add]
    congr 1
    funext j
    split_ifs <;> simp
  simp only [batchCost, hn, ite_true]
  linarith

/-- Universal two-turn lower optimum, including arbitrary randomization and mixed
near-cover/specialist first batches. -/
theorem TwoPolicy.lower_cost (π : TwoPolicy T) (hz : 0 < z)
    (hA : π.Admissible P) (hS : π.success P hz = 1) :
    min (∑ j, P.specialistCost j) (P.nearCost + P.missing.mean P.specialistCost) ≤ π.cost P := by
  classical
  rw [TwoPolicy.cost_eq]
  apply mean_lower
  intro A ha
  by_cases hn : none ∈ A
  · exact (min_le_right _ _).trans (π.near_first P hz hA hS A ha hn)
  · exact (min_le_left _ _).trans (π.no_near_first P hz hA hS A ha hn)

/-- All specialist opportunities, issued concurrently. -/
@[expose] def specialistBatch : Batch z := univ.erase none

/-- Source one-turn upper strategy: ask every specialist and return the received union. -/
@[expose] def allOne : OnePolicy T where
  first := Distribution.pure specialistBatch
  output A r := Distribution.pure (payload T (received A r))

/-- The same strategy is allowed with a two-turn budget, padding by an empty batch. -/
@[expose] def allTwo : TwoPolicy T where
  first := Distribution.pure specialistBatch
  second _ _ := Distribution.pure ∅
  output A r B s := Distribution.pure (payload T (received A r ∪ received B s))

/-- Source adaptive strategy: query near cover, decode its residual, then query the
one required specialist. Final output is the union of actual received indices. -/
@[expose] def adaptiveTwo : TwoPolicy T where
  first := Distribution.pure {none}
  second _ r := Distribution.pure (r.elim ∅ (fun j => {some j}))
  output A r B s := Distribution.pure (payload T (received A r ∪ received B s))

private theorem pure_pos_eq {α : Type} [Fintype α] (a b : α)
    (hb : 0 < (Distribution.pure a : Distribution α ℝ).weight b) : b = a := by
  exact (Distribution.mem_support_pure a b).mp (mem_filter.mpr ⟨mem_univ b, hb⟩)

/-- Actual upper outputs have selection-only provenance; opportunities are not reused. -/
theorem allOne_admissible : (allOne (T := T)).Admissible P := by
  intro A r C _ _ hc
  have he := pure_pos_eq _ _ hc
  subst C
  exact Subset.rfl

theorem allTwo_admissible : (allTwo (T := T)).Admissible P := by
  classical
  intro A r B _ _ hb
  have he := pure_pos_eq _ _ hb
  subst B
  refine ⟨by simp, ?_⟩
  intro s C _ hc
  have he := pure_pos_eq _ _ hc
  subst C
  exact Subset.rfl

theorem adaptiveTwo_admissible : (adaptiveTwo (T := T)).Admissible P := by
  classical
  intro A r B ha _ hb
  have he := pure_pos_eq _ _ ha
  subst A
  have he := pure_pos_eq _ _ hb
  subst B
  constructor
  · cases r <;> simp
  · intro s C _ hc
    have he := pure_pos_eq _ _ hc
    subst C
    exact Subset.rfl

private theorem optimal_full (hz : 0 < z) : optimalOutput (T := T) hz (payload T univ) = 1 := by
  simp [optimalOutput, (primal_optimum T hz).1, (primal_optimum T hz).2.1]

private theorem adaptive_received (j : Fin z) :
    received ({none} : Batch z) (some j) ∪ received {some j} none = univ := by
  classical
  ext k
  simp [received]
  tauto

/-- The one-turn witness really returns an actual optimal WSC cover surely. -/
theorem allOne_success (hz : 0 < z) : (allOne (T := T)).success P hz = 1 := by
  classical
  simp [OnePolicy.success, OnePolicy.run, allOne, reply, specialistBatch,
    Distribution.mean_bind, Distribution.mean_map, Distribution.mean_pure, Function.comp_def,
    received, optimal_full]

/-- Its exact token charge, independently of the WSC weight normalization. -/
theorem allOne_cost : (allOne (T := T)).cost P = ∑ j, P.specialistCost j := by
  classical
  rw [OnePolicy.cost_eq]
  simp [allOne, Distribution.mean_pure, batchCost, specialistBatch]

theorem allTwo_success (hz : 0 < z) : (allTwo (T := T)).success P hz = 1 := by
  classical
  simp [TwoPolicy.success, TwoPolicy.run, allTwo, reply, specialistBatch,
    Distribution.mean_bind, Distribution.mean_map, Distribution.mean_pure, Function.comp_def,
    received, optimal_full]

theorem allTwo_cost : (allTwo (T := T)).cost P = ∑ j, P.specialistCost j := by
  classical
  rw [TwoPolicy.cost_eq]
  simp [allTwo, reply, Distribution.mean_pure, batchCost, specialistBatch]

/-- Adaptive optimal output is certified by the actual constructed weight-one cover. -/
theorem adaptiveTwo_success (hz : 0 < z) : (adaptiveTwo (T := T)).success P hz = 1 := by
  classical
  simp [TwoPolicy.success, TwoPolicy.run, adaptiveTwo, reply,
    Distribution.mean_bind, Distribution.mean_map, Distribution.mean_pure,
    Distribution.mean_const, Function.comp_def, adaptive_received, optimal_full]

/-- The source residual-guided strategy has the derived expected token cost. -/
theorem adaptiveTwo_cost : (adaptiveTwo (T := T)).cost P =
    P.nearCost + P.missing.mean P.specialistCost := by
  classical
  rw [TwoPolicy.cost_eq]
  simp [adaptiveTwo, reply, Distribution.mean_pure, Distribution.mean_map,
    Function.comp_def, batchCost]

/-- Exact one-turn optimum: attained and no admissible randomized competitor is cheaper. -/
theorem one_turn_optimum (hz : 0 < z) :
    ∃ π : OnePolicy T, π.Admissible P ∧ π.success P hz = 1 ∧ π.cost P = ∑ j, P.specialistCost j ∧
      ∀ ψ : OnePolicy T, ψ.Admissible P → ψ.success P hz = 1 → π.cost P ≤ ψ.cost P := by
  refine ⟨allOne, allOne_admissible P, allOne_success P hz, allOne_cost P, ?_⟩
  intro ψ hA hS
  rw [allOne_cost]
  exact ψ.lower_cost P hz hA hS

/-- Exact two-turn optimum over every source-admissible randomized strategy. -/
theorem two_turn_optimum (hz : 0 < z) :
    ∃ π : TwoPolicy T, π.Admissible P ∧ π.success P hz = 1 ∧
      π.cost P = min (∑ j, P.specialistCost j) (P.nearCost + P.missing.mean P.specialistCost) ∧
      ∀ ψ : TwoPolicy T, ψ.Admissible P → ψ.success P hz = 1 → π.cost P ≤ ψ.cost P := by
  classical
  by_cases hc : (∑ j, P.specialistCost j) ≤ P.nearCost + P.missing.mean P.specialistCost
  · refine ⟨allTwo, allTwo_admissible P, allTwo_success P hz, ?_, ?_⟩
    · rw [allTwo_cost, min_eq_left hc]
    · intro ψ hA hS
      rw [allTwo_cost]
      simpa only [min_eq_left hc] using ψ.lower_cost P hz hA hS
  · refine ⟨adaptiveTwo, adaptiveTwo_admissible P, adaptiveTwo_success P hz, ?_, ?_⟩
    · rw [adaptiveTwo_cost, min_eq_right (le_of_not_ge hc)]
    · intro ψ hA hS
      rw [adaptiveTwo_cost]
      simpa only [min_eq_right (le_of_not_ge hc)] using ψ.lower_cost P hz hA hS

/-- Physical latency of a concurrent batch of unit-latency opportunities. -/
@[expose] def batchLatency (A : Batch z) : ℝ := if A.Nonempty then 1 else 0

/-- All policies in the one/two-batch models satisfy the corresponding physical
deadline, including empty batches and arbitrary randomization. -/
theorem unit_deadlines (A B : Batch z) :
    batchLatency A ≤ 1 ∧ batchLatency A + batchLatency B ≤ 2 := by
  classical
  simp only [batchLatency]
  split_ifs <;> norm_num

/-- For homogeneous specialists the exact derived minima have the source ratio;
probabilities may be any positive full-support normalized law. -/
theorem homogeneous_ratio (c α : ℝ) (hc : 0 < c)
    (hs : ∀ j, P.specialistCost j = c) (h0 : P.nearCost = α * c) :
    (∑ j, P.specialistCost j) /
        min (∑ j, P.specialistCost j) (P.nearCost + P.missing.mean P.specialistCost) =
      (z : ℝ) / min (z : ℝ) (α + 1) := by
  have he : P.missing.mean P.specialistCost = c := by
    simpa only [Distribution.mean_const] using
      congrArg P.missing.mean (funext hs)
  simp only [hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, he, h0]
  have hm : min ((z : ℝ) * c) (α * c + c) = min (z : ℝ) (α + 1) * c := by
    rw [show α * c + c = (α + 1) * c by ring, ← min_mul_of_nonneg _ _ hc.le]
  rw [hm]
  exact mul_div_mul_right _ _ (ne_of_gt hc)

/-- The attained optimal costs, rather than supplied optimum values, have the
source adaptivity ratio. Universal minimality is inherited from the preceding
one- and two-turn theorems. -/
theorem attained_ratio (hz : 0 < z) (c α : ℝ) (hc : 0 < c)
    (hs : ∀ j, P.specialistCost j = c) (h0 : P.nearCost = α * c) :
    ∃ (π : OnePolicy T) (σ : TwoPolicy T),
      π.Admissible P ∧ π.success P hz = 1 ∧
      σ.Admissible P ∧ σ.success P hz = 1 ∧
      (∀ ψ : OnePolicy T, ψ.Admissible P → ψ.success P hz = 1 → π.cost P ≤ ψ.cost P) ∧
      (∀ ψ : TwoPolicy T, ψ.Admissible P → ψ.success P hz = 1 → σ.cost P ≤ ψ.cost P) ∧
      π.cost P / σ.cost P = (z : ℝ) / min (z : ℝ) (α + 1) := by
  obtain ⟨π, hπA, hπS, hπC, hπO⟩ := one_turn_optimum (T := T) P hz
  obtain ⟨σ, hσA, hσS, hσC, hσO⟩ := two_turn_optimum (T := T) P hz
  refine ⟨π, σ, hπA, hπS, hσA, hσS, hπO, hσO, ?_⟩
  rw [hπC, hσC]
  exact homogeneous_ratio P c α hc hs h0

/-- The linear-gap branch of the source ratio, with its strict threshold explicit. -/
theorem attained_linear_ratio (hz : 0 < z) (c α : ℝ) (hc : 0 < c)
    (hs : ∀ j, P.specialistCost j = c) (h0 : P.nearCost = α * c)
    (hgap : α + 1 < (z : ℝ)) :
    ∃ (π : OnePolicy T) (σ : TwoPolicy T),
      π.Admissible P ∧ π.success P hz = 1 ∧
      σ.Admissible P ∧ σ.success P hz = 1 ∧
      π.cost P / σ.cost P = (z : ℝ) / (α + 1) := by
  obtain ⟨π, σ, hπA, hπS, hσA, hσS, _, _, hr⟩ := attained_ratio (T := T) P hz c α hc hs h0
  exact ⟨π, σ, hπA, hπS, hσA, hσS, by rwa [min_eq_right hgap.le] at hr⟩

/-- Actual residual computation implements the response-dependent second batch.
This uses the WSC instance and the received candidate indices, not a residual
certificate or an assumed equality of response laws. -/
theorem adaptiveTwo_residual (hz : 0 < z) (A : Batch z) (j : Fin z) :
    (adaptiveTwo (T := T)).second A (some j) = Distribution.pure
      {some (residualIndex T hz ((coverInstance T hz).ground \
        (coverInstance T hz).covered (payload T (univ.erase j))))} := by
  rw [decode_near_residual]
  rfl

end Cslib.Probability.StochasticOracle.ResidualCover
