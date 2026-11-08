/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.SelectionDeadline

/-!
# Selection-only policy optimum and matching envelopes

Theorem 5 of [Wang2027], PDF p. 12, Appendix A.5, p. 16. The candidate
upper policy uses actual local retention. Its comparator ranges over all admissible
randomized policies for the same oracle, including policies buffering uncertified
proposals. Bounds come from source conditional envelopes, not assumed optimality.
The scope is fixed finite batch/response alphabets, not encoded PTM realization.

## Main definitions

* `retainingPolicy`: an actual admissible upper-policy witness.
* `feasibleCosts`, `optimalCost`: all feasible behavioral policy costs and their infimum.

## Main results

* `retaining_guarantee`: derive the witness's finite upper probability/token guarantee.
* `optimalCost_sandwich`: universal lower bound and feasible actual upper cost.
* `matching_envelope_ratio`: the actual witness is within `1/eta` of the universal infimum.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy
open Cslib.Optimization.OneConstraint AdaptiveSelection PartialCover Finset MeasureTheory
variable {B R J E : Type} [Fintype B] [Fintype R] [Fintype J]
  [DecidableEq J] [DecidableEq E]

/-- Construct the source upper policy from a randomized batch selector: stop upon
retained completion and return the actual locally certified retained family. -/
@[expose] def retainingPolicy (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) : Policy B R J where
  choose h := if I.covered (selected I ρ (proposals O) h) = I.ground
    then Distribution.pure none else (select h).map some
  output h := Distribution.pure (selected I ρ (proposals O) h)

/-- The constructed upper policy is genuinely selection-only. -/
theorem retaining_admissible (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) :
    Admissible O (retainingPolicy O I ρ select) := by
  classical
  have hs (h : List (Record B R)) : selected I ρ (proposals O) h ⊆ available O h := by
    induction h with
    | nil => simp [selected, available]
    | cons x h ih =>
      apply (I.retain_subset ρ _ _).trans
      exact union_subset (ih.trans subset_union_right) subset_union_left
  intro h _ C hC
  have he : C = selected I ρ (proposals O) h := by
    by_contra he
    simp [retainingPolicy, Distribution.pure, he] at hC
  subst C
  exact hs h

/-- Before retained completion, the constructed policy disintegrates exactly into
its selected batch and actual response law. -/
theorem retaining_mean (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (h : List (Record B R))
    (hs : none ∉ h) (hc : I.covered (selected I ρ (proposals O) h) ≠ I.ground)
    (f : Record B R → ℝ) :
    (law O (retainingPolicy O I ρ select) h).mean f =
      (select h).mean (fun b => (O.respond h b).mean (fun x => f (some (b, x)))) := by
  rw [law_mean O _ h _ hs]
  simp only [retainingPolicy, hc, ite_false, Distribution.mean_map, Function.comp_def]

/-- A supported history of the retaining policy cannot have halted while incomplete. -/
theorem retaining_active (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (h : List (Record B R))
    (hh : Reachable (law O (retainingPolicy O I ρ select)) h)
    (hc : I.covered (selected I ρ (proposals O) h) ≠ I.ground) : none ∉ h := by
  classical
  induction hh with
  | nil => simp
  | @cons h x hh hx ih =>
    cases x with
    | none =>
      have hc' : I.covered (selected I ρ (proposals O) h) ≠ I.ground := by
        simpa only [selected, proposals, Instance.retain] using hc
      have hs := ih hc'
      have hz : (law O (retainingPolicy O I ρ select) h).weight none = 0 := by
        simp [law, hs, retainingPolicy, hc', Distribution.bind, Distribution.map]
      rw [hz] at hx
      exact (lt_irrefl _ hx).elim
    | some z =>
      rcases z with ⟨b, x⟩
      have hs := active_of_call O _ h b x hx
      simpa using hs

/-- The upper policy's source envelopes, conditional on each actually selected
batch at a supported incomplete history. No achieved-success or cost bound is a field. -/
structure UpperBounds (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a : ℕ) (p c ℓ : ℝ) : Prop where
  /-- Lower productivity envelope. -/
  progress : ∀ h, Reachable (law O (retainingPolicy O I ρ select)) h →
    I.covered (selected I ρ (proposals O) h) ≠ I.ground → ∀ b,
    0 < (select h).weight b → p ≤ (O.respond h b).mean
      (fun x => if productive I ρ (proposals O) a h (some (b, x)) then 1 else 0)
  /-- Conditional token-cost upper envelope. -/
  cost : ∀ h, Reachable (law O (retainingPolicy O I ρ select)) h →
    I.covered (selected I ρ (proposals O) h) ≠ I.ground → ∀ b,
    0 < (select h).weight b → (O.respond h b).mean (O.charge h b) ≤ c
  /-- Almost-sure upper latency per selected batch. -/
  time : ∀ h, Reachable (law O (retainingPolicy O I ρ select)) h →
    I.covered (selected I ρ (proposals O) h) ≠ I.ground → ∀ b,
    0 < (select h).weight b → ∀ x, 0 < (O.respond h b).weight x → O.duration h b x ≤ ℓ

/-- The source envelopes imply the exact conditional inequalities needed by the
existing actual-retention binomial and stopped-bill theorems. -/
theorem upper_conditional (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a : ℕ) (p c ℓ : ℝ)
    (H : UpperBounds O I ρ select a p c ℓ)
    (h : List (Record B R)) (hh : Reachable (law O (retainingPolicy O I ρ select)) h) :
    (I.covered (selected I ρ (proposals O) h) ≠ I.ground → p ≤
      (law O (retainingPolicy O I ρ select) h).mean
        (fun x => if productive I ρ (proposals O) a h x then 1 else 0)) ∧
    (law O (retainingPolicy O I ρ select) h).mean (bill O h) ≤
      c * (if I.covered (selected I ρ (proposals O) h) = I.ground then 0 else 1) := by
  classical
  constructor
  · intro hc
    rw [retaining_mean O I ρ select h (retaining_active O I ρ select h hh hc) hc]
    have he := Distribution.mean_const (select h) p
    apply he.symm.le.trans
    apply sum_le_sum
    intro b _
    by_cases hb : (select h).weight b = 0
    · simp [hb]
    · exact mul_le_mul_of_nonneg_left
        (H.progress h hh hc b (lt_of_le_of_ne ((select h).nonneg b) (Ne.symm hb)))
        ((select h).nonneg b)
  · by_cases hc : I.covered (selected I ρ (proposals O) h) = I.ground
    · by_cases hs : none ∈ h <;>
        simp [law, hs, retainingPolicy, hc, Distribution.mean_pure,
          Distribution.mean_bind, bill]
    · rw [retaining_mean O I ρ select h (retaining_active O I ρ select h hh hc) hc]
      simp only [hc, ite_false, mul_one]
      apply (show (select h).mean
        (fun b => (O.respond h b).mean (fun x => bill O h (some (b, x)))) ≤
        (select h).mean (fun _ => c) from ?_).trans_eq (Distribution.mean_const (select h) c)
      apply sum_le_sum
      intro b _
      by_cases hb : (select h).weight b = 0
      · simp [hb]
      · exact mul_le_mul_of_nonneg_left
          (H.cost h hh hc b (lt_of_le_of_ne ((select h).nonneg b) (Ne.symm hb)))
          ((select h).nonneg b)

/-- Supported calls of the retaining policy obey the upper latency envelope;
a call after completion has zero probability by construction. -/
theorem upper_latency (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a : ℕ) (p c ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (H : UpperBounds O I ρ select a p c ℓ) (h : List (Record B R))
    (hh : Reachable (law O (retainingPolicy O I ρ select)) h) :
    accruedBill (latency O) h ≤ (h.length : ℝ) * ℓ := by
  classical
  induction hh with
  | nil => simp [accruedBill]
  | @cons h x hh hx ih =>
    cases x with
    | none => simpa only [accruedBill, latency, add_zero, List.length_cons, Nat.cast_add,
        Nat.cast_one] using ih.trans (by nlinarith)
    | some z =>
      rcases z with ⟨b, x⟩
      have hs := active_of_call O _ h b x hx
      have hc : I.covered (selected I ρ (proposals O) h) ≠ I.ground := by
        intro hc
        simp [law, hs, retainingPolicy, hc, Distribution.bind, Distribution.pure] at hx
      rw [law_weight_call O _ h hs] at hx
      have hp : (retainingPolicy O I ρ select).choose h = (select h).map some := by
        simp [retainingPolicy, hc]
      rw [hp] at hx
      have hw : ((select h).map some).weight (some b) = (select h).weight b := by
        simp [Distribution.map]
      rw [hw] at hx
      have ht := H.time h hh hc b (pos_of_mul_pos_left hx ((O.respond h b).nonneg x)) x
        (pos_of_mul_pos_right hx ((select h).nonneg b))
      simp only [accruedBill, latency, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

private theorem historyExpectation_mono_terminal {Ω : Type} [Fintype Ω]
    (w : List Ω → Distribution Ω ℝ) (f g : List Ω → ℝ) (n : ℕ) (h : List Ω)
    (hh : Reachable w h)
    (hfg : ∀ k, Reachable w k → k.length = n + h.length → f k ≤ g k) :
    historyExpectation w f n h ≤ historyExpectation w g n h := by
  induction n generalizing h with
  | zero => exact hfg h hh (by omega)
  | succ n ih =>
    apply sum_le_sum
    intro x _
    by_cases hx : (w h).weight x = 0
    · simp [hx]
    · apply mul_le_mul_of_nonneg_left _ ((w h).nonneg x)
      apply ih (x :: h) (.cons hh (lt_of_le_of_ne ((w h).nonneg x) (Ne.symm hx)))
      intro k hk hlen
      apply hfg k hk
      simp only [List.length_cons] at hlen
      omega

/-- Derived source upper guarantee for an actual member of the competing policy
class: successful randomized output probability and finite expected token bound. -/
theorem retaining_guarantee (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a r u : ℕ)
    (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1) (c ℓ D : ℝ)
    (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ) (hD : (u : ℝ) * ℓ ≤ D)
    (H : UpperBounds O I ρ select a p c ℓ) :
    (∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial u p) ≤
      successProbability O (retainingPolicy O I ρ select) I ρ D u ∧
    expectedCost O (retainingPolicy O I ρ select) u ≤
      ∑ t ∈ range u, c * binomialFailure p r t := by
  classical
  let π := retainingPolicy O I ρ select
  have hp := fun h hh => (upper_conditional O I ρ select a p c ℓ H h hh).1
  have hb := fun h hh => (upper_conditional O I ρ select a p c ℓ H h hh).2
  constructor
  · apply (binomial_le_completion_reachable I ρ (proposals O) (law O π) a r u hr p hp).trans
    apply historyExpectation_mono_terminal (law O π) _ _ u [] .nil
    intro h hh hlen
    have hl := upper_latency O I ρ select a p c ℓ hℓ H h hh
    have hd : accruedBill (latency O) h ≤ D := by
      simp only [List.length_nil, Nat.add_zero] at hlen
      rw [hlen] at hl
      exact hl.trans hD
    by_cases hcov : I.covered (selected I ρ (proposals O) h) = I.ground
    · have hcert := selected_bound I ρ (proposals O) h
      rw [hcov] at hcert
      simp [success, retainingPolicy, Distribution.mean_pure, hcov, hcert, hd]
    · simp [success, retainingPolicy, Distribution.mean_pure, hcov]
  · have ht := accruedBill_le_binomial_sum_reachable I ρ (proposals O) (law O π)
      a r u hr p hp (bill O) c hc hb
    simpa only [expectedCost, π, binomialFailure_eq_complement] using ht

/-- All costs of actual admissible policies achieving the requested deadline
success level, for this fixed oracle, across all finite turn budgets. -/
@[expose] def feasibleCosts (O : Oracle B R J) (I : Instance E J)
    (ρ D η : ℝ) : Set ℝ :=
  {z | ∃ u : ℕ, ∃ π : Policy B R J, Admissible O π ∧ DeadlineFeasible O π D u ∧
    η ≤ successProbability O π I ρ D u ∧ z = expectedCost O π u}

/-- Infimum over every admissible randomized policy and every finite turn budget,
not just the candidate's budget or retained policies.
Nonemptiness and boundedness are proved from the source contracts below. -/
@[expose] def optimalCost (O : Oracle B R J) (I : Instance E J)
    (ρ D η : ℝ) : ℝ := sInf (feasibleCosts O I ρ D η)

/-- Source upper/lower sandwich for the universal policy infimum. The constructed
retaining policy supplies feasibility; the lower bound is derived for all competitors.
Neither nonemptiness, a lower optimum bound nor upper optimality is an input. -/
theorem optimalCost_sandwich (O : Oracle B R J) (I : Instance E J) (ρ D η : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a ra b rb u : ℕ)
    (hra : I.ground.card ≤ a * ra) (hrb : ∀ k < rb, b * k < I.ground.card)
    (pL pU : Set.Icc (0 : ℝ) 1) (hpU : 0 < (pU : ℝ))
    (cL cU ℓL ℓU : ℝ) (hcL : 0 ≤ cL) (hcU : 0 ≤ cU) (hℓU : 0 ≤ ℓU)
    (hD : (u : ℝ) * ℓU ≤ D) (hη0 : 0 ≤ η)
    (hη : η ≤ ∫ i, (if ra ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial u pL)
    (HU : UpperBounds O I ρ select a pL cU ℓU)
    (HL : UniversalBounds O I b pU cL ℓL) :
    η * (rb : ℝ) * cL / pU ≤ optimalCost O I ρ D η ∧
    optimalCost O I ρ D η ≤ expectedCost O (retainingPolicy O I ρ select) u ∧
    expectedCost O (retainingPolicy O I ρ select) u ≤
      ∑ t ∈ range u, cU * binomialFailure pL ra t := by
  have hU := retaining_guarantee O I ρ select a ra u hra pL cU ℓU D hcU hℓU hD HU
  have htime : DeadlineFeasible O (retainingPolicy O I ρ select) D u := by
    intro h hh hlen
    have ht := upper_latency O I ρ select a pL cU ℓU hℓU HU h hh
    rw [hlen] at ht
    exact ht.trans hD
  have hm : expectedCost O (retainingPolicy O I ρ select) u ∈ feasibleCosts O I ρ D η :=
    ⟨u, retainingPolicy O I ρ select, retaining_admissible O I ρ select, htime,
      hη.trans hU.1, rfl⟩
  have hlow : ∀ z ∈ feasibleCosts O I ρ D η, η * (rb : ℝ) * cL / pU ≤ z := by
    rintro z ⟨n, π, hA, _htime, hs, rfl⟩
    exact universal_lower_cost O I b rb n hrb pU cL ℓL ρ D η hpU hcL hη0 HL π hA hs
  have hbd : BddBelow (feasibleCosts O I ρ D η) := ⟨_, hlow⟩
  exact ⟨le_csInf ⟨_, hm⟩ hlow, csInf_le hbd hm, hU.2⟩

/-- With matching progress, coverage and token envelopes, the actual upper policy
is within 1/eta of the infimum over all admissible policies. This is a derived
comparison with the universal optimum, not a supplied optimality certificate. -/
theorem matching_envelope_ratio (O : Oracle B R J) (I : Instance E J) (ρ D η : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (a r u : ℕ)
    (hra : I.ground.card ≤ a * r) (hrb : ∀ k < r, a * k < I.ground.card)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (c ℓL ℓU : ℝ)
    (hc : 0 ≤ c) (hℓU : 0 ≤ ℓU) (hD : (u : ℝ) * ℓU ≤ D) (hη : 0 < η)
    (hηU : η ≤ ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial u p)
    (HU : UpperBounds O I ρ select a p c ℓU) (HL : UniversalBounds O I a p c ℓL) :
    optimalCost O I ρ D η ≤ expectedCost O (retainingPolicy O I ρ select) u ∧
    expectedCost O (retainingPolicy O I ρ select) u ≤ (1 / η) * optimalCost O I ρ D η := by
  have hs := optimalCost_sandwich O I ρ D η select a r a r u hra hrb p p hp
    c c ℓL ℓU hc hc hℓU hD hη.le hηU HU HL
  have hb : expectedCost O (retainingPolicy O I ρ select) u ≤ c * ((r : ℝ) / p) := by
    apply hs.2.2.trans
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_binomialFailure_le p hp u r) hc
  have he : η * (c * ((r : ℝ) / p)) = η * (r : ℝ) * c / p := by ring
  have hm := mul_le_mul_of_nonneg_left hb hη.le
  rw [he] at hm
  refine ⟨hs.2.1, ?_⟩
  have ht : expectedCost O (retainingPolicy O I ρ select) u ≤ optimalCost O I ρ D η / η :=
    (le_div_iff₀ hη).mpr (by nlinarith [hs.1])
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using ht

end Cslib.Probability.StochasticOracle.SelectionPolicy
