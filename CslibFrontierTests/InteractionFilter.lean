/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Interaction
import Mathlib.Tactic

/-!
# Two-turn filtering with policy-private coins and a persistent source bit

The source first returns the conjunction of two fair bits, retaining the first
bit. The policy's next query depends on that reply and its private coin. A false
query receives no new information; a true query reveals the persistent bit.
Fair and deterministic query policies have the same source posterior on their
common supported observation. Dropping an invoice seen by the policy breaks this
information separation, as the final counterexample demonstrates.
-/

public section
noncomputable section
namespace CslibFrontierTests.InteractionFilter
open Cslib.Probability
open scoped ENNReal

/-- Fresh independent fair private randomness. -/
@[expose] def fair : PMF Bool := PMF.uniformOfFintype Bool

/-- The actual first source response and persistent hidden bit. -/
@[expose] def first : PMF (Bool × Bool) :=
  fair.bind fun s => fair.map fun noise => (s && noise, s)

private theorem first_apply (r s : Bool) :
    first (r, s) = if r then (if s then 1 / 4 else 0) else
      (if s then 1 / 4 else 1 / 2 : ℝ≥0∞) := by
  cases r <;> cases s <;>
    norm_num [first, fair, PMF.bind_apply, PMF.map_apply, tsum_fintype, Fintype.sum_bool,
      PMF.uniformOfFintype_apply]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_mul]

private theorem first_false : (first.map Prod.fst) false = 3 / 4 := by
  rw [PMF.map_fst_apply, tsum_fintype, Fintype.sum_bool]
  norm_num only [first_apply, Bool.false_eq_true, ite_false, ite_true, one_div]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]

private theorem first_false_support : false ∈ (first.map Prod.fst).support := by
  change (first.map Prod.fst) false ≠ 0
  rw [first_false]
  norm_num

/-- Conditioning the actual noisy first response produces a nontrivial persistent filter. -/
theorem first_filter : PMF.conditionalSnd first false true = 1 / 3 := by
  rw [PMF.conditionalSnd_apply first false first_false_support, first_false, first_apply]
  norm_num only
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by simp) (by simp)) (by simp)).mp
  norm_num [ENNReal.toReal_div]

/-- The query is formed from the actual first response and policy-private randomness. -/
def policy (reply : Bool) (privateCoin : PMF Bool) : PMF (Bool × Bool) :=
  privateCoin.map fun c => (Bool.xor reply c, c)

/-- Querying reveals the hidden bit; declining the query returns a constant answer. -/
def source (reply query : Bool) : PMF (Bool × Bool) :=
  (PMF.conditionalSnd first reply).map fun s => ((if query then s else false), s)

private theorem source_false :
    PMF.conditionalSnd (source false false) false = PMF.conditionalSnd first false := by
  have he : source false false = (PMF.pure false).bind
      (fun _ => (PMF.conditionalSnd first false).map (false, ·)) := by
    simp [source]
  rw [he]
  simpa only [PMF.pure_bind] using PMF.conditionalSnd_bind_pair (PMF.pure false)
    (fun _ : Bool => PMF.conditionalSnd first false) false (by simp)

/-- The other query genuinely reveals the persistent bit on a supported reply. -/
theorem informative_query : PMF.conditionalSnd (source false true) true = PMF.pure true := by
  have he : source false true = (PMF.conditionalSnd first false).bind
      (fun s => (PMF.pure s).map (s, ·)) := by
    simp [source, PMF.map, Function.comp_def]
  rw [he]
  apply PMF.conditionalSnd_bind_pair (PMF.conditionalSnd first false)
    (fun s => PMF.pure s) true
  change PMF.conditionalSnd first false true ≠ 0
  rw [first_filter]
  norm_num

private theorem branch_support (privateCoin : PMF Bool) (hc : false ∈ privateCoin.support) :
    (false, false) ∈ ((PMF.queryResponse (policy false privateCoin) (source false)).map
      Prod.fst).support := by
  rw [PMF.map_fst_queryResponse]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨false, ?_, ?_⟩
  · have he : (policy false privateCoin).map Prod.fst = privateCoin := by
      simp only [policy, PMF.map_comp, Function.comp_def, Bool.false_xor]
      exact PMF.map_id _
    rw [he]
    exact hc
  · simp [source, PMF.map_comp]

/-- Both actual query laws give the same source posterior on their shared branch. -/
theorem source_filter_independent (privateCoin : PMF Bool)
    (hc : false ∈ privateCoin.support) :
    ((PMF.conditionalSnd (PMF.queryResponse (policy false privateCoin) (source false))
      (false, false)).map Prod.snd) true = 1 / 3 := by
  rw [PMF.conditionalSnd_queryResponse_source _ _ false false
    (branch_support privateCoin hc), source_false]
  exact first_filter

-- These are different actual private-query distributions, not supplied posterior laws.
example :
    ((PMF.conditionalSnd (PMF.queryResponse (policy false fair) (source false))
      (false, false)).map Prod.snd) true = 1 / 3 ∧
    ((PMF.conditionalSnd (PMF.queryResponse (policy false (PMF.pure false)) (source false))
      (false, false)).map Prod.snd) true = 1 / 3 := by
  constructor
  · exact source_filter_independent fair (by simp [fair])
  · exact source_filter_independent (PMF.pure false) (by simp)

/-- Actual private state after the policy processes the second reply. -/
structure RetentionState where
  /-- Private bit retained from the earlier query decision. -/
  old : Bool
  /-- Whether the fresh private decision retains the proposal. -/
  retained : Bool

/-- After the reply, a fresh private coin chooses retention while keeping earlier private state. -/
def update (_query reply old : Bool) : PMF RetentionState :=
  fair.map fun fresh => ⟨old, Bool.xor reply fresh⟩

-- Fresh-coin processing preserves the full private/source product.
example :
    PMF.conditionalSnd
      ((PMF.queryResponse (policy false fair) (source false)).bind
        fun ⟨⟨query, reply⟩, ⟨localState, sourceState⟩⟩ =>
          (update query reply localState).map fun next => ((query, reply), (next, sourceState)))
      (false, false) =
      (fair.map fun fresh => (⟨false, fresh⟩ : RetentionState)).bind fun d =>
        (PMF.conditionalSnd first false).map (d, ·) := by
  have hp : PMF.conditionalSnd (policy false fair) false = PMF.pure false := by
    have he : policy false fair = fair.bind (fun c => (PMF.pure c).map (c, ·)) := by
      simp [policy, PMF.map, Function.comp_def]
    rw [he]
    exact PMF.conditionalSnd_bind_pair _ _ false (by simp [fair])
  have he := PMF.conditionalSnd_queryResponse_update (policy false fair) (source false)
    update false false (branch_support fair (by simp [fair]))
  simpa only [hp, PMF.pure_bind, update, Bool.false_xor, source_false] using he

/-- A constant answer word hides a billed token count that the policy actually sees. -/
def coarse : PMF (Unit × Bool) := fair.map fun s => ((), s)

/-- The billed token amount is visible to the policy although the answer word is constant. -/
def invoice (s : Bool) : ℕ := if s then 2 else 1

/-- The policy reads the invoice and queries with the recovered hidden bit. -/
def invoiceQuery : PMF (Bool × Bool) := fair.map fun s => (decide (invoice s = 2), s)

-- Dropping that invoice leaves a fair coarse posterior, although the next query reveals the bit.
example : PMF.conditionalSnd coarse () false = 1 / 2 ∧
    PMF.conditionalSnd invoiceQuery false false = 1 := by
  constructor
  · have he : coarse = (PMF.pure ()).bind (fun _ => fair.map ((), ·)) := by
      simp [coarse]
    rw [he, PMF.conditionalSnd_bind_pair _ _ () (by simp)]
    norm_num [fair, PMF.uniformOfFintype_apply]
  · have he : invoiceQuery = fair.bind (fun s => (PMF.pure s).map (s, ·)) := by
      simp only [PMF.pure_map]
      change fair.map (fun s => (decide (invoice s = 2), s)) =
        fair.map (fun s => (s, s))
      apply congrArg fair.map
      funext s
      cases s <;> rfl
    rw [he, PMF.conditionalSnd_bind_pair _ _ false (by simp [fair])]
    simp

end CslibFrontierTests.InteractionFilter
