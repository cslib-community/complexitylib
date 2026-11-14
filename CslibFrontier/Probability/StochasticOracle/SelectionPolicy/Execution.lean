/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Record
public import CslibFrontier.Probability.PMF

/-!
# Actual discrete execution of arbitrary batch-selecting policies

A policy chooses a batch or halt from its full record history. Issued batches
sample the fixed oracle response law, preserving the selected batch in the next
record. A prior halt absorbs all subsequent turns. There is no finite alphabet,
retention rule or output-admissibility restriction in this execution kernel.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy

/-- Actual batch-then-response execution, with absorbing prior halt records. -/
@[expose] def policyLaw {B R : Type}
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) : PMF (Record B R) := by
  classical
  exact if none ∈ h then PMF.pure none else
    (choose h).bind fun b => match b with
      | none => PMF.pure none
      | some b => (respond h b).map fun x => some (b, x)

/-- An issued call record has exactly a supported chosen batch and supported
conditional response. A previously halted history cannot issue a call. -/
theorem mem_support_policyLaw_some {B R : Type}
    (choose : List (Record B R) → PMF (Option B))
    (respond : List (Record B R) → B → PMF R)
    (h : List (Record B R)) (b : B) (x : R) :
    some (b, x) ∈ (policyLaw choose respond h).support ↔
      none ∉ h ∧ some b ∈ (choose h).support ∧ x ∈ (respond h b).support := by
  classical
  by_cases hn : none ∈ h
  · simp [policyLaw, hn]
  · rw [policyLaw, ite_eq_right hn, PMF.mem_support_bind_iff]
    constructor
    · rintro ⟨q, hq, hx⟩
      cases q with
      | none => simp at hx
      | some q =>
        obtain ⟨y, hy, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        have hz : (q, y) = (b, x) := Option.some.inj he
        cases hz
        exact ⟨hn, hq, hy⟩
    · rintro ⟨_, hb, hx⟩
      exact ⟨some b, hb, (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩⟩

end Cslib.Probability.StochasticOracle.SelectionPolicy
