/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointEncoded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetweenOutput
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Linear complexity of total encoded schedule endpoint queries

The native adapter supplies a plain deterministic computation with separate linear time and
workspace bounds. It handles every typed input record, including malformed raw rows and arbitrary
binary selectors and interval indices. The input encoding specifies the outer record framing and
canonical binary integers; no behavior on arbitrary malformed outer byte strings is claimed.

The output is the explicit validity/found-tag encoding, so invalid input differs from valid
exhaustion. Its length is bounded by the actual native clock, which also provides the output
charge needed by `ComputableInO`. These are endpoint-query bounds, not a complete simulation or
its global alternating-time clock.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointEncoded

open ScheduleEndpointQuery ScheduleEndpointInput ScheduleEndpointAnswer

/-- For each fixed tape count, the total encoded query has separate linear time and workspace
bounds on the complete input length. Both constants and the finite machine precede runtime data. -/
theorem computableInTimeAndSpace_linear (k : ℕ) :
    ∃ cTime cSpace, ComputableInTimeAndSpaceOfLength (query k) encInput encAnswer
      (fun n => cTime * (n + 1)) (fun n => cSpace * (n + 1)) := by
  obtain ⟨K, Q, hQ, tm, c, htm⟩ := exists_machine k
  refine ⟨c, K * (c + 1), K, Q, hQ, tm, ?_⟩
  intro a
  obtain ⟨final, hr, hout⟩ := htm a []
  have hc := hr.computesInTimeAndSpace
  simp only [List.nil_append] at hout
  rw [hout] at hc
  refine ⟨hc.1, hc.2.1, hc.2.2.mono ?_⟩
  have h : c * ((encInput a).length + 1) + 1 ≤ (c + 1) * ((encInput a).length + 1) := by
    nlinarith
  exact (Nat.mul_le_mul_left K h).trans_eq (Nat.mul_assoc _ _ _).symm

/-- The actual native adapter gives linear plain computation, including the explicit tagged
output charge, in the length of the external encoded record. -/
@[fun_prop] theorem computableInO (k : ℕ) :
    ComputableInO (query k) encInput encAnswer
      (fun a => (encInput a).length) (fun a => (encInput a).length) := by
  obtain ⟨cTime, cSpace, h⟩ := computableInTimeAndSpace_linear k
  refine ComputableInO.of_bounds h (cTime + cSpace) ?_ ?_ ?_
  · intro a
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · intro a
    exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · intro a
    exact (h.length_le a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

end Turing.MultiTapeTM.ScheduleEndpointEncoded
