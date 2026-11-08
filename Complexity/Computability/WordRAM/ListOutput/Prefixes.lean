/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.ListOutput
public import Complexity.Computability.WordRAM.ExecInvariant
import all Complexity.Computability.WordRAM.ListOutput

/-!
# Prefix invariants survive halt parking

A predicate on the data at every prefix of a terminating list-valued execution
holds at every prefix of its parked execution, for arbitrarily large clocks.
After the halting jump, self-loops retain the final data. No bound on the sum of
allocations or a post-halt resource invariant is assumed.
-/

public section
namespace Cslib.WordRAM

/-- Prefix data invariants extend through the actual parking jump and all later self-loops. -/
theorem ExecutesList.parked_prefix {B : Basis} {r w n : ℕ} {p : Program B r}
    {start : State r} {output : List ℕ} (h : ExecutesList w p start output (n + 1))
    {P : Data r → Prop}
    (hP : ∀ k u, k ≤ n → Runs w p start u k → P u.data) (j : ℕ) :
    ∃ u, Runs w p.parkHalts start u j ∧ P u.data := by
  obtain ⟨finish, steps, v, hr, hh, _, hn⟩ := h
  have he : steps = n := by omega
  subst steps
  by_cases hj : j ≤ n
  · have hsum : n = j + (n - j) := by omega
    rw [hsum] at hr
    obtain ⟨u, hu, _⟩ := Relation.RelatesInSteps.add_iff.mp hr
    exact ⟨u, Program.runs_parkHalts hu, hP j u hj hu⟩
  · obtain ⟨i, _, hi⟩ := Program.next_parkHalts_of_halt hh
    have before := (Program.runs_parkHalts hr).tail _ _ _ _ hi
    have after := before.trans (Program.runs_parkHalts_park i finish.data (j - (n + 1)))
    refine ⟨⟨p.length + i, finish.data⟩, ?_, hP n finish le_rfl hr⟩
    convert after using 1; omega

end Cslib.WordRAM
