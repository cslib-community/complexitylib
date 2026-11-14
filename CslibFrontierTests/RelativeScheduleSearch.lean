/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork.RelativeSearch

open Turing.MultiTapePTM

-- Either boundary distance belongs to the window immediately.
example : RelativeSearch.scan (k := 1) (q := 2) (fun _ _ => 0)
    ⟨0, by decide⟩ 2 0 (-1) = some 0 := by decide

example : RelativeSearch.scan (k := 1) (q := 2) (fun _ _ => 0)
    ⟨0, by decide⟩ 2 0 1 = some 0 := by decide

-- An excursion leaves the queried window and returns on the following interval.
example : RelativeSearch.next (k := 1) (q := 3)
    (fun i _ => if i.val = 0 then -1 else 1) ⟨0, by decide⟩ ⟨0, by decide⟩
    ⟨2, by decide⟩ = some 2 := by decide

-- Moving away throughout the remaining horizon yields no later appearance.
example : RelativeSearch.next (k := 1) (q := 3) (fun _ _ => -1)
    ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩ = none := by decide

-- The last interval has no candidates, including for a stationary schedule.
example : RelativeSearch.next (k := 1) (q := 3) (fun _ _ => 0)
    ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = none := by decide

-- A successful candidate is inspected once and terminates the scan immediately.
example : RelativeSearch.inspections (k := 1) (q := 3) (fun _ _ => 0)
    ⟨0, by decide⟩ 3 0 0 = 1 := by decide

example : RelativeSearch.next (k := 1) (q := 1) (fun _ _ => 0)
    ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = none := by decide

example {k q : ℕ} (σ : Schedule k q) (h : Fin k) (fuel cursor : ℕ) (d : ℤ) :
    RelativeSearch.inspections σ h fuel cursor d ≤ fuel :=
  RelativeSearch.inspections_le σ h fuel cursor d
