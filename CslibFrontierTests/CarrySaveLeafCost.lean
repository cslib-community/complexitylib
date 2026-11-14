/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeafCost
import CslibFrontierTests.CountingLeafRawCost

namespace CslibFrontierTests.CarrySaveLeafCost

open Turing Turing.MultiTapeTM Turing.MultiTapeATM
open Cslib.CountingLeaf CslibFrontierTests.CountingLeafRawCost

-- One machine physically rewinds the path, writes the carry selector, serializes the fields,
-- evaluates the leaf and cleans evaluator scratch. The context is arbitrary, while the local
-- fields are fixed-size padded words. Both positive and rejected answers use the same clock.
example : ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (leaf : Bool → MultiTapeTM (k + 12) Bool State) (c d : ℕ),
    ∀ (input context : List Bool) (active carry : Bool),
      let q := query context active carry
      let cfg := CarrySaveLeaf.initial k input context q.count q.width [] q.bit q.path [] 0 false
      (leaf carry).runFrom (cfg.withState (some (leaf carry).q₀))
        (CarrySaveLeafCost.clock c d context q.count q.width 4 0) =
        (CarrySaveLeaf.completed (CarrySaveLeaf.prepared cfg carry) q [active && !carry]).withState
          none := by
  obtain ⟨k, State, hState, leaf, c, d, hr⟩ :=
    CarrySaveLeafCost.exists_counting (fun _ => true) true_inO
  refine ⟨k, State, hState, leaf, c, d, ?_⟩
  intro input context active carry
  let q := query context active carry
  have h := hr input context q.count q.width [] q.bit q.path [] 0 false carry 4 0
    (by simp [q, query]) (by decide)
  have hq : CarrySaveLeaf.query context q.count q.width q.path q.bit carry = q := rfl
  dsimp only at h ⊢
  rw [hq, query_answer] at h
  exact h

end CslibFrontierTests.CarrySaveLeafCost
