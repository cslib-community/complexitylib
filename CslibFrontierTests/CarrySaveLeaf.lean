/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf

namespace CslibFrontierTests.CarrySaveLeaf

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib.CountingLeaf
open Turing.MultiTapeATM.CarrySaveLeaf

-- Preparation physically writes either carry value and rewinds a nonempty persistent path.
example (input : List Bool) (carry : Bool) :
    let cfg := initial 0 input [true] [true, false] [true] [true, true]
      [false, false] [true, false] [true, true, true] 2 true
    (machine 0 carry).runFrom (cfg.withState (some (machine 0 carry).q₀)) 5 =
      (prepared cfg carry).withState none := by
  exact (runsBetween 0 input [true] [true, false] [true] [true, true]
    [false, false] [true, false] [true, true, true] 2 true carry).1

-- The carry is materialized while the path contents and unrelated controller head survive.
example {input : List Bool} (cfg : Cfg 12 Bool Unit input) (carry : Bool) :
    (prepared cfg carry).workTapes 9 = tapeOfList [carry] ∧
    (prepared cfg carry).workTapes 2 = cfg.workTapes 2 ∧
    (prepared cfg carry).workTapePos 2 = 0 ∧
    (prepared cfg carry).workTapePos 4 = cfg.workTapePos 4 := by
  have hc : CarrySaveStream.coreEmb 6 2 = (2 : Fin 12) := rfl
  simp [prepared, carryTape, hc]

-- One finite leaf family consumes real stream storage. The sum component is true while
-- the carry component is false; neither source carry word is assumed in the initial layout.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S)
    (leaf : Bool → MultiTapeTM (k + 12) Bool S) (c d : ℕ),
    ∀ (input : List Bool) (carry : Bool),
    let cfg := initial k input [] [true, false] [true, false]
      [] [false, false] [] [] 0 false
    (leaf carry).runFrom (cfg.withState (some (leaf carry).q₀))
      (clock c d [] [true, false] [true, false] 2) =
      (completed (prepared cfg carry) (query [] [true, false] [true, false] []
        [false, false] carry) [!carry]).withState none := by
  obtain ⟨k, S, hS, leaf, c, d, h⟩ := exists_counting (fun _ => true)
    (ComputableInPolyTime.const true)
  refine ⟨k, S, hS, leaf, c, d, fun input carry => ?_⟩
  have he : runRaw (fun _ => true)
      (query [] [true, false] [true, false] [] [false, false] carry) = !carry := by
    cases carry <;> decide
  simpa only [he] using h input [] [true, false] [true, false] []
    [false, false] [] [] 0 false carry 2 (by decide)

end CslibFrontierTests.CarrySaveLeaf
