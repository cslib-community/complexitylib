/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw

open Cslib Cslib.CountingLeaf Turing.MultiTapeTM

-- Count6, width4 and bit0 have redundant high zero digits; path101 is MSB-first5.
private def query : RawInput :=
  ⟨[true], [false, true, true, false], [false, false, true, false],
    [true, false, true], false, [false, false]⟩

example : query.normalize = ⟨[true], 6, 4, [true, false, true], false, 0⟩ := by rfl
example : runRaw (fun p => decide (p.2 = 5)) query = true := by decide
example : runRaw (fun _ => true) { query with count := [] } = false := by decide
example : runRaw (fun _ => true) { query with width := [false] } = false := by decide
example : runRaw (fun _ => true) { query with bit := [false, true] } = false := by decide
example : runRaw (fun _ => true) { query with carry := true } = false := by decide
example : (encRawInput query).length = 33 := by decide

example : ComputableInPolyTime (runRaw (fun p => decide (p.2 = 5))) encRawInput encBool := by
  apply computableInPolyTime_runRaw
  exact ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd encBits encNat)
    (ComputableInPolyTime.const 5)

example (q : RawInput) : encRawInput q =
    frame q.context ++ frame q.count ++ frame q.width ++ frame q.path ++
      frame [q.carry] ++ q.bit := encRawInput_eq q
