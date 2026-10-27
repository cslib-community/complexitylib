/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Mathlib.Data.List.Fold

/-!
# Direct conversion of framed Boolean lists to raw words

The canonical `ComputableInPolyTime.listToBits` certificate keeps its original public contract
and registration. Its direct proof prepends into a raw word with a reachable-prefix bound and
then reverses that word. The higher bit-string facade reexports this same declaration.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Convert framed Boolean lists to raw words without changing their contents. -/
@[fun_prop]
theorem listToBits :
    ComputableInPolyTime (fun l => l) (encList encBool) encBits := by
  have hstep : ComputableInPolyTime (fun p : List Bool × Bool => p.2 :: p.1)
      (encPair encBits encBool) encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.snd encBits encBool)
      (ComputableInPolyTime.fst encBits encBool)
  have hfold := ComputableInPolyTime.foldl' (encA := encBool) (encL := encList encBool)
    (encB := encBits) (list := id) (init := fun _ => []) (step := fun acc bit => bit :: acc)
    ComputableInPolyTime.id' (ComputableInPolyTime.const []) hstep
    (B := fun l => (encList encBool l).length) .self (by
      intro l i _
      change ((l.take i).foldl (flip List.cons) []).length ≤ _
      rw [List.foldl_cons_nil, List.length_reverse]
      exact (List.length_take_le' _ _).trans
        (SizedListEncoding.length_le (encA := encBool) (encL := encList encBool) l))
  have h := ComputableInPolyTime.bitsReverse.comp hfold
  simpa only [Function.comp_def, List.reverse_foldl, id_eq] using h


end Turing.MultiTapeTM.ComputableInPolyTime
