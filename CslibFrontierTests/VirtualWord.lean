/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.VirtualWord

/-!
# Native virtual-word access clients

The tests execute the actual accessor at prefix/suffix/default boundaries and instantiate its
native logspace certificate on inhabited domains, including zero, one and non-power-of-two
lengths. The materialized list occurs only in the mathematical specification and tests.
-/

public section

namespace Cslib.Complexity.VirtualWordTest

open Turing Turing.MultiTapeTM

-- Empty input: no suffix and a default read at zero.
example : (VirtualWord.machine (localQueryAccessData 0 [] 0)).output [] 1 = [false] := by decide

-- Length one has an empty suffix. Its sole original bit must still be read.
example : (VirtualWord.machine (localQueryAccessData 1 [] 0)).output [true] 1 = [true] := by decide
example : (VirtualWord.machine (localQueryAccessData 1 [] 1)).output [true] 1 = [false] := by decide

-- At length three the suffix has two bits. Index one is already in the stored suffix.
example : (VirtualWord.machine (localQueryAccessData 3 [false, true] 0)).output
    [false, true, false] 1 = [false] := by decide
example : (VirtualWord.machine (localQueryAccessData 3 [false, true] 1)).output
    [false, true, false] 1 = [false] := by decide
example : (VirtualWord.machine (localQueryAccessData 3 [false, true] 2)).output
    [false, true, false] 1 = [true] := by decide
example : (VirtualWord.machine (localQueryAccessData 3 [false, true] 3)).output
    [false, true, false] 1 = [false] := by decide

-- Non-power-of-two length five: last prefix bit, first suffix bit, last bit and default.
example : (List.range 6).map (fun i =>
    (VirtualWord.machine (localQueryAccessData 5 [false, true, false] i)).output
      [true, true, true, false, true] 1) =
    [[true], [true], [false], [true], [false], [false]] := by decide

example : (VirtualWord.machine (1, [false, true], 100)).output
    [true, false, false] 1 = [false] := by decide

/-- An actual local query, accessed through the original prefix rather than a copied query. -/
theorem local_query_reads (i : ℕ) :
    (VirtualWord.machine (localQueryAccessData 3 [false, true] i)).output
      [false, true, false] 1 = [[false, false, true].getD i false] := by
  exact (show LocalSelfReductionQuery [false, true, false] [false, false, true] by decide)
    |>.access_output i

/-- An inhabited native certificate domain, with the two-bit suffix already stored. -/
theorem three_native : ComputableInLogSpace
    (fun x : {x : List Bool // x.length = 3} =>
      VirtualWord.answer (localQueryAccessData 3 [false, true] 2) (x.val.getD 2 false))
    ((Function.Embedding.subtype (fun x : List Bool => x.length = 3)).trans encBits) encBool :=
  localQueryAccess_inLogSpace 3 2 [false, true] (by decide) (by decide)

example : Nonempty {x : List Bool // x.length = 3} := ⟨⟨[false, true, false], rfl⟩⟩
example : Nonempty {x : List Bool // x.length = 0} := ⟨⟨[], rfl⟩⟩
example : Nonempty {x : List Bool // x.length = 1} := ⟨⟨[true], rfl⟩⟩

example : ComputableInLogSpace
    (fun x : {x : List Bool // x.length = 0} =>
      VirtualWord.answer (localQueryAccessData 0 [] 0) (x.val.getD 0 false))
    ((Function.Embedding.subtype (fun x : List Bool => x.length = 0)).trans encBits) encBool :=
  localQueryAccess_inLogSpace 0 0 [] (by decide) (by decide)

example : ComputableInLogSpace
    (fun x : {x : List Bool // x.length = 1} =>
      VirtualWord.answer (localQueryAccessData 1 [] 0) (x.val.getD 0 false))
    ((Function.Embedding.subtype (fun x : List Bool => x.length = 1)).trans encBits) encBool :=
  localQueryAccess_inLogSpace 1 0 [] (by decide) (by decide)

-- Past-end addresses remain correct, but their binary storage must still be charged.
example : (VirtualWord.encState ((1, [false, true], 100), false)).length =
    4 * (encNat 1).length + 8 + 2 * (encNat 100).length + 6 :=
  VirtualWord.length_encState 1 100 [false, true] false

end Cslib.Complexity.VirtualWordTest
