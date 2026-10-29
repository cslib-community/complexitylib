/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.NativeExtract

/-! Runtime dimensions, signed challenge differences and total malformed-input behavior. -/

open Turing.MultiTapeTM Cslib.Crypto.Protocols.SigmaProtocol

example : lyubashevskyExtractList
    ((2, 1), (([false], some [0, 1]), ([true], some [1, 0]))) = [-1, 1, 1] := by
  decide +kernel

example : lyubashevskyExtractList
    ((1, 1), (([true], some [-2]), ([false], some [3]))) = [-5, -1] := by
  decide +kernel

-- Missing coordinates default to zero/false, while extra coordinates are ignored.
example : lyubashevskyExtractList
    ((3, 2), (([true, false, true], none), ([], some [7]))) = [-7, 0, 0, -1, 0] := by
  decide +kernel

example : lyubashevskyExtractList ((0, 0), (([true], some [7]), ([], none))) = [] := by
  decide +kernel

example : lyubashevskyExtractList ((0, 2), (([], none), ([true], none))) = [1, 0] := by
  decide +kernel

example : lyubashevskyExtractList ((2, 0), (([], none), ([], none))) = [0, 0] := by
  decide +kernel

example : lyubashevskyExtractWord [] = encList encIntBin [] := by decide +kernel

-- Round-trip encoding and polynomial-time projection composition on a concrete input.
example :
    lyubashevskyExtractWord (encLyubashevskyExtractInput
      ((1, 1), (([true], some [-2]), ([false], some [3])))) =
      encList encIntBin (lyubashevskyExtractList
        ((1, 1), (([true], some [-2]), ([false], some [3])))) ∧
    ComputableInPolyTime (lyubashevskyExtractWord ∘ fun p : List Bool × List Bool => p.1)
      (encPair encBits encBits) encBits :=
  ⟨lyubashevskyExtractWord_enc ((1, 1), (([true], some [-2]), ([false], some [3]))),
   computableInPolyTime_lyubashevskyExtractWord.comp (by polytime)⟩

-- The actual typed protocol extractor has the same negative response / positive challenge tail.
example : List.ofFn (fun i : Fin 3 =>
    lyubashevskyExtract 1 2 1 7 (0, 0) 0 (fun _ => false)
      (some fun i => (i.val : ℤ)) (fun _ => true) (some fun i => 1 - (i.val : ℤ))
      (finSumFinEquiv.symm i)) = [-1, 1, 1] := by
  decide +kernel

-- The named bridge applies even with no response coordinates or challenge coordinates.
example (q : ℕ) :
    lyubashevskyExtractWord (encLyubashevskyExtractInput
      ((0, 0), (([], none), ([], none)))) =
      encList encIntBin (List.ofFn (fun i : Fin 0 =>
        lyubashevskyExtract 0 0 0 q (0, 0) 0 (fun _ => false) none
          (fun _ => false) none (finSumFinEquiv.symm i))) := by
  simpa using lyubashevskyExtractWord_eq_extract 0 0 0 q (0, 0) 0
    (fun _ => false) none (fun _ => false) none
