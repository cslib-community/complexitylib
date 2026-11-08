/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Efficient

/-!
# Native bounded lattice signing

A one-dimensional example over `ZMod 7`, with secret and public matrix both `[1]`,
outer radius 2 and inner radius 1. Tests distinguish accepting and rejected randomness,
short native rows, truncated hash outputs, zero attempts and the quantitative two-attempt bound.
-/

namespace ComplexityTests.Crypto.LyubashevskySigning

open Cslib Cslib.Probability Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM Cslib.Interactive
open scoped ENNReal

abbrev params : LyubashevskyParams := ((1, 1, 1, 6), (7, 2, 1))
abbrev input : LyubashevskySignInput := (params, [[1]], [[1]], [])
def hashTrue : List Bool × List Bool → List Bool := fun _ => [true]

/-- Randomness zero yields commitment zero and response one. -/
example : lyubashevskySignPostprocess hashTrue (input, [0]) =
    some (encList encIntBin [0], encList encIntBin [1]) := by decide

/-- Randomness one would give response two, outside the inner box. -/
example : lyubashevskySignPostprocess hashTrue (input, [1]) = none := by decide

/-- Negative randomness remains an accepted signature after modular commitment reduction. -/
example : lyubashevskySignPostprocess hashTrue (input, [-2]) =
    some (encList encIntBin [5], encList encIntBin [-1]) := by decide

/-- The corresponding typed signature passes the existing exact verifier. -/
example : lyubashevskyVerifySig 1 1 1 7 2 1
    (lyubashevskyNativeHash hashTrue params) (!![1], !![1]) [] (![5], ![-1]) = true := by
  decide

/-- Missing secret/public rows and randomness coordinates use the documented zero defaults. -/
example : lyubashevskySignPostprocess hashTrue ((params, [], [], []), []) =
    some (encList encIntBin [0], encList encIntBin [0]) := by decide

/-- Only the configured challenge prefix is used. -/
example : lyubashevskySignPostprocess (fun _ => [true, false, true]) (input, [0]) =
    lyubashevskySignPostprocess hashTrue (input, [0]) := by decide

/-- An empty challenge word represents challenge zero. -/
example : lyubashevskySignPostprocess (fun _ => []) (input, [1]) =
    some (encList encIntBin [1], encList encIntBin [1]) := by decide

/-- The actual bounded algorithm carries its efficiency certificate for this concrete hash. -/
example : IsPPTOn (encPair encLyubashevskySignInput encUnary)
    (encOption (encPair encBits encBits)) (lyubashevskySignBoundedNative hashTrue) :=
  isPPTOn_lyubashevskySignBoundedNative (ComputableInPolyTime.const [true])

/-- No attempt produces an explicit abort with probability one. -/
example : ProbComp.eval (lyubashevskySignBoundedNative hashTrue (input, 0)) = PMF.pure none := by
  simp [lyubashevskySignBoundedNative]

/-- At width six, the two-attempt distance is at most `10/64`, below one. -/
example : CloseTo
    ((lyubashevskySignBounded 1 1 1 7 2 1 (lyubashevskyNativeHash hashTrue params) 2
      !![1] (!![1], !![1]) []).map (lyubashevskySignatureWords params))
    (ProbComp.eval (lyubashevskySignBoundedNative hashTrue (input, 2)))
    (10 / 64 : ℝ≥0∞) := by
  have h := closeTo_lyubashevskySignBoundedNative hashTrue params !![1] (!![1], !![1]) [] 2
  have hi : lyubashevskySignInput params !![1] !![1] [] = input := by decide
  rw [hi] at h
  convert h using 1
  norm_num [params]
  rw [← mul_div_assoc]
  norm_num

end ComplexityTests.Crypto.LyubashevskySigning
