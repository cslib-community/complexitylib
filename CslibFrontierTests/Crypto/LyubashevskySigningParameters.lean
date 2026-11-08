/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Parameters

/-!
# Explicit bounded-signing parameters

The zero-security case has one coordinate and no sample bits; it can fail with certainty.
At positive security, bounded nonzero secrets satisfy the family hypothesis. The asymptotic
bound becomes nonvacuous while the implementation's runtime charges the complete input.
-/

namespace ComplexityTests.Crypto.LyubashevskySigningParameters

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM
open scoped ENNReal NNReal

example : lyubashevskySigningParams 0 = ((1, 1, 1, 0), (2, 4, 1)) := rfl

example : lyubashevskySigningParams 1 = ((2, 2, 2, 1), (4, 16, 2)) := rfl

/-- A nonzero bounded secret and zero randomness yield a non-aborted response at λ=1. -/
example : lyubashevskySignPostprocess (fun _ => [true, true])
    ((lyubashevskySigningParams 1, [[1, 0], [0, -1]], [[1, 0], [0, 1]], []), [0, 0]) =
    some (encList encIntBin [0, 0], encList encIntBin [1, -1]) := by decide

/-- With no sample bits at λ=0, secret `[-1]` and challenge one reject the only sampled vector. -/
example : ProbComp.eval (lyubashevskySignBoundedNative (fun _ => [true])
    ((lyubashevskySigningParams 0, [[-1]], [[1]], []), 1)) = PMF.pure none := by
  have hp : lyubashevskySignPostprocess (fun _ => [true])
      ((((1, 1, 1, 0), (2, 4, 1)), [[-1]], [[1]], []), [-4]) = none := by decide
  simp [lyubashevskySignBoundedNative, lyubashevskySignAttemptNative,
    sampleIntBoxList, sampleIntBox, ProbComp.sampleModNat, OracleComp.replicate,
    lyubashevskySigningParams, LyubashevskyParams.m, LyubashevskyParams.width,
    LyubashevskyParams.γ, boxShift, hp]

/-- A typed hash genuinely selects its challenge from the commitment. -/
def hashZero : Unit × (Fin 1 → ZMod 2) → BitString 1 :=
  fun (_, commitment) => ![decide (commitment 0 = 0)]

example : hashZero ((), ![0]) = ![true] ∧ hashZero ((), ![1]) = ![false] := by decide

/-- The abort bound accepts this commitment-dependent hash without a fixed-challenge premise. -/
example : lyubashevskySignAttempt 1 1 1 2 4 1 hashZero !![1] (!![1], !![1]) () none ≤
    (4 / 9 : ℝ≥0∞) := by
  simpa [show (2 * 4 + 1 : ℝ≥0∞) = 9 by norm_num] using
    lyubashevskySignAttempt_none_le (η := 1) (by decide : 2 * 1 ≤ 4)
    (by decide : 1 * 1 ≤ 1) (by decide : ∀ i j, |(!![1] : Matrix (Fin 1) (Fin 1) ℤ) i j| ≤ 1)
    (!![1], !![1]) hashZero ()

/-- The same machine certificate charges unary security and the full raw inputs. -/
example : IsPPTOn
    (encPair encUnary
      (encPair (encList (encList encIntBin)) (encPair (encList (encList encIntBin)) encBits)))
    (encOption (encPair encBits encBits))
    (fun input : ℕ × List (List ℤ) × List (List ℤ) × List Bool =>
      let (security, secret, matrix, msg) := input
      lyubashevskySignBoundedNative (fun _ => [true])
        ((lyubashevskySigningParams security, secret, matrix, msg), security + 1)) :=
  isPPTOn_lyubashevskySigningParams (ComputableInPolyTime.const [true])

/-- All-one secrets witness the bound's satisfiable hypothesis in every growing dimension. -/
example (A : (security : ℕ) →
      Matrix (Fin (security + 1)) (Fin (security + 1)) (ZMod (2 ^ (security + 1)))) :
    Negligible (fun security =>
      (ProbComp.eval (lyubashevskySignBoundedNative (fun _ => [true])
        (lyubashevskySignInput (lyubashevskySigningParams security)
          (fun _ _ => 1) (A security) [], security + 1)) none).toNNReal) :=
  negligible_lyubashevskySigningParams_failure (fun _ _ _ => 1) (by simp)
    A (fun _ => [true]) (fun _ => [])

/-- Already at λ=32 the explicit upper bound is below one percent. -/
example : (1 / 2 : ℝ≥0) ^ (32 + 1) +
    (32 + 1) ^ 2 * (8 * (32 + 1) ^ 2 + 1) / 2 ^ 32 ≤ 1 / 100 := by
  norm_num
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  norm_num

end ComplexityTests.Crypto.LyubashevskySigningParameters
