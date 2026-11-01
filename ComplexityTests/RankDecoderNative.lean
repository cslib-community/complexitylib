/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Probability.RankDecoder.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision

/-!
# Native rank-decoder resource regression

A runtime unary depth controls the number of rounds. Starting from half that depth, a constant
left-child mass makes the decoder take both right and left branches. The oracle certificate has
an explicit exponential time allowance whose exponent depends on the retained original input.
The resulting decoder keeps that exponent and polynomial workspace.

The constant masses intentionally do not satisfy a probability-tree law: native realization and
its resource bound are independent of the distribution theorem's assumptions.
-/

public section

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.BitString.RankDecoder

namespace ComplexityTests.RankDecoderNative

private def mass (_ : ℕ) (_ : List Bool) : ℕ := 1

private theorem depth_polyTime : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
  ComputableInPolyTime.unary_to_binary

private theorem rank_polyTime : ComputableInPolyTime (fun n : ℕ => n / 2) encUnary encNat :=
  ComputableInPolyTime.binary_div.comp (depth_polyTime.prod (ComputableInPolyTime.const 2))

private theorem query_polyTime :
    ComputableInPolyTime (fun s : State ℕ => mass s.input (s.prefix ++ [false]))
      (stateEncoding encUnary) encNat :=
  ComputableInPolyTime.const 1

private noncomputable def base :
    NativeCertificate (fun s : State ℕ => mass s.input (s.prefix ++ [false]))
      (stateEncoding encUnary) encNat :=
  NativeCertificate.ofPolyTime query_polyTime

private noncomputable def oracle :
    NativeCertificate (fun s : State ℕ => mass s.input (s.prefix ++ [false]))
      (stateEncoding encUnary) encNat where
  time s := base.time s * 2 ^ s.input
  space := base.space
  computes := base.computes.mono_le
    (fun _ => Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) (fun _ => le_rfl)

private theorem oracle_bound : oracle.ExpTimePolySpace (fun s => s.input) := by
  obtain ⟨C, d, h⟩ := NativeCertificate.expTimePolySpace_ofPolyTime query_polyTime (fun _ => 0)
  refine ⟨C, d, fun s => ⟨?_, (h s).2⟩⟩
  change base.time s * 2 ^ s.input ≤ _
  calc _ ≤ (C * 2 ^ 0 * ((stateEncoding encUnary s).length + 1) ^ d) * 2 ^ s.input :=
      Nat.mul_le_mul_right _ (h s).1
    _ = _ := by ring

private theorem decoder_bound :
    (nativeCertificate depth_polyTime rank_polyTime oracle).ExpTimePolySpace (fun n => n) :=
  nativeCertificate_expTimePolySpace depth_polyTime rank_polyTime oracle
    (PolyBounded.of_forall_le 1 1 fun _ => by simp) oracle_bound

-- Right branches consume rank; left branches keep the residual rank unchanged.
example : decode (mass 4) 4 [] (4 / 2) = [true, true, false, false] := by decide
example : decode (mass 5) 5 [] (5 / 2) = [true, true, false, false, false] := by decide

-- Zero rounds and invalid ranks remain ordinary total computations.
example : decode (mass 0) 0 [] 100 = [] := rfl
example : decode (mass 2) 2 [] 5 = [true, true] := by decide
example : step mass (fun n => n) (0, [true], 5) = (0, [true], 5) := by decide

-- The concrete native loop and recursive decoder agree, including the residual-rank updates.
example : ((step mass (fun n => n))^[4] (4, [], 2)).prefix =
    [true, true, false, false] := by decide

-- A finite machine realizes the runtime decoder with the original input's exponent.
example : ∃ d : ℕ, ComputableInO (fun n : ℕ => decode (mass n) n [] (n / 2)) encUnary encBits
    (fun n => 2 ^ n * (n + 1) ^ d) (fun n => (n + 1) ^ d) := by
  simpa only [encUnary_apply, List.length_replicate] using decoder_bound.computableInO

end ComplexityTests.RankDecoderNative
