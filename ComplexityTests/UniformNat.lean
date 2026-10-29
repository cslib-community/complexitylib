/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Tactic.PPT
import Mathlib.Data.ZMod.Basic

/-! Strict fair-bit samplers: exact boundary laws and closed compositional certificates. -/

namespace ComplexityTests.UniformNat

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM

-- Binary words are most significant bit first; long words saturate before unary output grows.
example : BitString.binaryValue [true, false, false] = 4 := by decide
example : BitString.boundedBinaryValue 3 (List.replicate 8 true) = 3 := by decide
example : BitString.boundedBinaryValue 0 [true, true] = 0 := by decide

-- The range is strictly above the bound, including at powers of two and at zero.
example : dyadicSize 0 = 2 ∧ dyadicSize 3 = 4 ∧ dyadicSize 4 = 8 := by decide

-- Capping at four merges exactly half of the eight equally likely outcomes into the sentinel.
example : (ProbComp.eval (sampleBoundedIndex 4) 4).toReal = 1 / 2 := by
  rw [eval_sampleBoundedIndex]
  change (((PMF.uniformOfFintype (Fin 8)).map (fun i => min 4 i.val)) 4).toReal = 1 / 2
  norm_num [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Fin.sum_univ_succ,
    ENNReal.toReal_mul, ENNReal.toReal_inv]

-- A zero bound always returns the sentinel, despite consuming a fixed fair bit.
example : ProbComp.eval (sampleBoundedIndex 0) = PMF.pure 0 := by
  simp only [eval_sampleBoundedIndex, Nat.zero_min]
  exact PMF.map_const _ _

-- Exact dyadic acceptance includes the zero, proper-fraction and saturated endpoints.
example : ProbComp.eval (sampleDyadicCoin 3 0) true = 0 := by
  norm_num [eval_sampleDyadicCoin_true]
example : ProbComp.eval (sampleDyadicCoin 3 3) true = 3 / 4 := by
  norm_num [eval_sampleDyadicCoin_true, show dyadicSize 3 = 4 by decide]
example : (ProbComp.eval (sampleDyadicCoin 3 7) true).toReal = 1 := by
  norm_num [eval_sampleDyadicCoin_true_toReal, show dyadicSize 3 = 4 by decide]

-- Named samplers compose with captured inputs and arithmetic on the sampled unary index.
example : IsPPTOn (encPair encUnary encUnary) encBool (fun p : ℕ × ℕ => do
    let index ← sampleBoundedIndex (p.1 * p.1 + 1)
    let bit ← sampleDyadicCoin (p.1 + p.2) (index + p.2)
    return bit && decide (index < p.2)) := by
  ppt

example : ComputableInPolyTime
    (fun p : ℕ × List Bool => BitString.boundedBinaryValue (dyadicSize (p.1 + 1)) p.2)
    (encPair encUnary encBits) encUnary := by fun_prop

-- A raw word's unbounded numeric value has no polynomial unary-output certificate.
example : True := by
  fail_if_success
    have : ComputableInPolyTime BitString.binaryValue encBits encUnary := by polytime
  trivial

-- Residues of a uniform value below a multiple of the modulus are exactly uniform.
example : (PMF.uniformOfFintype (Fin 6)).map (fun x => (x.val : ZMod 3)) =
    PMF.uniformOfFintype (ZMod 3) := by
  have h := PMF.dist_map_natCast_uniformOfFintype_le 6 3
  norm_num at h
  exact h

-- Otherwise the distance is at most the leftover fraction: one extra preimage among four values.
open scoped Cslib.Probability.PMF in
example : dist ((PMF.uniformOfFintype (Fin 4)).map fun x => (x.val : ZMod 3))
    (PMF.uniformOfFintype (ZMod 3)) ≤ 1 / 4 := by
  have h := PMF.dist_map_natCast_uniformOfFintype_le 4 3
  norm_num at h
  exact h

-- Residues of `n + 8` fair bits modulo a computed modulus are strict PPT.
example : IsPPTOn encUnary encNat (fun n => sampleModNat (n + 8) (2 * n + 3)) :=
  isPPTOn_sampleModNat (by fun_prop) (by fun_prop)

end ComplexityTests.UniformNat

-- An arbitrary plain bound composes with the capped unary dyadic-size provider.
example {α : Type} {encode : α ↪ List Bool} {bound : α → ℕ}
    (hbound : Turing.MultiTapeTM.ComputableInPolyTime bound encode Turing.MultiTapeTM.encUnary) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun a => Cslib.Probability.dyadicSize (bound a)) encode Turing.MultiTapeTM.encUnary := by
  fun_prop

-- Public sampler rules consume plain numeric certificates on arbitrary encoded inputs.
example {α : Type} {input : α ↪ List Bool} {bound numerator : α → ℕ}
    (hb : Turing.MultiTapeTM.ComputableInPolyTime bound input Turing.MultiTapeTM.encUnary)
    (hn : Turing.MultiTapeTM.ComputableInPolyTime numerator input Turing.MultiTapeTM.encUnary) :
    Cslib.Probability.IsPPTOn input Turing.MultiTapeTM.encBool
      (fun a => Cslib.ProbComp.sampleDyadicCoin (bound a) (numerator a)) := by
  exact Cslib.Probability.isPPTOn_sampleDyadicCoin hb hn

example {α : Type} {input : α ↪ List Bool} {width : α → ℕ}
    (hw : Turing.MultiTapeTM.ComputableInPolyTime width input Turing.MultiTapeTM.encUnary) :
    Cslib.Probability.IsPPTOn input Turing.MultiTapeTM.encNat
      (fun a => Cslib.ProbComp.sampleBinaryNat (width a)) := by
  exact hw.sampleBinaryNat

-- The convenience theorem has one canonical public name, with no superseded raw alias.
run_elab do
  if (← Lean.getEnv).contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleBinaryNat then
    throwError "superseded raw sampler theorem remains exported"
