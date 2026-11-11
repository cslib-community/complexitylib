/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Polarization.PolyTime
import Complexity.Computability.Complexity.Problems.StatisticalDifference.PolyTime
import ComplexityTests.StatisticalDifference

/-! # Polynomial-time polarization of Statistical Difference

Checked instances: the raw code of two copies of a one-gate circuit, its agreement with
`Circuit.replicate`, the gate count of the multiplexer code, a polynomial-time polarization map
with fixed parameters, the reduction from `SD^{2/3,1/3}` to `SD^{9/10,1/10}` applied to a far and a
near instance, the length-indexed polarization applied to the same instances, the polarization
with the error parameter in unary applied to them for every `k`, and a polynomial-time
polarization of a computed instance with a computed parameter.
-/

namespace ComplexityTests.StatisticalDifferencePolyTime

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM
open ComplexityTests.StatisticalDifference

/-! ### Replicated codes -/

/-- Two copies of a negation gate on one input: copy `1` reads input `1`, and its gate reads
wire `1` and is wire `3`. -/
example : replicateCode 1 2 ([(.not, [0])], [1]) = ([(.not, [0]), (.not, [1])], [2, 3]) := by
  decide

/-- A negation gate on one input. -/
def notCircuit : Circuit signature 1 1 :=
  Circuit.oneGate Op.not fun _ => 0

/-- The raw replicated code of a typed circuit is the code of its typed copies. -/
example : replicateCode 1 2 notCircuit.code = (notCircuit.replicate 2).code :=
  replicateCode_code _ 2

/-- Zero copies give the empty code. -/
example : replicateCode 1 0 ([(.not, [0])], [1]) = ([], []) := by
  decide

/-! ### The multiplexer code -/

/-- The multiplexer on words of two bits has `3 * 2 + 1` gates. -/
example : (muxCode 2).1.length = 7 := by
  decide

example : (muxCode 2).1.length = (muxCircuit 2).code.1.length := by
  rw [muxCode_code]

/-! ### Polarization with fixed parameters -/

/-- Polarization with fixed parameters is polynomial-time. -/
example : ComputableInPolyTime (fun x : SDInstance => x.polarize 1 2 3) encSDInstance
    encSDInstance :=
  SDInstance.computableInPolyTime_polarize (ComputableInPolyTime.const 1)
    (ComputableInPolyTime.const 2) (ComputableInPolyTime.const 3)

/-- The encoding separates the far and the near instance. -/
example : encSDInstance far ≠ encSDInstance near := fun h => by
  have h := congrArg SDInstance.distance (encSDInstance.injective h)
  rw [far_distance, near_distance] at h
  exact one_ne_zero h

/-! ### The reduction between gap versions -/

/-- `SD^{2/3,1/3}` reduces to `SD^{9/10,1/10}`: the reduction maps the far instance into the
yes-set and the near instance into the no-set. -/
example : ∃ f : SDInstance → SDInstance, ComputableInPolyTime f encSDInstance encSDInstance ∧
    f far ∈ (StatisticalDifference (9 / 10) (1 / 10)).yes ∧
    f near ∈ (StatisticalDifference (9 / 10) (1 / 10)).no := by
  obtain ⟨f, hf, hyes, hno⟩ := StatisticalDifference.polyTimeReducible (α := 2 / 3) (β := 1 / 3)
    (α' := 9 / 10) (β' := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨f, hf, hyes ?_, hno ?_⟩
  · rw [mem_yes_statisticalDifference, far_distance]
    norm_num
  · rw [mem_no_statisticalDifference (by norm_num), near_distance]
    norm_num

/-! ### Error exponentially small in the instance length -/

/-- The length-indexed polarization takes the far instance to distance at least
`1 - 2⁻⁽ⁿ⁺¹⁾` and the near instance to distance at most `2⁻⁽ⁿ⁺¹⁾`, where `n` is the length of the
encoded instance. -/
example : ∃ f : SDInstance → SDInstance, ComputableInPolyTime f encSDInstance encSDInstance ∧
    1 - (1 / 2 : ℝ) ^ ((encSDInstance far).length + 1) ≤ (f far).distance ∧
    (f near).distance ≤ (1 / 2 : ℝ) ^ ((encSDInstance near).length + 1) := by
  obtain ⟨f, hf, h⟩ := SDInstance.exists_computableInPolyTime_polarize_length (α := 2 / 3)
    (β := 1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨f, hf, (h far).1 (by rw [far_distance]; norm_num),
    (h near).2 (by rw [near_distance]; norm_num)⟩

/-! ### The error parameter in unary -/

/-- With the error parameter `k` a separate unary input, as in the source, the far instance
polarizes to distance at least `1 - 2⁻⁽ᵏ⁺¹⁾` and the near instance to distance at most
`2⁻⁽ᵏ⁺¹⁾`, for every `k`. -/
example : ∃ f : SDInstance × ℕ → SDInstance,
    ComputableInPolyTime f (encPair encSDInstance encUnary) encSDInstance ∧
    ∀ k : ℕ, 1 - (1 / 2 : ℝ) ^ (k + 1) ≤ (f (far, k)).distance ∧
      (f (near, k)).distance ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  obtain ⟨f, hf, h⟩ := SDInstance.exists_computableInPolyTime_polarize_unary (α := 2 / 3)
    (β := 1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨f, hf, fun k => ⟨(h far k).1 (by rw [far_distance]; norm_num),
    (h near k).2 (by rw [near_distance]; norm_num)⟩⟩

/-- Polarization of a computed instance with computed parameters: polarizing the first component
of a pair, with the second component as the number of outer coordinates, is polynomial-time. -/
example : ComputableInPolyTime (fun p : SDInstance × ℕ => p.1.polarize 1 2 p.2)
    (encPair encSDInstance encUnary) encSDInstance :=
  SDInstance.computableInPolyTime_polarize_comp (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.const 1) (ComputableInPolyTime.const 2) (ComputableInPolyTime.snd _ _)

end ComplexityTests.StatisticalDifferencePolyTime
