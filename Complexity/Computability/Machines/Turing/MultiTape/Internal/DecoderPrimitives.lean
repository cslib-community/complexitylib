/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-! # Direct certificates for total decoder leaves

These witnesses apply to every input word, with the original independent degree-one cost and
output bounds. The type-indexed Decoder field can reuse them without a higher tidy calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.DecoderWords

/-- A runtime word decodes to itself. -/
theorem bits_degree : ComputableInDegree id encBits encBits 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- The unary decoder counts every symbol, including malformed false symbols. -/
theorem unary_degree : ComputableInDegree List.length encBits encUnary 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, unaryLengthT.toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show unaryLengthT.q₀ = () from rfl, unaryLengthT_run, encUnary_apply,
    encBits, Function.Embedding.refl_apply] using
    unaryLengthT.computesInTimeAndSpace_toTM w

/-- The Boolean decoder returns false on empty input and the first symbol otherwise. -/
theorem bool_degree : ComputableInDegree (fun w : List Bool => w.headD false)
    encBits encBool 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, (headDefaultT false).toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show (headDefaultT false).q₀ = false from rfl, headDefaultT_run,
    encBool_apply, encBits, Function.Embedding.refl_apply] using
    (headDefaultT false).computesInTimeAndSpace_toTM w

/-- The existing bit-list codec machine drops one symbol, including on empty input. -/
theorem tail_degree : ComputableInDegree List.tail encBits encBits 1 1 := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := encBool) (enc := encBits)
  refine ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, Q, hfin, tm, fun w => htm w⟩,
    ⟨c, fun w => ?_⟩⟩
  simpa using (htm w).length_output_le

/-- The existing bit-list codec machine tests whether the complete input is empty. -/
theorem empty_degree : ComputableInDegree List.isEmpty encBits encBool 1 1 := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.isEmpty (enc₁ := encBool) (enc := encBits)
  refine ⟨⟨_, _, ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, Q, hfin, tm, fun w => htm w⟩,
    ⟨c, fun w => ?_⟩⟩
  simpa using (htm w).length_output_le

/-- Read the initial frame on every word, including incomplete frames. -/
theorem unframe_degree : ComputableInDegree unframe encBits encBits 1 1 := by
  let τ := Internal.FrameMachines.readFrameT true
  have htm (w : List Bool) := τ.computesInTimeAndSpace_toTM w
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, τ.toTM, fun w => ?_⟩,
    ⟨3, fun w => ?_⟩⟩
  · simpa only [τ, show (Internal.FrameMachines.readFrameT true).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_true,
      encBits, Function.Embedding.refl_apply] using htm w
  · have hlen := (htm w).length_output_le
    simpa only [τ, show (Internal.FrameMachines.readFrameT true).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_true,
      encBits, Function.Embedding.refl_apply, pow_one] using hlen.trans
        (by omega : 2 * w.length + 3 ≤ 3 * (w.length + 1))

/-- Read what follows the initial frame on every word, including incomplete frames. -/
theorem dropFrame_degree : ComputableInDegree dropFrame encBits encBits 1 1 := by
  let τ := Internal.FrameMachines.readFrameT false
  have htm (w : List Bool) := τ.computesInTimeAndSpace_toTM w
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, τ.toTM, fun w => ?_⟩,
    ⟨3, fun w => ?_⟩⟩
  · simpa only [τ, show (Internal.FrameMachines.readFrameT false).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_false,
      encBits, Function.Embedding.refl_apply] using htm w
  · have hlen := (htm w).length_output_le
    simpa only [τ, show (Internal.FrameMachines.readFrameT false).q₀ = .marker from rfl,
      Internal.FrameMachines.readFrameT_run_false,
      encBits, Function.Embedding.refl_apply, pow_one] using hlen.trans
        (by omega : 2 * w.length + 3 ≤ 3 * (w.length + 1))

end Turing.MultiTapeTM.Internal.DecoderWords
