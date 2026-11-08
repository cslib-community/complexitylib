/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.CrossComposition
import Complexity.Computability.Complexity.Parameterized.VertexCover.BussKernel

/-!
# Tests: cross-composition and polynomial compressions

The hypotheses of the Bodlaender–Jansen–Kratsch theorem satisfied by concrete maps: "some entry is
`true`" is an OR-cross-composition of `{true}` into `{true}` with parameter `0`, and the identity
is a compression of `{true}` with size bound `1`, so the theorem places `{false}` in `NP/poly`.
"Every entry is `true`" is not an OR-cross-composition. Buss's kernel for vertex cover is a
polynomial compression, and the identity on bit strings is no compression when the parameter is
constant.
-/

namespace ComplexityTests.CrossComposition

open Cslib Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-! ### A cross-composition and a compression -/

/-- "Some entry is `true`" is an OR-cross-composition of `{true}` into `{true}` with parameter
`0`, with respect to the relation relating all instances. -/
theorem isORCrossComposition_any :
    IsORCrossComposition encBool (fun _ => true) {true} encBool (fun _ => 0) {true}
      (fun l => l.any id) fun _ => 0 := by
  refine ⟨anyWithInput (id' (encIn := encList encBool)) (snd _ _), fun l _ _ => ?_,
    fun _ _ _ _ _ => le_rfl⟩
  simp

/-- The identity is a compression of `{true}` with parameter `0` into `{true}`, with size bound
`1`. -/
theorem isCompression_id :
    IsCompression encBool (fun _ => 0) {true} encBool {true} id fun _ => 1 := by
  obtain ⟨t, s, -, -, h⟩ := ComputableInPolyTime.of_finite (encIn := encBool) (encOut := encBool) id
  refine ⟨⟨fun _ => t 1 + s 1, .const _, h.mono (fun a => ?_) fun a => ?_⟩, fun _ => Iff.rfl,
    fun _ => by simp⟩ <;>
  · simp only [encBool_apply, List.length_singleton]
    omega

/-- The theorem applies: `{false}` is in `NP/poly`. -/
example : ({false} : Set Bool) ∈ NPPoly encBool := by
  have := compl_mem_NPPoly_of_orCrossComposes Decoder.bool
    ⟨_, _, _, isPolyEquivalence_const_true encBool, .const 0, isORCrossComposition_any⟩
    (isCompression_id.hasPolyCompression (.const 1))
  have hcompl : ({true} : Set Bool)ᶜ = {false} := by
    ext b
    cases b <;> simp
  rwa [hcompl] at this

/-- "Every entry is `true`" is not an OR-cross-composition of `{true}`: on `[true, false]` it gives
`false`, although an entry is `true`. -/
example : ¬ IsORCrossComposition encBool (fun _ => true) {true} encBool (fun _ => 0) {true}
    (fun l => l.all id) fun _ => 0 := by
  intro h
  have := h.mem_iff [true, false] (by simp) (by simp)
  simp at this

/-! ### Kernels and compressions -/

/-- Buss's kernel for vertex cover gives a polynomial compression. -/
example : HasPolyCompression (encPair encGraph encNat) Prod.snd VertexCover :=
  VertexCover_hasPolyKernel.hasPolyCompression

/-- With a constant parameter, the identity on bit strings is no compression, whatever the size
bound: the output must stay shorter than `h 0 + 1`. -/
example (A : Set (List Bool)) (h : ℕ → ℕ) :
    ¬ IsCompression encBits (fun _ => 0) A encBits A id h := by
  intro hK
  have := hK.length_le (List.replicate (h 0 + 1) true)
  simp at this

end ComplexityTests.CrossComposition
