/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Invariance

/-!
# Polynomial-time functions on the word RAM at logarithmic word sizes

The length of a bit string, a Turing-machine polynomial-time function with polynomially bounded
values, is uniform polynomial word-RAM time at logarithmic word sizes over `Basis.additive`, and
conversely its word-RAM program gives back a Turing machine. The value bound that the equivalence
assumes holds for every such word-RAM function.
-/

namespace ComplexityTests.WordRAMFunctionInvariance

open Cslib Cslib.WordRAM Turing.MultiTapeTM

/-- The length of a bit string, in binary, is computable in polynomial time. -/
theorem length_polyTime :
    Turing.MultiTapeTM.ComputableInPolyTime (fun l : List Bool => l.length) encBits encNat :=
  ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.encoding_length encBits)

/-- The length of a bit string is uniform polynomial word-RAM time over `Basis.additive`, on its
bits, at every word size above a logarithmic threshold. -/
theorem length_uniformComputableInPolyTime :
    UniformComputableInPolyTime .additive (fun l : List Bool => l.length)
      (fun _ l => (encBits l).map Bool.toNat) (fun l => (encBits l).length) :=
  (turingComputableInPolyTime_iff_uniformComputableInPolyTime (.id _)
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime) PolyBounded.self).1
    length_polyTime

/-- The round trip: the simulation of the word RAM turns that program back into a polynomial-time
Turing machine. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun l : List Bool => l.length) encBits encNat :=
  length_uniformComputableInPolyTime.turingComputableInPolyTime
    (Basis.standard.restrict_checkedOp_polyTime _ checkedOp_polyTime) PolyBounded.self
    (computableInPolyTime_map_toNat encBits)

/-- Every uniform polynomial-time word-RAM function on bits has polynomially bounded values, so
the equivalence's hypothesis is no restriction on the word-RAM side. -/
example {α : Type} {encIn : α ↪ List Bool} {f : α → ℕ}
    (h : UniformComputableInPolyTime .standard f (fun _ a => (encIn a).map Bool.toNat)
      (fun a => (encIn a).length)) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat ∧
      PolyBounded (fun a => (encIn a).length) f :=
  ⟨(turingComputableInPolyTime_iff_uniformComputableInPolyTime Basis.additiveHomStandard
    checkedOp_polyTime h.polyBounded).2 h, h.polyBounded⟩

end ComplexityTests.WordRAMFunctionInvariance
