/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CircuitValue.Compilation

/-! Clients of uniform function-family compilation. Input and output widths may vary with the
instance, the constructor is certified, and correctness covers every assignment to live inputs. -/

namespace ComplexityTests.UniformCircuits

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-- One constructor builds reversal circuits at every instance-dependent input length. -/
theorem reverseFamily :
    ∃ circuits : (a : List Bool) → Circuit signature a.length a.length,
      ComputableInPolyTime (fun a => (circuits a).code) encBits encCode ∧
      ∀ a (x : Fin a.length → Bool) (j : Fin a.length),
        (circuits a).eval interpretation x j = (List.ofFn x).reverse.getD j.val false :=
  CircuitValue.exists_uniformCircuitFamily (F := fun p : List Bool × List Bool => p.2.reverse)
    (.of_tidy ComputableTidilyInPolyTime.length_bits)
    (.of_tidy ComputableTidilyInPolyTime.length_bits) (by fun_prop)

/-- Fixed output width is independent of input width. An empty function output is padded with
false, including at input length zero. -/
theorem paddedFamily :
    ∃ circuits : (a : List Bool) → Circuit signature a.length 3,
      ComputableInPolyTime (fun a => (circuits a).code) encBits encCode ∧
      ∀ a (x : Fin a.length → Bool) (j : Fin 3),
        (circuits a).eval interpretation x j = false := by
  obtain ⟨circuits, hc, he⟩ := CircuitValue.exists_uniformCircuitFamily
    (.of_tidy ComputableTidilyInPolyTime.length_bits)
    (.of_tidy (ComputableTidilyInPolyTime.const 3))
    (.of_tidy (ComputableTidilyInPolyTime.const ([] : List Bool)
      (encIn := encPair encBits encBits) (encMid := encBits)))
  exact ⟨circuits, hc, fun a x j => by simpa using he a x j⟩

/-- An empty output family is admitted, even for an input type with arbitrarily long encodings. -/
example : ∃ circuits : (a : List Bool) → Circuit signature a.length 0,
    ComputableInPolyTime (fun a => (circuits a).code) encBits encCode := by
  obtain ⟨circuits, hc, _⟩ := CircuitValue.exists_uniformCircuitFamily
    (.of_tidy ComputableTidilyInPolyTime.length_bits)
    (.of_tidy (ComputableTidilyInPolyTime.const 0))
    (.of_tidy (ComputableTidilyInPolyTime.const ([] : List Bool)
      (encIn := encPair encBits encBits) (encMid := encBits)))
  exact ⟨circuits, hc⟩

/-- info: 'Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.exists_uniformCircuitFamily

end ComplexityTests.UniformCircuits
