/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.Boolean.BitBlast

/-!
# Bit-blasting arithmetic with injective encodings

An arithmetic circuit on a carrier `F` with a left-invertible `w`-bit encoding can be
bit-synthesized with `bitBlastCost w` Boolean gates per arithmetic gate, given the encoded input
bits. The encoding need not fill the bit cube, so odd finite fields are admitted. Arithmetic
operations first enter the existing full binary basis with unit cost, then use the existing
bit-blasting implementation.

This is a synthesis-direction milestone for [Arora–Barak, web draft 2007-01-08,
Chapter 14 Exercise 1, printed p. 265/PDF p. 281][AroraBarak07]. Input bits must already be
available as stated in the theorem. This does not construct a general finite-field encoding,
prove a reverse Boolean-to-field simulation, specify malformed encodings or certify runtime.

## Main results

* `Cslib.Circuits.Synthesis.bitBlast_arithmetic`: encoded outputs of an arithmetic circuit
  synthesized at the original per-gate bit-blasting cost.
-/

public section

namespace Cslib.Circuits.Synthesis

variable {F : Type*} [Semiring F] {w n : ℕ}

/-- Given the encoded input bits, arithmetic circuits can be bit-blasted with the same
per-gate bound as the full binary basis. Only a decoder left inverse is required. -/
theorem bitBlast_arithmetic (enc : F → BitString w) (decode : BitString w → F)
    (hdecode : Function.LeftInverse decode enc) {s : Set (BooleanFunction n)} {N M : ℕ}
    (c : Circuit (arithSignature F) N M) (φ : Fin N → (Fin n → Bool) → F)
    (hφ : ∀ i j, bitsOf enc (φ i) j ∈ s) :
    Synthesis Boolean.interpretation s
      (Set.range fun oj : Fin M × Fin w =>
        bitsOf enc (fun x => c.eval (arithInterpretation F) (fun i => φ i x) oj.1) oj.2)
      (c.size * bitBlastCost w) := by
  have hsim := fullInterpretation_simulatesWithCost (k := 2) (arithInterpretation F)
    (fun op => by cases op <;> simp [ArithOp.arity])
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le hsim
  have hle : d.size ≤ c.size := by simpa using hsize
  refine (bitBlast enc decode hdecode d φ hφ).mono Set.Subset.rfl ?_
    (Nat.mul_le_mul_right _ hle)
  rintro _ ⟨⟨o, j⟩, rfl⟩
  refine ⟨(o, j), ?_⟩
  funext x
  simp only [bitsOf, hd]

end Cslib.Circuits.Synthesis
