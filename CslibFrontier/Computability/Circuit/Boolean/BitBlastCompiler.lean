/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.BitBlast
public import CslibFrontier.Foundations.Data.BitString.Block

/-!
# Boolean circuits for encoded bounded-arity computations

A carrier with a left-invertible fixed-width encoding admits Boolean circuit simulation of any
circuit whose operations have at most two arguments. Inputs and outputs are packed in
wire-major order. The circuit has free Boolean input wires; correctness is required on valid
encoded carrier inputs. Malformed codes are not assigned source semantics.

The construction lifts the source operations to whole bit strings, simulates that interpretation
in the full binary basis, and bit-blasts with the identity encoding. Carrier homomorphisms
supply correctness on the original carrier. This avoids an extra per-input decoding budget.

This advances the arithmetic-to-Boolean direction of [Arora–Barak, web draft 2007-01-08,
Chapter 14 Exercise 1, printed p. 265/PDF p. 281][AroraBarak07]. No reverse simulation,
encoding-construction theorem or compiler-runtime bound is claimed.

## Main results

* `Cslib.Circuits.Circuit.exists_encoded_boolean`: Boolean simulation on valid encoded inputs,
  with unchanged per-gate bit-blasting cost.
-/

public section

universe v

namespace Cslib.Circuits

variable {F : Type*} {w : ℕ}

private def encodedInterpretation {σ : Signature.{v}} (I : Interpretation σ F)
    (enc : F → BitString w) (decode : BitString w → F) : Interpretation σ (BitString w) :=
  fun op input => enc (I op (decode ∘ input))

/-- A circuit on a left-invertibly encoded carrier has a Boolean circuit on free input bits.
All encoded outputs are preserved on valid encoded inputs; constants count as gates, wires are
free, and no additive input-size overhead is charged. -/
theorem Circuit.exists_encoded_boolean {σ : Signature.{v}} (I : Interpretation σ F)
    (hArity : ∀ op, σ.Arity op ≤ 2) (enc : F → BitString w) (decode : BitString w → F)
    (hdecode : Function.LeftInverse decode enc) {N M : ℕ} (c : Circuit σ N M) :
    ∃ b : Circuit Boolean.signature (N * w) (M * w),
      b.size ≤ c.size * bitBlastCost w ∧
        ∀ x, b.eval Boolean.interpretation (BitString.blocksEquiv.symm (enc ∘ x)) =
          BitString.blocksEquiv.symm (enc ∘ c.eval I x) := by
  let J := encodedInterpretation I enc decode
  let hom : Homomorphism I J :=
    ⟨enc, fun op input => congrArg (fun v => enc (I op v))
      (funext fun a => (hdecode (input a)).symm)⟩
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le (fullInterpretation_simulatesWithCost J hArity)
  have hle : d.size ≤ c.size := by simpa using hsize
  let φ : Fin N → (Fin (N * w) → Bool) → BitString w :=
    fun i y j => y (finProdFinEquiv (i, j))
  have hbits : ∀ i j, bitsOf (_root_.id : BitString w → BitString w) (φ i) j ∈ inputs (N * w) :=
    fun i j => ⟨finProdFinEquiv (i, j), rfl⟩
  have hs := Synthesis.bitBlast (_root_.id : BitString w → BitString w)
    _root_.id (fun _ => rfl) d φ hbits
  let output : Fin (M * w) → BooleanFunction (N * w) := fun k =>
    bitsOf (_root_.id : BitString w → BitString w)
      (fun y => d.eval fullInterpretation (fun i => φ i y) (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2
  have hout : Synthesis Boolean.interpretation (inputs (N * w)) (Set.range output)
      (d.size * bitBlastCost w) := by
    refine hs.mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨k, rfl⟩
    exact ⟨finProdFinEquiv.symm k, rfl⟩
  obtain ⟨b, hb, hbsize⟩ := hout.exists_circuit_outputs
  refine ⟨b, hbsize.trans (Nat.mul_le_mul_right _ hle), ?_⟩
  intro x
  rw [hb]
  have hmap := c.map_eval hom x
  ext k
  simp only [output, bitsOf, id_eq, φ, BitString.blocksEquiv_symm_apply, Equiv.symm_apply_apply]
  rw [hd]
  change (c.eval J (enc ∘ x) (finProdFinEquiv.symm k).1)
      (finProdFinEquiv.symm k).2 = _
  rw [← hmap]

end Cslib.Circuits
