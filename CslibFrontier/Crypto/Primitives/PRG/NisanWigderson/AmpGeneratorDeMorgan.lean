/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.AmpGeneratorCircuit
import CslibFrontier.Computability.Circuit.Boolean.ACC0.Simulation

/-!
# The functions of the CIKK generator have small De Morgan circuits

Carmosino, Impagliazzo, Kabanets and Kolokolova's black-box generator is efficient within the
target class: each function `g_z`, whose truth table is the generator's output on the seed `z`,
has small circuits relative to the target `f` (Definition 3.1 and proof of Theorem 3.2,
pp. 10:10–10:11) [CarmosinoImpagliazzoKabanetsKolokolova2016].
`Cslib.Crypto.PRG.NisanWigderson.exists_circuit_generator_glAmp` proves this for `p = 2` in any
basis into which the unbounded fan-in basis with `MOD₂` gates translates, with a depth bound. This
file gives the form for fan-in-two De Morgan circuits, where only size is counted: if `f` has
De Morgan circuit complexity at most `s`, every `g_z` has De Morgan circuit complexity at most
`(2100 · 8)² (ℓ + k s + 6 n'² + 3 + 1) ^ 8`, with `n' = k n + k`.

The proof reads the De Morgan circuit for `f` as a circuit over the unbounded fan-in basis with
`MOD₂` gates, builds the generator circuit there, and converts back with the polynomial-size
simulation of `MOD₂` gates by De Morgan circuits
(`Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation_modGate`). The constants are this
library's and are not tight. Depth is not certified.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.complexity_generator_glAmp_le`: the De Morgan circuit
  complexity of every `g_z`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Cslib.Circuits Cslib.Circuits.Boolean

/-- **The CIKK generator in P/poly** [Carmosino et al., Definition 3.1 and proof of Theorem 3.2,
pp. 10:10–10:11][CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2` and fan-in-two De Morgan
circuits: if `f` has De Morgan circuit complexity at most `s`, then for every seed `z` the function
`g_z`, whose truth table is the Nisan–Wigderson generator of `glAmp f k` on `z` for the design
`Design.binaryPolynomial (k n + k) ℓ`, has De Morgan circuit complexity at most
`(2100 · 8)² (ℓ + k s + 6 (k n + k)² + 3 + 1) ^ 8`. Only size is counted. -/
theorem complexity_generator_glAmp_le {n s : ℕ} {f : BooleanFunction n}
    (hf : complexity interpretation (single f) ≤ s) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    complexity interpretation (single ((MCSP.truthTable ℓ).symm
        (generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp f k) z))) ≤
      (2100 * 8) ^ 2 * (ℓ + (k * s + 6 * (k * n + k) ^ 2 + 3) + 1) ^ 8 := by
  obtain ⟨C, hC, hCs⟩ := complexity_le_iff.1 hf
  -- read `C` over the unbounded fan-in basis with `MOD₂` gates
  have hC' := (hC.mapOp (φ := Unbounded.deMorganToUnbounded) (J := Unbounded.interpretation)).mapOp
    (φ := Unbounded.toExt) (J := Unbounded.extInterpretation (modGate 2))
  obtain ⟨G, hG, hGs, -⟩ := exists_circuit_generator_glAmp (Signature.Hom.id _) hC' k ℓ z
  -- and convert the generator circuit back to a De Morgan circuit
  obtain ⟨D, hDe, hDs⟩ := Unbounded.exists_deMorgan_simulation_modGate 2 G
  have hD : D.Computes interpretation _ := fun x => (congrFun hDe x).trans (hG x)
  have hG' : G.size ≤ k * s + 6 * (k * n + k) ^ 2 + 3 := by
    refine hGs.trans ?_
    simp only [Circuit.size_mapOp]
    gcongr
  refine (complexity_le_of_computes D hD).trans (hDs.trans ?_)
  have h8 : max 2 1 ^ 3 = 8 := rfl
  rw [h8]
  gcongr

end Cslib.Crypto.PRG.NisanWigderson
