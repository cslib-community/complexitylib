/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.AmpGeneratorCircuit

/-! Checks of the circuits for the functions `g_z` of the CIKK generator: the AC⁰[2] form used by
the natural-property step, an instance amplifying parity, and what `g_z` computes on one input. -/

namespace CslibFrontierTests.NisanWigdersonAmpGeneratorCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
  Cslib.Crypto.PRG.NisanWigderson Finset

/-- The AC⁰[2] form: from an AC⁰[2] circuit of size `s` and depth `d` for `f`, every `g_z` has an
AC⁰[2] circuit of size at most `k s + 6 n'² + 3` and depth at most `d + 7`, where `n' = k n + k`. -/
example {n s d : ℕ} {f : BooleanFunction n} {C : Circuit extSignature n 1}
    (hC : C.Computes (extInterpretation (modGate 2)) (single f)) (hs : C.size ≤ s)
    (hd : C.depth ≤ d) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) :
    ∃ G : Circuit extSignature ℓ 1,
      G.Computes (extInterpretation (modGate 2)) (single ((MCSP.truthTable ℓ).symm
        (generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp f k) z))) ∧
      G.size ≤ k * s + 6 * (k * n + k) ^ 2 + 3 ∧ G.depth ≤ d + 7 := by
  obtain ⟨G, hG, hsize, hdepth⟩ := exists_circuit_generator_glAmp (Signature.Hom.id _) hC k ℓ z
  exact ⟨G, hG, hsize.trans (by gcongr), hdepth.trans (by omega)⟩

/-- On input `i`, `g_z` applies `glAmp f k` to the seed bits in block `equivFin ℓ i` of the
design. -/
example {n : ℕ} (f : BooleanFunction n) (k ℓ : ℕ)
    (z : Fin ((k * n + k) * 2 ^ binaryFieldDegree (k * n + k)) → Bool) (i : BitString ℓ) :
    (MCSP.truthTable ℓ).symm (generator (Design.binaryPolynomial (k * n + k) ℓ) (glAmp f k) z) i =
      glAmp f k ((Design.binaryPolynomial (k * n + k) ℓ).restrict (BitString.equivFin ℓ i) z) := by
  rw [MCSP.truthTable_symm_apply, generator_apply]

/-- A `MOD₂` gate on all `n` inputs computes `parity n`. -/
theorem computes_parityOnCircuit_univ (n : ℕ) :
    (parityOnCircuit (univ : Finset (Fin n))).Computes (extInterpretation (modGate 2))
      (single (parity n)) :=
  fun x => funext fun o => eval_parityOnCircuit _ x o

/-- Amplifying parity on three bits with two copies (`n' = 8`): each `g_z` has an AC⁰[2] circuit
with at most `2 + 6 · 64 + 3 = 389` gates and depth at most `1 + 7`, for every `ℓ`. -/
example (ℓ : ℕ) (z : Fin ((2 * 3 + 2) * 2 ^ binaryFieldDegree (2 * 3 + 2)) → Bool) :
    (glAmpGeneratorCircuit (Signature.Hom.id _) (parityOnCircuit univ) 2 ℓ z).Computes
        (extInterpretation (modGate 2)) (single ((MCSP.truthTable ℓ).symm
          (generator (Design.binaryPolynomial (2 * 3 + 2) ℓ) (glAmp (parity 3) 2) z))) ∧
      (glAmpGeneratorCircuit (Signature.Hom.id _) (parityOnCircuit univ) 2 ℓ z).size ≤ 389 ∧
      (glAmpGeneratorCircuit (Signature.Hom.id _) (parityOnCircuit univ) 2 ℓ z).depth ≤ 8 := by
  refine ⟨(computes_parityOnCircuit_univ 3).glAmpGeneratorCircuit _ 2 ℓ z,
    (size_glAmpGeneratorCircuit_le _ _ 2 ℓ z).trans ?_,
    (depth_glAmpGeneratorCircuit_le _ _ 2 ℓ z).trans ?_⟩
  · simp
  · simp [depth_parityOnCircuit]

end CslibFrontierTests.NisanWigdersonAmpGeneratorCircuit
