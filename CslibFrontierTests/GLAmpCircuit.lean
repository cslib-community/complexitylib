/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmpCircuit

/-! Checks of the Goldreich–Levin amplification `glAmp` and its AC⁰[2] circuit: concrete values of
`glAmp`, the gadgets on concrete inputs, and the circuit built from a parity gate. -/

namespace CslibFrontierTests.GLAmpCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded Finset

/-! ### Values of the amplification -/

/-- The blocks `10` and `11` have parities `1` and `0`. The mask `11` selects both, so the
amplification is `1 ⊕ 0 = 1`. -/
example : glAmp (parity 2) 2 ![true, false, true, true, true, true] = true := by
  decide

/-- With the mask `01`, only the second block, of parity `0`, is selected. -/
example : glAmp (parity 2) 2 ![true, false, true, true, false, true] = false := by
  decide

/-! ### The gadgets on concrete inputs -/

/-- A `MOD₂` gate on the inputs `0` and `2` of `111` reads two ones. -/
example : (parityOnCircuit {0, 2}).eval (extInterpretation (modGate 2))
    ![true, true, true] 0 = false := by
  rw [eval_parityOnCircuit]
  decide

/-- The inner product of `110` and `111` over GF(2) is `1 + 1 + 0 = 0`. -/
example : (innerProductCircuit 3).eval (extInterpretation (modGate 2))
    (Fin.append ![true, true, false] ![true, true, true]) 0 = false := by
  rw [eval_innerProductCircuit]
  decide

/-- Two constant gates give the string `101` at any input. -/
example (x : BitString 4) :
    (constsCircuit toExt ![true, false, true]).eval (extInterpretation (modGate 2)) x 2 =
      true := by
  rw [eval_constsCircuit]
  rfl

/-- A conjunction on each of three blocks of two bits: the blocks of `111000` are `11`, `10` and
`00`. -/
example : ((andCircuit (n := 2) 0 1).replicateScalar 3).eval (extInterpretation (modGate 2))
    ![true, true, true, false, false, false] = ![true, false, false] := by
  rw [Circuit.eval_replicateScalar]
  simp only [eval_andCircuit]
  decide

/-! ### The circuit for the amplification of parity -/

/-- A `MOD₂` gate on all `n` inputs computes `parity n`. -/
theorem computes_parityOnCircuit_univ (n : ℕ) :
    (parityOnCircuit (univ : Finset (Fin n))).Computes (extInterpretation (modGate 2))
      (single (parity n)) :=
  fun x => funext fun o => eval_parityOnCircuit _ x o

/-- Amplifying parity on three bits with four copies gives an AC⁰[2] circuit with `4 + 4 + 1`
gates and depth at most `1 + 2`. -/
example :
    (glAmpCircuit (Signature.Hom.id _) (parityOnCircuit (univ : Finset (Fin 3))) 4).Computes
        (extInterpretation (modGate 2)) (single (glAmp (parity 3) 4)) ∧
      (glAmpCircuit (Signature.Hom.id _) (parityOnCircuit (univ : Finset (Fin 3))) 4).size = 9 ∧
      (glAmpCircuit (Signature.Hom.id _) (parityOnCircuit (univ : Finset (Fin 3))) 4).depth ≤ 3 :=
  ⟨(computes_parityOnCircuit_univ 3).glAmpCircuit _ 4, by simp,
    (depth_glAmpCircuit_le _ _ _).trans (by simp)⟩

/-- The circuit evaluated on the first input above. -/
example : (glAmpCircuit (Signature.Hom.id _) (parityOnCircuit (univ : Finset (Fin 2))) 2).eval
    (extInterpretation (modGate 2)) ![true, false, true, true, true, true] 0 = true := by
  simp only [eval_glAmpCircuit, eval_parityOnCircuit]
  decide

end CslibFrontierTests.GLAmpCircuit
