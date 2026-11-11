/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.MXCircuit

/-! Checks of the AC⁰[2] circuits reading the bit-indexed polynomial design: the selection used
inside a larger circuit, the size bound at a fixed number of rows, and the membership test. -/

namespace CslibFrontierTests.NisanWigdersonMXCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Unbounded
  Cslib.Crypto.PRG.NisanWigderson Finset

/-- A client: one `MOD₂` gate on the outputs of the selection computes the parity of the seed
bits in block `i`, with depth at most `5` whatever `n` and `ℓ`. -/
example (n ℓ : ℕ) (i : BitString ℓ) (z : Fin (n * 2 ^ binaryFieldDegree n) → Bool) :
    ((parityOnCircuit univ).comp (mxCircuit n ℓ)).eval (extInterpretation (modGate 2))
        (Fin.append i z) 0 =
      parity n ((Design.binaryPolynomial n ℓ).restrict (BitString.equivFin ℓ i) z) ∧
      ((parityOnCircuit univ).comp (mxCircuit n ℓ)).depth ≤ 5 := by
  refine ⟨?_, (Circuit.depth_comp_le _ _).trans ?_⟩
  · rw [Circuit.eval_comp, eval_mxCircuit, eval_parityOnCircuit]
    rfl
  · have := depth_mxCircuit_le n ℓ
    rw [depth_parityOnCircuit]
    omega

/-- With three rows, the selection has at most `45` gates, for every index length `ℓ`. -/
example (ℓ : ℕ) : (mxCircuit 3 ℓ).size ≤ 45 :=
  size_mxCircuit_le 3 ℓ

/-- The membership test accepts exactly the cells of the block: row `j` has one cell in block
`i`, so exactly one column `v` is accepted. -/
example (n ℓ : ℕ) (i : BitString ℓ) (j : Fin n) :
    ∃! v : Fin (2 ^ binaryFieldDegree n),
      (memCircuit n ℓ j v).eval (extInterpretation (modGate 2)) i 0 = true := by
  simp only [eval_memCircuit, decide_eq_true_iff, Design.mem_block_binaryPolynomial_iff]
  exact ⟨_, fun c => congrFun ((BitString.equivFin _).symm_apply_apply _) c,
    fun w hw => (Equiv.symm_apply_eq _).1 (funext hw)⟩

/-- The membership test has `2 e + 1` gates and depth at most `3`. -/
example (n ℓ : ℕ) (j : Fin n) (v : Fin (2 ^ binaryFieldDegree n)) :
    (memCircuit n ℓ j v).size = 2 * binaryFieldDegree n + 1 ∧
      (memCircuit n ℓ j v).depth ≤ 3 :=
  ⟨size_memCircuit j v, depth_memCircuit_le j v⟩

end CslibFrontierTests.NisanWigdersonMXCircuit
