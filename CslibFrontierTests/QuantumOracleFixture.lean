/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic

/-! Shared one-bit oracle fixture for the circuit and sampled-interference clients. -/

public section

namespace CslibFrontierTests.QuantumOracle

open Cslib.Quantum

/-- The generic XOR-query law in explicit two-bit coordinates. -/
theorem xorQuery_oneBit_ket (H : (Fin 1 → Bool) → Fin 1 → Bool) (x : Fin 2 → Bool) :
    (xorQuery H (Function.Embedding.refl _)).eval (ket x) =
      ket ![x 0, x 1 ^^ H (fun _ => x 0) 0] := by
  let A : Fin (1 + 1) ↪ Fin 2 := Function.Embedding.refl _
  let w : {j // ¬∃ i, A i = j} → Bool := fun _ => false
  have hin (r : Fin 1 → Bool) :
      (queryRegisters A).symm ((fun _ => x 0), r, w) = ![x 0, r 0] := by
    funext j
    fin_cases j
    · exact queryRegisters_symm_query A _ _ w 0
    · exact queryRegisters_symm_response A _ _ w 0
  have hx : ![x 0, x 1] = x := by
    ext j
    fin_cases j <;> rfl
  simpa only [hin, hx, Pi.add_apply, Bool.add_eq_xor, A] using
    xorQuery_eval_ket H A (fun _ => x 0) (fun _ => x 1) w

end CslibFrontierTests.QuantumOracle
