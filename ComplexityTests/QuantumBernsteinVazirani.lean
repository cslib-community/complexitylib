/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.BernsteinVazirani

/-! The Bernstein–Vazirani algorithm on concrete inputs with `N = 4` positions, identified with the
strings `{0,1}^2`. -/

namespace ComplexityTests.QuantumBernsteinVazirani

open Cslib Cslib.Quantum Cslib.BitString

/-- The positions `Fin 4` identified with `{0,1}^2`. -/
noncomputable def e4 : Fin 4 ≃ (Fin 2 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The hidden string `s = 10`. -/
def s10 : Fin 2 → Bool := ![true, false]

-- The input is the truth table of `a ↦ s ⬝ a = a₀`.
example (a : Fin 2 → Bool) : linearTable e4 s10 (e4.symm a) = a 0 := by
  simp only [linearTable, Equiv.apply_symm_apply, s10, dotProduct, Fin.sum_univ_two]
  cases a 0 <;> cases a 1 <;> rfl

-- One query leaves the algorithm in `|s, 1⟩`, so measuring the query register gives `s`.
example : run (bernsteinVazirani e4) (bernsteinVaziraniInit e4) (linearTable e4 s10) 1 =
    ket (e4.symm s10, true, ()) :=
  run_bernsteinVazirani e4 s10

example : regProb (run (bernsteinVazirani e4) (bernsteinVaziraniInit e4) (linearTable e4 s10) 1)
    (e4.symm s10) = 1 :=
  regProb_run_bernsteinVazirani e4 s10

-- The zero string is recovered from the all-zero table.
example : regProb (run (bernsteinVazirani e4) (bernsteinVaziraniInit e4) (fun _ => false) 1)
    (e4.symm 0) = 1 := by
  have h : linearTable e4 0 = fun _ => false := funext fun i => zero_dotProduct _
  rw [← h]
  exact regProb_run_bernsteinVazirani e4 0

end ComplexityTests.QuantumBernsteinVazirani
