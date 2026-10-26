/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Search

/-! The quantum query model: the oracle and a satisfiable instance of the search hypothesis. -/

namespace ComplexityTests.QuantumSearch

open Cslib.Quantum

/-- The unit state `|0, 1, ()⟩` with one query index, control bit `1` and a trivial workspace. -/
noncomputable def ψ₀ : State 1 Unit := EuclideanSpace.single (0, (true, ())) 1

theorem norm_ψ₀ : ‖ψ₀‖ = 1 := by simp [ψ₀]

-- With a single index, the zero-query identity algorithm outputs it with probability one, so the
-- hypothesis of `card_sub_two_le` is satisfiable.
example : ∀ z, 2 / 3 ≤ regProb (run (fun _ => LinearIsometry.id) ψ₀ (marked z) 0) z := by
  intro z
  fin_cases z
  simp [run, regProb_eq_sum, ψ₀, Fintype.sum_prod_type]
  norm_num

example : ((1 : ℕ) : ℝ) - 2 ≤ 144 * ((0 : ℕ) : ℝ) ^ 2 :=
  card_sub_two_le (fun _ => LinearIsometry.id) norm_ψ₀ 0 (by
    intro z
    fin_cases z
    simp [run, regProb_eq_sum, ψ₀, Fintype.sum_prod_type]
    norm_num)

-- The controlled phase oracle flips the sign on marked indices with control bit `1`, and leaves
-- the control-`0` part alone.
example (ψ : State 3 Unit) :
    (phaseOracle (marked 1) ψ).ofLp (1, (true, ())) = -ψ.ofLp (1, (true, ())) := by
  simp [marked]

example (ψ : State 3 Unit) :
    (phaseOracle (marked 1) ψ).ofLp (1, (false, ())) = ψ.ofLp (1, (false, ())) := by
  simp

end ComplexityTests.QuantumSearch
