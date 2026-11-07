/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.Amplification
import ComplexityTests.BQP

/-! Error reduction for `BQP`: the reversible counter on a concrete register, the exact
acceptance probability of a majority vote over two fair coins, and exponentially small error for a
language in `BQP`. -/

namespace ComplexityTests.BQPAmplification

open Cslib Cslib.Quantum Cslib.Complexity Finset Turing.MultiTapeTM
open ComplexityTests.BQP

/-! ### The counter -/

-- Two input bits at qubits `0, 1`, one of them set; two levels from `base = 2` on, on `9` qubits.
-- After both stages, level `0` (more than zero inputs set) is one and level `1` is zero.
example : readBit (GateCode.classicalRun (Counter.codes 2 2 id 2)
    (fun i : Fin 9 => decide (i = 0))) (Counter.level 2 2 2 0) = true := by decide
example : readBit (GateCode.classicalRun (Counter.codes 2 2 id 2)
    (fun i : Fin 9 => decide (i = 0))) (Counter.level 2 2 2 1) = false := by decide
-- With both inputs set, level `1` is one.
example : readBit (GateCode.classicalRun (Counter.codes 2 2 id 2)
    (fun i : Fin 9 => decide (i.val < 2))) (Counter.level 2 2 2 1) = true := by decide

/-! ### A majority of two fair coins -/

/-- Both of two fair coins land heads with probability `1 / 4`: amplifying the family that
measures `H|0⟩` by a strict majority of two copies. -/
theorem acceptProb_amplify_hadamardOnce (x : List Bool) :
    (hadamardOnce.amplify (fun _ => 1) (ComputableInPolyTime.const _)).acceptProb x = 1 / 4 := by
  rw [UniformCircuitFamily.acceptProb_amplify, acceptProb_hadamardOnce]
  have hhalf (c : Bool) : (if c = true then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
    cases c <;> norm_num
  simp only [hhalf, prod_const, card_univ, Fintype.card_fin, sum_const, nsmul_eq_mul]
  have hcard : (univ.filter fun b : Fin (2 * 1) → Bool =>
      1 < (univ.filter fun j => b j = true).card).card = 1 := by decide
  rw [hcard]
  norm_num

/-! ### Exponentially small error -/

-- The words starting with one are accepted with probability at least `1 - 2^{-q(n)}`, and the
-- others with probability at most `2^{-q(n)}`, for every polynomial `q`.
example (q : Polynomial ℕ) : ∃ F : UniformCircuitFamily, ∀ x,
    (x ∈ FirstBit → 1 - ((2 : ℝ) ^ q.eval (encBits x).length)⁻¹ ≤ F.acceptProb (encBits x)) ∧
    (x ∉ FirstBit → F.acceptProb (encBits x) ≤ ((2 : ℝ) ^ q.eval (encBits x).length)⁻¹) :=
  mem_BQP_iff_forall_errorExponent.mp firstBit_mem_BQP q

end ComplexityTests.BQPAmplification
