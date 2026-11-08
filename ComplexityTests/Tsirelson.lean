/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.TwoProverGame.Tsirelson

/-! # Quantum strategies for CHSH and Tsirelson's bound

Checked instances of the POVM and quantum-strategy API: the trivial and computational-basis
measurements, the projective measurement of a `±1` observable (and that such an observable is
unitary), deterministic strategies as quantum strategies, the winning probability of specific
deterministic strategies for CHSH, and Tsirelson's bound, which shows that no quantum strategy wins
CHSH with certainty.
-/

namespace ComplexityTests.Tsirelson

open Matrix Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open scoped Real

/-! ### POVMs -/

/-- The bit-flip matrix, a `±1` observable on a qubit. -/
def flip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem isHermitian_flip : flip.IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [flip]

theorem flip_mul_self : flip * flip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip, Matrix.mul_apply, Fin.sum_univ_two]

-- A `±1` observable is unitary.
example : flip ∈ unitaryGroup (Fin 2) ℂ :=
  mem_unitaryGroup_of_isHermitian_of_mul_self isHermitian_flip flip_mul_self

-- The projective measurement of a `±1` observable recovers the observable.
example : (POVM.ofObservable flip isHermitian_flip flip_mul_self).observable = flip :=
  POVM.observable_ofObservable _ _ _

-- The identity is the observable of the measurement that always answers `false`.
example : (POVM.ofObservable (1 : Matrix (Fin 2) (Fin 2) ℂ) isHermitian_one (mul_one 1)).effect
    true = 0 := by
  simp [POVM.ofObservable]

-- The trivial measurement reports its outcome with certainty on a unit state.
example : (POVM.const true : POVM Bool (Fin 2)).prob (ket 0) true = 1 := by
  simp [POVM.prob_const]

-- The computational-basis POVM is the computational-basis measurement.
example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    POVM.basis.measure ψ hψ = Cslib.Quantum.measure ψ hψ :=
  POVM.measure_basis ψ hψ

/-! ### Deterministic strategies -/

-- Alice and Bob echoing their questions win only on `(0, 0)`.
example : chsh.winProb id id = 1 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type]

-- Alice echoing her question and Bob answering `0` is optimal.
example : chsh.winProb id (fun _ => false) = 3 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type]
  norm_num

-- A deterministic strategy is a quantum strategy with the same winning probability.
example : chsh.quantumWinProb (QuantumStrategy.ofDeterministic (fun _ => false) fun _ => false) =
    3 / 4 := by
  rw [quantumWinProb_ofDeterministic, winProb_chsh_const]

-- A deterministic strategy has correlation `±1`: here `a = b = false`, so `+1`.
example (x y : Bool) :
    (QuantumStrategy.ofDeterministic (fun _ : Bool => false) fun _ : Bool => false).correlation
      x y = 1 := by
  rw [QuantumStrategy.correlation_eq]
  simp [QuantumStrategy.prob, QuantumStrategy.ofDeterministic, POVM.const]

/-! ### Values -/

-- Entanglement does not hurt.
example : (3 / 4 : ℝ) ≤ chsh.quantumValue := value_chsh ▸ chsh.value_le_quantumValue

-- Tsirelson's bound: no quantum strategy wins CHSH with certainty.
example : chsh.quantumValue < 1 := by
  refine quantumValue_chsh_le.trans_lt ?_
  rw [cos_sq_pi_div_eight]
  nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

end ComplexityTests.Tsirelson
