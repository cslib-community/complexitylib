/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Quantum.Approximation
import CslibFrontier.Computability.Complexity.Classes.BQP.ConstantGap
import CslibFrontierTests.BQP

/-! Approximation bookkeeping for quantum circuits and `BQP` from a constant gap: exact binomial
tails of threshold votes, a Hoeffding bound checked against the exact tail, gaps on one side of
`1 / 2`, the degenerate gap below `0`, lower bounds on distances forced by measurements, and the
distance between `NOT` and the identity. -/

namespace ComplexityTests.BQPApproximation

open Cslib Cslib.Quantum Cslib.Complexity Finset Turing.MultiTapeTM
open ComplexityTests.BQP
open scoped Matrix.Norms.L2Operator

/-! ### Threshold votes over two fair coins -/

/-- At least one of two fair coins lands heads with probability `3 / 4`: the threshold vote with
`k = 2`, `t = 0` of the family measuring `H|0⟩`. -/
example (x : List Bool) :
    (hadamardOnce.threshold (fun _ => 2) (fun _ => 0) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).acceptProb x = 3 / 4 := by
  rw [UniformCircuitFamily.acceptProb_threshold_eq_sum_choose, acceptProb_hadamardOnce]
  norm_num [sum_filter, sum_range_succ, Nat.choose]

/-- Both of two fair coins land heads with probability `1 / 4`: with `k = 2`, `t = 1` the threshold
vote is the strict majority vote of `UniformCircuitFamily.amplify`. -/
example (x : List Bool) :
    (hadamardOnce.threshold (fun _ => 2) (fun _ => 1) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).acceptProb x = 1 / 4 := by
  rw [UniformCircuitFamily.acceptProb_threshold_eq_sum_choose, acceptProb_hadamardOnce]
  norm_num [sum_filter, sum_range_succ, Nat.choose]

/-! ### Hoeffding against the exact tail -/

/-- More than `5` of `8` fair coins land heads with probability `37 / 256`; the Hoeffding bound
with `δ = 1 / 4` (`8 (1 / 2 + 1 / 4) = 5 + 1`) gives `exp (-1)`, and indeed
`37 / 256 ≤ exp (-1)`. -/
example (x : List Bool) :
    (hadamardOnce.threshold (fun _ => 8) (fun _ => 5) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).acceptProb x = 37 / 256 ∧
    (hadamardOnce.threshold (fun _ => 8) (fun _ => 5) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).acceptProb x ≤ Real.exp (-1) := by
  have hexact : (hadamardOnce.threshold (fun _ => 8) (fun _ => 5) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)).acceptProb x = 37 / 256 := by
    rw [UniformCircuitFamily.acceptProb_threshold_eq_sum_choose, acceptProb_hadamardOnce]
    norm_num [sum_filter, sum_range_succ, Nat.choose]
  refine ⟨hexact, ?_⟩
  have h := hadamardOnce.acceptProb_threshold_le_exp (k := fun _ => 8) (t := fun _ => 5)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) x (δ := 1 / 4) (by norm_num)
    (by rw [acceptProb_hadamardOnce]; norm_num)
  convert h using 2
  norm_num

/-! ### Gaps away from `1 / 2` -/

/-- The words starting with one are in `BQP` by a gap between `17 / 20` and `9 / 10`, both above
`1 / 2`, where a strict majority vote does not separate. -/
example : FirstBit ∈ BQP encBits := by
  refine mem_BQP_of_gap (s := 17 / 20) (c := 9 / 10) (by norm_num) readFirst fun x => ⟨?_, ?_⟩
  · intro hx
    rw [encBits_apply, acceptProb_readFirst, ite_eq_left (show x.headD false = true from hx)]
    norm_num
  · intro hx
    rw [encBits_apply, acceptProb_readFirst, ite_eq_right (show ¬x.headD false = true from hx)]
    norm_num

/-- A gap below `0` can only describe the problem of all instances, which is in `BQP`. -/
example : (Set.univ : Set (List Bool)) ∈ BQP encBits :=
  mem_BQP_of_gap (s := -1) (c := 0) (by norm_num) hadamardOnce fun _ =>
    ⟨fun _ => hadamardOnce.acceptProb_nonneg _, fun h => absurd (Set.mem_univ _) h⟩

/-! ### Distances forced by measurements -/

/-- Distinct basis states are at distance at least `1`: they give the outcome set `{x}`
probabilities `1` and `0`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {x y : ι} (hxy : x ≠ y) :
    1 ≤ ‖(ket x : EuclideanSpace ℂ ι) - ket y‖ := by
  have h := abs_measureProb_sub_le_norm_sub (norm_ket x) (norm_ket y) {x}
  rwa [measureProb_ket, measureProb_ket, ite_eq_left (mem_singleton_self x),
    ite_eq_right (by simpa using hxy.symm), sub_zero, abs_one] at h

/-- Two circuits of the same length whose measurement statistics differ by `η` on some input have
gates at total distance at least `η`. -/
example {n : ℕ} (C D : Circuit n) (h : C.length = D.length) (x : Fin n → Bool)
    (S : Finset (Fin n → Bool)) {η : ℝ}
    (hη : η ≤ |measureProb (Circuit.run C x) S - measureProb (Circuit.run D x) S|) :
    η ≤ (List.zipWith (fun g g' => ‖(g.matrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
      (g'.matrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖) C D).sum :=
  hη.trans ((Circuit.abs_measureProb_eval_sub_le C D (norm_ket x) S).trans
    (Circuit.norm_matrix_sub_matrix_le C D h))

/-! ### A telescoping instance with nonzero distance -/

/-- `NOT` on the only qubit of a one-qubit register. -/
noncomputable def notGate : PlacedGate 1 := ⟨1, Gate.not, Function.Embedding.refl _⟩

/-- The identity gate on the only qubit of a one-qubit register. -/
noncomputable def idGate : PlacedGate 1 := ⟨1, Gate.ofPerm 1, Function.Embedding.refl _⟩

theorem run_notGate : Circuit.run [notGate] (fun _ => false) = ket fun _ => true := by
  rw [Circuit.run, Circuit.eval_cons, Circuit.eval_nil]
  refine (PlacedGate.eval_ofPerm_ket _ _ _).trans (congrArg ket (funext fun j => ?_))
  fin_cases j
  exact splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ 0

theorem run_idGate : Circuit.run [idGate] (fun _ => false) = ket fun _ => false := by
  rw [Circuit.run, Circuit.eval_cons, Circuit.eval_nil]
  refine (PlacedGate.eval_ofPerm_ket _ _ _).trans (congrArg ket (funext fun j => ?_))
  fin_cases j
  exact splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ 0

/-- Replacing `NOT` by the identity moves the probability of reading `1` from `|0⟩` from `1` to
`0`. The perturbation and telescoping bounds therefore force `‖NOT - 1‖ ≥ 1`, a concrete pair of
one-gate circuits at nonzero distance. -/
example : 1 ≤ ‖(notGate.matrix : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) - idGate.matrix‖ := by
  have h := (Circuit.abs_measureProb_eval_sub_le [notGate] [idGate] (norm_ket fun _ => false)
    {fun _ => true}).trans (Circuit.norm_matrix_sub_matrix_le [notGate] [idGate] rfl)
  rw [← Circuit.run, ← Circuit.run, run_notGate, run_idGate, measureProb_ket, measureProb_ket,
    ite_eq_left (mem_singleton_self _),
    ite_eq_right fun h => Bool.false_ne_true (congrFun (mem_singleton.mp h) 0), sub_zero,
    abs_one] at h
  simpa using h

end ComplexityTests.BQPApproximation
