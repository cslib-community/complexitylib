/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Basic
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Approximating the gates of a quantum circuit

Replacing every gate of a circuit by a nearby gate moves the circuit's unitary by at most the sum of
the distances, in the operator norm (`Cslib.Quantum.Circuit.norm_matrix_sub_matrix_le`):
`‖U_m ⋯ U_1 - V_m ⋯ V_1‖ ≤ ∑ ‖U_i - V_i‖`. The same holds when whole subcircuits are replaced
(`Cslib.Quantum.Circuit.norm_matrix_flatten_sub_matrix_flatten_le`), which is how a circuit over one
gate set is compiled into another. The final states move by at most the distance of the unitaries
times the norm of the initial state (`Cslib.Quantum.Circuit.norm_eval_sub_eval_le`), and the
probability of every set of measurement outcomes by at most the distance of the unitaries
(`Cslib.Quantum.Circuit.abs_measureProb_eval_sub_le`), through
`Cslib.Quantum.abs_measureProb_sub_le_norm_sub`. Gates `ε`-close to the original ones therefore
change every measurement probability by at most `m ε`
(`Cslib.Quantum.Circuit.abs_measureProb_run_sub_le`).

The norm on matrices is the operator norm on `ℓ²`, the scoped instance
`Matrix.Norms.L2Operator` of Mathlib; it makes matrices a C⋆-ring, in which unitaries have norm
one. Statements mentioning `‖(U : Matrix _ _ ℂ)‖` refer to it and need
`open scoped Matrix.Norms.L2Operator`.

## Main results

* `Cslib.Quantum.norm_mul_sub_mul_le_of_mem_unitary`: `‖a u - b v‖ ≤ ‖u - v‖ + ‖a - b‖` for
  unitaries `a` and `v` of a C⋆-ring.
* `Cslib.Quantum.Circuit.norm_matrix_sub_matrix_le`: gate by gate, the distances add up.
* `Cslib.Quantum.Circuit.norm_matrix_flatten_sub_matrix_flatten_le`: block by block, the distances
  add up.
* `Cslib.Quantum.Circuit.norm_matrix_sub_matrix_le_mul`: gates `ε`-close give unitaries `m ε`-close.
* `Cslib.Quantum.Circuit.norm_eval_sub_eval_le`,
  `Cslib.Quantum.Circuit.abs_measureProb_eval_sub_le`: nearby unitaries give nearby final states
  and nearby measurement probabilities.
* `Cslib.Quantum.Circuit.abs_measureProb_run_sub_le`: the measurement probabilities of circuits
  whose gates are `ε`-close differ by at most `m ε`.

These are the standard error estimates of circuit approximation (the hybrid argument); no source
locator is claimed. They are the bookkeeping step of the comparison of `BQP` with Arora and Barak's
definition by arbitrary elementary gates ([Arora, Barak][AroraBarak09]).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- **One step of the hybrid argument**: in a C⋆-ring, `‖a u - b v‖ ≤ ‖u - v‖ + ‖a - b‖` when `a`
and `v` are unitary, since `a u - b v = a (u - v) + (a - b) v`. -/
theorem norm_mul_sub_mul_le_of_mem_unitary {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {a b u v : E} (ha : a ∈ unitary E) (hv : v ∈ unitary E) :
    ‖a * u - b * v‖ ≤ ‖u - v‖ + ‖a - b‖ := by
  have e : a * u - b * v = a * (u - v) + (a - b) * v := by noncomm_ring
  rw [e, ← CStarRing.norm_mem_unitary_mul (u - v) ha, ← CStarRing.norm_mul_mem_unitary (a - b) hv]
  exact norm_add_le _ _

namespace Circuit

/-- Running `C ++ C'` instead of `D ++ D'` moves the unitary by at most the two distances. -/
theorem norm_matrix_append_sub_le (C C' D D' : Circuit n) :
    ‖(matrix (C ++ C') : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix (D ++ D')‖ ≤
      ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖ +
        ‖(matrix C' : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D'‖ := by
  rw [matrix_append, matrix_append, Submonoid.coe_mul, Submonoid.coe_mul]
  exact norm_mul_sub_mul_le_of_mem_unitary (matrix C').2 (matrix D).2

/-- **Approximating a circuit gate by gate**: for circuits of the same length,
`‖U_m ⋯ U_1 - V_m ⋯ V_1‖ ≤ ∑ ‖U_i - V_i‖`. -/
theorem norm_matrix_sub_matrix_le (C D : Circuit n) (h : C.length = D.length) :
    ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖ ≤
      (List.zipWith (fun g g' => ‖(g.matrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
        g'.matrix‖) C D).sum := by
  induction C generalizing D with
  | nil =>
    cases D with
    | nil => simp
    | cons _ _ => simp at h
  | cons g C ih =>
    cases D with
    | nil => simp at h
    | cons g' D =>
      rw [List.length_cons, List.length_cons, add_left_inj] at h
      rw [List.zipWith_cons_cons, List.sum_cons, matrix_cons, matrix_cons, Submonoid.coe_mul,
        Submonoid.coe_mul]
      have := norm_mul_sub_mul_le_of_mem_unitary (u := (g.matrix : Matrix _ _ ℂ))
        (b := (matrix D : Matrix _ _ ℂ)) (matrix C).2 g'.matrix.2
      linarith [ih D h]

/-- **Approximating a circuit block by block**: replacing the subcircuits `C_1, …, C_m` by
`D_1, …, D_m` moves the unitary by at most `∑ ‖U(C_i) - U(D_i)‖`. -/
theorem norm_matrix_flatten_sub_matrix_flatten_le (Cs Ds : List (Circuit n))
    (h : Cs.length = Ds.length) :
    ‖(matrix Cs.flatten : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix Ds.flatten‖ ≤
      (List.zipWith (fun C D : Circuit n =>
        ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖) Cs Ds).sum := by
  induction Cs generalizing Ds with
  | nil =>
    cases Ds with
    | nil => simp
    | cons _ _ => simp at h
  | cons C Cs ih =>
    cases Ds with
    | nil => simp at h
    | cons D Ds =>
      rw [List.length_cons, List.length_cons, add_left_inj] at h
      rw [List.zipWith_cons_cons, List.sum_cons, List.flatten_cons, List.flatten_cons]
      linarith [norm_matrix_append_sub_le C Cs.flatten D Ds.flatten, ih Ds h]

/-- **Uniformly close gates**: if corresponding gates of two circuits of length `m` are `ε`-close,
their unitaries are `m ε`-close. -/
theorem norm_matrix_sub_matrix_le_mul {C D : Circuit n} {ε : ℝ}
    (h : List.Forall₂ (fun g g' => ‖(g.matrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
      g'.matrix‖ ≤ ε) C D) :
    ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖ ≤ C.length * ε := by
  refine (norm_matrix_sub_matrix_le C D h.length_eq).trans ?_
  induction h with
  | nil => simp
  | cons hgg' _ ih =>
    rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul,
      add_comm _ ε]
    exact add_le_add hgg' ih

/-- **Nearby unitaries give nearby final states**: `‖C ψ - D ψ‖ ≤ ‖U(C) - U(D)‖ ‖ψ‖`. -/
theorem norm_eval_sub_eval_le (C D : Circuit n) (ψ : Qubits n) :
    ‖eval C ψ - eval D ψ‖ ≤
      ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖ * ‖ψ‖ := by
  have e : eval C ψ - eval D ψ = (EuclideanSpace.equiv (Fin n → Bool) ℂ).symm
      (((matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
        (matrix D : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) *ᵥ ψ.ofLp) := by
    ext y
    simp [eval, sub_mulVec]
  rw [e]
  exact l2_opNorm_mulVec _ ψ

/-- **Nearby unitaries give nearby measurement probabilities**: started in a unit state, two
circuits give every set of outcomes probabilities differing by at most `‖U(C) - U(D)‖`. -/
theorem abs_measureProb_eval_sub_le (C D : Circuit n) {ψ : Qubits n} (hψ : ‖ψ‖ = 1)
    (S : Finset (Fin n → Bool)) :
    |measureProb (eval C ψ) S - measureProb (eval D ψ) S| ≤
      ‖(matrix C : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) - matrix D‖ := by
  refine (abs_measureProb_sub_le_norm_sub (by rw [norm_eval, hψ]) (by rw [norm_eval, hψ])
    S).trans ?_
  simpa [hψ] using norm_eval_sub_eval_le C D ψ

/-- **Measuring circuits with `ε`-close gates**: if corresponding gates of two circuits of length
`m` are `ε`-close, then from every basis state they give every set of outcomes probabilities
differing by at most `m ε`. -/
theorem abs_measureProb_run_sub_le {C D : Circuit n} {ε : ℝ}
    (h : List.Forall₂ (fun g g' => ‖(g.matrix : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) -
      g'.matrix‖ ≤ ε) C D) (x : Fin n → Bool) (S : Finset (Fin n → Bool)) :
    |measureProb (run C x) S - measureProb (run D x) S| ≤ C.length * ε :=
  (abs_measureProb_eval_sub_le C D (norm_ket x) S).trans (norm_matrix_sub_matrix_le_mul h)

end Circuit

end Cslib.Quantum
