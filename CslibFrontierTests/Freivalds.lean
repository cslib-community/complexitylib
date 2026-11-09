/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.Freivalds
import Mathlib.Algebra.Field.ZMod

/-!
# Freivalds verifier tests

Concrete runs of the costed check, its exact operation count, and the probability statements.
`A * B` and `C` below differ in one entry, so one vector exposes the error and another does not:
the verifier needs randomness, and its soundness error is not zero. A `1 × 1` instance accepts an
incorrect product with probability exactly `1/2`, so the `0`/`1` bound is attained. Over
`ZMod 4` the encoding `id` violates the injectivity hypothesis, and the counting bound it
supports fails there; the `0`/`1` encoding satisfies it.
-/

namespace CslibFrontierTests.Freivalds

open Cslib Cslib.Algorithms.Lean.Freivalds Cslib.Probability
open scoped Matrix ENNReal
open Cslib.Algorithms.Lean (TimeM)

set_option linter.hashCommand false

private def A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 4]
private def B : Matrix (Fin 2) (Fin 2) ℤ := !![5, 6; 7, 8]
/-- `A * B = !![19, 22; 43, 50]`; `C` is wrong only in the bottom-right entry. -/
private def C : Matrix (Fin 2) (Fin 2) ℤ := !![19, 22; 43, 51]

/-! ## Executable checks -/

-- The correct product passes on every vector.
#guard (checkM A B !![19, 22; 43, 50] ![1, 1]).ret
-- The vector `(1, 0)` misses the wrong entry, `(0, 1)` exposes it.
#guard (checkM A B C ![1, 0]).ret
#guard !(checkM A B C ![0, 1]).ret
-- Exact cost of one `2 × 2` check: `2 * (4 + 4 + 4) + 2 = 26` operations.
#guard (checkM A B C ![0, 1]).time = 26
-- Three checks cost three times as much, and one failure rejects.
#guard (checkAllM A B C 3 ![![1, 0], ![1, 1], ![0, 0]]).time = 78
#guard !(checkAllM A B C 3 ![![1, 0], ![1, 1], ![0, 0]]).ret
#guard (checkAllM A B C 2 ![![1, 0], ![0, 0]]).ret
-- The costed products agree with the matrix operations.
#guard (mulVecM 2 A ![1, 1]).ret = ![3, 7]
#guard (dotProductM 3 ![1, 2, 3] ![4, 5, 6] : TimeM ℕ ℤ).ret = 32

/-! ## Completeness and soundness on the example -/

theorem mul_ne : A * B ≠ C := by decide

example (k : ℕ) : ProbComp.eval (verify bit k A B !![19, 22; 43, 50]) = PMF.pure true :=
  eval_verify_of_mul_eq _ _ (by decide)

example : ProbComp.eval (verify bit 10 A B C) true ≤ 2⁻¹ ^ 10 :=
  eval_verify_bool_true_le 10 mul_ne

example : (checkAllM A B C 10 (fun _ => ![0, 1])).time = 10 * (6 * 2 ^ 2 + 2) :=
  time_checkAllM_square A B C 10 _

/-! ## Finite-field soundness -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def A5 : Matrix (Fin 2) (Fin 3) (ZMod 5) := !![1, 2, 3; 4, 0, 1]
private def B5 : Matrix (Fin 3) (Fin 2) (ZMod 5) := !![1, 0; 2, 1; 0, 3]
private def C5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 0; 0, 0]

example : ProbComp.eval (verify id 3 A5 B5 C5) true ≤ (5⁻¹ : ℝ≥0∞) ^ 3 := by
  have h := eval_verify_field_true_le 3 (A := A5) (B := B5) (C := C5) (by decide)
  rwa [ZMod.card, Nat.cast_ofNat] at h

/-! ## The `1/2` bound is attained -/

/-- With `A = B = [1]` and `C = [0]`, the check accepts exactly when the random bit is `0`. -/
theorem eval_verify_one_true :
    ProbComp.eval (verify bit 1 (1 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ) 0)
      true = 2⁻¹ := by
  classical
  rw [eval_verify, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : (Finset.univ.filter fun xs : Fin 1 → Fin 1 → Bool => xs ∈
      (fun xs : Fin 1 → Fin 1 → Bool =>
        decide (∀ t, ((1 : Matrix (Fin 1) (Fin 1) ℤ) * 1) *ᵥ (bit ∘ xs t) =
          (0 : Matrix (Fin 1) (Fin 1) ℤ) *ᵥ (bit ∘ xs t))) ⁻¹' {true}) =
      {fun _ _ => false} := by
    ext xs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
      Set.mem_singleton_iff, decide_eq_true_eq, Finset.mem_singleton, mul_one,
      Matrix.one_mulVec, Matrix.zero_mulVec]
    constructor
    · intro h
      funext t i
      have h0 := congrFun (h t) i
      rw [Subsingleton.elim t 0, Subsingleton.elim i 0] at h0 ⊢
      cases hx : xs 0 0 <;> simp_all
    · intro h t
      funext i
      simp [h]
  rw [hfilter, Finset.card_singleton, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool]
  norm_num

/-! ## The encoding hypothesis -/

/-- Over `ZMod 4`, multiplying by `2` is not injective, so `id` is not an admissible encoding. -/
theorem not_injective_two_mul_zmod4 : ¬ Function.Injective fun s : ZMod 4 => (2 : ZMod 4) * s := by
  decide

/-- Without the hypothesis the counting bound fails: `M = [2]` and `N = [0]` agree on two of the
four vectors `x : Fin 1 → ZMod 4`, not on at most one. -/
example : (Finset.univ.filter fun x : Fin 1 → ZMod 4 =>
    (!![2] : Matrix (Fin 1) (Fin 1) (ZMod 4)) *ᵥ (id ∘ x) = (0 : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (id ∘ x)).card * Fintype.card (ZMod 4) > Fintype.card (ZMod 4) ^ Fintype.card (Fin 1) := by
  decide

/-- The `0`/`1` encoding is admissible over `ZMod 4`, so the bound applies there with `1/2`. -/
example : (Finset.univ.filter fun x : Fin 1 → Bool =>
    (!![2] : Matrix (Fin 1) (Fin 1) (ZMod 4)) *ᵥ (bit ∘ x) = (0 : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (bit ∘ x)).card * Fintype.card Bool ≤ Fintype.card Bool ^ Fintype.card (Fin 1) :=
  card_filter_mulVec_eq_mul_card_le injective_mul_bit (by decide)

end CslibFrontierTests.Freivalds
