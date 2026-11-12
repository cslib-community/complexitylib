/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.MvPolynomial.CoefficientDegree
import CslibFrontier.Logics.Propositional.Algebraic.FunctionalPigeonhole
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: algebraic functional pigeonhole principle (`algFPHP`)

Checked examples for `algFPHP(1, 1)`, `algFPHP(2, 1)` (including an explicit degree-`2`
Polynomial Calculus refutation over any commutative ring), the zero-hole instances `n = 0 < m`,
and empty-pigeon boundary cases `m = 0`.
-/

namespace CslibFrontierTests.ProofComplexity.AlgebraicFunctionalPigeonhole

open Cslib Cslib.Logic.PL Cslib.Logic.PL.Algebraic MvPolynomial

/-! ### `algFPHP(1, 1)`: satisfiable with a unique solution -/

example :
    (∃ x : Fin 1 × Fin 1 → Bool, IsBoolSolution (algFPHP 1 1 ℚ) x) ∧
    (∃ a : Fin 1 × Fin 1 → ℚ, ∀ p ∈ algFPHP 1 1 ℚ, eval a p = 0) ∧
    (∀ d, ¬ PC.RefutableInDegree (algFPHP 1 1 ℚ) d) ∧
    (∀ d, ¬ PC.RefutableInDegree (algFPHP 1 1 (ZMod 2)) d) :=
  ⟨exists_isBoolSolution_algFPHP_iff.2 le_rfl,
    exists_commonZero_algFPHP_iff.2 le_rfl,
    not_pc_refutableInDegree_algFPHP le_rfl,
    not_pc_refutableInDegree_algFPHP le_rfl⟩

example (x : Fin 1 × Fin 1 → Bool) (hx : IsBoolSolution (algFPHP 1 1 ℤ) x) :
    x = fun _ => true := by
  rcases (isBoolSolution_algFPHP_iff (R := ℤ) x).1 hx with ⟨f, _, rfl⟩
  funext ⟨i, j⟩
  fin_cases i
  fin_cases j
  have hf0 : f 0 = 0 := Subsingleton.elim _ _
  simp [pigeonIndicator, hf0]

/-! ### `algFPHP(2, 1)`: unsatisfiable and refutable in degree `2` -/

private theorem algFPHPPigeonPoly_one_hole {m : ℕ} {R : Type*} [CommRing R] (i : Fin m) :
    (algFPHPPigeonPoly (n := 1) (R := R) i) = 1 - X (i, 0) := by
  simp [algFPHPPigeonPoly]

/-- Explicit `6`-line degree-`2` PC refutation of `algFPHP 2 1 R` over any commutative ring `R`:
`1 = (1 - x₀₀) + x₀₀ (1 - x₁₀) + x₀₀ x₁₀`. -/
private noncomputable def algFPHP21Proof (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin 2 × Fin 1) R) :=
  [1,
   X (0, 0),
   X (0, 0) * (1 - X (1, 0)),
   X (0, 0) * X (1, 0),
   1 - X (1, 0),
   1 - X (0, 0)]

private theorem refutableInDegree_two_algFPHP21 (R : Type*) [CommRing R] :
    PC.RefutableInDegree (algFPHP 2 1 R) 2 := by
  let p₀ : MvPolynomial (Fin 2 × Fin 1) R := 1 - X (0, 0)
  let p₁ : MvPolynomial (Fin 2 × Fin 1) R := 1 - X (1, 0)
  let h₀₁ : MvPolynomial (Fin 2 × Fin 1) R := X (0, 0) * X (1, 0)
  let q₁ : MvPolynomial (Fin 2 × Fin 1) R := X (0, 0) * p₁
  let q₂ : MvPolynomial (Fin 2 × Fin 1) R := C 1 * q₁ + C 1 * h₀₁
  let q₃ : MvPolynomial (Fin 2 × Fin 1) R := C 1 * p₀ + C 1 * q₂
  have hp₀ : p₀ ∈ algFPHP 2 1 R := by
    simpa [p₀, algFPHPPigeonPoly_one_hole] using
      algFPHPPigeonPoly_mem_algFPHP (m := 2) (n := 1) (R := R) 0
  have hp₁ : p₁ ∈ algFPHP 2 1 R := by
    simpa [p₁, algFPHPPigeonPoly_one_hole] using
      algFPHPPigeonPoly_mem_algFPHP (m := 2) (n := 1) (R := R) 1
  have hh₀₁ : h₀₁ ∈ algFPHP 2 1 R :=
    algFPHPHole_mem_algFPHP (by decide : (0 : Fin 2) ≠ 1) (0 : Fin 1)
  have proof₁ : PC.IsProof (algFPHP 2 1 R) [p₀] :=
    PC.IsProof.mem PC.IsProof.nil hp₀
  have proof₂ : PC.IsProof (algFPHP 2 1 R) [p₁, p₀] :=
    PC.IsProof.mem proof₁ hp₁
  have proof₃ : PC.IsProof (algFPHP 2 1 R) [h₀₁, p₁, p₀] :=
    PC.IsProof.mem proof₂ hh₀₁
  have proof₄ : PC.IsProof (algFPHP 2 1 R) [q₁, h₀₁, p₁, p₀] :=
    PC.IsProof.mulVar (0, 0) proof₃ (by simp)
  have proof₅ : PC.IsProof (algFPHP 2 1 R) [q₂, q₁, h₀₁, p₁, p₀] :=
    PC.IsProof.linear 1 1 proof₄ (by simp) (by simp)
  have proof₆ : PC.IsProof (algFPHP 2 1 R) [q₃, q₂, q₁, h₀₁, p₁, p₀] :=
    PC.IsProof.linear 1 1 proof₅ (by simp) (by simp)
  have hq₂ : q₂ = X (0, 0) := by
    simp only [q₂, q₁, p₁, h₀₁, map_one, one_mul]
    ring
  have hq₃ : q₃ = 1 := by
    simp only [q₃, p₀, hq₂, map_one, one_mul]
    ring
  have hproof : PC.IsProof (algFPHP 2 1 R) (algFPHP21Proof R) := by
    simpa [algFPHP21Proof, hq₂, hq₃, q₁, h₀₁, p₁, p₀] using proof₆
  refine ⟨algFPHP21Proof R, hproof, by simp [algFPHP21Proof], ?_⟩
  have hdeg_p₀ : p₀.totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans
      (max_le (by simp) ((totalDegree_X_le (0, 0)).trans (by decide)))
  have hdeg_p₁ : p₁.totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans
      (max_le (by simp) ((totalDegree_X_le (1, 0)).trans (by decide)))
  have hdeg_h₀₁ : h₀₁.totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans
      (add_le_add (totalDegree_X_le (0, 0)) (totalDegree_X_le (1, 0)))
  have hdeg_q₁ : q₁.totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans
      (add_le_add (totalDegree_X_le (0, 0))
        ((totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_X_le (1, 0)))))
  simp only [algFPHP21Proof, PC.degree_cons, PC.degree_nil, totalDegree_one]
  exact max_le (by decide) (max_le ((totalDegree_X_le (0, 0)).trans (by decide))
    (max_le hdeg_q₁ (max_le hdeg_h₀₁ (max_le hdeg_p₁ (max_le hdeg_p₀ (by decide))))))

example :
    (∀ x : Fin 2 × Fin 1 → Bool, ¬ IsBoolSolution (algFPHP 2 1 ℤ) x) ∧
    (∀ a : Fin 2 × Fin 1 → ℚ, ∃ p ∈ algFPHP 2 1 ℚ, eval a p ≠ 0) ∧
    PC.RefutableInDegree (algFPHP 2 1 ℤ) 2 ∧
    PC.RefutableInDegree (algFPHP 2 1 ℚ) 2 ∧
    PC.RefutableInDegree (algFPHP 2 1 (ZMod 2)) 2 ∧
    PC.RefutableInDegree (algFPHP 2 1 ℚ) 4 ∧
    (∃ d, PC.RefutableInDegree (algFPHP 2 1 (ZMod 2)) d) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_, refutableInDegree_two_algFPHP21 ℤ, refutableInDegree_two_algFPHP21 ℚ,
    refutableInDegree_two_algFPHP21 (ZMod 2),
    pc_refutableInDegree_algFPHP_of_lt (by decide : 1 < 2),
    exists_pc_refutableInDegree_algFPHP_iff.2 (by decide : 1 < 2)⟩
  · intro x hx
    have : 2 ≤ 1 := exists_isBoolSolution_algFPHP_iff.1 ⟨x, hx⟩
    omega
  · intro a
    by_contra hall
    push Not at hall
    have : 2 ≤ 1 := exists_commonZero_algFPHP_iff.1 ⟨a, hall⟩
    omega

/-! ### Zero-hole instances (`n = 0 < m`) and empty pigeon boundary (`m = 0`) -/

example :
    (1 : MvPolynomial (Fin 1 × Fin 0) ℤ) ∈ algFPHP 1 0 ℤ ∧
    (algFPHPPigeonPoly (n := 0) (R := ℚ) (0 : Fin 1) = 1) ∧
    PC.RefutableInDegree (algFPHP 1 0 ℤ) 0 ∧
    PC.RefutableInDegree (algFPHP 2 0 ℚ) 0 ∧
    (∀ x : Fin 1 × Fin 0 → Bool, ¬ IsBoolSolution (algFPHP 1 0 ℚ) x) ∧
    (∀ a : Fin 2 × Fin 0 → ℚ, ∃ p ∈ algFPHP 2 0 ℚ, eval a p ≠ 0) := by
  refine ⟨one_mem_algFPHP_zero (by decide), algFPHPPigeonPoly_zero 0,
    pc_refutableInDegree_algFPHP_zero (by decide) ℤ,
    pc_refutableInDegree_algFPHP_zero (by decide) ℚ, ?_, ?_⟩
  · intro x hx
    have : 1 ≤ 0 := exists_isBoolSolution_algFPHP_iff.1 ⟨x, hx⟩
    omega
  · intro a
    by_contra hall
    push Not at hall
    have : 2 ≤ 0 := exists_commonZero_algFPHP_iff.1 ⟨a, hall⟩
    omega

example :
    (∃ x : Fin 0 × Fin 0 → Bool, IsBoolSolution (algFPHP 0 0 ℚ) x) ∧
    (∀ d, ¬ PC.RefutableInDegree (algFPHP 0 0 ℚ) d) ∧
    (∃ a : Fin 0 × Fin 1 → ℤ, ∀ p ∈ algFPHP 0 1 ℤ, eval a p = 0) :=
  ⟨exists_isBoolSolution_algFPHP_iff.2 le_rfl,
    not_pc_refutableInDegree_algFPHP le_rfl,
    exists_commonZero_algFPHP_iff.2 (Nat.zero_le 1)⟩

/-! ### Roundtrip check on `boolSolutionEquivEmbedding` and `commonZeroEquivEmbedding` -/

example :
    let e : Fin 2 ↪ Fin 2 := (Equiv.swap (0 : Fin 2) 1).toEmbedding
    boolSolutionEquivEmbedding 2 2 ℚ ((boolSolutionEquivEmbedding 2 2 ℚ).symm e) = e ∧
    commonZeroEquivEmbedding 2 2 ℚ ((commonZeroEquivEmbedding 2 2 ℚ).symm e) = e := by
  intro e
  exact ⟨Equiv.apply_symm_apply _ e, Equiv.apply_symm_apply _ e⟩

end CslibFrontierTests.ProofComplexity.AlgebraicFunctionalPigeonhole
