/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.TseitinExpander

/-!
# Tests: sum-of-squares refutations and Grigoriev's degree lower bound

The Tseitin parity system of a triangle with one charged vertex: it is unsatisfiable, width-`2`
derivations reach `0 = 1`, Schoenebeck's pseudo-expectation of degree `1` exists (so the structure
`SOS.PseudoExpectation` is inhabited for an unsatisfiable system), there is no refutation of degree
`1`, and an explicit refutation of degree `2` shows that Grigoriev's bound `e(G) ≤ d` is attained.
With two charged vertices the system is satisfiable and point evaluation rules out refutations of
every degree. On `K₄`, Schoenebeck's pseudo-expectation of degree `3` exists and there is no
refutation of degree `3`. Finally, the expander family is instantiated.
-/

namespace CslibFrontierTests.ProofComplexity.SumOfSquares

open Cslib Cslib.Logic.PL Cslib.Logic.PL.ParitySystem MvPolynomial Finset
open scoped symmDiff

/-! ### Odd supports -/

example : Finsupp.oddSupport (Finsupp.single (0 : Fin 2) 3 + Finsupp.single 1 2) = {0} := by
  ext i
  rw [Finsupp.mem_oddSupport]
  fin_cases i <;> simp

/-! ### A triangle with one charged vertex -/

/-- The triangle on `Fin 3`: edge `i` joins `i` and `i + 1`. -/
private def triangle : Fin 3 → Sym2 (Fin 3) := fun i => s(i, i + 1)

private theorem connected_triangle : (Multigraph.toSimpleGraph triangle).Connected :=
  (Multigraph.connected_toSimpleGraph_iff triangle).2 ⟨⟨0⟩, by decide⟩

private theorem two_le_minBalancedCut_triangle : 2 ≤ Multigraph.minBalancedCut triangle :=
  (Multigraph.le_minBalancedCut_iff triangle (by decide)).2 (by decide)

/-- One charged vertex. -/
private def χ₁ : Fin 3 → Bool := fun v => decide (v = 0)

/-- Odd total charge: the system is unsatisfiable. -/
example (a : Fin 3 → Bool) : ¬ (tseitin triangle χ₁).Holds a := not_holds_tseitin (by decide) a

/-- Width-`2` derivations reach `0 = 1`: sum the three vertex equations. -/
example : (tseitin triangle χ₁).Derives 2 ∅ true := by
  have h (v : Fin 3) :
      (tseitin triangle χ₁).Derives 2 (Multigraph.incidence triangle v) (χ₁ v) :=
    Derives.mem (incidence_mem_tseitin v) (by revert v; decide)
  have h01 := (h 0).symmDiff (h 1) (by decide)
  have := h01.symmDiff (h 2) (by decide)
  rwa [show Multigraph.incidence triangle 0 ∆ Multigraph.incidence triangle 1 ∆
    Multigraph.incidence triangle 2 = ∅ by decide] at this

private theorem not_derives_one : ¬ (tseitin triangle χ₁).Derives 1 ∅ true :=
  not_derives_tseitin_empty_true connected_triangle
    (by have := two_le_minBalancedCut_triangle; omega)

/-- **Nonvacuity**: Schoenebeck's pseudo-expectation of degree `1` for the unsatisfiable
system, which therefore is not a point evaluation. -/
noncomputable example : SOS.PseudoExpectation ((tseitin triangle χ₁).toPolys ℚ) 1 :=
  pseudoExpectation not_derives_one

example : (pseudoExpectation (R := ℚ) not_derives_one).toLinearMap 1 = 1 :=
  (pseudoExpectation not_derives_one).map_one

/-- Grigoriev's theorem: no refutation of degree `1`. -/
example : ¬ SOS.RefutableInDegree ((tseitin triangle χ₁).toPolys ℚ) 1 :=
  Tseitin.not_sos_refutableInDegree_of_lt_minBalancedCut connected_triangle χ₁
    (by have := two_le_minBalancedCut_triangle; omega)

private theorem mem_tri (v : Fin 3) :
    parityPoly ℚ (Multigraph.incidence triangle v) (χ₁ v) ∈ (tseitin triangle χ₁).toPolys ℚ :=
  parityPoly_mem_toPolys (incidence_mem_tseitin v)

private theorem tri0 :
    parityPoly ℚ (Multigraph.incidence triangle 0) (χ₁ 0) = X 0 * X 2 + 1 := by
  rw [show Multigraph.incidence triangle 0 = {0, 2} by decide, parityPoly, prod_pair (by decide)]
  simp [χ₁]

private theorem tri1 :
    parityPoly ℚ (Multigraph.incidence triangle 1) (χ₁ 1) = X 0 * X 1 - 1 := by
  rw [show Multigraph.incidence triangle 1 = {0, 1} by decide, parityPoly, prod_pair (by decide)]
  simp [χ₁]

private theorem tri2 :
    parityPoly ℚ (Multigraph.incidence triangle 2) (χ₁ 2) = X 1 * X 2 - 1 := by
  rw [show Multigraph.incidence triangle 2 = {1, 2} by decide, parityPoly, prod_pair (by decide)]
  simp [χ₁]

private theorem totalDegree_tri_le (v : Fin 3) :
    (parityPoly ℚ (Multigraph.incidence triangle v) (χ₁ v)).totalDegree ≤ 2 :=
  (totalDegree_parityPoly_le _ _).trans (by revert v; decide)

private theorem totalDegree_sign_le (i : Fin 3) :
    (X i ^ 2 - 1 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (totalDegree_X_pow i 2).le (by simp))

private theorem totalDegree_C_mul_le {p : MvPolynomial (Fin 3) ℚ} (c : ℚ)
    (hp : p.totalDegree ≤ 2) : (C c * p).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)

/-- **An explicit refutation of degree `2`**:
`-2 (x₀x₂ + 1) + 2 (x₀x₁ - 1) + 2 (x₁x₂ - 1) - 3 (x₀² - 1) - (x₁² - 1) - (x₂² - 1)
  + (x₀ - x₁ + x₂)² + 2 x₀² = -1`,
so Grigoriev's bound `e(G) ≤ d` is attained on the triangle. The square `x₀²` has weight `2`. -/
private theorem triangle_refutable :
    SOS.RefutableInDegree ((tseitin triangle χ₁).toPolys ℚ) 2 := by
  refine SOS.RefutableInDegree.of_list
    [(C (-2), parityPoly ℚ (Multigraph.incidence triangle 0) (χ₁ 0)),
      (C 2, parityPoly ℚ (Multigraph.incidence triangle 1) (χ₁ 1)),
      (C 2, parityPoly ℚ (Multigraph.incidence triangle 2) (χ₁ 2)),
      (C (-3), X 0 ^ 2 - 1), (C (-1), X 1 ^ 2 - 1), (C (-1), X 2 ^ 2 - 1)] ?_
    [(1, X 0 - X 1 + X 2), (2, X 0)] ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨⟨mem_tri 0, totalDegree_C_mul_le _ (totalDegree_tri_le 0)⟩,
      ⟨mem_tri 1, totalDegree_C_mul_le _ (totalDegree_tri_le 1)⟩,
      ⟨mem_tri 2, totalDegree_C_mul_le _ (totalDegree_tri_le 2)⟩,
      ⟨X_sq_sub_one_mem_toPolys _ 0, totalDegree_C_mul_le _ (totalDegree_sign_le 0)⟩,
      ⟨X_sq_sub_one_mem_toPolys _ 1, totalDegree_C_mul_le _ (totalDegree_sign_le 1)⟩,
      ⟨X_sq_sub_one_mem_toPolys _ 2, totalDegree_C_mul_le _ (totalDegree_sign_le 2)⟩⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    norm_num
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨Nat.mul_le_mul_left 2 ((totalDegree_add _ _).trans (max_le ?_ (totalDegree_X _).le)),
      by rw [totalDegree_X]⟩
    exact (totalDegree_sub _ _).trans (max_le (totalDegree_X _).le (totalDegree_X _).le)
  · simp only [tri0, tri1, tri2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [map_neg, map_one, map_ofNat]
    ring

/-- A refutation can be extracted, and it refutes in every larger degree. -/
example : Nonempty (SOS.Refutation ((tseitin triangle χ₁).toPolys ℚ) 2) :=
  SOS.refutableInDegree_iff.1 triangle_refutable

example (r : SOS.Refutation ((tseitin triangle χ₁).toPolys ℚ) 2) :
    SOS.RefutableInDegree ((tseitin triangle χ₁).toPolys ℚ) 5 :=
  r.refutableInDegree.mono (by norm_num)

/-! ### A triangle with two charged vertices -/

/-- Even total charge: the system is satisfiable, so point evaluation at a satisfying `±1` point
rules out refutations of every degree. -/
example (d : ℕ) :
    ¬ SOS.RefutableInDegree ((tseitin triangle fun v => decide (v ≠ 0)).toPolys ℚ) d := by
  obtain ⟨x, hx⟩ :=
    (exists_eval_eq_zero_iff (R := ℚ) (tseitin triangle fun v => decide (v ≠ 0))).2
      ⟨![false, true, false], (holds_tseitin_iff _).2 (by decide)⟩
  exact (SOS.PseudoExpectation.ofEval x hx).not_refutableInDegree

/-! ### `K₄` -/

/-- The complete graph on `Fin 4`. -/
private def K4 : Fin 6 → Sym2 (Fin 4) :=
  ![s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(2, 3)]

private theorem connected_K4 : (Multigraph.toSimpleGraph K4).Connected :=
  (Multigraph.connected_toSimpleGraph_iff K4).2 ⟨⟨0⟩, by decide⟩

/-- Every set of one or two vertices of `K₄` has at least `3` edges leaving it; sets of two vertices
are the balanced ones, with `4`. -/
private theorem four_le_minBalancedCut_K4 : 4 ≤ Multigraph.minBalancedCut K4 :=
  (Multigraph.le_minBalancedCut_iff K4 (by decide)).2 (by decide)

example (a : Fin 6 → Bool) : ¬ (tseitin K4 fun v => decide (v = 0)).Holds a :=
  not_holds_tseitin (by decide) a

/-- Schoenebeck's pseudo-expectation of degree `3` for the unsatisfiable Tseitin system of `K₄`,
over `ℝ`. -/
noncomputable example :
    SOS.PseudoExpectation ((tseitin K4 fun v => decide (v = 0)).toPolys ℝ) 3 :=
  pseudoExpectation (not_derives_tseitin_empty_true connected_K4
    (by have := four_le_minBalancedCut_K4; omega))

/-- Grigoriev's theorem on `K₄`: no refutation of degree `3`, over `ℝ`. -/
example : ¬ SOS.RefutableInDegree ((tseitin K4 fun v => decide (v = 0)).toPolys ℝ) 3 :=
  Tseitin.not_sos_refutableInDegree_of_lt_minBalancedCut connected_K4 _
    (by have := four_le_minBalancedCut_K4; omega)

/-! ### The expander family -/

/-- The expander family at `n = 2`: at most `240` variables, `2` equations. -/
example : ∃ m ≤ 120 * 2, ∃ P : ParitySystem (Fin m),
    P.length = 2 ∧ (∀ e ∈ P, #e.vars ≤ 120) ∧ (∀ a, ¬ P.Holds a) ∧
    ∀ (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (d : ℕ),
      SOS.RefutableInDegree (P.toPolys R) d → 2 ≤ 18000 * d :=
  exists_forall_sos_refutableInDegree_le 2 le_rfl

end CslibFrontierTests.ProofComplexity.SumOfSquares
