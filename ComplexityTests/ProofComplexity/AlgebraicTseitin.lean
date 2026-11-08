/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Expander.Existence
import Complexity.Logics.Propositional.Algebraic.CNF.Parity
import Complexity.Logics.Propositional.Algebraic.Nullstellensatz.Tseitin
import Complexity.Logics.Propositional.Algebraic.PolynomialCalculus.TseitinExpander
import Mathlib.Algebra.Field.ZMod

/-!
# Tests: algebraic degree lower bounds for Tseitin formulas

The polynomial calculus degree lower bound for Tseitin formulas on the triangle over `ℚ`; the
refutation of degree `2` in characteristic `2` on the same triangle; a disconnected multigraph
whose Tseitin formula contains the empty clause although `e(G) = 2`, which shows that the lower
bound needs connectivity; an expander whose Tseitin formula has a refutation of degree `120` over
`ZMod 2` although `e(G) > 240`, which shows that the lower bound needs `2 ≠ 0`; and the hard
formulas of linear degree over `ZMod 3`.
-/

namespace ComplexityTests.ProofComplexity.AlgebraicTseitin

open Cslib Cslib.Logic.PL Cslib.Logic.PL.Algebraic Finset MvPolynomial

/-! ### Clauses excluding an assignment -/

/-- The clause polynomial of a clause excluding an assignment to two variables has degree `2`. -/
example (y : Fin 2 → Bool) :
    ((Clause.exclude ({0, 1} : Finset (Fin 2)) y).toBoolPoly ℚ).totalDegree = 2 := by
  rw [Clause.totalDegree_toBoolPoly_exclude]
  rfl

/-! ### A triangle -/

/-- The triangle on `Fin 3`: edge `i` joins `i` and `i + 1`. -/
private def triangle : Fin 3 → Sym2 (Fin 3) := fun i => s(i, i + 1)

private theorem connected_triangle : (Multigraph.toSimpleGraph triangle).Connected :=
  (Multigraph.connected_toSimpleGraph_iff triangle).2 ⟨⟨0⟩, by decide⟩

private theorem two_le_minBalancedCut_triangle : 2 ≤ Multigraph.minBalancedCut triangle :=
  (Multigraph.le_minBalancedCut_iff triangle (by decide)).2 (by decide)

/-- Over `ℚ`, the unsatisfiable Tseitin formula on the triangle has no polynomial calculus
refutation of degree `0`. -/
example : ¬ PC.RefutableInDegree
    ((CNF.tseitinFormula triangle fun v => decide (v = 0)).toBoolPolys ℚ ++
      boolAxioms (Fin 3) ℚ) 0 := fun h => by
  have := Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree two_ne_zero
    connected_triangle h
  have := two_le_minBalancedCut_triangle
  omega

/-- The same bound for the Nullstellensatz over the field with three elements. -/
example : ¬ NS.RefutableInDegree
    ((CNF.tseitinFormula triangle fun v => decide (v = 0)).toBoolPolys (ZMod 3) ++
      boolAxioms (Fin 3) (ZMod 3)) 0 := fun h => by
  have := Tseitin.minBalancedCut_le_two_mul_of_ns_refutableInDegree (by decide)
    connected_triangle h
  have := two_le_minBalancedCut_triangle
  omega

/-- Over `ZMod 2`, the clause polynomials of the Tseitin formula on the triangle add up to `1`, a
Nullstellensatz refutation of degree `2`. -/
example : NS.RefutableInDegree
    ((CNF.tseitinFormula triangle fun v => decide (v = 0)).toBoolPolys (ZMod 2)) 2 :=
  CNF.ns_refutableInDegree_tseitinFormula_of_charP_two (fun v => by revert v; decide)
    (by decide)

/-! ### Connectivity is needed -/

/-- A triangle on `0, 1, 2` and an isolated vertex `3`. -/
private def triangleAndPoint : Fin 3 → Sym2 (Fin 4) := ![s(0, 1), s(1, 2), s(2, 0)]

/-- Every set of two vertices has two edges leaving it, so `e(G) = 2`. -/
private theorem two_le_minBalancedCut_triangleAndPoint :
    2 ≤ Multigraph.minBalancedCut triangleAndPoint :=
  (Multigraph.le_minBalancedCut_iff triangleAndPoint (by decide)).2 (by decide)

/-- The charge of the isolated vertex gives the empty clause. -/
private theorem nil_mem_tseitinFormula_triangleAndPoint :
    [] ∈ CNF.tseitinFormula triangleAndPoint fun v => decide (v = 3) := by
  refine CNF.mem_tseitinFormula.2 ⟨3, ?_⟩
  rw [show Multigraph.incidence triangleAndPoint 3 = ∅ by decide]
  simp [CNF.parityOnEq, Clause.exclude, parityOn_empty]

/-- So the Tseitin formula has a Nullstellensatz refutation of degree `0`. -/
private theorem ns_triangleAndPoint : NS.RefutableInDegree
    ((CNF.tseitinFormula triangleAndPoint fun v => decide (v = 3)).toBoolPolys ℚ ++
      boolAxioms (Fin 3) ℚ) 0 := by
  have hmem : (1 : MvPolynomial (Fin 3) ℚ) ∈
      (CNF.tseitinFormula triangleAndPoint fun v => decide (v = 3)).toBoolPolys ℚ ++
        boolAxioms (Fin 3) ℚ :=
    List.mem_append_left _
      (List.mem_map.2 ⟨[], nil_mem_tseitinFormula_triangleAndPoint, Clause.toBoolPoly_nil⟩)
  obtain ⟨P, hP, hPd⟩ := NS.exists_isProof_of_sum {()} (fun _ => 1) (fun _ => 1)
    (fun _ _ => hmem) (d := 0) fun _ _ _ => by rw [totalDegree_one]
  exact ⟨P, by simpa using hP, hPd⟩

/-- The degree bound fails on this disconnected multigraph, so the theorem needs connectivity. -/
example : ¬ (Multigraph.toSimpleGraph triangleAndPoint).Connected := fun hG => by
  have := Tseitin.minBalancedCut_le_two_mul_of_ns_refutableInDegree (K := ℚ) two_ne_zero hG
    ns_triangleAndPoint
  have := two_le_minBalancedCut_triangleAndPoint
  omega

/-! ### The characteristic is needed -/

/-- One charged vertex gives odd total charge. Stated for every `n`: `simp` is slow on the concrete
`Fin 5000000`. -/
private theorem parityOn_univ_decide_eq_zero (n : ℕ) [NeZero n] :
    parityOn univ (fun v : Fin n => decide (v = 0)) = true := by
  simp [parityOn, filter_eq']

/-- An expander with `120` labels on `5000000` vertices. -/
private noncomputable abbrev bigExpander : RotationMap (Fin 5000000) (Fin 120) :=
  RotationMap.expander (Fin 5000000)

/-- Its expansion is more than `240`. -/
private theorem lt_minBalancedCut_bigExpander :
    240 < Multigraph.minBalancedCut bigExpander.edgeEnds := by
  have hh := RotationMap.le_edgeExpansion_expander (Fin 5000000)
  have he := bigExpander.edgeExpansion_mul_card_div_three_le_minBalancedCut
  simp only [Fintype.card_fin] at he
  have : (240 : ℝ) < Multigraph.minBalancedCut bigExpander.edgeEnds := by
    push_cast at he
    linarith
  exact_mod_cast this

private theorem connected_bigExpander :
    (Multigraph.toSimpleGraph bigExpander.edgeEnds).Connected := by
  rw [bigExpander.toSimpleGraph_edgeEnds]
  exact bigExpander.connected_toSimpleGraph_of_edgeExpansion_pos
    (lt_of_lt_of_le (by norm_num) (RotationMap.le_edgeExpansion_expander (Fin 5000000)))

/-- Over `ZMod 2`, the Tseitin formula on the expander has a polynomial calculus refutation of
degree `120`, below `e(G) / 2`; so the degree lower bound needs `2 ≠ 0`. -/
example : PC.RefutableInDegree
      ((CNF.tseitinFormula bigExpander.edgeEnds fun v => decide (v = 0)).toBoolPolys (ZMod 2) ++
        boolAxioms bigExpander.edges (ZMod 2)) 120 ∧
    2 * 120 < Multigraph.minBalancedCut bigExpander.edgeEnds ∧
    (Multigraph.toSimpleGraph bigExpander.edgeEnds).Connected := by
  refine ⟨(PC.RefutableInDegree.of_ns ?_).mono (List.subset_append_left _ _) le_rfl,
    lt_minBalancedCut_bigExpander, connected_bigExpander⟩
  refine CNF.ns_refutableInDegree_tseitinFormula_of_charP_two (fun v => ?_) ?_
  · simpa using bigExpander.card_incidence_edgeEnds_le v
  · exact parityOn_univ_decide_eq_zero 5000000

/-! ### Hard formulas -/

/-- An unsatisfiable formula without polynomial calculus refutations of degree `1` over
`ZMod 3`. -/
example : ∃ m, ∃ φ : CNF (Fin m), ¬ φ.Satisfiable ∧
    ¬ PC.RefutableInDegree (φ.toBoolPolys (ZMod 3) ++ boolAxioms (Fin m) (ZMod 3)) 1 := by
  obtain ⟨m, -, φ, -, -, hφ, h⟩ := CNF.exists_forall_pc_refutableInDegree_le 72001 (by norm_num)
  exact ⟨m, φ, hφ, fun hd => by
    have := h (ZMod 3) (by decide) 1 hd
    omega⟩

end ComplexityTests.ProofComplexity.AlgebraicTseitin
