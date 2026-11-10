/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Multigraph
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Tseitin
import CslibFrontier.Foundations.Combinatorics.Expander.MultigraphExistence

/-!
# Tseitin formulas on expanders need polynomial calculus refutations of linear degree

A rotation map `G` (`Cslib.RotationMap`) has expansion `e(G) ≥ h(G) |V| / 3`, where `h(G)` is its
edge expansion (`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`). So over a
field of characteristic other than `2`, if `h(G) > 0`, polynomial calculus refutations of Tseitin
formulas on `G` have degree at least `h(G) |V| / 6`
(`Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_six_le_of_pc_refutableInDegree`), by
`Cslib.Logic.PL.Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree`.

Constant-degree expanders (`Cslib.RotationMap.expander`) have `120` labels and edge expansion at
least `1 / 6000` (`Cslib.RotationMap.le_edgeExpansion_expander`). Their Tseitin formulas with a
single charged vertex form **a family, with explicit constants, of unsatisfiable formulas with
`O(n)` variables and clauses of constant length whose polynomial calculus refutations over every
field of characteristic other than `2` have degree `Ω(n)`**
(`Cslib.Logic.PL.CNF.exists_forall_pc_refutableInDegree_le`). That Tseitin formulas on expanders
need polynomial calculus refutations of linear degree over these fields is due to
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001], and is recorded
qualitatively in [Buss and Nordström, §7.5.4][BussNordstrom2021]; the constants are those of this
formalization. The expanders, and so the formulas, are obtained non-constructively, from a
counting argument (`Cslib.RotationMap.exists_spectralExpansion_le`).

## Main results

* `Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_six_le_of_pc_refutableInDegree`: the degree
  lower bound for Tseitin formulas on rotation maps, in terms of edge expansion.
* `Cslib.Logic.PL.CNF.exists_forall_pc_refutableInDegree_le`: for every `n ≥ 2`, an unsatisfiable
  formula with at most `120 n` variables and `2 ^ 120 · n` clauses of at most `120` literals needs
  polynomial calculus refutations of degree at least `n / 36000` over every field of
  characteristic other than `2`.

## References

* [S. Buss, D. Grigoriev, R. Impagliazzo, T. Pitassi, *Linear gaps between degrees for the
  polynomial calculus modulo distinct primes*][BussGrigorievImpagliazzoPitassi2001]
* [S. Buss, J. Nordström, *Proof complexity and SAT solving*, §7.5.4][BussNordstrom2021]
-/

public section

namespace Cslib.Logic.PL

universe u

open Finset Cslib.Logic.PL.Algebraic

namespace Tseitin

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-- **The polynomial calculus degree lower bound for Tseitin formulas on rotation maps**: over a
field of characteristic other than `2`, if `h(G) > 0`, every polynomial calculus refutation of a
Tseitin formula on `G` has degree at least `h(G) |V| / 6`. The qualitative result is due to
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001]; the constant is
that of this formalization. -/
theorem edgeExpansion_mul_card_div_six_le_of_pc_refutableInDegree {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (hG : 0 < G.edgeExpansion) {χ : V → Bool} {d : ℕ}
    (h : PC.RefutableInDegree
      ((CNF.tseitinFormula G.edgeEnds χ).toBoolPolys K ++ boolAxioms G.edges K) d) :
    G.edgeExpansion * Fintype.card V / 6 ≤ d := by
  have hc := G.connected_toSimpleGraph_of_edgeExpansion_pos hG
  rw [← G.toSimpleGraph_edgeEnds] at hc
  have he := G.edgeExpansion_mul_card_div_three_le_minBalancedCut
  have hd : (Multigraph.minBalancedCut G.edgeEnds : ℝ) ≤ 2 * d := by
    exact_mod_cast minBalancedCut_le_two_mul_of_pc_refutableInDegree h2 hc h
  linarith

end Tseitin

/-! ### Hard formulas -/

namespace CNF

/-- **Unsatisfiable formulas with `O(n)` variables and clauses of constant length need polynomial
calculus refutations of degree `Ω(n)`**
[Buss, Grigoriev, Impagliazzo and Pitassi][BussGrigorievImpagliazzoPitassi2001]. For every `n ≥ 2`
there is an unsatisfiable formula with at most `120 n` variables and at most `2 ^ 120 · n` clauses,
of at most `120` literals each, whose polynomial calculus refutations over every field of
characteristic other than `2` have degree at least `n / 36000`; the constants are those of this
formalization. It is the Tseitin formula, with a single charged vertex, of an expander with `120`
labels on `n` vertices (`Cslib.RotationMap.expander`, through `Cslib.Multigraph.exists_expander`),
whose existence is proved non-constructively. The same bound holds for Nullstellensatz refutations
(`Cslib.Logic.PL.PC.RefutableInDegree.of_ns`). -/
theorem exists_forall_pc_refutableInDegree_le :
    ∀ n ≥ 2, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.length ≤ 120) ∧ ¬ φ.Satisfiable ∧
      ∀ (K : Type u) [Field K], (2 : K) ≠ 0 → ∀ d,
        PC.RefutableInDegree (φ.toBoolPolys K ++ boolAxioms (Fin m) K) d → n ≤ 36000 * d := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm, ends, hdeg, hG, he⟩ := Multigraph.exists_expander n hn
  let χ : Fin n → Bool := fun v => decide (v = 0)
  refine ⟨m, hm, tseitinFormula ends χ, ?_, fun c hc => ?_, not_satisfiable_tseitinFormula ?_,
    fun K _ h2 d hd => ?_⟩
  · simpa [mul_comm] using length_tseitinFormula_le (χ := χ) hdeg
  · exact length_le_of_mem_tseitinFormula hdeg hc
  · simp [χ, parityOn, filter_eq']
  have h' : (Multigraph.minBalancedCut ends : ℝ) ≤ 2 * d := by
    exact_mod_cast Tseitin.minBalancedCut_le_two_mul_of_pc_refutableInDegree h2 hG hd
  have : (n : ℝ) ≤ 36000 * d := by linarith
  exact_mod_cast this

end CNF

end Cslib.Logic.PL
