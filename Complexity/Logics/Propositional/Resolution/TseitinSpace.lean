/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.SpaceWidth
public import Complexity.Logics.Propositional.Resolution.TseitinExpander
import Complexity.Foundations.Combinatorics.Expander.Existence

/-!
# Tseitin formulas on expanders need linear clause space

Tseitin formulas on connected multigraphs need resolution refutations of width at least the
expansion `e(G)` (`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth`). By the
Atserias–Dalmau inequality (`Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth`), their
refutations in clause space `s` therefore satisfy `e(G) ≤ s + k - 3`, where `k` bounds the number of
edges at a vertex (`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInSpace`); on a rotation
map with positive edge expansion `h(G)` this is `h(G) |V| / 3 + 3 ≤ s + |D|`
(`Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace`).
Constant-degree expanders thus give **a family, with explicit constants, of unsatisfiable formulas
with `O(n)` variables and clauses of constant width whose resolution refutations need clause space
`Ω(n)`** (`Cslib.Logic.PL.CNF.exists_forall_refutableInSpace_le`).

Clause-space lower bounds for Tseitin formulas on expanders were first proved by Alekhnovich,
Ben-Sasson, Razborov and Wigderson [AlekhnovichBenSassonRazborovWigderson2002] and by Esteban and
Torán [EstebanToran2001], as remarked in [Filmus, Lauria, Mikša, Nordström and Vinyals,
Section 4][FilmusLauriaMiksaNordstromVinyals2014]; those two papers were not inspected for this
formalization. Atserias and Dalmau observe, after their Theorem 3, that space lower bounds follow
from width lower bounds [Atserias and Dalmau, Section 4][AtseriasDalmau2008], and we derive them
that way, from the width bound of Ben-Sasson and Wigderson [BenSassonWigderson2001], using the
constant `s + k - 3` of [Filmus, Lauria, Mikša, Nordström and Vinyals,
Theorem 1][FilmusLauriaMiksaNordstromVinyals2014].

## Main results

* `Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInSpace`: the clause-space lower bound for
  Tseitin formulas on multigraphs, in terms of expansion.
* `Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace`: the
  same on rotation maps, in terms of edge expansion.
* `Cslib.Logic.PL.CNF.exists_forall_refutableInSpace_le`: for every `n ≥ 4392000`, an unsatisfiable
  formula with at most `120 n` variables and `2 ^ 120 · n` clauses of width at most `120` needs
  resolution refutations in clause space at least `n / 36000`.

## References

* [M. Alekhnovich, E. Ben-Sasson, A. A. Razborov, A. Wigderson, *Space complexity in
  propositional calculus*][AlekhnovichBenSassonRazborovWigderson2002]
* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [J. L. Esteban, J. Torán, *Space bounds for resolution*][EstebanToran2001]
* [Y. Filmus, M. Lauria, M. Mikša, J. Nordström, M. Vinyals, *From small space to small width in
  resolution*][FilmusLauriaMiksaNordstromVinyals2014]
-/

public section

namespace Cslib.Logic.PL

open Finset

namespace Tseitin

section Multigraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {ends : E → Sym2 V} {χ : V → Bool}

/-- **The clause-space lower bound for Tseitin formulas**: on a connected multigraph whose vertices
have at most `k` edges other than self-loops, every resolution refutation of a Tseitin formula in
clause space `s` has `e(G) ≤ s + k - 3`. -/
theorem minBalancedCut_le_of_refutableInSpace (hG : (Multigraph.toSimpleGraph ends).Connected)
    {k s : ℕ} (hk : ∀ v, #(Multigraph.incidence ends v) ≤ k)
    (h : (CNF.tseitinFormula ends χ).RefutableInSpace s) :
    Multigraph.minBalancedCut ends ≤ s + k - 3 :=
  minBalancedCut_le_of_refutableInWidth hG <| h.refutableInWidth fun _ hc =>
    (List.toFinset_card_le _).trans (CNF.length_le_of_mem_tseitinFormula hk hc)

end Multigraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-- **The clause-space lower bound for Tseitin formulas on rotation maps**: if `h(G) > 0`, every
resolution refutation of a Tseitin formula on `G` in clause space `s` has
`h(G) |V| / 3 + 3 ≤ s + |D|`. -/
theorem edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace
    (hG : 0 < G.edgeExpansion) {χ : V → Bool} {s : ℕ}
    (h : (CNF.tseitinFormula G.edgeEnds χ).RefutableInSpace s) :
    G.edgeExpansion * Fintype.card V / 3 + 3 ≤ s + Fintype.card D := by
  have hc := G.connected_toSimpleGraph_of_edgeExpansion_pos hG
  rw [← G.toSimpleGraph_edgeEnds] at hc
  have he := G.edgeExpansion_mul_card_div_three_le_minBalancedCut
  have hle := minBalancedCut_le_of_refutableInSpace hc G.card_incidence_edgeEnds_le h
  -- the expansion is positive, so the truncated subtraction is exact
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hG.ne' G.edgeExpansion_eq_zero_of_subsingleton
  have hpos : (0 : ℝ) < Multigraph.minBalancedCut G.edgeEnds :=
    lt_of_lt_of_le (by have := Fintype.one_lt_card (α := V); positivity) he
  have hle' : Multigraph.minBalancedCut G.edgeEnds + 3 ≤ s + Fintype.card D := by
    have : 0 < Multigraph.minBalancedCut G.edgeEnds := by exact_mod_cast hpos
    omega
  have : (Multigraph.minBalancedCut G.edgeEnds : ℝ) + 3 ≤ s + Fintype.card D := by
    exact_mod_cast hle'
  linarith

end Tseitin

/-! ### Formulas needing linear space -/

namespace CNF

/-- **Unsatisfiable formulas with `O(n)` variables and clauses of constant width need resolution
refutations in clause space `Ω(n)`** [Atserias and Dalmau, Section 4][AtseriasDalmau2008]
[Filmus, Lauria, Mikša, Nordström and Vinyals, Theorem 1][FilmusLauriaMiksaNordstromVinyals2014]
[Ben-Sasson and Wigderson][BenSassonWigderson2001]. For every `n ≥ 4392000` there is an
unsatisfiable formula with at most `120 n` variables and at most `2 ^ 120 · n` clauses, of width at
most `120`, whose resolution refutations in clause space `s` all have `n ≤ 36000 s`. It is the
Tseitin formula, with a single charged vertex, of a `120`-regular expander on `n` vertices
(`Cslib.RotationMap.expander`), whose existence is proved non-constructively. -/
theorem exists_forall_refutableInSpace_le :
    ∀ n ≥ 4392000, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.width ≤ 120) ∧ ¬ φ.Satisfiable ∧
      ∀ s, φ.RefutableInSpace s → n ≤ 36000 * s := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  set G := RotationMap.expander (Fin n)
  let f : Fin (Fintype.card G.edges) ≃ G.edges := (Fintype.equivFin G.edges).symm
  let ends := G.edgeEnds ∘ f
  let χ : Fin n → Bool := fun v => decide (v = 0)
  have hdeg (v : Fin n) : #(Multigraph.incidence ends v) ≤ 120 := by
    rw [Multigraph.card_incidence_comp]
    simpa using G.card_incidence_edgeEnds_le v
  have hm : Fintype.card G.edges ≤ 120 * n := by
    rw [Fintype.card_coe, mul_comm]
    simpa using G.card_edges_le
  refine ⟨_, hm, tseitinFormula ends χ, ?_, fun c hc => ?_, not_satisfiable_tseitinFormula ?_,
    fun s hs => ?_⟩
  · simpa [mul_comm] using length_tseitinFormula_le (χ := χ) hdeg
  · exact (List.toFinset_card_le c).trans (length_le_of_mem_tseitinFormula hdeg hc)
  · simp [χ, parityOn, filter_eq']
  -- the edge expansion is at least `1 / 6000`, so `e(G) ≥ n / 18000`
  have hh := RotationMap.le_edgeExpansion_expander (Fin n)
  have he : (n : ℝ) / 18000 ≤ Multigraph.minBalancedCut ends := by
    rw [Multigraph.minBalancedCut_comp]
    have := G.edgeExpansion_mul_card_div_three_le_minBalancedCut
    simp only [Fintype.card_fin] at this
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have he' : n ≤ 18000 * Multigraph.minBalancedCut ends := by
    have : (n : ℝ) ≤ 18000 * Multigraph.minBalancedCut ends := by linarith
    exact_mod_cast this
  have hG : (Multigraph.toSimpleGraph ends).Connected := by
    rw [Multigraph.toSimpleGraph_comp, G.toSimpleGraph_edgeEnds]
    exact G.connected_toSimpleGraph_of_edgeExpansion_pos (by linarith)
  have hspace := Tseitin.minBalancedCut_le_of_refutableInSpace hG hdeg hs
  omega

end CNF

end Cslib.Logic.PL
