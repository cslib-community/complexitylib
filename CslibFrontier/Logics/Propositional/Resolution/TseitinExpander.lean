/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Multigraph
public import CslibFrontier.Logics.Propositional.Resolution.Tseitin
import CslibFrontier.Foundations.Combinatorics.Expander.MultigraphExistence

/-!
# Tseitin formulas on expanders are hard for resolution

A rotation map `G` (`Cslib.RotationMap`) is a multigraph with an edge for each pair of a dart and
its reversal (`Cslib.RotationMap.edgeEnds`), and its edge expansion `h(G)` bounds the expansion
`e(G)` of Ben-Sasson and Wigderson: `h(G) |V| / 3 ≤ e(G)`
(`Cslib.RotationMap.edgeExpansion_mul_card_div_three_le_minBalancedCut`). If `h(G) > 0`, the
multigraph is connected, and Tseitin formulas on it need resolution refutations of width at least
`h(G) |V| / 3` (`Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_refutableInWidth`)
and, when `|D| + 2 ≤ h(G) |V| / 3`, of at least `exp ((h(G) |V| / 3 - |D| - 2)² / (8 |V| |D|))`
lines (`Cslib.Logic.PL.Tseitin.exp_edgeExpansion_le_of_refutableInSize`).

Constant-degree expanders (`Cslib.RotationMap.expander`) have `120` labels and edge expansion at
least `1 / 6000` (`Cslib.RotationMap.le_edgeExpansion_expander`). Their Tseitin formulas with a
single charged vertex form **a family, with explicit constants, of unsatisfiable formulas with
`O(n)` variables and clauses of constant width whose resolution refutations have `2 ^ Ω(n)`
lines** (`Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`) [Urquhart][Urquhart1987]
[Ben-Sasson and Wigderson][BenSassonWigderson2001]. The expanders, and so the formulas, are
obtained non-constructively, from a counting argument
(`Cslib.RotationMap.exists_spectralExpansion_le`).

## Main results

* `Cslib.Logic.PL.Tseitin.edgeExpansion_mul_card_div_three_le_of_refutableInWidth`,
  `Cslib.Logic.PL.Tseitin.exp_edgeExpansion_le_of_refutableInSize`: the width and size lower bounds
  for Tseitin formulas on rotation maps, in terms of edge expansion.
* `Cslib.Logic.PL.Tseitin.exists_expander_tseitinFormula`: the explicit expander family of Tseitin
  formulas, with its constants.
* `Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`: for every `n ≥ 4392000`, an
  unsatisfiable formula with at most `120 n` variables and `2 ^ 120 · n` clauses of width at most
  `120` needs resolution refutations of `exp (n / (960 · 36000²))` lines.

## References

* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
-/

public section

namespace Cslib.Logic.PL

open Finset

namespace Tseitin

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
  (G : RotationMap V D)

/-- **The width lower bound for Tseitin formulas on rotation maps**
[Ben-Sasson and Wigderson][BenSassonWigderson2001]: if `h(G) > 0`, every resolution
refutation of a Tseitin formula on `G` has width at least `h(G) |V| / 3`. -/
theorem edgeExpansion_mul_card_div_three_le_of_refutableInWidth (hG : 0 < G.edgeExpansion)
    {χ : V → Bool} {w : ℕ} (h : (CNF.tseitinFormula G.edgeEnds χ).RefutableInWidth w) :
    G.edgeExpansion * Fintype.card V / 3 ≤ w := by
  have hc := G.connected_toSimpleGraph_of_edgeExpansion_pos hG
  rw [← G.toSimpleGraph_edgeEnds] at hc
  exact G.edgeExpansion_mul_card_div_three_le_minBalancedCut.trans
    (by exact_mod_cast minBalancedCut_le_of_refutableInWidth hc h)

/-- **The size lower bound for Tseitin formulas on rotation maps**
[Ben-Sasson and Wigderson, Corollary 3.6][BenSassonWigderson2001]: if
`|D| + 2 ≤ h(G) |V| / 3`, every resolution refutation of a Tseitin formula on `G` has at least
`exp ((h(G) |V| / 3 - |D| - 2)² / (8 |V| |D|))` lines. -/
theorem exp_edgeExpansion_le_of_refutableInSize
    (hG : Fintype.card D + 2 ≤ G.edgeExpansion * Fintype.card V / 3) {χ : V → Bool} {s : ℕ}
    (hs : (CNF.tseitinFormula G.edgeEnds χ).RefutableInSize s) :
    Real.exp ((G.edgeExpansion * Fintype.card V / 3 - Fintype.card D - 2) ^ 2 /
      (8 * Fintype.card V * Fintype.card D)) ≤ s := by
  have hh : 0 < G.edgeExpansion := by
    by_contra h
    have : G.edgeExpansion = 0 := le_antisymm (not_lt.1 h) G.edgeExpansion_nonneg
    rw [this, zero_mul, zero_div] at hG
    linarith [(Fintype.card D).cast_nonneg (α := ℝ)]
  have hc := G.connected_toSimpleGraph_of_edgeExpansion_pos hh
  rw [← G.toSimpleGraph_edgeEnds] at hc
  have he := G.edgeExpansion_mul_card_div_three_le_minBalancedCut
  have hke : Fintype.card D + 2 ≤ Multigraph.minBalancedCut G.edgeEnds := by
    exact_mod_cast hG.trans he
  have hsize := exp_le_of_refutableInSize (N := Fintype.card V * Fintype.card D) hc
    G.card_incidence_edgeEnds_le (by rw [Fintype.card_coe]; exact G.card_edges_le) hke hs
  refine le_trans (Real.exp_le_exp.2 ?_) hsize
  push_cast
  rw [mul_assoc]
  gcongr
  linarith

end Tseitin

/-! ### Hard formulas -/

namespace Tseitin

/-- **The explicit expander family of Tseitin formulas**: for every `n ≥ 2` there is a connected
multigraph on `n` vertices with at most `120 n` edges, each vertex on at most `120` edges other
than self-loops, and expansion `e(G) ≥ n / 18000`, whose Tseitin formula with a single charged
vertex has at most `2 ^ 120 · n` clauses, each with at most `120` literals and so of width at most
`120`, and is unsatisfiable. The multigraph comes from `Cslib.Multigraph.exists_expander`: it is
that of the `120`-regular expander `Cslib.RotationMap.expander (Fin n)`, with edge expansion at
least `1 / 6000`, whose existence is proved non-constructively. This is the common setup of
`Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le` and of the clause-space family in
`CslibFrontier.Logics.Propositional.Resolution.TseitinSpace`. -/
theorem exists_expander_tseitinFormula (n : ℕ) (hn : 2 ≤ n) :
    ∃ m ≤ 120 * n, ∃ (ends : Fin m → Sym2 (Fin n)) (χ : Fin n → Bool),
      (∀ v, #(Multigraph.incidence ends v) ≤ 120) ∧ (Multigraph.toSimpleGraph ends).Connected ∧
      (n : ℝ) / 18000 ≤ Multigraph.minBalancedCut ends ∧
      (CNF.tseitinFormula ends χ).length ≤ 2 ^ 120 * n ∧
      (∀ c ∈ CNF.tseitinFormula ends χ, c.length ≤ 120) ∧
      (∀ c ∈ CNF.tseitinFormula ends χ, c.width ≤ 120) ∧
      ¬ (CNF.tseitinFormula ends χ).Satisfiable := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm, ends, hdeg, hG, he⟩ := Multigraph.exists_expander n hn
  let χ : Fin n → Bool := fun v => decide (v = 0)
  have hlen (c) (hc : c ∈ CNF.tseitinFormula ends χ) : c.length ≤ 120 :=
    CNF.length_le_of_mem_tseitinFormula hdeg hc
  refine ⟨m, hm, ends, χ, hdeg, hG, he, ?_, hlen, fun c hc => ?_,
    CNF.not_satisfiable_tseitinFormula ?_⟩
  · simpa [mul_comm] using CNF.length_tseitinFormula_le (χ := χ) hdeg
  · exact (List.toFinset_card_le c).trans (hlen c hc)
  · simp [χ, parityOn, filter_eq']

end Tseitin

namespace CNF

/-- **Unsatisfiable formulas with `O(n)` variables and clauses of constant width need resolution
refutations of `2 ^ Ω(n)` lines** [Urquhart][Urquhart1987]
[Ben-Sasson and Wigderson][BenSassonWigderson2001] [Jukna, Chapter 18][Jukna2012]. For every
`n ≥ 4392000` there is an unsatisfiable formula with at most `120 n` variables and at most
`2 ^ 120 · n` clauses, of width at most `120`, whose resolution refutations all have at least
`exp (n / (960 · 36000²))` lines. It is the Tseitin formula, with a single charged vertex, of a
`120`-regular expander on `n` vertices (`Cslib.RotationMap.expander`), whose existence is proved
non-constructively. -/
theorem exists_forall_refutableInSize_exp_le :
    ∀ n ≥ 4392000, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.width ≤ 120) ∧ ¬ φ.Satisfiable ∧
      ∀ s, φ.RefutableInSize s → Real.exp (n / (960 * 36000 ^ 2)) ≤ s := by
  intro n hn
  obtain ⟨m, hm, ends, χ, hdeg, hG, he, hlen, -, hw, hunsat⟩ :=
    Tseitin.exists_expander_tseitinFormula n (by omega)
  refine ⟨m, hm, tseitinFormula ends χ, hlen, hw, hunsat, fun s hs => ?_⟩
  have hn' : (4392000 : ℝ) ≤ n := by exact_mod_cast hn
  have hke : 120 + 2 ≤ Multigraph.minBalancedCut ends := by
    have : (122 : ℝ) ≤ Multigraph.minBalancedCut ends := by linarith
    exact_mod_cast this
  have hsize := Tseitin.exp_le_of_refutableInSize hG hdeg (by simpa using hm) hke hs
  refine le_trans (Real.exp_le_exp.2 ?_) hsize
  -- `e(G) - 122 ≥ n / 36000`
  have hx : (n : ℝ) / 36000 ≤ (Multigraph.minBalancedCut ends : ℝ) - 120 - 2 := by linarith
  have hsq := pow_le_pow_left₀ (by positivity) hx 2
  have hnpos : (0 : ℝ) < n := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  nlinarith

end CNF

end Cslib.Logic.PL
