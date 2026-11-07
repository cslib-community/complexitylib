/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.CliqueColoring
import Complexity.Computability.Circuit.Monotone.Clique.Essential
import Mathlib.Tactic.FinCases

/-!
# Tests: clique–colouring formulas and their resolution lower bound

On three vertices, the complete graph extends to the clique formula with three members but not to
the colouring formula with two colours. The clique–colouring formula with two members and one
colour is unsatisfiable, while with two members and two colours it is satisfied by an edge
coloured with both colours, so unsatisfiability comes from `r < k`.

The hypotheses of the `64 ^ w` resolution bound hold at `w = 16`, `k = 1025` and
`n = 64 * 16 ^ 6 * 1025`, where the formula does have refutations, each of more than `64 ^ 16 / 2`
lines. Monotone circuits computing `k`-clique separate the two classes of graphs, so the circuit
bound for separators applies to actual circuits.

The bounds also hold for small cliques. At `k = 2` and `n = 16` the formula is refutable, and every
refutation has more than `2 ^ (2 ⌊√2⌋) / 2 = 2` lines, indeed at least `60`, since all
`C(16, 2) = 120` edges are essential to its interpolants. A monotone circuit detecting triangles on
four vertices separates, so it has at least `C(4, 2) - 1 = 5` gates.
-/

namespace ComplexityTests.ProofComplexity.CliqueColoring

open Cslib Cslib.Circuits Cslib.Circuits.Clique Cslib.Logic.PL

/-- Every pair of vertices is adjacent in the graph of the all-`true` input. -/
private theorem adj_top {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    (graph fun _ : Fin (edgeCount n) => true).Adj u v :=
  (graph_adj h).2 rfl

/-- The triangle extends to the clique formula with three members. -/
example : ∃ q, (CNF.clique 3 3).eval (Sum.elim (fun _ => true) q) = true :=
  (CNF.exists_eval_clique_iff _).2 (decide_eq_true ⟨Finset.univ, rfl, fun _ _ => rfl⟩)

/-- The triangle does not extend to the colouring formula with two colours. -/
example : ¬ ∃ z, (CNF.coloring 3 2).eval (Sum.elim (fun _ => true) z) = true := by
  rw [CNF.exists_eval_coloring_iff]
  intro h
  have hclique : (graph fun _ : Fin (edgeCount 3) => true).IsClique
      ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := fun _ _ _ _ huv => adj_top huv
  have := hclique.card_le_of_colorable h
  simp at this

/-- **Unsatisfiability on a small instance**: no graph on three vertices has an edge and is
`1`-colourable. -/
example : ¬ (CNF.cliqueColoring 3 2 1).Satisfiable :=
  CNF.not_satisfiable_cliqueColoring (by norm_num)

/-- With two colours, the edge between the vertices `0` and `1` satisfies the clique–colouring
formula with two members. -/
example : (CNF.cliqueColoring 3 2 2).Satisfiable := by
  let x := ofFinset ({0, 1} : Finset (Fin 3))
  obtain ⟨q, hq⟩ := (CNF.exists_eval_clique_iff (k := 2) x).2 (clique_ofFinset rfl)
  have hcol : (graph x).Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk ![0, 1, 0] fun {u v} huv => ?_⟩
    have h := (graph_adj huv.ne).1 huv
    simp only [x, ofFinset_edgeEquiv, toFinset_edge, decide_eq_true_eq] at h
    have hne := huv.ne
    revert h hne
    fin_cases u <;> fin_cases v <;> decide
  obtain ⟨z, hz⟩ := (CNF.exists_eval_coloring_iff x).2 hcol
  exact ⟨Sum.elim x (Sum.elim q z), by rw [CNF.eval_appendShared, hq, hz]; rfl⟩

private abbrev vertices : ℕ := 64 * 16 ^ 6 * 1025

/-- **The `64 ^ w` bound instantiated**: at `w = 16`, `k = 1025` and `n = 64 * 16 ^ 6 * 1025`, the
clique–colouring formula is refutable, and every refutation has more than `64 ^ 16 / 2` lines. -/
example : (∃ s, (CNF.cliqueColoring vertices 1025 1024).RefutableInSize s) ∧
    ∀ s, (CNF.cliqueColoring vertices 1025 1024).RefutableInSize s → 64 ^ 16 < 2 * s :=
  ⟨CNF.exists_refutableInSize_iff_not_satisfiable.2
      (CNF.not_satisfiable_cliqueColoring (by norm_num)),
    fun _ h => CNF.sixtyFour_pow_lt_two_mul_of_refutableInSize_cliqueColoring (k := 1025)
      (by norm_num) (by norm_num) le_rfl h⟩

/-- A monotone circuit computing `1025`-clique separates the graphs with a `1025`-clique from the
`1024`-colourable graphs, and the separator bound applies to it. -/
example : ∃ C : Circuit Monotone.signature (edgeCount vertices) 1,
    Separates 1025 1024 (fun x => C.eval Monotone.interpretation x 0) ∧ 64 ^ 16 < C.size := by
  obtain ⟨C, hC⟩ := Monotone.exists_computes_clique vertices 1025
  have hsep := Monotone.separates_of_computes_clique (r := 1024) (by norm_num) hC
  exact ⟨C, hsep, Monotone.pow_lt_size_of_separates (k := 1025) (by norm_num) (by norm_num)
    le_rfl hsep⟩

/-- `⌊√2⌋ = 1`. -/
private theorem sqrt_two : Nat.sqrt 2 = 1 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm

/-- **Small cliques**: at `k = 2` and `n = 16`, the clique–colouring formula is refutable, and every
refutation with `s` lines has `2 ^ (2 ⌊√2⌋) < 2 s` and `C(16, 2) = 120 ≤ 1 + 2 s`, so `s ≥ 60`. -/
example : (∃ s, (CNF.cliqueColoring 16 2 1).RefutableInSize s) ∧
    ∀ s, (CNF.cliqueColoring 16 2 1).RefutableInSize s → 4 < 2 * s ∧ 60 ≤ s := by
  refine ⟨CNF.exists_refutableInSize_iff_not_satisfiable.2
    (CNF.not_satisfiable_cliqueColoring (by norm_num)), fun s h => ⟨?_, ?_⟩⟩
  · simpa [sqrt_two] using
      CNF.two_pow_two_mul_sqrt_lt_two_mul_of_refutableInSize_cliqueColoring (k := 2) le_rfl
        (by norm_num) h
  · have edges := CNF.edgeCount_le_one_add_two_mul_of_refutableInSize_cliqueColoring (k := 2)
      le_rfl (by norm_num) h
    rw [edgeCount_eq_choose, show Nat.choose 16 2 = 120 by decide] at edges
    omega

/-- A monotone circuit detecting triangles on four vertices separates the graphs with a triangle
from the `2`-colourable graphs, so it has at least `C(4, 2) - 1 = 5` gates. -/
example : ∃ C : Circuit Monotone.signature (edgeCount 4) 1,
    Separates 3 2 (fun x => C.eval Monotone.interpretation x 0) ∧ 5 ≤ C.size := by
  obtain ⟨C, hC⟩ := Monotone.exists_computes_clique 4 3
  have hsep := Monotone.separates_of_computes_clique (r := 2) (by norm_num) hC
  have edges := Monotone.edgeCount_le_succ_size_of_separates (k := 3) (by norm_num) (by norm_num)
    hsep
  have hcount : edgeCount 4 = 6 := by rw [edgeCount_eq_choose]; decide
  exact ⟨C, hsep, by omega⟩

end ComplexityTests.ProofComplexity.CliqueColoring
