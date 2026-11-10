/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BinomialRandomGraph

/-!
# Tests for the 0-1 law for `G(n, p)` with constant edge probability

The law at the edge probability `p = 1/3 ≠ 1/2`: a triangle exists almost surely and "there are no
edges" fails almost surely, both decided in the Rado graph. The hypothesis `0 < p < 1` is needed:
in `G(n, 0)` (no edges) and in `G(n, 1)` (complete) an extension axiom that holds in the Rado graph
has probability `0` for every `n ≥ 1`, so the Rado-graph characterization fails at `p = 0` and
`p = 1`. Finally `G(2, 1/2)` agrees with the uniform random graph on its only potential edge.
-/

namespace CslibFrontierTests.BinomialZeroOneLaw

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.graph
open MeasureTheory unitInterval Filter
open scoped SimpleGraph
open SimpleGraph (radoGraph)

/-! ### The law at `p = 1/3` -/

/-- The edge probability `1/3`. -/
noncomputable def third : I := ⟨1 / 3, by norm_num, by norm_num⟩

theorem third_pos : 0 < (third : ℝ) := by
  change (0 : ℝ) < 1 / 3
  norm_num

theorem third_lt_one : (third : ℝ) < 1 := by
  change (1 / 3 : ℝ) < 1
  norm_num

/-- The sentence "there is a triangle". -/
noncomputable def hasTriangle : Language.graph.Sentence :=
  closeEx (Fin 3)
    (rel₂ adj (0 : Fin 3) 1 ⊓ rel₂ adj (1 : Fin 3) 2 ⊓ rel₂ adj (0 : Fin 3) 2)

/-- The Rado graph has the triangle `0, 1, 3`, so `G(n, 1/3)` has a triangle with probability
tending to `1`. -/
example : Tendsto (fun n => G(Fin n, third).real {G | Satisfies G hasTriangle}) atTop (nhds 1) := by
  rw [tendsto_binomialRandom_real_one_iff_radoGraph third_pos third_lt_one]
  let := radoGraph.structure
  change Sentence.Realize ℕ hasTriangle
  rw [hasTriangle, realize_closeEx]
  refine ⟨![0, 1, 3], ?_⟩
  simp only [Formula.realize_inf, realize_rel₂]
  exact ⟨⟨(by decide : radoGraph.Adj 0 1), (by decide : radoGraph.Adj 1 3)⟩,
    (by decide : radoGraph.Adj 0 3)⟩

/-- The sentence "there are no edges". -/
noncomputable def noEdges : Language.graph.Sentence :=
  closeAll (Fin 2) ∼(rel₂ adj (0 : Fin 2) 1)

/-- The Rado graph has the edge `0 1`, so `G(n, 1/3)` has no edges with probability tending to
`0`. -/
example : Tendsto (fun n => G(Fin n, third).real {G | Satisfies G noEdges}) atTop (nhds 0) := by
  rw [tendsto_binomialRandom_real_zero_iff_radoGraph third_pos third_lt_one]
  let := radoGraph.structure
  change ¬Sentence.Realize ℕ noEdges
  rw [noEdges, realize_closeAll]
  intro h
  have := h ![0, 1]
  simp only [Formula.realize_not, realize_rel₂] at this
  exact this (by decide : radoGraph.Adj 0 1)

/-- The extension axioms hold almost surely in `G(n, 1/3)`, as at `p = 1/2`. -/
example : Tendsto (fun n => G(Fin n, third).real
    {G | Satisfies G (extensionAxiom 2 ![true, false])}) atTop (nhds 1) :=
  tendsto_binomialRandom_real_extensionAxiom third_pos third_lt_one 2 _

/-- The almost-sure sentences of `G(n, 1/3)` and `G(n, 1/2)` agree. -/
example (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, third).real {G | Satisfies G φ}) atTop (nhds 1) ↔
      Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) atTop (nhds 1) :=
  tendsto_binomialRandom_real_one_iff_tendsto_randomGraphProb third_pos third_lt_one φ

/-! ### The hypothesis `0 < p < 1` is needed -/

/-- `G(n, 0)` is the empty graph, which violates the extension axiom "every vertex has a neighbour"
once `n ≥ 1`. -/
theorem binomialRandom_zero_real_extensionAxiom {n : ℕ} (hn : 1 ≤ n) :
    G(Fin n, 0).real {G | Satisfies G (extensionAxiom 1 fun _ => true)} = 0 := by
  rw [SimpleGraph.binomialRandom_zero, Measure.dirac_real_apply, Set.indicator_of_notMem]
  rw [Set.mem_ofPred_eq, satisfies_extensionAxiom_iff]
  intro h
  obtain ⟨z, -, hz⟩ := h (fun _ => ⟨0, hn⟩) (fun i j _ => Subsingleton.elim i j)
  exact (SimpleGraph.bot_adj _ _).1 ((hz 0).2 rfl)

/-- At `p = 0` the Rado-graph characterization fails: the Rado graph satisfies "every vertex has a
neighbour", yet its probability in `G(n, 0)` does not tend to `1`. -/
example : ¬(Tendsto (fun n => G(Fin n, 0).real
      {G | Satisfies G (extensionAxiom 1 fun _ => true)}) atTop (nhds 1) ↔
    Satisfies radoGraph (extensionAxiom 1 fun _ => true)) := by
  rw [iff_iff_implies_and_implies, not_and_or]
  refine Or.inr fun h => ?_
  have h0 : Tendsto (fun n => G(Fin n, 0).real
      {G | Satisfies G (extensionAxiom 1 fun _ => true)}) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (binomialRandom_zero_real_extensionAxiom hn).symm)
  exact zero_ne_one (tendsto_nhds_unique h0 (h (satisfies_extensionAxiom_radoGraph 1 _)))

/-- `G(n, 1)` is the complete graph, which violates the extension axiom "every vertex has a
non-neighbour" once `n ≥ 1`. -/
theorem binomialRandom_one_real_extensionAxiom {n : ℕ} (hn : 1 ≤ n) :
    G(Fin n, 1).real {G | Satisfies G (extensionAxiom 1 fun _ => false)} = 0 := by
  rw [SimpleGraph.binomialRandom_one, Measure.dirac_real_apply, Set.indicator_of_notMem]
  rw [Set.mem_ofPred_eq, satisfies_extensionAxiom_iff]
  intro h
  obtain ⟨z, hz, hadj⟩ := h (fun _ => ⟨0, hn⟩) (fun i j _ => Subsingleton.elim i j)
  exact Bool.false_ne_true ((hadj 0).1 ((SimpleGraph.top_adj _ _).2 (hz 0)))

/-- At `p = 1` the Rado-graph characterization fails: the Rado graph satisfies "every vertex has a
non-neighbour", yet its probability in `G(n, 1)` does not tend to `1`. -/
example : ¬(Tendsto (fun n => G(Fin n, 1).real
      {G | Satisfies G (extensionAxiom 1 fun _ => false)}) atTop (nhds 1) ↔
    Satisfies radoGraph (extensionAxiom 1 fun _ => false)) := by
  rw [iff_iff_implies_and_implies, not_and_or]
  refine Or.inr fun h => ?_
  have h0 : Tendsto (fun n => G(Fin n, 1).real
      {G | Satisfies G (extensionAxiom 1 fun _ => false)}) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (binomialRandom_one_real_extensionAxiom hn).symm)
  exact zero_ne_one (tendsto_nhds_unique h0 (h (satisfies_extensionAxiom_radoGraph 1 _)))

/-! ### `G(n, 1/2)` is the uniform random graph -/

/-- The edge probability `1/2`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- In `G(2, 1/2)` the only potential edge is present with probability `1/2`, as in the uniform
random graph. -/
example : G(Fin 2, half).real {G | G.Adj 0 1} = 1 / 2 := by
  rw [binomialRandom_real_eq_randomGraphProb rfl]
  exact randomGraphProb_adj (by decide)

end CslibFrontierTests.BinomialZeroOneLaw
