/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
public import CslibFrontierTests.FOPebbleGames
public import CslibFrontierTests.Foundations.Combinatorics.SimpleGraph.ColorRefinement
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# The Immerman–Lander theorem: checked instances

* **`C₆` and `C₃ ⊕ C₃` agree on `C²` and are separated by `FO³`.** Both graphs are `2`-regular of
  order `6`, so `SimpleGraph.IsRegularOfDegree.colorHistogram_eq` gives equal color histograms in
  every round without constructing bijections by hand. By the Immerman–Lander theorem, they satisfy
  the same `C²` sentences of every quantifier rank (and any two of their vertices satisfy the same
  one-variable `C²` formulas), while the three-variable `triangle` sentence separates them at
  quantifier rank `3`.
* **Round `0` / quantifier rank `1`: order separation.** `P₃` and `P₂` have different round-`0`
  color histograms and are separated by the rank-`1` sentence `atLeastVertices 3`.
* **Round `1` / quantifier rank `2`: degree-sequence separation at equal order.** `P₄` and `K₁,₃`
  (both on `Fin 4`, exercising shared vertex types) agree at round `0` and therefore satisfy the
  same `C²` sentences of quantifier rank at most `1`, but differ at round `1` and are separated at
  quantifier rank `2` by `existsDegAtLeastThree`.
* **Vertex-level (`1` free variable) round `1` / rank `1`.** On `P₃`, an endpoint and the middle
  vertex differ in round-`1` color and are separated by a `C²` formula of quantifier rank `1`,
  whereas the two endpoints receive the same color in every round and satisfy the same `C²`
  formulas in `x₀` of every quantifier rank.
* **Empty-graph negative control.** Without `[Nonempty V]`, the assignment-quantified `C²`
  sentence condition holds vacuously between the empty graph on `Empty` and the one-vertex graph on
  `Unit`, even though their round-`0` histograms differ.
-/

public section

namespace Cslib.Tests.ImmermanLander

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO
open Cslib.Tests.ColorRefinement
open Cslib.Tests.FOPebbleGames

private theorem comp_vec_two {α β : Type*} (a : α → β) (i j : α) : a ∘ ![i, j] = ![a i, a j] :=
  (FinVec.map_eq a ![i, j]).symm

/-! ### `C₆` vs `C₃ ⊕ C₃`: `C²`-equivalence from regularity, `FO³` separation by triangles -/

/-- By `IsRegularOfDegree.colorHistogram_eq` and the Immerman–Lander theorem, `C₆` and `C₃ ⊕ C₃`
satisfy the exact same `C²` sentences of every quantifier rank. -/
theorem realize_cycleGraph_six_iff_sum
    {φ : FiniteVariable.CountingFormula Language.graph 2} (hφ : φ.freeVars = ∅)
    (a : Fin 2 → Fin 6) (b : Fin 2 → Fin 3 ⊕ Fin 3) :
    (letI := (cycleGraph 6).structure; φ.Realize a) ↔
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure; φ.Realize b) :=
  forall_realize_countingFormula_empty_iff.2
    (cycleGraph_six_regular.colorHistogram_eq cycleGraph_three_sum_regular rfl) φ hφ a b

/-- Every vertex of `C₆` and every vertex of `C₃ ⊕ C₃` satisfy the same `C²` formulas in `x₀`:
their disjoint union is `2`-regular, so its constant coloring is already equitable and all vertices
share a single color in every round. -/
theorem realize_cycleGraph_six_vertex_iff_sum
    {φ : FiniteVariable.CountingFormula Language.graph 2}
    (hφ : ↑φ.freeVars ⊆ ({0} : Set (Fin 2))) (v : Fin 6) (w : Fin 3 ⊕ Fin 3) :
    (letI := (cycleGraph 6).structure; φ.Realize (fun _ => v)) ↔
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure; φ.Realize (fun _ => w)) := by
  refine (forall_realize_countingFormula_singleton_iff_card_add_card (i := 0) (v := v) (w := w)).2
    ⟨?_, cycleGraph_six_regular.colorHistogram_eq cycleGraph_three_sum_regular rfl _⟩ φ hφ
  let U := cycleGraph 6 ⊕g (cycleGraph 3 ⊕g cycleGraph 3)
  have hU_reg : U.IsRegularOfDegree 2 := by
    rintro (u | u)
    · rw [← card_neighborFinset_eq_degree, neighborFinset_sum_inl, Finset.card_map,
        card_neighborFinset_eq_degree, cycleGraph_six_regular.degree_eq]
    · rw [← card_neighborFinset_eq_degree, neighborFinset_sum_inr, Finset.card_map,
        card_neighborFinset_eq_degree, cycleGraph_three_sum_regular.degree_eq]
  have hU_eq : U.IsEquitable (fun _ => ()) :=
    (isEquitable_const_iff ()).2 fun x y => by rw [hU_reg.degree_eq, hU_reg.degree_eq]
  have hker := hU_eq.ker_le_ker_refinementColoring (χ₀ := fun _ => ()) le_rfl
    (Fintype.card (Fin 6) + Fintype.card (Fin 3 ⊕ Fin 3))
    (x := .inl v) (y := .inr w) rfl
  rw [Setoid.ker_def, refinementColoring_sum_inl, refinementColoring_sum_inr] at hker
  exact hker

/-- The three-variable `triangle` sentence holds in `C₃ ⊕ C₃` and fails in `C₆`, separating them in
`FO³` (and via `Formula.toCounting` in `C³`) at quantifier rank `3`. -/
theorem triangle_separates_cycleGraph_six_sum (a : Fin 3 → Fin 6)
    (b : Fin 3 → Fin 3 ⊕ Fin 3) :
    ¬(letI := (cycleGraph 6).structure; triangle.Realize a) ∧
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure; triangle.Realize b) := by
  refine ⟨not_realize_triangle_fin a, ?_⟩
  let := (cycleGraph 3 ⊕g cycleGraph 3).structure
  refine (realize_triangle_iff b).2 ⟨.inl 0, .inl 1, .inl 2, ?_, ?_, ?_⟩
  · exact sum_adj_inl.2 (by decide)
  · exact sum_adj_inl.2 (by decide)
  · exact sum_adj_inl.2 (by decide)

/-! ### Round `0` / quantifier rank `1`: separating graphs of different orders -/

/-- At least `m` vertices: a `C²` sentence of quantifier rank `1`. -/
def atLeastVertices (m : ℕ) : FiniteVariable.CountingFormula Language.graph 2 :=
  .atLeast m 0 ⊤

theorem quantifierRank_atLeastVertices (m : ℕ) : (atLeastVertices m).quantifierRank = 1 := by
  rw [atLeastVertices, FiniteVariable.CountingFormula.quantifierRank_atLeast,
    FiniteVariable.CountingFormula.quantifierRank_top]

theorem freeVars_atLeastVertices (m : ℕ) : (atLeastVertices m).freeVars = ∅ := by
  rw [atLeastVertices, FiniteVariable.CountingFormula.freeVars_atLeast,
    FiniteVariable.CountingFormula.freeVars_top, Finset.erase_empty]

theorem realize_atLeastVertices {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ)
    (a : Fin 2 → V) :
    (letI := G.structure; (atLeastVertices m).Realize a) ↔ m ≤ Fintype.card V := by
  let := G.structure
  rw [atLeastVertices, FiniteVariable.CountingFormula.realize_atLeast]
  simp only [FiniteVariable.CountingFormula.realize_top, Set.ofPred_true, Set.encard_univ,
    ENat.card_eq_coe_fintype_card, Nat.cast_le]

/-- `P₃` and `P₂` have different round-`0` histograms, so Immerman–Lander guarantees a separating
`C²` sentence of quantifier rank at most `1`, witnessed explicitly by `atLeastVertices 3`. -/
theorem round_zero_separates_pathGraph_three_two :
    (pathGraph 3).colorHistogram (fun _ => ()) 0 ≠
        (pathGraph 2).colorHistogram (fun _ => ()) 0 ∧
      (∀ a : Fin 2 → Fin 3,
        letI := (pathGraph 3).structure; (atLeastVertices 3).Realize a) ∧
      ∀ b : Fin 2 → Fin 2,
        ¬(letI := (pathGraph 2).structure; (atLeastVertices 3).Realize b) := by
  refine ⟨fun h => ?_, fun a => ?_, fun b => ?_⟩
  · rw [colorHistogram_zero_const_eq_iff, Fintype.card_fin, Fintype.card_fin] at h
    omega
  · rw [realize_atLeastVertices, Fintype.card_fin]
  · rw [realize_atLeastVertices, Fintype.card_fin]
    omega

/-! ### Round `1` / quantifier rank `2`: separating degree sequences at equal order -/

/-- `P₄` and `K₁,₃` (both on `Fin 4`) have the same order, so their round-`0` histograms agree and
they satisfy the exact same `C²` sentences of quantifier rank at most `1`. -/
theorem pathGraph_four_iff_starGraph_le_one
    {φ : FiniteVariable.CountingFormula Language.graph 2}
    (hr : φ.quantifierRank ≤ 1) (hφ : φ.freeVars = ∅) (a b : Fin 2 → Fin 4) :
    (letI := (pathGraph 4).structure; φ.Realize a) ↔
      (letI := (starGraph (0 : Fin 4)).structure; φ.Realize b) := by
  refine forall_realize_countingFormula_empty_le_iff (n := 0) |>.2 ?_ φ hr hφ a b
  rw [colorHistogram_zero_const, colorHistogram_zero_const]

/-- "Some vertex has degree at least `3`": a `C²` sentence of quantifier rank `2`. -/
def existsDegAtLeastThree : FiniteVariable.CountingFormula Language.graph 2 :=
  .ex 0 (.atLeast 3 1 (.rel adj ![0, 1]))

theorem quantifierRank_existsDegAtLeastThree :
    existsDegAtLeastThree.quantifierRank = 2 := by
  rw [existsDegAtLeastThree, FiniteVariable.CountingFormula.quantifierRank_ex,
    FiniteVariable.CountingFormula.quantifierRank_atLeast,
    FiniteVariable.CountingFormula.quantifierRank_rel]

theorem freeVars_existsDegAtLeastThree : existsDegAtLeastThree.freeVars = ∅ := by
  rw [existsDegAtLeastThree, FiniteVariable.CountingFormula.freeVars_ex,
    FiniteVariable.CountingFormula.freeVars_atLeast, FiniteVariable.CountingFormula.freeVars_rel]
  decide

/-- Round `1` separates `P₄` and `K₁,₃`, so Immerman–Lander refutes rank-`2` `C²`-equivalence, and
`existsDegAtLeastThree` explicitly holds in `K₁,₃` and fails in `P₄`. -/
theorem round_one_separates_pathGraph_four_starGraph :
    (pathGraph 4).colorHistogram (fun _ => ()) 1 ≠
        (starGraph (0 : Fin 4)).colorHistogram (fun _ => ()) 1 ∧
      (∀ b : Fin 2 → Fin 4,
        letI := (starGraph (0 : Fin 4)).structure; existsDegAtLeastThree.Realize b) ∧
      ∀ a : Fin 2 → Fin 4,
        ¬(letI := (pathGraph 4).structure; existsDegAtLeastThree.Realize a) := by
  have hne : (pathGraph 4).colorHistogram (fun _ => ()) 1 ≠
      (starGraph (0 : Fin 4)).colorHistogram (fun _ => ()) 1 := by
    intro h
    have hmem : (starGraph (0 : Fin 4)).refinementColoring (fun _ => ()) 1 0 ∈
        (pathGraph 4).colorHistogram (fun _ => ()) 1 := by
      rw [h, mem_colorHistogram]
      exact ⟨0, rfl⟩
    obtain ⟨v, hv⟩ := mem_colorHistogram.1 hmem
    have hdeg := congrArg (fun c : RefinementColor Unit 1 => Multiset.card c.2) hv
    simp only [refinementColoring_succ, card_refineColoring_snd] at hdeg
    clear hv
    revert v
    decide
  refine ⟨hne, fun b => ?_, fun a => ?_⟩
  · let := (starGraph (0 : Fin 4)).structure
    rw [existsDegAtLeastThree, FiniteVariable.CountingFormula.realize_ex]
    refine ⟨0, ?_⟩
    rw [FiniteVariable.CountingFormula.realize_atLeast]
    have hset : {c : Fin 4 |
        (FiniteVariable.CountingFormula.rel adj ![0, 1]).Realize
          (Function.update (Function.update b 0 0) 1 c)} = ({1, 2, 3} : Finset (Fin 4)) := by
      ext c
      simp only [FiniteVariable.CountingFormula.realize_rel, comp_vec_two,
        Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      change (starGraph (0 : Fin 4)).Adj 0 c ↔ c ∈ ({1, 2, 3} : Finset (Fin 4))
      revert c
      decide
    rw [hset, Set.encard_coe_eq_coe_finsetCard]
    decide
  · let := (pathGraph 4).structure
    rw [existsDegAtLeastThree, FiniteVariable.CountingFormula.realize_ex]
    rintro ⟨v, hv⟩
    rw [FiniteVariable.CountingFormula.realize_atLeast] at hv
    have hsub : {c : Fin 4 |
        (FiniteVariable.CountingFormula.rel adj ![0, 1]).Realize
          (Function.update (Function.update a 0 v) 1 c)} =
        ((pathGraph 4).neighborFinset v : Set (Fin 4)) := by
      ext c
      simp only [Set.mem_ofPred_eq, FiniteVariable.CountingFormula.realize_rel, comp_vec_two,
        Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Finset.mem_coe, mem_neighborFinset]
      rfl
    rw [hsub, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at hv
    clear hsub a hne
    revert v hv
    decide

/-! ### Vertex-level (`1` free variable) separation and equivalence on `P₃` -/

/-- "Vertex `x₀` has degree at least `2`": a `C²` formula of quantifier rank `1` in `{0}`. -/
def degAtLeastTwo : FiniteVariable.CountingFormula Language.graph 2 :=
  .atLeast 2 1 (.rel adj ![0, 1])

theorem quantifierRank_degAtLeastTwo : degAtLeastTwo.quantifierRank = 1 := by
  rw [degAtLeastTwo, FiniteVariable.CountingFormula.quantifierRank_atLeast,
    FiniteVariable.CountingFormula.quantifierRank_rel]

theorem freeVars_degAtLeastTwo : degAtLeastTwo.freeVars ⊆ {0} := by
  rw [degAtLeastTwo, FiniteVariable.CountingFormula.freeVars_atLeast,
    FiniteVariable.CountingFormula.freeVars_rel]
  decide

/-- On `P₃`, endpoint `0` and middle vertex `1` receive different colors after one round and are
separated by `degAtLeastTwo` at quantifier rank `1`. -/
theorem vertex_round_one_separates_pathGraph_three :
    (pathGraph 3).refinementColoring (fun _ => ()) 1 0 ≠
        (pathGraph 3).refinementColoring (fun _ => ()) 1 1 ∧
      ¬(letI := (pathGraph 3).structure; degAtLeastTwo.Realize (fun _ => (0 : Fin 3))) ∧
      (letI := (pathGraph 3).structure; degAtLeastTwo.Realize (fun _ => (1 : Fin 3))) := by
  have hne : (pathGraph 3).refinementColoring (fun _ => ()) 1 0 ≠
      (pathGraph 3).refinementColoring (fun _ => ()) 1 1 := by
    intro h
    have hdeg := congrArg (fun c : RefinementColor Unit 1 => Multiset.card c.2) h
    simp only [refinementColoring_succ, card_refineColoring_snd] at hdeg
    revert hdeg
    decide
  let := (pathGraph 3).structure
  have hreal : ∀ v : Fin 3, degAtLeastTwo.Realize (fun _ => v) ↔
      2 ≤ ((pathGraph 3).neighborFinset v).card := by
    intro v
    rw [degAtLeastTwo, FiniteVariable.CountingFormula.realize_atLeast]
    have hset : {c : Fin 3 |
        (FiniteVariable.CountingFormula.rel adj ![0, 1]).Realize
          (Function.update (fun _ : Fin 2 => v) 1 c)} =
        ((pathGraph 3).neighborFinset v : Set (Fin 3)) := by
      ext c
      simp only [Set.mem_ofPred_eq, FiniteVariable.CountingFormula.realize_rel, comp_vec_two,
        Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        Finset.mem_coe, mem_neighborFinset]
      rfl
    rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  refine ⟨hne, ?_, ?_⟩
  · rw [hreal]
    decide
  · rw [hreal]
    decide

/-- Conversely, the two endpoints `0` and `2` of `P₃` belong to the same equitable class of
`isEquitable_pathGraph_three_middle`, so they receive the same color in every round and satisfy the
same `C²` formulas in `x₀` of every quantifier rank. -/
theorem endpoints_pathGraph_three_realize_iff
    {φ : FiniteVariable.CountingFormula Language.graph 2}
    (hφ : ↑φ.freeVars ⊆ ({0} : Set (Fin 2))) :
    (letI := (pathGraph 3).structure; φ.Realize (fun _ => (0 : Fin 3))) ↔
      (letI := (pathGraph 3).structure; φ.Realize (fun _ => (2 : Fin 3))) := by
  refine forall_realize_countingFormula_singleton_iff.2 ⟨fun n => ?_, fun _ => rfl⟩ φ hφ
  exact isEquitable_pathGraph_three_middle.ker_le_ker_refinementColoring
    (χ₀ := fun _ => ()) (fun _ _ _ => rfl) n (by decide : decide ((0 : Fin 3) = 1) = decide (2 = 1))

/-! ### Negative control and small-cardinality edge cases -/

/-- **Nonemptiness is necessary in `forall_realize_countingFormula_empty_le_iff`.** Between the
empty graph on `Empty` and the one-vertex graph on `Unit`, universal quantification over
assignments `Fin 2 → Empty` is vacuously true for every `C²` sentence, even though the round-`0`
color histograms differ (`0 ≠ {()}`). -/
theorem vacuous_empty_graph_counterexample :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 2,
      φ.freeVars = ∅ →
        ∀ (a : Fin 2 → Empty) (b : Fin 2 → Unit),
          ((letI := (⊥ : SimpleGraph Empty).structure; φ.Realize a) ↔
            (letI := (⊥ : SimpleGraph Unit).structure; φ.Realize b))) ∧
      (⊥ : SimpleGraph Empty).colorHistogram (fun _ => ()) 0 ≠
        (⊥ : SimpleGraph Unit).colorHistogram (fun _ => ()) 0 := by
  refine ⟨fun _ _ a => isEmptyElim (a 0), fun h => ?_⟩
  rw [colorHistogram_zero_const_eq_iff, Fintype.card_empty, Fintype.card_unit] at h
  omega

/-- Edge case on a `1`-vertex graph with both pebbles placed (`S = Set.univ`): Duplicator wins the
one-round bijective `2`-pebble game via `bijPebbleWins_graph_univ_iff`. -/
example :
    letI := (⊥ : SimpleGraph Unit).structure
    BijPebbleWins Language.graph 1 Set.univ (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) := by
  refine (bijPebbleWins_graph_univ_iff (G := (⊥ : SimpleGraph Unit))
    (H := (⊥ : SimpleGraph Unit)) (n := 0)).2 ⟨?_, fun _ => rfl, rfl⟩
  let := (⊥ : SimpleGraph Unit).structure
  exact PartialIso.refl (fun _ => ())

end Cslib.Tests.ImmermanLander
