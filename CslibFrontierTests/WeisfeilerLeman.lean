/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman
public import CslibFrontierTests.FOPebbleGames
public import CslibFrontierTests.Foundations.Combinatorics.SimpleGraph.ColorRefinement
import CslibFrontier.Foundations.Data.Fintype.FiberEquiv
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# `k`-dimensional Weisfeiler–Leman and `C^{k+1}`: checked instances

* **`2`-WL (`C³`) separates `C₆` from `C₃ ⊕ C₃`, while `1`-WL (`C²`) does not.** At dimension
  `k = 1`, `C₆` and `C₃ ⊕ C₃` have identical `1`-WL histograms in every round. At dimension `k = 2`,
  adjacent pairs `![0, 1]` in `C₆` and `![.inl 0, .inl 1]` in `C₃ ⊕ C₃` still agree at round `0`
  (and therefore satisfy the same quantifier-free `C³` formulas in `{0, 1}`), but round `1`
  separates both the edge tuples and the graph-level `2`-WL histograms (`wlHistogram 2 1`), refuting
  `C₆ ≃g C₃ ⊕ C₃` purely combinatorially via `isEmpty_iso_of_wlHistogram_ne` and matching the
  rank-`1` common-neighbor formula `hasCommonNeighbor` and rank-`3` sentence `triangle.toCounting`.
* **Sharpness of the `+ k` sentence quantifier-rank shift.** `P₄` and `K₁,₃` (both on `Fin 4`)
  satisfy the exact same `C³` sentences of quantifier rank at most `1`, yet their round-`1` `2`-WL
  histograms (`wlHistogram 2 1`) already differ, showing that rank-`n` sentence equivalence does not
  imply round-`n` `k`-WL histogram equality without the `+ k` shift in
  `wlHistogram_eq_of_forall_realize_countingFormula_empty_le`.
* **Isomorphism invariance and automorphism orbits.** The non-identity isomorphism
  `pathGraphThreeIsoStar : pathGraph 3 ≃g starGraph (0 : Fin 3)` preserves `k`-WL tuple colors and
  histograms across all dimensions and rounds, and rotation on `C₆` implies that distance-`2` pairs
  `![0, 2]` and `![1, 3]` satisfy the same `C³` formulas in `{0, 1}` of every quantifier rank.
* **Dimension `k = 0` (`C¹`) and `[Nonempty]` edge-case controls.** At `k = 0`, the unique empty
  tuples on `P₃` and `P₂` agree at round `0` and separate at round `1` by vertex count; on `Empty`
  vs `Unit`, `[Nonempty]` is required for `wlHistogram (k + 1) 0` agreement.
-/

public section

namespace Cslib.Tests.WeisfeilerLeman

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO
open Cslib.Tests.ColorRefinement
open Cslib.Tests.FOPebbleGames

/-! ### `C₆` vs `C₃ ⊕ C₃`: `1`-WL agrees forever, `2`-WL agrees at round `0` and separates at `1` -/

/-- At dimension `k = 1`, `C₆` and `C₃ ⊕ C₃` have the same `1`-WL histogram in every round. -/
theorem wlHistogram_one_cycleGraph_six_eq_sum (n : ℕ) :
    (cycleGraph 6).wlHistogram 1 n = (cycleGraph 3 ⊕g cycleGraph 3).wlHistogram 1 n :=
  forall_wlHistogram_one_eq_iff.2
    (cycleGraph_six_regular.colorHistogram_eq cycleGraph_three_sum_regular rfl) n

/-- At round `0` of `2`-WL, the adjacent pairs `![0, 1]` in `C₆` and `![.inl 0, .inl 1]` in
`C₃ ⊕ C₃` have the same atomic color, so they satisfy the same quantifier-free `C³` formulas in
`{0, 1}`. -/
theorem wlColoring_zero_edge_cycleGraph_six_eq_sum :
    (cycleGraph 6).wlColoring 0 (![0, 1] : Fin 2 → Fin 6) =
      (cycleGraph 3 ⊕g cycleGraph 3).wlColoring 0
        (![.inl 0, .inl 1] : Fin 2 → Fin 3 ⊕ Fin 3) := by
  rw [wlColoring_zero_eq_iff]
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨iff_of_true rfl rfl, iff_of_false (cycleGraph 6).irrefl
      (cycleGraph 3 ⊕g cycleGraph 3).irrefl⟩
  · refine ⟨iff_of_false (by decide) (by decide), iff_of_true (by decide) ?_⟩
    exact sum_adj_inl.2 (by decide)
  · refine ⟨iff_of_false (by decide) (by decide), iff_of_true (by decide) ?_⟩
    exact sum_adj_inl.2 (by decide)
  · exact ⟨iff_of_true rfl rfl, iff_of_false (cycleGraph 6).irrefl
      (cycleGraph 3 ⊕g cycleGraph 3).irrefl⟩

/-- Quantifier-free `C³` agreement on the edge tuples `![0, 1]` and `![.inl 0, .inl 1]`, deduced
from `wlColoring_zero_edge_cycleGraph_six_eq_sum`. -/
theorem realize_zero_edge_cycleGraph_six_iff_sum
    {φ : FiniteVariable.CountingFormula Language.graph 3}
    (hr : φ.quantifierRank ≤ 0)
    (hφ : ↑φ.freeVars ⊆ Set.range (Fin.castSucc : Fin 2 → Fin 3)) :
    (letI := (cycleGraph 6).structure; φ.Realize (Fin.snoc (![0, 1] : Fin 2 → Fin 6) 0)) ↔
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure;
        φ.Realize (Fin.snoc (![.inl 0, .inl 1] : Fin 2 → Fin 3 ⊕ Fin 3) (.inl 0))) :=
  forall_realize_countingFormula_castSucc_le_iff.2
    wlColoring_zero_edge_cycleGraph_six_eq_sum φ hr hφ

/-- Round `1` of `2`-WL separates the edge `![0, 1]` of `C₆` from the edge `![.inl 0, .inl 1]` of
`C₃ ⊕ C₃`: `.inl 2` completes a triangle with `.inl 0` and `.inl 1`, whereas no vertex in `C₆` is
adjacent to both `0` and `1`. -/
theorem wlColoring_one_edge_cycleGraph_six_ne_sum :
    (cycleGraph 6).wlColoring 1 (![0, 1] : Fin 2 → Fin 6) ≠
      (cycleGraph 3 ⊕g cycleGraph 3).wlColoring 1
        (![.inl 0, .inl 1] : Fin 2 → Fin 3 ⊕ Fin 3) := by
  intro h
  obtain ⟨_, hmset⟩ := wlColoring_succ_eq_iff.1 h
  obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmset
  have hatom := tupleAtom_eq_iff.1 (wlStepProfile_eq_iff.1 (hf (f.symm (.inl 2)))).1
  rw [Equiv.apply_symm_apply] at hatom
  have hadj0 : (cycleGraph 6).Adj 0 (f.symm (.inl 2)) := by
    have h0 := (hatom (0 : Fin 2).castSucc (Fin.last 2)).2
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero] at h0
    exact h0.1 (sum_adj_inl.2 (by decide))
  have hadj1 : (cycleGraph 6).Adj 1 (f.symm (.inl 2)) := by
    have h1 := (hatom (1 : Fin 2).castSucc (Fin.last 2)).2
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_one] at h1
    exact h1.1 (sum_adj_inl.2 (by decide))
  have hex : ∃ v : Fin 6, (cycleGraph 6).Adj 0 v ∧ (cycleGraph 6).Adj 1 v :=
    ⟨f.symm (.inl 2), hadj0, hadj1⟩
  revert hex
  decide

/-- "`x₀` and `x₁` share a common neighbor": a `C³` formula of quantifier rank `1` with free
variables in `Set.range Fin.castSucc`. -/
def hasCommonNeighbor : FiniteVariable.CountingFormula Language.graph 3 :=
  .ex 2 (.rel adj ![0, 2] ⊓ .rel adj ![1, 2])

theorem quantifierRank_hasCommonNeighbor : hasCommonNeighbor.quantifierRank = 1 := by
  rw [hasCommonNeighbor, FiniteVariable.CountingFormula.quantifierRank_ex,
    FiniteVariable.CountingFormula.quantifierRank_inf,
    FiniteVariable.CountingFormula.quantifierRank_rel,
    FiniteVariable.CountingFormula.quantifierRank_rel, max_self]

theorem freeVars_hasCommonNeighbor :
    ↑hasCommonNeighbor.freeVars ⊆ Set.range (Fin.castSucc : Fin 2 → Fin 3) := by
  intro j hj
  rw [hasCommonNeighbor, FiniteVariable.CountingFormula.freeVars_ex,
    FiniteVariable.CountingFormula.freeVars_inf, FiniteVariable.CountingFormula.freeVars_rel,
    FiniteVariable.CountingFormula.freeVars_rel] at hj
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · simp at hj

/-- Explicit rank-`1` `C³` separation of `![0, 1]` in `C₆` from `![.inl 0, .inl 1]` in `C₃ ⊕ C₃`,
matching `wlColoring_one_edge_cycleGraph_six_ne_sum`. -/
theorem hasCommonNeighbor_separates_edges :
    ¬(letI := (cycleGraph 6).structure;
        hasCommonNeighbor.Realize (Fin.snoc (![0, 1] : Fin 2 → Fin 6) 0)) ∧
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure;
        hasCommonNeighbor.Realize
          (Fin.snoc (![.inl 0, .inl 1] : Fin 2 → Fin 3 ⊕ Fin 3) (.inl 0))) := by
  refine ⟨?_, ?_⟩
  · let := (cycleGraph 6).structure
    rw [hasCommonNeighbor, FiniteVariable.CountingFormula.realize_ex]
    rintro ⟨v, hv⟩
    rw [FiniteVariable.CountingFormula.realize_inf, FiniteVariable.CountingFormula.realize_rel,
      FiniteVariable.CountingFormula.realize_rel, ← FinVec.map_eq, ← FinVec.map_eq] at hv
    simp only [FinVec.map] at hv
    have hex : ∃ x : Fin 6, (cycleGraph 6).Adj 0 x ∧ (cycleGraph 6).Adj 1 x := ⟨v, hv.1, hv.2⟩
    revert hex
    decide
  · let := (cycleGraph 3 ⊕g cycleGraph 3).structure
    rw [hasCommonNeighbor, FiniteVariable.CountingFormula.realize_ex]
    refine ⟨.inl 2, ?_⟩
    rw [FiniteVariable.CountingFormula.realize_inf, FiniteVariable.CountingFormula.realize_rel,
      FiniteVariable.CountingFormula.realize_rel, ← FinVec.map_eq, ← FinVec.map_eq]
    simp only [FinVec.map]
    exact ⟨sum_adj_inl.2 (by decide), sum_adj_inl.2 (by decide)⟩

/-- **Round `1` of `2`-WL separates the graphs `C₆` and `C₃ ⊕ C₃`.** No `2`-tuple in `C₆` can match
the round-`1` `2`-WL color of `![.inl 0, .inl 1]` in `C₃ ⊕ C₃`, because that would produce three
mutually adjacent vertices in `C₆`. -/
theorem wlHistogram_two_one_cycleGraph_six_ne_sum :
    (cycleGraph 6).wlHistogram 2 1 ≠ (cycleGraph 3 ⊕g cycleGraph 3).wlHistogram 2 1 := by
  intro h
  have hmem :
      (cycleGraph 3 ⊕g cycleGraph 3).wlColoring 1
        (![.inl 0, .inl 1] : Fin 2 → Fin 3 ⊕ Fin 3) ∈
      (cycleGraph 6).wlHistogram 2 1 := by
    rw [h, mem_wlHistogram]
    exact ⟨![.inl 0, .inl 1], rfl⟩
  obtain ⟨u, hu⟩ := mem_wlHistogram.1 hmem
  obtain ⟨h0, hmset⟩ := wlColoring_succ_eq_iff.1 hu
  obtain ⟨_, hadj01_iff⟩ := (wlColoring_zero_eq_iff.1 h0) 0 1
  have hadj01 : (cycleGraph 6).Adj (u 0) (u 1) := hadj01_iff.2 (sum_adj_inl.2 (by decide))
  obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmset
  have hatom := tupleAtom_eq_iff.1 (wlStepProfile_eq_iff.1 (hf (f.symm (.inl 2)))).1
  rw [Equiv.apply_symm_apply] at hatom
  have hadj0v : (cycleGraph 6).Adj (u 0) (f.symm (.inl 2)) := by
    have h0v := (hatom (0 : Fin 2).castSucc (Fin.last 2)).2
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero] at h0v
    exact h0v.1 (sum_adj_inl.2 (by decide))
  have hadj1v : (cycleGraph 6).Adj (u 1) (f.symm (.inl 2)) := by
    have h1v := (hatom (1 : Fin 2).castSucc (Fin.last 2)).2
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_one] at h1v
    exact h1v.1 (sum_adj_inl.2 (by decide))
  have htri : ∃ x y z : Fin 6,
      (cycleGraph 6).Adj x y ∧ (cycleGraph 6).Adj x z ∧ (cycleGraph 6).Adj y z :=
    ⟨u 0, u 1, f.symm (.inl 2), hadj01, hadj0v, hadj1v⟩
  revert htri
  decide

/-- Purely combinatorial non-isomorphism of `C₆` and `C₃ ⊕ C₃` deduced from `2`-WL at round `1`. -/
theorem isEmpty_iso_cycleGraph_six_sum_via_wl :
    IsEmpty (cycleGraph 6 ≃g cycleGraph 3 ⊕g cycleGraph 3) :=
  isEmpty_iso_of_wlHistogram_ne wlHistogram_two_one_cycleGraph_six_ne_sum

/-- By the Cai–Fürer–Immerman sentence equivalence (`k = 2`), `C₆` and `C₃ ⊕ C₃` are separated by a
`C³` sentence, witnessed explicitly by `triangle.toCounting` at quantifier rank `3`. -/
theorem counting_triangle_separates_cycleGraph_six_sum (a : Fin 3 → Fin 6)
    (b : Fin 3 → Fin 3 ⊕ Fin 3) :
    ¬(letI := (cycleGraph 6).structure; triangle.toCounting.Realize a) ∧
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure; triangle.toCounting.Realize b) := by
  have htri : ¬(letI := (cycleGraph 6).structure; triangle.Realize a) ∧
      (letI := (cycleGraph 3 ⊕g cycleGraph 3).structure; triangle.Realize b) := by
    refine ⟨not_realize_triangle_fin a, ?_⟩
    let := (cycleGraph 3 ⊕g cycleGraph 3).structure
    exact (realize_triangle_iff b).2
      ⟨.inl 0, .inl 1, .inl 2, sum_adj_inl.2 (by decide), sum_adj_inl.2 (by decide),
        sum_adj_inl.2 (by decide)⟩
  refine ⟨?_, ?_⟩
  · let := (cycleGraph 6).structure
    rw [FiniteVariable.Formula.realize_toCounting]
    exact htri.1
  · let := (cycleGraph 3 ⊕g cycleGraph 3).structure
    rw [FiniteVariable.Formula.realize_toCounting]
    exact htri.2

/-! ### Sharpness of the `+ k` shift: `P₄` and `K₁,₃` agree at rank `1` in `C³` yet differ in
`wlHistogram 2 1` -/

/-- `P₄` and `K₁,₃` (both on `Fin 4`) satisfy the exact same `C³` sentences of quantifier rank at
most `1`, yet their round-`1` `2`-WL histograms already differ because `![0, 0]` in `K₁,₃` sees `3`
distinct neighbors while every vertex of `P₄` has degree at most `2`. -/
theorem rank_one_c3_agrees_but_wlHistogram_two_one_ne :
    (∀ φ : FiniteVariable.CountingFormula Language.graph 3,
      φ.quantifierRank ≤ 1 → φ.freeVars = ∅ →
        ∀ a b : Fin 3 → Fin 4,
          ((letI := (pathGraph 4).structure; φ.Realize a) ↔
            (letI := (starGraph (0 : Fin 4)).structure; φ.Realize b))) ∧
      (pathGraph 4).wlHistogram 2 1 ≠ (starGraph (0 : Fin 4)).wlHistogram 2 1 := by
  refine ⟨fun φ hr hφ a b =>
    realize_countingFormula_le_one_iff_of_card_eq rfl hr hφ a b, fun h => ?_⟩
  have hmem : (starGraph (0 : Fin 4)).wlColoring 1 (![0, 0] : Fin 2 → Fin 4) ∈
      (pathGraph 4).wlHistogram 2 1 := by
    rw [h, mem_wlHistogram]
    exact ⟨![0, 0], rfl⟩
  obtain ⟨u, hu⟩ := mem_wlHistogram.1 hmem
  obtain ⟨_, hmset⟩ := wlColoring_succ_eq_iff.1 hu
  obtain ⟨f, hf⟩ := Equiv.exists_apply_eq_iff_map_univ_eq.2 hmset
  have hadj : ∀ z : Fin 4, (starGraph (0 : Fin 4)).Adj 0 z →
      (pathGraph 4).Adj (u 0) (f.symm z) := by
    intro z hz
    have hatom := tupleAtom_eq_iff.1 (wlStepProfile_eq_iff.1 (hf (f.symm z))).1
    rw [Equiv.apply_symm_apply] at hatom
    have h0 := (hatom (0 : Fin 2).castSucc (Fin.last 2)).2
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.cons_val_zero] at h0
    exact h0.1 hz
  have hdeg3 : ∃ x y₁ y₂ y₃ : Fin 4,
      y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧
        (pathGraph 4).Adj x y₁ ∧ (pathGraph 4).Adj x y₂ ∧ (pathGraph 4).Adj x y₃ :=
    ⟨u 0, f.symm 1, f.symm 2, f.symm 3,
      f.symm.injective.ne (by decide), f.symm.injective.ne (by decide),
      f.symm.injective.ne (by decide),
      hadj 1 (by decide), hadj 2 (by decide), hadj 3 (by decide)⟩
  revert hdeg3
  decide

/-! ### Positive tests: non-identity graph isomorphism and `C₆` automorphism orbits -/

/-- Swapping `0` and `1` on `Fin 3` is a non-identity isomorphism `P₃ ≃g K₁,₂`. -/
def pathGraphThreeIsoStar : pathGraph 3 ≃g starGraph (0 : Fin 3) where
  toEquiv := Equiv.swap (0 : Fin 3) 1
  map_rel_iff' {x y} := by
    revert x y
    decide

/-- Non-identity isomorphism invariance of `k`-WL histograms across all dimensions and rounds. -/
theorem wlHistogram_pathGraph_three_eq_star (k n : ℕ) :
    (pathGraph 3).wlHistogram k n = (starGraph (0 : Fin 3)).wlHistogram k n :=
  (pathGraphThreeIsoStar.wlHistogram_eq k n).symm

/-- Cyclic shift `v ↦ v + 1` as an automorphism of `C₆`. -/
def cycleGraphSixRot : cycleGraph 6 ≃g cycleGraph 6 where
  toEquiv := Equiv.addRight (1 : Fin 6)
  map_rel_iff' {x y} := by
    revert x y
    decide

/-- Distance-`2` pairs `![0, 2]` and `![1, 3]` in `C₆` lie in the same automorphism orbit, so they
receive the same `2`-WL color in every round and satisfy the exact same `C³` formulas in `{0, 1}`
of every quantifier rank. -/
theorem distance_two_pairs_cycleGraph_six_realize_iff
    {φ : FiniteVariable.CountingFormula Language.graph 3}
    (hφ : ↑φ.freeVars ⊆ Set.range (Fin.castSucc : Fin 2 → Fin 3)) :
    (letI := (cycleGraph 6).structure; φ.Realize (Fin.snoc (![0, 2] : Fin 2 → Fin 6) 0)) ↔
      (letI := (cycleGraph 6).structure; φ.Realize (Fin.snoc (![1, 3] : Fin 2 → Fin 6) 0)) := by
  refine forall_realize_countingFormula_castSucc_iff.2 (fun n => ?_) φ hφ
  have hcomp : (cycleGraphSixRot ∘ (![0, 2] : Fin 2 → Fin 6)) = ![1, 3] := by
    ext i
    fin_cases i <;> rfl
  rw [← hcomp]
  exact (cycleGraphSixRot.wlColoring_comp n (![0, 2] : Fin 2 → Fin 6)).symm

/-! ### Small-`k` (`k = 0`) and empty-graph negative controls -/

/-- At dimension `k = 0`, the unique empty tuples on `P₃` and `P₂` agree at round `0` and separate
at round `1` because their step-profile multisets have sizes `3` and `2`. -/
theorem zero_dim_wl_separates_orders :
    (pathGraph 3).wlColoring 0 (Fin.elim0 : Fin 0 → Fin 3) =
        (pathGraph 2).wlColoring 0 (Fin.elim0 : Fin 0 → Fin 2) ∧
      (pathGraph 3).wlColoring 1 (Fin.elim0 : Fin 0 → Fin 3) ≠
        (pathGraph 2).wlColoring 1 (Fin.elim0 : Fin 0 → Fin 2) := by
  refine ⟨?_, fun h => ?_⟩
  · rw [wlColoring_zero_eq_iff]
    exact fun i => Fin.elim0 i
  · obtain ⟨_, hmset⟩ := wlColoring_succ_eq_iff.1 h
    have hcard := congrArg Multiset.card hmset
    simp only [Multiset.card_map, Finset.card_val, Finset.card_fin] at hcard
    omega

/-- **Nonemptiness is necessary in `forall_realize_countingFormula_empty_iff_wlHistogram_eq` for
every positive dimension `k + 1`.** Quantification over assignments `Fin (k + 2) → Empty` holds
vacuously, whereas `wlHistogram (k + 1) 0` has cardinality `0` on `Empty` and `1` on `Unit`. -/
theorem vacuous_empty_graph_wl_counterexample (k : ℕ) :
    (∀ φ : FiniteVariable.CountingFormula Language.graph (k + 2),
      φ.freeVars = ∅ →
        ∀ (a : Fin (k + 2) → Empty) (b : Fin (k + 2) → Unit),
          ((letI := (⊥ : SimpleGraph Empty).structure; φ.Realize a) ↔
            (letI := (⊥ : SimpleGraph Unit).structure; φ.Realize b))) ∧
      (⊥ : SimpleGraph Empty).wlHistogram (k + 1) 0 ≠
        (⊥ : SimpleGraph Unit).wlHistogram (k + 1) 0 := by
  refine ⟨fun _ _ a => isEmptyElim (a 0), fun h => ?_⟩
  have hcard := congrArg Multiset.card h
  rw [card_wlHistogram, card_wlHistogram, Fintype.card_empty, Fintype.card_unit,
    zero_pow (Nat.succ_ne_zero k), one_pow] at hcard
  omega

end Cslib.Tests.WeisfeilerLeman
