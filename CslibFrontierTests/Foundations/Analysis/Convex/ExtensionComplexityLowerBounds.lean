/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Cut
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.TSP
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for exponential extension-complexity lower bounds

Kernel-checked examples (without `native_decide`) exercising:

* `UniqueDisjointness`: valid/invalid disjoint-pair families on `Fin 1`, `3 ^ 1` disjoint pairs,
  `coverNumber` lower bound `3 ≤ r` on `Fin 2`, and `3 ≤ N¹(UDISJ)` on `Fin 4`.
* `Correlation`: evaluation of `2 diag(a) - a aᵀ` on `Fin 2`, an explicit exterior point outside
  `corrPolytope ℚ (Fin 2)`, and `4 ≤ r` on `Fin 3`.
* `Cut`: nonvacuous `cutPolytope ℚ (Fin 4)` bound `4 ≤ r` and singleton degeneracy on `Fin 1`.
* `StableSet`: `card_corrGadgetV` (`|V(H₁)| = 2`) and `stabHardGraph` bounds for `m = 8` (`3 ≤ r`)
  and `m = 18` (`4 ≤ r`).
* `TourSplit` and `CorrDigraph`: concrete `Fin 3` Hamiltonian tours, empty subgraph-tour face on a
  missing-edge `Fin 3` graph, and `p = 1` directed/undirected tour round-trip for `∅` vs `{0}`.
* `TSP`: explicit `Fin 69` (`2 ≤ r`), `Fin 276` (`3 ≤ r`), `Fin 621` (`4 ≤ r`), and
  `Fin 3 × Fin 23` (`2 ≤ r`) lower bounds.
-/

@[expose] public section

namespace Cslib.Foundations.Analysis.Convex.ExtensionComplexityLowerBoundsTests

open Cslib.Communication Cslib.Communication.Nondeterministic

/-! ### Unique disjointness -/

example : (disjointPairs (Finset.univ : Finset (Fin 1))).card = 3 := by
  rw [card_disjointPairs, Finset.card_univ, Fintype.card_fin]
  norm_num

example : IsValidDisjointSet (Finset.univ : Finset (Fin 1)) {(∅, ∅), ({0}, ∅)} := by
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> exact mem_disjointPairs.2 (by decide)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> decide

/-- A crossing pair with intersection cardinality `1` violates Kaibel–Weltge validity. -/
example : ¬ IsValidDisjointSet (Finset.univ : Finset (Fin 1)) {(∅, {0}), ({0}, ∅)} := by
  intro h
  exact h.2 ({0}, ∅) (by decide) (∅, {0}) (by decide) (by decide)

theorem udisj_fin2_cover_ge_three {r : ℕ}
    (hr : coverNumber true (uniqueDisjointnessRel (Fin 2)) Set.univ Set.univ ≤ r) :
    3 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Fintype.card (Fin 2) ≤ (r : ℚ) :=
    three_div_two_pow_le_of_coverNumber_uniqueDisjointnessRel_le hr
  rw [Fintype.card_fin] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (2 : ℚ) < (3 / 2) ^ 2) hq

example : (3 : ℕ∞) ≤ ecomplexity true (uniqueDisjointnessRel (Fin 4)) Set.univ Set.univ := by
  have h := clog_ceil_div_le_ecomplexity_uniqueDisjointnessRel (α := Fin 4)
  have hc : Nat.clog 2 ((3 ^ Fintype.card (Fin 4) + 2 ^ Fintype.card (Fin 4) - 1) /
      2 ^ Fintype.card (Fin 4)) = 3 := by decide
  simpa only [hc, Nat.cast_ofNat] using h

/-! ### Correlation polytope -/

example :
    corrValidVec ℚ ({0, 1} : Finset (Fin 2)) ⬝ᵥ corrVertex ℚ ({0, 1} : Finset (Fin 2)) = 0 := by
  rw [corrValidVec_dotProduct_corrVertex]
  have hc : (({0, 1} : Finset (Fin 2)) ∩ {0, 1}).card = 2 := by decide
  rw [hc]
  norm_num

/-- Vertices intersecting `a` in a single element saturate `corrValidVec ℚ a ⬝ᵥ x ≤ 1`. -/
example :
    corrValidVec ℚ ({0, 1} : Finset (Fin 2)) ⬝ᵥ corrVertex ℚ ({0} : Finset (Fin 2)) = 1 := by
  rw [corrValidVec_dotProduct_corrVertex]
  have hc : (({0, 1} : Finset (Fin 2)) ∩ {0}).card = 1 := by decide
  rw [hc]
  norm_num

example : (corrPolytope ℚ (Fin 2)).Nontrivial :=
  corrPolytope_nontrivial ℚ

theorem two_not_mem_corrPolytope :
    (2 : ℚ) • corrVertex ℚ ({0} : Finset (Fin 2)) ∉ corrPolytope ℚ (Fin 2) := by
  intro hx
  have hsub : corrPolytope ℚ (Fin 2) ⊆
      {y : Fin 2 × Fin 2 → ℚ | corrValidVec ℚ ({0} : Finset (Fin 2)) ⬝ᵥ y ≤ 1} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨b, rfl⟩
      simp only [Set.mem_ofPred_eq, corrValidVec_dotProduct_corrVertex]
      have hk : (({0} : Finset (Fin 2)) ∩ b).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton 0)
      interval_cases (({0} : Finset (Fin 2)) ∩ b).card <;> norm_num
    · intro y hy z hz a b ha hb _
      simp only [Set.mem_ofPred_eq, smul_eq_mul, dotProduct_add, dotProduct_smul] at hy hz ⊢
      nlinarith
  have hle : corrValidVec ℚ ({0} : Finset (Fin 2)) ⬝ᵥ
      ((2 : ℚ) • corrVertex ℚ ({0} : Finset (Fin 2))) ≤ 1 := hsub hx
  have hc : (({0} : Finset (Fin 2)) ∩ ({0} : Finset (Fin 2))).card = 1 := by decide
  have heval : corrValidVec ℚ ({0} : Finset (Fin 2)) ⬝ᵥ
      ((2 : ℚ) • corrVertex ℚ ({0} : Finset (Fin 2))) = 2 := by
    simp only [dotProduct_smul, smul_eq_mul, corrValidVec_dotProduct_corrVertex, hc, Nat.cast_one]
    norm_num
  linarith

theorem corr_fin3_ef_ge_four {r : ℕ}
    (hr : HasExtendedFormulation (corrPolytope ℚ (Fin 3)) r) : 4 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Fintype.card (Fin 3) ≤ r := hr.three_div_two_pow_le_of_corrPolytope
  rw [Fintype.card_fin] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (3 : ℚ) < (3 / 2) ^ 3) hq

/-! ### Cut polytope -/

example : extensionComplexity (cutPolytope ℚ (Option (Fin 3))) =
    extensionComplexity (corrPolytope ℚ (Fin 3)) :=
  extensionComplexity_cutPolytope_option_eq (Fin 3)

/-- `cutPolytope ℚ (Fin 1)` lies in a zero-dimensional space, so it is not nontrivial. -/
example : ¬ (cutPolytope ℚ (Fin 1)).Nontrivial := by
  rintro ⟨x, _, y, _, hne⟩
  apply hne
  ext ⟨s, hs⟩
  induction s using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hs
      exact False.elim (hs (Subsingleton.elim u v))

theorem cut_fin4_ef_ge_four {r : ℕ}
    (hr : HasExtendedFormulation (cutPolytope ℚ (Fin 4)) r) : 4 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ (Fintype.card (Fin 4) - 1) ≤ r :=
    hr.three_div_two_pow_le_of_cutPolytope (by decide)
  rw [Fintype.card_fin] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (3 : ℚ) < (3 / 2) ^ (4 - 1)) hq

/-! ### Stable set polytope -/

example : Fintype.card (CorrGadgetV 1) = 2 := by
  rw [card_corrGadgetV]
  norm_num

example : (3 : ℕ∞) ≤ extensionComplexity (stabPolytope ℚ (corrGadgetGraph 2)) := by
  have h1 : (3 : ℕ∞) ≤ extensionComplexity (corrPolytope ℚ (Fin 2)) := by
    have := ceil_three_div_two_pow_le_extensionComplexity_corrPolytope (K := ℚ) (α := Fin 2)
    rw [Fintype.card_fin] at this
    simpa only [Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Nat.cast_ofNat]
      using this
  exact h1.trans (extensionComplexity_corrPolytope_le_corrGadgetGraph 2)

private theorem sqrt_eq_of_sq_le {n s : ℕ} (h1 : s * s ≤ n) (h2 : n < (s + 1) ^ 2) :
    Nat.sqrt n = s :=
  le_antisymm (Nat.lt_succ_iff.1 (Nat.sqrt_lt'.2 h2)) (Nat.le_sqrt.2 h1)

theorem stab_fin8_ef_ge_three {r : ℕ}
    (hr : HasExtendedFormulation (stabPolytope ℚ (stabHardGraph 8)) r) : 3 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (8 / 2) ≤ r :=
    hr.three_div_two_pow_le_of_stabPolytope (by decide)
  rw [sqrt_eq_of_sq_le (n := 8 / 2) (s := 2) (by decide) (by decide)] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (2 : ℚ) < (3 / 2) ^ 2) hq

theorem stab_fin18_ef_ge_four {r : ℕ}
    (hr : HasExtendedFormulation (stabPolytope ℚ (stabHardGraph 18)) r) : 4 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (18 / 2) ≤ r :=
    hr.three_div_two_pow_le_of_stabPolytope (by decide)
  rw [sqrt_eq_of_sq_le (n := 18 / 2) (s := 3) (by decide) (by decide)] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (3 : ℚ) < (3 / 2) ^ 3) hq

/-! ### Tour splits and correlation digraphs -/

private def fin3IdEquiv : Fin (Fintype.card (Fin 3)) ≃ Fin 3 :=
  finCongr (Fintype.card_fin 3)

example : IsTourEdgeSet (tourEdgeSet fin3IdEquiv (by decide)) ∧
    ⟨s((0 : Fin 3), (1 : Fin 3)), by decide⟩ ∈ tourEdgeSet fin3IdEquiv (by decide) := by
  refine ⟨⟨by decide, fin3IdEquiv, rfl⟩, ?_⟩
  rw [tourEdgeSet, Finset.mem_image]
  exact ⟨⟨0, by rw [Fintype.card_fin]; omega⟩, Finset.mem_univ _, rfl⟩

private def path3Graph : SimpleGraph (Fin 3) where
  Adj i j := i ≠ j ∧ ¬ (i = 0 ∧ j = 2) ∧ ¬ (i = 2 ∧ j = 0)
  symm := ⟨fun _ _ ⟨hne, h1, h2⟩ =>
    ⟨hne.symm, fun h => h2 ⟨h.2, h.1⟩, fun h => h1 ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

private instance : DecidableRel path3Graph.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ ¬ (i = 0 ∧ j = 2) ∧ ¬ (i = 2 ∧ j = 0)))

/-- A `Fin 3` path missing edge `{0, 2}` has no Hamiltonian tour, so `tspPolytope_inter_subgraph_eq`
gives the empty face. -/
example :
    let c : ↥(⊤ : SimpleGraph (Fin 3)).edgeSet → ℚ :=
      fun e => if ↑e ∈ path3Graph.edgeSet then 0 else -1
    tspPolytope ℚ (Fin 3) ∩ {x | c ⬝ᵥ x = 0} = ∅ := by
  intro c
  rw [tspPolytope_inter_subgraph_eq (K := ℚ) path3Graph]
  have hempty :
      IsEmpty {F : Finset ↥(⊤ : SimpleGraph (Fin 3)).edgeSet // IsSubgraphTour path3Graph F} := by
    refine ⟨fun ⟨F, ⟨hV, σ, hF⟩, hsub⟩ => ?_⟩
    subst hF
    obtain ⟨i0, hi0⟩ := σ.surjective (0 : Fin 3)
    have hlt : i0.1 < 3 := by simpa only [Fintype.card_fin] using i0.isLt
    let step1 : Fin (Fintype.card (Fin 3)) := ⟨1, by rw [Fintype.card_fin]; omega⟩
    let j0 : Fin (Fintype.card (Fin 3)) := i0 + step1
    let k0 : Fin (Fintype.card (Fin 3)) := j0 + step1
    have hij : i0 ≠ j0 := fun h => by
      have hv : i0.1 = j0.1 := congrArg Fin.val h
      simp only [j0, step1, Fin.val_add, Fintype.card_fin] at hv
      omega
    have hik : i0 ≠ k0 := fun h => by
      have hv : i0.1 = k0.1 := congrArg Fin.val h
      simp only [k0, j0, step1, Fin.val_add, Fintype.card_fin] at hv
      omega
    have hjk : j0 ≠ k0 := fun h => by
      have hv : j0.1 = k0.1 := congrArg Fin.val h
      simp only [k0, j0, step1, Fin.val_add, Fintype.card_fin] at hv
      omega
    have h02 : σ j0 = 2 ∨ σ k0 = 2 := by
      have hne1 : (σ j0).1 ≠ 0 := fun h => hij (σ.injective (hi0.trans (Fin.ext h).symm))
      have hne2 : (σ k0).1 ≠ 0 := fun h => hik (σ.injective (hi0.trans (Fin.ext h).symm))
      have hne3 : (σ j0).1 ≠ (σ k0).1 := fun h => hjk (σ.injective (Fin.ext h))
      by_contra hnot
      have hj2 : (σ j0).1 ≠ 2 := fun h => hnot (Or.inl (Fin.ext h))
      have hk2 : (σ k0).1 ≠ 2 := fun h => hnot (Or.inr (Fin.ext h))
      have hjb := (σ j0).isLt
      have hkb := (σ k0).isLt
      omega
    have hmem : ⟨s(0, 2), by decide⟩ ∈ tourEdgeSet σ hV := by
      rw [tourEdgeSet, Finset.mem_image]
      rcases h02 with hj | hk
      · refine ⟨i0, Finset.mem_univ _, Subtype.ext ?_⟩
        dsimp only
        have hj' : i0 + ⟨1, by rw [Fintype.card_fin]; omega⟩ = j0 := rfl
        rw [hi0, hj', hj]
      · refine ⟨k0, Finset.mem_univ _, Subtype.ext ?_⟩
        dsimp only
        have hk' : k0 + ⟨1, by rw [Fintype.card_fin]; omega⟩ = i0 := Fin.ext (by
          simp only [k0, j0, step1, Fin.val_add, Fintype.card_fin]
          omega)
        rw [hk', hi0, hk, Sym2.eq_swap]
    have hadj := hsub ⟨s(0, 2), by decide⟩ hmem
    simp only [path3Graph, SimpleGraph.mem_edgeSet] at hadj
    exact hadj.2.1 (by decide)
  rw [Set.range_eq_empty, convexHull_empty]

example : 3 ≤ Fintype.card (CorrDigraphV 1) ∧ Fintype.card (CorrDigraphV 1) ≤ 23 :=
  ⟨three_le_card_corrDigraphV (by decide), by
    simpa only [one_pow, mul_one] using card_corrDigraphV_le (p := 1) (by decide)⟩

/-- For `p = 1`, `{0}` lifts to an undirected tour of `paddedSplitGraph` whose inter-gadget
edge recovers `0 ∈ b`, while `∅` lifts to a tour with no reverse diagonal edge. -/
example :
    let v₀ : CorrDigraphV 1 := .gate (.diag ⟨0, by decide⟩)
    let c1 : CorrDigraphV 1 := .chain (.diag 0) ⟨1, by
      have := two_le_chainLen (by decide : 1 ≤ 1) (.diag 0); omega⟩
    let c0 : CorrDigraphV 1 := .chain (.diag 0) ⟨0, by
      have := two_le_chainLen (by decide : 1 ≤ 1) (.diag 0); omega⟩
    (∃ F, IsSubgraphTour (paddedSplitGraph v₀ 0 (corrDigraphAdj 1 (by decide))) F ∧
      ⟨s(SplitV.vOut c1, SplitV.vIn c0), splitV_top_edge_vOut_vIn v₀ 0 c1 c0⟩ ∈ F) ∧
    (∃ F, IsSubgraphTour (paddedSplitGraph v₀ 0 (corrDigraphAdj 1 (by decide))) F ∧
      ⟨s(SplitV.vOut c1, SplitV.vIn c0), splitV_top_edge_vOut_vIn v₀ 0 c1 c0⟩ ∉ F) := by
  intro v₀ c1 c0
  have hp : 1 ≤ 1 := by decide
  have h2 : 2 ≤ Fintype.card (CorrDigraphV 1) := two_le_card_corrDigraphV hp
  constructor
  · obtain ⟨τ, hτ, hdiag, _⟩ := exists_dirTour_of_assignment (p := 1) hp ({0} : Finset (Fin 1))
    obtain ⟨F, hF, hinter⟩ := paddedSplitTour_of_dirTour v₀ 0 (corrDigraphAdj 1 hp) h2 τ hτ
    refine ⟨F, hF, (hinter c1 c0).2 ?_⟩
    exact (hdiag 0).2 (Finset.mem_singleton_self 0)
  · obtain ⟨τ, hτ, hdiag, _⟩ := exists_dirTour_of_assignment (p := 1) hp ∅
    obtain ⟨F, hF, hinter⟩ := paddedSplitTour_of_dirTour v₀ 0 (corrDigraphAdj 1 hp) h2 τ hτ
    refine ⟨F, hF, fun hmem => ?_⟩
    have hmem' := (hinter c1 c0).1 hmem
    have h0 := (hdiag 0).1 hmem'
    simp only [Finset.notMem_empty] at h0

/-! ### TSP polytope lower bounds -/

theorem tsp_fin69_ef_ge_two {r : ℕ}
    (hr : HasExtendedFormulation (tspPolytope ℚ (Fin 69)) r) : 2 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (69 / 69) ≤ r := hr.three_div_two_pow_le_of_tspPolytope_fin
    (by decide)
  rw [show Nat.sqrt (69 / 69) = 1 by decide] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℚ) < (3 / 2) ^ 1) hq

theorem tsp_fin276_ef_ge_three {r : ℕ}
    (hr : HasExtendedFormulation (tspPolytope ℚ (Fin 276)) r) : 3 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (276 / 69) ≤ r := hr.three_div_two_pow_le_of_tspPolytope_fin
    (by decide)
  rw [sqrt_eq_of_sq_le (n := 276 / 69) (s := 2) (by decide) (by decide)] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (2 : ℚ) < (3 / 2) ^ 2) hq

theorem tsp_fin621_ef_ge_four {r : ℕ}
    (hr : HasExtendedFormulation (tspPolytope ℚ (Fin 621)) r) : 4 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (621 / 69) ≤ r := hr.three_div_two_pow_le_of_tspPolytope_fin
    (by decide)
  rw [sqrt_eq_of_sq_le (n := 621 / 69) (s := 3) (by decide) (by decide)] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (3 : ℚ) < (3 / 2) ^ 3) hq

theorem tsp_prod_ef_ge_two {r : ℕ}
    (hr : HasExtendedFormulation (tspPolytope ℚ (Fin 3 × Fin 23)) r) : 2 ≤ r := by
  have hq : (3 / 2 : ℚ) ^ Nat.sqrt (Fintype.card (Fin 3 × Fin 23) / 69) ≤ r :=
    hr.three_div_two_pow_le_of_tspPolytope (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin])
  rw [show Nat.sqrt (Fintype.card (Fin 3 × Fin 23) / 69) = 1 by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; decide] at hq
  exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℚ) < (3 / 2) ^ 1) hq

example : (3 : ℕ∞) ≤ extensionComplexity (tspPolytope ℚ (Fin 276)) := by
  have h := ceil_three_div_two_pow_le_extensionComplexity_tspPolytope (K := ℚ) (Fin 276)
    (by rw [Fintype.card_fin]; decide)
  have hc : (3 ^ Nat.sqrt (Fintype.card (Fin 276) / 69) +
      2 ^ Nat.sqrt (Fintype.card (Fin 276) / 69) - 1) /
      2 ^ Nat.sqrt (Fintype.card (Fin 276) / 69) = 3 := by
    rw [Fintype.card_fin, sqrt_eq_of_sq_le (n := 276 / 69) (s := 2) (by decide) (by decide)]
    decide
  simpa only [hc, Nat.cast_ofNat] using h

example :
    let _ : DecidableRel (tspHardGraph 276).Adj := Classical.decRel _
    let c : ↥(⊤ : SimpleGraph (Fin 276)).edgeSet → ℚ :=
      fun e => if e.1 ∈ (tspHardGraph 276).edgeSet then 0 else -1
    (3 : ℕ∞) ≤ extensionComplexity (tspPolytope ℚ (Fin 276) ∩ {x | c ⬝ᵥ x = 0}) := by
  classical
  intro c
  have : Nonempty (Fin (Nat.sqrt (276 / 69))) := ⟨⟨0, Nat.sqrt_pos.2 (by decide)⟩⟩
  have h1 : (3 : ℕ∞) ≤ extensionComplexity (corrPolytope ℚ (Fin (Nat.sqrt (276 / 69)))) := by
    have hc : (3 ^ Nat.sqrt (276 / 69) + 2 ^ Nat.sqrt (276 / 69) - 1) /
        2 ^ Nat.sqrt (276 / 69) = 3 := by
      rw [sqrt_eq_of_sq_le (n := 276 / 69) (s := 2) (by decide) (by decide)]
      decide
    simpa only [Fintype.card_fin, hc, Nat.cast_ofNat] using
      ceil_three_div_two_pow_le_extensionComplexity_corrPolytope
        (K := ℚ) (α := Fin (Nat.sqrt (276 / 69)))
  exact h1.trans (extensionComplexity_corrPolytope_le_tspHardGraph_face (K := ℚ) 276 (by decide))

end Cslib.Foundations.Analysis.Convex.ExtensionComplexityLowerBoundsTests
