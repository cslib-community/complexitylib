/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Bipartite
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Cycle
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Tree
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Cycle
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Tree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Schummer–Vohra facility-location characterization: checked clients and separations

Nonvacuous instantiations and counterexamples for:
1. `Cslib.GameTheory.FacilityLocation` on intervals (`MoulinScheme`), including concrete `[0, 1]`
   evaluation and a constant mechanism failing surjectivity.
2. `Cslib.GameTheory.FacilityLocation` on trees (`TreeEMVS`), exhibiting a concrete
   majority-based non-dictatorial group-strategyproof surjective rule on a 3-star `star3`.
3. `Cslib.GameTheory.FacilityLocation` on cycles: global dictatorship on `cycleGraph 3`, and a
   `Triangle + Tail` (`Fin 4`) group-strategyproof onto mechanism that acts as dictator `0` on
   the shortest cycle `0-1-2` without being a global dictatorship.
-/

set_option linter.privateModule false
namespace CslibFrontierTests.SchummerVohra

open SimpleGraph SimpleGraph.MetricGraph Cslib.GameTheory Cslib.GameTheory.FacilityLocation

noncomputable local instance {V : Type*} (W : WeightedGraph V) [Finite V] :
    MeasurableSpace (MetricGraph W) := borel _

local instance {V : Type*} (W : WeightedGraph V) [Finite V] :
    BorelSpace (MetricGraph W) := ⟨rfl⟩

/-! ### 1. Interval characterization and non-onto counterexample -/

section IntervalClients

private noncomputable def halfIcc : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Symmetric 3-agent generalized median scheme on `[0, 1]` with interior phantom `1/2`. -/
private noncomputable def symMedianScheme : MoulinScheme (Fin 3) 0 1 where
  alpha S := if S = Finset.univ then 0 else if S = ∅ then 1 else 1 / 2
  mem_Icc S := by split_ifs <;> constructor <;> norm_num
  antitone S T hST := by
    by_cases hT : T = Finset.univ
    · subst hT; simp only [ite_true]; split_ifs <;> norm_num
    · by_cases hS : S = ∅
      · subst hS
        have hne : (∅ : Finset (Fin 3)) ≠ Finset.univ := by decide
        simp only [hne, ↓reduceIte]; split_ifs <;> norm_num
      · have hSn : S ≠ Finset.univ := fun h => hT (Finset.eq_univ_iff_forall.mpr
          fun x => hST (h ▸ Finset.mem_univ x))
        have hTn : T ≠ ∅ := fun h => hS (Finset.subset_empty.mp (h ▸ hST))
        simp only [hT, hS, hSn, hTn, ↓reduceIte, le_rfl]
  boundary_empty := by
    have hne : (∅ : Finset (Fin 3)) ≠ Finset.univ := by decide
    simp only [hne, ↓reduceIte]
  boundary_univ := by simp only [↓reduceIte]

example :
    (Mechanism.deterministic symMedianScheme.eval).IsGroupStrategyProof ∧
    (Mechanism.deterministic symMedianScheme.eval).IsStrategyProof ∧
    Function.Surjective symMedianScheme.eval ∧
    (∃ E : MoulinScheme (Fin 3) 0 1, symMedianScheme.eval = E.eval) :=
  ⟨symMedianScheme.eval_isGroupStrategyProof, symMedianScheme.eval_isStrategyProof,
    symMedianScheme.eval_surjective,
    (isStrategyProof_and_surjective_iff_exists_moulinScheme (by norm_num) _).mp
      ⟨symMedianScheme.eval_isStrategyProof, symMedianScheme.eval_surjective⟩⟩

example :
    symMedianScheme.eval ![⟨0, by norm_num, by norm_num⟩,
      ⟨1 / 4, by norm_num, by norm_num⟩, ⟨3 / 4, by norm_num, by norm_num⟩] = halfIcc := by
  let x : Fin 3 → Set.Icc (0 : ℝ) 1 :=
    ![⟨0, by norm_num, by norm_num⟩, ⟨1 / 4, by norm_num, by norm_num⟩,
      ⟨3 / 4, by norm_num, by norm_num⟩]
  ext
  refine le_antisymm ?_ ?_
  · rw [← not_lt, symMedianScheme.lt_eval_iff x halfIcc]
    have hS : (Finset.univ.filter fun i : Fin 3 => (x i : ℝ) ≤ halfIcc) = {0, 1} := by
      ext i; fin_cases i <;> simp [x, halfIcc] <;> norm_num
    rw [hS]
    have h1 : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := by decide
    have h2 : ({0, 1} : Finset (Fin 3)) ≠ ∅ := by decide
    simp [symMedianScheme, halfIcc, h1, h2]
  · rw [← not_lt, symMedianScheme.eval_lt_iff x halfIcc]
    have hS : (Finset.univ.filter fun i : Fin 3 => (x i : ℝ) < halfIcc) = {0, 1} := by
      ext i; fin_cases i <;> simp [x, halfIcc] <;> norm_num
    rw [hS]
    have h1 : ({0, 1} : Finset (Fin 3)) ≠ Finset.univ := by decide
    have h2 : ({0, 1} : Finset (Fin 3)) ≠ ∅ := by decide
    simp [symMedianScheme, halfIcc, h1, h2]

/-- A constant rule on `[0, 1]` is group strategyproof yet fails surjectivity, so it cannot be
represented by any `MoulinScheme`. -/
example :
    let f : (Fin 2 → Set.Icc (0 : ℝ) 1) → Set.Icc (0 : ℝ) 1 := fun _ => halfIcc
    (Mechanism.deterministic f).IsGroupStrategyProof ∧
    ¬ Function.Surjective f ∧
    ¬ ∃ E : MoulinScheme (Fin 2) 0 1, f = E.eval := by
  intro f
  refine ⟨?_, ?_, ?_⟩
  · rw [Mechanism.isGroupStrategyProof_deterministic_iff]
    rintro x z A ⟨_, i, _, hlt⟩
    exact absurd hlt (lt_irrefl _)
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj ⟨0, by norm_num, by norm_num⟩
    have hval : (1 / 2 : ℝ) = 0 := congrArg Subtype.val hx
    norm_num at hval
  · rintro ⟨E, hE⟩
    obtain ⟨x, hx⟩ := E.eval_surjective ⟨0, by norm_num, by norm_num⟩
    have hcon := congrFun hE x
    rw [hx] at hcon
    have hval : (1 / 2 : ℝ) = 0 := congrArg Subtype.val hcon
    norm_num at hval

end IntervalClients

/-! ### 2. Tree characterization: non-dictatorial 3-star majority EMVS -/

section TreeClients

private def star3Graph : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl, hne⟩ | ⟨rfl, hne⟩ <;> exact hne rfl⟩

private theorem star3Graph_connected : star3Graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; exact Reachable.refl 0
  · exact Adj.reachable (Or.inl ⟨rfl, hv⟩)

private theorem star3Graph_isAcyclic : star3Graph.IsAcyclic := by
  intro v₀ c hc
  have hlen := hc.three_le_length
  have hnd := hc.support_nodup
  cases c with
  | nil => simp at hlen
  | @cons _ b _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ w _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 q =>
        rw [Walk.support_cons, List.tail_cons, Walk.support_cons, List.nodup_cons] at hnd
        rcases h1 with ⟨rfl, hb⟩ | ⟨rfl, hv⟩
        · rcases h2 with ⟨hbw, _⟩ | ⟨rfl, _⟩
          · exact absurd hbw hb
          · rw [Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.2.1 (Walk.end_mem_support q)
        · rcases h2 with ⟨_, hw⟩ | ⟨_, hne0⟩
          · rcases h3 with ⟨hwz, _⟩ | ⟨rfl, _⟩
            · exact absurd hwz hw
            · exact hnd.1 (List.mem_cons_of_mem w (Walk.start_mem_support q))
          · exact absurd rfl hne0

private noncomputable def star3 : WeightedGraph (Fin 4) :=
  equalLength star3Graph star3Graph_connected 1 one_pos

private theorem star3_isTree : star3.graph.IsTree :=
  ⟨star3Graph_connected, star3Graph_isAcyclic⟩

/-- Coalition-size `≥ 2` (`2`-of-`3` majority) on the 3-star `star3`, yielding a non-dictatorial
group-strategyproof surjective `TreeEMVS`. -/
private noncomputable def majorityStar3 : TreeEMVS star3 (Fin 3) where
  win _ _ S := 2 ≤ S.card
  branch_eq _ _ _ := rfl
  empty_false _ h := by simp at h
  univ_true _ := by decide
  mono _ hST hS := hS.trans (Finset.card_le_card hST)
  nesting _ _ _ hS := hS
  duality _ hS := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  exclusive _ _ _ h := by
    have h2 := h.2
    rw [Finset.card_compl, Fintype.card_fin] at h2
    omega
  open_interior {y q S} hqy hS := by
    obtain ⟨γ, hγ⟩ := exists_isGeodesic y q
    let m : ℝ := dist y q / 2
    have hdp : 0 < dist y q := dist_pos.mpr hqy.symm
    have hm_mem : m ∈ Set.Icc 0 (dist y q) := ⟨by positivity, by dsimp only [m]; linarith [hdp]⟩
    have h0_mem : (0 : ℝ) ∈ Set.Icc 0 (dist y q) := ⟨le_rfl, dist_nonneg⟩
    have hd_mem : dist y q ∈ Set.Icc 0 (dist y q) := ⟨dist_nonneg, le_rfl⟩
    have hdy : dist y (γ m) = m := by
      rw [← hγ.map_zero, hγ.dist_eq h0_mem hm_mem, zero_sub, abs_neg,
        abs_of_nonneg (by positivity)]
    have hdq : dist (γ m) q = m := by
      rw [← hγ.map_dist, hγ.dist_eq hm_mem hd_mem, abs_sub_comm,
        abs_of_nonneg (by dsimp only [m]; linarith)]
      dsimp only [m]; ring
    have hmem : γ m ∈ interval y q := by
      rw [mem_interval_iff, hdy, hdq]
      dsimp only [m]; ring
    exact ⟨γ m, hmem, fun h => by rw [h, _root_.dist_self] at hdy; dsimp only [m] at hdy; linarith,
      fun h => by rw [h, _root_.dist_self] at hdq; dsimp only [m] at hdq; linarith, hS⟩

private theorem star3_leaf_dist_center {v : Fin 4} (hv : v ≠ 0) :
    dist (vertex 0 : MetricGraph star3) (vertex v) = 1 := by
  rw [dist_vertex, vertexDist_adj star3_isTree (Or.inl ⟨rfl, hv⟩)]
  rfl

private theorem star3_leaf_dist_leaf {u v : Fin 4} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    dist (vertex u : MetricGraph star3) (vertex v) = 2 := by
  rw [dist_vertex]
  refine le_antisymm ?_ ?_
  · have h1 := vertexDist_triangle star3.weight_nonneg (star3.connected u 0) (star3.connected 0 v)
    rw [vertexDist_adj star3_isTree (Or.inr ⟨rfl, hu⟩),
      vertexDist_adj star3_isTree (Or.inl ⟨rfl, hv⟩)] at h1
    exact h1.trans_eq (by change (1 : ℝ) + 1 = 2; norm_num)
  · obtain ⟨p, -, hp⟩ :=
      SimpleGraph.exists_isPath_walkLength_eq_vertexDist star3.weight_nonneg
        (star3.connected u v)
    rw [← hp]
    cases p with
    | nil => exact absurd rfl huv
    | @cons _ b _ hadj q =>
      rw [walkLength_cons]
      have hw : star3.weight s(u, b) = 1 := rfl
      have hb0 : b = 0 := by
        rcases hadj with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact absurd rfl hu
        · rfl
      subst hb0
      cases q with
      | nil => exact absurd rfl hv
      | @cons _ w _ hadj2 q2 =>
        rw [walkLength_cons]
        have hw2 : star3.weight s(0, w) = 1 := rfl
        have hq2 := walkLength_nonneg star3.weight star3.weight_nonneg q2
        linarith

example :
    (Mechanism.deterministic (majorityStar3.eval star3_isTree)).IsGroupStrategyProof ∧
    Function.Surjective (majorityStar3.eval star3_isTree) ∧
    majorityStar3.eval star3_isTree ![vertex 1, vertex 2, vertex 3] = vertex 0 ∧
    (¬ ∃ i₀ : Fin 3, ∀ x, majorityStar3.eval star3_isTree x = x i₀) ∧
    (∃ E : TreeEMVS star3 (Fin 3), majorityStar3.eval star3_isTree = E.eval star3_isTree) := by
  let f := majorityStar3.eval star3_isTree
  have hf_eval : f ![vertex 1, vertex 2, vertex 3] = vertex 0 := by
    rw [TreeEMVS.eval_eq_iff star3_isTree]
    intro q hq S hS hcard
    have hcard2 : 2 ≤ S.card := hcard
    obtain ⟨i, hiS, j, hjS, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    let x : Fin 3 → MetricGraph star3 := ![vertex 1, vertex 2, vertex 3]
    have hxi : x i ∈ branch (vertex 0) q := (hS i).mp hiS
    have hxj : x j ∈ branch (vertex 0) q := (hS j).mp hjS
    have hx_idx (a : Fin 3) : ∃ v : Fin 4, v ≠ 0 ∧ x a = vertex v := by
      fin_cases a
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
    have hx_inj : Function.Injective x := by
      intro a b h
      fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (vertex_inj.ne.mpr (by decide))
    have hx_dist : ∀ a b : Fin 3, a ≠ b →
        (vertex 0 : MetricGraph star3) ∈ interval (x a) (x b) := by
      intro a b hab
      obtain ⟨va, hva, hxa⟩ := hx_idx a
      obtain ⟨vb, hvb, hxb⟩ := hx_idx b
      have hvab : va ≠ vb := fun h => hab (hx_inj (hxa.trans (h ▸ hxb.symm)))
      rw [mem_interval_iff, hxa, hxb, _root_.dist_comm (vertex va) (vertex 0),
        star3_leaf_dist_center hva, star3_leaf_dist_center hvb, star3_leaf_dist_leaf hva hvb hvab]
      norm_num
    have hdisj := branch_disjoint_of_mem_interval star3_isTree (hx_dist i j hij)
    have hbi := branch_eq_of_mem star3_isTree hxi
    have hbj := branch_eq_of_mem star3_isTree hxj
    have hne_i : x i ≠ vertex 0 := by
      fin_cases i <;> simp [x, vertex_inj]
    exact Set.disjoint_left.mp hdisj (mem_branch_self hne_i)
      (hbj ▸ hbi ▸ mem_branch_self hne_i)
  refine ⟨majorityStar3.eval_isGroupStrategyProof star3_isTree,
    majorityStar3.eval_surjective star3_isTree, hf_eval, ?_, ⟨majorityStar3, rfl⟩⟩
  rintro ⟨i₀, hi₀⟩
  have h := (hi₀ ![vertex 1, vertex 2, vertex 3]).symm.trans hf_eval
  fin_cases i₀ <;> simp [vertex_inj] at h

/-- Every strategyproof surjective rule on `star3` is automatically group strategyproof and
represented by a `TreeEMVS`. -/
example {f : (Fin 3 → MetricGraph star3) → MetricGraph star3}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    (Mechanism.deterministic f).IsGroupStrategyProof ∧
    ∃ E : TreeEMVS star3 (Fin 3), f = E.eval star3_isTree :=
  ⟨isGroupStrategyProof_of_isStrategyProof_of_surjective_tree star3_isTree hf_sp hf_onto,
    (isStrategyProof_and_surjective_iff_exists_treeEMVS star3_isTree f).mp ⟨hf_sp, hf_onto⟩⟩

end TreeClients

/-! ### 3. Cycle dictatorship and Triangle + Tail counterexample -/

section CycleClients

private noncomputable def triGraph : WeightedGraph (Fin 3) :=
  equalLength (SimpleGraph.cycleGraph 3) SimpleGraph.connected_cycleGraph_add_one 1 one_pos

/-- On `cycleGraph 3`, any deterministic strategyproof surjective mechanism (for instance,
player `1`'s dictatorship) is globally dictatorial. -/
example :
    let f : (Fin 3 → MetricGraph triGraph) → MetricGraph triGraph := fun x => x 1
    (Mechanism.deterministic f).IsStrategyProof ∧
    Function.Surjective f ∧
    ∃ i₀ : Fin 3, ∀ x, f x = x i₀ := by
  intro f
  have hsp : (Mechanism.deterministic f).IsStrategyProof :=
    (dictatorship_isGroupStrategyProof (ι := Fin 3) (G := MetricGraph triGraph) 1).isStrategyProof
  have honto : Function.Surjective f := fun y => ⟨fun _ => y, rfl⟩
  exact ⟨hsp, honto, exists_dictatorship_of_cycleGraph triGraph (RelIso.refl _) hsp honto⟩

private def triTailGraph : SimpleGraph (Fin 4) where
  Adj u v :=
    s(u, v) = s(0, 1) ∨ s(u, v) = s(1, 2) ∨ s(u, v) = s(2, 0) ∨ s(u, v) = s(2, 3)
  symm := ⟨fun _ _ h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun u h => by fin_cases u <;> simp at h⟩

private instance : DecidableRel triTailGraph.Adj := fun u v =>
  inferInstanceAs (Decidable
    (s(u, v) = s(0, 1) ∨ s(u, v) = s(1, 2) ∨ s(u, v) = s(2, 0) ∨ s(u, v) = s(2, 3)))

private theorem triTailGraph_connected : triTailGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact Reachable.refl 0
  · exact Adj.reachable (by decide)
  · exact Adj.reachable (by decide)
  · exact (Adj.reachable (by decide : triTailGraph.Adj 0 2)).trans
      (Adj.reachable (by decide : triTailGraph.Adj 2 3))

private noncomputable def triTail : WeightedGraph (Fin 4) :=
  equalLength triTailGraph triTailGraph_connected 1 one_pos

private def triCycle : triTail.graph.Walk 0 0 :=
  Walk.cons (by decide : triTailGraph.Adj 0 1)
    (Walk.cons (by decide : triTailGraph.Adj 1 2)
      (Walk.cons (by decide : triTailGraph.Adj 2 0) .nil))

private theorem triTail_walkLength_eq {u v : Fin 4} (p : triTail.graph.Walk u v) :
    walkLength triTail.weight p = p.length := by
  induction p with
  | nil => simp [walkLength_nil]
  | cons _ q ih =>
    rw [walkLength_cons, Walk.length_cons, ih]
    change (1 : ℝ) + (q.length : ℝ) = ((q.length + 1 : ℕ) : ℝ)
    push_cast; ring

private theorem triCycle_isShortestCycle : IsShortestCycle triTail triCycle := by
  refine ⟨?_, ?_⟩
  · rw [Walk.isCycle_def]
    refine ⟨?_, by decide, by decide⟩
    rw [Walk.isTrail_def]
    decide
  · intro u c' hc'
    rw [triTail_walkLength_eq, triTail_walkLength_eq]
    exact_mod_cast (show triCycle.length ≤ c'.length from hc'.three_le_length)

private def dart23 : triTail.graph.Dart := ⟨(2, 3), show triTailGraph.Adj 2 3 by decide⟩

private theorem triTail_adj_three {u : Fin 4} (h : triTailGraph.Adj 3 u) : u = 2 := by
  revert u h; decide

private theorem triTail_vertexDist_three_of_ne {u : Fin 4} (hu : u ≠ 3) :
    SimpleGraph.vertexDist triTail.graph triTail.weight u 3 =
      SimpleGraph.vertexDist triTail.graph triTail.weight u 2 + 1 := by
  refine le_antisymm ?_ ?_
  · have h := vertexDist_triangle triTail.weight_nonneg (triTail.connected u 2)
      (triTail.connected 2 3)
    have h23 : SimpleGraph.vertexDist triTail.graph triTail.weight 2 3 ≤ 1 := by
      refine (vertexDist_le triTail.weight_nonneg
        (Adj.toWalk (by decide : triTailGraph.Adj 2 3))).trans_eq ?_
      change walkLength triTail.weight (Walk.cons (by decide : triTailGraph.Adj 2 3) .nil) = 1
      rw [walkLength_cons, walkLength_nil, add_zero]; rfl
    linarith
  · obtain ⟨p, -, hp⟩ :=
      SimpleGraph.exists_isPath_walkLength_eq_vertexDist triTail.weight_nonneg
        (triTail.connected u 3)
    rw [← hp, ← walkLength_reverse triTail.weight p]
    cases hpr : p.reverse with
    | nil => exact absurd rfl hu.symm
    | @cons _ w _ hadj q =>
      have hw : w = 2 := triTail_adj_three hadj
      subst hw
      rw [walkLength_cons]
      have hwe : triTail.weight s(3, 2) = 1 := rfl
      have hq := vertexDist_le triTail.weight_nonneg q
      rw [vertexDist_comm] at hq
      linarith

private noncomputable def tailPos : MetricGraph triTail → unitInterval :=
  MetricGraph.lift
    (fun v => if v = 3 then 1 else 0)
    (fun d t => if d.edge = dart23.edge then (if d = dart23 then t else unitInterval.symm t) else 0)
    (fun d => by
      by_cases he : d.edge = dart23.edge
      · rcases (dart_edge_eq_iff d dart23).mp he with rfl | rfl
        · simp [dart23]
        · simp only [Dart.edge_symm, dart23.symm_ne, ↓reduceIte]
          simp [dart23]
      · have hne : d.toProd.1 ≠ 3 := fun h => by
          have hsnd := triTail_adj_three (h ▸ d.adj)
          exact he (by
            change s(d.toProd.1, d.toProd.2) = s(2, 3)
            rw [h, hsnd, Sym2.eq_swap])
        simp [he, hne])
    (fun d => by
      by_cases he : d.edge = dart23.edge
      · rcases (dart_edge_eq_iff d dart23).mp he with rfl | rfl
        · simp [dart23]
        · simp only [Dart.edge_symm, dart23.symm_ne, ↓reduceIte]
          simp [dart23]
      · have hne : d.toProd.2 ≠ 3 := fun h => by
          have hfst := triTail_adj_three (h ▸ d.adj.symm)
          exact he (by
            change s(d.toProd.1, d.toProd.2) = s(2, 3)
            rw [h, hfst])
        simp [he, hne])
    (fun d t => by
      by_cases he : d.edge = dart23.edge
      · rcases (dart_edge_eq_iff d dart23).mp he with rfl | rfl
        · simp [Dart.edge_symm, dart23.symm_ne]
        · simp [Dart.edge_symm, Dart.symm_symm, dart23.symm_ne]
      · simp [he])

private lemma tailPos_vertex_three : tailPos (vertex 3 : MetricGraph triTail) = 1 := by
  simp [tailPos, MetricGraph.lift_vertex]

private lemma tailPos_vertex_ne {v : Fin 4} (hv : v ≠ 3) :
    tailPos (vertex v : MetricGraph triTail) = 0 := by
  simp [tailPos, MetricGraph.lift_vertex, hv]

private lemma tailPos_dart23 (t : unitInterval) :
    tailPos (edgePoint dart23 t : MetricGraph triTail) = t := by
  simp [tailPos, MetricGraph.lift_edgePoint]

private noncomputable def tailScheme2 : MoulinScheme (Fin 2) 0 1 where
  alpha S := if (0 : Fin 2) ∈ S then 0 else if (1 : Fin 2) ∈ S then 1 / 2 else 1
  mem_Icc S := by split_ifs <;> constructor <;> norm_num
  antitone S T hST := by
    by_cases h0S : (0 : Fin 2) ∈ S
    · have h0T : (0 : Fin 2) ∈ T := hST h0S
      simp [h0S, h0T]
    · by_cases h1S : (1 : Fin 2) ∈ S
      · have h1T : (1 : Fin 2) ∈ T := hST h1S
        simp only [h0S, h1S, h1T, ↓reduceIte]
        split_ifs <;> norm_num
      · simp only [h0S, h1S, ↓reduceIte]
        split_ifs <;> norm_num
  boundary_empty := by simp
  boundary_univ := by simp

private def inTail (p : MetricGraph triTail) : Prop :=
  ∃ t : unitInterval, p = edgePoint dart23 t

open Classical in
private noncomputable def triTailMech (x : Fin 2 → MetricGraph triTail) : MetricGraph triTail :=
  if inTail (x 0) then edgePoint dart23 (tailScheme2.eval fun i => tailPos (x i)) else x 0

private lemma dist_not_inTail_edgePoint (p : MetricGraph triTail) (hp : ¬ inTail p)
    (τ : unitInterval) :
    dist p (edgePoint dart23 τ) = dist p (vertex 2) + (τ : ℝ) ∧ 0 < dist p (vertex 2) := by
  revert hp
  induction p using MetricGraph.ind with
  | vertex u =>
    intro hu
    have hu2 : u ≠ 2 := fun h => hu ⟨0, h ▸ (edgePoint_zero dart23).symm⟩
    have hu3 : u ≠ 3 := fun h => hu ⟨1, h ▸ (edgePoint_one dart23).symm⟩
    have hvd : SimpleGraph.vertexDist triTail.graph triTail.weight u 3 =
        SimpleGraph.vertexDist triTail.graph triTail.weight u 2 + 1 :=
      triTail_vertexDist_three_of_ne hu3
    refine ⟨?_, dist_pos.mpr (vertex_inj.ne.mpr hu2)⟩
    rw [dist_vertex_edgePoint, dist_vertex]
    change min (SimpleGraph.vertexDist triTail.graph triTail.weight u 2 + (τ : ℝ) * 1)
        (SimpleGraph.vertexDist triTail.graph triTail.weight u 3 + (1 - (τ : ℝ)) * 1) =
      SimpleGraph.vertexDist triTail.graph triTail.weight u 2 + (τ : ℝ)
    rw [hvd, mul_one, mul_one]
    exact min_eq_left (by linarith [τ.2.2])
  | edgePoint d t ht0 ht1 =>
    intro hnp
    have hne : d.edge ≠ dart23.edge := by
      intro he
      rcases (dart_edge_eq_iff d dart23).mp he with rfl | rfl
      · exact hnp ⟨t, rfl⟩
      · exact hnp ⟨unitInterval.symm t, by rw [← edgePoint_symm dart23 (unitInterval.symm t),
          unitInterval.symm_symm]⟩
    have h3f : d.fst ≠ 3 := fun h => by
      have hs := triTail_adj_three (h ▸ d.adj)
      exact hne (by change s(d.toProd.1, d.toProd.2) = s(2, 3); rw [h, hs, Sym2.eq_swap])
    have h3s : d.snd ≠ 3 := fun h => by
      have hs := triTail_adj_three (h ▸ d.adj.symm)
      exact hne (by change s(d.toProd.1, d.toProd.2) = s(2, 3); rw [h, hs])
    have hvd1 := triTail_vertexDist_three_of_ne h3f
    have hvd2 := triTail_vertexDist_three_of_ne h3s
    have hpos_d : 0 < dist (edgePoint d t : MetricGraph triTail) (vertex 2) := by
      rw [dist_pos]
      intro h
      rw [edgePoint_eq_vertex_iff] at h
      rcases h with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact ht0.ne' (congrArg Subtype.val ht)
      · exact ht1.ne (congrArg Subtype.val ht)
    refine ⟨?_, hpos_d⟩
    rw [dist_edgePoint_edgePoint_of_edge_ne hne, dist_edgePoint_vertex]
    have hw_d : triTail.weight d.edge = 1 := rfl
    have hw_23 : triTail.weight dart23.edge = 1 := rfl
    change min
        (min ((t : ℝ) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 2 +
            (τ : ℝ) * 1)
          ((t : ℝ) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 3 +
            (1 - (τ : ℝ)) * 1))
        (min ((1 - (t : ℝ)) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 2 +
            (τ : ℝ) * 1)
          ((1 - (t : ℝ)) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 3 +
            (1 - (τ : ℝ)) * 1)) =
      min ((t : ℝ) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 2)
        ((1 - (t : ℝ)) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 2) +
        (τ : ℝ)
    rw [hvd1, hvd2]
    have h1 : (t : ℝ) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 2 +
        (τ : ℝ) * 1 ≤ (t : ℝ) * 1 +
          (SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 2 + 1) +
          (1 - (τ : ℝ)) * 1 := by linarith [τ.2.2]
    have h2 : (1 - (t : ℝ)) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 2 +
        (τ : ℝ) * 1 ≤ (1 - (t : ℝ)) * 1 +
          (SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 2 + 1) +
          (1 - (τ : ℝ)) * 1 := by linarith [τ.2.2]
    rw [min_eq_left h1, min_eq_left h2]
    rcases le_total
        ((t : ℝ) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.fst 2)
        ((1 - (t : ℝ)) * 1 + SimpleGraph.vertexDist triTail.graph triTail.weight d.snd 2)
        with hm | hm
    · rw [min_eq_left hm, min_eq_left (by linarith)]
      ring
    · rw [min_eq_right hm, min_eq_right (by linarith)]
      ring

private lemma dist_dart23_eq (s t : unitInterval) :
    dist (edgePoint dart23 s : MetricGraph triTail) (edgePoint dart23 t) = |(s : ℝ) - t| := by
  rw [dist_edgePoint_edgePoint_same]
  have hw : triTail.weight dart23.edge = 1 := rfl
  have h22 : SimpleGraph.vertexDist triTail.graph triTail.weight 2 2 = 0 :=
    vertexDist_self triTail.weight_nonneg 2
  have h33 : SimpleGraph.vertexDist triTail.graph triTail.weight 3 3 = 0 :=
    vertexDist_self triTail.weight_nonneg 3
  have h23 : SimpleGraph.vertexDist triTail.graph triTail.weight 2 3 = 1 := by
    have h := triTail_vertexDist_three_of_ne (by decide : (2 : Fin 4) ≠ 3)
    simpa [h22] using h
  have h32 : SimpleGraph.vertexDist triTail.graph triTail.weight 3 2 = 1 := by
    rw [vertexDist_comm, h23]
  change min (|(s : ℝ) - t| * triTail.weight dart23.edge)
      (min
        (min ((s : ℝ) * triTail.weight dart23.edge +
            SimpleGraph.vertexDist triTail.graph triTail.weight 2 2 +
            (t : ℝ) * triTail.weight dart23.edge)
          ((s : ℝ) * triTail.weight dart23.edge +
            SimpleGraph.vertexDist triTail.graph triTail.weight 2 3 +
            (1 - (t : ℝ)) * triTail.weight dart23.edge))
        (min ((1 - (s : ℝ)) * triTail.weight dart23.edge +
            SimpleGraph.vertexDist triTail.graph triTail.weight 3 2 +
            (t : ℝ) * triTail.weight dart23.edge)
          ((1 - (s : ℝ)) * triTail.weight dart23.edge +
            SimpleGraph.vertexDist triTail.graph triTail.weight 3 3 +
            (1 - (t : ℝ)) * triTail.weight dart23.edge))) = |(s : ℝ) - t|
  rw [hw, h22, h33, h23, h32]
  simp only [mul_one, add_zero]
  refine min_eq_left (le_min (le_min ?_ ?_) (le_min ?_ ?_)) <;>
    exact abs_le.mpr ⟨by linarith [s.2.1, s.2.2, t.2.1, t.2.2],
      by linarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

private lemma tailPos_not_inTail {p : MetricGraph triTail} (hp : ¬ inTail p) :
    tailPos p = 0 := by
  revert hp
  induction p using MetricGraph.ind with
  | vertex u =>
    intro hu
    have hu3 : u ≠ 3 := fun h => hu ⟨1, h ▸ (edgePoint_one dart23).symm⟩
    exact tailPos_vertex_ne hu3
  | edgePoint d t _ _ =>
    intro hnp
    have hne : d.edge ≠ dart23.edge := by
      intro he
      rcases (dart_edge_eq_iff d dart23).mp he with rfl | rfl
      · exact hnp ⟨t, rfl⟩
      · exact hnp ⟨unitInterval.symm t, by rw [← edgePoint_symm dart23 (unitInterval.symm t),
          unitInterval.symm_symm]⟩
    simp [tailPos, MetricGraph.lift_edgePoint, hne]

private lemma dist_triTail_edgePoint_le_iff (p : MetricGraph triTail) (τ₁ τ₂ : unitInterval) :
    dist p (edgePoint dart23 τ₁) ≤ dist p (edgePoint dart23 τ₂) ↔
      dist (tailPos p) τ₁ ≤ dist (tailPos p) τ₂ := by
  by_cases hp : inTail p
  · rcases hp with ⟨s, rfl⟩
    rw [dist_dart23_eq, dist_dart23_eq, tailPos_dart23]
    rfl
  · obtain ⟨h1, _⟩ := dist_not_inTail_edgePoint p hp τ₁
    obtain ⟨h2, _⟩ := dist_not_inTail_edgePoint p hp τ₂
    rw [h1, h2, tailPos_not_inTail hp]
    simp only [Subtype.dist_eq, Real.dist_eq, Set.Icc.coe_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg τ₁.2.1, abs_of_nonneg τ₂.2.1]
    constructor <;> intro h <;> linarith

private lemma tailScheme2_eval_le_zero (y : Fin 2 → unitInterval) :
    tailScheme2.eval y ≤ y 0 := by
  rw [← not_lt, ← Subtype.coe_lt_coe, tailScheme2.lt_eval_iff y (y 0)]
  have h0 : (0 : Fin 2) ∈ Finset.univ.filter fun i : Fin 2 => (y i : ℝ) ≤ y 0 := by simp
  simp [tailScheme2, (y 0).2.1]

private theorem triTailMech_isGroupStrategyProof :
    (Mechanism.deterministic triTailMech).IsGroupStrategyProof := by
  rw [Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨h_le, j, hj, h_lt⟩
  let x' := A.piecewise z x
  by_cases hx0 : inTail (x 0)
  · by_cases hx'0 : inTail (x' 0)
    · have hf : ∀ y : Fin 2 → MetricGraph triTail, inTail (y 0) →
          triTailMech y = edgePoint dart23 (tailScheme2.eval fun i => tailPos (y i)) := by
        intro y hy
        simp only [triTailMech, hy, ↓reduceIte]
      rw [hf x hx0, hf x' hx'0] at h_le h_lt
      have h_le' : ∀ i ∈ A,
          dist (tailPos (x i)) (tailScheme2.eval fun k => tailPos (x' k)) ≤
            dist (tailPos (x i)) (tailScheme2.eval fun k => tailPos (x k)) := fun i hi =>
        (dist_triTail_edgePoint_le_iff (x i) _ _).mp (h_le i hi)
      have h_lt' :
          dist (tailPos (x j)) (tailScheme2.eval fun k => tailPos (x' k)) <
            dist (tailPos (x j)) (tailScheme2.eval fun k => tailPos (x k)) :=
        lt_of_not_ge fun hge =>
          not_le_of_gt h_lt ((dist_triTail_edgePoint_le_iff (x j) _ _).mpr hge)
      have h_piece : (fun k => tailPos (x' k)) =
          A.piecewise (fun k => tailPos (z k)) (fun k => tailPos (x k)) := by
        ext k
        by_cases hk : k ∈ A <;> simp [x', hk]
      rw [h_piece] at h_le' h_lt'
      exact (Mechanism.isGroupStrategyProof_deterministic_iff tailScheme2.eval).mp
        tailScheme2.eval_isGroupStrategyProof
        (fun k => tailPos (x k)) (fun k => tailPos (z k)) A ⟨h_le', j, hj, h_lt'⟩
    · have h0A : (0 : Fin 2) ∈ A := by
        by_contra h0n
        apply hx'0
        simpa [x', h0n] using hx0
      have hf' : triTailMech x' = x' 0 := by simp only [triTailMech, hx'0, ↓reduceIte]
      have hf : triTailMech x =
          edgePoint dart23 (tailScheme2.eval fun i => tailPos (x i)) := by
        simp only [triTailMech, hx0, ↓reduceIte]
      obtain ⟨t0, ht0⟩ := hx0
      have hpos : 0 < dist (x' 0) (vertex 2) := (dist_not_inTail_edgePoint (x' 0) hx'0 0).2
      have hdist_x' : dist (x 0) (triTailMech x') = dist (x' 0) (vertex 2) + (t0 : ℝ) := by
        rw [hf', ht0, _root_.dist_comm]
        exact (dist_not_inTail_edgePoint (x' 0) hx'0 t0).1
      have hτ_le : (tailScheme2.eval fun i => tailPos (x i) : ℝ) ≤ t0 := by
        have h := tailScheme2_eval_le_zero (fun i => tailPos (x i))
        simpa [ht0, tailPos_dart23] using h
      have hdist_x : dist (x 0) (triTailMech x) ≤ (t0 : ℝ) := by
        rw [hf, ht0, dist_dart23_eq, abs_of_nonneg (sub_nonneg.mpr hτ_le)]
        linarith [(tailScheme2.eval fun i => tailPos (x i)).2.1]
      have hle0 := h_le 0 h0A
      linarith
  · have hfx : triTailMech x = x 0 := by simp only [triTailMech, hx0, ↓reduceIte]
    have h0_eq : triTailMech x' = x 0 := by
      by_cases h0A : (0 : Fin 2) ∈ A
      · have hle0 := h_le 0 h0A
        rw [hfx, _root_.dist_self] at hle0
        exact (dist_eq_zero.mp (le_antisymm hle0 dist_nonneg)).symm
      · have hx'0_eq : x' 0 = x 0 := by simp [x', h0A]
        simp only [triTailMech, hx'0_eq, hx0, ↓reduceIte]
    rw [hfx, h0_eq] at h_lt
    exact lt_irrefl _ h_lt

private theorem triTailMech_surjective : Function.Surjective triTailMech := by
  intro y
  refine ⟨fun _ => y, ?_⟩
  by_cases hy : inTail y
  · obtain ⟨t, rfl⟩ := hy
    simp only [triTailMech, show inTail (edgePoint dart23 t) from ⟨t, rfl⟩, ↓reduceIte]
    have hconst : (fun _ : Fin 2 => tailPos (edgePoint dart23 t : MetricGraph triTail)) =
        fun _ => t := by
      ext _; exact congrArg Subtype.val (tailPos_dart23 t)
    rw [hconst, tailScheme2.eval_const]
  · simp only [triTailMech, hy, ↓reduceIte]

private lemma tailScheme2_one_zero :
    tailScheme2.eval ![1, 0] = (halfIcc : unitInterval) := by
  let y : Fin 2 → unitInterval := ![1, 0]
  change tailScheme2.eval y = halfIcc
  ext
  refine le_antisymm ?_ ?_
  · rw [← not_lt, tailScheme2.lt_eval_iff y halfIcc]
    have hS : (Finset.univ.filter fun i : Fin 2 => (y i : ℝ) ≤ halfIcc) = {1} := by
      ext i; fin_cases i <;> simp [y, halfIcc]; norm_num
    rw [hS]
    have h0 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
    have h1 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
    simp [tailScheme2, halfIcc, h0, h1]
  · rw [← not_lt, tailScheme2.eval_lt_iff y halfIcc]
    have hS : (Finset.univ.filter fun i : Fin 2 => (y i : ℝ) < halfIcc) = {1} := by
      ext i; fin_cases i <;> simp [y, halfIcc]; norm_num
    rw [hS]
    have h0 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
    have h1 : (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by decide
    simp [tailScheme2, halfIcc, h0, h1]

private lemma vertex_zero_mem_triCycle :
    (vertex 0 : MetricGraph triTail) ∈ Set.range (circleMap triCycle_isShortestCycle.1) :=
  ⟨0, circleMap_zero triCycle_isShortestCycle.1⟩

private lemma vertex_one_mem_triCycle :
    (vertex 1 : MetricGraph triTail) ∈ Set.range (circleMap triCycle_isShortestCycle.1) := by
  refine ⟨1, ?_⟩
  let p01 : triTail.graph.Walk 0 1 := Adj.toWalk (by decide : triTailGraph.Adj 0 1)
  let q10 : triTail.graph.Walk 1 0 :=
    Walk.cons (by decide : triTailGraph.Adj 1 2)
      (Walk.cons (by decide : triTailGraph.Adj 2 0) .nil)
  have hlen1 : walkLength triTail.weight p01 = 1 := by
    change walkLength triTail.weight (Walk.cons (by decide : triTailGraph.Adj 0 1) .nil) = 1
    rw [walkLength_cons, walkLength_nil, add_zero]; rfl
  have htri : triCycle = p01.append q10 := rfl
  have hlen_tri : triCycle.length = 3 := rfl
  rw [circleMap_eq_walkPoint triCycle_isShortestCycle.1 (by norm_num) (by
    rw [triTail_walkLength_eq, hlen_tri]; norm_num),
    htri, walkPoint_append_of_le p01 q10 (hlen1 ▸ le_rfl), walkPoint_ge p01 (hlen1 ▸ le_rfl)]

/-- `triTailMech` on `Triangle + Tail` is group strategyproof and surjective, so
`exists_cycleDictator_of_isShortestCycle` forces a dictator on the shortest cycle `0-1-2` (player
`0`), while on `![vertex 3, vertex 0]` the outcome is the midpoint of edge `2-3`, ruling out any
global dictatorship. -/
example :
    (Mechanism.deterministic triTailMech).IsGroupStrategyProof ∧
    Function.Surjective triTailMech ∧
    (∀ (x : Fin 2 → MetricGraph triTail),
      (∀ i, x i ∈ Set.range (circleMap triCycle_isShortestCycle.1)) → triTailMech x = x 0) ∧
    ¬ ∃ i₀ : Fin 2, ∀ x, triTailMech x = x i₀ := by
  refine ⟨triTailMech_isGroupStrategyProof, triTailMech_surjective, ?_, ?_⟩
  · obtain ⟨i₀, hi₀⟩ := exists_cycleDictator_of_isShortestCycle triTail triCycle_isShortestCycle
      triTailMech_isGroupStrategyProof.isStrategyProof triTailMech_surjective
    have hi0_eq : i₀ = 0 := by
      let x01 : Fin 2 → MetricGraph triTail := ![vertex 0, vertex 1]
      have hx01 : ∀ i, x01 i ∈ Set.range (circleMap triCycle_isShortestCycle.1) := by
        intro i
        fin_cases i
        · exact vertex_zero_mem_triCycle
        · exact vertex_one_mem_triCycle
      have h0_not : ¬ inTail (vertex 0 : MetricGraph triTail) := by
        rintro ⟨t, ht⟩
        have hv := congrArg tailPos ht
        rw [tailPos_dart23, tailPos_vertex_ne (by decide : (0 : Fin 4) ≠ 3)] at hv
        have heq := ht.trans (by rw [← hv, edgePoint_zero dart23])
        exact (vertex_inj.ne.mpr (by decide : (0 : Fin 4) ≠ 2)) heq
      have hfx01 : triTailMech x01 = vertex 0 := by
        simp only [triTailMech, x01, Matrix.cons_val_zero, h0_not, ↓reduceIte]
      have hdict := (hi₀ x01 hx01).symm.trans hfx01
      fin_cases i₀
      · rfl
      · exfalso
        exact vertex_inj.ne.mpr (by decide : (1 : Fin 4) ≠ 0) hdict
    simpa [hi0_eq] using hi₀
  · rintro ⟨i₀, hi₀⟩
    have hx : triTailMech ![vertex 3, vertex 0] = edgePoint dart23 halfIcc := by
      simp only [triTailMech, Matrix.cons_val_zero,
        show inTail (vertex 3 : MetricGraph triTail) from ⟨1, (edgePoint_one dart23).symm⟩,
        ↓reduceIte]
      have harg : (fun i : Fin 2 => tailPos ((![vertex 3, vertex 0] : Fin 2 → _) i)) = ![1, 0] := by
        ext i; fin_cases i
        · exact congrArg Subtype.val tailPos_vertex_three
        · exact congrArg Subtype.val (tailPos_vertex_ne (by decide : (0 : Fin 4) ≠ 3))
      rw [harg, tailScheme2_one_zero]
    have hval := congrArg tailPos ((hi₀ ![vertex 3, vertex 0]).symm.trans hx)
    rw [tailPos_dart23] at hval
    fin_cases i₀
    · have h1 : (tailPos (vertex 3 : MetricGraph triTail) : ℝ) = halfIcc :=
        congrArg Subtype.val hval
      rw [tailPos_vertex_three] at h1
      change (1 : ℝ) = 1 / 2 at h1
      norm_num at h1
    · have h0 : (tailPos (vertex 0 : MetricGraph triTail) : ℝ) = halfIcc :=
        congrArg Subtype.val hval
      rw [tailPos_vertex_ne (by decide : (0 : Fin 4) ≠ 3)] at h0
      change (0 : ℝ) = 1 / 2 at h0
      norm_num at h0

end CycleClients

end CslibFrontierTests.SchummerVohra
