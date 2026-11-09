/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DominatingInducedMatching
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Actual dominating induced matching reduction

Write the degree-at-most-one clauses for selected vertices, one selected-neighbor condition per
vertex, and positive edge-cover clauses. The endpoint-set bridge identifies actual unordered
matching edges, each dominating precisely the original edges incident to it. This is
[ChenJiangZhu2027], Corollary D.4 (PDF p. 36) and Corollary 7.4 (p. 26).

## Main definitions

* `upper`: original-column degree-at-most-one clauses.
* `cover`: positive edge-cover clauses, reusing the original matrix arc traversal.
* `conditions`: selected-neighbor predicates, permitting unselected vertices.
* `build`: actual graph-to-DNF constructor, without a supplied matching or runtime contract.

## Main results

* `build_polytime`: actual encoded traversal, literal writing and bounded-degree construction.
* `finite_semantics`, `plan_count`: source matching-support characterization and exact counts.
* `query_count`, `query_budget`, `query_cubic_budget`: actual source two-query budgets.
-/

public section

namespace Cslib.Logic.PL.DominatingInducedMatching

open Turing.MultiTapeTM IndependentDomination

/-- Selected vertices may not have two distinct selected neighbors. -/
@[expose] def upper (x : Input) : CNF ℕ :=
  (List.range (order x)).flatMap fun u => (List.range (order x)).flatMap fun a =>
    (List.range (order x)).flatMap fun b =>
      if decide (a ≠ b) && adjacent x u a && adjacent x u b then
        [[(u, false), (a, false), (b, false)]] else []

/-- Flip the already written edge exclusions to positive endpoint-cover clauses. -/
@[expose] def cover (x : Input) : CNF ℕ :=
  (exclusions x).map (List.map Std.Sat.Literal.negate)

/-- Every selected vertex has a selected neighbor; an unselected vertex satisfies its own term. -/
@[expose] def conditions (x : Input) : List (DNF ℕ) :=
  (List.range (order x)).map fun u =>
    [[(u, false)]] ++ ((List.range (order x)).filter (adjacent x u)).map (fun v => [(v, true)])

/-- Actual construction on the original declared vertices, with no auxiliary matching witnesses. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (order x, upper x ++ cover x, conditions x)

private theorem upper_polytime : ComputableInPolyTime upper encInput VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  unfold upper VCOne.encSignedCNF
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _))))
  let ei := encPair (encPair (encPair encInput encUnary) encUnary) encUnary
  have hau := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : ((Input × ℕ) × ℕ) × ℕ => (p.1.1.1, p.1.1.2, p.1.2)) ei
    (encPair encInput (encPair encUnary encUnary)) from by unfold ei; fun_prop)
  have hbu := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : ((Input × ℕ) × ℕ) × ℕ => (p.1.1.1, p.1.1.2, p.2)) ei
    (encPair encInput (encPair encUnary encUnary)) from by unfold ei; fun_prop)
  have hne : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2))
      ei encBool := by unfold ei; fun_prop
  have hu : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.1.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have ha : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hb : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have htest : ComputableInPolyTime
      (fun p : ((Input × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2) &&
        adjacent p.1.1.1 p.1.1.2 p.1.2 && adjacent p.1.1.1 p.1.1.2 p.2) ei encBool := by fun_prop
  have hbody : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ =>
      [[(p.1.1.2, false), (p.1.2, false), (p.2, false)]]) ei
      (encList (encList (encPair encNat encBool))) := by fun_prop
  exact (htest.ite' hbody (.const [])).of_enc_eq fun _ => rfl

private theorem cover_polytime : ComputableInPolyTime cover encInput VCOne.encSignedCNF :=
  ((Literal.computableInPolyTime_negate encNat).map.map.comp
    IndependentDomination.exclusions_polytime)

private theorem conditions_polytime : ComputableInPolyTime conditions encInput
    (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  let ei := encPair encInput encUnary
  have hns : ComputableInPolyTime (fun p : Input × ℕ =>
      (List.range (order p.1)).filter (adjacent p.1 p.2)) ei (encList encUnary) := by
    apply ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
    exact IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
      (fun p : (Input × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
        (encPair ei encUnary) (encPair encInput (encPair encUnary encUnary)) from by
          unfold ei; fun_prop)
  have hlit : ComputableInPolyTime (fun v : ℕ => [(v, true)]) encUnary
      (encList (encPair encNat encBool)) := by
    have h := ComputableInPolyTime.unary_to_binary
    fun_prop
  have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hself : ComputableInPolyTime (fun p : Input × ℕ => [[(p.2, false)]]) ei
      (encList (encList (encPair encNat encBool))) := by fun_prop
  have hbody := ComputableInPolyTime.listAppend' hself (hlit.map.comp hns)
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn) hbody

/-- Actual triple/matrix traversal, binary literal writes and shared edge-cover construction. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  exact hn.prod ((ComputableInPolyTime.listAppend' upper_polytime cover_polytime).prod
    conditions_polytime)

/-- Finite original-column degree-at-most-one clauses. -/
@[expose] def finiteUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : CNF (Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun a =>
    (List.finRange n).flatMap fun b =>
      if a ≠ b ∧ G.Adj u a ∧ G.Adj u b then [[(u, false), (a, false), (b, false)]] else []

/-- Finite positive edge-cover clauses, using the existing original-column edge writer. -/
@[expose] def finiteCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : CNF (Fin n) :=
  (finiteExclusions G).map (List.map Std.Sat.Literal.negate)

/-- A selected vertex requires a selected neighbor; unselected vertices satisfy their own term. -/
@[expose] def finiteConditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (DNF (Fin n)) :=
  (List.finRange n).map fun u =>
    [[(u, false)]] ++ ((List.finRange n).filter (fun v => decide (G.Adj u v))).map
      (fun v => [(v, true)])

/-- Actual matrix construction agrees with finite original-column erasure. -/
theorem build_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    build (ofGraph G) = TwoBoundary.BinaryFrontend.ofFinite
      (finiteUpper G ++ finiteCover G) (finiteConditions G) := by
  have hn : order (ofGraph G) = n := rfl
  have hEG := congrArg TwoBoundary.BinaryFrontend.side (IndependentDomination.build_ofGraph G)
  change exclusions (ofGraph G) = (finiteExclusions G).relabel Fin.val at hEG
  have hCover : cover (ofGraph G) = (finiteCover G).relabel Fin.val := by
    simp only [cover, finiteCover, hEG, CNF.relabel, Clause.relabel, List.map_map,
      Function.comp_def]
    rfl
  have hUpper : upper (ofGraph G) = (finiteUpper G).relabel Fin.val := by
    simp only [upper, finiteUpper, hn, ← List.map_coe_finRange_eq_range,
      List.flatMap_map, CNF.relabel, List.map_flatMap]
    congr 1
    funext u
    congr 1
    funext a
    congr 1
    funext b
    simp only [IndependentDomination.adjacent_ofGraph, Bool.and_eq_true,
      decide_eq_true_eq, ne_eq, Fin.val_inj, and_assoc]
    split_ifs <;> rfl
  have hConditions : conditions (ofGraph G) = (finiteConditions G).map (CNF.relabel Fin.val) := by
    simp only [conditions, finiteConditions, hn, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
    congr 1
    funext u
    simp only [List.filter_map, IndependentDomination.adjacent_ofGraph,
      CNF.relabel, List.map_map, Function.comp_def, List.map_append, List.map_cons, List.map_nil,
      Clause.relabel]
    rfl
  change (n, upper (ofGraph G) ++ cover (ofGraph G), conditions (ofGraph G)) = _
  simp only [TwoBoundary.BinaryFrontend.ofFinite, CNF.relabel, List.map_append]
  rw [hUpper, hCover, hConditions]
  rfl

/-- The upper part forbids a selected vertex with two distinct selected neighbors. -/
theorem finiteUpper_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteUpper G).eval σ = true ↔ ∀ u a b, a ≠ b → G.Adj u a → G.Adj u b →
      ¬(σ u = true ∧ σ a = true ∧ σ b = true) := by
  have he (u a b : Fin n) :
      CNF.eval σ (if a ≠ b ∧ G.Adj u a ∧ G.Adj u b then
        [[(u, false), (a, false), (b, false)]] else []) = true ↔
        (a ≠ b → G.Adj u a → G.Adj u b → ¬(σ u = true ∧ σ a = true ∧ σ b = true)) := by
    split_ifs with h
    · cases hu : σ u <;> cases ha : σ a <;> cases hb : σ b <;>
        simp_all [CNF.eval, Clause.eval, Literal.eval]
    · simp only [CNF.eval_nil, true_iff]
      intro ha hu hv
      exact False.elim (h ⟨ha, hu, hv⟩)
  simp only [finiteUpper, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_true_left, he]

/-- Positive edge clauses enforce that the selected support covers every original edge. -/
theorem finiteCover_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteCover G).eval σ = true ↔ ∀ u v, G.Adj u v → σ u = true ∨ σ v = true := by
  have he (u v : Fin n) :
      CNF.eval σ ((if G.Adj u v then [[(u, false), (v, false)]] else []).map
        (List.map Std.Sat.Literal.negate)) = true ↔
          (G.Adj u v → σ u = true ∨ σ v = true) := by
    by_cases h : G.Adj u v <;>
      simp [h, CNF.eval, Clause.eval, Literal.eval, Std.Sat.Literal.negate]
  simp only [finiteCover, finiteExclusions, List.map_flatMap, CNF.eval_flatMap_eq_true_iff,
    List.mem_finRange, forall_true_left, he]

/-- Lower predicates permit unselected vertices and require neighbors for selected ones. -/
theorem finiteConditions_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (∀ p ∈ finiteConditions G, DNF.eval σ p = true) ↔
      ∀ u, σ u = false ∨ ∃ v, G.Adj u v ∧ σ v = true := by
  simp [finiteConditions, DNF.eval_eq_true_iff, Term.eval, Literal.eval]

/-- Selected vertices induce a conventional Mathlib matching, not oriented edge witnesses. -/
theorem regular_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteUpper G).eval σ = true ∧ (∀ p ∈ finiteConditions G, DNF.eval σ p = true) ↔
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching := by
  rw [finiteUpper_eval, finiteConditions_eval]
  constructor
  · rintro ⟨hu, hl⟩ u hσ
    rcases hl u with hfalse | ⟨v, ha, hv⟩
    · simp_all
    · refine ⟨v, ⟨hσ, hv, ha⟩, fun w hw => ?_⟩
      by_contra hne
      exact hu u w v hne hw.2.2 ha ⟨hσ, hw.2.1, hv⟩
  · intro h
    constructor
    · intro u a b hne hua hub hsel
      exact hne ((h hsel.1).unique ⟨hsel.1, hsel.2.1, hua⟩ ⟨hsel.1, hsel.2.2, hub⟩)
    · intro u
      by_cases hu : σ u = true
      · obtain ⟨v, hv, _⟩ := h hu
        exact Or.inr ⟨v, hv.2.2, hv.2.1⟩
      · exact Or.inl (Bool.eq_false_iff.mpr hu)

/-- Exact source endpoint characterization, including edge cover and the unique matching support. -/
theorem finite_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteUpper G ++ finiteCover G).eval σ = true ∧
      (∀ p ∈ finiteConditions G, DNF.eval σ p = true) ↔
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        ∀ u v, G.Adj u v → σ u = true ∨ σ v = true := by
  rw [CNF.eval_append, Bool.and_eq_true, finiteCover_eval, ← regular_semantics G σ]
  tauto

/-- The bounded part has width at most three, and each neighborhood term is a singleton. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∀ c ∈ finiteUpper G ++ finiteCover G, c.length ≤ 3) ∧
      (∀ p ∈ finiteConditions G, ∀ t ∈ p, t.length ≤ 1) := by
  constructor
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨u, _, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨a, _, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, _, hc⟩ := List.mem_flatMap.mp hc
      split_ifs at hc
      · have he := List.mem_singleton.mp hc
        subst c
        simp
      · simp at hc
    · change c ∈ (finiteExclusions G).map (List.map Std.Sat.Literal.negate) at hc
      obtain ⟨c0, hc0, heq⟩ := List.mem_map.mp hc
      rw [← heq, List.length_map]
      exact ((IndependentDomination.widths G).1 c0 hc0).trans (by decide : 2 ≤ 3)
  · intro p hp t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp ht with ht | ht
    · have he := List.mem_singleton.mp ht
      subst t
      simp
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
      simp

/-- There is one selected-neighbor condition per original vertex. -/
theorem finiteConditions_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteConditions G).length = n := by simp [finiteConditions]

/-- Cubic bounded-clause volume and quadratic neighborhood-term volume, at arbitrary density. -/
theorem volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteUpper G ++ finiteCover G).length ≤ n ^ 3 + n ^ 2 ∧
      ((finiteConditions G).map List.length).sum ≤ n * (n + 1) := by
  constructor
  · have hupper : (finiteUpper G).length ≤ n ^ 3 := by
      simp only [finiteUpper, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
      calc
        _ ≤ ∑ _u : Fin n, ∑ _a : Fin n, ∑ _b : Fin n, 1 := by
          apply Finset.sum_le_sum
          intro u _
          apply Finset.sum_le_sum
          intro a _
          apply Finset.sum_le_sum
          intro b _
          dsimp only [Function.comp_def]
          split_ifs <;> simp
        _ = _ := by simp; ring
    have hcover : (finiteCover G).length ≤ n ^ 2 := by
      simpa only [finiteCover, List.length_map] using (IndependentDomination.volumes G).1
    rw [List.length_append]
    omega
  · simp only [finiteConditions, Function.comp_def, List.finRange, List.map_ofFn,
      List.sum_ofFn, List.length_append, List.length_map, List.length_cons, List.length_nil]
    calc
      _ ≤ ∑ _u : Fin n, (n + 1) := by
        apply Finset.sum_le_sum
        intro u _
        have hl := List.length_filter_le (fun v => decide (G.Adj u v))
          (List.ofFn (fun i : Fin n => i))
        simp only [List.length_ofFn] at hl
        omega
      _ = _ := by simp

/-- Exactly two ordinary queries on nonempty graphs; zero vertices use the one-query base case. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))).length = 2 := by
  rw [TwoBoundary.BinaryFrontend.compile_query_count, build_ofGraph]
  have hl := finiteConditions_length G
  have he : (finiteConditions G).isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    omega
  simp only [TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.isEmpty_map, he, Bool.false_eq_true, ↓reduceIte]

/-- Actual declaration/width/size/literal bounds, including the zero-vertex base query. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))) :
    N = 2 * n - 1 ∧ q.length ≤ n ^ 3 + 3 * n ^ 2 + 2 * n ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  rw [build_ofGraph] at hq
  obtain ⟨hb, hp⟩ := widths G
  obtain ⟨hv, hm, hw⟩ := TwoBoundary.BinaryFrontend.compile_budget
    (finiteUpper G ++ finiteCover G) (finiteConditions G) hb hp N q hq
  obtain ⟨hside, hterms⟩ := volumes G
  have hl := finiteConditions_length G
  refine ⟨?_, by nlinarith, by simpa using hw⟩
  split_ifs at hv with he
  · have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  · omega

/-- The source cubic budget on every positive-vertex query, uniformly over edge density. -/
theorem query_cubic_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n)
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))) : q.length ≤ 6 * n ^ 3 := by
  have h := (query_budget G N q hq).2.1
  have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      _ = n ^ 3 := by ring
  nlinarith

open Classical in
/-- The actual plan counts conventional matching subgraphs with exact edge domination, once each. -/
theorem plan_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile (build (ofGraph G))) =
      Fintype.card {M : G.Subgraph // M.IsDominatingInducedMatching} := by
  rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count]
  have ha := Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics G))
  have hb := G.card_dominatingMatching_supports_eq
  simp only [← Nat.card_eq_fintype_card] at ha ⊢
  exact ha.trans hb

end Cslib.Logic.PL.DominatingInducedMatching
