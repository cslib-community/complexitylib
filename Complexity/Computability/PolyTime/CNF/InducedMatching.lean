/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.InducedMatchingInterval
import all Complexity.Computability.PolyTime.CNF.DominatingInducedMatching

/-!
# Induced matching counts without a size circuit

Use only the approved selected-degree-one clauses and selected-neighbor predicates. There are no
size gates or domination constraints. The actual plan counts conventional unordered-edge induced
matching subgraphs once each, including the empty matching. This supplies the no-size-test query
budget of [ChenJiangZhu2027], Corollary 7.5 / Appendix D.1 (PDF pp. 26, 34).

## Main results

* `build_polytime`: actual original-matrix traversal and binary literal writing.
* `plan_count`: exact original matching-object count.
* `query_count`, `query_budget`: two width-three queries with `2v-1` variables for positive `v`.
-/

public section

namespace Cslib.Logic.PL.InducedMatching

open Turing.MultiTapeTM IndependentDomination DominatingInducedMatching

/-- Actual degree-one construction with neither size-test gates nor edge-cover clauses. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (order x, upper x, conditions x)

/-- Polynomial resources include all actual matrix reads and binary query-input writes. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  exact hn.prod (upper_polytime.prod conditions_polytime)

/-- Finite original columns erase to the actual constructed lists in traversal order. -/
theorem build_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    build (ofGraph G) =
      TwoBoundary.BinaryFrontend.ofFinite (finiteUpper G) (finiteConditions G) := by
  have hc := congrArg TwoBoundary.BinaryFrontend.conditions
    (DominatingInducedMatching.build_ofGraph G)
  change conditions (ofGraph G) = (finiteConditions G).map (CNF.relabel Fin.val) at hc
  change (n, upper (ofGraph G), conditions (ofGraph G)) = _
  rw [InducedMatchingInterval.upper_ofGraph, hc]
  rfl

/-- The upper clauses and neighborhood terms retain fixed widths three and one. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∀ c ∈ finiteUpper G, c.length ≤ 3) ∧
      ∀ p ∈ finiteConditions G, ∀ t ∈ p, t.length ≤ 1 :=
  ⟨fun c hc => (DominatingInducedMatching.widths G).1 c (List.mem_append_left _ hc),
    (DominatingInducedMatching.widths G).2⟩

open Classical in
/-- The actual no-size query plan counts conventional induced matching subgraphs, including empty
and edgeless graphs, without orientations or isolated marks. -/
theorem plan_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile (build (ofGraph G))) =
      Fintype.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced} := by
  rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count]
  have ha := Fintype.card_congr (Equiv.subtypeEquivRight
    (DominatingInducedMatching.regular_semantics G))
  have hb := SimpleGraph.card_inducedMatching_supports_eq G (fun _ => True)
  simp only [and_true, Nat.card_eq_fintype_card] at hb
  exact ha.trans hb

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
    (finiteUpper G) (finiteConditions G) hb hp N q hq
  obtain ⟨hside, hterms⟩ := DominatingInducedMatching.volumes G
  simp only [List.length_append] at hside
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


end Cslib.Logic.PL.InducedMatching
