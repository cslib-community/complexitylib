/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.IndependentDomination
public import Complexity.Foundations.Combinatorics.Digraph.Kernel
import Complexity.Foundations.Data.List.Lookup

/-!
# Actual outgoing-absorbing digraph kernel reduction

The already executable explicit-matrix arc-exclusion/coverage writer also applies to directed
matrices. Its new correspondence here uses directed independence and outgoing absorption, without
symmetrizing the graph. This is [ChenJiangZhu2027], Proposition D.5 (PDF p. 37) and the kernel
specialization of Corollary 7.4 (p. 26). The source assumes loopless digraphs; the formulas also
count the same explicitly defined kernel predicate on digraphs with loops.

## Main definitions

* `ofDigraph`: original directed adjacency-matrix input with a unary declaration.
* `plan`: the actual binary one/two-query writer, reusing the existing matrix traversal.

## Main results

* `plan_polytime`: actual binary construction, including arc tests and clause writes.
* `plan_count`: exact count of original kernel selections, with no marking multiplicity.
* `plan_budget`: width-three, quadratic-size queries on `2v-1` variables.
-/

public section

namespace Cslib.Logic.PL.DigraphKernel

open Turing.MultiTapeTM IndependentDomination

/-- Canonical directed matrix; orientation is retained and no undirected closure is formed. -/
@[expose] def ofDigraph {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] : Input :=
  (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v))

/-- Actual source arc exclusions and outgoing-neighborhood predicates, followed by query writing. -/
@[expose] def plan (x : Input) : TwoBoundary.BinaryFrontend.Output :=
  TwoBoundary.BinaryFrontend.compile (build x)

/-- The whole directed matrix-to-query construction has polynomial binary resources. -/
@[fun_prop] theorem plan_polytime : ComputableInPolyTime plan encInput
    TwoBoundary.BinaryFrontend.encOutput :=
  TwoBoundary.BinaryFrontend.compile_polytime.comp build_polytime

private theorem adjacent_ofDigraph {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : adjacent (ofDigraph G) u.val v.val = decide (G.Adj u v) := by
  simp only [adjacent, ofDigraph, matrix, List.getD_ofFn]

/-- Finite edge clauses used only to state the original-assignment correspondence. -/
@[expose] def finiteExclusions {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    CNF (Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun v =>
    if G.Adj u v then [[(u, false), (v, false)]] else []
/-- Finite closed-neighborhood singleton terms, without a vertex-subset enumeration. -/
@[expose] def finiteCoverage {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    List (DNF (Fin n)) :=
  (List.finRange n).map fun u =>
    ((List.finRange n).filter fun v => decide (u = v) || decide (G.Adj u v)).map
      fun v => [(v, true)]

/-- The actual raw graph writer is precisely finite-variable erasure of these original clauses. -/
theorem build_ofDigraph {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    build (ofDigraph G) = TwoBoundary.BinaryFrontend.ofFinite
      (finiteExclusions G) (finiteCoverage G) := by
  have hn : order (ofDigraph G) = n := rfl
  simp only [build, exclusions, coverage, hn, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.map_map, Function.comp_def, TwoBoundary.BinaryFrontend.ofFinite,
    CNF.relabel, finiteExclusions, finiteCoverage, List.map_flatMap]
  apply congrArg (fun z : CNF ℕ × List (DNF ℕ) => (n, z))
  apply Prod.ext <;> dsimp only
  · congr 1
    funext u
    congr 1
    funext v
    simp only [adjacent_ofDigraph, decide_eq_true_eq]
    split_ifs <;> simp [Clause.relabel]
  · congr 1
    funext u
    simp only [List.filter_map, List.map_map, Function.comp_def, adjacent_ofDigraph,
      Fin.val_inj]
    rfl

/-- Side width is two and every term has width one, uniformly over graph density. -/
theorem widths {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    (∀ c ∈ finiteExclusions G, c.length ≤ 2) ∧
      (∀ p ∈ finiteCoverage G, ∀ t ∈ p, t.length ≤ 1) := by
  constructor
  · intro c hc
    obtain ⟨u, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨v, _, hc⟩ := List.mem_flatMap.mp hc
    split_ifs at hc
    · have he := List.mem_singleton.mp hc
      subst c
      simp
    · simp at hc
  · intro p hp t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    simp

/-- Arc exclusions and outgoing coverage count precisely the original absorbing kernels. -/
theorem finite_semantics {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteExclusions G).eval σ = true ∧
        (∀ p ∈ finiteCoverage G, DNF.eval σ p = true) ↔
      G.IsKernel {u | σ u = true} := by
  have he (u v : Fin n) :
      CNF.eval σ (if G.Adj u v then [[(u, false), (v, false)]] else []) = true ↔
        (G.Adj u v → σ u = false ∨ σ v = false) := by
    by_cases ha : G.Adj u v <;> simp [ha, CNF.eval, Clause.eval, Literal.eval]
  have hB : (finiteExclusions G).eval σ = true ↔
      ∀ u v, G.Adj u v → σ u = false ∨ σ v = false := by
    simp only [finiteExclusions, CNF.eval_flatMap_eq_true_iff, List.mem_finRange,
      forall_true_left, he]
  rw [Digraph.isKernel_selection_iff, hB]
  apply and_congr_right
  intro _
  simp only [finiteCoverage, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff, List.mem_finRange, forall_true_left]
  simp only [DNF.eval_eq_true_iff, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, Bool.or_eq_true, decide_eq_true_eq, Term.eval]
  constructor
  · intro h u
    obtain ⟨_, ⟨v, hgood, rfl⟩, hv⟩ := h u
    rcases hgood with rfl | ha
    · exact Or.inl (by simpa [Literal.eval] using hv)
    · exact Or.inr ⟨v, ha, by simpa [Literal.eval] using hv⟩
  · intro h u
    rcases h u with hu | ⟨v, ha, hv⟩
    · exact ⟨[(u, true)], ⟨u, Or.inl rfl, rfl⟩, by simpa [Literal.eval] using hu⟩
    · exact ⟨[(v, true)], ⟨v, Or.inr ha, rfl⟩, by simpa [Literal.eval] using hv⟩

/-- The constructor has one condition per vertex, independently of graph density. -/
theorem finiteCoverage_length {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    (finiteCoverage G).length = n := by simp [finiteCoverage]

/-- Actual edge exclusions and neighborhood-term volume are quadratic even on dense graphs. -/
theorem volumes {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    (finiteExclusions G).length ≤ n ^ 2 ∧
      ((finiteCoverage G).map List.length).sum ≤ n ^ 2 := by
  constructor
  · simp only [finiteExclusions, List.length_flatMap, List.finRange, List.map_ofFn,
      List.sum_ofFn]
    calc
      _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        dsimp only [Function.comp_def]
        split_ifs <;> simp
      _ = _ := by simp [pow_two]
  · simp only [finiteCoverage, List.length_map, List.finRange,
      List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _u : Fin n, n := Finset.sum_le_sum fun u _ => by
        have hlen := List.length_filter_le
          (fun v => decide (u = v) || decide (G.Adj u v))
          (List.ofFn (fun i : Fin n => i))
        simp only [List.length_ofFn] at hlen
        omega
      _ = _ := by simp [pow_two]

/-- Positive-vertex directed graphs emit exactly two ordinary boundary queries. -/
theorem query_count {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries (plan (ofDigraph G))).length = 2 := by
  have hlen : (TwoBoundary.BinaryFrontend.conditions (build (ofDigraph G))).length = n := by
    simp only [build, TwoBoundary.BinaryFrontend.conditions, coverage, ofDigraph, order,
      List.length_map, List.length_range]
  have hem : (TwoBoundary.BinaryFrontend.conditions (build (ofDigraph G))).isEmpty ≠ true := by
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  simp only [plan, TwoBoundary.BinaryFrontend.compile, hem, Bool.false_eq_true, ↓reduceIte,
    TwoBoundary.BinaryFrontend.queries, List.length_cons, List.length_nil]

/-- Every actual graph query has the source's `2v-1` variables, width three and quadratic size.
At zero vertices the one-query branch is used, without a negative declaration. -/
theorem plan_budget {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries (plan (ofDigraph G))) :
    N = 2 * n - 1 ∧ q.length ≤ 3 * n ^ 2 ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  change (N, q) ∈ TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (build (ofDigraph G))) at hq
  rw [build_ofDigraph] at hq
  obtain ⟨hb, hp⟩ := widths G
  obtain ⟨hv, hm, hw⟩ := TwoBoundary.BinaryFrontend.compile_budget
    (finiteExclusions G) (finiteCoverage G) hb hp N q hq
  obtain ⟨hside, hterms⟩ := volumes G
  refine ⟨?_, by omega, by simpa using hw⟩
  have hlen := finiteCoverage_length G
  split_ifs at hv with he
  · have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  · omega

open Classical in
/-- Actual emitted-plan count equals the number of absorbing kernels, retaining
all declared vertices and requiring no marking, witness or output advice. -/
theorem plan_count {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (plan (ofDigraph G)) =
      Fintype.card {S : Set (Fin n) // G.IsKernel S} := by
  rw [plan, build_ofDigraph, TwoBoundary.BinaryFrontend.compile_count]
  have ha := Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics G))
  have hb := Digraph.card_kernel_selections_eq G
  simp only [← Nat.card_eq_fintype_card] at ha hb ⊢
  exact ha.trans hb

end Cslib.Logic.PL.DigraphKernel
