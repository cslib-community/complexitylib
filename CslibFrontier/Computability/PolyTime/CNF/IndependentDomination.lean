/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.TwoBoundaryFrontend
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Actual independent-domination DNF frontend

The no-size-test case of [ChenJiangZhu2027], Corollary 7.2 and Appendix D.4, Proposition D.3
(PDF pp. 24–25, 36): edge exclusions express independence and closed-neighborhood coverage
expresses domination. Input is an explicit adjacency matrix with a unary vertex declaration.
The constructor is polynomial on all raw matrices and never enumerates vertex subsets.
Input size bounds, functional size tests and other graph rules are separate obligations.
-/

public section

namespace Cslib.Logic.PL.IndependentDomination

open Turing.MultiTapeTM

/-- Unary declared vertex count and explicit framed Boolean adjacency rows. -/
abbrev Input := ℕ × List (List Bool)
/-- Original number of vertices, including isolated vertices. -/
@[expose] def order : Input → ℕ | (n, _) => n
/-- Explicit original matrix rows. -/
@[expose] def matrix : Input → List (List Bool) | (_, rows) => rows
/-- Row and column lookup, with a total fallback for malformed raw matrices. -/
@[expose] def adjacent (x : Input) (u v : ℕ) : Bool :=
  ((matrix x).getD u []).getD v false
/-- All framing and cells are charged, and the vertex declaration is unary. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair encUnary (encList (encList encBool))

/-- Actual edge exclusions in the original vertex columns. -/
@[expose] def exclusions (x : Input) : CNF ℕ :=
  (List.range (order x)).flatMap fun u => (List.range (order x)).flatMap fun v =>
    if adjacent x u v then [[(u, false), (v, false)]] else []
/-- One ordinary coverage condition per original closed neighborhood. -/
@[expose] def coverage (x : Input) : List (DNF ℕ) :=
  (List.range (order x)).map fun u =>
    ((List.range (order x)).filter fun v => decide (u = v) || adjacent x u v).map
      fun v => [(v, true)]
/-- The actual original graph-to-generic-DNF constructor. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (order x, exclusions x, coverage x)

private theorem adjacent_polytime : ComputableInPolyTime
    (fun p : Input × ℕ × ℕ => let (x, u, v) := p; adjacent x u v)
    (encPair encInput (encPair encUnary encUnary)) encBool := by
  let ei := encPair encInput (encPair encUnary encUnary)
  have hM : ComputableInPolyTime (fun p : Input × ℕ × ℕ => matrix p.1)
      ei (encList (encList encBool)) := by unfold matrix ei encInput; fun_prop
  have hu : ComputableInPolyTime (fun p : Input × ℕ × ℕ => p.2.1)
      ei encUnary := by unfold ei; fun_prop
  have hv : ComputableInPolyTime (fun p : Input × ℕ × ℕ => p.2.2)
      ei encUnary := by unfold ei; fun_prop
  exact ComputableInPolyTime.listGetDWithInput
    (ComputableInPolyTime.listGetDWithInput hM hu []) hv false

private theorem exclusions_polytime : ComputableInPolyTime exclusions encInput
    VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  unfold exclusions VCOne.encSignedCNF
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
  have ha := adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : (Input × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (encPair (encPair encInput encUnary) encUnary)
      (encPair encInput (encPair encUnary encUnary)) from by fun_prop)
  have hbody : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ =>
      [[(p.1.2, false), (p.2, false)]])
      (encPair (encPair encInput encUnary) encUnary)
      (encList (encList (encPair encNat encBool))) := by
    have hu : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => p.1.2)
        (encPair (encPair encInput encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hv : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => p.2)
        (encPair (encPair encInput encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    fun_prop
  exact (ha.ite' hbody (.const [])).of_enc_eq fun _ => rfl

private theorem coverage_polytime : ComputableInPolyTime coverage encInput
    (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  unfold coverage VCOne.encSignedCNF
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _))) ?_)
  · have hv : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => p.2)
        (encPair (encPair encInput encUnary) encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    fun_prop
  · have ha := adjacent_polytime.comp (show ComputableInPolyTime
      (fun p : (Input × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (encPair (encPair encInput encUnary) encUnary)
      (encPair encInput (encPair encUnary encUnary)) from by fun_prop)
    fun_prop

/-- Complete polynomial binary construction, including every actual edge/coverage literal write. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  exact hn.prod (exclusions_polytime.prod coverage_polytime)

/-- Canonical explicit square adjacency matrix for a simple undirected graph. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Input :=
  (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v))

/-- The actual graph input decodes every declared adjacency bit exactly. -/
theorem adjacent_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : adjacent (ofGraph G) u.val v.val = decide (G.Adj u v) := by
  simp only [adjacent, ofGraph, matrix, List.getD_ofFn]

/-- Finite edge clauses used only to state the original-assignment correspondence. -/
@[expose] def finiteExclusions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    CNF (Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun v =>
    if G.Adj u v then [[(u, false), (v, false)]] else []
/-- Finite closed-neighborhood singleton terms, without a vertex-subset enumeration. -/
@[expose] def finiteCoverage {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (DNF (Fin n)) :=
  (List.finRange n).map fun u =>
    ((List.finRange n).filter fun v => decide (u = v) || decide (G.Adj u v)).map
      fun v => [(v, true)]

/-- The actual raw graph writer is precisely finite-variable erasure of these original clauses. -/
theorem build_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    build (ofGraph G) = TwoBoundary.BinaryFrontend.ofFinite
      (finiteExclusions G) (finiteCoverage G) := by
  have hn : order (ofGraph G) = n := rfl
  simp only [build, exclusions, coverage, hn, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.map_map, Function.comp_def, TwoBoundary.BinaryFrontend.ofFinite,
    CNF.relabel, finiteExclusions, finiteCoverage, List.map_flatMap]
  apply congrArg (fun z : CNF ℕ × List (DNF ℕ) => (n, z))
  apply Prod.ext <;> dsimp only
  · congr 1
    funext u
    congr 1
    funext v
    simp only [adjacent_ofGraph, decide_eq_true_eq]
    split_ifs <;> simp [Clause.relabel]
  · congr 1
    funext u
    simp only [List.filter_map, List.map_map, Function.comp_def, adjacent_ofGraph,
      Fin.val_inj]
    rfl

/-- Side width is two and every term has width one, uniformly over graph density. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
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

/-- Independence and closed-neighborhood coverage are precisely the original selected-set
predicate, with no certificate/marking multiplicity. -/
theorem finite_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteExclusions G).eval σ = true ∧
        (∀ p ∈ finiteCoverage G, DNF.eval σ p = true) ↔
      G.IsIndepSet {u | σ u = true} ∧
        ∀ u, σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true := by
  have he (u v : Fin n) :
      CNF.eval σ (if G.Adj u v then [[(u, false), (v, false)]] else []) = true ↔
        (G.Adj u v → σ u = false ∨ σ v = false) := by
    by_cases ha : G.Adj u v <;> simp [ha, CNF.eval, Clause.eval, Literal.eval]
  have hB : (finiteExclusions G).eval σ = true ↔
      ∀ u v, G.Adj u v → σ u = false ∨ σ v = false := by
    simp only [finiteExclusions, CNF.eval_flatMap_eq_true_iff, List.mem_finRange,
      forall_true_left, he]
  have hI : (∀ u v, G.Adj u v → σ u = false ∨ σ v = false) ↔
      G.IsIndepSet {u | σ u = true} := by
    constructor
    · intro h u hu v hv _ ha
      rcases h u v ha with hz | hz <;> simp_all
    · intro h u v ha
      by_cases hu : σ u = true
      · by_cases hv : σ v = true
        · exact False.elim (h hu hv (G.ne_of_adj ha) ha)
        · exact Or.inr (Bool.eq_false_iff.mpr hv)
      · exact Or.inl (Bool.eq_false_iff.mpr hu)
  rw [hB, hI]
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
theorem finiteCoverage_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteCoverage G).length = n := by simp [finiteCoverage]

/-- Actual edge exclusions and neighborhood-term volume are quadratic even on dense graphs. -/
theorem volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
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

/-- Every actual graph query has the source's `2v-1` variables, width three and quadratic size.
At zero vertices the one-query branch is used, without a negative declaration. -/
theorem plan_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))) :
    N = 2 * n - 1 ∧ q.length ≤ 3 * n ^ 2 ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  rw [build_ofGraph] at hq
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
/-- Actual emitted-plan count equals the number of independent dominating selections, retaining
all declared vertices and requiring no marking, witness or output advice. -/
theorem plan_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile (build (ofGraph G))) =
      Fintype.card {σ : Fin n → Bool // G.IsIndepSet {u | σ u = true} ∧
        ∀ u, σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true} := by
  classical
  rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics G))

end Cslib.Logic.PL.IndependentDomination
