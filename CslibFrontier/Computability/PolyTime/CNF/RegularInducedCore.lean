/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.SigmaRho
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import all CslibFrontier.Computability.PolyTime.CNF.DegreeThreshold
import all CslibFrontier.Computability.PolyTime.CNF.WeightedQuery

/-!
# Compact regular induced-subgraph core

The threshold-free core of [ChenJiangZhu2027], Proposition C.2 (PDF pp.32–33). It uses only
original selection variables, with no degree-threshold bits or subset witnesses. Fixed-length
neighbor sublists are enumerated directly, with the existing binary machine certificate.
Size-test gates and the complete source resource endpoint are separate frontend obligations.

## Main definitions

* `upper`, `conditions`, `build`: actual original-matrix construction for fixed degree.
* `finiteUpper`, `finiteConditions`: finite versions on the original selected vertices.

## Main results

* `build_polytime`: actual bounded enumeration and binary literal writing.
* `finite_semantics`, `plan_count`: exact original-selection regularity and no-size counts.
* `query_budget`: compact no-size declaration, widths, clause volumes and literal indices.
-/

public section

namespace Cslib.Logic.PL.RegularInducedCore

open Turing.MultiTapeTM IndependentDomination

/-- A selected vertex cannot have a selected `(d+1)`-element neighbor set. -/
@[expose] def upper (d : ℕ) (g : Input) : CNF ℕ :=
  (List.range (order g)).flatMap fun u =>
    ((DegreeThreshold.neighbors g u).sublistsLen (d + 1)).map fun t =>
      Term.negate ((u, true) :: t.map fun v => (v, true))

/-- An unselected vertex is accepted; otherwise exactly d neighbors witness the lower bound. -/
@[expose] def conditions (d : ℕ) (g : Input) : List (DNF ℕ) :=
  (List.range (order g)).map fun u => [[(u, false)]] ++
    ((DegreeThreshold.neighbors g u).sublistsLen d).map fun t => t.map fun v => (v, true)

/-- The compact no-size-test core allocates no variables beyond original selections. -/
@[expose] def build (d : ℕ) (g : Input) : TwoBoundary.BinaryFrontend.Input :=
  (order g, upper d g, conditions d g)

/-- The finite upper-degree clauses, with the same neighbor/sublist ordering. -/
@[expose] def finiteUpper {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    CNF (Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((DegreeThreshold.finiteNeighbors G u).sublistsLen (d + 1)).map fun t =>
      Term.negate ((u, true) :: t.map fun v => (v, true))

/-- Exactly one finite lower-degree predicate per vertex, sharing all selection bits. -/
@[expose] def finiteConditions {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : List (DNF (Fin n)) :=
  (List.finRange n).map fun u => [[(u, false)]] ++
    ((DegreeThreshold.finiteNeighbors G u).sublistsLen d).map fun t => t.map fun v => (v, true)

private theorem candidates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (u : Fin n) (d : ℕ) :
    (∃ t ∈ (DegreeThreshold.finiteNeighbors G u).sublistsLen d,
      Term.eval x (t.map fun v => (v, true)) = true) ↔ d ≤ DegreeThreshold.count G x u := by
  simpa [Term.eval, Literal.eval, DegreeThreshold.count] using
      DegreeThreshold.selected_sublists (DegreeThreshold.finiteNeighbors G u) x d

/-- Both local tests apply only to selected vertices; unselected vertices have no degree rule. -/
theorem finite_semantics {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    ((finiteUpper d G).eval x = true ∧
      ∀ p ∈ finiteConditions d G, DNF.eval x p = true) ↔
        G.IsSigmaRhoSet {d} Set.univ {u | x u = true} := by
  have hupper : (finiteUpper d G).eval x = true ↔
      ∀ u, x u = true → DegreeThreshold.count G x u ≤ d := by
    simp only [finiteUpper, CNF.eval, List.all_flatMap, List.all_map, List.all_eq_true,
      List.mem_finRange, forall_const, Function.comp_def, Term.eval_negate]
    constructor
    · intro h u hu
      have hno : ¬ ∃ t ∈ (DegreeThreshold.finiteNeighbors G u).sublistsLen (d + 1),
          Term.eval x (t.map fun v => (v, true)) = true := by
        rintro ⟨t, ht, hx⟩
        have hc := h u t ht
        simp [Term.eval_cons, Literal.eval, hu, hx] at hc
      have hc := (candidates G x u (d + 1)).not.mp hno
      omega
    · intro h u t ht
      have hc := (candidates G x u (d + 1)).mp
      by_cases hx : x u = true
      · have hfalse : Term.eval x (t.map fun v => (v, true)) = false := by
          apply Bool.eq_false_iff.mpr
          intro he
          have := hc ⟨t, ht, he⟩
          have := h u hx
          omega
        simp [Term.eval_cons, Literal.eval, hx, hfalse]
      · simp [Term.eval_cons, Literal.eval, hx]
  have hlower : (∀ p ∈ finiteConditions d G, DNF.eval x p = true) ↔
      ∀ u, x u = true → d ≤ DegreeThreshold.count G x u := by
    simp only [finiteConditions, List.forall_mem_map, List.mem_finRange, forall_const]
    apply forall_congr'
    intro u
    have he : DNF.eval x ([[(u, false)]] ++
        ((DegreeThreshold.finiteNeighbors G u).sublistsLen d).map
          (fun t => t.map fun v => (v, true))) = true ↔
        x u = false ∨ d ≤ DegreeThreshold.count G x u := by
      simp only [DNF.eval, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true, List.any_map, List.any_eq_true, Function.comp_def]
      change (Term.eval x [(u, false)] = true ∨
        ∃ t ∈ (DegreeThreshold.finiteNeighbors G u).sublistsLen d,
          Term.eval x (t.map fun v => (v, true)) = true) ↔ _
      rw [candidates]
      simp [Term.eval, Literal.eval]
    rw [he]
    cases hx : x u <;> simp
  rw [hupper, hlower]
  simp only [SimpleGraph.IsSigmaRhoSet, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Set.mem_univ, implies_true, and_true, ← SigmaRho.count_eq_selectedDegree]
  constructor
  · rintro ⟨hu, hl⟩ u hx
    exact (hu u hx).antisymm (hl u hx)
  · intro h
    exact ⟨fun u hu => (h u hu).le, fun u hu => (h u hu).ge⟩

private theorem upper_polytime (d : ℕ) :
    ComputableInPolyTime (upper d) encInput VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  have ht := (Cslib.sublistsLen_polytime encUnary 0 (d + 1)).comp
    DegreeThreshold.neighbors_polytime
  have hpos := DegreeThreshold.signedTerm_polytime true
  have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair encInput encUnary) encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  unfold upper
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.mapWithInput ht
  have hhead := hu.comp (ComputableInPolyTime.fst _ (encList encUnary))
  have htail := hpos.comp (ComputableInPolyTime.snd (encPair encInput encUnary) (encList encUnary))
  have hterm : ComputableInPolyTime
      (fun p : (Input × ℕ) × List ℕ => (p.1.2, true) :: p.2.map fun v => (v, true))
      (encPair (encPair encInput encUnary) (encList encUnary))
      (encList (encPair encNat encBool)) := by fun_prop
  exact ((Literal.computableInPolyTime_negate encNat).map.comp hterm).of_enc_eq fun _ => rfl

private theorem conditions_polytime (d : ℕ) :
    ComputableInPolyTime (conditions d) encInput (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  have ht := (Cslib.sublistsLen_polytime encUnary 0 d).comp DegreeThreshold.neighbors_polytime
  have hp : ComputableInPolyTime
      (fun p : Input × ℕ => ((DegreeThreshold.neighbors p.1 p.2).sublistsLen d).map
        fun t => t.map fun v => (v, true)) (encPair encInput encUnary) VCOne.encSignedCNF :=
    ComputableInPolyTime.mapWithInput ht
      ((DegreeThreshold.signedTerm_polytime true).comp (ComputableInPolyTime.snd _ _))
  have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2)
      (encPair encInput encUnary) encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hf : ComputableInPolyTime (fun p : Input × ℕ => [[(p.2, false)]])
      (encPair encInput encUnary) VCOne.encSignedCNF := by unfold VCOne.encSignedCNF; fun_prop
  unfold conditions
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
    (ComputableInPolyTime.listAppend' hf hp)

/-- Actual fixed-degree enumeration and all binary literal writes have polynomial resources.
The degree is fixed, never an input-dependent enumeration dimension. -/
theorem build_polytime (d : ℕ) : ComputableInPolyTime (build d) encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  exact hn.prod ((upper_polytime d).prod (conditions_polytime d))

/-- Erasing the finite constructor gives exactly the original encoded graph traversal. -/
theorem build_ofGraph {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    build d (ofGraph G) = TwoBoundary.BinaryFrontend.ofFinite (finiteUpper d G)
      (finiteConditions d G) := by
  have hu : upper d (ofGraph G) = (finiteUpper d G).relabel Fin.val := by
    simp only [upper, finiteUpper, order, ofGraph, ← List.map_coe_finRange_eq_range,
      List.flatMap_map, CNF.relabel, List.map_flatMap]
    congr 1
    funext u
    change ((DegreeThreshold.neighbors (ofGraph G) u.val).sublistsLen (d + 1)).map
      (fun t => Term.negate ((u.val, true) :: t.map fun v => (v, true))) = _
    rw [DegreeThreshold.neighbors_ofGraph G u, WeightedRow.BinaryQuery.sublistsLen_map]
    simp only [List.map_map, Function.comp_def, Clause.relabel, Term.negate, List.map_cons]
    rfl
  have hp : conditions d (ofGraph G) = (finiteConditions d G).map (CNF.relabel Fin.val) := by
    simp only [conditions, finiteConditions, order, ofGraph, ← List.map_coe_finRange_eq_range,
      List.map_map, Function.comp_def]
    congr 1
    funext u
    change [[(u.val, false)]] ++ ((DegreeThreshold.neighbors (ofGraph G) u.val).sublistsLen d).map
      (fun t => t.map fun v => (v, true)) = _
    rw [DegreeThreshold.neighbors_ofGraph G u, WeightedRow.BinaryQuery.sublistsLen_map]
    simp only [CNF.relabel, List.map_append, List.map_cons, List.map_nil, List.map_map,
      Clause.relabel, Function.comp_def]
    rfl
  change (_, upper d (ofGraph G), conditions d (ofGraph G)) = _
  rw [hu, hp]
  rfl

open Classical in
/-- Without a size test the actual plan counts original regular selection words exactly.
No threshold-bit or subset-witness multiplicity is introduced. -/
theorem plan_count {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G))) =
        Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true}} := by
  rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics d G))

/-- Exactly the source widths and one lower predicate per original vertex, for positive degree. -/
theorem widths {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (∀ c ∈ finiteUpper d G, c.length ≤ d + 2) ∧
      (∀ p ∈ finiteConditions d G, ∀ t ∈ p, t.length ≤ d) ∧
      (finiteConditions d G).length = n := by
  refine ⟨?_, ?_, by simp [finiteConditions]⟩
  · intro c hc
    obtain ⟨u, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have hl := (List.mem_sublistsLen.mp ht).2
    simp [Term.negate, hl]
  · intro p hp t ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp ht with ht | ht
    · obtain rfl := List.mem_singleton.mp ht
      simpa using hd
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      simpa only [List.length_map] using (List.mem_sublistsLen.mp ha).2.le

/-- Candidate volume is polynomial in the original declaration for fixed degree. -/
theorem volumes {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteUpper d G).length ≤ n ^ (d + 2) ∧
      ((finiteConditions d G).map List.length).sum ≤ n + n ^ (d + 1) := by
  have hc (u : Fin n) (k : ℕ) :
      ((DegreeThreshold.finiteNeighbors G u).sublistsLen k).length ≤ n ^ k := by
    rw [List.length_sublistsLen]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left
      ((List.length_filter_le _ _).trans (by simp)) k)
  constructor
  · simp only [finiteUpper, List.length_flatMap, List.length_map, List.finRange,
      List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc _ ≤ ∑ u : Fin n, n ^ (d + 1) := Finset.sum_le_sum fun u _ => hc u _
      _ = n ^ (d + 2) := by simp; ring
  · simp only [finiteConditions, List.length_append, List.length_map,
      List.length_cons, List.length_nil, List.finRange, List.map_ofFn, List.sum_ofFn,
      Function.comp_def]
    calc _ ≤ ∑ u : Fin n, (1 + n ^ d) :=
        Finset.sum_le_sum fun u _ => Nat.add_le_add_left (hc u d) 1
      _ = n + n ^ (d + 1) := by simp; ring

/-- The actual no-size core emits the compact source declaration, fixed width, polynomial clause
volume and validated indices. Size-test gates are not included in this core theorem. -/
theorem query_budget {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G)))) :
    N = 2 * n - 1 ∧ q.length ≤ n ^ (d + 2) + 2 * (n + n ^ (d + 1)) ∧
      ∀ c ∈ q, c.length ≤ d + 2 ∧ ∀ l ∈ c, l.1 < N := by
  rw [build_ofGraph] at hq
  obtain ⟨hb, hp, hl⟩ := widths d hd G
  obtain ⟨hN, hM, hW⟩ := TwoBoundary.BinaryFrontend.compile_budget
    (finiteUpper d G) (finiteConditions d G) hb hp N q hq
  obtain ⟨hB, hP⟩ := volumes d G
  refine ⟨?_, by omega, by simpa only [Nat.max_self] using hW⟩
  split_ifs at hN with he
  · have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  · omega

end Cslib.Logic.PL.RegularInducedCore
