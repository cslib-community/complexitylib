/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.IndependentDominationInterval
public import Complexity.Computability.PolyTime.CNF.DominatingInducedMatching
public import Complexity.Foundations.Combinatorics.SimpleGraph.InducedMatching
import all Complexity.Computability.PolyTime.CNF.IndependentDominationInterval
import Complexity.Logics.Propositional.DNF.Relabel
import all Complexity.Computability.PolyTime.CNF.DominatingInducedMatching

/-!
# Original-graph induced matching counts with computed size tests

Use the actual degree-one upper clauses and selected-neighbor conditions, omitting the edge-cover
clauses required only by dominating induced matching. Append a functional cardinality circuit on
original vertices. The input is the existing explicit matrix / binary natural interval frame;
no rank, output, graph reduction or resource advice is supplied. The circuit counts endpoints;
`plan_count` proves that this is twice the unordered edge count of an actual induced matching.
This is the construction of [ChenJiangZhu2027], Proposition D.1 (PDF pp. 33–34).

## Main results

* `build_polytime`: actual matrix traversal, size-circuit generation and binary query-input writes.
* `representation`: exactly one gate extension per original matching support.
* `plan_count`: actual ordinary-query plan counts matching subgraphs with the specified size test.
* `Maximum.prepare_polytime`: compute the endpoint interval from the signed binary edge threshold.
-/

public section

namespace Cslib.Logic.PL.InducedMatchingInterval

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean
open IndependentDominationInterval

/-- Actual degree-one constraints and functional size test, without any domination constraint. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (IndependentDomination.order (graph x) + auxiliary x,
    DominatingInducedMatching.upper (graph x) ++ CardinalityInterval.formula (cardinalityInput x),
    DominatingInducedMatching.conditions (graph x))

/-- Binary polynomial resources for the complete original-matrix/size-test construction. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold IndependentDomination.order graph encInput IndependentDomination.encInput
    fun_prop
  have hB := DominatingInducedMatching.upper_polytime.comp hg
  have hP := DominatingInducedMatching.conditions_polytime.comp hg
  have hC := CardinalityInterval.formula_polytime.comp cardinalityInput_polytime
  exact ((ComputableInPolyTime.unary_add.comp (hn.prod auxiliary_polytime)).prod
    ((ComputableInPolyTime.listAppend' hB hC).prod hP)).of_enc_eq fun _ => rfl

/-- Erasing finite original columns gives the actual upper-clause list, in its traversal order. -/
theorem upper_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    DominatingInducedMatching.upper (IndependentDomination.ofGraph G) =
      (DominatingInducedMatching.finiteUpper G).relabel Fin.val := by
  have hn : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
  simp only [DominatingInducedMatching.upper, DominatingInducedMatching.finiteUpper, hn,
    ← List.map_coe_finRange_eq_range, List.flatMap_map, CNF.relabel, List.map_flatMap]
  congr 1
  funext u
  congr 1
  funext a
  congr 1
  funext b
  simp only [IndependentDomination.adjacent_ofGraph, Bool.and_eq_true,
    decide_eq_true_eq, ne_eq, Fin.val_inj, and_assoc]
  split_ifs <;> rfl

open Classical in
/-- The actual source input has a finite presentation with proved widths and exact original
count. All circuit/auxiliary data are computed; these witnesses are semantic proof objects only. -/
theorem representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ) :
    let a := (CardinalityInterval.circuit n lo hi).size
    ∃ B : CNF (Fin (n + a)), ∃ P : List (DNF (Fin (n + a))),
      build (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ 1) ∧ P.length = n ∧
      Fintype.card {y : Fin (n + a) → Bool // B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {x : Fin n → Bool // ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching ∧
          lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} := by
  generalize hc : CardinalityInterval.circuit n lo hi = c
  let a := c.size
  let ι : Fin n → Fin (n + a) := Fin.castAdd a
  obtain ⟨hCsize, hCbounds⟩ := CardinalityInterval.formula_bounds n lo hi
  rw [hc] at hCbounds
  obtain ⟨F, hF⟩ := lift_cnf (CardinalityInterval.formula (n, lo, hi))
    (fun q hq => (hCbounds q hq).2)
  let B := (DominatingInducedMatching.finiteUpper G).relabel ι ++ F
  let P := (DominatingInducedMatching.finiteConditions G).map (CNF.relabel ι)
  have hG := DominatingInducedMatching.build_ofGraph G
  have hBG := upper_ofGraph G
  have hPG := congrArg TwoBoundary.BinaryFrontend.conditions hG
  change DominatingInducedMatching.upper (IndependentDomination.ofGraph G) =
    (DominatingInducedMatching.finiteUpper G).relabel Fin.val at hBG
  change DominatingInducedMatching.conditions (IndependentDomination.ofGraph G) =
    (DominatingInducedMatching.finiteConditions G).map (CNF.relabel Fin.val) at hPG
  have herase (D : CNF (Fin n)) : CNF.relabel Fin.val (D.relabel ι) = D.relabel Fin.val := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    congr 1
  have hNF : CNF.relabel Fin.val B = DominatingInducedMatching.upper
      (IndependentDomination.ofGraph G) ++ CardinalityInterval.formula (n, lo, hi) := by
    change (List.map (Clause.relabel Fin.val)
      ((DominatingInducedMatching.finiteUpper G).relabel ι ++ F)) = _
    rw [List.map_append]
    change CNF.relabel Fin.val ((DominatingInducedMatching.finiteUpper G).relabel ι) ++
      CNF.relabel Fin.val F = _
    rw [herase, hF, hBG]
  have hPF : P.map (CNF.relabel Fin.val) =
      DominatingInducedMatching.conditions (IndependentDomination.ofGraph G) := by
    rw [hPG]
    simp only [P, List.map_map, Function.comp_def, herase]
  have haux := auxiliary_ofGraph G lo hi
  rw [hc] at haux
  have horder : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
  have hcard : cardinalityInput (ofGraph G lo hi) = (n, lo, hi) := rfl
  have hgraph : graph (ofGraph G lo hi) = IndependentDomination.ofGraph G := rfl
  refine ⟨B, P, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [build, hgraph, hcard, horder, haux, TwoBoundary.BinaryFrontend.ofFinite]
    rw [← hNF, ← hPF]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
      simpa only [Clause.relabel, List.length_map] using
        (DominatingInducedMatching.widths G).1 u (List.mem_append_left _ hu)
    · have hq' : q.relabel Fin.val ∈ CardinalityInterval.formula (n, lo, hi) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      have hlen := (hCbounds _ hq').1
      simp only [Clause.relabel, List.length_map] at hlen
      omega
  · intro p hp t ht
    change p ∈ (DominatingInducedMatching.finiteConditions G).map (CNF.relabel ι) at hp
    obtain ⟨p0, hp0, heq⟩ := List.mem_map.mp hp
    rw [← heq] at ht
    change t ∈ p0.map (Clause.relabel ι) at ht
    obtain ⟨t0, ht0, hteq⟩ := List.mem_map.mp ht
    rw [← hteq]
    simpa only [Clause.relabel, List.length_map] using
      (DominatingInducedMatching.widths G).2 p0 hp0 t0 ht0
  · simp only [P, List.length_map, DominatingInducedMatching.finiteConditions_length]
  · simp only [← Nat.card_eq_fintype_card]
    have hPred (y : Fin (n + a) → Bool) :
        B.eval y = true ∧ (∀ p ∈ P, DNF.eval y p = true) ↔
        (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) = true ∧
          ((⊤ : G.Subgraph).induce {u | y (ι u) = true}).IsMatching := by
      have hFE : F.eval y = (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) := by
        rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
      have hPE : (∀ p ∈ P, DNF.eval y p = true) ↔
          ∀ p ∈ DominatingInducedMatching.finiteConditions G, DNF.eval (y ∘ ι) p = true := by
        constructor
        · intro h p hp
          have hmem : CNF.relabel ι p ∈ P := List.mem_map.mpr ⟨p, hp, rfl⟩
          have ht := h _ hmem
          rwa [DNF.eval_relabel] at ht
        · intro h p hp
          change p ∈ (DominatingInducedMatching.finiteConditions G).map (CNF.relabel ι) at hp
          obtain ⟨p0, hp0, heq⟩ := List.mem_map.mp hp
          rw [← heq, DNF.eval_relabel]
          exact h p0 hp0
      simp only [B, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, hFE, hPE]
      rw [← DominatingInducedMatching.regular_semantics G (fun u => y (ι u))]
      tauto
    have haccept (x : Fin n → Bool) : c.eval interpretation x = CardinalityInterval.wanted ↔
        lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
      have h := CardinalityInterval.circuit_accepts n lo hi x
      rwa [hc] at h
    calc
      _ = Nat.card {y : Fin (n + c.size) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val y (fun _ => false)) = true ∧
              ((⊤ : G.Subgraph).induce {u | y (Fin.castAdd c.size u) = true}).IsMatching} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro y
        simpa only [CardinalityInterval.formula, CardinalityInterval.payload_eq, hc] using hPred y
      _ = Nat.card {x : Fin n → Bool // c.eval interpretation x = CardinalityInterval.wanted ∧
          ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching} :=
        by
          have h := FunctionalCNF.count_extensions c CardinalityInterval.wanted
            (fun x => ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching)
          simpa only [← Nat.card_eq_fintype_card] using h
      _ = _ := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        rw [haccept]
        constructor
        · rintro ⟨⟨hl, hu⟩, hm⟩
          exact ⟨hm, hl, hu⟩
        · rintro ⟨hm, hl, hu⟩
          exact ⟨⟨hl, hu⟩, hm⟩

/-- Nonempty original graphs write exactly the source's two ordinary boundary queries. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi)))).length = 2 := by
  have hlen : (TwoBoundary.BinaryFrontend.conditions (build (ofGraph G lo hi))).length = n := by
    simp only [build, TwoBoundary.BinaryFrontend.conditions, graph, ofGraph,
      DominatingInducedMatching.conditions, IndependentDomination.ofGraph,
        IndependentDomination.order,
      List.length_map, List.length_range]
  have hem : (TwoBoundary.BinaryFrontend.conditions (build (ofGraph G lo hi))).isEmpty ≠ true := by
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  simp only [TwoBoundary.BinaryFrontend.compile, hem, Bool.false_eq_true, ↓reduceIte,
    TwoBoundary.BinaryFrontend.queries, List.length_cons, List.length_nil]

/-- Actual positive-vertex query budgets, including the computed linear size-test variables.
The number of clauses remains cubic, with every functional gate clause included. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi)))) :
    N = 2 * n + (CardinalityInterval.circuit n lo hi).size - 1 ∧
      q.length ≤ n ^ 3 + 3 * n ^ 2 + 2 * n + 2 + 2856 * (n + 1) ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, hbuild, hb, hp, hplen, _⟩ := representation G lo hi
  rw [hbuild] at hq
  obtain ⟨hN, hM, hW⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N q hq
  have hem : P.isEmpty ≠ true := by
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte] at hN
  have hB := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length) hbuild
  change (DominatingInducedMatching.upper (IndependentDomination.ofGraph G) ++
      CardinalityInterval.formula (n, lo, hi)).length =
      (CNF.relabel Fin.val B).length at hB
  simp only [List.length_append, CNF.relabel, List.length_map] at hB
  have hBG := congrArg List.length (upper_ofGraph G)
  change (DominatingInducedMatching.upper (IndependentDomination.ofGraph G)).length =
    (CNF.relabel Fin.val (DominatingInducedMatching.finiteUpper G)).length at hBG
  simp only [CNF.relabel, List.length_map] at hBG
  have hP := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum)
    hbuild
  change ((DominatingInducedMatching.conditions (IndependentDomination.ofGraph G)).map
    List.length).sum =
    ((P.map (CNF.relabel Fin.val)).map List.length).sum at hP
  have hPG := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum)
    (DominatingInducedMatching.build_ofGraph G)
  change ((DominatingInducedMatching.conditions (IndependentDomination.ofGraph G)).map
    List.length).sum =
    (((DominatingInducedMatching.finiteConditions G).map (CNF.relabel Fin.val)).map
      List.length).sum at hPG
  simp only [List.map_map, CNF.relabel, List.length_map, Function.comp_def] at hP hPG
  change ((DominatingInducedMatching.conditions (IndependentDomination.ofGraph G)).map
    List.length).sum =
    (P.map List.length).sum at hP
  change ((DominatingInducedMatching.conditions (IndependentDomination.ofGraph G)).map
    List.length).sum =
    ((DominatingInducedMatching.finiteConditions G).map List.length).sum at hPG
  have hs := CardinalityInterval.formula_bounds n lo hi |>.1
  obtain ⟨hside, hterms⟩ := DominatingInducedMatching.volumes G
  simp only [List.length_append] at hside
  refine ⟨by omega, by nlinarith, by simpa using hW⟩

/-- The source cubic clause bound, including every generated functional gate clause. -/
theorem query_cubic_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi)))) : q.length ≤ 6000 * n ^ 3 :=
        by
  have h := (query_budget G lo hi hn N q hq).2.1
  have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      _ = n ^ 3 := by ring
  nlinarith

open Classical in
/-- The actual query plan counts each conventional induced matching once; the interval tests
endpoints, which are exactly twice its number of unordered edges. This includes empty graphs. -/
theorem plan_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ) :
    TwoBoundary.BinaryFrontend.value
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi))) =
      Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧
        lo ≤ 2 * Nat.card M.edgeSet ∧ 2 * Nat.card M.edgeSet ≤ hi} := by
  obtain ⟨B, P, he, hb, hp, _, hc⟩ := representation G lo hi
  rw [he, TwoBoundary.BinaryFrontend.compile_count, hc]
  simpa only [Nat.card_eq_fintype_card] using
    SimpleGraph.card_inducedMatching_supports_eq G (fun w => lo ≤ w ∧ w ≤ hi)

namespace Maximum

/-- Original explicit adjacency matrix and varying signed binary edge threshold. -/
abbrev Input := IndependentDomination.Input × ℤ
/-- Original graph frame, retaining its declared unused vertices. -/
@[expose] def graph (x : Input) := x.1
/-- Inclusive lower bound on the number of matching edges. -/
@[expose] def threshold (x : Input) := x.2
/-- Unary vertex declaration, framed adjacency cells and signed binary threshold. -/
@[expose] def encInput : Input ↪ List Bool := encPair IndependentDomination.encInput encIntBin
/-- Compute the endpoint-size interval. Negative thresholds accept all matching sizes;
oversized binary thresholds are capped by the actual cardinality generator before unary work. -/
@[expose] def prepare (x : Input) : IndependentDominationInterval.Input :=
  (graph x, (2 * threshold x).toNat, IndependentDomination.order (graph x))
/-- Canonical original graph and signed edge threshold, without supplied circuit data. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) : Input := (IndependentDomination.ofGraph G, k)

/-- Actual binary multiplication, sign normalization and original-declaration conversion. -/
@[fun_prop] theorem prepare_polytime : ComputableInPolyTime prepare encInput
    IndependentDominationInterval.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hk : ComputableInPolyTime threshold encInput encIntBin := by
    unfold threshold encInput; fun_prop
  have hlo := (ComputableInPolyTime.intBin_toNat).comp
    (ComputableInPolyTime.intBin_mul' (ComputableInPolyTime.const 2) hk)
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold IndependentDomination.order graph encInput IndependentDomination.encInput; fun_prop
  exact (hg.prod (hlo.prod (ComputableInPolyTime.unary_to_binary.comp hn))).of_enc_eq fun _ => rfl

open Classical in
/-- A threshold on edges is precisely the computed natural endpoint interval, including negative,
oversized and empty cases. The upper test removes no actual support. -/
theorem count_correspondence {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℤ) :
    Fintype.card {x : Fin n → Bool //
      ((⊤ : G.Subgraph).induce {u | x u = true}).IsMatching ∧
        (2 * k).toNat ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ n} =
      Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ (k ≤ (Nat.card M.edgeSet : ℤ))} := by
  have he := SimpleGraph.card_inducedMatching_supports_eq G
    (fun w => (2 * k).toNat ≤ w ∧ w ≤ n)
  rw [← Nat.card_eq_fintype_card]
  refine he.trans (Nat.card_congr (Equiv.subtypeEquivRight fun M => ?_))
  have hb : Nat.card M.verts ≤ n := by
    have h := Nat.card_le_card_of_injective (Subtype.val : M.verts → Fin n) Subtype.val_injective
    simpa only [Nat.card_fin] using h
  constructor
  · rintro ⟨hm, hi, hlo, _⟩
    have hcast := Int.toNat_le.mp hlo
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hk⟩
    refine ⟨hm, hi, ?_, ?_⟩
    · apply Int.toNat_le.mpr
      omega
    · rwa [← hm.card_verts_eq_twice_edges]

end Maximum

end Cslib.Logic.PL.InducedMatchingInterval
