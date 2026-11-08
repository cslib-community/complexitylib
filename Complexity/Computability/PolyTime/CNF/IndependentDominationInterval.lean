/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.IndependentDomination
public import Complexity.Computability.PolyTime.CNF.CardinalityInterval
import all Complexity.Computability.PolyTime.CNF.VCOneDispatch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# Actual original-graph independent domination with input size bounds

Append the computed functional cardinality test to the original edge exclusions, sharing only
original vertex inputs, then use the existing generic DNF constructor. The interval bounds are
binary inputs. Every accepted original vertex selection has exactly one gate extension.
This is the size-test independent-domination specialization of [ChenJiangZhu2027], Corollary 7.2
and Appendix D.4, Proposition D.3 (PDF pp. 25, 36), rather than a supplied graph reduction.

## Main definitions

* `build`: actual graph exclusions, functional size test and neighborhood conditions.
* `Signed.run`: signed binary normalization with direct empty-graph dispatch.

## Main results

* `representation`: the actual constructed input counts original selections exactly once.
* `query_count`: positive-vertex inputs emit exactly two ordinary queries.
* `query_budget`: source variable/width/clause bounds, including computed gate variables.
-/

public section

namespace Cslib.Logic.PL.IndependentDominationInterval

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-- Original explicit adjacency matrix and binary inclusive size bounds. -/
abbrev Input := IndependentDomination.Input × ℕ × ℕ
/-- Original graph input, retaining the original declaration. -/
@[expose] def graph : Input → IndependentDomination.Input | (g, _, _) => g
/-- Inclusive binary lower bound. -/
@[expose] def lower : Input → ℕ | (_, lo, _) => lo
/-- Inclusive binary upper bound. -/
@[expose] def upper : Input → ℕ | (_, _, hi) => hi
/-- Explicit matrix and binary size-bound framing. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encNat encNat)
/-- Compute the original declaration and input bounds for the actual size-test generator. -/
@[expose] def cardinalityInput (x : Input) : CardinalityInterval.Input :=
  (IndependentDomination.order (graph x), lower x, upper x)
/-- Count the generated gate variables, without accepting a supplied size bound. -/
@[expose] def auxiliary (x : Input) : ℕ :=
  let (gs, _) := CardinalityInterval.generate (cardinalityInput x)
  gs.length
/-- Actual full graph/size-test DNF input, with every auxiliary gate constrained functionally. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (IndependentDomination.order (graph x) + auxiliary x,
    IndependentDomination.exclusions (graph x) ++ CardinalityInterval.formula (cardinalityInput x),
    IndependentDomination.coverage (graph x))

private theorem cardinalityInput_polytime : ComputableInPolyTime cardinalityInput encInput
    CardinalityInterval.encInput := by
  unfold cardinalityInput graph lower upper encInput IndependentDomination.order
    IndependentDomination.encInput CardinalityInterval.encInput
  fun_prop

private theorem auxiliary_polytime : ComputableInPolyTime auxiliary encInput encUnary := by
  have hcode := CardinalityInterval.generate_polytime.comp cardinalityInput_polytime
  have h := (ComputableInPolyTime.length_list encGate).comp hcode.fst'
  exact h.of_enc_eq fun _ => rfl

/-- Polynomial binary resources for the actual size-constrained graph constructor. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hG := IndependentDomination.build_polytime.comp hg
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold IndependentDomination.order graph encInput IndependentDomination.encInput
    fun_prop
  have hB : ComputableInPolyTime (fun x => IndependentDomination.exclusions (graph x))
      encInput VCOne.encSignedCNF := hG.snd'.fst'
  have hP : ComputableInPolyTime (fun x => IndependentDomination.coverage (graph x))
      encInput (encList VCOne.encSignedCNF) := hG.snd'.snd'
  have hC := CardinalityInterval.formula_polytime.comp cardinalityInput_polytime
  have h := (ComputableInPolyTime.unary_add.comp (hn.prod auxiliary_polytime)).prod
    ((ComputableInPolyTime.listAppend' hB hC).prod hP)
  exact h.of_enc_eq fun _ => rfl

/-- The canonical explicit simple undirected graph with the original binary size bounds. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) : Input := (IndependentDomination.ofGraph G, lo, hi)

/-- The actual auxiliary declaration is the size of the computed cardinality circuit. -/
theorem auxiliary_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) : auxiliary (ofGraph G lo hi) = (CardinalityInterval.circuit n lo hi).size := by
  simp only [auxiliary, ofGraph, cardinalityInput, graph, lower, upper,
    IndependentDomination.ofGraph, IndependentDomination.order, CardinalityInterval.generate_eq]
  exact Circuit.length_code_fst _

private theorem lift_cnf {N : ℕ} (C : CNF ℕ) (hv : ∀ c ∈ C, ∀ l ∈ c, l.1 < N) :
    ∃ F : CNF (Fin N), CNF.relabel Fin.val F = C := by
  classical
  choose f hf using (fun c : {c // c ∈ C} => VCOne.BinaryFrontend.lift_clause
    (hv c.val c.property))
  refine ⟨C.attach.map f, ?_⟩
  simp only [CNF.relabel, List.map_map, Function.comp_def]
  calc _ = C.attach.map Subtype.val := List.map_congr_left fun c _ => hf c
    _ = C := by simpa only [List.map_id, id_eq] using
        (List.attach_map_val (l := C) (f := id))

private theorem eval_dnf_relabel {V W : Type} (f : V → W) (σ : W → Bool) (p : DNF V) :
    DNF.eval σ (CNF.relabel f p) = DNF.eval (σ ∘ f) p := by
  simp only [DNF.eval, CNF.relabel, List.any_map, Function.comp_def]
  congr 1
  funext t
  simp only [Term.eval, Clause.relabel, List.all_map, Function.comp_def]
  congr 1

open Classical in
/-- The actual source input has a finite presentation with proved widths and exact original
count. All circuit/auxiliary data are computed; these witnesses are semantic proof objects only. -/
theorem representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ) :
    let a := (CardinalityInterval.circuit n lo hi).size
    ∃ B : CNF (Fin (n + a)), ∃ P : List (DNF (Fin (n + a))),
      build (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ 1) ∧ P.length = n ∧
      Fintype.card {y : Fin (n + a) → Bool // B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {x : Fin n → Bool // G.IsIndepSet {u | x u = true} ∧
          (∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true) ∧
          lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} := by
  generalize hc : CardinalityInterval.circuit n lo hi = c
  let a := c.size
  let ι : Fin n → Fin (n + a) := Fin.castAdd a
  obtain ⟨hCsize, hCbounds⟩ := CardinalityInterval.formula_bounds n lo hi
  rw [hc] at hCbounds
  obtain ⟨F, hF⟩ := lift_cnf (CardinalityInterval.formula (n, lo, hi))
    (fun q hq => (hCbounds q hq).2)
  let B := (IndependentDomination.finiteExclusions G).relabel ι ++ F
  let P := (IndependentDomination.finiteCoverage G).map (CNF.relabel ι)
  have hG := IndependentDomination.build_ofGraph G
  have hBG := congrArg TwoBoundary.BinaryFrontend.side hG
  have hPG := congrArg TwoBoundary.BinaryFrontend.conditions hG
  change IndependentDomination.exclusions (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteExclusions G).relabel Fin.val at hBG
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hPG
  have herase (D : CNF (Fin n)) : CNF.relabel Fin.val (D.relabel ι) = D.relabel Fin.val := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    congr 1
  have hNF : CNF.relabel Fin.val B = IndependentDomination.exclusions
      (IndependentDomination.ofGraph G) ++ CardinalityInterval.formula (n, lo, hi) := by
    change (List.map (Clause.relabel Fin.val)
      ((IndependentDomination.finiteExclusions G).relabel ι ++ F)) = _
    rw [List.map_append]
    change CNF.relabel Fin.val ((IndependentDomination.finiteExclusions G).relabel ι) ++
      CNF.relabel Fin.val F = _
    rw [herase, hF, hBG]
  have hPF : P.map (CNF.relabel Fin.val) =
      IndependentDomination.coverage (IndependentDomination.ofGraph G) := by
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
        ((IndependentDomination.widths G).1 u hu).trans (by decide : 2 ≤ 3)
    · have hq' : q.relabel Fin.val ∈ CardinalityInterval.formula (n, lo, hi) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      have hlen := (hCbounds _ hq').1
      simp only [Clause.relabel, List.length_map] at hlen
      omega
  · intro p hp t ht
    change p ∈ (IndependentDomination.finiteCoverage G).map (CNF.relabel ι) at hp
    obtain ⟨p0, hp0, heq⟩ := List.mem_map.mp hp
    rw [← heq] at ht
    change t ∈ p0.map (Clause.relabel ι) at ht
    obtain ⟨t0, ht0, hteq⟩ := List.mem_map.mp ht
    rw [← hteq]
    simpa only [Clause.relabel, List.length_map] using
      (IndependentDomination.widths G).2 p0 hp0 t0 ht0
  · simp only [P, List.length_map, IndependentDomination.finiteCoverage_length]
  · simp only [← Nat.card_eq_fintype_card]
    have hPred (y : Fin (n + a) → Bool) :
        B.eval y = true ∧ (∀ p ∈ P, DNF.eval y p = true) ↔
        (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) = true ∧
          (G.IsIndepSet {u | y (ι u) = true} ∧
            ∀ u, y (ι u) = true ∨ ∃ v, G.Adj u v ∧ y (ι v) = true) := by
      have hFE : F.eval y = (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) := by
        rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
      have hPE : (∀ p ∈ P, DNF.eval y p = true) ↔
          ∀ p ∈ IndependentDomination.finiteCoverage G, DNF.eval (y ∘ ι) p = true := by
        constructor
        · intro h p hp
          have hmem : CNF.relabel ι p ∈ P := List.mem_map.mpr ⟨p, hp, rfl⟩
          have ht := h _ hmem
          rwa [eval_dnf_relabel] at ht
        · intro h p hp
          change p ∈ (IndependentDomination.finiteCoverage G).map (CNF.relabel ι) at hp
          obtain ⟨p0, hp0, heq⟩ := List.mem_map.mp hp
          rw [← heq, eval_dnf_relabel]
          exact h p0 hp0
      simp only [B, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, hFE, hPE]
      rw [← IndependentDomination.finite_semantics G (fun u => y (ι u))]
      tauto
    have haccept (x : Fin n → Bool) : c.eval interpretation x = CardinalityInterval.wanted ↔
        lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
      have h := CardinalityInterval.circuit_accepts n lo hi x
      rwa [hc] at h
    calc
      _ = Nat.card {y : Fin (n + c.size) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val y (fun _ => false)) = true ∧
              (G.IsIndepSet {u | y (Fin.castAdd c.size u) = true} ∧
                ∀ u, y (Fin.castAdd c.size u) = true ∨
                  ∃ v, G.Adj u v ∧ y (Fin.castAdd c.size v) = true)} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro y
        simpa only [CardinalityInterval.formula, CardinalityInterval.payload_eq, hc] using hPred y
      _ = Nat.card {x : Fin n → Bool // c.eval interpretation x = CardinalityInterval.wanted ∧
          (G.IsIndepSet {u | x u = true} ∧
            ∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true)} :=
        by
          have h := FunctionalCNF.count_extensions c CardinalityInterval.wanted
            (fun x => G.IsIndepSet {u | x u = true} ∧
              ∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true)
          simpa only [← Nat.card_eq_fintype_card] using h
      _ = _ := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        rw [haccept]
        constructor
        · rintro ⟨⟨hl, hu⟩, hI, hD⟩
          exact ⟨hI, hD, hl, hu⟩
        · rintro ⟨hI, hD, hl, hu⟩
          exact ⟨⟨hl, hu⟩, hI, hD⟩

/-- Nonempty original graphs write exactly the source's two ordinary boundary queries. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi)))).length = 2 := by
  have hlen : (TwoBoundary.BinaryFrontend.conditions (build (ofGraph G lo hi))).length = n := by
    simp only [build, TwoBoundary.BinaryFrontend.conditions, graph, ofGraph,
      IndependentDomination.coverage, IndependentDomination.ofGraph, IndependentDomination.order,
      List.length_map, List.length_range]
  have hem : (TwoBoundary.BinaryFrontend.conditions (build (ofGraph G lo hi))).isEmpty ≠ true := by
    intro he
    have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  simp only [TwoBoundary.BinaryFrontend.compile, hem, Bool.false_eq_true, ↓reduceIte,
    TwoBoundary.BinaryFrontend.queries, List.length_cons, List.length_nil]

/-- Actual positive-vertex query budgets, including the computed linear size-test variables.
The number of clauses remains quadratic, with every functional gate clause included. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℕ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G lo hi)))) :
    N = 2 * n + (CardinalityInterval.circuit n lo hi).size - 1 ∧
      q.length ≤ 3 * n ^ 2 + 2 + 2856 * (n + 1) ∧
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
  change (IndependentDomination.exclusions (IndependentDomination.ofGraph G) ++
      CardinalityInterval.formula (n, lo, hi)).length =
      (CNF.relabel Fin.val B).length at hB
  simp only [List.length_append, CNF.relabel, List.length_map] at hB
  have hBG := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length)
    (IndependentDomination.build_ofGraph G)
  change (IndependentDomination.exclusions (IndependentDomination.ofGraph G)).length =
    (CNF.relabel Fin.val (IndependentDomination.finiteExclusions G)).length at hBG
  simp only [CNF.relabel, List.length_map] at hBG
  have hP := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum)
    hbuild
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G)).map List.length).sum =
    ((P.map (CNF.relabel Fin.val)).map List.length).sum at hP
  have hPG := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum)
    (IndependentDomination.build_ofGraph G)
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G)).map List.length).sum =
    (((IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val)).map
      List.length).sum at hPG
  simp only [List.map_map, CNF.relabel, List.length_map, Function.comp_def] at hP hPG
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G)).map List.length).sum =
    (P.map List.length).sum at hP
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G)).map List.length).sum =
    ((IndependentDomination.finiteCoverage G).map List.length).sum at hPG
  have hs := CardinalityInterval.formula_bounds n lo hi |>.1
  obtain ⟨hside, hterms⟩ := IndependentDomination.volumes G
  refine ⟨by omega, by omega, by simpa using hW⟩

namespace Signed

/-- Original graph and two unrestricted signed binary interval bounds. -/
abbrev Input := IndependentDomination.Input × ℤ × ℤ
/-- Original graph in a signed-bound input. -/
@[expose] def graph : Input → IndependentDomination.Input | (g, _, _) => g
/-- Original signed lower bound. -/
@[expose] def lower : Input → ℤ | (_, lo, _) => lo
/-- Original signed upper bound. -/
@[expose] def upper : Input → ℤ | (_, _, hi) => hi
/-- Signed binary bounds retain their signs and full bit lengths in the original input. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encIntBin encIntBin)
/-- Normalize a negative upper bound to an impossible natural interval. -/
@[expose] def lowerNat (lo hi : ℤ) : ℕ := if hi < 0 then 1 else lo.toNat
/-- Natural upper bound; a negative upper bound is paired with lower bound one. -/
@[expose] def upperNat (hi : ℤ) : ℕ := hi.toNat
/-- Actual signed-bound normalization, preserving every original graph bit. -/
@[expose] def normalize : Input → IndependentDominationInterval.Input
  | (g, lo, hi) => (g, lowerNat lo hi, upperNat hi)
/-- Canonical graph input with signed binary lower and upper bounds. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : ℤ) : Input := (IndependentDomination.ofGraph G, lo, hi)

/-- Binary normalization includes sign tests and avoids unary decoding of either input bound. -/
@[fun_prop] theorem normalize_polytime : ComputableInPolyTime normalize encInput
    IndependentDominationInterval.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hlo : ComputableInPolyTime lower encInput encIntBin := by unfold lower encInput; fun_prop
  have hhi : ComputableInPolyTime upper encInput encIntBin := by unfold upper encInput; fun_prop
  have hneg : ComputableInPolyTime (fun x => decide (upper x < 0)) encInput encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_isNeg.comp hhi.tidy)
  have hl := hneg.ite' (ComputableInPolyTime.const 1) (ComputableInPolyTime.intBin_toNat.comp hlo)
  have hh := ComputableInPolyTime.intBin_toNat.comp hhi
  have h := hg.prod (hl.prod hh)
  exact h.of_enc_eq fun x => by
    rcases x with ⟨g, lo, hi⟩
    simp only [normalize, graph, lower, upper, lowerNat, upperNat, Function.comp_def,
      IndependentDominationInterval.encInput]
    by_cases hn : hi < 0 <;> simp [hn]

/-- Normalization is pointwise exact for every nonnegative cardinality, including negative and
out-of-range input bounds. It supplies no weight, count or runtime advice. -/
theorem bounds_iff (lo hi : ℤ) (w : ℕ) :
    lowerNat lo hi ≤ w ∧ w ≤ upperNat hi ↔ lo ≤ (w : ℤ) ∧ (w : ℤ) ≤ hi := by
  unfold lowerNat upperNat
  split_ifs <;> omega

/-- Test for an empty original graph before constructing any size-test circuit. -/
@[expose] def isEmpty (x : Input) : Bool := decide (IndependentDomination.order (graph x) = 0)
/-- Direct empty-graph result, including arbitrary signed input bounds. -/
@[expose] def emptyAnswer (x : Input) : ℕ :=
  if lower x ≤ 0 ∧ 0 ≤ upper x then 1 else 0
/-- Actual signed-bound execution: empty graphs bypass normalization and counting. -/
@[expose] def run (counter : IndependentDominationInterval.Input → ℕ) (x : Input) : ℕ :=
  if isEmpty x then emptyAnswer x else counter (normalize x)

/-- Empty-input dispatch reads the original unary declaration in polynomial binary time. -/
@[fun_prop] theorem isEmpty_polytime : ComputableInPolyTime isEmpty encInput encBool := by
  unfold isEmpty IndependentDomination.order graph encInput IndependentDomination.encInput
  fun_prop

/-- Direct empty-graph comparison charges both signed binary bounds and the answer bits. -/
@[fun_prop] theorem emptyAnswer_polytime : ComputableInPolyTime emptyAnswer encInput encNat := by
  have hlo : ComputableInPolyTime lower encInput encIntBin := by unfold lower encInput; fun_prop
  have hhi : ComputableInPolyTime upper encInput encIntBin := by unfold upper encInput; fun_prop
  have hl : ComputableInPolyTime (fun x => decide (lower x ≤ 0)) encInput encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_le.comp (hlo.tidy.prod (.const 0)))
  have hh : ComputableInPolyTime (fun x => decide (0 ≤ upper x)) encInput encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_le.comp
      ((ComputableTidilyInPolyTime.const 0).prod hhi.tidy))
  have hc : ComputableInPolyTime (fun x => decide (lower x ≤ 0) && decide (0 ≤ upper x))
      encInput encBool := by fun_prop
  have h : ComputableInPolyTime
      (fun x => if (decide (lower x ≤ 0) && decide (0 ≤ upper x)) then 1 else 0)
      encInput encNat := hc.ite' (.const 1) (.const 0)
  exact h.of_enc_eq fun x => by
    simp only [emptyAnswer, Bool.and_eq_true, decide_eq_true_eq]

open Classical in
/-- The direct empty-graph branch counts its single possible original selection exactly. -/
theorem zero_count (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj] (lo hi : ℤ) :
    Fintype.card {x : Fin 0 → Bool // G.IsIndepSet {u | x u = true} ∧
      (∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true) ∧
      lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} =
        if lo ≤ 0 ∧ 0 ≤ hi then 1 else 0 := by
  have hw (x : Fin 0 → Bool) : Cslib.BitString.weight x = 0 := by simp [Cslib.BitString.weight]
  have hp (x : Fin 0 → Bool) :
      (G.IsIndepSet {u | x u = true} ∧
        (∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true) ∧
        lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi) ↔
          lo ≤ 0 ∧ 0 ≤ hi := by
    rw [hw]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      refine ⟨?_, ?_, h⟩
      · intro u
        exact Fin.elim0 u
      · intro u
        exact Fin.elim0 u
  calc
    _ = Fintype.card {x : Fin 0 → Bool // lo ≤ 0 ∧ 0 ≤ hi} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hp)
    _ = _ := by
      by_cases h : lo ≤ 0 ∧ 0 ≤ hi <;> simp [h]

end Signed

end Cslib.Logic.PL.IndependentDominationInterval
