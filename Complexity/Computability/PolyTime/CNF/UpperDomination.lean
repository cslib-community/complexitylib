/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.DominatingSet
public import Complexity.Computability.Circuit.Boolean.FunctionalCNFContext
public import Complexity.Computability.PolyTime.CNF.IndependentDominationInterval
import all Complexity.Computability.PolyTime.CNF.IndependentDomination
import all Complexity.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Actual Upper Dominating Set set–marking construction

Compute a functional selection-size test, at-most-one-selected-neighbor clauses for private marks,
domination clauses, and marked-neighbor coverage for each selected vertex. The actual count is
of valid set–marking pairs, not unmarked minimal dominating sets. This is the width-three decision
construction of [ChenJiangZhu2027], Proposition 7.6 / Appendix D.3 (PDF pp. 27, 34–35).

## Main results

* `build_polytime`: actual signed normalization, generated gates and graph/marking literal writes.
* `representation`, `word_count_eq_pairs`: one gate trace per ordinary valid set–marking pair.
* `query_budget`: actual width-three queries on `4v+a-1` variables with cubic clauses.
-/

public section

namespace Cslib.Logic.PL.UpperDomination

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-- Original explicit matrix and varying signed binary lower cardinality bound. -/
abbrev Input := IndependentDomination.Input × ℤ
/-- Retain the original graph declaration and all matrix cells. -/
@[expose] def graph (x : Input) : IndependentDomination.Input := x.1
/-- Inclusive signed lower bound on the selected dominating set. -/
@[expose] def threshold (x : Input) : ℤ := x.2
/-- Unary vertex declaration, framed matrix and signed binary threshold. -/
@[expose] def encInput : Input ↪ List Bool := encPair IndependentDomination.encInput encIntBin
/-- Natural functional size-test frame. Negative bounds accept every natural cardinality. -/
@[expose] def normalize (x : Input) : IndependentDominationInterval.Input :=
  (graph x, (threshold x).toNat, IndependentDomination.order (graph x))
/-- Runtime cardinality circuit input, without supplied gates or size advice. -/
@[expose] def cardinalityInput (x : Input) : CardinalityInterval.Input :=
  IndependentDominationInterval.cardinalityInput (normalize x)
/-- Actual generated size-gate count. -/
@[expose] def auxiliary (x : Input) : ℕ := IndependentDominationInterval.auxiliary (normalize x)
/-- Graph and unary first private-mark wire, after the selection and functional gate wires. -/
abbrev CoreInput := IndependentDomination.Input × ℕ
/-- Original matrix in the local marking construction. -/
@[expose] def coreGraph (x : CoreInput) : IndependentDomination.Input := x.1
/-- First private-mark wire. -/
@[expose] def markBase (x : CoreInput) : ℕ := x.2
/-- Complete local graph/offset frame, charging the computed offset. -/
@[expose] def encCore : CoreInput ↪ List Bool := encPair IndependentDomination.encInput encUnary
/-- Actual closed-neighborhood test, including self membership. -/
@[expose] def closed (g : IndependentDomination.Input) (w u : ℕ) : Bool :=
  decide (w = u) || IndependentDomination.adjacent g w u
/-- For each mark and distinct pair of selected closed neighbors, forbid simultaneous truth. -/
@[expose] def upper (x : CoreInput) : CNF ℕ :=
  (List.range (IndependentDomination.order (coreGraph x))).flatMap fun w =>
    (List.range (IndependentDomination.order (coreGraph x))).flatMap fun u =>
      (List.range (IndependentDomination.order (coreGraph x))).flatMap fun v =>
        if decide (u ≠ v) && closed (coreGraph x) w u && closed (coreGraph x) w v then
          [[(markBase x + w, false), (u, false), (v, false)]] else []
/-- Every selected original vertex has a marked closed neighbor. -/
@[expose] def witnesses (x : CoreInput) : List (DNF ℕ) :=
  (List.range (IndependentDomination.order (coreGraph x))).map fun u =>
    [[(u, false)]] ++
      ((List.range (IndependentDomination.order (coreGraph x))).filter (closed (coreGraph x) u)).map
        fun w => [(markBase x + w, true)]
/-- The mark offset is computed from the original declaration and actual size-test gates. -/
@[expose] def coreInput (x : Input) : CoreInput :=
  (graph x, IndependentDomination.order (graph x) + auxiliary x)
/-- Complete actual graph/size/marking constructor. Selection inputs precede functional gate
wires; the private marks follow them and remain original counted marking bits. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (IndependentDomination.order (graph x) + auxiliary x + IndependentDomination.order (graph x),
    CardinalityInterval.formula (cardinalityInput x) ++ upper (coreInput x),
    IndependentDomination.coverage (graph x) ++ witnesses (coreInput x))
/-- Canonical original simple graph and signed input bound. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ) : Input :=
  (IndependentDomination.ofGraph G, k)

/-- Canonical closed-neighborhood matrix lookup. -/
theorem closed_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w u : Fin n) :
    closed (IndependentDomination.ofGraph G) w.val u.val = decide (G.ClosedAdj w u) := by
  simp only [closed, SimpleGraph.ClosedAdj, IndependentDomination.adjacent_ofGraph, Fin.val_inj]
  exact (Bool.decide_or (w = u) (G.Adj w u)).symm

/-- Original selection wire, leaving room for both gate and private-mark wires. -/
@[expose] def selection {n : ℕ} (a : ℕ) (u : Fin n) : Fin ((n + a) + n) :=
  Fin.castAdd n (Fin.castAdd a u)
/-- Private-mark wire after every functional size-test gate. -/
@[expose] def mark {n : ℕ} (a : ℕ) (w : Fin n) : Fin ((n + a) + n) := Fin.natAdd (n + a) w
/-- Finite upper clauses, used for the original-object count correspondence. -/
@[expose] def finiteUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    CNF (Fin ((n + a) + n)) :=
  (List.finRange n).flatMap fun w => (List.finRange n).flatMap fun u =>
    (List.finRange n).flatMap fun v =>
      if u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v then
        [[(mark a w, false), (selection a u, false), (selection a v, false)]] else []
/-- Finite domination predicates on original selection columns. -/
@[expose] def finiteDomination {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    List (DNF (Fin ((n + a) + n))) :=
  (IndependentDomination.finiteCoverage G).map (CNF.relabel (selection a))
/-- Finite coverage of each selected vertex by its private marks. -/
@[expose] def finiteWitnesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    List (DNF (Fin ((n + a) + n))) :=
  (List.finRange n).map fun u => [[(selection a u, false)]] ++
    ((List.finRange n).filter (fun w => decide (G.ClosedAdj u w))).map fun w => [(mark a w, true)]

/-- Upper clauses forbid a mark with two distinct selected closed neighbors. -/
theorem finiteUpper_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ)
    (y : Fin ((n + a) + n) → Bool) :
    (finiteUpper G a).eval y = true ↔ ∀ w u v, u ≠ v → G.ClosedAdj w u → G.ClosedAdj w v →
      ¬(y (mark a w) = true ∧ y (selection a u) = true ∧ y (selection a v) = true) := by
  have he (w u v : Fin n) : CNF.eval y (if u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v then
      [[(mark a w, false), (selection a u, false), (selection a v, false)]] else []) = true ↔
      (u ≠ v → G.ClosedAdj w u → G.ClosedAdj w v →
        ¬(y (mark a w) = true ∧ y (selection a u) = true ∧ y (selection a v) = true)) := by
    split_ifs with h
    · cases hw : y (mark a w) <;> cases hu : y (selection a u) <;>
        cases hv : y (selection a v) <;> simp_all [CNF.eval, Clause.eval, Literal.eval]
    · simp only [CNF.eval_nil, true_iff]
      intro hne hw hu
      exact False.elim (h ⟨hne, hw, hu⟩)
  simp only [finiteUpper, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_true_left, he]

/-- The finite domination predicates are exactly original closed-neighborhood domination. -/
theorem finiteDomination_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ)
    (y : Fin ((n + a) + n) → Bool) :
    (∀ p ∈ finiteDomination G a, DNF.eval y p = true) ↔
      G.IsDominatingSet {u | y (selection a u) = true} := by
  simp only [finiteDomination, List.forall_mem_map,
    IndependentDominationInterval.eval_dnf_relabel]
  simp [IndependentDomination.finiteCoverage, DNF.eval_eq_true_iff, Term.eval, Literal.eval,
    SimpleGraph.IsDominatingSet, SimpleGraph.ClosedAdj, Function.comp_def, and_comm]

/-- Original selection/mark coverage, not a choice of a labeled owner for each mark. -/
theorem finiteWitnesses_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ)
    (y : Fin ((n + a) + n) → Bool) :
    (∀ p ∈ finiteWitnesses G a, DNF.eval y p = true) ↔
      ∀ u, y (selection a u) = true → ∃ w, G.ClosedAdj u w ∧ y (mark a w) = true := by
  have he : (∀ p ∈ finiteWitnesses G a, DNF.eval y p = true) ↔
      ∀ u, y (selection a u) = false ∨ ∃ w, G.ClosedAdj u w ∧ y (mark a w) = true := by
    simp [finiteWitnesses, DNF.eval_eq_true_iff, Term.eval, Literal.eval]
  rw [he]
  constructor
  · intro h u hu
    rcases h u with hf | ⟨w, hw, hy⟩
    · exact False.elim (Bool.false_ne_true (hf.symm.trans hu))
    · exact ⟨w, hw, hy⟩
  · intro h u
    cases hu : y (selection a u)
    · exact Or.inl rfl
    · exact Or.inr (h u hu)

/-- The actual local constraints express precisely valid source set–marking pairs. -/
theorem finite_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ)
    (y : Fin ((n + a) + n) → Bool) :
    (finiteUpper G a).eval y = true ∧
      (∀ p ∈ finiteDomination G a ++ finiteWitnesses G a, DNF.eval y p = true) ↔
        G.IsPrivateMarking {u | y (selection a u) = true} {w | y (mark a w) = true} := by
  rw [List.forall_mem_append, finiteDomination_eval, finiteWitnesses_eval, finiteUpper_eval]
  constructor
  · rintro ⟨hu, hd, hw⟩
    refine ⟨hd, ?_, ?_⟩
    · intro w hmark u hsu v hsv hwu hwv
      by_contra hne
      exact hu w u v hne hwu hwv ⟨hmark, hsu, hsv⟩
    · intro u hsu
      obtain ⟨w, huw, hmark⟩ := hw u hsu
      exact ⟨w, hmark, huw⟩
  · rintro ⟨hd, hu, hw⟩
    refine ⟨?_, hd, ?_⟩
    · rintro w u v hne hwu hwv ⟨hmark, hsu, hsv⟩
      exact hne (hu w hmark u hsu v hsv hwu hwv)
    · intro u hsu
      obtain ⟨w, hmark, huw⟩ := hw u hsu
      exact ⟨w, huw, hmark⟩

private theorem closed_polytime : ComputableInPolyTime
    (fun p : IndependentDomination.Input × ℕ × ℕ => closed p.1 p.2.1 p.2.2)
    (encPair IndependentDomination.encInput (encPair encUnary encUnary)) encBool := by
  have ha := IndependentDomination.adjacent_polytime
  unfold closed
  fun_prop

private theorem upper_polytime : ComputableInPolyTime upper encCore VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (coreGraph x))
      encCore encUnary := by
    unfold coreGraph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  unfold upper VCOne.encSignedCNF
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _))))
  let ei := encPair (encPair (encPair encCore encUnary) encUnary) encUnary
  have hwu := closed_polytime.comp (show ComputableInPolyTime
    (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => (coreGraph p.1.1.1, p.1.1.2, p.1.2)) ei
      (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by
        unfold coreGraph ei encCore; fun_prop)
  have hwv := closed_polytime.comp (show ComputableInPolyTime
    (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => (coreGraph p.1.1.1, p.1.1.2, p.2)) ei
      (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by
        unfold coreGraph ei encCore; fun_prop)
  have hne : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2))
      ei encBool := by unfold ei; fun_prop
  have hmark : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ =>
      markBase p.1.1.1 + p.1.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold markBase ei encCore; fun_prop)
  have hu : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => p.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hv : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have htest : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ =>
      decide (p.1.2 ≠ p.2) && closed (coreGraph p.1.1.1) p.1.1.2 p.1.2 &&
        closed (coreGraph p.1.1.1) p.1.1.2 p.2) ei encBool := by fun_prop
  have hbody : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ =>
      [[(markBase p.1.1.1 + p.1.1.2, false), (p.1.2, false), (p.2, false)]])
      ei (encList (encList (encPair encNat encBool))) := by fun_prop
  exact (htest.ite' hbody (.const [])).of_enc_eq fun _ => rfl

private theorem witnesses_polytime : ComputableInPolyTime witnesses encCore
    (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (coreGraph x))
      encCore encUnary := by
    unfold coreGraph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  let ei := encPair encCore encUnary
  have hns : ComputableInPolyTime (fun p : CoreInput × ℕ =>
      (List.range (IndependentDomination.order (coreGraph p.1))).filter
        (closed (coreGraph p.1) p.2)) ei (encList encUnary) := by
    apply ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
    exact closed_polytime.comp (show ComputableInPolyTime
      (fun p : (CoreInput × ℕ) × ℕ => (coreGraph p.1.1, p.1.2, p.2))
        (encPair ei encUnary) (encPair IndependentDomination.encInput (encPair encUnary encUnary))
          from by unfold coreGraph ei encCore; fun_prop)
  have hm : ComputableInPolyTime (fun p : (CoreInput × ℕ) × ℕ => markBase p.1.1 + p.2)
      (encPair ei encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold markBase ei encCore; fun_prop)
  have hlit : ComputableInPolyTime (fun p : (CoreInput × ℕ) × ℕ =>
      [(markBase p.1.1 + p.2, true)]) (encPair ei encUnary)
      (encList (encPair encNat encBool)) := by fun_prop
  have hu : ComputableInPolyTime (fun p : CoreInput × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hself : ComputableInPolyTime (fun p : CoreInput × ℕ => [[(p.2, false)]]) ei
      (encList (encList (encPair encNat encBool))) := by fun_prop
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
    (ComputableInPolyTime.listAppend' hself (ComputableInPolyTime.mapWithInput hns hlit))

private theorem normalize_polytime : ComputableInPolyTime normalize encInput
    IndependentDominationInterval.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hk : ComputableInPolyTime threshold encInput encIntBin := by
    unfold threshold encInput; fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold graph encInput IndependentDomination.order IndependentDomination.encInput; fun_prop
  exact (hg.prod ((ComputableInPolyTime.intBin_toNat.comp hk).prod
    (ComputableInPolyTime.unary_to_binary.comp hn))).of_enc_eq fun _ => rfl

/-- Actual original-input normalization, generated gates, mark offsets and every clause/term write
have polynomial binary construction resources. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold graph encInput IndependentDomination.order IndependentDomination.encInput; fun_prop
  have ha : ComputableInPolyTime auxiliary encInput encUnary :=
    IndependentDominationInterval.auxiliary_polytime.comp normalize_polytime
  have hcard := IndependentDominationInterval.cardinalityInput_polytime.comp normalize_polytime
  have hcore : ComputableInPolyTime coreInput encInput encCore := by
    exact hg.prod (ComputableInPolyTime.unary_add.comp (hn.prod ha))
  have hB := CardinalityInterval.formula_polytime.comp hcard
  have hU := upper_polytime.comp hcore
  have hD := IndependentDomination.coverage_polytime.comp hg
  have hW := witnesses_polytime.comp hcore
  have hN : ComputableInPolyTime (fun x => IndependentDomination.order (graph x) + auxiliary x +
      IndependentDomination.order (graph x)) encInput encUnary := by fun_prop
  exact (hN.prod ((ComputableInPolyTime.listAppend' hB hU).prod
    (ComputableInPolyTime.listAppend' hD hW))).of_enc_eq fun _ => rfl

/-- Finite marking clauses erase to the actual triple traversal. -/
theorem upper_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    upper (IndependentDomination.ofGraph G, n + a) =
      (finiteUpper G a).relabel Fin.val := by
  simp only [upper, finiteUpper, coreGraph, markBase, IndependentDomination.order,
    IndependentDomination.ofGraph, ← List.map_coe_finRange_eq_range, List.flatMap_map,
    CNF.relabel, List.map_flatMap]
  congr 1
  funext w
  congr 1
  funext u
  congr 1
  funext v
  have hc (w u : Fin n) : closed
      (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v)) w.val u.val =
        decide (G.ClosedAdj w u) := closed_ofGraph G w u
  simp only [hc, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Fin.val_inj, and_assoc]
  split_ifs <;> rfl

/-- Finite mark-coverage terms erase to the actual original-matrix writer. -/
theorem witnesses_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    witnesses (IndependentDomination.ofGraph G, n + a) =
      (finiteWitnesses G a).map (CNF.relabel Fin.val) := by
  simp only [witnesses, finiteWitnesses, coreGraph, markBase, IndependentDomination.order,
    IndependentDomination.ofGraph, ← List.map_coe_finRange_eq_range, List.map_map,
    Function.comp_def]
  congr 1
  funext u
  have hc (w : Fin n) : closed
      (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v)) u.val w.val =
        decide (G.ClosedAdj u w) := closed_ofGraph G u w
  simp only [List.filter_map, hc, CNF.relabel, List.map_map, Function.comp_def,
    List.map_append, List.map_cons, List.map_nil, Clause.relabel, selection, mark]
  rfl

/-- Finite local clauses and terms have source widths three and one, with exactly two predicates
per original vertex. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    (∀ q ∈ finiteUpper G a, q.length ≤ 3) ∧
      (∀ p ∈ finiteDomination G a ++ finiteWitnesses G a, ∀ t ∈ p, t.length ≤ 1) ∧
      (finiteDomination G a ++ finiteWitnesses G a).length = 2 * n := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp only [finiteUpper, List.mem_flatMap, List.mem_finRange, true_and] at hq
    obtain ⟨w, u, v, hq⟩ := hq
    split_ifs at hq <;> simp_all
  · intro p hp t ht
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      simpa only [Clause.relabel, List.length_map] using
        (IndependentDomination.widths G).2 p0 hp0 t0 ht0
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
      rcases List.mem_append.mp ht with ht | ht
      · have he := List.mem_singleton.mp ht
        subst t
        simp
      · obtain ⟨w, _, rfl⟩ := List.mem_map.mp ht
        simp
  · simp [finiteDomination, finiteWitnesses, IndependentDomination.finiteCoverage, two_mul]

open Classical in
/-- The actual constructed input counts original selection/private-mark words, with exactly one
functional cardinality trace for each accepted pair. The mark word remains counted context. -/
theorem representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ) :
    let a := (CardinalityInterval.circuit n k.toNat n).size
    ∃ B : CNF (Fin ((n + a) + n)), ∃ P : List (DNF (Fin ((n + a) + n))),
      build (ofGraph G k) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ q ∈ B, q.length ≤ 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ 1) ∧ P.length = 2 * n ∧
      Fintype.card {y : Fin ((n + a) + n) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
          G.IsPrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
            k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} := by
  generalize hc : CardinalityInterval.circuit n k.toNat n = c
  let a := c.size
  obtain ⟨_, hCbounds⟩ := CardinalityInterval.formula_bounds n k.toNat n
  rw [hc] at hCbounds
  obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
    (CardinalityInterval.formula (n, k.toNat, n)) (fun q hq => (hCbounds q hq).2)
  let B := F.relabel (Fin.castAdd n) ++ finiteUpper G a
  let P := finiteDomination G a ++ finiteWitnesses G a
  have haux : auxiliary (ofGraph G k) = c.size := by
    change IndependentDominationInterval.auxiliary
      (IndependentDominationInterval.ofGraph G k.toNat n) = _
    rw [IndependentDominationInterval.auxiliary_ofGraph, hc]
  have hNF : CNF.relabel Fin.val B = CardinalityInterval.formula (n, k.toNat, n) ++
      upper (IndependentDomination.ofGraph G, n + a) := by
    simp only [B, CNF.relabel, List.map_append, List.map_map, Clause.relabel, Function.comp_def]
    rw [← hF, upper_ofGraph]
    rfl
  have hD := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hD
  have hDom : (finiteDomination G a).map (CNF.relabel Fin.val) =
      IndependentDomination.coverage (IndependentDomination.ofGraph G) := by
    rw [hD]
    simp only [finiteDomination, List.map_map, CNF.relabel, Clause.relabel, Function.comp_def]
    rfl
  have hPF : P.map (CNF.relabel Fin.val) = IndependentDomination.coverage
      (IndependentDomination.ofGraph G) ++ witnesses (IndependentDomination.ofGraph G, n + a) := by
    simp only [P, List.map_append, hDom, witnesses_ofGraph]
  obtain ⟨hU, hP, hplen⟩ := widths G a
  refine ⟨B, P, ?_, ?_, hP, hplen, ?_⟩
  · have hgraph : graph (ofGraph G k) = IndependentDomination.ofGraph G := rfl
    have horder : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
    have hcard : cardinalityInput (ofGraph G k) = (n, k.toNat, n) := rfl
    simp only [build, coreInput, hgraph, horder, haux, hcard,
      TwoBoundary.BinaryFrontend.ofFinite]
    rw [← hNF, ← hPF]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have hmem : q0.relabel Fin.val ∈ CardinalityInterval.formula (n, k.toNat, n) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q0, hq0, rfl⟩
      have hh := (hCbounds _ hmem).1
      simp only [Clause.relabel, List.length_map] at hh ⊢
      omega
    · exact hU q hq
  · simp only [← Nat.card_eq_fintype_card]
    have hFE (ν : Fin (n + a) → Bool) : F.eval ν =
        (CardinalityInterval.formula (n, k.toNat, n)).eval
          (Function.extend Fin.val ν (fun _ => false)) := by
      rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
    have hPred (y : Fin ((n + a) + n) → Bool) :
        B.eval y = true ∧ (∀ p ∈ P, DNF.eval y p = true) ↔
        (CardinalityInterval.formula (n, k.toNat, n)).eval
          (Function.extend Fin.val (fun j => y (Fin.castAdd n j)) (fun _ => false)) = true ∧
        G.IsPrivateMarking {u | y (selection a u) = true} {w | y (mark a w) = true} := by
      simp only [B, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, hFE]
      rw [← finite_semantics G a y]
      tauto
    have haccept (σ : Fin n → Bool) : c.eval interpretation σ = CardinalityInterval.wanted ↔
        k.toNat ≤ Cslib.BitString.weight σ ∧ Cslib.BitString.weight σ ≤ n := by
      have h := CardinalityInterval.circuit_accepts n k.toNat n σ
      rwa [hc] at h
    calc
      _ = Nat.card {y : Fin ((n + c.size) + n) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val (fun j => y (Fin.castAdd n j)) (fun _ => false)) = true ∧
          G.IsPrivateMarking {u | y (selection c.size u) = true}
            {w | y (mark c.size w) = true}} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro y
        simpa only [CardinalityInterval.formula, CardinalityInterval.payload_eq, hc] using hPred y
      _ = Nat.card {p : (Fin n → Bool) × (Fin n → Bool) //
          c.eval interpretation p.2 = CardinalityInterval.wanted ∧
          G.IsPrivateMarking {u | p.2 u = true} {w | p.1 w = true}} :=
        FunctionalCNF.count_extensions_appended c CardinalityInterval.wanted n
          (fun (μ : Fin n → Bool) (σ : Fin n → Bool) =>
            G.IsPrivateMarking {u | σ u = true} {w | μ w = true})
      _ = _ := by
        apply Nat.card_congr
        apply (Equiv.prodComm _ _).subtypeEquiv
        intro p
        rw [haccept]
        constructor
        · rintro ⟨⟨hl, hu⟩, hm⟩; exact ⟨hm, hl, hu⟩
        · rintro ⟨hm, hl, hu⟩; exact ⟨⟨hl, hu⟩, hm⟩

open Classical in
/-- Original Boolean words biject with ordinary set–marking pairs, preserving the signed size
bound. Gate values and owners are absent from this source object type. -/
theorem word_count_eq_pairs {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℤ) :
    Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
      G.IsPrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
        k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} =
      Fintype.card {p : Set (Fin n) × Set (Fin n) //
        G.IsPrivateMarking p.1 p.2 ∧ k ≤ (Nat.card p.1 : ℤ)} := by
  have hw (σ : Fin n → Bool) : Cslib.BitString.weight σ = Nat.card {u | σ u = true} := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  let f : {p : (Fin n → Bool) × (Fin n → Bool) //
      G.IsPrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
        k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} →
      {p : Set (Fin n) × Set (Fin n) // G.IsPrivateMarking p.1 p.2 ∧
        k ≤ (Nat.card p.1 : ℤ)} := fun p =>
    ⟨({u | p.val.1 u = true}, {w | p.val.2 w = true}), p.property.1,
      Int.toNat_le.mp (by simpa only [← hw] using p.property.2.1)⟩
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro x y he
    apply Subtype.ext
    apply Prod.ext
    · funext u
      have hh := Set.ext_iff.mp (congrArg (fun z => z.val.1) he) u
      change (x.val.1 u = true) ↔ (y.val.1 u = true) at hh
      cases hx : x.val.1 u <;> cases hy : y.val.1 u <;> simp_all
    · funext u
      have hh := Set.ext_iff.mp (congrArg (fun z => z.val.2) he) u
      change (x.val.2 u = true) ↔ (y.val.2 u = true) at hh
      cases hx : x.val.2 u <;> cases hy : y.val.2 u <;> simp_all
  · rintro ⟨⟨S, W⟩, hmark, hk⟩
    let σ (u : Fin n) := decide (u ∈ S)
    let μ (w : Fin n) := decide (w ∈ W)
    have hS : {u | σ u = true} = S := by ext u; simp [σ]
    have hW : {w | μ w = true} = W := by ext w; simp [μ]
    refine ⟨⟨(σ, μ), ?_, ?_, Cslib.BitString.weight_le_length σ⟩, ?_⟩
    · simpa only [hS, hW] using hmark
    · rw [hw, hS]
      exact Int.toNat_le.mpr hk
    · apply Subtype.ext
      exact Prod.ext hS hW

/-- Volumes of the actual local degree and marking lists, uniformly over graph density. -/
theorem volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    (finiteUpper G a).length ≤ n ^ 3 ∧
      (((finiteDomination G a ++ finiteWitnesses G a).map List.length).sum ≤
        2 * n ^ 2 + n) := by
  constructor
  · simp only [finiteUpper, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _w : Fin n, ∑ _u : Fin n, ∑ _v : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro w _
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        dsimp only [Function.comp_def]
        split_ifs <;> simp
      _ = _ := by simp; ring
  · have hd : (((finiteDomination G a).map List.length).sum) ≤ n ^ 2 := by
      simpa only [finiteDomination, List.map_map, CNF.relabel, List.length_map,
        Function.comp_def] using (IndependentDomination.volumes G).2
    have hw : (((finiteWitnesses G a).map List.length).sum) ≤ n * (n + 1) := by
      simp only [finiteWitnesses, Function.comp_def, List.finRange, List.map_ofFn,
        List.sum_ofFn, List.length_append, List.length_map, List.length_cons, List.length_nil]
      calc
        _ ≤ ∑ _u : Fin n, (n + 1) := by
          apply Finset.sum_le_sum
          intro u _
          have hl := List.length_filter_le (fun w => decide (G.ClosedAdj u w))
            (List.ofFn (fun i : Fin n => i))
          simp only [List.length_ofFn] at hl
          omega
        _ = _ := by simp
    simp only [List.map_append, List.sum_append]
    nlinarith

/-- Positive graphs produce exactly the source's two ordinary boundary queries. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))).length = 2 := by
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation G k
  rw [he, TwoBoundary.BinaryFrontend.compile_query_count]
  have hem : P.isEmpty ≠ true := by
    intro hp
    have hz := List.isEmpty_iff_length_eq_zero.mp hp
    omega
  simp only [TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.isEmpty_map, hem, Bool.false_eq_true, ↓reduceIte]

/-- Actual source query budgets, including every cardinality gate and literal label. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))) :
    N = 4 * n + (CardinalityInterval.circuit n k.toNat n).size - 1 ∧
      q.length ≤ n ^ 3 + 4 * n ^ 2 + 2 * n + 2 + 2856 * (n + 1) ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation G k
  rw [he] at hq
  obtain ⟨hN, hM, hW⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N q hq
  have hem : P.isEmpty ≠ true := by
    intro hs
    have hz := List.isEmpty_iff_length_eq_zero.mp hs
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte] at hN
  let a := (CardinalityInterval.circuit n k.toNat n).size
  have haux : auxiliary (ofGraph G k) = a := by
    exact IndependentDominationInterval.auxiliary_ofGraph G k.toNat n
  have hB := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length) he
  change (CardinalityInterval.formula (n, k.toNat, n) ++
    upper (coreInput (ofGraph G k))).length = (CNF.relabel Fin.val B).length at hB
  have hcore : coreInput (ofGraph G k) = (IndependentDomination.ofGraph G, n + a) := by
    simp only [coreInput, haux]
    rfl
  rw [hcore, upper_ofGraph] at hB
  simp only [List.length_append, CNF.relabel, List.length_map] at hB
  have hP := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum) he
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G) ++
    witnesses (coreInput (ofGraph G k))).map List.length).sum =
      ((P.map (CNF.relabel Fin.val)).map List.length).sum at hP
  have hD := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hD
  rw [hcore, witnesses_ofGraph, hD] at hP
  simp only [List.map_append, List.map_map, List.sum_append, CNF.relabel,
    List.length_map, Function.comp_def] at hP
  change ((IndependentDomination.finiteCoverage G).map List.length).sum +
    ((finiteWitnesses G a).map List.length).sum = (P.map List.length).sum at hP
  obtain ⟨hu, hpterms⟩ := volumes G a
  simp only [finiteDomination, List.map_append, List.map_map, List.sum_append,
    CNF.relabel, List.length_map, Function.comp_def] at hpterms
  change ((IndependentDomination.finiteCoverage G).map List.length).sum +
    ((finiteWitnesses G a).map List.length).sum ≤ 2 * n ^ 2 + n at hpterms
  have hc := (CardinalityInterval.formula_bounds n k.toNat n).1
  refine ⟨by omega, by omega, by simpa using hW⟩

/-- The source cubic clause bound, uniformly over the binary input threshold. -/
theorem query_cubic_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))) : q.length ≤ 6000 * n ^ 3 := by
  have h := (query_budget G k hn N q hq).2.1
  have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      _ = n ^ 3 := by ring
  nlinarith

end Cslib.Logic.PL.UpperDomination
