/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.DegreeRules
public import Complexity.Computability.PolyTime.CNF.IndependentDominationInterval
public import Complexity.Computability.PolyTime.CNF.WeightedQuery
import all Complexity.Computability.PolyTime.CNF.IndependentDomination
import all Complexity.Computability.PolyTime.CNF.WeightedQuery
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual functional neighbor-threshold construction

Enumerate fixed-length neighbor sublists, never a powerset or a witness variable per subset.
The forward clauses and reverse predicates force exactly the source threshold bits of
[ChenJiangZhu2027], Lemma C.1 (PDF pp.31–32).
-/

public section

namespace Cslib.Logic.PL.DegreeThreshold

open Turing.MultiTapeTM Cslib.Circuits.Boolean

/-- Original graph and computed offset after its selection/gate prefix. -/
abbrev Core := IndependentDomination.Input × ℕ
/-- Original runtime graph. -/
@[expose] def graph (x : Core) : IndependentDomination.Input := x.1
/-- First threshold wire, computed by the original-input constructor. -/
@[expose] def offset (x : Core) : ℕ := x.2
/-- Explicit matrix and unary computed wire offset. -/
@[expose] def encCore : Core ↪ List Bool := encPair IndependentDomination.encInput encUnary
/-- Actual list of original open neighbors, retaining canonical original indices. -/
@[expose] def neighbors (g : IndependentDomination.Input) (u : ℕ) : List ℕ :=
  (List.range (IndependentDomination.order g)).filter (IndependentDomination.adjacent g u)
/-- Runtime threshold index, without allocating a variable for a neighbor subset. -/
@[expose] def threshold (x : Core) (j u : ℕ) : ℕ :=
  offset x + (u + IndependentDomination.order (graph x) * j)
/-- Forward clauses for all fixed threshold levels and original vertices. -/
@[expose] def forward (D : ℕ) (x : Core) : CNF ℕ :=
  (List.range D).flatMap fun j =>
    (List.range (IndependentDomination.order (graph x))).flatMap fun u =>
      ((neighbors (graph x) u).sublistsLen (j + 1)).map fun t =>
        (threshold x j u, true) :: t.map fun v => (v, false)
/-- Exactly D predicates per vertex, enforcing the converse of each forward implication. -/
@[expose] def reverse (D : ℕ) (x : Core) : List (DNF ℕ) :=
  (List.range D).flatMap fun j =>
    (List.range (IndependentDomination.order (graph x))).map fun u =>
      [[(threshold x j u, false)]] ++
        ((neighbors (graph x) u).sublistsLen (j + 1)).map fun t => t.map fun v => (v, true)

/-- Original selection/gate prefix and the D by n threshold array. -/
abbrev Vars (n D a : ℕ) := Fin (n + a) ⊕ (Fin D × Fin n)
/-- Original selected vertex bit. -/
@[expose] def selection {n D : ℕ} (a : ℕ) (u : Fin n) : Vars n D a :=
  Sum.inl (Fin.castAdd a u)
/-- Threshold level j+1 for vertex u. -/
@[expose] def bit {n D a : ℕ} (j : Fin D) (u : Fin n) : Vars n D a := Sum.inr (j, u)
/-- Bijection onto the full declared finite wire set. -/
@[expose] def wireEquiv (n D a : ℕ) : Vars n D a ≃ Fin ((n + a) + D * n) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv
/-- Canonical original open-neighbor list. -/
@[expose] def finiteNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : List (Fin n) := (List.finRange n).filter fun v => decide (G.Adj u v)
/-- Original selected-neighbor count, with no threshold or gate advice. -/
@[expose] def count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) (u : Fin n) : ℕ := ((finiteNeighbors G u).filter σ).length
/-- Positive selection term of one actual candidate sublist. -/
@[expose] def term {n D : ℕ} (a : ℕ) (t : List (Fin n)) : Term (Vars n D a) :=
  t.map fun v => (selection a v, true)
/-- Finite forward block for one threshold bit. -/
@[expose] def forwardAt {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (j : Fin D) (u : Fin n) : CNF (Vars n D a) :=
  ((finiteNeighbors G u).sublistsLen (j.val + 1)).map fun t =>
    (bit j u, true) :: (term a t).negate
/-- Finite reverse predicate for one threshold bit. -/
@[expose] def reverseAt {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (j : Fin D) (u : Fin n) : DNF (Vars n D a) :=
  [[(bit j u, false)]] ++ ((finiteNeighbors G u).sublistsLen (j.val + 1)).map (term a)
/-- Finite forward clauses, sharing original selection wires across all levels. -/
@[expose] def finiteForward {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D a : ℕ) : CNF (Vars n D a) :=
  (List.finRange D).flatMap fun j => (List.finRange n).flatMap (forwardAt G a j)
/-- Finite reverse predicates, one per array cell. -/
@[expose] def finiteReverse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D a : ℕ) : List (DNF (Vars n D a)) :=
  (List.finRange D).flatMap fun j => (List.finRange n).map (reverseAt G a j)

private theorem selected_sublists {α : Type} (l : List α) (p : α → Bool) (j : ℕ) :
    (∃ t ∈ l.sublistsLen j, ∀ v ∈ t, p v = true) ↔ j ≤ (l.filter p).length := by
  constructor
  · rintro ⟨t, ht, hp⟩
    obtain ⟨hs, hl⟩ := List.mem_sublistsLen.mp ht
    have hf : t.filter p = t := List.filter_eq_self.mpr hp
    have hlen := (hs.filter p).length_le
    rwa [hf, hl] at hlen
  · intro h
    let t := (l.filter p).take j
    have hs : t.Sublist l := (List.take_sublist j (l.filter p)).trans List.filter_sublist
    have hl : t.length = j := by simp only [t, List.length_take, Nat.min_eq_left h]
    refine ⟨t, List.mem_sublistsLen.mpr ⟨hs, hl⟩, ?_⟩
    intro v hv
    exact (List.mem_filter.mp ((List.take_sublist j (l.filter p)).subset hv)).2

private theorem term_eval {n D : ℕ} (a : ℕ) (t : List (Fin n)) (y : Vars n D a → Bool) :
    Term.eval y (term a t) = true ↔ ∀ v ∈ t, y (selection a v) = true := by
  simp [term, Term.eval, Literal.eval]

private theorem candidates {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (j : Fin D) (u : Fin n) (y : Vars n D a → Bool) :
    (∃ t ∈ (finiteNeighbors G u).sublistsLen (j.val + 1), Term.eval y (term a t) = true) ↔
      j.val + 1 ≤ count G (fun v => y (selection a v)) u := by
  simp only [term_eval, count]
  exact selected_sublists _ _ _

/-- Every selected-neighbor witness forces its shared threshold bit, and conversely. -/
theorem local_eval {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (j : Fin D) (u : Fin n) (y : Vars n D a → Bool) :
    (CNF.eval y (forwardAt G a j u) = true ∧ DNF.eval y (reverseAt G a j u) = true) ↔
      y (bit j u) = decide (j.val + 1 ≤ count G (fun v => y (selection a v)) u) := by
  have hc := candidates G a j u y
  have hf : CNF.eval y (forwardAt G a j u) = true ↔
      (j.val + 1 ≤ count G (fun v => y (selection a v)) u → y (bit j u) = true) := by
    have he (t : List (Fin n)) :
        Clause.eval y ((bit j u, true) :: (term a t).negate) = true ↔
          Term.eval y (term a t) = true → y (bit j u) = true := by
      cases hy : y (bit j u) <;> cases ht : Term.eval y (term a t) <;>
        simp [Clause.eval_cons, Literal.eval, Term.eval_negate, hy, ht]
    simp only [forwardAt, CNF.eval_eq_true_iff, List.forall_mem_map, he]
    constructor
    · intro h hl
      obtain ⟨t, ht, hp⟩ := hc.mpr hl
      exact h t ht hp
    · intro h t ht hp; exact h (hc.mp ⟨t, ht, hp⟩)
  have hr : DNF.eval y (reverseAt G a j u) = true ↔
      (y (bit j u) = true → j.val + 1 ≤ count G (fun v => y (selection a v)) u) := by
    have he : DNF.eval y (reverseAt G a j u) = true ↔
        y (bit j u) = false ∨
          ∃ t ∈ (finiteNeighbors G u).sublistsLen (j.val + 1), Term.eval y (term a t) = true := by
      simp [reverseAt, DNF.eval, Term.eval, Literal.eval]
    rw [he, hc]
    cases y (bit j u) <;> simp
  rw [hf, hr]
  cases y (bit j u) <;> simp

/-- All threshold bits are uniquely determined by the original selection, including thresholds
above the neighborhood size. No monotonicity constraints or witness variables are needed. -/
theorem functional {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D a : ℕ) (y : Vars n D a → Bool) :
    ((finiteForward G D a).eval y = true ∧
      ∀ p ∈ finiteReverse G D a, DNF.eval y p = true) ↔
      ∀ (j : Fin D) (u : Fin n),
        y (bit j u) = decide (j.val + 1 ≤ count G (fun v => y (selection a v)) u) := by
  have hf : (finiteForward G D a).eval y = true ↔
      ∀ (j : Fin D) (u : Fin n), (forwardAt G a j u).eval y = true := by
    simp only [finiteForward, CNF.eval_eq_true_iff, List.forall_mem_flatMap,
      List.mem_finRange, forall_const]
  have hr : (∀ p ∈ finiteReverse G D a, DNF.eval y p = true) ↔
      ∀ (j : Fin D) (u : Fin n), DNF.eval y (reverseAt G a j u) = true := by
    simp only [finiteReverse, List.forall_mem_flatMap, List.forall_mem_map,
      List.mem_finRange, forall_const]
  rw [hf, hr]
  constructor
  · intro h j u; exact (local_eval G a j u y).mp ⟨h.1 j u, h.2 j u⟩
  · intro h
    exact ⟨fun j u => ((local_eval G a j u y).mpr (h j u)).1,
      fun j u => ((local_eval G a j u y).mpr (h j u)).2⟩

private theorem neighbors_polytime : ComputableInPolyTime
    (fun p : IndependentDomination.Input × ℕ => neighbors p.1 p.2)
    (encPair IndependentDomination.encInput encUnary) (encList encUnary) := by
  have hn : ComputableInPolyTime
      (fun p : IndependentDomination.Input × ℕ => IndependentDomination.order p.1)
      (encPair IndependentDomination.encInput encUnary) encUnary := by
    unfold IndependentDomination.order IndependentDomination.encInput; fun_prop
  have ha := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : (IndependentDomination.Input × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
    (encPair (encPair IndependentDomination.encInput encUnary) encUnary)
    (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by fun_prop)
  unfold neighbors
  exact ComputableInPolyTime.filterWithInput (ComputableInPolyTime.range.comp hn) ha

private abbrev encRow := encPair encCore encUnary

private theorem rowNeighbors_polytime : ComputableInPolyTime
    (fun p : Core × ℕ => neighbors (graph p.1) p.2) encRow (encList encUnary) := by
  have hp : ComputableInPolyTime (fun p : Core × ℕ => (graph p.1, p.2)) encRow
      (encPair IndependentDomination.encInput encUnary) := by
    unfold graph encRow encCore; fun_prop
  exact neighbors_polytime.comp hp

private theorem index_polytime (j : ℕ) : ComputableInPolyTime
    (fun p : Core × ℕ => threshold p.1 j p.2) encRow encNat :=
  ComputableInPolyTime.unary_to_binary.comp (by
    unfold offset graph encRow encCore IndependentDomination.order
      IndependentDomination.encInput; fun_prop)

private theorem signedTerm_polytime (b : Bool) : ComputableInPolyTime
    (fun t : List ℕ => t.map fun v => (v, b)) (encList encUnary)
    (encList (encPair encNat encBool)) := by
  have hl : ComputableInPolyTime (fun v : ℕ => (v, b)) encUnary
      (encPair encNat encBool) := ComputableInPolyTime.unary_to_binary.prod (.const b)
  apply ComputableInPolyTime.mapWithInput
    (show ComputableInPolyTime (fun t : List ℕ => t) (encList encUnary) (encList encUnary)
      from by fun_prop)
  exact hl.comp (ComputableInPolyTime.snd _ _)

/-- Actual fixed-D forward enumeration charges sublist traversal and all binary literal writes. -/
@[fun_prop] theorem forward_polytime (D : ℕ) :
    ComputableInPolyTime (forward D) encCore VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encCore encUnary := by
    unfold graph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  unfold forward
  apply ComputableInPolyTime.flatMapConst
  intro j _
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  have ht := (Cslib.sublistsLen_polytime encUnary 0 (j + 1)).comp rowNeighbors_polytime
  apply ComputableInPolyTime.mapWithInput ht
  have hm := (index_polytime j).comp (ComputableInPolyTime.fst encRow (encList encUnary))
  have hs := (signedTerm_polytime false).comp
    (ComputableInPolyTime.snd encRow (encList encUnary))
  unfold encRow at *
  fun_prop

/-- Exactly D reverse predicates per vertex, with certified bounded sublist writing. -/
@[fun_prop] theorem reverse_polytime (D : ℕ) :
    ComputableInPolyTime (reverse D) encCore (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encCore encUnary := by
    unfold graph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  unfold reverse
  apply ComputableInPolyTime.flatMapConst
  intro j _
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have ht := (Cslib.sublistsLen_polytime encUnary 0 (j + 1)).comp rowNeighbors_polytime
  have hs : ComputableInPolyTime
      (fun p : Core × ℕ => ((neighbors (graph p.1) p.2).sublistsLen (j + 1)).map
        fun t => t.map fun v => (v, true)) encRow VCOne.encSignedCNF :=
    ComputableInPolyTime.mapWithInput ht
      ((signedTerm_polytime true).comp (ComputableInPolyTime.snd _ _))
  have hm := index_polytime j
  have hf : ComputableInPolyTime (fun p : Core × ℕ => [[(threshold p.1 j p.2, false)]])
      encRow VCOne.encSignedCNF := by unfold VCOne.encSignedCNF; fun_prop
  exact ComputableInPolyTime.listAppend' hf hs

/-- Finite neighbor listing erases to the actual original matrix scan. -/
theorem neighbors_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    neighbors (IndependentDomination.ofGraph G) u.val = (finiteNeighbors G u).map Fin.val := by
  simp only [neighbors, finiteNeighbors, IndependentDomination.order, IndependentDomination.ofGraph,
    ← List.map_coe_finRange_eq_range, List.filter_map]
  congr 1
  apply congrArg (fun f => (List.finRange n).filter f)
  funext v
  exact IndependentDomination.adjacent_ofGraph G u v

/-- The abstract wire layout preserves the actual natural index of each threshold. -/
theorem wireEquiv_bit {n D a : ℕ} (j : Fin D) (u : Fin n) :
    (wireEquiv n D a (bit j u)).val = (n + a) + (u.val + n * j.val) := rfl

/-- The finite forward representation is exactly the actual raw writer. -/
theorem forward_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D a : ℕ) :
    forward D (IndependentDomination.ofGraph G, n + a) =
      (finiteForward G D a).relabel (fun v => (wireEquiv n D a v).val) := by
  simp only [forward, finiteForward, graph, IndependentDomination.order,
    IndependentDomination.ofGraph, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, CNF.relabel, List.map_flatMap]
  congr 1
  funext j
  congr 1
  funext u
  change ((neighbors (IndependentDomination.ofGraph G) u.val).sublistsLen (j.val + 1)).map
    (fun t => (threshold (IndependentDomination.ofGraph G, n + a) j.val u.val, true) ::
      t.map fun v => (v, false)) =
        CNF.relabel (fun v => (wireEquiv n D a v).val) (forwardAt G a j u)
  rw [neighbors_ofGraph G u, WeightedRow.BinaryQuery.sublistsLen_map]
  simp only [forwardAt, CNF.relabel, List.map_map, Clause.relabel, Term.negate, term, List.map_cons,
    Function.comp_def, selection, bit, threshold, offset, graph, IndependentDomination.order,
    IndependentDomination.ofGraph, wireEquiv, Equiv.trans_apply, Equiv.sumCongr_apply]
  rfl

/-- Reverse predicates use precisely the same actual bounded subset lists and original labels. -/
theorem reverse_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D a : ℕ) :
    reverse D (IndependentDomination.ofGraph G, n + a) =
      (finiteReverse G D a).map (CNF.relabel (fun v => (wireEquiv n D a v).val)) := by
  simp only [reverse, finiteReverse, graph, IndependentDomination.order,
    IndependentDomination.ofGraph, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  funext j
  congr 1
  funext u
  change [[(threshold (IndependentDomination.ofGraph G, n + a) j.val u.val, false)]] ++
    ((neighbors (IndependentDomination.ofGraph G) u.val).sublistsLen (j.val + 1)).map
      (fun t => t.map fun v => (v, true)) =
        CNF.relabel (fun v => (wireEquiv n D a v).val) (reverseAt G a j u)
  rw [neighbors_ofGraph G u, WeightedRow.BinaryQuery.sublistsLen_map]
  simp only [reverseAt, CNF.relabel, Clause.relabel, List.map_append, List.map_cons,
    List.map_nil, List.map_map, term, Function.comp_def, selection, bit, threshold, offset,
    graph, IndependentDomination.order, IndependentDomination.ofGraph, wireEquiv,
    Equiv.trans_apply, Equiv.sumCongr_apply]
  rfl

/-- Forward clause width, reverse term width and exact reverse-condition count. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D a : ℕ) (hD : 1 ≤ D) :
    (∀ c ∈ finiteForward G D a, c.length ≤ D + 1) ∧
      (∀ p ∈ finiteReverse G D a, ∀ t ∈ p, t.length ≤ D) ∧
      (finiteReverse G D a).length = D * n := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [finiteForward, List.mem_flatMap, List.mem_finRange, true_and] at hc
    obtain ⟨j, u, hc⟩ := hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    have hl := (List.mem_sublistsLen.mp ht).2
    simp only [List.length_cons, Term.negate, term, List.length_map]
    omega
  · intro p hp t ht
    simp only [finiteReverse, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hp
    obtain ⟨j, u, _, rfl⟩ := hp
    rcases List.mem_append.mp ht with ht | ht
    · have he := List.mem_singleton.mp ht
      subst t
      simpa using hD
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
      have hl := (List.mem_sublistsLen.mp hw).2
      simp only [term, List.length_map]
      omega
  · simp [finiteReverse, List.length_flatMap, List.finRange, List.sum_ofFn]

/-- Fixed-length neighbor candidates have polynomial volume, even when D exceeds the degree.
This is a combinatorial bound, separate from the actual binary enumeration cost above. -/
theorem candidate_bound {n D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (j : Fin D) (u : Fin n) :
    ((finiteNeighbors G u).sublistsLen (j.val + 1)).length ≤ (n + 1) ^ D := by
  rw [List.length_sublistsLen]
  have hn : (finiteNeighbors G u).length ≤ n + 1 :=
    (List.length_filter_le _ _).trans (by simp)
  exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left hn (j.val + 1)).trans
    (Nat.pow_le_pow_right (by omega) (by omega)))

/-- Total forward clauses and reverse terms of the actual finite construction are polynomial in
v for fixed D. In particular no full-neighborhood powerset is enumerated. -/
theorem volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D a : ℕ) :
    (finiteForward G D a).length ≤ D * n * (n + 1) ^ D ∧
      ((finiteReverse G D a).map List.length).sum ≤ D * n * ((n + 1) ^ D + 1) := by
  have hf (j : Fin D) (u : Fin n) : (forwardAt G a j u).length ≤ (n + 1) ^ D := by
    simpa only [forwardAt, List.length_map] using candidate_bound G j u
  have hr (j : Fin D) (u : Fin n) : (reverseAt G a j u).length ≤ (n + 1) ^ D + 1 := by
    simpa only [reverseAt, List.length_append, List.length_cons, List.length_nil,
      List.length_map, Nat.add_comm] using Nat.add_le_add_right (candidate_bound G j u) 1
  constructor
  · simp only [finiteForward, List.length_flatMap, List.finRange, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _j : Fin D, ∑ _u : Fin n, (n + 1) ^ D :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun u _ => hf j u
      _ = _ := by simp; ring
  · simp only [finiteReverse, List.flatMap, List.map_flatten, List.sum_flatten, List.finRange,
      List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _j : Fin D, ∑ _u : Fin n, ((n + 1) ^ D + 1) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun u _ => hr j u
      _ = _ := by simp; ring

end Cslib.Logic.PL.DegreeThreshold
