/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.BoundedDegreePartition
public import CslibFrontier.Computability.PolyTime.CNF.DegreePartition
import all CslibFrontier.Computability.PolyTime.CNF.DegreePartition
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Actual binary per-class size bounds

The original matrix and binary interval list vary at runtime; the label count/rule matrix are
fixed. Relocate the approved no-test construction and append actual functional interval circuits
with explicit zero padding. Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
## Main results

* `build_polytime`: actual encoded relocation, test construction and writing.
* `representation`: complete original bounded-partition count and functional extensions.
* `query_budget`, `auxiliary_linear`: actual source dimension, width and linear allocation.

-/

public section

namespace Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend

open Turing.MultiTapeTM

/-- Original explicit graph and runtime binary bound pairs, one per fixed label. -/
abbrev Input := IndependentDomination.Input × List (ℕ × ℕ)
/-- Original graph, retaining the unary declared vertex count. -/
@[expose] def original (x : Input) : IndependentDomination.Input := x.1
/-- Runtime class intervals; missing entries have the deterministic raw-frame fallback (0,0). -/
@[expose] def intervals (x : Input) : List (ℕ × ℕ) := x.2
/-- Inclusive interval of a fixed class. -/
@[expose] def entry (i : ℕ) (x : Input) : ℕ × ℕ := (intervals x).getD i (0, 0)
/-- Inclusive binary lower class bound. -/
@[expose] def lower (i : ℕ) (x : Input) : ℕ := (entry i x).1
/-- Inclusive binary upper class bound. -/
@[expose] def upper (i : ℕ) (x : Input) : ℕ := (entry i x).2
/-- Canonical explicit input framing; bounds are binary, never unary padding in the input. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair IndependentDomination.encInput (encList (encPair encNat encNat))
/-- Actual cardinality generator request for a fixed class. -/
@[expose] def interval (i : ℕ) (x : Input) : CardinalityInterval.Input :=
  (IndependentDomination.order (original x), lower i x, upper i x)
/-- Actual padded selection/gate/threshold block width. -/
@[expose] def block (D : ℕ) (x : Input) : ℕ :=
  let n := IndependentDomination.order (original x)
  n + PaddedCardinality.capacity n + D * n
/-- Relocate an actual old literal index, inserting all functional gate slots. -/
@[expose] def relocate (D : ℕ) (x : Input) (v : ℕ) : ℕ :=
  let n := IndependentDomination.order (original x)
  let b := DegreePartition.BinaryFrontend.block D (original x)
  let j := v % b
  block D x * (v / b) + if j < n then j else j + PaddedCardinality.capacity n
/-- Actual per-class size-test clauses, sharing the original membership bits. -/
@[expose] def sizeTest (D i : ℕ) (x : Input) : CNF ℕ :=
  (PaddedCardinality.formula (interval i x)).relabel (block D x * i + ·)
/-- Full actual original-input writer; every allocated bit has a functional constraint. -/
@[expose] def build {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (q * block D x,
    (DegreePartition.BinaryFrontend.side M (original x)).relabel (relocate D x) ++
      (List.finRange q).flatMap fun i => sizeTest D i.val x,
    (DegreePartition.BinaryFrontend.conditions q D (original x)).map (CNF.relabel (relocate D x)))
/-- Canonical original graph and arbitrary input-varying bounds for all labels. -/
@[expose] def ofGraph {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) : Input :=
  (IndependentDomination.ofGraph G, List.ofFn fun i => (lo i, hi i))

private theorem original_polytime : ComputableInPolyTime original encInput
    IndependentDomination.encInput := by unfold original encInput; fun_prop

private theorem order_polytime : ComputableInPolyTime
    (fun x => IndependentDomination.order (original x)) encInput encUnary := by
  unfold original encInput IndependentDomination.order IndependentDomination.encInput
  fun_prop

private theorem interval_polytime (i : ℕ) : ComputableInPolyTime (interval i) encInput
    CardinalityInterval.encInput := by
  unfold interval lower upper entry intervals encInput CardinalityInterval.encInput
  have he : ComputableInPolyTime (fun x : Input => x.2.getD i (0, 0)) encInput
      (encPair encNat encNat) := by unfold encInput; fun_prop
  have hn := order_polytime
  fun_prop

private theorem block_polytime (D : ℕ) : ComputableInPolyTime (block D) encInput encUnary := by
  unfold block PaddedCardinality.capacity
  have hn := order_polytime
  fun_prop

private theorem relocate_polytime (D : ℕ) : ComputableInPolyTime
    (fun p : Input × ℕ => relocate D p.1 p.2) (encPair encInput encNat) encNat := by
  let ei := encPair encInput encNat
  have ho := order_polytime.comp (ComputableInPolyTime.fst encInput encNat)
  have hn := ComputableInPolyTime.unary_to_binary.comp ho
  have hb := ComputableInPolyTime.unary_to_binary.comp
    ((DegreePartition.BinaryFrontend.block_polytime D).comp
      (original_polytime.comp (ComputableInPolyTime.fst encInput encNat)))
  have hv : ComputableInPolyTime (fun p : Input × ℕ => p.2) ei encNat := .snd _ _
  have hj := ComputableInPolyTime.binary_mod.comp (hv.prod hb)
  have hi := ComputableInPolyTime.binary_div.comp (hv.prod hb)
  have hbNew := ComputableInPolyTime.unary_to_binary.comp
    ((block_polytime D).comp (ComputableInPolyTime.fst encInput encNat))
  have hA : ComputableInPolyTime (fun p : Input × ℕ =>
      PaddedCardinality.capacity (IndependentDomination.order (original p.1))) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have htest := ComputableInPolyTime.binary_lt.comp (hj.prod hn)
  have hlocal := htest.ite' hj (ComputableInPolyTime.binary_add.comp (hj.prod hA))
  have h := ComputableInPolyTime.binary_add.comp
    ((ComputableInPolyTime.binary_mul' hbNew hi).prod hlocal)
  simpa only [relocate, Function.comp_def, decide_eq_true_eq] using h

private theorem relabel_polytime (D : ℕ) : ComputableInPolyTime
    (fun p : Input × CNF ℕ => p.2.relabel (relocate D p.1))
    (encPair encInput VCOne.encSignedCNF) VCOne.encSignedCNF := by
  have hterm : ComputableInPolyTime
      (fun p : Input × Clause ℕ => Clause.relabel (relocate D p.1) p.2)
      (encPair encInput (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool)) := by
    let eLit := encPair encNat encBool
    let eTerm := encList eLit
    have hr := (relocate_polytime D).comp (show ComputableInPolyTime
      (fun p : (Input × Clause ℕ) × Literal ℕ => (p.1.1, p.2.1))
        (encPair (encPair encInput eTerm) eLit) (encPair encInput encNat) from by
          unfold eTerm eLit; fun_prop)
    have hb : ComputableInPolyTime (fun p : (Input × Clause ℕ) × Literal ℕ => p.2.2)
        (encPair (encPair encInput eTerm) eLit) encBool := by unfold eTerm eLit; fun_prop
    have hm := ComputableInPolyTime.mapWithInput
      (f := fun (p : Input × Clause ℕ) (l : Literal ℕ) => (relocate D p.1 l.1, l.2))
      (ComputableInPolyTime.snd encInput eTerm) (hr.prod hb)
    change ComputableInPolyTime (fun p : Input × Clause ℕ =>
      p.2.map (fun l => (relocate D p.1 l.1, l.2))) _ _
    simpa only [Function.comp_def] using hm
  have ht := hterm.comp (show ComputableInPolyTime
    (fun p : (Input × CNF ℕ) × Clause ℕ => (p.1.1, p.2))
      (encPair (encPair encInput VCOne.encSignedCNF) (encList (encPair encNat encBool)))
      (encPair encInput (encList (encPair encNat encBool))) from by
        unfold VCOne.encSignedCNF; fun_prop)
  have hm := ComputableInPolyTime.mapWithInput
    (f := fun (p : Input × CNF ℕ) (c : Clause ℕ) => Clause.relabel (relocate D p.1) c)
    (ComputableInPolyTime.snd encInput VCOne.encSignedCNF) ht
  change ComputableInPolyTime (fun p : Input × CNF ℕ =>
    p.2.map (fun c => Clause.relabel (relocate D p.1) c)) _ _
  simpa only [VCOne.encSignedCNF, Function.comp_def] using hm

/-- Actual binary construction, including all relocations and padded test writes. -/
@[fun_prop] theorem build_polytime {q D : ℕ}
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ComputableInPolyTime (build M) encInput TwoBoundary.BinaryFrontend.encInput := by
  have hold := (DegreePartition.BinaryFrontend.build_polytime M).comp original_polytime
  have hid : ComputableInPolyTime (fun x : Input => x) encInput encInput := .id'
  have hside := (relabel_polytime D).comp (hid.prod hold.snd'.fst')
  have htests : ComputableInPolyTime
      (fun x => (List.finRange q).flatMap fun i => sizeTest D i.val x)
      encInput VCOne.encSignedCNF := by
    apply ComputableInPolyTime.flatMapConst
    intro i _
    have ht := PaddedCardinality.formula_polytime.comp (interval_polytime i.val)
    have hoff : ComputableInPolyTime (fun x => block D x * i.val) encInput encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by have := block_polytime D; fun_prop)
    have hw := DegreePartition.BinaryFrontend.shift_polytime.comp (hoff.prod ht)
    simpa only [sizeTest, Function.comp_def, VCOne.encSignedCNF] using hw
  have hp : ComputableInPolyTime (fun x =>
      (DegreePartition.BinaryFrontend.conditions q D (original x)).map
        (CNF.relabel (relocate D x))) encInput (encList VCOne.encSignedCNF) := by
    apply ComputableInPolyTime.mapWithInput hold.snd'.snd'
    exact (relabel_polytime D).comp (show ComputableInPolyTime
      (fun p : Input × CNF ℕ => p) _ _ from .id')
  have hN : ComputableInPolyTime (fun x => q * block D x) encInput encUnary := by
    have := block_polytime D
    fun_prop
  exact hN.prod ((ComputableInPolyTime.listAppend' hside htests).prod hp)

/-- Canonical runtime bounds are read at their original label positions. -/
theorem interval_ofGraph {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) (i : Fin q) : interval i.val (ofGraph G lo hi) = (n, lo i, hi i) := by
  simp [interval, lower, upper, entry, intervals, original, ofGraph,
    IndependentDomination.order, IndependentDomination.ofGraph]

/-- Bijection packing every original, functional gate and threshold bit. -/
@[expose] def wireEquiv (n q D : ℕ) : Bounded.Vars n q D ≃
    Fin (q * (n + PaddedCardinality.capacity n + D * n)) :=
  (Equiv.prodCongr (Equiv.refl (Fin q))
    (DegreeThreshold.wireEquiv n D (PaddedCardinality.capacity n))).trans finProdFinEquiv

private theorem inputWire_val {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) (i : Fin q) (j : Fin (n + PaddedCardinality.capacity n)) :
    block D (ofGraph G lo hi) * i.val + j.val =
      (wireEquiv n q D (Bounded.inputWire i j)).val := by
  simp [block, original, ofGraph, IndependentDomination.order, IndependentDomination.ofGraph,
    wireEquiv, Bounded.inputWire, DegreeThreshold.wireEquiv, Nat.add_comm]

private theorem relocate_embed {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) (v : DegreePartition.Vars n q D) :
    relocate D (ofGraph G lo hi) ((DegreePartition.BinaryFrontend.wireEquiv n q D v).val) =
      (wireEquiv n q D (Bounded.embed v)).val := by
  rcases v with ⟨i, v⟩
  by_cases hn : n = 0
  · subst n
    cases v with
    | inl u => exact Fin.elim0 u
    | inr t => exact Fin.elim0 t.2
  have hpos : 0 < n + D * n := by omega
  let j := DegreeThreshold.wireEquiv n D 0 v
  have hj : j.val < n + D * n := j.isLt
  have hv : (DegreePartition.BinaryFrontend.wireEquiv n q D (i, v)).val =
      j.val + (n + D * n) * i.val := by
    simp [DegreePartition.BinaryFrontend.wireEquiv, j]
  rw [hv]
  simp only [relocate, original, ofGraph, IndependentDomination.order,
    IndependentDomination.ofGraph, DegreePartition.BinaryFrontend.block,
    Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hj,
    Nat.mod_eq_of_lt hj, zero_add]
  cases v with
  | inl u =>
    simp only [j, DegreeThreshold.wireEquiv, Equiv.trans_apply, Equiv.sumCongr_apply] at *
    simp [Bounded.embed, wireEquiv, DegreeThreshold.wireEquiv, block, original,
      IndependentDomination.order, Nat.add_comm]
  | inr t =>
    have hge : n ≤ j.val := by
      simp [j, DegreeThreshold.wireEquiv]
    have hnot : ¬ j.val < n := by omega
    simp only [hnot, ↓reduceIte]
    simp [j, Bounded.embed, wireEquiv, DegreeThreshold.wireEquiv, block, original,
      IndependentDomination.order, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]

private theorem erasure {V : Type*} {N : ℕ} (e : V ≃ Fin N) (F : CNF V) :
    (F.relabel e).relabel Fin.val = F.relabel (fun v => (e v).val) := by
  simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
  rfl

private theorem relocate_formula {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lo hi : Fin q → ℕ) (F : CNF (DegreePartition.Vars n q D)) :
    (F.relabel (fun v => (DegreePartition.BinaryFrontend.wireEquiv n q D v).val)).relabel
      (relocate D (ofGraph G lo hi)) =
        (F.relabel Bounded.embed).relabel (fun v => (wireEquiv n q D v).val) := by
  simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
  congr 1
  funext c
  congr 1
  funext l
  exact Prod.ext (relocate_embed G lo hi l.1) rfl

open Classical in
/-- Complete original-input finite presentation, including every runtime class bound and every
allocated functional gate. Finite formula witnesses are derived from actual written literals. -/
theorem representation {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ) :
    ∃ B : CNF (Fin (q * (n + PaddedCardinality.capacity n + D * n))),
      ∃ P : List (DNF (Fin (q * (n + PaddedCardinality.capacity n + D * n)))),
      build M (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ max q (max (D + 1) 3)) ∧
      (∀ p ∈ P, ∀ t ∈ p, t.length ≤ D) ∧ P.length = q * (D * n) ∧
      Fintype.card {y : Fin (q * (n + PaddedCardinality.capacity n + D * n)) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
      Fintype.card {S : Fin q → Set (Fin n) // G.IsDegreePartition (fun i j => (M i j).counts) S ∧
        SimpleGraph.InClassBounds lo hi S} := by
  have hFexist (i : Fin q) : ∃ F : CNF (Fin (n + PaddedCardinality.capacity n)),
      F.relabel Fin.val = PaddedCardinality.formula (n, lo i, hi i) ∧
      ∀ c ∈ F, c.length ≤ 3 := by
    have hb := (PaddedCardinality.bounds n (lo i) (hi i)).2
    obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
      (PaddedCardinality.formula (n, lo i, hi i)) (fun c hc => (hb c hc).2)
    refine ⟨F, hF, ?_⟩
    intro c hc
    have hm : c.relabel Fin.val ∈ PaddedCardinality.formula (n, lo i, hi i) := by
      rw [← hF]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    simpa only [Clause.relabel, List.length_map] using (hb _ hm).1
  choose F hF hw using hFexist
  let B := (Bounded.side G hD M F).relabel (wireEquiv n q D)
  let P := (Bounded.conditions G q D).map (CNF.relabel (wireEquiv n q D))
  have hold := DegreePartition.BinaryFrontend.build_ofGraph G hD M
  have hside := congrArg TwoBoundary.BinaryFrontend.side hold
  change DegreePartition.BinaryFrontend.side M (IndependentDomination.ofGraph G) =
    ((DegreePartition.side G q D hD M).relabel
      (DegreePartition.BinaryFrontend.wireEquiv n q D)).relabel Fin.val at hside
  rw [erasure] at hside
  have hconds := congrArg TwoBoundary.BinaryFrontend.conditions hold
  change DegreePartition.BinaryFrontend.conditions q D (IndependentDomination.ofGraph G) =
    ((DegreePartition.conditions G q D).map
      (CNF.relabel (DegreePartition.BinaryFrontend.wireEquiv n q D))).map
        (CNF.relabel Fin.val) at hconds
  simp only [List.map_map, Function.comp_def, erasure] at hconds
  have htest (i : Fin q) : sizeTest D i.val (ofGraph G lo hi) =
      ((F i).relabel (Bounded.inputWire i)).relabel
        (fun v => (wireEquiv n q D v).val) := by
    rw [sizeTest, interval_ofGraph G lo hi i, ← hF i]
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    congr 1
    funext c
    congr 1
    funext l
    exact Prod.ext (inputWire_val G lo hi i l.1) rfl
  have hB : B.relabel Fin.val =
      (DegreePartition.BinaryFrontend.side M (original (ofGraph G lo hi))).relabel
        (relocate D (ofGraph G lo hi)) ++
      (List.finRange q).flatMap (fun i => sizeTest D i.val (ofGraph G lo hi)) := by
    rw [erasure]
    simp only [Bounded.side, CNF.relabel, List.map_append, List.map_flatMap]
    apply congrArg₂ List.append
    · rw [show original (ofGraph G lo hi) = IndependentDomination.ofGraph G from rfl, hside]
      exact (relocate_formula G lo hi _).symm
    · apply List.flatMap_congr
      intro i _
      exact (htest i).symm
  have hP : P.map (CNF.relabel Fin.val) =
      (DegreePartition.BinaryFrontend.conditions q D (original (ofGraph G lo hi))).map
        (CNF.relabel (relocate D (ofGraph G lo hi))) := by
    simp only [P, Bounded.conditions, List.map_map, Function.comp_def, erasure]
    rw [show original (ofGraph G lo hi) = IndependentDomination.ofGraph G from rfl, hconds]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p _
    exact (relocate_formula G lo hi p).symm
  obtain ⟨hb, hp, hl⟩ := Bounded.widths G hD M F hw
  refine ⟨B, P, ?_, ?_, ?_, by simpa only [P, List.length_map] using hl, ?_⟩
  · simp only [build, TwoBoundary.BinaryFrontend.ofFinite, hB, hP]
    rfl
  · intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    simpa only [Clause.relabel, List.length_map] using hb t ht
  · intro p hmap t ht
    obtain ⟨localP, hlocalP, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨localT, hlocalT, rfl⟩ := List.mem_map.mp ht
    simpa only [Clause.relabel, List.length_map] using hp localP hlocalP localT hlocalT
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    let e : (Fin (q * (n + PaddedCardinality.capacity n + D * n)) → Bool) ≃
        (Bounded.Vars n q D → Bool) :=
      Equiv.arrowCongr (wireEquiv n q D).symm (Equiv.refl Bool)
    have he : Nat.card {y : Fin (q * (n + PaddedCardinality.capacity n + D * n)) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Nat.card {y : Bounded.Vars n q D → Bool // (Bounded.side G hD M F).eval y = true ∧
          ∀ p ∈ Bounded.conditions G q D, DNF.eval y p = true} := by
      apply Nat.card_congr
      exact e.subtypeEquiv fun _ => by
        simp only [B, P, CNF.eval_relabel, List.forall_mem_map, DNF.eval_relabel]
        rfl
    exact he.trans (Bounded.count_eq_partitions G hD M lo hi F hF)

/-- Actual auxiliary allocation is linear and independent of binary bound magnitudes. -/
theorem auxiliary_bound (q n : ℕ) : q * PaddedCardinality.capacity n ≤ 952 * q * (n + 1) := by
  unfold PaddedCardinality.capacity
  nlinarith

/-- For positive source vertex counts, every allocated functional slot is within O_q(v). -/
theorem auxiliary_linear (q n : ℕ) (hn : 1 ≤ n) :
    q * PaddedCardinality.capacity n ≤ 1904 * q * n := by
  have hq : q ≤ q * n := by simpa using Nat.mul_le_mul_left q hn
  unfold PaddedCardinality.capacity
  nlinarith

/-- The completed bounded instance emits exactly two queries on positive source dimensions. -/
theorem query_count {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hn : 1 ≤ n)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build M (ofGraph G lo hi)))).length = 2 := by
  classical
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation G hD M lo hi
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    have hpos := Nat.mul_pos (by omega : 0 < q)
      (Nat.mul_pos (by omega : 0 < D) (by omega : 0 < n))
    omega
  rw [he]
  simp only [TwoBoundary.BinaryFrontend.compile, TwoBoundary.BinaryFrontend.conditions,
    TwoBoundary.BinaryFrontend.ofFinite, List.isEmpty_map, hem, Bool.false_eq_true, ↓reduceIte,
    TwoBoundary.BinaryFrontend.queries, List.length_cons, List.length_nil]

/-- Source dimension/width, with all actual functional padding variables included in a. -/
theorem query_budget {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hn : 1 ≤ n)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (lo hi : Fin q → ℕ)
    (N : ℕ) (Q : CNF ℕ) (hQ : (N, Q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build M (ofGraph G lo hi)))) :
    N = q * (2 * D + 1) * n + q * PaddedCardinality.capacity n - 1 ∧
      ∀ c ∈ Q, c.length ≤ max q (D + 2) ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation G hD M lo hi
  rw [he] at hQ
  obtain ⟨hN, _, hw⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N Q hQ
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    have hpos := Nat.mul_pos (by omega : 0 < q)
      (Nat.mul_pos (by omega : 0 < D) (by omega : 0 < n))
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte, hl] at hN
  refine ⟨hN.trans ?_, fun c hc => ⟨(hw c hc).1.trans ?_, (hw c hc).2⟩⟩
  · congr 1; ring
  · omega

end Cslib.Logic.PL.DegreePartition.Bounded.BinaryFrontend
