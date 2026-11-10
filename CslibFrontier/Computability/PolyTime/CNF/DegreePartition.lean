/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.DegreePartition
public import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ExactlyOneRelabel
import all CslibFrontier.Computability.PolyTime.CNF.SigmaRho
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual encoded labeled degree-partition writer

The graph alone varies; q, D and the entire degree-rule matrix are fixed. Class-major blocks
share each original selection with every target-neighbor threshold test. No edge/subset variable
is introduced. Source: [ChenJiangZhu2027], Theorem 7.3 / Appendix C.2, PDF pp.25,32.
This module supplies the no-size-test construction; input class-bound gates are a separate stage.
-/

public section

namespace Cslib.Logic.PL.DegreePartition.BinaryFrontend

open Turing.MultiTapeTM IndependentDomination

/-- Actual number of selection/threshold wires in one target-class block. -/
@[expose] def block (D : ℕ) (g : Input) : ℕ := order g + D * order g
/-- Class-major binary literal index, with no permutation of labels. -/
@[expose] def wire (D : ℕ) (g : Input) (i v : ℕ) : ℕ := block D g * i + v
/-- Local threshold construction starts after the original class's selection bits. -/
@[expose] def localInput (g : Input) : DegreeThreshold.Core := (g, order g)
/-- Actual one-hot construction, including the all-class clause at each vertex. -/
@[expose] def oneHot (q D : ℕ) (g : Input) : CNF ℕ :=
  (List.range (order g)).flatMap fun u =>
    CNF.exactlyOne ((List.finRange q).map fun i => wire D g i.val u)
/-- Actual matrix-rule implications for every fixed source/target class and original vertex. -/
@[expose] def rules {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (g : Input) : CNF ℕ :=
  (List.finRange q).flatMap fun i => (List.finRange q).flatMap fun j =>
    (List.range (order g)).flatMap fun u => (List.finRange (D + 1)).flatMap fun s =>
      if M i j s then [] else [Term.negate ((wire D g i.val u, true) ::
        Clause.relabel (wire D g j.val) (SigmaRho.state D (localInput g) s.val u))]
/-- Complete actual side formula; no size gate is introduced in this no-test variant. -/
@[expose] def side {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (g : Input) : CNF ℕ :=
  oneHot q D g ++ ((List.finRange q).flatMap fun j =>
    (DegreeThreshold.forward D (localInput g)).relabel (wire D g j.val)) ++ rules M g
/-- The actual reverse predicates, with original label order retained. -/
@[expose] def conditions (q D : ℕ) (g : Input) : List (DNF ℕ) :=
  (List.finRange q).flatMap fun j => (DegreeThreshold.reverse D (localInput g)).map
    (CNF.relabel (wire D g j.val))
/-- Executable original-matrix construction, without a supplied rank, labeling or output. -/
@[expose] def build {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (g : Input) : TwoBoundary.BinaryFrontend.Input := (q * block D g, side M g, conditions q D g)

private theorem shiftTerm_polytime : ComputableInPolyTime
    (fun p : ℕ × Term ℕ => Clause.relabel (p.1 + ·) p.2)
    (encPair encNat (encList (encPair encNat encBool)))
    (encList (encPair encNat encBool)) := by
  unfold Clause.relabel
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.snd _ _)
  change ComputableInPolyTime (fun p : (ℕ × Term ℕ) × Literal ℕ =>
    (p.1.1 + p.2.1, p.2.2)) _ _
  fun_prop

private theorem shift_polytime : ComputableInPolyTime
    (fun p : ℕ × CNF ℕ => p.2.relabel (p.1 + ·))
    (encPair encNat VCOne.encSignedCNF) VCOne.encSignedCNF := by
  unfold CNF.relabel VCOne.encSignedCNF
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.snd _ _)
  exact shiftTerm_polytime.comp (show ComputableInPolyTime
    (fun p : (ℕ × CNF ℕ) × Clause ℕ => (p.1.1, p.2)) _ _ from by fun_prop)

private theorem block_polytime (D : ℕ) : ComputableInPolyTime (block D) encInput encUnary := by
  unfold block order encInput
  fun_prop

private theorem offset_polytime (D i : ℕ) :
    ComputableInPolyTime (fun g => block D g * i) encInput encNat :=
  ComputableInPolyTime.unary_to_binary.comp (by unfold block order encInput; fun_prop)

private theorem local_polytime : ComputableInPolyTime localInput encInput
    DegreeThreshold.encCore := by
  unfold localInput DegreeThreshold.encCore order encInput
  fun_prop

private theorem oneHot_polytime (q D : ℕ) :
    ComputableInPolyTime (oneHot q D) encInput VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  unfold oneHot
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply CNF.computableInPolyTime_exactlyOne encNat |>.comp
  apply ComputableInPolyTime.mapConst
  intro i _
  have ho := (offset_polytime D i.val).comp
    (ComputableInPolyTime.fst encInput encUnary)
  have hu := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.snd encInput encUnary)
  change ComputableInPolyTime (fun p : Input × ℕ => block D p.1 * i.val + p.2) _ encNat
  fun_prop

private theorem rules_polytime {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ComputableInPolyTime (rules M) encInput VCOne.encSignedCNF := by
  unfold rules
  apply ComputableInPolyTime.flatMapConst
  intro i _
  apply ComputableInPolyTime.flatMapConst
  intro j _
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapConst
  intro s _
  split_ifs
  · exact .const []
  · let ei := encPair encInput encUnary
    have hc : ComputableInPolyTime (fun p : Input × ℕ => (localInput p.1, p.2)) ei
        (encPair DegreeThreshold.encCore encUnary) :=
      (local_polytime.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _)
    have ht : ComputableInPolyTime (fun p : Input × ℕ =>
        SigmaRho.state D (localInput p.1) s.val p.2) ei
        (encList (encPair encNat encBool)) := (SigmaRho.state_polytime D s.val).comp hc
    have ho := (offset_polytime D j.val).comp (ComputableInPolyTime.fst encInput encUnary)
    have hs : ComputableInPolyTime (fun p : Input × ℕ =>
        Clause.relabel (wire D p.1 j.val) (SigmaRho.state D (localInput p.1) s.val p.2)) ei
        (encList (encPair encNat encBool)) := shiftTerm_polytime.comp (ho.prod ht)
    have hi := (offset_polytime D i.val).comp (ComputableInPolyTime.fst encInput encUnary)
    have hu := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd encInput encUnary)
    have hw : ComputableInPolyTime (fun p : Input × ℕ => wire D p.1 i.val p.2) ei encNat := by
      change ComputableInPolyTime (fun p : Input × ℕ => block D p.1 * i.val + p.2) ei encNat
      exact ComputableInPolyTime.binary_add.comp (hi.prod hu)
    have hprepend : ComputableInPolyTime (fun p : Input × ℕ =>
        (wire D p.1 i.val p.2, true) :: Clause.relabel (wire D p.1 j.val)
          (SigmaRho.state D (localInput p.1) s.val p.2)) ei
        (encList (encPair encNat encBool)) :=
      ComputableInPolyTime.cons' (hw.prod (.const true)) hs
    have hneg : ComputableInPolyTime (fun p : Input × ℕ => Term.negate
        ((wire D p.1 i.val p.2, true) :: Clause.relabel (wire D p.1 j.val)
          (SigmaRho.state D (localInput p.1) s.val p.2))) ei
        (encList (encPair encNat encBool)) := SigmaRho.negate_polytime.comp hprepend
    exact ComputableInPolyTime.cons' hneg (.const [])

/-- Actual fixed-matrix binary construction costs, including all original literal writes. -/
@[fun_prop] theorem build_polytime {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ComputableInPolyTime (build M) encInput TwoBoundary.BinaryFrontend.encInput := by
  have hf := (DegreeThreshold.forward_polytime D).comp local_polytime
  have hp := (DegreeThreshold.reverse_polytime D).comp local_polytime
  have hforward : ComputableInPolyTime (fun g => (List.finRange q).flatMap fun j =>
      (DegreeThreshold.forward D (localInput g)).relabel (wire D g j.val))
      encInput VCOne.encSignedCNF := by
    apply ComputableInPolyTime.flatMapConst
    intro j _
    exact shift_polytime.comp ((offset_polytime D j.val).prod hf)
  have hconditions : ComputableInPolyTime (conditions q D) encInput
      (encList VCOne.encSignedCNF) := by
    unfold conditions
    apply ComputableInPolyTime.flatMapConst
    intro j _
    apply ComputableInPolyTime.mapWithInput hp
    have ho := (offset_polytime D j.val).comp
      (ComputableInPolyTime.fst encInput VCOne.encSignedCNF)
    exact shift_polytime.comp (ho.prod (ComputableInPolyTime.snd _ _))
  have hside : ComputableInPolyTime (side M) encInput VCOne.encSignedCNF :=
    ComputableInPolyTime.listAppend'
      (ComputableInPolyTime.listAppend' (oneHot_polytime q D) hforward) (rules_polytime M)
  have hn : ComputableInPolyTime (fun g => q * block D g) encInput encUnary := by
    have := block_polytime D
    fun_prop
  exact hn.prod (hside.prod hconditions)

/-- All class blocks are bijectively packed into the actual finite declared wire range. -/
@[expose] def wireEquiv (n q D : ℕ) : DegreePartition.Vars n q D ≃ Fin (q * (n + D * n)) :=
  (Equiv.prodCongr (Equiv.refl (Fin q)) (DegreeThreshold.wireEquiv n D 0)).trans
    finProdFinEquiv

private theorem wire_val {n q D : ℕ} (i : Fin q) (v : DegreeThreshold.Vars n D 0)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    wire D (ofGraph G) i.val ((DegreeThreshold.wireEquiv n D 0 v).val) =
      (wireEquiv n q D (i, v)).val := by
  simp [wire, block, order, ofGraph, wireEquiv, Nat.add_comm]

private theorem formula_relabel {n q D : ℕ} (i : Fin q)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (F : CNF (DegreeThreshold.Vars n D 0)) :
    (F.relabel (fun v => (DegreeThreshold.wireEquiv n D 0 v).val)).relabel
      (wire D (ofGraph G) i.val) =
        F.relabel (fun v => (wireEquiv n q D (i, v)).val) := by
  simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
  congr 1
  funext c
  congr 1
  funext l
  exact Prod.ext (wire_val i l.1 G) rfl

private theorem oneHot_ofGraph {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    oneHot q D (ofGraph G) = (DegreePartition.oneHot n q D).relabel
      (fun v => (wireEquiv n q D v).val) := by
  have hsel (i : Fin q) (u : Fin n) :
      wire D (ofGraph G) i.val u.val =
        (wireEquiv n q D (DegreePartition.selection i u)).val :=
        wire_val (D := D) i (DegreeThreshold.selection 0 u) G
  change (List.range n).flatMap _ = _
  rw [← List.map_coe_finRange_eq_range]
  simp only [DegreePartition.oneHot, CNF.relabel, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro u _
  change CNF.exactlyOne ((List.finRange q).map _) = CNF.relabel
    (fun v => (wireEquiv n q D v).val) (CNF.exactlyOne ((List.finRange q).map _))
  rw [CNF.relabel_exactlyOne (fun v => (wireEquiv n q D v).val)
    (fun _ _ h => (wireEquiv n q D).injective (Fin.val_injective h))]
  congr 1
  simp only [List.map_map, Function.comp_def, hsel]

private theorem rules_ofGraph {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    rules M (ofGraph G) = (DegreePartition.rules n q D hD M).relabel
      (fun v => (wireEquiv n q D v).val) := by
  have hstate (j : Fin q) (u : Fin n) (s : Fin (D + 1)) :
      Clause.relabel (wire D (ofGraph G) j.val)
        (SigmaRho.state D (localInput (ofGraph G)) s.val u.val) =
        Clause.relabel (fun v => (wireEquiv n q D (j, v)).val) (SigmaRho.finiteState hD 0 u s) := by
    change Clause.relabel _ (SigmaRho.state D (ofGraph G, n + 0) s.val u.val) = _
    rw [SigmaRho.state_ofGraph hD 0 u s G]
    simp only [Clause.relabel, List.map_map, Function.comp_def]
    congr 1
    funext l
    exact Prod.ext (wire_val j l.1 G) rfl
  have hsel (i : Fin q) (u : Fin n) : wire D (ofGraph G) i.val u.val =
      (wireEquiv n q D (DegreePartition.selection i u)).val :=
        wire_val (D := D) i (DegreeThreshold.selection 0 u) G
  simp only [rules, DegreePartition.rules, CNF.relabel, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  apply List.flatMap_congr
  intro j _
  change (List.range n).flatMap _ = _
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro u _
  simp only [DegreePartition.ruleAt, List.map_flatMap]
  apply List.flatMap_congr
  intro st _
  split_ifs
  · rfl
  · simp only [List.map_cons, List.map_nil]
    rw [Term.negate_relabel]
    apply congrArg (fun t => [Term.negate t])
    rw [hstate, hsel]
    simp only [Clause.relabel, List.map_cons, List.map_map, Function.comp_def]
    rfl

/-- Exact erasure of the actual original-input constructor to its finite labeled model. -/
theorem build_ofGraph {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    build M (ofGraph G) = TwoBoundary.BinaryFrontend.ofFinite
      ((DegreePartition.side G q D hD M).relabel (wireEquiv n q D))
      ((DegreePartition.conditions G q D).map (CNF.relabel (wireEquiv n q D))) := by
  have hmap (F : CNF (DegreePartition.Vars n q D)) :
      (F.relabel (wireEquiv n q D)).relabel Fin.val =
        F.relabel (fun v => (wireEquiv n q D v).val) := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    rfl
  have hf (j : Fin q) :
      (DegreeThreshold.forward D (localInput (ofGraph G))).relabel (wire D (ofGraph G) j.val) =
        (DegreeThreshold.finiteForward G D 0).relabel
          (fun v => (wireEquiv n q D (j, v)).val) := by
    change (DegreeThreshold.forward D (ofGraph G, n + 0)).relabel _ = _
    rw [DegreeThreshold.forward_ofGraph G D 0]
    exact formula_relabel j G _
  have hp (j : Fin q) : (DegreeThreshold.reverse D (localInput (ofGraph G))).map
      (CNF.relabel (wire D (ofGraph G) j.val)) =
        (DegreeThreshold.finiteReverse G D 0).map
          (CNF.relabel (fun v => (wireEquiv n q D (j, v)).val)) := by
    change (DegreeThreshold.reverse D (ofGraph G, n + 0)).map _ = _
    rw [DegreeThreshold.reverse_ofGraph G D 0]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro F _
    exact formula_relabel j G F
  simp only [build, TwoBoundary.BinaryFrontend.ofFinite, hmap]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · rw [side, oneHot_ofGraph, rules_ofGraph G hD M]
    simp only [DegreePartition.side, CNF.relabel, List.map_append, List.map_flatMap,
      List.map_map, Function.comp_def]
    congr 1
    congr 1
    apply List.flatMap_congr
    intro j _
    calc
      _ = (DegreeThreshold.finiteForward G D 0).relabel
          (fun v => (wireEquiv n q D (j, v)).val) := by
        simpa only [CNF.relabel] using hf j
      _ = _ := by
        simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
        rfl
  · simp only [conditions, DegreePartition.conditions, List.map_flatMap, List.map_map]
    apply List.flatMap_congr
    intro j _
    rw [hp j]
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    rfl

open Classical in
/-- The actual original-graph writer has the finite source widths, predicate count and exact
ordinary labeled-partition count. No class-size tests are imposed by this variant. -/
theorem representation {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hD : 1 ≤ D) (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ∃ B : CNF (Fin (q * (n + D * n))), ∃ P : List (DNF (Fin (q * (n + D * n)))),
      build M (ofGraph G) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ max q (max (D + 1) 3)) ∧
      (∀ p ∈ P, ∀ t ∈ p, t.length ≤ D) ∧ P.length = q * (D * n) ∧
      Fintype.card {y : Fin (q * (n + D * n)) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
      Fintype.card {S : Fin q → Set (Fin n) //
        G.IsDegreePartition (fun i j => (M i j).counts) S} := by
  let B := (DegreePartition.side G q D hD M).relabel (wireEquiv n q D)
  let P := (DegreePartition.conditions G q D).map (CNF.relabel (wireEquiv n q D))
  obtain ⟨hb, hp, hl⟩ := DegreePartition.widths G hD M
  refine ⟨B, P, build_ofGraph G hD M, ?_, ?_, by simpa only [P, List.length_map] using hl, ?_⟩
  · intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    simpa only [Clause.relabel, List.length_map] using hb t ht
  · intro p hc t ht
    obtain ⟨localP, hlocalP, rfl⟩ := List.mem_map.mp hc
    obtain ⟨localT, hlocalT, rfl⟩ := List.mem_map.mp ht
    simpa only [Clause.relabel, List.length_map] using hp localP hlocalP localT hlocalT
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    let e : (Fin (q * (n + D * n)) → Bool) ≃ (DegreePartition.Vars n q D → Bool) :=
      Equiv.arrowCongr (wireEquiv n q D).symm (Equiv.refl Bool)
    have hc : Nat.card {y : Fin (q * (n + D * n)) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Nat.card {y : DegreePartition.Vars n q D → Bool //
          (DegreePartition.side G q D hD M).eval y = true ∧
          ∀ p ∈ DegreePartition.conditions G q D, DNF.eval y p = true} := by
      apply Nat.card_congr
      exact e.subtypeEquiv fun _ => by
        simp only [B, P, CNF.eval_relabel, List.forall_mem_map, DNF.eval_relabel]
        rfl
    exact hc.trans (DegreePartition.count_eq_partitions G hD M)

/-- Every nonempty source instance has exactly two emitted ordinary queries. -/
theorem query_count {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hn : 1 ≤ n)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build M (ofGraph G)))).length = 2 := by
  classical
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation G hD M
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

/-- Every positive-vertex source query has the exact no-test dimension and width. -/
theorem query_budget {n q D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hn : 1 ≤ n)
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (N : ℕ) (Q : CNF ℕ)
    (hQ : (N, Q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build M (ofGraph G)))) :
    N = q * (2 * D + 1) * n - 1 ∧
      ∀ c ∈ Q, c.length ≤ max q (D + 2) ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation G hD M
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

end Cslib.Logic.PL.DegreePartition.BinaryFrontend
