/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Query
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryInvariants
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Native bounded candidate recovery

All raw labels are binary. Unary iteration counts come only from actual endpoint fibers and
vertex lists. Split queries are temporary; loop states contain orders and one candidate block,
never systems or query history. Successful candidates use the existing certificate checker.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

/-- Framed fixed/free input followed by the binary current vertex. -/
abbrev encWordInput := encPair encFixedRotationInput encNat

/-- Framed input/vertex pair followed by a framed binary dart block. -/
abbrev encBlockInput := encPair encWordInput (encList encNat)

/-- Framed input/vertex pair followed by an optional framed binary dart block. -/
abbrev encAdvanceInput := encPair encWordInput (encOption (encList encNat))

private theorem redirectEnd_polyTime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => redirectEnd p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encNat (encList encNat)) (encPair encNat encNat)) encNat := by
  unfold redirectEnd
  fun_prop

/-- The split is a native list construction even on malformed raw labels and blocks. -/
private theorem splitEdges_polyTime : ComputableTidilyInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => (split p.1.1 p.1.2 p.2).graph.edges)
    encBlockInput (encList (encPair encNat encNat)) := by
  let hp := (ComputableTidilyInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy.comp hp
  let hn := ComputableTidilyInPolyTime.unary_to_binary.comp
    ((ComputableTidilyInPolyTime.length_list encNat).comp
      (encGraph_vertices_deg.computableInPolyTime.tidy.comp hg))
  let hedges := (ComputableTidilyInPolyTime.zipIdx (encPair encNat encNat)).comp
    (encGraph_edges_deg.computableInPolyTime.tidy.comp hg)
  unfold split
  apply ComputableTidilyInPolyTime.listAppend'
  · apply ComputableTidilyInPolyTime.mapWithInput hedges
    let he := ComputableTidilyInPolyTime.snd encBlockInput
      (encPair (encPair encNat encNat) encUnary)
    let hcap := (hn.prod (ComputableTidilyInPolyTime.snd encWordInput (encList encNat))).comp
      (ComputableTidilyInPolyTime.fst encBlockInput (encPair (encPair encNat encNat) encUnary))
    let hi := ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const 2).prod he.snd'))
    let hj := ComputableTidilyInPolyTime.binary_add' hi (ComputableTidilyInPolyTime.const 1)
    exact (redirectEnd_polyTime.comp (hcap.prod (hi.prod he.fst'.fst'))).prod
      (redirectEnd_polyTime.comp (hcap.prod (hj.prod he.fst'.snd')))
  · exact ComputableTidilyInPolyTime.cons'
      (hn.prod ((ComputableTidilyInPolyTime.snd encFixedRotationInput encNat).comp
        (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))))
      (ComputableTidilyInPolyTime.const [])

private theorem splitOrders_polyTime : ComputableTidilyInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => (split p.1.1 p.1.2 p.2).orders)
    encBlockInput (encList (encOption (encList encNat))) := by
  let hp := (ComputableTidilyInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy.comp hp
  let ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy.comp hp
  let hm := ComputableTidilyInPolyTime.unary_to_binary.comp
    (ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const 2).prod
      ((ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
        (encGraph_edges_deg.computableInPolyTime.tidy.comp hg))))
  unfold split
  apply ComputableTidilyInPolyTime.listAppend'
  · exact ho
  · apply ComputableTidilyInPolyTime.cons'
    · apply (ComputableTidilyInPolyTime.optionSome (encList encNat)).comp
      apply ComputableTidilyInPolyTime.listAppend' (ComputableTidilyInPolyTime.snd _ _)
      exact ComputableTidilyInPolyTime.cons' hm (ComputableTidilyInPolyTime.const [])
    · exact ComputableTidilyInPolyTime.const []

/-- The split is a native list construction even on malformed raw labels and blocks. -/
theorem split_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => split p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  let hp := (ComputableTidilyInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy.comp hp
  have hr : ComputableTidilyInPolyTime
      (fun p : (FixedRotationInput × ℕ) × List ℕ => List.range (p.1.1.graph.vertices.length + 1))
      encBlockInput (encList encNat) := by
    have hc : ComputableTidilyInPolyTime
        (fun p : (FixedRotationInput × ℕ) × List ℕ => p.1.1.graph.vertices.length + 1)
        encBlockInput encUnary := ComputableTidilyInPolyTime.unary_add.comp
      (((ComputableTidilyInPolyTime.length_list encNat).comp
        (encGraph_vertices_deg.computableInPolyTime.tidy.comp hg)).prod
        (ComputableTidilyInPolyTime.const 1))
    simpa [Function.comp_def] using ((ComputableTidilyInPolyTime.map
      ComputableTidilyInPolyTime.unary_to_binary).comp ComputableTidilyInPolyTime.range).comp hc
  exact encFixedRotationInput_mk_polyTime
    (encGraph_mk_polyTime (ComputableInPolyTime.of_tidy hr)
      (ComputableInPolyTime.of_tidy splitEdges_polyTime))
    (ComputableInPolyTime.of_tidy splitOrders_polyTime)

/-- Only actual unused fiber darts are scanned as candidates. -/
theorem remaining_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => remaining p.1.1 p.1.2 p.2)
    encBlockInput (encList encNat) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold remaining
  apply ComputableTidilyInPolyTime.filterWithInput
    (fiber_polyTime.tidy.comp (g := fun p : (FixedRotationInput × ℕ) × List ℕ =>
      (p.1.1.graph, p.1.2)) (by unfold encBlockInput encWordInput; fun_prop))
  unfold encBlockInput encWordInput
  fun_prop

/-- First-candidate search actually calls the concrete native XOR query on each ephemeral split. -/
theorem nextCandidate_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => nextCandidate p.1.1 p.1.2 p.2)
    encBlockInput (encOption encNat) := by
  apply ComputableInPolyTime.of_tidy
  unfold nextCandidate
  apply ComputableTidilyInPolyTime.findWithInput remaining_polyTime.tidy
  exact query_polyTime.tidy.comp (split_polyTime.tidy.comp
    (g := fun p : ((FixedRotationInput × ℕ) × List ℕ) × ℕ =>
      (p.1.1, p.1.2 ++ [p.2])) (by unfold encBlockInput encWordInput; fun_prop))

/-- A block step has native time independent of query feasibility or input validity. -/
theorem advance_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × Option (List ℕ) => advance p.1.1 p.1.2 p.2)
    encAdvanceInput (encOption (encList encNat)) := by
  have hr := remaining_polyTime.tidy
  have hc := nextCandidate_polyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold advance
  apply ComputableTidilyInPolyTime.optionElimWithInput
    (ComputableTidilyInPolyTime.snd _ _) (ComputableTidilyInPolyTime.const none)
  apply ComputableTidilyInPolyTime.ite' (encC := encBool)
  · exact (ComputableTidilyInPolyTime.listIsEmpty' encNat).comp (hr.comp
      (g := fun p : ((FixedRotationInput × ℕ) × Option (List ℕ)) × List ℕ =>
        (p.1.1, p.2)) (by simp only [encBlockInput, encWordInput]; fun_prop))
  · fun_prop
  · apply ComputableTidilyInPolyTime.optionElimWithInput
      (hc.comp (g := fun p : ((FixedRotationInput × ℕ) × Option (List ℕ)) × List ℕ =>
        (p.1.1, p.2)) (by simp only [encBlockInput, encWordInput]; fun_prop))
      (ComputableTidilyInPolyTime.const none)
    simp only [encWordInput]
    fun_prop

/-- Bounded word recovery is native polynomial-time on all raw input/vertex pairs. The loop
stores only one optional block and adds at most one bounded dart per iteration. -/
theorem recoverWord_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × ℕ => recoverWord p.1 p.2)
    encWordInput (encOption (encList encNat)) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy
  have hf : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ℕ => fiber p.1.graph p.2)
      encWordInput (encList encNat) :=
    fiber_polyTime.tidy.comp ((hg.comp (ComputableTidilyInPolyTime.fst _ _)).prod
      (ComputableTidilyInPolyTime.snd _ _))
  have hm : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ℕ => p.1.graph.edges.length) encWordInput encUnary :=
    (ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
      ((encGraph_edges_deg.computableInPolyTime.tidy.comp hg).comp
        (ComputableTidilyInPolyTime.fst _ _))
  apply ComputableInPolyTime.of_tidy
  unfold recoverWord
  apply ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (par := fun p : FixedRotationInput × ℕ => p)
    (step := fun p state => advance p.1 p.2 state)
    (ComputableTidilyInPolyTime.id')
  · exact ComputableTidilyInPolyTime.unary_sub.comp
      (((ComputableTidilyInPolyTime.length_list encNat).comp hf).prod
        (ComputableTidilyInPolyTime.const 1))
  · apply (ComputableTidilyInPolyTime.optionSome (encList encNat)).comp
    apply ComputableTidilyInPolyTime.ite' (encC := encBool)
      ((ComputableTidilyInPolyTime.listIsEmpty' encNat).comp hf)
      (ComputableTidilyInPolyTime.const [])
    exact ComputableTidilyInPolyTime.cons'
      ((ComputableTidilyInPolyTime.headD 0).comp hf) (ComputableTidilyInPolyTime.const [])
  · exact advance_polyTime.tidy
  · exact ((PolyBounded.const 4).mul hm.polyBounded).add (.const 1)
  · intro p state
    exact (length_enc_advance p.1 p.2 state).trans (by omega)

/-- Replacement of a complete order is native; supplied vertex labels stay binary. -/
theorem prescribe_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => prescribe p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  let hp := (ComputableTidilyInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy.comp hp
  let ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy.comp hp
  have ht : ComputableTidilyInPolyTime
      (fun p : (FixedRotationInput × ℕ) × List ℕ => (prescribe p.1.1 p.1.2 p.2).orders)
      encBlockInput (encList (encOption (encList encNat))) := by
    unfold prescribe
    apply ComputableTidilyInPolyTime.mapWithInput
      ((ComputableTidilyInPolyTime.zipIdx (encOption (encList encNat))).comp ho)
    let he := ComputableTidilyInPolyTime.snd encBlockInput
      (encPair (encOption (encList encNat)) encUnary)
    let hp' := ComputableTidilyInPolyTime.fst encBlockInput
      (encPair (encOption (encList encNat)) encUnary)
    let hi := ComputableTidilyInPolyTime.unary_to_binary.comp he.snd'
    let hv := ((ComputableTidilyInPolyTime.snd encFixedRotationInput encNat).comp
      (ComputableTidilyInPolyTime.fst encWordInput (encList encNat))).comp hp'
    exact ComputableTidilyInPolyTime.ite_decide (hi.decide_eq' hv)
      ((ComputableTidilyInPolyTime.optionSome (encList encNat)).comp
        ((ComputableTidilyInPolyTime.snd encWordInput (encList encNat)).comp hp')) he.fst'
  exact encFixedRotationInput_mk_polyTime
    (ComputableInPolyTime.of_tidy hg) (ComputableInPolyTime.of_tidy ht)

/-- A complete-vertex step uses only the current optional state and a binary vertex. -/
theorem completeVertex_polyTime : ComputableInPolyTime
    (fun p : Option FixedRotationInput × ℕ => completeVertex p.1 p.2)
    (encPair (encOption encFixedRotationInput) encNat) (encOption encFixedRotationInput) := by
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold completeVertex
  apply ComputableTidilyInPolyTime.optionElimWithInput
    (ComputableTidilyInPolyTime.fst _ _) (ComputableTidilyInPolyTime.const none)
  apply ComputableTidilyInPolyTime.ite' (encC := encBool)
  · exact (ComputableTidilyInPolyTime.listGetD_binary (encA := encOption (encList encNat)) none
      (ho.comp (ComputableTidilyInPolyTime.snd _ _))
      (by fun_prop)).optionIsSome
  · fun_prop
  · apply ComputableTidilyInPolyTime.optionElimWithInput
      (recoverWord_polyTime.tidy.comp
        (g := fun p : (Option FixedRotationInput × ℕ) × FixedRotationInput => (p.2, p.1.2))
        (by unfold encWordInput; fun_prop)) (ComputableTidilyInPolyTime.const none)
    exact (ComputableTidilyInPolyTime.optionSome encFixedRotationInput).comp
      (prescribe_polyTime.tidy.comp
        (g := fun p : ((Option FixedRotationInput × ℕ) × FixedRotationInput) × List ℕ =>
          ((p.1.2, p.1.1.2), p.2)) (by unfold encBlockInput encWordInput; fun_prop))

/-- Native outer recovery stores only original-graph orders. The prefix bound is proved from
the actual implementation, with no resource-provider premise. -/
theorem recoverOrders_polyTime : ComputableInPolyTime recoverOrders
    encFixedRotationInput (encOption encFixedRotationInput) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy
  have hn := (ComputableTidilyInPolyTime.length_list encNat).comp
    (encGraph_vertices_deg.computableInPolyTime.tidy.comp hg)
  have hm := (ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
    (encGraph_edges_deg.computableInPolyTime.tidy.comp hg)
  have hw := (ComputableTidilyInPolyTime.length_list (encOption (encList encNat))).comp ho
  have hr : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => List.range I.graph.vertices.length)
      encFixedRotationInput (encList encNat) := by
    simpa [Function.comp_def] using ((ComputableTidilyInPolyTime.map
      ComputableTidilyInPolyTime.unary_to_binary).comp ComputableTidilyInPolyTime.range).comp hn
  have hb : PolyBounded (fun I => (encFixedRotationInput I).length)
      (fun I => (encFixedRotationInput I).length + 1 +
        I.graph.vertices.length * outerGrowth I) := by
    unfold outerGrowth
    exact (PolyBounded.self.add (.const 1)).add
      (hn.polyBounded.mul (hw.polyBounded.mul ((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hm.polyBounded).mul
          (((PolyBounded.const 4).mul hm.polyBounded).add (.const 1))).add (.const 1)))))
  apply ComputableInPolyTime.of_tidy
  unfold recoverOrders
  apply ComputableTidilyInPolyTime.foldl' hr
    (ComputableTidilyInPolyTime.optionSome encFixedRotationInput) completeVertex_polyTime.tidy hb
  intro I i hi
  rcases completeVertex_fold I ((List.range I.graph.vertices.length).take i) with
    hn | ⟨J, hj, _, _, hb⟩
  · rw [hn, encOption_none, List.length_nil]
    exact Nat.zero_le _
  · rw [hj, encOption_some, List.length_cons]
    have hlen : ((List.range I.graph.vertices.length).take i).length ≤
        I.graph.vertices.length := by simp
    exact hb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (outerGrowth I) hlen) _)

/-- Native cyclic successor lookup, with unary word position and binary word entries. -/
theorem nextInWord_polyTime : ComputableInPolyTime
    (fun p : List ℕ × ℕ => nextInWord p.1 p.2)
    (encPair (encList encNat) encUnary) encNat := by
  apply ComputableInPolyTime.of_tidy
  unfold nextInWord
  let hl := ComputableTidilyInPolyTime.fst (encList encNat) encUnary
  let hi := ComputableTidilyInPolyTime.unary_add.comp
    ((ComputableTidilyInPolyTime.snd (encList encNat) encUnary).prod
      (ComputableTidilyInPolyTime.const 1))
  let hn := (ComputableTidilyInPolyTime.length_list encNat).comp hl
  exact ComputableTidilyInPolyTime.listGetD_binary 0 hl
    (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.ite_decide
        (ComputableTidilyInPolyTime.unary_lt' hi hn) hi (ComputableTidilyInPolyTime.const 0)))

/-- Assemble one binary successor per original dart using saturating binary endpoint lookup. -/
theorem certificate_polyTime : ComputableInPolyTime certificate
    encFixedRotationInput encRotationCertificate := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy
  have hc : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => 2 * I.graph.edges.length) encFixedRotationInput encUnary :=
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
        (encGraph_edges_polyTime (ComputableInPolyTime.of_tidy hg)))).tidy
  have hr : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => List.range (2 * I.graph.edges.length))
      encFixedRotationInput (encList encNat) := by
    simpa [Function.comp_def] using ((ComputableTidilyInPolyTime.map
      ComputableTidilyInPolyTime.unary_to_binary).comp ComputableTidilyInPolyTime.range).comp hc
  have hendpoints : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => I.graph.incidenceVertices)
      encFixedRotationInput (encList encNat) :=
    RotationCertificate.incidenceVertices_polyTime.tidy.comp hg
  have hword : ComputableTidilyInPolyTime
      (fun p : FixedRotationInput × ℕ =>
        (p.1.orders.getD (p.1.graph.incidenceVertices.getD p.2 0) none).getD [])
      encWordInput (encList encNat) := by
    apply ComputableTidilyInPolyTime.optionGetDWithInput
    · exact ComputableTidilyInPolyTime.listGetD_binary (encA := encOption (encList encNat)) none
        (ho.comp (ComputableTidilyInPolyTime.fst _ _))
        (ComputableTidilyInPolyTime.listGetD_binary 0
          (hendpoints.comp (ComputableTidilyInPolyTime.fst _ _))
          (ComputableTidilyInPolyTime.snd _ _))
    · exact ComputableTidilyInPolyTime.const []
  have hlist : ComputableTidilyInPolyTime
      (fun I : FixedRotationInput => (certificate I).successor)
      encFixedRotationInput (encList encNat) := by
    unfold certificate
    apply ComputableTidilyInPolyTime.mapWithInput hr
    exact nextInWord_polyTime.tidy.comp (hword.prod
      (ComputableTidilyInPolyTime.idxOfWithInput hword (ComputableTidilyInPolyTime.snd _ _)))
  exact .of_tidy (hlist.of_enc_eq fun _ => rfl)

/-- Framed fixed/free input followed by an existing binary successor certificate. -/
abbrev encFixedCertificate := encPair encFixedRotationInput encRotationCertificate

/-- The supplied complete-word guard is native on all raw words and successor tables. -/
theorem verifyFixed_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × RotationCertificate => verifyFixed p.1 p.2)
    encFixedCertificate encBool := by
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime.tidy
  have hs := encRotationCertificate_successor_deg.computableInPolyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold verifyFixed
  apply ComputableTidilyInPolyTime.allWithInput
    (ho.comp (ComputableTidilyInPolyTime.fst _ _))
  apply ComputableTidilyInPolyTime.optionElimWithInput
    (ComputableTidilyInPolyTime.snd _ _) (ComputableTidilyInPolyTime.const true)
  apply ComputableTidilyInPolyTime.allWithInput
    ((ComputableTidilyInPolyTime.zipIdx encNat).comp (ComputableTidilyInPolyTime.snd _ _))
  apply ComputableTidilyInPolyTime.decide_eq'
  · exact ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) 0
      (hs.comp (by fun_prop)) (by fun_prop)
  · exact nextInWord_polyTime.tidy.comp
      (g := fun p : (((FixedRotationInput × RotationCertificate) × Option (List ℕ)) × List ℕ) ×
          (ℕ × ℕ) => (p.1.2, p.2.2)) (by fun_prop)

/-- The complete concrete candidate driver has native polynomial time on every raw input.
Its sound guard uses the existing numerical checker; completeness remains separate. -/
theorem recover_polyTime : ComputableInPolyTime recover encFixedRotationInput
    (encOption encRotationCertificate) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime.tidy
  apply ComputableInPolyTime.of_tidy
  unfold recover
  apply ComputableTidilyInPolyTime.ite' (encC := encBool) query_polyTime.tidy
  · apply ComputableTidilyInPolyTime.optionElimWithInput recoverOrders_polyTime.tidy
      (ComputableTidilyInPolyTime.const none)
    have hc := certificate_polyTime.tidy.comp
      (ComputableTidilyInPolyTime.snd encFixedRotationInput encFixedRotationInput)
    apply ComputableTidilyInPolyTime.ite' (encC := encBool)
    · exact (RotationCertificate.computableInPolyTime_verifyGenusZero.tidy.comp
        ((hg.comp (ComputableTidilyInPolyTime.fst _ _)).prod hc)).bool_and'
        (verifyFixed_polyTime.tidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod hc))
    · exact (ComputableTidilyInPolyTime.optionSome encRotationCertificate).comp hc
    · exact ComputableTidilyInPolyTime.const none
  · exact ComputableTidilyInPolyTime.const none

private theorem numVars_binary_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableTidilyInPolyTime (fun F : Cslib.Logic.PL.CSP Rel V => F.numVars)
      (encCSP encRel encV) encNat := by
  have hu := (Cslib.Logic.PL.CNF.computableInPolyTime_numVars encV).tidy.comp
    (CSP.computableInPolyTime_varCNF encRel encV).tidy
  simpa only [Function.comp_def, Cslib.Logic.PL.CSP.numVars_varCNF] using
    ComputableTidilyInPolyTime.unary_to_binary.comp hu

/-- Fixing the full orders after a free vertex prefix scans the listed graph only. Its raw
binary cutoff is compared with labels, never converted into a unary scan bound. -/
theorem freePrefix_polyTime : ComputableInPolyTime
    (fun p : Graph × ℕ => freePrefix p.1 p.2)
    (encPair encGraph encNat) encFixedRotationInput := by
  let hg := ComputableTidilyInPolyTime.fst encGraph encNat
  have ho : ComputableTidilyInPolyTime
      (fun p : Graph × ℕ => (freePrefix p.1 p.2).orders)
      (encPair encGraph encNat) (encList (encOption (encList encNat))) := by
    unfold freePrefix
    apply ComputableTidilyInPolyTime.mapWithInput
      (encGraph_vertices_deg.computableInPolyTime.tidy.comp hg)
    let hp := ComputableTidilyInPolyTime.fst (encPair encGraph encNat) encNat
    let hv := ComputableTidilyInPolyTime.snd (encPair encGraph encNat) encNat
    exact ComputableTidilyInPolyTime.ite_decide
      (ComputableTidilyInPolyTime.binary_lt' hv
        ((ComputableTidilyInPolyTime.snd encGraph encNat).comp hp))
      (ComputableTidilyInPolyTime.const none)
      ((ComputableTidilyInPolyTime.optionSome (encList encNat)).comp
        (fiber_polyTime.tidy.comp ((hg.comp hp).prod hv)))
  exact encFixedRotationInput_mk_polyTime
    (ComputableInPolyTime.of_tidy hg) (ComputableInPolyTime.of_tidy ho)

/-- Original CSP scopes compile through the existing dense incidence graph. Binary source
names are compared as bit strings; relation semantics and declared arity fund no scans. -/
theorem ofCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (ofCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) encFixedRotationInput :=
  freePrefix_polyTime.comp
    (g := fun F : Cslib.Logic.PL.CSP Rel V => (CSP.incidenceGraph F, F.numVars))
    ((CSP.computableInPolyTime_incidenceGraph encRel encV).prod
      (numVars_binary_polyTime encRel encV).computableInPolyTime)

/-- Bare original CSP recovery is a native polynomial-time program using the concrete XOR
solver and the existing original-position certificate checker, on every raw encoded CSP. -/
theorem recoverCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (recoverCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) (encOption encRotationCertificate) := by
  apply ComputableInPolyTime.of_tidy
  unfold recoverCSP
  apply ComputableTidilyInPolyTime.optionElimWithInput
    (recover_polyTime.tidy.comp (ofCSP_polyTime encRel encV).tidy)
    (ComputableTidilyInPolyTime.const none)
  apply ComputableTidilyInPolyTime.ite' (encC := encBool)
    (CSP.computableInPolyTime_verifyRotationCertificate encRel encV).tidy
  · exact (ComputableTidilyInPolyTime.optionSome encRotationCertificate).comp
      (ComputableTidilyInPolyTime.snd _ _)
  · exact ComputableTidilyInPolyTime.const none

end Cslib.Complexity.Graph.RotationRecognition
