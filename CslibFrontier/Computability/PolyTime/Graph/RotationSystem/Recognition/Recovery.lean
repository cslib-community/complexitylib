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

private theorem redirectEnd_polyTime : ComputableInPolyTime
    (fun p : (ℕ × List ℕ) × (ℕ × ℕ) => redirectEnd p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encNat (encList encNat)) (encPair encNat encNat)) encNat := by
  unfold redirectEnd
  fun_prop

/-- The split is a native list construction even on malformed raw labels and blocks. -/
private theorem splitEdges_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => (split p.1.1 p.1.2 p.2).graph.edges)
    encBlockInput (encList (encPair encNat encNat)) := by
  let hp := (ComputableInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.comp hp
  let hn := ComputableInPolyTime.unary_to_binary.comp
    ((ComputableInPolyTime.length_list encNat).comp
      (encGraph_vertices_deg.computableInPolyTime.comp hg))
  let hedges := (ComputableInPolyTime.zipIdx (encPair encNat encNat)).comp
    (encGraph_edges_deg.computableInPolyTime.comp hg)
  unfold split
  apply ComputableInPolyTime.listAppend'
  · apply ComputableInPolyTime.mapWithInput hedges
    let he := ComputableInPolyTime.snd encBlockInput
      (encPair (encPair encNat encNat) encUnary)
    let hcap := (hn.prod (ComputableInPolyTime.snd encWordInput (encList encNat))).comp
      (ComputableInPolyTime.fst encBlockInput (encPair (encPair encNat encNat) encUnary))
    let hi := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_mul.comp
        ((ComputableInPolyTime.const 2).prod he.snd'))
    let hj := ComputableInPolyTime.binary_add' hi (ComputableInPolyTime.const 1)
    exact (redirectEnd_polyTime.comp (hcap.prod (hi.prod he.fst'.fst'))).prod
      (redirectEnd_polyTime.comp (hcap.prod (hj.prod he.fst'.snd')))
  · exact ComputableInPolyTime.cons'
      (hn.prod ((ComputableInPolyTime.snd encFixedRotationInput encNat).comp
        (ComputableInPolyTime.fst encWordInput (encList encNat))))
      (ComputableInPolyTime.const [])

private theorem splitOrders_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => (split p.1.1 p.1.2 p.2).orders)
    encBlockInput (encList (encOption (encList encNat))) := by
  let hp := (ComputableInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.comp hp
  let ho := encFixedRotationInput_orders_deg.computableInPolyTime.comp hp
  let hm := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod
      ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
        (encGraph_edges_deg.computableInPolyTime.comp hg))))
  unfold split
  apply ComputableInPolyTime.listAppend'
  · exact ho
  · apply ComputableInPolyTime.cons'
    · apply (ComputableInPolyTime.optionSome (encList encNat)).comp
      apply ComputableInPolyTime.listAppend' (ComputableInPolyTime.snd _ _)
      exact ComputableInPolyTime.cons' hm (ComputableInPolyTime.const [])
    · exact ComputableInPolyTime.const []

/-- The split is a native list construction even on malformed raw labels and blocks. -/
theorem split_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => split p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  let hp := (ComputableInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.comp hp
  have hr : ComputableInPolyTime
      (fun p : (FixedRotationInput × ℕ) × List ℕ => List.range (p.1.1.graph.vertices.length + 1))
      encBlockInput (encList encNat) := by
    have hc : ComputableInPolyTime
        (fun p : (FixedRotationInput × ℕ) × List ℕ => p.1.1.graph.vertices.length + 1)
        encBlockInput encUnary := ComputableInPolyTime.unary_add.comp
      (((ComputableInPolyTime.length_list encNat).comp
        (encGraph_vertices_deg.computableInPolyTime.comp hg)).prod
        (ComputableInPolyTime.const 1))
    simpa [Function.comp_def] using ((ComputableInPolyTime.map
      ComputableInPolyTime.unary_to_binary).comp ComputableInPolyTime.range).comp hc
  exact encFixedRotationInput_mk_polyTime
    (encGraph_mk_polyTime hr
      splitEdges_polyTime)
    splitOrders_polyTime

/-- Only actual unused fiber darts are scanned as candidates. -/
theorem remaining_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => remaining p.1.1 p.1.2 p.2)
    encBlockInput (encList encNat) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime
  unfold remaining
  apply ComputableInPolyTime.filterWithInput
    (fiber_polyTime.comp (g := fun p : (FixedRotationInput × ℕ) × List ℕ =>
      (p.1.1.graph, p.1.2)) (by unfold encBlockInput encWordInput; fun_prop))
  unfold encBlockInput encWordInput
  fun_prop

/-- First-candidate search actually calls the concrete native XOR query on each ephemeral split. -/
theorem nextCandidate_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => nextCandidate p.1.1 p.1.2 p.2)
    encBlockInput (encOption encNat) := by
  unfold nextCandidate
  apply ComputableInPolyTime.findWithInput remaining_polyTime
  exact query_polyTime.comp (split_polyTime.comp
    (g := fun p : ((FixedRotationInput × ℕ) × List ℕ) × ℕ =>
      (p.1.1, p.1.2 ++ [p.2])) (by unfold encBlockInput encWordInput; fun_prop))

/-- A block step has native time independent of query feasibility or input validity. -/
theorem advance_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × Option (List ℕ) => advance p.1.1 p.1.2 p.2)
    encAdvanceInput (encOption (encList encNat)) := by
  have hr := remaining_polyTime
  have hc := nextCandidate_polyTime
  unfold advance
  apply ComputableInPolyTime.optionElimWithInput
    (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.const none)
  apply ComputableInPolyTime.ite' (encC := encBool)
  · exact (ComputableInPolyTime.listIsEmpty (encA := encNat)).comp (hr.comp
      (g := fun p : ((FixedRotationInput × ℕ) × Option (List ℕ)) × List ℕ =>
        (p.1.1, p.2)) (by simp only [encBlockInput, encWordInput]; fun_prop))
  · fun_prop
  · apply ComputableInPolyTime.optionElimWithInput
      (hc.comp (g := fun p : ((FixedRotationInput × ℕ) × Option (List ℕ)) × List ℕ =>
        (p.1.1, p.2)) (by simp only [encBlockInput, encWordInput]; fun_prop))
      (ComputableInPolyTime.const none)
    simp only [encWordInput]
    fun_prop

/-- Bounded word recovery is native polynomial-time on all raw input/vertex pairs. The loop
stores only one optional block and adds at most one bounded dart per iteration. -/
theorem recoverWord_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × ℕ => recoverWord p.1 p.2)
    encWordInput (encOption (encList encNat)) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime
  have hf : ComputableInPolyTime
      (fun p : FixedRotationInput × ℕ => fiber p.1.graph p.2)
      encWordInput (encList encNat) :=
    fiber_polyTime.comp ((hg.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))
  have hm : ComputableInPolyTime
      (fun p : FixedRotationInput × ℕ => p.1.graph.edges.length) encWordInput encUnary :=
    (ComputableInPolyTime.length_list (encPair encNat encNat)).comp
      ((encGraph_edges_deg.computableInPolyTime.comp hg).comp
        (ComputableInPolyTime.fst _ _))
  unfold recoverWord
  apply ComputableInPolyTime.iterateWith_of_bounded_growth
    (par := fun p : FixedRotationInput × ℕ => p)
    (step := fun p state => advance p.1 p.2 state)
    (ComputableInPolyTime.id')
  · exact ComputableInPolyTime.unary_sub.comp
      (((ComputableInPolyTime.length_list encNat).comp hf).prod
        (ComputableInPolyTime.const 1))
  · apply (ComputableInPolyTime.optionSome (encList encNat)).comp
    apply ComputableInPolyTime.ite' (encC := encBool)
      ((ComputableInPolyTime.listIsEmpty (encA := encNat)).comp hf)
      (ComputableInPolyTime.const [])
    exact ComputableInPolyTime.cons'
      ((ComputableInPolyTime.headD 0).comp hf) (ComputableInPolyTime.const [])
  · exact advance_polyTime
  · exact ((PolyBounded.const 4).mul hm.polyBounded).add (.const 1)
  · intro p state
    exact (length_enc_advance p.1 p.2 state).trans (by omega)

/-- Replacement of a complete order is native; supplied vertex labels stay binary. -/
theorem prescribe_polyTime : ComputableInPolyTime
    (fun p : (FixedRotationInput × ℕ) × List ℕ => prescribe p.1.1 p.1.2 p.2)
    encBlockInput encFixedRotationInput := by
  let hp := (ComputableInPolyTime.fst encFixedRotationInput encNat).comp
    (ComputableInPolyTime.fst encWordInput (encList encNat))
  let hg := encFixedRotationInput_graph_deg.computableInPolyTime.comp hp
  let ho := encFixedRotationInput_orders_deg.computableInPolyTime.comp hp
  have ht : ComputableInPolyTime
      (fun p : (FixedRotationInput × ℕ) × List ℕ => (prescribe p.1.1 p.1.2 p.2).orders)
      encBlockInput (encList (encOption (encList encNat))) := by
    unfold prescribe
    apply ComputableInPolyTime.mapWithInput
      ((ComputableInPolyTime.zipIdx (encOption (encList encNat))).comp ho)
    let he := ComputableInPolyTime.snd encBlockInput
      (encPair (encOption (encList encNat)) encUnary)
    let hp' := ComputableInPolyTime.fst encBlockInput
      (encPair (encOption (encList encNat)) encUnary)
    let hi := ComputableInPolyTime.unary_to_binary.comp he.snd'
    let hv := ((ComputableInPolyTime.snd encFixedRotationInput encNat).comp
      (ComputableInPolyTime.fst encWordInput (encList encNat))).comp hp'
    exact ComputableInPolyTime.ite_decide (hi.decide_eq' hv)
      ((ComputableInPolyTime.optionSome (encList encNat)).comp
        ((ComputableInPolyTime.snd encWordInput (encList encNat)).comp hp')) he.fst'
  exact encFixedRotationInput_mk_polyTime
    hg ht

/-- A complete-vertex step uses only the current optional state and a binary vertex. -/
theorem completeVertex_polyTime : ComputableInPolyTime
    (fun p : Option FixedRotationInput × ℕ => completeVertex p.1 p.2)
    (encPair (encOption encFixedRotationInput) encNat) (encOption encFixedRotationInput) := by
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime
  unfold completeVertex
  apply ComputableInPolyTime.optionElimWithInput
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const none)
  apply ComputableInPolyTime.ite' (encC := encBool)
  · exact (ComputableInPolyTime.listGetD_binary (encA := encOption (encList encNat)) none
      (ho.comp (ComputableInPolyTime.snd _ _))
      (by fun_prop)).optionIsSome
  · fun_prop
  · apply ComputableInPolyTime.optionElimWithInput
      (recoverWord_polyTime.comp
        (g := fun p : (Option FixedRotationInput × ℕ) × FixedRotationInput => (p.2, p.1.2))
        (by unfold encWordInput; fun_prop)) (ComputableInPolyTime.const none)
    exact (ComputableInPolyTime.optionSome encFixedRotationInput).comp
      (prescribe_polyTime.comp
        (g := fun p : ((Option FixedRotationInput × ℕ) × FixedRotationInput) × List ℕ =>
          ((p.1.2, p.1.1.2), p.2)) (by unfold encBlockInput encWordInput; fun_prop))

/-- Native outer recovery stores only original-graph orders. The prefix bound is proved from
the actual implementation, with no resource-provider premise. -/
theorem recoverOrders_polyTime : ComputableInPolyTime recoverOrders
    encFixedRotationInput (encOption encFixedRotationInput) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime
  have hn := (ComputableInPolyTime.length_list encNat).comp
    (encGraph_vertices_deg.computableInPolyTime.comp hg)
  have hm := (ComputableInPolyTime.length_list (encPair encNat encNat)).comp
    (encGraph_edges_deg.computableInPolyTime.comp hg)
  have hw := (ComputableInPolyTime.length_list (encOption (encList encNat))).comp ho
  have hr : ComputableInPolyTime
      (fun I : FixedRotationInput => List.range I.graph.vertices.length)
      encFixedRotationInput (encList encNat) := by
    simpa [Function.comp_def] using ((ComputableInPolyTime.map
      ComputableInPolyTime.unary_to_binary).comp ComputableInPolyTime.range).comp hn
  have hb : PolyBounded (fun I => (encFixedRotationInput I).length)
      (fun I => (encFixedRotationInput I).length + 1 +
        I.graph.vertices.length * outerGrowth I) := by
    unfold outerGrowth
    exact (PolyBounded.self.add (.const 1)).add
      (hn.polyBounded.mul (hw.polyBounded.mul ((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hm.polyBounded).mul
          (((PolyBounded.const 4).mul hm.polyBounded).add (.const 1))).add (.const 1)))))
  unfold recoverOrders
  apply ComputableInPolyTime.foldl' hr
    (ComputableInPolyTime.optionSome encFixedRotationInput) completeVertex_polyTime hb
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
  unfold nextInWord
  let hl := ComputableInPolyTime.fst (encList encNat) encUnary
  let hi := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.snd (encList encNat) encUnary).prod
      (ComputableInPolyTime.const 1))
  let hn := (ComputableInPolyTime.length_list encNat).comp hl
  exact ComputableInPolyTime.listGetD_binary 0 hl
    (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.ite_decide
        (ComputableInPolyTime.unary_lt' hi hn) hi (ComputableInPolyTime.const 0)))

/-- Assemble one binary successor per original dart using saturating binary endpoint lookup. -/
theorem certificate_polyTime : ComputableInPolyTime certificate
    encFixedRotationInput encRotationCertificate := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime
  have hc : ComputableInPolyTime
      (fun I : FixedRotationInput => 2 * I.graph.edges.length) encFixedRotationInput encUnary :=
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
        (encGraph_edges_polyTime hg)))
  have hr : ComputableInPolyTime
      (fun I : FixedRotationInput => List.range (2 * I.graph.edges.length))
      encFixedRotationInput (encList encNat) := by
    simpa [Function.comp_def] using ((ComputableInPolyTime.map
      ComputableInPolyTime.unary_to_binary).comp ComputableInPolyTime.range).comp hc
  have hendpoints : ComputableInPolyTime
      (fun I : FixedRotationInput => I.graph.incidenceVertices)
      encFixedRotationInput (encList encNat) :=
    RotationCertificate.incidenceVertices_polyTime.comp hg
  have hword : ComputableInPolyTime
      (fun p : FixedRotationInput × ℕ =>
        (p.1.orders.getD (p.1.graph.incidenceVertices.getD p.2 0) none).getD [])
      encWordInput (encList encNat) := by
    apply ComputableInPolyTime.optionGetDWithInput
    · exact ComputableInPolyTime.listGetD_binary (encA := encOption (encList encNat)) none
        (ho.comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.listGetD_binary 0
          (hendpoints.comp (ComputableInPolyTime.fst _ _))
          (ComputableInPolyTime.snd _ _))
    · exact ComputableInPolyTime.const []
  have hlist : ComputableInPolyTime
      (fun I : FixedRotationInput => (certificate I).successor)
      encFixedRotationInput (encList encNat) := by
    unfold certificate
    apply ComputableInPolyTime.mapWithInput hr
    exact nextInWord_polyTime.comp (hword.prod
      (ComputableInPolyTime.idxOfWithInput hword (ComputableInPolyTime.snd _ _)))
  exact (hlist.of_enc_eq fun _ => rfl)

/-- Framed fixed/free input followed by an existing binary successor certificate. -/
abbrev encFixedCertificate := encPair encFixedRotationInput encRotationCertificate

/-- The supplied complete-word guard is native on all raw words and successor tables. -/
theorem verifyFixed_polyTime : ComputableInPolyTime
    (fun p : FixedRotationInput × RotationCertificate => verifyFixed p.1 p.2)
    encFixedCertificate encBool := by
  have ho := encFixedRotationInput_orders_deg.computableInPolyTime
  have hs := encRotationCertificate_successor_deg.computableInPolyTime
  unfold verifyFixed
  apply ComputableInPolyTime.allWithInput
    (ho.comp (ComputableInPolyTime.fst _ _))
  apply ComputableInPolyTime.optionElimWithInput
    (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.const true)
  apply ComputableInPolyTime.allWithInput
    ((ComputableInPolyTime.zipIdx encNat).comp (ComputableInPolyTime.snd _ _))
  apply ComputableInPolyTime.decide_eq'
  · exact ComputableInPolyTime.listGetD_binary (encA := encNat) 0
      (hs.comp (by fun_prop)) (by fun_prop)
  · exact nextInWord_polyTime.comp
      (g := fun p : (((FixedRotationInput × RotationCertificate) × Option (List ℕ)) × List ℕ) ×
          (ℕ × ℕ) => (p.1.2, p.2.2)) (by fun_prop)

/-- The complete concrete candidate driver has native polynomial time on every raw input.
Its sound guard uses the existing numerical checker; completeness remains separate. -/
theorem recover_polyTime : ComputableInPolyTime recover encFixedRotationInput
    (encOption encRotationCertificate) := by
  have hg := encFixedRotationInput_graph_deg.computableInPolyTime
  unfold recover
  apply ComputableInPolyTime.ite' (encC := encBool) query_polyTime
  · apply ComputableInPolyTime.optionElimWithInput recoverOrders_polyTime
      (ComputableInPolyTime.const none)
    have hc := certificate_polyTime.comp
      (ComputableInPolyTime.snd encFixedRotationInput encFixedRotationInput)
    apply ComputableInPolyTime.ite' (encC := encBool)
    · exact (RotationCertificate.computableInPolyTime_verifyGenusZero.comp
        ((hg.comp (ComputableInPolyTime.fst _ _)).prod hc)).bool_and'
        (verifyFixed_polyTime.comp ((ComputableInPolyTime.fst _ _).prod hc))
    · exact (ComputableInPolyTime.optionSome encRotationCertificate).comp hc
    · exact ComputableInPolyTime.const none
  · exact ComputableInPolyTime.const none

private theorem numVars_binary_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun F : Cslib.Logic.PL.CSP Rel V => F.numVars)
      (encCSP encRel encV) encNat := by
  have hu := (Cslib.Logic.PL.CNF.computableInPolyTime_numVars encV).comp
    (CSP.computableInPolyTime_varCNF encRel encV)
  simpa only [Function.comp_def, Cslib.Logic.PL.CSP.numVars_varCNF] using
    ComputableInPolyTime.unary_to_binary.comp hu

/-- Fixing the full orders after a free vertex prefix scans the listed graph only. Its raw
binary cutoff is compared with labels, never converted into a unary scan bound. -/
theorem freePrefix_polyTime : ComputableInPolyTime
    (fun p : Graph × ℕ => freePrefix p.1 p.2)
    (encPair encGraph encNat) encFixedRotationInput := by
  let hg := ComputableInPolyTime.fst encGraph encNat
  have ho : ComputableInPolyTime
      (fun p : Graph × ℕ => (freePrefix p.1 p.2).orders)
      (encPair encGraph encNat) (encList (encOption (encList encNat))) := by
    unfold freePrefix
    apply ComputableInPolyTime.mapWithInput
      (encGraph_vertices_deg.computableInPolyTime.comp hg)
    let hp := ComputableInPolyTime.fst (encPair encGraph encNat) encNat
    let hv := ComputableInPolyTime.snd (encPair encGraph encNat) encNat
    exact ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.binary_lt' hv
        ((ComputableInPolyTime.snd encGraph encNat).comp hp))
      (ComputableInPolyTime.const none)
      ((ComputableInPolyTime.optionSome (encList encNat)).comp
        (fiber_polyTime.comp ((hg.comp hp).prod hv)))
  exact encFixedRotationInput_mk_polyTime
    hg ho

/-- Original CSP scopes compile through the existing dense incidence graph. Binary source
names are compared as bit strings; relation semantics and declared arity fund no scans. -/
theorem ofCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (ofCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) encFixedRotationInput :=
  freePrefix_polyTime.comp
    (g := fun F : Cslib.Logic.PL.CSP Rel V => (CSP.incidenceGraph F, F.numVars))
    ((CSP.computableInPolyTime_incidenceGraph encRel encV).prod
      (numVars_binary_polyTime encRel encV))

/-- Bare original CSP recovery is a native polynomial-time program using the concrete XOR
solver and the existing original-position certificate checker, on every raw encoded CSP. -/
theorem recoverCSP_polyTime {Rel V : Type} [DecidableEq V]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (recoverCSP (Rel := Rel) (V := V))
      (encCSP encRel encV) (encOption encRotationCertificate) := by
  unfold recoverCSP
  apply ComputableInPolyTime.optionElimWithInput
    (recover_polyTime.comp (ofCSP_polyTime encRel encV))
    (ComputableInPolyTime.const none)
  apply ComputableInPolyTime.ite' (encC := encBool)
    (CSP.computableInPolyTime_verifyRotationCertificate encRel encV)
  · exact (ComputableInPolyTime.optionSome encRotationCertificate).comp
      (ComputableInPolyTime.snd _ _)
  · exact ComputableInPolyTime.const none

end Cslib.Complexity.Graph.RotationRecognition
