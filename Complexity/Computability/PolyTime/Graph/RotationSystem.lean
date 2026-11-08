/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD
import Complexity.Tactic.EncLen

/-!
# Native polynomial-time rotation-certificate verification

Binary table lookup uses the existing saturating binary-index implementation. Orbit clocks
are unary and computed from the edge-list length. Every intermediate iterate is a table entry
or zero, whose encoded length is bounded by the encoded table; this remains true on malformed
input. No certificate validity premise appears in the native resource theorem.

## Main results

* `Cslib.Complexity.Graph.RotationCertificate.computableInPolyTime_verifyRotation`: native
  permutation and endpoint-fiber verification.
* `Cslib.Complexity.Graph.RotationCertificate.computableInPolyTime_verifyGenusZero`: native
  verification including each component's numerical Euler equation.
-/

public section

namespace Cslib.Complexity.Graph.RotationCertificate

open Turing.MultiTapeTM

/-- Reading the supplied binary successor table is a projection of its structure encoding. -/
@[fun_prop] theorem computableInPolyTime_successor :
    ComputableInPolyTime RotationCertificate.successor encRotationCertificate (encList encNat) :=
  encRotationCertificate_successor_deg.computableInPolyTime

private theorem incidenceVertices_polyTime :
    ComputableInPolyTime incidenceVertices encGraph (encList encNat) := by
  unfold incidenceVertices encGraph
  fun_prop

attribute [local fun_prop] incidenceVertices_polyTime

private theorem getD_polyTime {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {table : α → List β} {index : α → ℕ} (fallback : β)
    (ht : ComputableInPolyTime table input (encList enc))
    (hi : ComputableInPolyTime index input encNat) :
    ComputableInPolyTime (fun x => (table x).getD (index x) fallback) input enc :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary fallback ht.tidy hi.tidy)

attribute [local fun_prop] getD_polyTime

/-- The table and unary iteration count are paired and framed before the binary start index. -/
abbrev encRotationWalk := encPair (encPair (encList encNat) encUnary) encNat

/-- Iterating a binary-indexed successor table has a native polynomial-time implementation
for a unary number of steps, including invalid and oversized table indices. -/
theorem computableInPolyTime_walk :
    ComputableInPolyTime (fun x : (List ℕ × ℕ) × ℕ => walk x.1.1 x.1.2 x.2)
      encRotationWalk encNat := by
  have hpar : ComputableTidilyInPolyTime
      (fun x : (List ℕ × ℕ) × ℕ => x.1.1) encRotationWalk (encList encNat) := by
    unfold encRotationWalk
    fun_prop
  apply ComputableInPolyTime.of_tidy
  unfold walk
  refine ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (count := fun x => x.1.2) (init := fun x => x.2)
    (step := fun table i => table.getD i 0) (encState := encNat) hpar
    (by unfold encRotationWalk; fun_prop) (by unfold encRotationWalk; fun_prop)
    (ComputableTidilyInPolyTime.listGetD_binary 0
      (ComputableTidilyInPolyTime.fst _ _) (ComputableTidilyInPolyTime.snd _ _))
    hpar.polyBounded_length ?_
  intro x state
  have hb : (encNat (x.1.1.getD state 0)).length ≤ (encList encNat x.1.1).length := by
    by_cases hi : state < x.1.1.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat)
        x.1.1 _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [encNat_apply]
  exact hb.trans (Nat.le_add_left _ _)

/-- Orbit input: unary dart count, binary successor list, then two binary dart indices.
Each left part is framed by its enclosing pair. -/
abbrev encRotationOrbit :=
  encPair (encPair encUnary (encList encNat)) (encPair encNat encNat)

/-- Bounded orbit membership is native polynomial-time on all tables. -/
theorem computableInPolyTime_orbitBool :
    ComputableInPolyTime (fun x : (ℕ × List ℕ) × (ℕ × ℕ) =>
      orbitBool x.1.1 x.1.2 x.2.1 x.2.2)
      encRotationOrbit encBool := by
  unfold orbitBool encRotationOrbit
  apply ComputableInPolyTime.anyWithInput (encA := encUnary) (by fun_prop)
  apply ComputableInPolyTime.decide_eq'
  · exact computableInPolyTime_walk.comp
      (g := fun p : ((ℕ × List ℕ) × (ℕ × ℕ)) × ℕ => ((p.1.1.2, p.2), p.1.2.1))
      (by unfold encRotationWalk; fun_prop)
  · fun_prop

private theorem orbitBool_polyTime {α : Type} {enc : α ↪ List Bool}
    {n i j : α → ℕ} {table : α → List ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (ht : ComputableInPolyTime table enc (encList encNat))
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun x => orbitBool (n x) (table x) (i x) (j x)) enc encBool :=
  computableInPolyTime_orbitBool.comp ((hn.prod ht).prod (hi.prod hj))

attribute [local fun_prop] orbitBool_polyTime

private theorem range_binary :
    ComputableInPolyTime List.range encUnary (encList encNat) := by
  have h := (ComputableTidilyInPolyTime.map
    ComputableTidilyInPolyTime.unary_to_binary).comp ComputableTidilyInPolyTime.range
  have heq : (List.map (fun n : ℕ => n) ∘ List.range) = List.range := by
    funext n
    simp
  rw [heq] at h
  exact .of_tidy h

private theorem fiberCheck_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ =>
      (List.range p.1.1).all fun i => (List.range p.1.1).all fun j =>
        decide (orbitBool p.1.1 p.2 i j = decide (p.1.2.getD i 0 = p.1.2.getD j 0)))
      (encPair (encPair encUnary (encList encNat)) (encList encNat)) encBool := by
  apply ComputableInPolyTime.allWithInput (encA := encNat) (range_binary.comp (by fun_prop))
  apply ComputableInPolyTime.allWithInput (encA := encNat) (range_binary.comp (by fun_prop))
  fun_prop

/-- Every part of rotation validation runs natively in polynomial time in the graph and table
encodings, without an assumed checker, recognizer, or well-formedness hypothesis. -/
@[fun_prop] theorem computableInPolyTime_verifyRotation :
    ComputableInPolyTime (fun x : Graph × RotationCertificate => verifyRotation x.1 x.2)
      encGraphRotationCertificate encBool := by
  unfold verifyRotation
  have hsuccessor := encRotationCertificate_successor_deg.computableInPolyTime
  have hinc : ComputableInPolyTime incidenceVertices encGraph (encList encNat) := by
    unfold incidenceVertices encGraph
    fun_prop
  have hG : ComputableInPolyTime (fun x : Graph × RotationCertificate => x.1)
      encGraphRotationCertificate encGraph := by fun_prop
  have hc : ComputableInPolyTime (fun x : Graph × RotationCertificate => x.2.successor)
      encGraphRotationCertificate (encList encNat) := hsuccessor.comp (by fun_prop)
  have hn : ComputableInPolyTime (fun x : Graph × RotationCertificate => 2 * x.1.2.length)
      encGraphRotationCertificate encUnary := by
    unfold encGraphRotationCertificate encGraph
    fun_prop
  apply ComputableInPolyTime.bool_and'
  · apply ComputableInPolyTime.bool_and'
    · apply ComputableInPolyTime.bool_and'
      · apply ComputableInPolyTime.allWithInput (hinc.comp hG)
        unfold encGraphRotationCertificate encGraph
        fun_prop
      · exact ComputableInPolyTime.decide_eq' (by fun_prop) hn
    · exact computableInPolyTime_enumeratesBool.comp ((range_binary.comp hn).prod hc)
  · exact fiberCheck_polyTime.comp ((hn.prod (hinc.comp hG)).prod hc)

private theorem componentStep_polyTime :
    ComputableInPolyTime (fun p : Graph × List ℕ => componentStep p.1 p.2)
      (encPair encGraph (encList encNat)) (encList encNat) := by
  unfold componentStep encGraph
  fun_prop

/-- Breadth-first expansion is native polynomial-time; the accumulated list grows by at most
one copy of the declared vertex list per iteration, including on malformed graphs. -/
theorem computableInPolyTime_componentVertices :
    ComputableInPolyTime (fun p : Graph × ℕ => componentVertices p.1 p.2)
      (encPair encGraph encNat) (encList encNat) := by
  have hv : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1.1)
      (encPair encGraph encNat) (encList encNat) := by unfold encGraph; fun_prop
  apply ComputableInPolyTime.of_tidy
  unfold componentVertices
  refine ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (par := fun p : Graph × ℕ => p.1) (count := fun p => p.1.1.length)
    (init := fun p => [p.2]) (step := componentStep)
    (by fun_prop) (by unfold encGraph; fun_prop) (by fun_prop)
    componentStep_polyTime.tidy hv.polyBounded_length ?_
  intro p state
  simp only [componentStep, encList_append, List.length_append]
  apply Nat.add_le_add_left
  rw [length_encList, length_encList]
  exact (List.filter_sublist.map (fun n : ℕ => 2 * (encNat n).length + 1)).sum_le_sum (by simp)

private theorem componentBool_polyTime {α : Type} {enc : α ↪ List Bool}
    {G : α → Graph} {root v : α → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hr : ComputableInPolyTime root enc encNat) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => componentBool (G x) (root x) (v x)) enc encBool := by
  unfold componentBool
  apply ComputableInPolyTime.anyWithInput
    (computableInPolyTime_componentVertices.comp (hG.prod hr))
  fun_prop

attribute [local fun_prop] componentBool_polyTime

private theorem reverseIndex_polyTime : ComputableInPolyTime reverseIndex encNat encNat := by
  unfold reverseIndex
  fun_prop

attribute [local fun_prop] reverseIndex_polyTime

private theorem faceTable_polyTime :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => faceTable p.1 p.2)
      encGraphRotationCertificate (encList encNat) := by
  unfold faceTable encGraphRotationCertificate encGraph
  apply ComputableInPolyTime.mapWithInput (encA := encNat) (range_binary.comp (by fun_prop))
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.unary_to_binary.comp
  exact ComputableTidilyInPolyTime.idxOfWithInput
    (computableInPolyTime_successor.tidy.comp (by fun_prop))
    (reverseIndex_polyTime.tidy.comp (ComputableTidilyInPolyTime.snd _ _))

private theorem faceRepBool_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => faceRepBool p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encNat)) encNat) encBool := by
  unfold faceRepBool
  apply ComputableInPolyTime.allWithInput (encA := encNat) (range_binary.comp (by fun_prop))
  refine ComputableInPolyTime.bool_or.comp (g := fun p : ((ℕ × List ℕ) × ℕ) × ℕ =>
    (!orbitBool p.1.1.1 p.1.1.2 p.1.2 p.2, decide (p.1.2 ≤ p.2))) ?_
  apply ComputableInPolyTime.prod
  · have ho : ComputableInPolyTime (fun p : ((ℕ × List ℕ) × ℕ) × ℕ =>
        orbitBool p.1.1.1 p.1.1.2 p.1.2 p.2)
        (encPair (encPair (encPair encUnary (encList encNat)) encNat) encNat) encBool :=
      orbitBool_polyTime (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    exact ComputableInPolyTime.bool_not.comp ho
  · exact ComputableInPolyTime.binary_le.comp
      (((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))

private theorem faceRepBool_polyTime' {α : Type} {enc : α ↪ List Bool}
    {n i : α → ℕ} {table : α → List ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (ht : ComputableInPolyTime table enc (encList encNat))
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun x => faceRepBool (n x) (table x) (i x)) enc encBool :=
  faceRepBool_polyTime.comp ((hn.prod ht).prod hi)

attribute [local fun_prop] faceRepBool_polyTime' faceTable_polyTime

private theorem vertexCount_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ =>
      p.1.distinctVertices.countP (componentBool p.1 p.2))
      (encPair encGraph encNat) encUnary := by
  apply ComputableInPolyTime.countPWithInput (by fun_prop)
  fun_prop

private theorem edgeCount_polyTime :
    ComputableInPolyTime (fun p : Graph × ℕ =>
      p.1.2.countP (fun e => componentBool p.1 p.2 e.1))
      (encPair encGraph encNat) encUnary := by
  apply ComputableInPolyTime.countPWithInput (encA := encPair encNat encNat)
    (by unfold encGraph; fun_prop)
  fun_prop

private theorem faceCount_polyTime :
    ComputableInPolyTime (fun p : (Graph × RotationCertificate) × ℕ =>
      (List.range (2 * p.1.1.2.length)).countP fun i =>
        componentBool p.1.1 p.2 (p.1.1.incidenceVertices.getD i 0) &&
          faceRepBool (2 * p.1.1.2.length) (faceTable p.1.1 p.1.2) i)
      (encPair encGraphRotationCertificate encNat) encUnary := by
  apply ComputableInPolyTime.countPWithInput (encA := encNat)
    (range_binary.comp (by unfold encGraphRotationCertificate encGraph; fun_prop))
  have hG : ComputableInPolyTime
      (fun p : ((Graph × RotationCertificate) × ℕ) × ℕ => p.1.1.1)
      (encPair (encPair encGraphRotationCertificate encNat) encNat) encGraph := by fun_prop
  have hn : ComputableInPolyTime
      (fun p : ((Graph × RotationCertificate) × ℕ) × ℕ => 2 * p.1.1.1.2.length)
      (encPair (encPair encGraphRotationCertificate encNat) encNat) encUnary := by
    exact ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
      ((ComputableInPolyTime.of_tidy
        (ComputableTidilyInPolyTime.length (encPair encNat encNat))).comp
        ((ComputableInPolyTime.snd _ _).comp hG))
  exact (componentBool_polyTime hG (by fun_prop)
    (getD_polyTime 0 (incidenceVertices_polyTime.comp hG) (by fun_prop))).bool_and'
      (faceRepBool_polyTime' hn (faceTable_polyTime.comp
        (g := fun p : ((Graph × RotationCertificate) × ℕ) × ℕ => p.1.1) (by fun_prop))
        (by fun_prop))

/-- Componentwise Euler verification is native polynomial-time in the actual encoded graph
and successor table. No connectivity, permutation, or index-bound premise is required. -/
@[fun_prop] theorem computableInPolyTime_verifyEuler :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => verifyEuler p.1 p.2)
      encGraphRotationCertificate encBool := by
  unfold verifyEuler encGraphRotationCertificate encGraph
  apply ComputableInPolyTime.allWithInput (encA := encNat) (by fun_prop)
  have hp : ComputableInPolyTime (fun p : (Graph × RotationCertificate) × ℕ => (p.1.1, p.2))
      (encPair encGraphRotationCertificate encNat) (encPair encGraph encNat) := by fun_prop
  have hv := vertexCount_polyTime.comp hp
  have he := edgeCount_polyTime.comp hp
  have hf := faceCount_polyTime
  apply ComputableInPolyTime.ite
  · apply ComputableInPolyTime.anyWithInput
      (incidenceVertices_polyTime.comp (g := fun p : (Graph × RotationCertificate) × ℕ => p.1.1)
        (by fun_prop))
    fun_prop
  · exact ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.unary_add' hv hf)
      (ComputableInPolyTime.unary_add' he (ComputableInPolyTime.const 2))
  · exact ComputableInPolyTime.const true

/-- The full finite supplied-certificate verifier has a native polynomial-time certificate. -/
@[fun_prop] theorem computableInPolyTime_verifyGenusZero :
    ComputableInPolyTime (fun p : Graph × RotationCertificate => verifyGenusZero p.1 p.2)
      encGraphRotationCertificate encBool := by
  unfold verifyGenusZero
  exact computableInPolyTime_verifyRotation.bool_and' computableInPolyTime_verifyEuler

end Cslib.Complexity.Graph.RotationCertificate
