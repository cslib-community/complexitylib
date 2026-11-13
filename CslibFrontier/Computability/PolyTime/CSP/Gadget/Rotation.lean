/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Table
public import CslibFrontier.Computability.PolyTime.CSP.Gadget.Size
import CslibFrontier.Computability.PolyTime.CSP.Gadget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Computability.Complexity.FineGrained.CountingCSP
import Mathlib.Data.List.GetD

/-!
# Positional rotation tables for fixed-gadget replacement

The target body is exactly `replaceGadgets`, with its existing even/odd fresh namespaces.
Local rotation blocks use local **occurrence positions**. At each original variable, its
source successor cycle orders the blocks of its distinct source incidences, even when the
same variable occurs repeatedly in one constraint. Target argument rotations are built
from the target's actual ordered scope lists, so no relation is reflected.

Every loop is funded by a source, template, or target list. Binary source names and invalid
binary successor entries are lookup data, not loop bounds. Fixed template preprocessing is
nonuniform in the language. This module defines the executed positional table construction;
its vertex-fiber and componentwise numerical Euler properties are separate proof obligations.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM Graph.RotationCertificate

variable {Src Rel : Type}

/-- Native bounded successor walking on binary tables and binary starts. The result keeps
binary entries as data and uses only the table length as its iteration clock. -/
theorem computableInPolyTime_cycleWord :
    ComputableInPolyTime (fun p : Graph.RotationCertificate × ℕ => cycleWord p.1 p.2)
      (encPair Graph.encRotationCertificate encNat) (encList encNat) := by
  have hs := Graph.RotationCertificate.computableInPolyTime_successor
  have hw := Graph.RotationCertificate.computableInPolyTime_walk
  have hf : ComputableInPolyTime (fun p : Graph.RotationCertificate × ℕ =>
      (List.range p.1.successor.length).map fun k =>
        Graph.RotationCertificate.walk p.1.successor (k + 1) p.2)
      (encPair Graph.encRotationCertificate encNat) (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput (encA := encUnary) (by fun_prop)
    exact hw.comp (g := fun p : (Graph.RotationCertificate × ℕ) × ℕ =>
      ((p.1.1.successor, p.2 + 1), p.1.2)) (by
        unfold Graph.RotationCertificate.encRotationWalk
        fun_prop)
  unfold cycleWord
  fun_prop

/-- Fixed template prefix counts use unary list positions and native framed input sizes. -/
theorem computableInPolyTime_occurrencePrefix [Finite Src]
    (encSrc : Src ↪ List Bool) (templates : Src → CSP Rel (Bool × ℕ)) :
    ComputableInPolyTime (fun p : CSP Src ℕ × ℕ => occurrencePrefix templates p.1 p.2)
      (encPair (encCSP encSrc encNat) encUnary) encUnary := by
  have ht : ComputableInPolyTime (fun r => (templates r).vars) encSrc
      (encList (encPair encBool encUnary)) := .of_finite _
  unfold occurrencePrefix
  have hflat : ComputableInPolyTime (fun p : CSP Src ℕ × ℕ =>
      (p.1.take p.2).flatMap fun c => (templates c.1).vars)
      (encPair (encCSP encSrc encNat) encUnary) (encList (encPair encBool encUnary)) := by
    apply ComputableInPolyTime.flatMapWithInput (encA := encConstraint encSrc encNat)
    · unfold encCSP
      fun_prop
    · exact ht.comp (g := fun p : (CSP Src ℕ × ℕ) × Constraint Src ℕ => p.2.1)
        (by unfold encConstraint; fun_prop)
  fun_prop

/-- Shift unary occurrence positions by a unary prefix; this is independent of labels. -/
theorem computableInPolyTime_shiftBlock :
    ComputableInPolyTime (fun p : ℕ × List ℕ => shiftBlock p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  unfold shiftBlock
  fun_prop

/-- The next-slot computation scans actual unary occurrence words. -/
theorem computableInPolyTime_nextInCycles :
    ComputableInPolyTime (fun p : List (List ℕ) × ℕ => List.nextInCycles p.1 p.2)
      (encPair (encList (encList encUnary)) encUnary) encUnary := by
  apply ComputableInPolyTime.of_tidy
  have hf : ComputableTidilyInPolyTime (fun p : List (List ℕ) × ℕ =>
      p.1.find? (fun word => decide (p.2 ∈ word)))
      (encPair (encList (encList encUnary)) encUnary) (encOption (encList encUnary)) := by
    apply ComputableTidilyInPolyTime.findWithInput (encA := encList encUnary) (by fun_prop)
    fun_prop
  have hw : ComputableTidilyInPolyTime (fun p : List (List ℕ) × ℕ =>
      (p.1.find? (fun word => decide (p.2 ∈ word))).getD [])
      (encPair (encList (encList encUnary)) encUnary) (encList encUnary) :=
    ComputableTidilyInPolyTime.optionGetDWithInput hf (by fun_prop)
  unfold List.nextInCycles
  apply ComputableTidilyInPolyTime.optionGetDWithInput
  · apply ComputableTidilyInPolyTime.getElem? hw
    fun_prop
  · fun_prop

/-- A source body, framed, followed by its unary constraint and argument positions. -/
abbrev encBlockRecordInput (encSrc : Src ↪ List Bool) :=
  encPair (encCSP encSrc encNat) (encPair encUnary encUnary)

private theorem shiftedLocalBlock_polyTime [Finite Src] (encSrc : Src ↪ List Bool)
    (freeBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : Src × (ℕ × ℕ) =>
      shiftBlock p.2.1 ((freeBlocks p.1).getD p.2.2 []))
      (encPair encSrc (encPair encUnary encUnary)) (encList encUnary) := by
  have hb : ComputableInPolyTime freeBlocks encSrc (encList (encList encUnary)) :=
    .of_finite _
  refine computableInPolyTime_shiftBlock.comp
    (g := fun p : Src × (ℕ × ℕ) => (p.2.1, (freeBlocks p.1).getD p.2.2 [])) ?_
  apply ComputableInPolyTime.prod
  · fun_prop
  · exact ComputableInPolyTime.listGetDWithInput
      (hb.comp (g := fun p : Src × (ℕ × ℕ) => p.1) (by fun_prop)) (by fun_prop) []

/-- Native expansion of a recorded positional incidence. The constraint scan is funded by
its original list, independently of the two indices. -/
theorem computableInPolyTime_blockAtRecord [Finite Src]
    (encSrc : Src ↪ List Bool) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : CSP Src ℕ × (ℕ × ℕ) =>
      blockAtRecord templates freeBlocks p.1 p.2)
      (encBlockRecordInput encSrc) (encList encUnary) := by
  have hp := computableInPolyTime_occurrencePrefix encSrc templates
  have hb := shiftedLocalBlock_polyTime encSrc freeBlocks
  have hz : ComputableInPolyTime (fun p : CSP Src ℕ × (ℕ × ℕ) => p.1.zipIdx)
      (encBlockRecordInput encSrc)
      (encList (encPair (encConstraint encSrc encNat) encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx _).comp
      (by unfold encBlockRecordInput encCSP; fun_prop))
  unfold blockAtRecord
  apply ComputableInPolyTime.flatMapWithInput hz
  apply ComputableInPolyTime.ite_decide
  · unfold encBlockRecordInput
    fun_prop
  · refine hb.comp (g := fun p : (CSP Src ℕ × (ℕ × ℕ)) × (Constraint Src ℕ × ℕ) =>
      (p.2.1.1, (occurrencePrefix templates p.1.1 p.2.2, p.1.2.2))) ?_
    have hp' : ComputableInPolyTime
        (fun p : (CSP Src ℕ × (ℕ × ℕ)) × (Constraint Src ℕ × ℕ) =>
          occurrencePrefix templates p.1.1 p.2.2)
        (encPair (encBlockRecordInput encSrc)
          (encPair (encConstraint encSrc encNat) encUnary)) encUnary :=
      hp.comp (g := fun p : (CSP Src ℕ × (ℕ × ℕ)) × (Constraint Src ℕ × ℕ) =>
        (p.1.1, p.2.2)) (by unfold encBlockRecordInput; fun_prop)
    unfold encBlockRecordInput encConstraint
    fun_prop
  · exact ComputableInPolyTime.const []

/-- Read a local block through a binary source-dart lookup, with unary returned positions.
The runtime theorem covers huge malformed certificate indices without a validity premise. -/
theorem computableInPolyTime_incidenceBlock [Finite Src]
    (encSrc : Src ↪ List Bool) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : CSP Src ℕ × ℕ =>
      incidenceBlock templates freeBlocks p.1 p.2)
      (encPair (encCSP encSrc encNat) encNat) (encList encUnary) := by
  have ho := computableInPolyTime_occurrences encSrc encNat
  have hr : ComputableInPolyTime (fun p : CSP Src ℕ × ℕ =>
      p.1.occurrences.getD (p.2 / 2) (0, 0, 0))
      (encPair (encCSP encSrc encNat) encNat) (encOccurrenceRecord encNat) :=
    .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (0, 0, 0)
      (ho.tidy.comp (by fun_prop)) (by fun_prop))
  exact (computableInPolyTime_blockAtRecord encSrc templates freeBlocks).comp
    (g := fun p : CSP Src ℕ × ℕ =>
      (p.1, ((p.1.occurrences.getD (p.2 / 2) (0, 0, 0)).1,
        (p.1.occurrences.getD (p.2 / 2) (0, 0, 0)).2.1))) (by
      unfold encBlockRecordInput encOccurrenceRecord at *
      fun_prop)

/-- A CSP/certificate pair, framed, followed by a binary original variable name. -/
abbrev encVariableBlockInput (encSrc : Src ↪ List Bool) :=
  encPair (encCSPRotationCertificate encSrc encNat) encNat

private theorem firstVariableDart_polyTime (encSrc : Src ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Src ℕ × ℕ =>
      2 * (p.1.occurrences.map fun o => o.2.2).idxOf p.2)
      (encPair (encCSP encSrc encNat) encNat) encNat := by
  have ho := computableInPolyTime_occurrences encSrc encNat
  have hv : ComputableInPolyTime (fun p : CSP Src ℕ × ℕ =>
      p.1.occurrences.map fun o => o.2.2)
      (encPair (encCSP encSrc encNat) encNat) (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput
      (ho.comp (ComputableInPolyTime.fst _ _))
    unfold encOccurrenceRecord
    fun_prop
  apply ComputableInPolyTime.of_tidy
  exact ComputableTidilyInPolyTime.unary_to_binary.comp
    (ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod
        (ComputableTidilyInPolyTime.idxOfWithInput hv.tidy
          (ComputableTidilyInPolyTime.snd _ _))))

private theorem sourceCycle_polyTime (encSrc : Src ↪ List Bool) :
    ComputableInPolyTime (fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ =>
      cycleWord p.1.2 (2 * (p.1.1.occurrences.map fun o => o.2.2).idxOf p.2))
      (encVariableBlockInput encSrc) (encList encNat) := by
  have hstart : ComputableInPolyTime
      (fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ =>
        2 * (p.1.1.occurrences.map fun o => o.2.2).idxOf p.2)
      (encVariableBlockInput encSrc) encNat :=
    (firstVariableDart_polyTime encSrc).comp
      (g := fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ => (p.1.1, p.2))
      (by unfold encVariableBlockInput encCSPRotationCertificate; fun_prop)
  have hcert : ComputableInPolyTime
      (fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ => p.1.2)
      (encVariableBlockInput encSrc) Graph.encRotationCertificate := by
    unfold encVariableBlockInput encCSPRotationCertificate
    fun_prop
  exact computableInPolyTime_cycleWord.comp
    (g := fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ =>
      (p.1.2, 2 * (p.1.1.occurrences.map fun o => o.2.2).idxOf p.2)) (hcert.prod hstart)

/-- Source rotations splice local blocks natively; all original names stay binary. -/
theorem computableInPolyTime_variableBlock [Finite Src]
    (encSrc : Src ↪ List Bool) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : (CSP Src ℕ × Graph.RotationCertificate) × ℕ =>
      variableBlock templates freeBlocks p.1.1 p.1.2 p.2)
      (encVariableBlockInput encSrc) (encList encUnary) := by
  have hb := computableInPolyTime_incidenceBlock encSrc templates freeBlocks
  unfold variableBlock
  apply ComputableInPolyTime.flatMapWithInput (sourceCycle_polyTime encSrc)
  exact hb.comp (g := fun p : ((CSP Src ℕ × Graph.RotationCertificate) × ℕ) × ℕ =>
    (p.1.1.1, p.2)) (by unfold encVariableBlockInput encCSPRotationCertificate; fun_prop)

private theorem shiftBlocks_polyTime :
    ComputableInPolyTime (fun p : ℕ × List (List ℕ) => p.2.map (shiftBlock p.1))
      (encPair encUnary (encList (encList encUnary))) (encList (encList encUnary)) := by
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  exact computableInPolyTime_shiftBlock.comp
    (g := fun p : (ℕ × List (List ℕ)) × List ℕ => (p.1.1, p.2)) (by fun_prop)

private theorem auxiliaryCycles_polyTime [Finite Src] (encSrc : Src ↪ List Bool)
    (templates : Src → CSP Rel (Bool × ℕ)) (auxiliaryBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun F : CSP Src ℕ => F.zipIdx.flatMap fun entry =>
      (auxiliaryBlocks entry.1.1).map (shiftBlock (occurrencePrefix templates F entry.2)))
      (encCSP encSrc encNat) (encList (encList encUnary)) := by
  have ha : ComputableInPolyTime auxiliaryBlocks encSrc (encList (encList encUnary)) :=
    .of_finite _
  have hp := computableInPolyTime_occurrencePrefix encSrc templates
  have hz : ComputableInPolyTime (fun F : CSP Src ℕ => F.zipIdx)
      (encCSP encSrc encNat) (encList (encPair (encConstraint encSrc encNat) encUnary)) :=
    .of_tidy (ComputableTidilyInPolyTime.zipIdx _)
  apply ComputableInPolyTime.flatMapWithInput hz
  refine shiftBlocks_polyTime.comp
    (g := fun p : CSP Src ℕ × (Constraint Src ℕ × ℕ) =>
      (occurrencePrefix templates p.1 p.2.2, auxiliaryBlocks p.2.1.1)) ?_
  apply ComputableInPolyTime.prod
  · exact hp.comp (g := fun p : CSP Src ℕ × (Constraint Src ℕ × ℕ) => (p.1, p.2.2))
      (by fun_prop)
  · exact ha.comp (g := fun p : CSP Src ℕ × (Constraint Src ℕ × ℕ) => p.2.1.1)
      (by unfold encConstraint; fun_prop)

/-- The full list of target variable cycles is native polynomial-time on every raw input.
The fixed local words may be precomputed nonuniformly; no planarity search is executed. -/
theorem computableInPolyTime_replacementCycles [Finite Src]
    (encSrc : Src ↪ List Bool) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : CSP Src ℕ × Graph.RotationCertificate =>
      replacementCycles templates freeBlocks auxiliaryBlocks p.1 p.2)
      (encCSPRotationCertificate encSrc encNat) (encList (encList encUnary)) := by
  have hv := computableInPolyTime_distinctVars encSrc encNat
  have hb := computableInPolyTime_variableBlock encSrc templates freeBlocks
  have ha := auxiliaryCycles_polyTime encSrc templates auxiliaryBlocks
  unfold replacementCycles
  apply ComputableInPolyTime.listAppend'
  · apply ComputableInPolyTime.mapWithInput (hv.comp (ComputableInPolyTime.fst _ _))
    exact hb
  · exact ha.comp (ComputableInPolyTime.fst _ _)

/-- Target occurrence words and their candidate variable cycles, with both parts framed.
Source variable labels remain binary; candidate local occurrence positions are unary. -/
abbrev encTargetCycles (encRel : Rel ↪ List Bool) :=
  encPair (encCSP encRel encNat) (encList (encList encUnary))

private theorem successorPairs_polyTime (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × List (List ℕ) => successorPairs p.1 p.2)
      (encTargetCycles encRel) (encList (encPair encUnary encUnary)) := by
  have ho := computableInPolyTime_occurrences encRel encNat
  have hn := argumentNextIndex_polyTime encRel encNat
  have hx := computableInPolyTime_nextInCycles
  have hz : ComputableInPolyTime
      (fun p : CSP Rel ℕ × List (List ℕ) => p.1.occurrences.zipIdx)
      (encTargetCycles encRel)
      (encList (encPair (encOccurrenceRecord encNat) encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx _).comp
      (ho.tidy.comp (by unfold encTargetCycles; fun_prop)))
  unfold successorPairs
  apply ComputableInPolyTime.mapWithInput hz
  apply ComputableInPolyTime.prod
  · have hnext : ComputableInPolyTime
        (fun p : (CSP Rel ℕ × List (List ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) =>
          List.nextInCycles p.1.2 p.2.2)
        (encPair (encTargetCycles encRel)
          (encPair (encOccurrenceRecord encNat) encUnary)) encUnary :=
      hx.comp (g := fun p : (CSP Rel ℕ × List (List ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) =>
        (p.1.2, p.2.2)) (by unfold encTargetCycles; fun_prop)
    fun_prop
  · have hnext : ComputableInPolyTime
        (fun p : (CSP Rel ℕ × List (List ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) =>
          argumentNextIndex p.1.1 p.2.1.1 p.2.1.2.1)
        (encPair (encTargetCycles encRel)
          (encPair (encOccurrenceRecord encNat) encUnary)) encUnary :=
      hn.comp (g := fun p : (CSP Rel ℕ × List (List ℕ)) × ((ℕ × ℕ × ℕ) × ℕ) =>
        ((p.1.1, p.2.1.1), p.2.1.2.1)) (by
          unfold encTargetCycles encOccurrenceRecord
          fun_prop)
    fun_prop

/-- Emitting the complete framed successor certificate is native polynomial-time, including
malformed words and empty targets. The counter encodings are converted explicitly to binary. -/
theorem computableInPolyTime_certificate (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel ℕ × List (List ℕ) => certificate p.1 p.2)
      (encTargetCycles encRel) Graph.encRotationCertificate := by
  have hp := successorPairs_polyTime encRel
  have hflat : ComputableInPolyTime (fun p : CSP Rel ℕ × List (List ℕ) =>
      (successorPairs p.1 p.2).flatMap fun q => [q.1, q.2])
      (encTargetCycles encRel) (encList encUnary) := by
    apply ComputableInPolyTime.flatMapWithInput hp
    fun_prop
  have hbinary : ComputableInPolyTime (fun p : CSP Rel ℕ × List (List ℕ) =>
      (successorPairs p.1 p.2).flatMap fun q => [q.1, q.2])
      (encTargetCycles encRel) (encList encNat) := by
    have h := ComputableInPolyTime.of_tidy
      ((ComputableTidilyInPolyTime.map ComputableTidilyInPolyTime.unary_to_binary).comp
        hflat.tidy)
    simpa only [Function.comp_def, List.map_id'] using h
  have hmk := Graph.encRotationCertificate_mk_deg.computableInPolyTime
  exact hmk.comp hbinary

/-- Full native computation of the explicit candidate target certificate from the original
CSP and original binary source certificate. There is no valid-input premise on this bound. -/
theorem computableInPolyTime_replacementCertificate [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) :
    ComputableInPolyTime (fun p : CSP Src ℕ × Graph.RotationCertificate =>
      replacementCertificate B templates freeBlocks auxiliaryBlocks p.1 p.2)
      (encCSPRotationCertificate encSrc encNat) Graph.encRotationCertificate := by
  have hbody := computableInPolyTime_replaceGadgets encSrc encRel B templates
  have hcycles := computableInPolyTime_replacementCycles encSrc templates freeBlocks auxiliaryBlocks
  have hbody' : ComputableInPolyTime
      (fun p : CSP Src ℕ × Graph.RotationCertificate => replaceGadgets B templates p.1)
      (encCSPRotationCertificate encSrc encNat) (encCSP encRel encNat) :=
    hbody.comp (ComputableInPolyTime.fst (encCSP encSrc encNat) Graph.encRotationCertificate)
  exact (computableInPolyTime_certificate encRel).comp
    (g := fun p : CSP Src ℕ × Graph.RotationCertificate =>
      (replaceGadgets B templates p.1,
        replacementCycles templates freeBlocks auxiliaryBlocks p.1 p.2))
    (hbody'.prod hcycles)

end Cslib.Complexity.CSP.GadgetRotation
