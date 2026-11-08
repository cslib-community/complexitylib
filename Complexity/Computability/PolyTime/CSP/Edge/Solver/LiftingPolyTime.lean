/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.Edge.Solver.Lifting
import Complexity.Computability.PolyTime.CSP.Edge.Forest.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Native certificates for finite lifting operations

All working scope/constraint coordinates and prefix lengths are unary and list-funded.
Original names and global walk positions remain binary. Malformed binary positions are looked
up with bounded native scans; none is expanded into an unbounded unary traversal.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeLifting

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open EdgeAugmenting (Record encRecord WalkCode encWalkCode)

attribute [local fun_prop] NativeWalk.computableInPolyTime_portWith
  NativeWalk.computableInPolyTime_start NativeWalk.computableInPolyTime_steps
  NativeWalk.computableInPolyTime_mk NativeWalk.computableInPolyTime_takeWith
  Contraction.computableInPolyTime_positionsWith Contraction.computableInPolyTime_outsideWith
  Contraction.computableInPolyTime_nameReadWith EdgeAugmenting.poly_zipIdx
  EdgeForest.poly_binaryIndex NativeWalk.computableInPolyTime_findIdxWith

private theorem poly_scope : ComputableInPolyTime
    (fun p : CSP Table ℕ × Record => scope p.1 p.2)
    (encPair (encCSP encTable encNat) encRecord) (encList encNat) := by
  unfold scope
  have hget : ComputableInPolyTime
      (fun p : CSP Table ℕ × Record => p.1.getD p.2.1 (⟨0, []⟩, []))
      (encPair (encCSP encTable encNat) encRecord) (encConstraint encTable encNat) :=
    ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) _
  exact hget.snd'

private theorem poly_scopeWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {o : α → Record}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (ho : ComputableInPolyTime o e encRecord) :
    ComputableInPolyTime (fun a => scope (F a) (o a)) e (encList encNat) := by
  simpa only [Function.comp_def] using poly_scope.comp (hF.prod ho)

attribute [local fun_prop] poly_scopeWith

/-- Framed original body and selected binary names, followed by the original work record
with unary constraint/scope coordinates and its binary variable name. -/
private abbrev encOldArgs := encPair
  (encPair (encCSP encTable encNat) (encList encNat)) encRecord

private theorem poly_oldRecord : ComputableInPolyTime
    (fun p : (CSP Table ℕ × List ℕ) × Record => oldRecord p.1.1 p.1.2 p.2)
    encOldArgs encRecord := by
  unfold oldRecord
  have hi : ComputableInPolyTime (fun p : (CSP Table ℕ × List ℕ) × Record => p.2.2.1)
      encOldArgs encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hpos : ComputableInPolyTime
      (fun p : (CSP Table ℕ × List ℕ) × Record =>
        Table.outsidePositions (scope p.1.1 p.2).length
          (Blossom.positions p.1.2 (scope p.1.1 p.2))) encOldArgs (encList encNat) := by fun_prop
  have hindex := EdgeAugmenting.poly_idxOf hpos hi
  fun_prop

private theorem poly_oldRecordWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {vs : α → List ℕ} {o : α → Record}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hv : ComputableInPolyTime vs e (encList encNat))
    (ho : ComputableInPolyTime o e encRecord) :
    ComputableInPolyTime (fun a => oldRecord (F a) (vs a) (o a)) e encRecord := by
  simpa only [Function.comp_def] using poly_oldRecord.comp ((hF.prod hv).prod ho)

attribute [local fun_prop] poly_oldRecordWith Contraction.computableInPolyTime_contractWith
  EdgeAugmenting.poly_records

/-- Input and internal names are framed, then binary fallback and target positions are paired.
Only actual work records use unary local coordinates. -/
private abbrev encRestoreArgs := encPair (encPair EdgeForest.encInput (encList encNat))
  (encPair encNat encNat)

private theorem poly_restore : ComputableInPolyTime
    (fun p : (EdgeForest.Input × List ℕ) × (ℕ × ℕ) => restore p.1.1 p.1.2 p.2.1 p.2.2)
    encRestoreArgs encNat := by
  unfold restore
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hindex : ComputableInPolyTime
      (fun p : ((EdgeForest.Input × List ℕ) × (ℕ × ℕ)) × Record =>
        (CSP.occurrences p.1.1.1.body).idxOf p.2)
      (encPair encRestoreArgs encRecord) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (EdgeAugmenting.poly_idxOf (by fun_prop) (by fun_prop))
  simp only [List.contains_eq_mem]
  fun_prop

private theorem poly_restoreWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {vs : α → List ℕ} {fallback index : α → ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hv : ComputableInPolyTime vs e (encList encNat))
    (hf : ComputableInPolyTime fallback e encNat)
    (hj : ComputableInPolyTime index e encNat) :
    ComputableInPolyTime (fun a => restore (input a) (vs a) (fallback a) (index a)) e encNat := by
  simpa only [Function.comp_def] using poly_restore.comp ((hi.prod hv).prod (hf.prod hj))

attribute [local fun_prop] poly_restoreWith

/-- Original input, selected names and binary fallback are framed, followed by the complete
binary-position walk to restore. -/
abbrev encRestoreWalkArgs := encPair EdgeForest.encInput
  (encPair (encList encNat) (encPair encNat encWalkCode))

/-- Finite surviving-port restoration is ordinary native polynomial-time on every raw input. -/
theorem computableInPolyTime_restoreWalk : ComputableInPolyTime
    (fun p : EdgeForest.Input × List ℕ × ℕ × WalkCode => restoreWalk p.1 p.2.1 p.2.2.1 p.2.2.2)
    encRestoreWalkArgs encWalkCode := by
  unfold restoreWalk
  fun_prop

attribute [local fun_prop] NativeWalk.computableInPolyTime_flipWith
  NativeWalk.computableInPolyTime_edgesWith EdgeAugmenting.poly_validWith
  NativeWalk.computableInPolyTime_finishWith NativeWalk.computableInPolyTime_inputArmWith
  NativeWalk.computableInPolyTime_outputArmWith

/-- Original input, cycle and outside walk are framed in order. The final prefix count is
unary; all positions inside the two walk codes remain binary. -/
private abbrev encExitArgs := encPair EdgeForest.encInput
  (encPair encWalkCode (encPair encWalkCode encUnary))

private theorem poly_exitsAt : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × WalkCode × ℕ => exitsAt p.1 p.2.1 p.2.2.1 p.2.2.2)
    encExitArgs (encList (encPair encNat encNat)) := by
  unfold exitsAt
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hl := EdgeForest.encInput_labels_deg.computableInPolyTime
  have hindex : ComputableInPolyTime
      (fun p : (EdgeForest.Input × WalkCode × WalkCode × ℕ) × Record =>
        (CSP.occurrences p.1.1.body).idxOf p.2) (encPair encExitArgs encRecord) encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      (EdgeAugmenting.poly_idxOf (by fun_prop) (by fun_prop))
  simp only [List.contains_eq_mem]
  fun_prop

private theorem poly_exitsWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {w r : α → WalkCode} {n : α → ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hw : ComputableInPolyTime w e encWalkCode)
    (hr : ComputableInPolyTime r e encWalkCode)
    (hn : ComputableInPolyTime n e encUnary) :
    ComputableInPolyTime (fun a => exitsAt (input a) (w a) (r a) (n a)) e
      (encList (encPair encNat encNat)) := by
  simpa only [Function.comp_def] using poly_exitsAt.comp (hi.prod (hw.prod (hr.prod hn)))

attribute [local fun_prop] poly_exitsWith

/-- Framed original input and cycle, followed by the complete binary-position outside walk. -/
abbrev encPrefixArgs := encPair EdgeForest.encInput (encPair encWalkCode encWalkCode)

private theorem poly_firstExit : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × WalkCode => firstExit p.1 p.2.1 p.2.2)
    encPrefixArgs (encOption encExitCode) := by
  let n (p : EdgeForest.Input × WalkCode × WalkCode) :=
    (List.range (p.2.2.steps.length + 1)).findIdx
      (fun n => !(exitsAt p.1 p.2.1 p.2.2 n).isEmpty)
  have hn : ComputableInPolyTime n encPrefixArgs encUnary :=
    NativeWalk.computableInPolyTime_findIdxWith (by fun_prop) (by fun_prop)
  have hc : ComputableInPolyTime
      (fun p : EdgeForest.Input × WalkCode × WalkCode => p.2.2.steps.length + 1)
      encPrefixArgs encUnary := by fun_prop
  have hg : ComputableInPolyTime
      (fun p => decide (n p < p.2.2.steps.length + 1)) encPrefixArgs encBool := by fun_prop
  have hx := poly_exitsWith
    (show ComputableInPolyTime (fun p : EdgeForest.Input × WalkCode × WalkCode => p.1)
      encPrefixArgs EdgeForest.encInput from by fun_prop)
    (show ComputableInPolyTime (fun p : EdgeForest.Input × WalkCode × WalkCode => p.2.1)
      encPrefixArgs encWalkCode from by fun_prop)
    (show ComputableInPolyTime (fun p : EdgeForest.Input × WalkCode × WalkCode => p.2.2)
      encPrefixArgs encWalkCode from by fun_prop) hn
  have hhead : ComputableInPolyTime
      (fun p : EdgeForest.Input × WalkCode × WalkCode => (exitsAt p.1 p.2.1 p.2.2 (n p)).head?)
      encPrefixArgs (encOption (encPair encNat encNat)) := by fun_prop
  have hm := encExitCode_mk_deg.computableInPolyTime
  have hbody : ComputableInPolyTime
      (fun p : (EdgeForest.Input × WalkCode × WalkCode) × (ℕ × ℕ) =>
        ExitCode.mk (n p.1) p.2.1 p.2.2)
      (encPair encPrefixArgs (encPair encNat encNat)) encExitCode := by fun_prop
  have hyes := ComputableInPolyTime.optionMapWithInput
    (f := fun p pair => ExitCode.mk (n p) pair.1 pair.2) hhead hbody
  simpa only [firstExit, n, decide_eq_true_eq] using
    hg.ite' hyes (ComputableInPolyTime.const none)

private theorem poly_firstExitWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {w r : α → WalkCode}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hw : ComputableInPolyTime w e encWalkCode)
    (hr : ComputableInPolyTime r e encWalkCode) :
    ComputableInPolyTime (fun a => firstExit (input a) (w a) (r a)) e
      (encOption encExitCode) := by
  simpa only [Function.comp_def] using poly_firstExit.comp (hi.prod (hw.prod hr))

attribute [local fun_prop] poly_firstExitWith

/-- The original explicit body is framed, followed by the framed binary walk and the binary
outside position. The cycle-step enumeration itself is unary and list-funded. -/
private abbrev encArmArgs := encPair (encCSP encTable encNat) (encPair encWalkCode encNat)

private theorem poly_armCandidates : ComputableInPolyTime
    (fun p : CSP Table ℕ × WalkCode × ℕ => armCandidates p.1 p.2.1 p.2.2)
    encArmArgs (encList encWalkCode) := by
  unfold armCandidates
  fun_prop

private theorem poly_armCandidatesWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {w : α → WalkCode} {outside : α → ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hw : ComputableInPolyTime w e encWalkCode)
    (ho : ComputableInPolyTime outside e encNat) :
    ComputableInPolyTime (fun a => armCandidates (F a) (w a) (outside a)) e
      (encList encWalkCode) := by
  simpa only [Function.comp_def] using poly_armCandidates.comp (hF.prod (hw.prod ho))

attribute [local fun_prop] poly_armCandidatesWith

/-- Original input and cycle are framed, followed by the binary original outside port. -/
private abbrev encAttachmentArgs := encPair EdgeForest.encInput (encPair encWalkCode encNat)

private theorem poly_attachment : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × ℕ => attachment p.1 p.2.1 p.2.2)
    encAttachmentArgs (encOption encWalkCode) := by
  unfold attachment
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hl := EdgeForest.encInput_labels_deg.computableInPolyTime
  fun_prop

private theorem poly_attachmentWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {w : α → WalkCode} {outside : α → ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hw : ComputableInPolyTime w e encWalkCode)
    (ho : ComputableInPolyTime outside e encNat) :
    ComputableInPolyTime (fun a => attachment (input a) (w a) (outside a)) e
      (encOption encWalkCode) := by
  simpa only [Function.comp_def] using poly_attachment.comp (hi.prod (hw.prod ho))

attribute [local fun_prop] poly_attachmentWith

/-- The shortest outside prefix and actual-arm scan are ordinary native polynomial-time.
The certificate covers all raw buffers and codes, without semantic or width assumptions. -/
theorem computableInPolyTime_liftPrefix : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × WalkCode => liftPrefix p.1 p.2.1 p.2.2)
    encPrefixArgs (encOption (encList encBool)) := by
  unfold liftPrefix
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hl := EdgeForest.encInput_labels_deg.computableInPolyTime
  have hc := EdgeForest.encInput_mk_deg.computableInPolyTime
  have hn := encExitCode_length_deg.computableInPolyTime
  have hi := encExitCode_input_deg.computableInPolyTime
  fun_prop

private theorem poly_restoreWalkWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {vs : α → List ℕ} {fallback : α → ℕ}
    {p : α → WalkCode}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hv : ComputableInPolyTime vs e (encList encNat))
    (hf : ComputableInPolyTime fallback e encNat)
    (hp : ComputableInPolyTime p e encWalkCode) :
    ComputableInPolyTime (fun a => restoreWalk (input a) (vs a) (fallback a) (p a)) e
      encWalkCode := by
  simpa only [Function.comp_def] using
    computableInPolyTime_restoreWalk.comp (hi.prod (hv.prod (hf.prod hp)))

private theorem poly_liftPrefixWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {w r : α → WalkCode}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hw : ComputableInPolyTime w e encWalkCode)
    (hr : ComputableInPolyTime r e encWalkCode) :
    ComputableInPolyTime (fun a => liftPrefix (input a) (w a) (r a)) e
      (encOption (encList encBool)) := by
  simpa only [Function.comp_def] using computableInPolyTime_liftPrefix.comp (hi.prod (hw.prod hr))

attribute [local fun_prop] poly_restoreWalkWith NativeWalk.computableInPolyTime_internalWith
  Contraction.computableInPolyTime_connectorsWith
  poly_liftPrefixWith

/-- The two connector cases of whole-instance walk lifting are native polynomial-time
on every raw code and buffer. Original binary names and positions retain their bit lengths. -/
theorem computableInPolyTime_liftWalk : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × WalkCode => liftWalk p.1 p.2.1 p.2.2)
    encPrefixArgs (encOption (encList encBool)) := by
  unfold liftWalk
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hl := EdgeForest.encInput_labels_deg.computableInPolyTime
  apply ComputableInPolyTime.optionElimWithInput
    (show ComputableInPolyTime
      (fun p : EdgeForest.Input × WalkCode × WalkCode => p.2.1.steps.head?)
      encPrefixArgs (encOption (encPair encNat encNat)) from by fun_prop)
    (ComputableInPolyTime.const none)
  simp only [List.contains_eq_mem]
  fun_prop

/-- Original input is framed, then the cycle is framed, then the improving comparison's
actual Boolean buffer is framed. All original names and walk positions remain binary. -/
abbrev encComparisonArgs := encPair EdgeForest.encInput
  (encPair encWalkCode (encList encBool))

/-- Native augmentation and arbitrary outside-comparison lifting supply the full machine
certificate on all raw data, including malformed widths and huge binary names. -/
theorem computableInPolyTime_liftComparison : ComputableInPolyTime
    (fun p : EdgeForest.Input × WalkCode × List Bool => liftComparison p.1 p.2.1 p.2.2)
    encComparisonArgs (encOption (encList encBool)) := by
  unfold liftComparison
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hm := EdgeAugmenting.encInput_mk_deg.computableInPolyTime
  have hr : ComputableInPolyTime
      (fun p : EdgeForest.Input × List ℕ => Contraction.referenceRows p.1 p.2)
      (encPair EdgeForest.encInput (encList encNat)) (encList (encList encBool)) :=
    Contraction.computableInPolyTime_referenceRows
  have hw := computableInPolyTime_liftWalk
  fun_prop

end Cslib.Complexity.CSP.EdgeSolver.NativeLifting
