/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Forest.Code
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Contraction
import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Transport
import CslibFrontier.Algorithms.Lean.EdgeCSP.Solver.Rows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Finite-buffer whole-instance contraction

Native list operations implement the existing whole-instance constructor. All old constraints,
including nullaries, keep their positions. Selected internal coordinates are gathered once per
original constraint, surviving coordinates keep their order, and one central exactly-one table
is appended. Local rows and positions are funded by actual scopes, not declared binary arities.

Original names and fresh connectors remain binary. The maximum scan traverses only occurring
names; no interval below a name is enumerated. The source construction is Section 5.3 of
[KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed pp. 12–13.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Contraction

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM
open Cslib.BitString

/-- Actual local rows, in original constraint and argument order, read from the existing buffer. -/
@[expose] def rows (input : EdgeForest.Input) : List (List Bool) :=
  input.body.zipIdx.map fun (c, i) => c.scope.zipIdx.map fun (v, j) =>
    EdgeAugmenting.readRecord input.body input.labels (i, j, v)

/-- A fresh binary base, obtained by one scan of actual original names. -/
@[expose] def freshBase (F : CSP Table ℕ) : ℕ := F.vars.foldl max 0 + 1

/-- Actual fresh connectors, one per touched original constraint and in original order. -/
@[expose] def connectors (F : CSP Table ℕ) (vs : List ℕ) : List ℕ :=
  (F.zipIdx.filter fun (c, _) => !(Blossom.positions vs c.scope).isEmpty).map fun (_, i) =>
    freshBase F + i

/-- Replace all selected positions of one original constraint in a single local contraction. -/
@[expose] def constraint (input : EdgeForest.Input) (vs : List ℕ)
    (c : Constraint Table ℕ) (i : ℕ) : Constraint Table ℕ :=
  let ps := Blossom.positions vs c.scope
  if ps.isEmpty then c else
    let os := Table.outsidePositions c.scope.length ps
    ⟨c.rel.contract ((rows input).getD i []) ps,
      os.map (fun j => c.scope.getD j 0) ++ [freshBase input.body + i]⟩

/-- Total finite whole-instance contraction on arbitrary raw table and buffer inputs. -/
@[expose] def contract (input : EdgeForest.Input) (vs : List ℕ) : CSP Table ℕ :=
  input.body.zipIdx.map (fun (c, i) => constraint input vs c i) ++
    [Constraint.mk (Table.exactlyOne (connectors input.body vs)) (connectors input.body vs)]

/-- The honest contracted reference: zero old connector bits, followed by one central one-hot
row. The central row is paid for by the actual connector list. -/
@[expose] def referenceRows (input : EdgeForest.Input) (vs : List ℕ) : List (List Bool) :=
  input.body.zipIdx.map (fun (c, i) =>
    let row := (rows input).getD i []
    let ps := Blossom.positions vs c.scope
    if ps.isEmpty then row else
      Table.project row (Table.outsidePositions c.scope.length ps) ++ [false]) ++
    [listSingle (connectors input.body vs).length 0]

/-- The fresh-name scan agrees with the original constructor's maximum scan. -/
theorem freshBase_eq (F : CSP Table ℕ) : freshBase F = Blossom.freshBase F := by
  unfold freshBase Blossom.freshBase
  congr 1
  rw [List.foldr_eq_foldl]

/-- Every raw-buffer row is exactly the original positional local tuple; no width premise
is needed, since both readers default identically on missing occurrence bits. -/
theorem rows_eq (input : EdgeForest.Input) : rows input =
    List.ofFn (fun i : Fin input.body.length =>
      localTuple (EdgeAugmenting.labeling input.body input.labels) i) := by
  apply List.ext_getElem
  · simp [rows]
  · intro i hi hj
    have hi' : i < input.body.length := by simpa using hj
    simp only [rows, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.getElem_ofFn]
    apply List.ext_getElem
    · simp [localTuple]
    · intro j hj hk
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add, localTuple,
        List.getElem_ofFn]
      exact EdgeAugmenting.read_record input.labels ⟨⟨i, hi'⟩, ⟨j, by simpa [localTuple] using hk⟩⟩

/-- Fresh connectors are precisely those of the original whole-instance constructor. -/
theorem connectors_eq (F : CSP Table ℕ) (vs : List ℕ) :
    connectors F vs = Blossom.connectors F vs := by
  unfold connectors Blossom.connectors Blossom.touched
  conv_lhs => rw [← List.ofFn_getElem (xs := F.zipIdx)]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, List.ofFn_eq_map,
    List.filter_map, List.map_map, Function.comp_def, freshBase_eq]
  rfl

/-- Exact native whole-instance contraction on every raw buffer, without semantic premises. -/
theorem contract_eq (input : EdgeForest.Input) (vs : List ℕ) :
    contract input vs = Blossom.contract (EdgeAugmenting.labeling input.body input.labels) vs := by
  unfold contract Blossom.contract
  rw [connectors_eq]
  congr 1
  conv_lhs => rw [← List.ofFn_getElem (xs := input.body.zipIdx)]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def, Fin.val_cast, constraint, Blossom.constraint, rows_eq,
    List.getD_ofFn, freshBase_eq, Blossom.connector]

/-- Exact actual reference rows, including the central one-hot row. -/
theorem referenceRows_eq (input : EdgeForest.Input) (vs : List ℕ) :
    referenceRows input vs =
      Blossom.referenceRows (EdgeAugmenting.labeling input.body input.labels) vs := by
  unfold referenceRows Blossom.referenceRows Blossom.transportRows
  rw [connectors_eq]
  congr 1
  conv_lhs => rw [← List.ofFn_getElem (xs := input.body.zipIdx)]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def, Fin.val_cast, rows_eq, List.getD_ofFn]

/-- Flattening the actual constructor's reference rows gives precisely its occurrence buffer.
Every row has the actual scope width, including the appended central row and all nullaries. -/
theorem flatten_referenceRows {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (vs : List ℕ) :
    (Blossom.referenceRows f vs).flatten =
      (incidenceList (Blossom.contract f vs)).map (Blossom.reference f vs) := by
  let G := Blossom.contract f vs
  let rs := Blossom.referenceRows f vs
  have hlen : rs.length = G.length := by
    simp [rs, G, Blossom.referenceRows, Blossom.transportRows]
  have hw (i : Fin G.length) : (rs.getD i.val []).length = G[i.val].scope.length :=
    Blossom.transportRows_length f f vs (fun _ => false) (by simp [listSingle]) i
  exact (Solver.materialize_labels G rs hlen hw).symm

attribute [local fun_prop] EdgeAugmenting.poly_zipIdx EdgeAugmenting.poly_readWith

private theorem poly_rows : ComputableInPolyTime rows EdgeForest.encInput
    (encList (encList encBool)) := by
  unfold rows
  have hbody := EdgeForest.encInput_body_deg.computableInPolyTime
  have hlabels := EdgeForest.encInput_labels_deg.computableInPolyTime
  fun_prop

private theorem poly_max : ComputableInPolyTime
    (fun p : ℕ × ℕ => max p.1 p.2) (encPair encNat encNat) encNat := by
  simp only [max_def]
  fun_prop

private theorem poly_maxList : ComputableInPolyTime (fun xs : List ℕ => xs.foldl max 0)
    (encList encNat) encNat := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth
    (encA := encNat) (encL := encList encNat) (encB := encNat)
    (growth := fun xs => (encList encNat xs).length)
    (ComputableInPolyTime.const 0).tidy
  · refine ⟨(ComputableInPolyTime.id' (encIn := encList encNat)).tidy, ?_,
      inferInstance, inferInstance⟩
    exact (poly_max.comp ((ComputableInPolyTime.fst _ _).snd'.prod
      (ComputableInPolyTime.snd _ _))).tidy
  · refine ⟨PolyBounded.self, ?_⟩
    intro xs state value hv
    have hb := length_le_encList_of_mem encNat hv
    rcases le_total state value with h | h
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left h]
      omega

attribute [local fun_prop] poly_maxList poly_rows

private theorem poly_rowsWith {α : Type} {e : α ↪ List Bool} {input : α → EdgeForest.Input}
    (hi : ComputableInPolyTime input e EdgeForest.encInput) :
    ComputableInPolyTime (fun a => rows (input a)) e (encList (encList encBool)) :=
  poly_rows.comp hi

private theorem poly_rowReadWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {index : α → ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hj : ComputableInPolyTime index e encUnary) :
    ComputableInPolyTime (fun a => (rows (input a)).getD (index a) []) e (encList encBool) :=
  ComputableInPolyTime.listGetDWithInput (poly_rowsWith hi) hj []

attribute [local fun_prop] poly_rowsWith poly_rowReadWith

private theorem poly_freshBase : ComputableInPolyTime freshBase
    (encCSP encTable encNat) encNat := by
  unfold freshBase
  fun_prop

private theorem poly_positions : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => Blossom.positions p.1 p.2)
    (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  have hrange : ComputableInPolyTime List.range encUnary (encList encNat) := by
    have h := ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary
    simpa only [Function.comp_def, List.map_id'] using h.comp
      (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.range)
  unfold Blossom.positions
  simp only [List.contains_eq_mem]
  apply ComputableInPolyTime.filterWithInput (hrange.comp (by fun_prop))
  have hl := ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) 0
    (show ComputableInPolyTime
      (fun p : (List ℕ × List ℕ) × ℕ => p.1.2)
      (encPair (encPair (encList encNat) (encList encNat)) encNat) (encList encNat)
      from by fun_prop).tidy
    (ComputableInPolyTime.snd _ _).tidy
  have hlookup := ComputableInPolyTime.of_tidy hl
  fun_prop

/-- Native composition on actual lists with binary names and positions. -/
theorem computableInPolyTime_positionsWith {α : Type} {e : α ↪ List Bool}
    {vs scope : α → List ℕ}
    (hv : ComputableInPolyTime vs e (encList encNat))
    (hs : ComputableInPolyTime scope e (encList encNat)) :
    ComputableInPolyTime (fun x => Blossom.positions (vs x) (scope x)) e
      (encList encNat) := poly_positions.comp (hv.prod hs)

private theorem poly_freshWith {α : Type} {e : α ↪ List Bool} {F : α → CSP Table ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat)) :
    ComputableInPolyTime (fun x => freshBase (F x)) e encNat := poly_freshBase.comp hF

attribute [local fun_prop] computableInPolyTime_positionsWith poly_freshWith
  EdgeAugmenting.poly_zipIdx

/-- Native composition on actual lists with binary names and positions. -/
theorem computableInPolyTime_nameReadWith {α : Type} {e : α ↪ List Bool}
    {scope : α → List ℕ} {index : α → ℕ}
    (hs : ComputableInPolyTime scope e (encList encNat))
    (hi : ComputableInPolyTime index e encNat) :
    ComputableInPolyTime (fun a => (scope a).getD (index a) 0) e encNat :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0 hs.tidy hi.tidy)

/-- Native composition on actual lists with binary names and positions. -/
theorem computableInPolyTime_outsideWith {α : Type} {e : α ↪ List Bool}
    {width : α → ℕ} {positions : α → List ℕ}
    (hw : ComputableInPolyTime width e encUnary)
    (hp : ComputableInPolyTime positions e (encList encNat)) :
    ComputableInPolyTime (fun a => Table.outsidePositions (width a) (positions a)) e
      (encList encNat) := computableInPolyTime_tableOutsidePositions.comp (hw.prod hp)

private theorem poly_tableContractWith {α : Type} {e : α ↪ List Bool}
    {table : α → Table} {row : α → List Bool} {positions : α → List ℕ}
    (ht : ComputableInPolyTime table e encTable)
    (hr : ComputableInPolyTime row e (encList encBool))
    (hp : ComputableInPolyTime positions e (encList encNat)) :
    ComputableInPolyTime (fun a => (table a).contract (row a) (positions a)) e encTable := by
  simpa only [Function.comp_def] using
    computableInPolyTime_tableContract.comp (ht.prod (hr.prod hp))

private theorem poly_projectWith {α : Type} {e : α ↪ List Bool}
    {row : α → List Bool} {positions : α → List ℕ}
    (hr : ComputableInPolyTime row e (encList encBool))
    (hp : ComputableInPolyTime positions e (encList encNat)) :
    ComputableInPolyTime (fun a => Table.project (row a) (positions a)) e
      (encList encBool) := computableInPolyTime_tableProject.comp (hr.prod hp)

attribute [local fun_prop] computableInPolyTime_nameReadWith computableInPolyTime_outsideWith
  poly_tableContractWith
  poly_projectWith

/-- Framed original body followed by the framed list of selected original binary names. -/
abbrev encConnectorArgs := encPair (encCSP encTable encNat) (encList encNat)

/-- Fresh binary connector names are computed by bounded scans of actual scopes. -/
theorem computableInPolyTime_connectors : ComputableInPolyTime
    (fun p : CSP Table ℕ × List ℕ => connectors p.1 p.2) encConnectorArgs (encList encNat) := by
  unfold connectors
  have hi : ComputableInPolyTime
      (fun p : (CSP Table ℕ × List ℕ) × (Constraint Table ℕ × ℕ) => p.2.2)
      (encPair encConnectorArgs (encPair (encConstraint encTable encNat) encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hs : ComputableInPolyTime
      (fun p : (CSP Table ℕ × List ℕ) × (Constraint Table ℕ × ℕ) => freshBase p.1.1 + p.2.2)
      (encPair encConnectorArgs (encPair (encConstraint encTable encNat) encUnary)) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_add'
      (show ComputableInPolyTime
        (fun p : (CSP Table ℕ × List ℕ) × (Constraint Table ℕ × ℕ) => freshBase p.1.1)
        (encPair encConnectorArgs (encPair (encConstraint encTable encNat) encUnary))
        encNat from by fun_prop).tidy hi.tidy)
  apply ComputableInPolyTime.mapWithInput
    (show ComputableInPolyTime (fun p : CSP Table ℕ × List ℕ =>
      p.1.zipIdx.filter fun (c, _) => !(Blossom.positions p.2 c.scope).isEmpty)
      encConnectorArgs (encList (encPair (encConstraint encTable encNat) encUnary))
      from by fun_prop)
  exact hs

/-- Compose connector construction with computed finite inputs, charging their full encodings. -/
theorem computableInPolyTime_connectorsWith {α : Type} {e : α ↪ List Bool}
    {F : α → CSP Table ℕ} {vs : α → List ℕ}
    (hF : ComputableInPolyTime F e (encCSP encTable encNat))
    (hv : ComputableInPolyTime vs e (encList encNat)) :
    ComputableInPolyTime (fun a => connectors (F a) (vs a)) e (encList encNat) :=
  computableInPolyTime_connectors.comp (hF.prod hv)

attribute [local fun_prop] computableInPolyTime_connectorsWith

/-- Original input and selected names are framed, then the current constraint and its unary
position are framed. The stored relation's declared arity and scope names remain binary. -/
private abbrev encConstraintArgs := encPair
  (encPair EdgeForest.encInput (encList encNat))
  (encPair (encConstraint encTable encNat) encUnary)

private theorem poly_constraint : ComputableInPolyTime
    (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
      constraint p.1.1 p.1.2 p.2.1 p.2.2) encConstraintArgs
      (encConstraint encTable encNat) := by
  unfold constraint
  have hi : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) => p.2.2)
      encConstraintArgs encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hp : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        Blossom.positions p.1.2 p.2.1.scope) encConstraintArgs (encList encNat) := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (rows p.1.1).getD p.2.2 []) encConstraintArgs (encList encBool) :=
    poly_rowReadWith (by fun_prop) (by fun_prop)
  have ht : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        p.2.1.rel.contract ((rows p.1.1).getD p.2.2 [])
          (Blossom.positions p.1.2 p.2.1.scope)) encConstraintArgs encTable :=
    poly_tableContractWith (by fun_prop) hr hp
  have hn : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        freshBase p.1.1.body + p.2.2) encConstraintArgs encNat :=
    ComputableInPolyTime.binary_add.comp
      ((show ComputableInPolyTime
        (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
          freshBase p.1.1.body) encConstraintArgs encNat from by fun_prop).prod hi)
  have hos : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        Table.outsidePositions p.2.1.scope.length (Blossom.positions p.1.2 p.2.1.scope))
      encConstraintArgs (encList encNat) := computableInPolyTime_outsideWith (by fun_prop) hp
  have hmap : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (Table.outsidePositions p.2.1.scope.length (Blossom.positions p.1.2 p.2.1.scope)).map
          (fun j => p.2.1.scope.getD j 0)) encConstraintArgs (encList encNat) := by
    apply ComputableInPolyTime.mapWithInput hos
    exact computableInPolyTime_nameReadWith (by fun_prop) (by fun_prop)
  have ho : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (Table.outsidePositions p.2.1.scope.length (Blossom.positions p.1.2 p.2.1.scope)).map
          (fun j => p.2.1.scope.getD j 0) ++ [freshBase p.1.1.body + p.2.2])
      encConstraintArgs (encList encNat) := by fun_prop
  have hnew := ht.prod ho
  have hg : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (Blossom.positions p.1.2 p.2.1.scope).isEmpty) encConstraintArgs encBool := by fun_prop
  have hc : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) => p.2.1)
      encConstraintArgs (encConstraint encTable encNat) := by fun_prop
  exact hg.ite' hc hnew

/-- Whole-instance contraction is ordinary native polynomial-time on all raw inputs.
The certificate scans actual rows and scopes and includes binary fresh-name arithmetic. -/
theorem computableInPolyTime_contract : ComputableInPolyTime
    (fun p : EdgeForest.Input × List ℕ => contract p.1 p.2)
    (encPair EdgeForest.encInput (encList encNat)) (encCSP encTable encNat) := by
  unfold contract
  have hc := poly_constraint
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hex : ComputableInPolyTime Table.exactlyOne (encList encNat) encTable :=
    computableInPolyTime_tableExactlyOne
  fun_prop

private theorem poly_referenceRow : ComputableInPolyTime
    (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
      let row := (rows p.1.1).getD p.2.2 []
      let ps := Blossom.positions p.1.2 p.2.1.scope
      if ps.isEmpty then row else
        Table.project row (Table.outsidePositions p.2.1.scope.length ps) ++ [false])
    encConstraintArgs (encList encBool) := by
  have hp : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        Blossom.positions p.1.2 p.2.1.scope) encConstraintArgs (encList encNat) := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (rows p.1.1).getD p.2.2 []) encConstraintArgs (encList encBool) :=
    poly_rowReadWith (by fun_prop) (by fun_prop)
  have hnew : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        Table.project ((rows p.1.1).getD p.2.2 [])
          (Table.outsidePositions p.2.1.scope.length
            (Blossom.positions p.1.2 p.2.1.scope)) ++ [false])
      encConstraintArgs (encList encBool) := by fun_prop
  have hg : ComputableInPolyTime
      (fun p : (EdgeForest.Input × List ℕ) × (Constraint Table ℕ × ℕ) =>
        (Blossom.positions p.1.2 p.2.1.scope).isEmpty) encConstraintArgs encBool := by fun_prop
  exact hg.ite' hr hnew

/-- The honest reference rows are native polynomial-time, including all row/list framing. -/
theorem computableInPolyTime_referenceRows : ComputableInPolyTime
    (fun p : EdgeForest.Input × List ℕ => referenceRows p.1 p.2)
    (encPair EdgeForest.encInput (encList encNat)) (encList (encList encBool)) := by
  unfold referenceRows
  have hr := poly_referenceRow
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hhot : ComputableInPolyTime
      (fun p : EdgeForest.Input × List ℕ => listSingle (connectors p.1.body p.2).length 0)
      (encPair EdgeForest.encInput (encList encNat)) (encList encBool) := by
    simpa only [Function.comp_def] using computableInPolyTime_tableOneHot.comp
      (show ComputableInPolyTime
        (fun p : EdgeForest.Input × List ℕ => ((connectors p.1.body p.2).length, 0))
        (encPair EdgeForest.encInput (encList encNat)) (encPair encUnary encUnary)
        from by fun_prop)
  have hm : ComputableInPolyTime
      (fun p : EdgeForest.Input × List ℕ => p.1.body.zipIdx.map fun (c, i) =>
        let row := (rows p.1).getD i []
        let ps := Blossom.positions p.2 c.scope
        if ps.isEmpty then row else
          Table.project row (Table.outsidePositions c.scope.length ps) ++ [false])
      (encPair EdgeForest.encInput (encList encNat)) (encList (encList encBool)) := by
    apply ComputableInPolyTime.mapWithInput
      (show ComputableInPolyTime (fun p : EdgeForest.Input × List ℕ => p.1.body.zipIdx)
        (encPair EdgeForest.encInput (encList encNat))
        (encList (encPair (encConstraint encTable encNat) encUnary)) from by fun_prop)
    exact hr
  exact ComputableInPolyTime.listAppend' hm
    (ComputableInPolyTime.cons' hhot (ComputableInPolyTime.const []))

/-- Compose the native finite operation with computed inputs, charging their full encodings. -/
theorem computableInPolyTime_contractWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {vs : α → List ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hv : ComputableInPolyTime vs e (encList encNat)) :
    ComputableInPolyTime (fun a => contract (input a) (vs a)) e
      (encCSP encTable encNat) := by
  simpa only [Function.comp_def] using computableInPolyTime_contract.comp (hi.prod hv)

/-- Compose honest reference-row construction with computed finite inputs. -/
theorem computableInPolyTime_referenceRowsWith {α : Type} {e : α ↪ List Bool}
    {input : α → EdgeForest.Input} {vs : α → List ℕ}
    (hi : ComputableInPolyTime input e EdgeForest.encInput)
    (hv : ComputableInPolyTime vs e (encList encNat)) :
    ComputableInPolyTime (fun a => referenceRows (input a) (vs a)) e
      (encList (encList encBool)) := by
  simpa only [Function.comp_def] using computableInPolyTime_referenceRows.comp (hi.prod hv)

end Cslib.Complexity.CSP.EdgeSolver.Contraction
