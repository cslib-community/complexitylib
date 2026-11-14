/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import CslibFrontier.Computability.Complexity.Problems.SAT.ExactOne.DrawingFinitePolyTime
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import CslibFrontier.Logics.Propositional.CNF.ExactOne.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Geometry.Orthogonal.PointPolyTime
import CslibFrontier.Foundations.Geometry.Orthogonal.Macrocell
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Native polynomial-time positive incidence drawing compilation

Coordinates and original source labels use binary encodings. Clause, literal, and list indices
use unary counters bounded by the emitted lists. The finite profile and collar choices are fixed
independently of the input; there is no enumeration of the coordinate rectangle.

The certificates use the plain polynomial-time calculus throughout: captured list scans handle
source routes and clause blocks, and finite case analysis selects the fixed local templates.

The input, a source formula with its supplied binary-coordinate drawing, is encoded by
`DrawingFinitePolyTime.encInput`.

## Main results

Native certificates for source route normalization, constant-scale trimming, and the actual
positive drawing compiler.

## References

These are original native certificates for the explicit drawing construction.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne.DrawingNative

open Cslib.Logic.PL Orthogonal Turing.MultiTapeTM
open DrawingFinitePolyTime (encInput)

/-- Listed graphs retain binary vertex labels; edge positions use unary counters. -/
abbrev encSourceIndex : ((Graph × Graph.OrthogonalDrawing) × ℕ) ↪ List Bool :=
  encPair (encPair encGraph Graph.encOrthogonalDrawing) encUnary

local instance : ListEncoding encPoint encRoute :=
  inferInstanceAs (ListEncoding encPoint (encList encPoint))

local instance : SizedListEncoding encPoint encRoute :=
  inferInstanceAs (SizedListEncoding encPoint (encList encPoint))

private theorem point_scale (k : ℕ) :
    ComputableInPolyTime (fun p : Point => k • p) encPoint encPoint := by
  change ComputableInPolyTime
    (fun p : Point => ((k : ℤ) * p.1, (k : ℤ) * p.2)) _ _
  unfold encPoint
  fun_prop

attribute [local fun_prop] computableInPolyTime_pointAdd point_scale
  computableInPolyTime_direction computableInPolyTime_translate

/-- Position lookup compares binary graph labels and scans only the declared vertex list. -/
@[fun_prop]
theorem drawingPosition :
    ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        Graph.drawingPosition p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) encPoint := by
  unfold Graph.drawingPosition encGraph Graph.encOrthogonalDrawing encRoute
  fun_prop

private theorem sourceEdge :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      p.1.1.2.getD p.2 (0, 0)) encSourceIndex (encPair encNat encNat) := by
  fun_prop

/-- The clause endpoint of an indexed source edge is computed without expanding labels. -/
@[fun_prop]
theorem sourceStart :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceStart p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (p.1, (p.1.1.2.getD p.2 (0, 0)).2)) encSourceIndex
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) := by fun_prop
  simpa only [Function.comp_def, ExactOne.sourceStart] using
    (drawingPosition.comp hp)

/-- Reading and, when necessary, reversing an actual source route is polynomial-time. -/
@[fun_prop]
theorem sourceRoute :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceRoute p.1.1 p.1.2 p.2) encSourceIndex encRoute := by
  have hs := sourceStart
  have hr : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ => p.1.2.2.getD p.2 [])
      encSourceIndex encRoute := by fun_prop
  have hhead := (ComputableInPolyTime.head? encPoint).comp hr
  have hsome := (ComputableInPolyTime.optionSome encPoint).comp hs
  exact ((hhead.decide_eq' hsome).ite_decide hr
    (ComputableInPolyTime.listReverseWithInput hr))

private theorem routeSecond :
    ComputableInPolyTime (fun r : Route => r.getD 1 (0, 0)) encRoute encPoint := by
  fun_prop

/-- The source exit direction needs only the first two listed route points. -/
@[fun_prop]
theorem sourceDirection :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceDirection p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (ExactOne.sourceStart p.1.1 p.1.2 p.2,
          (ExactOne.sourceRoute p.1.1 p.1.2 p.2).getD 1 (0, 0)))
      encSourceIndex (encPair encPoint encPoint) := by fun_prop
  simpa only [Function.comp_def, ExactOne.sourceDirection] using
    (computableInPolyTime_direction.comp hp)

private theorem route_dilate (k : ℕ) :
    ComputableInPolyTime (dilateRoute k) encRoute encRoute := by
  unfold dilateRoute encRoute
  fun_prop

private theorem point_cut (k radius : ℕ) :
    ComputableInPolyTime (fun p : Point × Point => cutPoint k radius p.1 p.2)
      (encPair encPoint encPoint) encPoint := by
  unfold cutPoint
  fun_prop

attribute [local fun_prop] route_dilate point_cut

private theorem cutStart_eq (k radius : ℕ) (r : Route) :
    cutStart k radius r =
      if r.length < 2 then dilateRoute k r else
        cutPoint k radius (r.getD 0 (0, 0)) (r.getD 1 (0, 0)) ::
          dilateRoute k r.tail := by
  rcases r with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [cutStart, dilateRoute]

/-- Constant-scale endpoint trimming scans the supplied route and computes two point images. -/
@[fun_prop]
theorem cutStart (k radius : ℕ) :
    ComputableInPolyTime (Orthogonal.cutStart k radius) encRoute encRoute := by
  have hget (i : ℕ) :=
    (ComputableInPolyTime.listGetD (encA := encPoint) (encL := encRoute) (0, 0)).comp
      ((ComputableInPolyTime.id' (encIn := encRoute)).prod
        (ComputableInPolyTime.const i))
  have hcut := (point_cut k radius).comp ((hget 0).prod (hget 1))
  have htail := (route_dilate k).comp
    (ComputableInPolyTime.tail (encA := encPoint))
  have hlen := ComputableInPolyTime.length_list encPoint
  have htest := ComputableInPolyTime.unary_lt.comp
    (hlen.prod (ComputableInPolyTime.const 2))
  have h := htest.ite_decide (route_dilate k) (hcut.cons' htail)
  change ComputableInPolyTime (fun r => Orthogonal.cutStart k radius r) _ _
  simpa only [cutStart_eq, Function.comp_def, encRoute] using h

/-- The trimmed exterior of each indexed source edge is polynomial-time. -/
@[fun_prop]
theorem exteriorRoute (k radius : ℕ) :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.exteriorRoute k radius p.1.1 p.1.2 p.2) encSourceIndex encRoute :=
  (cutStart k radius).comp sourceRoute

/-- Clause and literal indices of a source occurrence are unary; original labels stay binary. -/
@[fun_prop]
theorem sourceEdgeIndex :
    ComputableInPolyTime (fun p : CNF ℕ × (ℕ × ℕ) =>
      ExactOne.sourceEdgeIndex p.1 p.2.1 p.2.2)
      (encPair encCNF (encPair encUnary encUnary)) encUnary := by
  apply ComputableInPolyTime.idxOfWithInput
  · exact (Cslib.Logic.PL.computableInPolyTime_occurrences encNat).comp
      (ComputableInPolyTime.fst encCNF (encPair encUnary encUnary))
  · change ComputableInPolyTime
      (fun p : CNF ℕ × (ℕ × ℕ) => sourceOccurrence p.1 p.2.1 p.2.2)
      (encPair encCNF (encPair encUnary encUnary)) (Cslib.Logic.PL.encOccurrence encNat)
    have hφ := ComputableInPolyTime.fst encCNF (encPair encUnary encUnary)
    have hij := ComputableInPolyTime.snd encCNF (encPair encUnary encUnary)
    have hi := (ComputableInPolyTime.fst encUnary encUnary).comp hij
    have hj := (ComputableInPolyTime.snd encUnary encUnary).comp hij
    have hc : ComputableInPolyTime
        (fun p : CNF ℕ × (ℕ × ℕ) => p.1.getD p.2.1 [])
        (encPair encCNF (encPair encUnary encUnary)) DrawingFinitePolyTime.encClause := by fun_prop
    have hl : ComputableInPolyTime
        (fun p : CNF ℕ × (ℕ × ℕ) => (p.1.getD p.2.1 []).getD p.2.2 (0, true))
        (encPair encCNF (encPair encUnary encUnary)) (encPair encNat encBool) := by fun_prop
    exact (hi.prod (hj.prod hl)).of_enc_eq fun _ => rfl

private theorem graphDrawing :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => (SAT.incidenceGraph p.1, p.2))
      encInput (encPair encGraph Graph.encOrthogonalDrawing) := by
  fun_prop

private theorem sourceIndex (j : ℕ) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ((SAT.incidenceGraph p.1.1, p.1.2), ExactOne.sourceEdgeIndex p.1.1 p.2 j))
      (encPair encInput encUnary) encSourceIndex := by
  fun_prop

/-- Each actual source exit has a native finite cardinal-direction tag. -/
@[fun_prop]
theorem literalSide (j : ℕ) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => ExactOne.literalSide p.1.1 p.1.2 p.2 j)
      (encPair encInput encUnary) (encFinite (Fin 4)) := by
  have h := DrawingFinitePolyTime.computableInPolyTime_directionSide.comp
    (sourceDirection.comp (sourceIndex j))
  simpa only [Function.comp_def, ExactOne.literalSide] using h

/-- Complete the present exits to one of the fixed ordered collars in native polynomial time. -/
@[fun_prop]
theorem clausePorts :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => ExactOne.clausePorts p.1.1 p.1.2 p.2)
      (encPair encInput encUnary) (encFinite PortAssignment) :=
  DrawingFinitePolyTime.computableInPolyTime_clausePorts_of_literalSide literalSide

/-- The lower-left box origin uses the source's actual clause position and a constant dilation. -/
@[fun_prop]
theorem positiveBoxOrigin :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2)
      (encPair encInput encUnary) encPoint := by
  have hd := (CNF.computableInPolyTime_distinctVars encNat)
  have hn : ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => p.1.1.distinctVars.length + p.2)
      (encPair encInput encUnary) encUnary := by fun_prop
  have hb := ComputableInPolyTime.unary_to_binary.comp hn
  have hg := graphDrawing.comp (ComputableInPolyTime.fst encInput encUnary)
  have hp := drawingPosition.comp (hg.prod hb)
  have h := (point_scale positiveScale).comp hp
  simpa only [Function.comp_def, ExactOne.positiveBoxOrigin] using h

/-- The actual dilated and trimmed inherited route is emitted without searching the plane. -/
@[fun_prop]
theorem positiveExterior (j : ℕ) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ExactOne.positiveExterior p.1.1 p.1.2 p.2 j)
      (encPair encInput encUnary) encRoute := by
  have he := (exteriorRoute positiveScale positiveRadius).comp (sourceIndex j)
  have h := computableInPolyTime_translate.comp
    ((ComputableInPolyTime.const positiveTranslation).prod he)
  simpa only [Function.comp_def, ExactOne.positiveExterior] using h

private theorem take_zipIdx {A : Type*} (xs : List A) (i start : ℕ) :
    (xs.zipIdx start).take i = (xs.take i).zipIdx start := by
  induction xs generalizing i start with
  | nil => simp
  | cons a xs ih => cases i <;> simp [List.zipIdx_cons, ih]

private theorem signedOffset_eq_length (φ : CNF ℕ) (i : ℕ) :
    CNF.PositiveExactOneCompile.signedOffset φ i = (CNF.FromSAT.formula (φ.take i)).length := by
  simp only [CNF.PositiveExactOneCompile.signedOffset, CNF.PositiveExactOne.blockOffset,
    ← List.map_take, take_zipIdx, List.map_map, Function.comp_def, CNF.FromSAT.formula,
    List.length_flatMap]

/-- Prefix offsets are computed as lengths of the already certified signed clause compiler. -/
@[fun_prop]
theorem signedOffset :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => CNF.PositiveExactOneCompile.signedOffset p.1 p.2)
      (encPair encCNF encUnary) encUnary := by
  have ht : ComputableInPolyTime (fun p : CNF ℕ × ℕ => p.1.take p.2)
      (encPair encCNF encUnary) encCNF :=
    ComputableInPolyTime.listTakeWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.snd _ _)
  have hf := (CNF.FromSAT.computableInPolyTime_formula encNat).comp ht
  have hl := (ComputableInPolyTime.length_list
    (encList (encPair (CNF.FromSAT.encVariable encNat) encBool))).comp hf
  simpa only [Function.comp_def, signedOffset_eq_length] using hl

private abbrev BlockInput := (CNF ℕ × Graph.OrthogonalDrawing) × (ℕ × Clause ℕ)

private abbrev encBlockInput : BlockInput ↪ List Bool :=
  encPair encInput (encPair encUnary DrawingFinitePolyTime.encClause)

private abbrev encRawVariable := DrawingFinitePolyTime.encRawVariable

private abbrev encPlacedClause : PositivePlacedClause ↪ List Bool :=
  encPair (encList (encPair encRawVariable encBool)) (encPair encPoint (encList encRoute))

private theorem blockIndex :
    ComputableInPolyTime (fun p : BlockInput => (p.1, p.2.1))
      encBlockInput (encPair encInput encUnary) := by
  unfold encBlockInput
  fun_prop

private theorem blockOrigin :
    ComputableInPolyTime
      (fun p : BlockInput => ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1)
      encBlockInput encPoint := by
  simpa only [Function.comp_def] using positiveBoxOrigin.comp blockIndex

private theorem blockSignedOffset :
    ComputableInPolyTime
      (fun p : BlockInput => CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1)
      encBlockInput encUnary := by
  have hp : ComputableInPolyTime (fun p : BlockInput => (p.1.1, p.2.1))
      encBlockInput (encPair encCNF encUnary) := by fun_prop
  simpa only [Function.comp_def] using signedOffset.comp hp

private theorem blockVariable (v : CNF.PositiveExactOneCompile.Variable ℕ) :
    ComputableInPolyTime (fun p : BlockInput =>
      profileVariableMap p.2.1 (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2 v)
      encBlockInput encRawVariable := by
  rcases v with (n | ⟨i, k⟩) | ⟨⟨i, j⟩, k⟩
  · have hc : ComputableInPolyTime (fun p : BlockInput => p.2.2)
        encBlockInput DrawingFinitePolyTime.encClause := by
      unfold encBlockInput
      fun_prop
    have hn : ComputableInPolyTime (fun p : BlockInput => (p.2.2.getD n (0, true)).1)
        encBlockInput encNat := by fun_prop
    unfold profileVariableMap encRawVariable DrawingFinitePolyTime.encRawVariable
      CNF.PositiveExactOneCompile.encVariable CNF.PositiveExactOne.encVariable
      CNF.FromSAT.encVariable
    fun_prop
  · unfold profileVariableMap encRawVariable DrawingFinitePolyTime.encRawVariable
      CNF.PositiveExactOneCompile.encVariable CNF.PositiveExactOne.encVariable
      CNF.FromSAT.encVariable encBlockInput
    fun_prop
  · have ho := blockSignedOffset
    unfold profileVariableMap encRawVariable DrawingFinitePolyTime.encRawVariable
      CNF.PositiveExactOneCompile.encVariable CNF.PositiveExactOne.encVariable
      CNF.FromSAT.encVariable
    fun_prop

private def incidenceFor (profile : ClauseProfile) (e : LocalIncidence) (p : BlockInput) : Route :=
  let stem := translate (ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1) e.2.2
  match (profileVariables profile).getD e.2.1 (.inl (.inl 0)) with
  | .inl (.inl j) => stem ++ (ExactOne.positiveExterior p.1.1 p.1.2 p.2.1 j).tail
  | _ => stem

private theorem incidenceFor_poly (profile : ClauseProfile) (e : LocalIncidence) :
    ComputableInPolyTime (incidenceFor profile e) encBlockInput encRoute := by
  have hs := computableInPolyTime_translate.comp
    (blockOrigin.prod (ComputableInPolyTime.const e.2.2))
  have he (j : ℕ) := (positiveExterior j).comp blockIndex
  unfold incidenceFor
  rcases (profileVariables profile).getD e.2.1 (.inl (.inl 0)) with (j | v) | v
  · exact hs.listAppend' ((ComputableInPolyTime.tail (encA := encPoint)).comp (he j))
  · exact hs
  · exact hs

private theorem blockTag :
    ComputableInPolyTime (fun p : BlockInput =>
      (clauseProfile p.2.2, ExactOne.clausePorts p.1.1 p.1.2 p.2.1))
      encBlockInput DrawingFinitePolyTime.encProfilePorts := by
  have hc : ComputableInPolyTime (fun p : BlockInput => p.2.2)
      encBlockInput DrawingFinitePolyTime.encClause := by fun_prop
  have hp : ComputableInPolyTime (fun p : BlockInput => clauseProfile p.2.2)
      encBlockInput (encFinite ClauseProfile) := by fun_prop
  have hs : ComputableInPolyTime
      (fun p : BlockInput => ExactOne.clausePorts p.1.1 p.1.2 p.2.1)
      encBlockInput (encFinite PortAssignment) := by
    simpa only [Function.comp_def] using clausePorts.comp blockIndex
  exact hp.prod hs

private def placedBlockFor (tag : ClauseProfile × PortAssignment) (p : BlockInput) :
    List PositivePlacedClause :=
  let g := collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2
  (profileFormula tag.1).zipIdx.map fun a =>
    (a.1.relabel (profileVariableMap p.2.1
      (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2),
      ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1 + g.clausePosition a.2,
      (g.incidenceRoutes.filter fun e => e.1 == a.2).map fun e => incidenceFor tag.1 e p)

private theorem placedBlockFor_poly (tag : ClauseProfile × PortAssignment) :
    ComputableInPolyTime (placedBlockFor tag) encBlockInput (encList encPlacedClause) := by
  unfold placedBlockFor
  apply ComputableInPolyTime.mapConst
  intro a _
  have hc : ComputableInPolyTime (fun p : BlockInput => a.1.relabel
      (profileVariableMap p.2.1 (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2))
      encBlockInput (encList (encPair encRawVariable encBool)) := by
    unfold Clause.relabel
    apply ComputableInPolyTime.mapConst
    intro l _
    exact (blockVariable l.1).prod (ComputableInPolyTime.const l.2)
  have hp := computableInPolyTime_pointAdd.comp
    (blockOrigin.prod (ComputableInPolyTime.const
      ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).clausePosition a.2)))
  have hr := ComputableInPolyTime.mapConst
    ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).incidenceRoutes.filter
      fun e => e.1 == a.2) (fun e _ => incidenceFor_poly tag.1 e)
  exact hc.prod (hp.prod hr)

private theorem positiveClauseBlock :
    ComputableInPolyTime (fun p : BlockInput =>
      ExactOne.positiveClauseBlock p.1.1 p.1.2 p.2.1 p.2.2)
      encBlockInput (encList encPlacedClause) := by
  convert ComputableInPolyTime.finite_cases blockTag placedBlockFor_poly using 1
  funext p
  rfl

private def auxiliaryBlockFor (tag : ClauseProfile × PortAssignment) (p : BlockInput) :
    List (CNF.PositiveExactOneCompile.Variable ℕ × Point) :=
  (profileVariables tag.1).zipIdx.filterMap fun v =>
    match v.1 with
    | .inl (.inl _) => none
    | _ => some (profileVariableMap p.2.1
        (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2 v.1,
        ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1 +
          (collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).variablePosition v.2)

private theorem auxiliaryBlockFor_poly (tag : ClauseProfile × PortAssignment) :
    ComputableInPolyTime (auxiliaryBlockFor tag) encBlockInput
      (encList (encPair encRawVariable encPoint)) := by
  have hlist (xs : List (CNF.PositiveExactOneCompile.Variable ℕ × ℕ)) :
      ComputableInPolyTime (fun p : BlockInput => xs.filterMap fun v =>
        match v.1 with
        | .inl (.inl _) => none
        | _ => some (profileVariableMap p.2.1
            (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2 v.1,
            ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1 +
              (collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).variablePosition v.2))
        encBlockInput (encList (encPair encRawVariable encPoint)) := by
    induction xs with
    | nil => exact ComputableInPolyTime.const []
    | cons v xs ih =>
      have hp := computableInPolyTime_pointAdd.comp
        (blockOrigin.prod (ComputableInPolyTime.const
          ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).variablePosition v.2)))
      rcases v with ⟨(j | a) | a, n⟩
      · exact ih
      · exact ((blockVariable _).prod hp).cons' ih
      · exact ((blockVariable _).prod hp).cons' ih
  exact hlist _

private theorem positiveAuxiliaryBlock :
    ComputableInPolyTime (fun p : BlockInput =>
      ExactOne.positiveAuxiliaryBlock p.1.1 p.1.2 p.2.1 p.2.2)
      encBlockInput (encList (encPair encRawVariable encPoint)) := by
  convert ComputableInPolyTime.finite_cases blockTag auxiliaryBlockFor_poly using 1
  funext p
  rfl

private theorem sourceClauses :
    ComputableInPolyTime (fun p : CNF ℕ × Graph.OrthogonalDrawing => p.1.zipIdx)
      encInput (encList (encPair DrawingFinitePolyTime.encClause encUnary)) := by
  unfold encInput encCNF DrawingFinitePolyTime.encClause
  fun_prop

private theorem clauseFrame :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × (Clause ℕ × ℕ) =>
        (p.1, (p.2.2, p.2.1)))
      (encPair encInput (encPair DrawingFinitePolyTime.encClause encUnary)) encBlockInput := by
  unfold encBlockInput
  fun_prop

private theorem positivePlacedClauses :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positivePlacedClauses p.1 p.2)
      encInput (encList encPlacedClause) := by
  have hf := positiveClauseBlock.comp clauseFrame
  simpa only [Function.comp_def, ExactOne.positivePlacedClauses] using
    ComputableInPolyTime.flatMapWithInput sourceClauses hf

private theorem positiveAuxiliaryPositions :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveAuxiliaryPositions p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) := by
  have hf : ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × (Clause ℕ × ℕ) =>
        ExactOne.positiveAuxiliaryBlock p.1.1 p.1.2 p.2.2 p.2.1)
      (encPair encInput (encPair DrawingFinitePolyTime.encClause encUnary))
      (encList (encPair encRawVariable encPoint)) := by
    simpa only [Function.comp_def] using positiveAuxiliaryBlock.comp clauseFrame
  unfold ExactOne.positiveAuxiliaryPositions
  exact ComputableInPolyTime.flatMapWithInput
    (f := fun (p : CNF ℕ × Graph.OrthogonalDrawing) (c : Clause ℕ × ℕ) =>
      ExactOne.positiveAuxiliaryBlock p.1 p.2 c.2 c.1)
    (encA := encPair DrawingFinitePolyTime.encClause encUnary)
    (encB := encPair encRawVariable encPoint) (encIn := encInput) sourceClauses hf

private theorem sourceVariables :
    ComputableInPolyTime (fun p : CNF ℕ × Graph.OrthogonalDrawing => p.1.distinctVars)
      encInput (encList encNat) :=
  (CNF.computableInPolyTime_distinctVars encNat).comp
    (ComputableInPolyTime.fst encCNF Graph.encOrthogonalDrawing)

private theorem sourceVariablePosition :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => positiveScale •
        Graph.drawingPosition (SAT.incidenceGraph p.1.1) p.1.2 (p.1.1.distinctVars.idxOf p.2) +
          positiveTranslation) (encPair encInput encNat) encPoint := by
  have hi : ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => p.1.1.distinctVars.idxOf p.2)
      (encPair encInput encNat) encUnary := by fun_prop
  have hb := ComputableInPolyTime.unary_to_binary.comp hi
  have hg := graphDrawing.comp (ComputableInPolyTime.fst encInput encNat)
  have hp := drawingPosition.comp (hg.prod hb)
  have h := computableInPolyTime_pointAdd.comp
    (((point_scale positiveScale).comp hp).prod
      (ComputableInPolyTime.const positiveTranslation))
  simpa only [Function.comp_def] using h

private theorem positiveSourcePositions :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveSourcePositions p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) := by
  have hv : ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        (Sum.inl (Sum.inl p.2) : CNF.PositiveExactOneCompile.Variable ℕ))
      (encPair encInput encNat) encRawVariable := by fun_prop
  simpa only [ExactOne.positiveSourcePositions] using
    ComputableInPolyTime.mapWithInput sourceVariables (hv.prod sourceVariablePosition)

private theorem positivePositionTable :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positivePositionTable p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) :=
  positiveSourcePositions.listAppend' positiveAuxiliaryPositions

private theorem positiveVariablePoint :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × CNF.PositiveExactOneCompile.Variable ℕ =>
        ExactOne.positiveVariablePoint p.1.1 p.1.2 p.2)
      (encPair encInput encRawVariable) encPoint := by
  have ht := positivePositionTable.comp (ComputableInPolyTime.fst encInput encRawVariable)
  have hk := (ComputableInPolyTime.map
    (ComputableInPolyTime.fst encRawVariable encPoint)).comp ht
  have hp := (ComputableInPolyTime.map
    (ComputableInPolyTime.snd encRawVariable encPoint)).comp ht
  have hi := ComputableInPolyTime.idxOfWithInput hk
    (ComputableInPolyTime.snd encInput encRawVariable)
  have eqIdx (xs : List (CNF.PositiveExactOneCompile.Variable ℕ))
      (v : CNF.PositiveExactOneCompile.Variable ℕ) :
      @List.idxOf _ instBEqOfDecidableEq v xs = xs.idxOf v := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.idxOf_cons, beq_iff_eq, ih]
  have hd := (ComputableInPolyTime.dropUnary (encA := encPoint)).comp (hp.prod hi)
  have h := (ComputableInPolyTime.headD (encA := encPoint) (0, 0)).comp hd
  simpa only [Function.comp_def, ExactOne.positiveVariablePoint, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD, eqIdx] using h

private theorem rawVariables :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (CNF.PositiveExactOneCompile.rawFormula p.1).distinctVars)
      encInput (encList encRawVariable) := by
  have hf : ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => CNF.PositiveExactOneCompile.rawFormula p.1)
      encInput (encList (encList (encPair encRawVariable encBool))) := by fun_prop
  simpa only [Function.comp_def] using
    (CNF.computableInPolyTime_distinctVars encRawVariable).comp hf

private theorem outputVariables :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (CNF.PositiveExactOneCompile.rawFormula p.1).distinctVars.map
          (ExactOne.positiveVariablePoint p.1 p.2)) encInput (encList encPoint) :=
  ComputableInPolyTime.mapWithInput
    (encA := encRawVariable) (encB := encPoint) (encIn := encInput)
    (f := fun p v => ExactOne.positiveVariablePoint p.1 p.2 v) rawVariables positiveVariablePoint

private theorem outputClauses :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (ExactOne.positivePlacedClauses p.1 p.2).map fun c => c.2.1)
      encInput (encList encPoint) := by
  have h := (ComputableInPolyTime.map
    ((ComputableInPolyTime.snd (encList (encPair encRawVariable encBool))
      (encPair encPoint (encList encRoute))).fst')).comp positivePlacedClauses
  simpa only [Function.comp_def] using h

private theorem outputRoutes :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (ExactOne.positivePlacedClauses p.1 p.2).flatMap fun c => c.2.2)
      encInput (encList encRoute) := by
  have hm := (ComputableInPolyTime.map
    ((ComputableInPolyTime.snd (encList (encPair encRawVariable encBool))
      (encPair encPoint (encList encRoute))).snd')).comp positivePlacedClauses
  have h := ComputableInPolyTime.flatMapWithInput
    (f := fun _ (routes : List Route) => routes) hm (ComputableInPolyTime.snd _ _)
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using h

/-- The actual emitted drawing is natively polynomial-time on binary coordinates and labels.
The proof scans the explicit lists and dispatches among fixed local templates. -/
@[fun_prop]
theorem computableInPolyTime_positiveDrawing :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveDrawing p.1 p.2)
      encInput Graph.encOrthogonalDrawing := by
  have h := (outputVariables.listAppend' outputClauses).prod outputRoutes
  simpa only [Function.comp_def, ExactOne.positiveDrawing, Graph.encOrthogonalDrawing,
    encRoute] using h

end Cslib.Complexity.SAT.ExactOne.DrawingNative
