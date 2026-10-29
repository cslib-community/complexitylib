/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingFinitePolyTime
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import Complexity.Logics.Propositional.CNF.ExactOne.PolyTime
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Foundations.Geometry.Orthogonal.Macrocell
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Native polynomial-time positive incidence drawing compilation

Coordinates and original source labels use binary encodings. Clause, literal, and list indices
use unary counters bounded by the emitted lists. The finite profile and collar choices are fixed
independently of the input; there is no enumeration of the coordinate rectangle.

## Main definitions

* `DrawingNative.encInput`: the source formula and its supplied binary-coordinate drawing.

## Main results

Native certificates for source route normalization, constant-scale trimming, and the actual
positive drawing compiler.

## References

These are original native certificates for the explicit drawing construction.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne.DrawingNative

open Cslib.Logic.PL Orthogonal Turing.MultiTapeTM

/-- The encoded source formula and its supplied drawing. -/
abbrev encInput : (CNF ℕ × Graph.OrthogonalDrawing) ↪ List Bool :=
  encPair encCNF Graph.encOrthogonalDrawing

/-- Listed graphs retain binary vertex labels; edge positions use unary counters. -/
abbrev encSourceIndex : ((Graph × Graph.OrthogonalDrawing) × ℕ) ↪ List Bool :=
  encPair (encPair encGraph Graph.encOrthogonalDrawing) encUnary

attribute [local fun_prop] ComputableInPolyTime.tidy

local instance : ListEncoding encPoint encRoute :=
  inferInstanceAs (ListEncoding encPoint (encList encPoint))

local instance : SizedListEncoding encPoint encRoute :=
  inferInstanceAs (SizedListEncoding encPoint (encList encPoint))

private theorem point_add :
    ComputableInPolyTime (fun p : Point × Point => p.1 + p.2)
      (encPair encPoint encPoint) encPoint := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime
    (fun p : Point × Point => (p.1.1 + p.2.1, p.1.2 + p.2.2)) _ _
  unfold encPoint
  fun_prop

private theorem point_scale (k : ℕ) :
    ComputableInPolyTime (fun p : Point => k • p) encPoint encPoint := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime
    (fun p : Point => ((k : ℤ) * p.1, (k : ℤ) * p.2)) _ _
  unfold encPoint
  fun_prop

private theorem point_direction :
    ComputableInPolyTime (fun p : Point × Point => direction p.1 p.2)
      (encPair encPoint encPoint) encPoint := by
  refine .of_tidy ?_
  unfold direction encPoint
  fun_prop

private theorem route_translate :
    ComputableInPolyTime (fun p : Point × Route => translate p.1 p.2)
      (encPair encPoint encRoute) encRoute := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime
    (fun p : Point × Route => p.2.map fun q => (q.1 + p.1.1, q.2 + p.1.2)) _ _
  unfold encPoint encRoute
  fun_prop

attribute [local fun_prop] point_add point_scale point_direction route_translate

/-- Position lookup compares binary graph labels and scans only the declared vertex list. -/
@[fun_prop]
theorem drawingPosition :
    ComputableInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        Graph.drawingPosition p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) encPoint := by
  refine .of_tidy ?_
  unfold Graph.drawingPosition encGraph Graph.encOrthogonalDrawing encRoute
  fun_prop

private theorem sourceEdge :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      p.1.1.2.getD p.2 (0, 0)) encSourceIndex (encPair encNat encNat) := by
  refine .of_tidy ?_
  unfold encSourceIndex encGraph
  fun_prop

/-- The clause endpoint of an indexed source edge is computed without expanding labels. -/
@[fun_prop]
theorem sourceStart :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceStart p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableTidilyInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (p.1, (p.1.1.2.getD p.2 (0, 0)).2)) encSourceIndex
      (encPair (encPair encGraph Graph.encOrthogonalDrawing) encNat) :=
    (ComputableTidilyInPolyTime.fst (encPair encGraph Graph.encOrthogonalDrawing) encUnary).prod
      sourceEdge.tidy.snd'
  simpa only [Function.comp_def, ExactOne.sourceStart] using
    ComputableInPolyTime.of_tidy (drawingPosition.tidy.comp hp)

/-- Reading and, when necessary, reversing an actual source route is polynomial-time. -/
@[fun_prop]
theorem sourceRoute :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceRoute p.1.1 p.1.2 p.2) encSourceIndex encRoute := by
  have hs := sourceStart.tidy
  have hr : ComputableTidilyInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ => p.1.2.2.getD p.2 [])
      encSourceIndex encRoute := by
    unfold encSourceIndex Graph.encOrthogonalDrawing encRoute
    fun_prop
  have hhead := (ComputableTidilyInPolyTime.head? encPoint).comp hr
  have hsome := (ComputableTidilyInPolyTime.optionSome encPoint).comp hs
  exact .of_tidy ((hhead.decide_eq' hsome).ite_decide hr
    ((ComputableTidilyInPolyTime.listReverse encPoint).comp hr))

private theorem routeSecond :
    ComputableInPolyTime (fun r : Route => r.getD 1 (0, 0)) encRoute encPoint := by
  have he : (fun r : Route => r.getD 1 (0, 0)) = (fun r => r.tail.headD (0, 0)) := by
    funext r
    rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> rfl
  rw [he]
  refine .of_tidy ?_
  unfold encRoute
  exact (ComputableTidilyInPolyTime.headD (encA := encPoint)
    (encL := encList encPoint) (0, 0)).comp
      (ComputableTidilyInPolyTime.tail (encA := encPoint) (encL := encList encPoint))

/-- The source exit direction needs only the first two listed route points. -/
@[fun_prop]
theorem sourceDirection :
    ComputableInPolyTime (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
      ExactOne.sourceDirection p.1.1 p.1.2 p.2) encSourceIndex encPoint := by
  have hp : ComputableTidilyInPolyTime
      (fun p : (Graph × Graph.OrthogonalDrawing) × ℕ =>
        (ExactOne.sourceStart p.1.1 p.1.2 p.2,
          (ExactOne.sourceRoute p.1.1 p.1.2 p.2).getD 1 (0, 0)))
      encSourceIndex (encPair encPoint encPoint) :=
    sourceStart.tidy.prod (routeSecond.tidy.comp sourceRoute.tidy)
  simpa only [Function.comp_def, ExactOne.sourceDirection] using
    ComputableInPolyTime.of_tidy (point_direction.tidy.comp hp)

private theorem route_dilate (k : ℕ) :
    ComputableInPolyTime (dilateRoute k) encRoute encRoute := by
  refine .of_tidy ?_
  unfold dilateRoute encRoute
  fun_prop

private theorem point_cut (k radius : ℕ) :
    ComputableInPolyTime (fun p : Point × Point => cutPoint k radius p.1 p.2)
      (encPair encPoint encPoint) encPoint := by
  refine .of_tidy ?_
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
    (ComputableTidilyInPolyTime.listGetD (encA := encPoint) (encL := encRoute) (0, 0)).comp
      ((ComputableTidilyInPolyTime.id' (encIn := encRoute)).prod
        (ComputableTidilyInPolyTime.const i))
  have hcut := (point_cut k radius).tidy.comp ((hget 0).prod (hget 1))
  have htail := (route_dilate k).tidy.comp
    (ComputableTidilyInPolyTime.tail (encA := encPoint))
  have hlen := ComputableTidilyInPolyTime.length encPoint (encL := encRoute)
  have htest := ComputableTidilyInPolyTime.unary_lt.comp
    (hlen.prod (ComputableTidilyInPolyTime.const 2))
  have h := htest.ite_decide (route_dilate k).tidy (hcut.cons' htail)
  apply ComputableInPolyTime.of_tidy
  change ComputableTidilyInPolyTime (fun r => Orthogonal.cutStart k radius r) _ _
  simpa only [cutStart_eq, Function.comp_def] using h

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
  refine .of_tidy ?_
  apply ComputableTidilyInPolyTime.idxOfWithInput
  · exact (Cslib.Logic.PL.computableInPolyTime_occurrences encNat).tidy.comp
      (ComputableTidilyInPolyTime.fst encCNF (encPair encUnary encUnary))
  · change ComputableTidilyInPolyTime
      (fun p : CNF ℕ × (ℕ × ℕ) => sourceOccurrence p.1 p.2.1 p.2.2)
      (encPair encCNF (encPair encUnary encUnary)) (Cslib.Logic.PL.encOccurrence encNat)
    have hφ := ComputableTidilyInPolyTime.fst encCNF (encPair encUnary encUnary)
    have hij := ComputableTidilyInPolyTime.snd encCNF (encPair encUnary encUnary)
    have hi := (ComputableTidilyInPolyTime.fst encUnary encUnary).comp hij
    have hj := (ComputableTidilyInPolyTime.snd encUnary encUnary).comp hij
    have hc : ComputableTidilyInPolyTime
        (fun p : CNF ℕ × (ℕ × ℕ) => p.1.getD p.2.1 [])
        (encPair encCNF (encPair encUnary encUnary)) DrawingFinitePolyTime.encClause :=
      (ComputableTidilyInPolyTime.listGetD (encA := DrawingFinitePolyTime.encClause)
        (encL := encList DrawingFinitePolyTime.encClause) []).comp (hφ.prod hi)
    have hl : ComputableTidilyInPolyTime
        (fun p : CNF ℕ × (ℕ × ℕ) => (p.1.getD p.2.1 []).getD p.2.2 (0, true))
        (encPair encCNF (encPair encUnary encUnary)) (encPair encNat encBool) := by
      have hdrop := (ComputableTidilyInPolyTime.dropUnary
        (encA := encPair encNat encBool) (encL := encList (encPair encNat encBool))).comp
          (hc.prod hj)
      have h := (ComputableTidilyInPolyTime.headD (encA := encPair encNat encBool)
        (encL := encList (encPair encNat encBool)) (0, true)).comp hdrop
      simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
        List.getD_eq_getElem?_getD] using h
    simpa only [Function.comp_def, sourceOccurrence, Cslib.Logic.PL.encOccurrence] using
      hi.prod (hj.prod hl)

private theorem graphDrawing :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => (SAT.incidenceGraph p.1, p.2))
      encInput (encPair encGraph Graph.encOrthogonalDrawing) := by
  have hg := (SAT.computableInPolyTime_incidenceGraph encNat).tidy
  refine .of_tidy ?_
  unfold encInput encCNF at *
  fun_prop

private theorem sourceIndex (j : ℕ) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ((SAT.incidenceGraph p.1.1, p.1.2), ExactOne.sourceEdgeIndex p.1.1 p.2 j))
      (encPair encInput encUnary) encSourceIndex := by
  have hg := graphDrawing.tidy.comp (ComputableTidilyInPolyTime.fst encInput encUnary)
  have hp : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => (p.1.1, (p.2, j)))
      (encPair encInput encUnary) (encPair encCNF (encPair encUnary encUnary)) := by
    unfold encInput
    fun_prop
  have hx : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ExactOne.sourceEdgeIndex p.1.1 p.2 j) (encPair encInput encUnary) encUnary := by
    simpa only [Function.comp_def] using sourceEdgeIndex.tidy.comp hp
  simpa only [Function.comp_def] using ComputableInPolyTime.of_tidy (hg.prod hx)

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
  have hd := (CNF.computableInPolyTime_distinctVars encNat).tidy
  have hn : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => p.1.1.distinctVars.length + p.2)
      (encPair encInput encUnary) encUnary := by
    unfold encInput encCNF at *
    fun_prop
  have hb := ComputableTidilyInPolyTime.unary_to_binary.comp hn
  have hg := graphDrawing.tidy.comp (ComputableTidilyInPolyTime.fst encInput encUnary)
  have hp := drawingPosition.tidy.comp (hg.prod hb)
  have h := (point_scale positiveScale).tidy.comp hp
  simpa only [Function.comp_def, ExactOne.positiveBoxOrigin] using ComputableInPolyTime.of_tidy h

/-- The actual dilated and trimmed inherited route is emitted without searching the plane. -/
@[fun_prop]
theorem positiveExterior (j : ℕ) :
    ComputableInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        ExactOne.positiveExterior p.1.1 p.1.2 p.2 j)
      (encPair encInput encUnary) encRoute := by
  have he := (exteriorRoute positiveScale positiveRadius).tidy.comp (sourceIndex j).tidy
  have h := route_translate.tidy.comp
    ((ComputableTidilyInPolyTime.const positiveTranslation).prod he)
  simpa only [Function.comp_def, ExactOne.positiveExterior] using ComputableInPolyTime.of_tidy h

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
  have ht : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => p.1.take p.2)
      (encPair encCNF encUnary) encCNF := by
    unfold encCNF
    fun_prop
  have hf := (CNF.FromSAT.computableInPolyTime_formula encNat).tidy.comp ht
  have hl := (ComputableTidilyInPolyTime.length
    (encList (encPair (CNF.FromSAT.encVariable encNat) encBool))).comp hf
  simpa only [Function.comp_def, signedOffset_eq_length] using ComputableInPolyTime.of_tidy hl

private abbrev BlockInput := (CNF ℕ × Graph.OrthogonalDrawing) × (ℕ × Clause ℕ)

private abbrev encBlockInput : BlockInput ↪ List Bool :=
  encPair encInput (encPair encUnary DrawingFinitePolyTime.encClause)

private abbrev encRawVariable := DrawingFinitePolyTime.encRawVariable

private abbrev encPlacedClause : PositivePlacedClause ↪ List Bool :=
  encPair (encList (encPair encRawVariable encBool)) (encPair encPoint (encList encRoute))

private theorem blockIndex :
    ComputableTidilyInPolyTime (fun p : BlockInput => (p.1, p.2.1))
      encBlockInput (encPair encInput encUnary) := by
  unfold encBlockInput
  fun_prop

private theorem blockOrigin :
    ComputableTidilyInPolyTime
      (fun p : BlockInput => ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1)
      encBlockInput encPoint := by
  simpa only [Function.comp_def] using positiveBoxOrigin.tidy.comp blockIndex

private theorem blockSignedOffset :
    ComputableTidilyInPolyTime
      (fun p : BlockInput => CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1)
      encBlockInput encUnary := by
  have hp : ComputableTidilyInPolyTime (fun p : BlockInput => (p.1.1, p.2.1))
      encBlockInput (encPair encCNF encUnary) := by
    unfold encBlockInput encInput
    fun_prop
  simpa only [Function.comp_def] using signedOffset.tidy.comp hp

private theorem blockVariable (v : CNF.PositiveExactOneCompile.Variable ℕ) :
    ComputableTidilyInPolyTime (fun p : BlockInput =>
      profileVariableMap p.2.1 (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2 v)
      encBlockInput encRawVariable := by
  rcases v with (n | ⟨i, k⟩) | ⟨⟨i, j⟩, k⟩
  · have hc : ComputableTidilyInPolyTime (fun p : BlockInput => p.2.2)
        encBlockInput DrawingFinitePolyTime.encClause := by
      unfold encBlockInput
      fun_prop
    have hd := (ComputableTidilyInPolyTime.dropUnary (encA := encPair encNat encBool)
      (encL := encList (encPair encNat encBool))).comp
        (hc.prod (ComputableTidilyInPolyTime.const n))
    have h := (ComputableTidilyInPolyTime.headD (encA := encPair encNat encBool)
      (encL := encList (encPair encNat encBool)) (0, true)).comp hd
    have hn : ComputableTidilyInPolyTime (fun p : BlockInput => (p.2.2.getD n (0, true)).1)
        encBlockInput encNat := by
      simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
        List.getD_eq_getElem?_getD] using h.fst'
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
    ComputableTidilyInPolyTime (incidenceFor profile e) encBlockInput encRoute := by
  have hs := route_translate.tidy.comp
    (blockOrigin.prod (ComputableTidilyInPolyTime.const e.2.2))
  have he (j : ℕ) := (positiveExterior j).tidy.comp blockIndex
  unfold incidenceFor
  rcases (profileVariables profile).getD e.2.1 (.inl (.inl 0)) with (j | v) | v
  · exact hs.listAppend' ((ComputableTidilyInPolyTime.tail (encA := encPoint)).comp (he j))
  · exact hs
  · exact hs

private theorem blockTag :
    ComputableTidilyInPolyTime (fun p : BlockInput =>
      (clauseProfile p.2.2, ExactOne.clausePorts p.1.1 p.1.2 p.2.1))
      encBlockInput DrawingFinitePolyTime.encProfilePorts := by
  have hc : ComputableTidilyInPolyTime (fun p : BlockInput => p.2.2)
      encBlockInput DrawingFinitePolyTime.encClause := by
    unfold encBlockInput
    fun_prop
  have hp : ComputableTidilyInPolyTime (fun p : BlockInput => clauseProfile p.2.2)
      encBlockInput (encFinite ClauseProfile) := by
    simpa only [Function.comp_def] using
      DrawingFinitePolyTime.computableInPolyTime_clauseProfile.tidy.comp hc
  have hs : ComputableTidilyInPolyTime
      (fun p : BlockInput => ExactOne.clausePorts p.1.1 p.1.2 p.2.1)
      encBlockInput (encFinite PortAssignment) := by
    simpa only [Function.comp_def] using clausePorts.tidy.comp blockIndex
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
    ComputableTidilyInPolyTime (placedBlockFor tag) encBlockInput (encList encPlacedClause) := by
  unfold placedBlockFor
  apply ComputableTidilyInPolyTime.mapConst
  intro a _
  have hc : ComputableTidilyInPolyTime (fun p : BlockInput => a.1.relabel
      (profileVariableMap p.2.1 (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2))
      encBlockInput (encList (encPair encRawVariable encBool)) := by
    unfold Clause.relabel
    apply ComputableTidilyInPolyTime.mapConst
    intro l _
    exact (blockVariable l.1).prod (ComputableTidilyInPolyTime.const l.2)
  have hp := point_add.tidy.comp (blockOrigin.prod (ComputableTidilyInPolyTime.const
    ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).clausePosition a.2)))
  have hr := ComputableTidilyInPolyTime.mapConst
    ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).incidenceRoutes.filter
      fun e => e.1 == a.2) (fun e _ => incidenceFor_poly tag.1 e)
  exact hc.prod (hp.prod hr)

private theorem positiveClauseBlock :
    ComputableTidilyInPolyTime (fun p : BlockInput =>
      ExactOne.positiveClauseBlock p.1.1 p.1.2 p.2.1 p.2.2)
      encBlockInput (encList encPlacedClause) := by
  convert ComputableTidilyInPolyTime.finite_cases blockTag placedBlockFor_poly using 1
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
    ComputableTidilyInPolyTime (auxiliaryBlockFor tag) encBlockInput
      (encList (encPair encRawVariable encPoint)) := by
  have hlist (xs : List (CNF.PositiveExactOneCompile.Variable ℕ × ℕ)) :
      ComputableTidilyInPolyTime (fun p : BlockInput => xs.filterMap fun v =>
        match v.1 with
        | .inl (.inl _) => none
        | _ => some (profileVariableMap p.2.1
            (CNF.PositiveExactOneCompile.signedOffset p.1.1 p.2.1) p.2.2 v.1,
            ExactOne.positiveBoxOrigin p.1.1 p.1.2 p.2.1 +
              (collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).variablePosition v.2))
        encBlockInput (encList (encPair encRawVariable encPoint)) := by
    induction xs with
    | nil => exact ComputableTidilyInPolyTime.const []
    | cons v xs ih =>
      have hp := point_add.tidy.comp (blockOrigin.prod (ComputableTidilyInPolyTime.const
        ((collaredPrefixGeometry (profilePrefixGeometry tag.1) tag.2).variablePosition v.2)))
      rcases v with ⟨(j | a) | a, n⟩
      · exact ih
      · exact ((blockVariable _).prod hp).cons' ih
      · exact ((blockVariable _).prod hp).cons' ih
  exact hlist _

private theorem positiveAuxiliaryBlock :
    ComputableTidilyInPolyTime (fun p : BlockInput =>
      ExactOne.positiveAuxiliaryBlock p.1.1 p.1.2 p.2.1 p.2.2)
      encBlockInput (encList (encPair encRawVariable encPoint)) := by
  convert ComputableTidilyInPolyTime.finite_cases blockTag auxiliaryBlockFor_poly using 1
  funext p
  rfl

private theorem sourceClauses :
    ComputableTidilyInPolyTime (fun p : CNF ℕ × Graph.OrthogonalDrawing => p.1.zipIdx)
      encInput (encList (encPair DrawingFinitePolyTime.encClause encUnary)) := by
  unfold encInput encCNF DrawingFinitePolyTime.encClause
  fun_prop

private theorem clauseFrame :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × (Clause ℕ × ℕ) =>
        (p.1, (p.2.2, p.2.1)))
      (encPair encInput (encPair DrawingFinitePolyTime.encClause encUnary)) encBlockInput := by
  unfold encBlockInput
  fun_prop

private theorem positivePlacedClauses :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positivePlacedClauses p.1 p.2)
      encInput (encList encPlacedClause) := by
  have hf := positiveClauseBlock.comp clauseFrame
  simpa only [Function.comp_def, ExactOne.positivePlacedClauses] using
    ComputableTidilyInPolyTime.flatMapWithInput sourceClauses hf

private theorem positiveAuxiliaryPositions :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveAuxiliaryPositions p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) := by
  have hf : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × (Clause ℕ × ℕ) =>
        ExactOne.positiveAuxiliaryBlock p.1.1 p.1.2 p.2.2 p.2.1)
      (encPair encInput (encPair DrawingFinitePolyTime.encClause encUnary))
      (encList (encPair encRawVariable encPoint)) := by
    simpa only [Function.comp_def] using positiveAuxiliaryBlock.comp clauseFrame
  unfold ExactOne.positiveAuxiliaryPositions
  exact ComputableTidilyInPolyTime.flatMapWithInput
    (f := fun (p : CNF ℕ × Graph.OrthogonalDrawing) (c : Clause ℕ × ℕ) =>
      ExactOne.positiveAuxiliaryBlock p.1 p.2 c.2 c.1)
    (encA := encPair DrawingFinitePolyTime.encClause encUnary)
    (encB := encPair encRawVariable encPoint) (encIn := encInput) sourceClauses hf

private theorem sourceVariables :
    ComputableTidilyInPolyTime (fun p : CNF ℕ × Graph.OrthogonalDrawing => p.1.distinctVars)
      encInput (encList encNat) :=
  (CNF.computableInPolyTime_distinctVars encNat).tidy.comp
    (ComputableTidilyInPolyTime.fst encCNF Graph.encOrthogonalDrawing)

private theorem sourceVariablePosition :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => positiveScale •
        Graph.drawingPosition (SAT.incidenceGraph p.1.1) p.1.2 (p.1.1.distinctVars.idxOf p.2) +
          positiveTranslation) (encPair encInput encNat) encPoint := by
  have hi : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ => p.1.1.distinctVars.idxOf p.2)
      (encPair encInput encNat) encUnary :=
    ComputableTidilyInPolyTime.idxOfWithInput
      (sourceVariables.comp (ComputableTidilyInPolyTime.fst encInput encNat))
      (ComputableTidilyInPolyTime.snd encInput encNat)
  have hb := ComputableTidilyInPolyTime.unary_to_binary.comp hi
  have hg := graphDrawing.tidy.comp (ComputableTidilyInPolyTime.fst encInput encNat)
  have hp := drawingPosition.tidy.comp (hg.prod hb)
  have h := point_add.tidy.comp (((point_scale positiveScale).tidy.comp hp).prod
    (ComputableTidilyInPolyTime.const positiveTranslation))
  simpa only [Function.comp_def] using h

private theorem positiveSourcePositions :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveSourcePositions p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) := by
  have hv : ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × ℕ =>
        (Sum.inl (Sum.inl p.2) : CNF.PositiveExactOneCompile.Variable ℕ))
      (encPair encInput encNat) encRawVariable := by
    unfold encRawVariable DrawingFinitePolyTime.encRawVariable
      CNF.PositiveExactOneCompile.encVariable CNF.PositiveExactOne.encVariable
      CNF.FromSAT.encVariable
    fun_prop
  simpa only [ExactOne.positiveSourcePositions] using
    ComputableTidilyInPolyTime.mapWithInput sourceVariables (hv.prod sourceVariablePosition)

private theorem positivePositionTable :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positivePositionTable p.1 p.2)
      encInput (encList (encPair encRawVariable encPoint)) :=
  positiveSourcePositions.listAppend' positiveAuxiliaryPositions

private theorem positiveVariablePoint :
    ComputableTidilyInPolyTime
      (fun p : (CNF ℕ × Graph.OrthogonalDrawing) × CNF.PositiveExactOneCompile.Variable ℕ =>
        ExactOne.positiveVariablePoint p.1.1 p.1.2 p.2)
      (encPair encInput encRawVariable) encPoint := by
  have ht := positivePositionTable.comp (ComputableTidilyInPolyTime.fst encInput encRawVariable)
  have hk := (ComputableTidilyInPolyTime.map
    (ComputableTidilyInPolyTime.fst encRawVariable encPoint)).comp ht
  have hp := (ComputableTidilyInPolyTime.map
    (ComputableTidilyInPolyTime.snd encRawVariable encPoint)).comp ht
  have hi := ComputableTidilyInPolyTime.idxOfWithInput hk
    (ComputableTidilyInPolyTime.snd encInput encRawVariable)
  have eqIdx (xs : List (CNF.PositiveExactOneCompile.Variable ℕ))
      (v : CNF.PositiveExactOneCompile.Variable ℕ) :
      @List.idxOf _ instBEqOfDecidableEq v xs = xs.idxOf v := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [List.idxOf_cons, beq_iff_eq, ih]
  have hd := (ComputableTidilyInPolyTime.dropUnary (encA := encPoint)).comp (hp.prod hi)
  have h := (ComputableTidilyInPolyTime.headD (encA := encPoint) (0, 0)).comp hd
  simpa only [Function.comp_def, ExactOne.positiveVariablePoint, List.headD_eq_head?_getD,
    List.head?_drop, List.getD_eq_getElem?_getD, eqIdx] using h

private theorem rawVariables :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (CNF.PositiveExactOneCompile.rawFormula p.1).distinctVars)
      encInput (encList encRawVariable) := by
  have hf : ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => CNF.PositiveExactOneCompile.rawFormula p.1)
      encInput (encList (encList (encPair encRawVariable encBool))) := by
    simpa only [Function.comp_def] using
      (CNF.PositiveExactOneCompile.computableInPolyTime_rawFormula encNat).tidy.comp
        (ComputableTidilyInPolyTime.fst encCNF Graph.encOrthogonalDrawing)
  simpa only [Function.comp_def] using
    (CNF.computableInPolyTime_distinctVars encRawVariable).tidy.comp hf

private theorem outputVariables :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (CNF.PositiveExactOneCompile.rawFormula p.1).distinctVars.map
          (ExactOne.positiveVariablePoint p.1 p.2)) encInput (encList encPoint) :=
  ComputableTidilyInPolyTime.mapWithInput
    (encA := encRawVariable) (encB := encPoint) (encIn := encInput)
    (f := fun p v => ExactOne.positiveVariablePoint p.1 p.2 v) rawVariables positiveVariablePoint

private theorem outputClauses :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (ExactOne.positivePlacedClauses p.1 p.2).map fun c => c.2.1)
      encInput (encList encPoint) := by
  have h := (ComputableTidilyInPolyTime.map
    ((ComputableTidilyInPolyTime.snd (encList (encPair encRawVariable encBool))
      (encPair encPoint (encList encRoute))).fst')).comp positivePlacedClauses
  simpa only [Function.comp_def] using h

private theorem outputRoutes :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing =>
        (ExactOne.positivePlacedClauses p.1 p.2).flatMap fun c => c.2.2)
      encInput (encList encRoute) := by
  have hm := (ComputableTidilyInPolyTime.map
    ((ComputableTidilyInPolyTime.snd (encList (encPair encRawVariable encBool))
      (encPair encPoint (encList encRoute))).snd')).comp positivePlacedClauses
  have h := (ComputableTidilyInPolyTime.flatten encRoute).comp hm
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using h

/-- The actual emitted drawing is natively polynomial-time on binary coordinates and labels.
The proof scans the explicit lists and dispatches among fixed local templates. -/
@[fun_prop]
theorem computableInPolyTime_positiveDrawing :
    ComputableInPolyTime
      (fun p : CNF ℕ × Graph.OrthogonalDrawing => ExactOne.positiveDrawing p.1 p.2)
      encInput Graph.encOrthogonalDrawing := by
  have h := (outputVariables.listAppend' outputClauses).prod outputRoutes
  apply ComputableInPolyTime.of_tidy
  simpa only [Function.comp_def, ExactOne.positiveDrawing, Graph.encOrthogonalDrawing,
    encRoute] using h

end Cslib.Complexity.SAT.ExactOne.DrawingNative
