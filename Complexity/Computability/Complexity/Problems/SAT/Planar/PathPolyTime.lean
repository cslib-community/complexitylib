/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathData
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Geometry.Orthogonal.Subdivision
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


/-!
# Native computation of canonical path data

Input natural labels and coordinates use binary encodings; syntactic positions and the
subdivision budget use unary counters. These certificates compute only the shared paths,
crossing cells, and occurrence lookup, with no geometric validity assumption.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_budget`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_paths`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_crossingSites`.
* `Cslib.Complexity.SAT.PlanarCompile.computableInPolyTime_occurrencePath`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal
open Turing.MultiTapeTM

private theorem computable_intAdd {α : Type} {enc : α ↪ List Bool} {f g : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin)
    (hg : ComputableInPolyTime g enc encIntBin) :
    ComputableInPolyTime (fun a => f a + g a) enc encIntBin :=
  (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin by fun_prop).comp (hf.prod hg)

private theorem computable_natCast :
    ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  ComputableInPolyTime.intBin_natCast.comp ComputableInPolyTime.unary_to_binary

private theorem computable_finVal :
    ComputableInPolyTime (fun s : Fin 3 => s.val) (encFinEnum (Fin 3)) encUnary :=
  ComputableInPolyTime.of_finite _

attribute [local fun_prop] computable_intAdd computable_natCast computable_finVal

private theorem computable_incidencePort :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.incidencePort p.2)
      (encPair encGraph encUnary) (encFinEnum (Fin 3)) := by
  let unary3 : Fin 3 ↪ List Bool :=
    ⟨fun index => encUnary index.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩
  have hmod : ComputableInPolyTime (fun index : ℕ =>
      (⟨index % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3)) encUnary (encFinEnum (Fin 3)) :=
    (ComputableInPolyTime.of_finite (encIn := unary3) (encOut := encFinEnum (Fin 3)) id).comp
      ((ComputableInPolyTime.unary_mod.comp
        (ComputableInPolyTime.id'.prod (.const 3))).of_enc_eq fun _ => rfl)
  have hiv : ComputableInPolyTime Graph.incidenceVertices encGraph (encList encNat) := by
    unfold Graph.incidenceVertices encGraph
    fun_prop
  have htake : ComputableInPolyTime (fun q : List ℕ × ℕ => q.1.take q.2)
      (encPair (encList encNat) encUnary) (encList encNat) := by fun_prop
  have hc : ComputableInPolyTime (fun p : Graph × ℕ =>
      (p.1.incidenceVertices.take p.2).count (p.1.incidenceVertices.getD p.2 0))
      (encPair encGraph encUnary) encUnary := by
    simp only [List.count_eq_countP]
    have hl := htake.comp ((hiv.comp (.fst _ _)).prod (.snd _ _))
    have hv := ComputableInPolyTime.listGetDWithInput (hiv.comp (.fst _ _)) (.snd _ _) 0
    exact ComputableInPolyTime.countPWithInput hl
      ((ComputableInPolyTime.snd _ _).beq (hv.comp (.fst _ _)))
  exact hmod.comp hc

attribute [local fun_prop] computable_incidencePort

private theorem computable_canonicalPorts :
    ComputableInPolyTime Graph.canonicalPorts encGraph
      (encList (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3)))) := by
  have hlen : ComputableInPolyTime (fun G : Graph => G.2.length) encGraph encUnary :=
    (ComputableInPolyTime.length_list (encPair encNat encNat)).comp
      (by unfold encGraph; fun_prop)
  unfold Graph.canonicalPorts
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hlen) (by fun_prop)

attribute [local fun_prop] computable_canonicalPorts

private theorem computable_layoutCenter :
    ComputableInPolyTime Layout.center encUnary encPoint := by
  unfold Layout.center encPoint
  fun_prop

private theorem computable_layoutColumn :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.column p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encIntBin := by
  unfold Layout.column
  fun_prop

private theorem computable_layoutTrack :
    ComputableInPolyTime (fun p : ℕ × ℕ => Layout.track p.1 p.2)
      (encPair encUnary encUnary) encIntBin := by
  unfold Layout.track
  fun_prop

attribute [local fun_prop] computable_layoutCenter computable_layoutColumn computable_layoutTrack

private theorem computable_layoutElbow :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.elbow p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encPoint := by
  unfold Layout.elbow encPoint
  fun_prop

attribute [local fun_prop] computable_layoutElbow

private theorem computable_layoutRoute :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ × Fin 3 × Fin 3 =>
      Layout.route p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3))))))) encRoute := by
  unfold Layout.route encRoute
  fun_prop

attribute [local fun_prop] computable_layoutRoute

private theorem computable_orthogonalRoutes :
    ComputableInPolyTime (fun G : Graph => G.orthogonalRoutes G.canonicalPorts)
      encGraph (encList encRoute) := by
  let edgeEncoding := encPair (encPair encNat encNat) encUnary
  let routeInput := encPair encUnary (encPair encUnary (encPair encUnary
    (encPair encUnary (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3))))))
  have hp : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) =>
      p.1.canonicalPorts.getD p.2.2 (0, 0))
      (encPair encGraph edgeEncoding) (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3))) :=
    ComputableInPolyTime.listGetDWithInput (computable_canonicalPorts.comp (.fst _ _))
      (by unfold edgeEncoding; fun_prop) (0, 0)
  have hvlen : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) => p.1.1.length)
      (encPair encGraph edgeEncoding) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp (by unfold encGraph; fun_prop)
  have hargs : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) =>
      (p.1.1.length, p.2.2, p.1.1.idxOf p.2.1.1, p.1.1.idxOf p.2.1.2,
        (p.1.canonicalPorts.getD p.2.2 (0, 0)).1,
        (p.1.canonicalPorts.getD p.2.2 (0, 0)).2))
      (encPair encGraph edgeEncoding) routeInput := by
    unfold routeInput edgeEncoding encGraph at *
    fun_prop
  have hbody := computable_layoutRoute.comp hargs
  have hzip : ComputableInPolyTime (List.zipIdx (α := ℕ × ℕ))
      (encList (encPair encNat encNat)) (encList edgeEncoding) := by
    unfold edgeEncoding
    fun_prop
  have hlist : ComputableInPolyTime (fun G : Graph => G.2.zipIdx) encGraph
      (encList edgeEncoding) :=
    hzip.comp (by unfold encGraph; fun_prop)
  simpa only [Graph.orthogonalRoutes, Function.comp_def] using
    ComputableInPolyTime.mapWithInput hlist hbody

attribute [local fun_prop] computable_orthogonalRoutes

/-- The budget is a linear expression in syntactic list lengths, computed as a unary counter. -/
@[fun_prop]
theorem computableInPolyTime_budget : ComputableInPolyTime budget encCNF encUnary := by
  have hg := SAT.computableInPolyTime_incidenceGraph encNat
  have hl1 : ComputableInPolyTime (fun φ : CNF ℕ => (SAT.incidenceGraph φ).1.length)
      encCNF encUnary :=
    (ComputableInPolyTime.length_list encNat).comp (by unfold encGraph at hg; exact hg.fst')
  have hl2 : ComputableInPolyTime (fun φ : CNF ℕ => (SAT.incidenceGraph φ).2.length)
      encCNF encUnary :=
    (ComputableInPolyTime.length_list (encPair encNat encNat)).comp
      (by unfold encGraph at hg; exact hg.snd')
  unfold budget
  fun_prop

/-- Canonical incidence routes have a native polynomial-time bounded unit expansion.
The input labels and output coordinates are binary; only the step budget is unary. -/
@[fun_prop]
theorem computableInPolyTime_paths :
    ComputableInPolyTime paths encCNF (encList encRoute) := by
  change ComputableInPolyTime (fun φ =>
    ((SAT.incidenceGraph φ).orthogonalRoutes (SAT.incidenceGraph φ).canonicalPorts).map
      (subdivideWithin (budget φ))) encCNF (encList encRoute)
  have hraw := computable_orthogonalRoutes.comp (SAT.computableInPolyTime_incidenceGraph encNat)
  have hargs : ComputableInPolyTime (fun p : CNF ℕ × Route => (budget p.1, p.2))
      (encPair encCNF encRoute) (encPair encUnary encRoute) := by fun_prop
  have hsub := computableInPolyTime_subdivideWithin.comp hargs
  simpa only [Function.comp_def, encCNF] using ComputableInPolyTime.mapWithInput hraw hsub

private def endpointColumns (p : Graph × ℕ) : Point :=
  (Layout.column (p.1.1.idxOf (p.1.edgeEndpoint p.2 false))
      (Graph.portAt p.1.canonicalPorts p.2 false),
    Layout.column (p.1.1.idxOf (p.1.edgeEndpoint p.2 true))
      (Graph.portAt p.1.canonicalPorts p.2 true))

private theorem computable_endpointColumns :
    ComputableInPolyTime endpointColumns (encPair encGraph encUnary) encPoint := by
  unfold endpointColumns
  have hp : ComputableInPolyTime (fun p : Graph × ℕ =>
      p.1.canonicalPorts.getD p.2 (0, 0))
      (encPair encGraph encUnary) (encPair (encFinEnum (Fin 3)) (encFinEnum (Fin 3))) :=
    ComputableInPolyTime.listGetDWithInput (computable_canonicalPorts.comp (.fst _ _))
      (.snd _ _) (0, 0)
  have he : ComputableInPolyTime (fun p : Graph × ℕ => p.1.2.getD p.2 (0, 0))
      (encPair encGraph encUnary) (encPair encNat encNat) := by
    unfold encGraph
    fun_prop
  unfold Graph.edgeEndpoint Graph.portAt encPoint encGraph at *
  simp only [Bool.false_eq_true, ↓reduceIte]
  fun_prop

attribute [local fun_prop] computable_endpointColumns

private def candidatePair (p : Graph × (ℕ × ℕ)) : List Point :=
  [((endpointColumns (p.1, p.2.2)).1, Layout.track p.1.1.length p.2.1),
    ((endpointColumns (p.1, p.2.2)).2, Layout.track p.1.1.length p.2.1)]

private theorem computable_candidatePair :
    ComputableInPolyTime candidatePair (encPair encGraph (encPair encUnary encUnary))
      (encList encPoint) := by
  have hselect : ComputableInPolyTime
      (fun p : Graph × (ℕ × ℕ) => (p.1, p.2.2))
      (encPair encGraph (encPair encUnary encUnary)) (encPair encGraph encUnary) := by fun_prop
  have hcols := computable_endpointColumns.comp hselect
  have hleft := hcols.fst'
  have hright := hcols.snd'
  have hvlen : ComputableInPolyTime (fun p : Graph × (ℕ × ℕ) => p.1.1.length)
      (encPair encGraph (encPair encUnary encUnary)) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp (by unfold encGraph; fun_prop)
  have htrack : ComputableInPolyTime (fun p : Graph × (ℕ × ℕ) =>
      Layout.track p.1.1.length p.2.1)
      (encPair encGraph (encPair encUnary encUnary)) encIntBin := by
    fun_prop
  unfold candidatePair encPoint at *
  fun_prop

private def candidateRow (p : Graph × ℕ) : List Point :=
  (List.range p.1.2.length).flatMap fun j => candidatePair (p.1, p.2, j)

private theorem computable_edgeRange :
    ComputableInPolyTime (fun G : Graph => List.range G.2.length) encGraph
      (encList encUnary) :=
  ComputableInPolyTime.range.comp
    ((ComputableInPolyTime.length_list (encPair encNat encNat)).comp
      (by unfold encGraph; fun_prop))

private theorem computable_candidateRow :
    ComputableInPolyTime candidateRow (encPair encGraph encUnary) (encList encPoint) := by
  have hlist := computable_edgeRange.comp (ComputableInPolyTime.fst encGraph encUnary)
  have harg : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
      (encPair (encPair encGraph encUnary) encUnary)
      (encPair encGraph (encPair encUnary encUnary)) := by fun_prop
  have hbody := computable_candidatePair.comp harg
  change ComputableInPolyTime (fun p : Graph × ℕ =>
    (List.range p.1.2.length).flatMap fun j => candidatePair (p.1, p.2, j)) _ _
  simpa only [Function.comp_def] using ComputableInPolyTime.flatMapWithInput hlist hbody

private theorem computable_crossingCandidates :
    ComputableInPolyTime (fun G : Graph => G.crossingCandidates G.canonicalPorts)
      encGraph (encList encPoint) := by
  have h := ComputableInPolyTime.flatMapWithInput
    (f := fun G i => candidateRow (G, i)) (encB := encPoint)
    computable_edgeRange computable_candidateRow
  simpa only [candidateRow, candidatePair, endpointColumns, Graph.crossingCandidates] using h

attribute [local fun_prop] computable_crossingCandidates

private theorem computable_orthogonalPositions :
    ComputableInPolyTime Graph.orthogonalPositions encGraph encRoute := by
  unfold Graph.orthogonalPositions encRoute
  exact (ComputableInPolyTime.map computable_layoutCenter).comp
    (ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.length_list encNat).comp (by unfold encGraph; fun_prop)))

attribute [local fun_prop] computable_orthogonalPositions

private theorem computable_distinctPoints :
    ComputableInPolyTime (fun l : Route => selectDistinct l (List.replicate l.length true))
      encRoute encRoute := by
  have hrep : ComputableInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hlen : ComputableInPolyTime (fun l : Route => l.length) encRoute encUnary :=
    ComputableInPolyTime.length_list encPoint
  unfold encRoute at *
  fun_prop

private theorem computable_crossingPredicate :
    ComputableInPolyTime (fun p : CNF ℕ × Point =>
      !((SAT.incidenceGraph p.1).orthogonalPositions.contains p.2) &&
        decide (2 ≤ ((paths p.1).filter fun r => r.contains p.2).length))
      (encPair encCNF encPoint) encBool := by
  have hg := SAT.computableInPolyTime_incidenceGraph encNat
  have hv : ComputableInPolyTime (fun p : CNF ℕ × Point =>
      (SAT.incidenceGraph p.1).orthogonalPositions)
      (encPair encCNF encPoint) (encList encPoint) :=
    (computable_orthogonalPositions.comp hg).comp (ComputableInPolyTime.fst _ _)
  have hp : ComputableInPolyTime (fun p : CNF ℕ × Point => paths p.1)
      (encPair encCNF encPoint) (encList (encList encPoint)) :=
    computableInPolyTime_paths.comp (ComputableInPolyTime.fst _ _)
  simp only [List.contains_eq_mem]
  have hf : ComputableInPolyTime
      (fun p : CNF ℕ × Point => (paths p.1).filter fun r => decide (p.2 ∈ r))
      (encPair encCNF encPoint) (encList (encList encPoint)) :=
    ComputableInPolyTime.filterWithInput hp (by fun_prop)
  have hflen : ComputableInPolyTime
      (fun p : CNF ℕ × Point => ((paths p.1).filter fun r => decide (p.2 ∈ r)).length)
      (encPair encCNF encPoint) encUnary :=
    (ComputableInPolyTime.length_list (encList encPoint)).comp hf
  fun_prop

/-- Occupied nonvertex crossing sites can be selected in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_crossingSites :
    ComputableInPolyTime crossingSites encCNF encRoute := by
  have hc := computable_crossingCandidates.comp (SAT.computableInPolyTime_incidenceGraph encNat)
  have hf := ComputableInPolyTime.filterWithInput
    (test := fun φ p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
      decide (2 ≤ ((paths φ).filter fun r => r.contains p).length))
    hc computable_crossingPredicate
  have h := computable_distinctPoints.comp hf
  change ComputableInPolyTime (fun φ =>
    selectDistinct
      (((SAT.incidenceGraph φ).crossingCandidates (SAT.incidenceGraph φ).canonicalPorts).filter
        fun p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
          decide (2 ≤ ((paths φ).filter fun r => r.contains p).length))
      (List.replicate
        ((((SAT.incidenceGraph φ).crossingCandidates (SAT.incidenceGraph φ).canonicalPorts).filter
          fun p => !((SAT.incidenceGraph φ).orthogonalPositions.contains p) &&
            decide (2 ≤ ((paths φ).filter fun r => r.contains p).length)).length) true)) _ _
  simpa only [Function.comp_def, encCNF] using h

/-- Looking up the path for a syntactic literal occurrence is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_occurrencePath :
    ComputableInPolyTime (fun p : CNF ℕ × Occurrence ℕ => occurrencePath p.1 p.2)
      (encPair encCNF (Cslib.Logic.PL.encOccurrence encNat)) encRoute :=
  ComputableInPolyTime.listGetDWithInput
    (computableInPolyTime_paths.comp (ComputableInPolyTime.fst _ _))
    (ComputableInPolyTime.idxOfWithInput
      ((Cslib.Logic.PL.computableInPolyTime_occurrences encNat).comp
        (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)) []

end Cslib.Complexity.SAT.PlanarCompile
