/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathPolyTime
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Geometry.Orthogonal.Subdivision
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


import Diag1155.Measure
/-!
# Native computation of the finite planarization compiler

Input variable names and all coordinates use binary encodings. Syntactic indices, ranks and
the subdivision budget use unary counters. The fixed template has 53 names independently of
the runtime input, so its finite encoding introduces no growing enumeration.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.encVariable`: binary coordinates and a fixed optional tag.
* `Cslib.Complexity.SAT.PlanarCompile.encPlacedClause`: a clause with its finite geometric data.

## Main results

* `computableInPolyTime_formula`: the complete formula compiler under binary CNF encodings.
* `computableInPolyTime_positions`, `computableInPolyTime_routes`: its actual geometric output.
* `computableInPolyTime_paths`, `computableInPolyTime_crossingSites`: bounded unit paths and
  finite crossing-site selection, with no geometric validity assumption on the input.

## References

The compiler is the finite construction defined in `Compile`.
-/


diag1155_install
@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal Turing.MultiTapeTM

/-- Structured names retain binary coordinates and a fixed finite crossover tag. -/
noncomputable def encVariable : Variable ↪ List Bool :=
  encPair encPoint (encOption (encFinite Crossover.SplitVariable))

/-- Framed literal, position and route data of one emitted clause. -/
noncomputable def encPlacedClause : PlacedClause ↪ List Bool :=
  encPair (encList (encPair encVariable encBool)) (encPair encPoint (encList encRoute))

private theorem computable_natCast :
    ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_natCast.comp
    ComputableTidilyInPolyTime.unary_to_binary)

private theorem computable_finVal :
    ComputableInPolyTime (fun s : Fin 3 => s.val) (encFinite (Fin 3)) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.of_finite _)

attribute [local fun_prop] computable_natCast computable_finVal ComputableInPolyTime.tidy

private theorem computable_incidencePort :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.incidencePort p.2)
      (encPair encGraph encUnary) (encFinite (Fin 3)) := by
  have hc : ComputableTidilyInPolyTime (fun p : Graph × ℕ =>
      (p.1.incidenceVertices.take p.2).count (p.1.incidenceVertices.getD p.2 0))
      (encPair encGraph encUnary) encUnary := by
    unfold Graph.incidenceVertices encGraph
    fun_prop
  exact .of_tidy ((ComputableTidilyInPolyTime.unary_finMod (by decide)
    (encFinite (Fin 3))).comp hc)

attribute [local fun_prop] computable_incidencePort

private theorem computable_canonicalPorts :
    ComputableInPolyTime Graph.canonicalPorts encGraph
      (encList (encPair (encFinite (Fin 3)) (encFinite (Fin 3)))) := by
  refine .of_tidy ?_
  unfold Graph.canonicalPorts encGraph
  fun_prop

attribute [local fun_prop] computable_canonicalPorts

private theorem computable_layoutCenter :
    ComputableInPolyTime Layout.center encUnary encPoint := by
  refine .of_tidy ?_
  unfold Layout.center encPoint
  fun_prop

private theorem computable_layoutColumn :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.column p.1 p.2)
      (encPair encUnary (encFinite (Fin 3))) encIntBin := by
  refine .of_tidy ?_
  unfold Layout.column
  fun_prop

private theorem computable_layoutTrack :
    ComputableInPolyTime (fun p : ℕ × ℕ => Layout.track p.1 p.2)
      (encPair encUnary encUnary) encIntBin := by
  refine .of_tidy ?_
  unfold Layout.track
  fun_prop

attribute [local fun_prop] computable_layoutCenter computable_layoutColumn computable_layoutTrack

private theorem computable_layoutElbow :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => Layout.elbow p.1 p.2)
      (encPair encUnary (encFinite (Fin 3))) encPoint := by
  refine .of_tidy ?_
  unfold Layout.elbow encPoint
  fun_prop

attribute [local fun_prop] computable_layoutElbow

private theorem computable_layoutRoute :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ × Fin 3 × Fin 3 =>
      Layout.route p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary (encPair (encFinite (Fin 3)) (encFinite (Fin 3))))))) encRoute := by
  refine .of_tidy ?_
  unfold Layout.route encRoute
  fun_prop

attribute [local fun_prop] computable_layoutRoute

private theorem computable_orthogonalRoutes :
    ComputableInPolyTime (fun G : Graph => G.orthogonalRoutes G.canonicalPorts)
      encGraph (encList encRoute) := by
  let edgeEncoding := encPair (encPair encNat encNat) encUnary
  let routeInput := encPair encUnary (encPair encUnary (encPair encUnary
    (encPair encUnary (encPair (encFinite (Fin 3)) (encFinite (Fin 3))))))
  have hcan := computable_canonicalPorts.tidy
  have hp : ComputableTidilyInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) =>
      p.1.canonicalPorts.getD p.2.2 (0, 0))
      (encPair encGraph edgeEncoding) (encPair (encFinite (Fin 3)) (encFinite (Fin 3))) := by
    unfold edgeEncoding encGraph
    fun_prop
  have hargs : ComputableInPolyTime (fun p : Graph × ((ℕ × ℕ) × ℕ) =>
      (p.1.1.length, p.2.2, p.1.1.idxOf p.2.1.1, p.1.1.idxOf p.2.1.2,
        (p.1.canonicalPorts.getD p.2.2 (0, 0)).1,
        (p.1.canonicalPorts.getD p.2.2 (0, 0)).2))
      (encPair encGraph edgeEncoding) routeInput := by
    refine .of_tidy ?_
    unfold routeInput edgeEncoding encGraph at *
    fun_prop
  have hbody := computable_layoutRoute.comp hargs
  have hlist : ComputableInPolyTime (fun G : Graph => G.2.zipIdx) encGraph
      (encList edgeEncoding) := by
    refine .of_tidy ?_
    unfold encGraph edgeEncoding
    fun_prop
  simpa only [Graph.orthogonalRoutes, Function.comp_def] using
    ComputableInPolyTime.mapWithInput hlist hbody

attribute [local fun_prop] computable_orthogonalRoutes

private def endpointColumns (p : Graph × ℕ) : Point :=
  (Layout.column (p.1.1.idxOf (p.1.edgeEndpoint p.2 false))
      (Graph.portAt p.1.canonicalPorts p.2 false),
    Layout.column (p.1.1.idxOf (p.1.edgeEndpoint p.2 true))
      (Graph.portAt p.1.canonicalPorts p.2 true))

private theorem computable_endpointColumns :
    ComputableInPolyTime endpointColumns (encPair encGraph encUnary) encPoint := by
  unfold endpointColumns
  have hcan := computable_canonicalPorts.tidy
  have hp : ComputableTidilyInPolyTime (fun p : Graph × ℕ =>
      p.1.canonicalPorts.getD p.2 (0, 0))
      (encPair encGraph encUnary) (encPair (encFinite (Fin 3)) (encFinite (Fin 3))) := by
    unfold encGraph
    fun_prop
  have he : ComputableTidilyInPolyTime (fun p : Graph × ℕ => p.1.2.getD p.2 (0, 0))
      (encPair encGraph encUnary) (encPair encNat encNat) := by
    unfold encGraph
    fun_prop
  refine .of_tidy ?_
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
  have hselect : ComputableTidilyInPolyTime
      (fun p : Graph × (ℕ × ℕ) => (p.1, p.2.2))
      (encPair encGraph (encPair encUnary encUnary)) (encPair encGraph encUnary) := by fun_prop
  have hcols := computable_endpointColumns.tidy.comp hselect
  have hleft := hcols.fst'
  have hright := hcols.snd'
  have htrack : ComputableTidilyInPolyTime (fun p : Graph × (ℕ × ℕ) =>
      Layout.track p.1.1.length p.2.1)
      (encPair encGraph (encPair encUnary encUnary)) encIntBin := by
    unfold encGraph
    fun_prop
  refine .of_tidy ?_
  unfold candidatePair encPoint at *
  fun_prop

private def candidateRow (p : Graph × ℕ) : List Point :=
  (List.range p.1.2.length).flatMap fun j => candidatePair (p.1, p.2, j)

private theorem computable_edgeRange :
    ComputableInPolyTime (fun G : Graph => List.range G.2.length) encGraph
      (encList encUnary) := by
  refine .of_tidy ?_
  unfold encGraph
  fun_prop

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
  refine .of_tidy ?_
  unfold Graph.orthogonalPositions encRoute encGraph
  fun_prop

attribute [local fun_prop] computable_orthogonalPositions

private theorem computable_distinctPoints :
    ComputableInPolyTime (fun l : Route => selectDistinct l (List.replicate l.length true))
      encRoute encRoute := by
  have hrep : ComputableTidilyInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    ComputableTidilyInPolyTime.of_linear (.of_eq fun _ => rfl)
  refine .of_tidy ?_
  unfold selectDistinct encRoute
  fun_prop

private theorem computable_crossingPredicate :
    ComputableInPolyTime (fun p : CNF ℕ × Point =>
      !((SAT.incidenceGraph p.1).orthogonalPositions.contains p.2) &&
        decide (2 ≤ ((paths p.1).filter fun r => r.contains p.2).length))
      (encPair encCNF encPoint) encBool := by
  have hg := SAT.computableInPolyTime_incidenceGraph encNat
  have hv : ComputableTidilyInPolyTime (fun p : CNF ℕ × Point =>
      (SAT.incidenceGraph p.1).orthogonalPositions) (encPair encCNF encPoint) encRoute :=
    (computable_orthogonalPositions.comp hg).tidy.comp (ComputableTidilyInPolyTime.fst _ _)
  have hp : ComputableTidilyInPolyTime (fun p : CNF ℕ × Point => paths p.1)
      (encPair encCNF encPoint) (encList encRoute) :=
    computableInPolyTime_paths.tidy.comp (ComputableTidilyInPolyTime.fst _ _)
  refine .of_tidy ?_
  unfold encRoute at *
  simp only [List.contains_eq_mem]
  fun_prop

private theorem computable_side :
    ComputableInPolyTime (fun p : Point × Point => side p.1 p.2)
      (encPair encPoint encPoint) (encFinite (Fin 4)) := by
  refine .of_tidy ?_
  unfold side encPoint
  fun_prop

private theorem computable_cellOrigin :
    ComputableInPolyTime (cellOrigin 120) encPoint encPoint := by
  refine .of_tidy ?_
  unfold cellOrigin encPoint
  fun_prop

private theorem computable_center : ComputableInPolyTime center encPoint encPoint := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun p : Point =>
    (240 * p.1 + 120, 240 * p.2 + 120)) encPoint encPoint
  unfold encPoint
  fun_prop

private theorem computable_translate :
    ComputableInPolyTime (fun p : Point × Route => translate p.1 p.2)
      (encPair encPoint encRoute) encRoute := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun p : Point × Route =>
    p.2.map fun q => (q.1 + p.1.1, q.2 + p.1.2)) _ _
  unfold encPoint encRoute
  fun_prop

private theorem computable_pointAdd :
    ComputableInPolyTime (fun p : Point × Point => p.1 + p.2)
      (encPair encPoint encPoint) encPoint := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun p : Point × Point =>
    (p.1.1 + p.2.1, p.1.2 + p.2.2)) _ _
  unfold encPoint
  fun_prop

attribute [local fun_prop] computable_side computable_cellOrigin computable_center
  computable_translate computable_pointAdd

private theorem computable_signal :
    ComputableInPolyTime (fun p : List Point × Point × Point => signal p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encPoint encPoint)) encVariable := by
  have ht : ComputableTidilyInPolyTime Crossover.splitTerminal (encFinite (Fin 4))
      (encFinite Crossover.SplitVariable) := ComputableTidilyInPolyTime.of_finite _
  refine .of_tidy ?_
  unfold signal encVariable encRoute
  fun_prop

private theorem computable_cellPort :
    ComputableInPolyTime (fun p : Point × Fin 4 => cellPort 120 p.1 p.2)
      (encPair encPoint (encFinite (Fin 4))) encPoint := by
  refine .of_tidy ?_
  have hlocal : ComputableTidilyInPolyTime (cellPort 120 (0, 0)) (encFinite (Fin 4))
      encPoint := ComputableTidilyInPolyTime.of_finite _
  have heq : (fun p : Point × Fin 4 => cellPort 120 p.1 p.2) =
      fun p => cellOrigin 120 p.1 + cellPort 120 (0, 0) p.2 := by
    funext p
    simp [cellPort, cellOrigin]
  rw [heq]
  fun_prop

attribute [local fun_prop] computable_cellPort

private theorem computable_access :
    ComputableInPolyTime (fun p : List Point × Point × Point => access p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encPoint encPoint)) encRoute := by
  have ha : ComputableTidilyInPolyTime Crossover.accessRoute (encFinite (Fin 4)) encRoute :=
    ComputableTidilyInPolyTime.of_finite _
  refine .of_tidy ?_
  unfold access encRoute
  fun_prop

attribute [local fun_prop] computable_signal computable_access

private theorem computable_variablePosition :
    ComputableInPolyTime variablePosition encVariable encPoint := by
  have hl : ComputableTidilyInPolyTime (fun v : Option Crossover.SplitVariable =>
      v.elim (120, 120) Crossover.variablePosition)
      (encOption (encFinite Crossover.SplitVariable)) encPoint :=
    ComputableTidilyInPolyTime.of_finite _
  refine .of_tidy ?_
  unfold variablePosition encVariable
  fun_prop

private theorem computable_link :
    ComputableInPolyTime (fun p : List Point × Bool × Point × Point =>
      link p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encBool (encPair encPoint encPoint))) encPlacedClause := by
  refine .of_tidy ?_
  dsimp only [link]
  unfold encPlacedClause
  fun_prop

private theorem computable_dropLast :
    ComputableInPolyTime (List.dropLast (α := Point)) encRoute encRoute := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun r : Route => r.dropLast) encRoute encRoute
  simp only [List.dropLast_eq_take]
  unfold encRoute
  fun_prop

attribute [local fun_prop] computable_variablePosition computable_link computable_dropLast

private theorem computable_links :
    ComputableInPolyTime (fun p : List Point × Bool × Route => links p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encBool encRoute)) (encList encPlacedClause) := by
  refine .of_tidy ?_
  unfold links List.consecutivePairs
  fun_prop

private theorem computable_lastLiteral :
    ComputableInPolyTime (fun p : List Point × Route × Bool => lastLiteral p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encRoute encBool))
      (encPair (encPair encVariable encBool) encRoute) := by
  refine .of_tidy ?_
  dsimp only [lastLiteral]
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse]
  unfold encRoute
  fun_prop

attribute [local fun_prop] computable_links computable_lastLiteral

private theorem computable_originalClauses :
    ComputableInPolyTime (fun p : CNF ℕ × List Point => originalClauses p.1 p.2)
      (encPair encCNF encRoute) (encList encPlacedClause) := by
  refine .of_tidy ?_
  dsimp only [originalClauses]
  unfold encPlacedClause encCNF
  fun_prop

private theorem computable_crossingClauses :
    ComputableInPolyTime crossingClauses encPoint (encList encPlacedClause) := by
  let rowEncoding := encPair
    (encList (encPair (encFinite Crossover.SplitVariable) encBool)) encUnary
  have hbody : ComputableInPolyTime (fun p : Point × (Clause Crossover.SplitVariable × ℕ) =>
      (p.2.1.relabel (fun v => (p.1, some v)),
        cellOrigin 120 p.1 + Crossover.clausePositions.getD p.2.2 (0, 0),
        (Crossover.incidenceRoutes.filter fun e => e.1 == p.2.2).map fun e =>
          translate (cellOrigin 120 p.1) e.2.2))
      (encPair encPoint rowEncoding) encPlacedClause := by
    have horigin := computable_cellOrigin.tidy.comp
      (ComputableTidilyInPolyTime.fst encPoint rowEncoding)
    have hpositions : ComputableTidilyInPolyTime
        (fun _ : Point × (Clause Crossover.SplitVariable × ℕ) => Crossover.clausePositions)
        (encPair encPoint rowEncoding) encRoute := ComputableTidilyInPolyTime.const _
    have hposition : ComputableTidilyInPolyTime
        (fun p : Point × (Clause Crossover.SplitVariable × ℕ) =>
          Crossover.clausePositions.getD p.2.2 (0, 0))
        (encPair encPoint rowEncoding) encPoint := by
      unfold rowEncoding encRoute at *
      fun_prop
    refine .of_tidy ?_
    unfold rowEncoding encPlacedClause Clause.relabel encVariable Prod.map at *
    fun_prop
  have hlist : ComputableInPolyTime (fun _ : Point => Crossover.splitFormula.zipIdx)
      encPoint (encList rowEncoding) := .of_tidy (ComputableTidilyInPolyTime.const _)
  change ComputableInPolyTime (fun p => crossingClauses p) _ _
  simpa only [crossingClauses] using ComputableInPolyTime.mapWithInput hlist hbody

attribute [local fun_prop] computable_originalClauses computable_crossingClauses

/-- The actual clause and incidence-route records are produced in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_placedClauses :
    ComputableInPolyTime placedClauses encCNF (encList encPlacedClause) := by
  have hs := computableInPolyTime_crossingSites.tidy
  have ho := (Cslib.Logic.PL.computableInPolyTime_occurrences encNat).tidy
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => placedClauses φ) _ _
  dsimp only [placedClauses]
  unfold encCNF Cslib.Logic.PL.encOccurrence at *
  fun_prop

/-- Structured formula output is computed by projecting the actual emitted clause records. -/
@[fun_prop]
theorem computableInPolyTime_rawFormula :
    ComputableInPolyTime rawFormula encCNF (encList (encList (encPair encVariable encBool))) := by
  have hp := computableInPolyTime_placedClauses.tidy
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => rawFormula φ) _ _
  unfold rawFormula encPlacedClause at *
  fun_prop

/-- The complete formula compiler is native polynomial-time under the usual binary CNF
encoding. Compact indices are computed in unary and then encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_formula : ComputableInPolyTime formula encCNF encCNF := by
  have hu := (CNF.isPolyTime_compact encVariable).comp computableInPolyTime_rawFormula
  have hi : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
    .of_tidy ComputableTidilyInPolyTime.unary_to_binary
  have hr := (CNF.computableInPolyTime_relabel hi).comp hu
  have he (ψ : CNF ℕ) : ψ.relabel (fun n : ℕ => n) = ψ := CNF.relabel_id ψ
  change ComputableInPolyTime (fun φ => (rawFormula φ).compact) _ _
  simpa only [Function.comp_def, he, encCNF] using hr

/-- All output vertex positions are computed in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_positions : ComputableInPolyTime positions encCNF encRoute := by
  have hv := (CNF.computableInPolyTime_distinctVars encVariable).comp
    computableInPolyTime_rawFormula
  have hp := computableInPolyTime_placedClauses.tidy
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => positions φ) _ _
  dsimp only [positions]
  unfold encPlacedClause encRoute at *
  fun_prop

/-- All output incidence routes are computed in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_routes :
    ComputableInPolyTime routes encCNF (encList encRoute) := by
  have hp := computableInPolyTime_placedClauses.tidy
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => routes φ) _ _
  unfold routes encPlacedClause at *
  fun_prop

end Cslib.Complexity.SAT.PlanarCompile
