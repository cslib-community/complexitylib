/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain


import Diag1155.Measure
/-!
# Native polynomial-time computation of the paired-port compiler

Original variable names and all integer coordinates use binary encodings. List positions and
compact ranks use unary counters. The paths, crossing-site selection, and occurrence lookup reuse
the original compiler's native polynomial-time implementations. Ordinary cells are selected from
the retained path points by filtering and first-occurrence selection.

Only the local port tag has a fixed finite encoding: an ordinary side/lane pair or a paired
crossover variable. Template tables and all finite dispatches are fixed independently of the
input formula. Neither the input formulas nor their coordinate or variable domains are finite.

## Main definitions

* `encVariable`: binary cell coordinates and a fixed finite local tag.
* `encPlacedClause`: the emitted clause, position, and literal incidence routes.

## Main results

* `computableInPolyTime_ordinaryCells`: polynomial-time selection of occupied ordinary cells.
* `computableInPolyTime_placedClauses`, `computableInPolyTime_rawFormula`: actual compiler records.
* `computableInPolyTime_formula`: the compact formula under binary CNF encodings.
* `computableInPolyTime_positions`, `computableInPolyTime_routes`: its binary geometric data.

## References

The compiler is the construction defined in `PairedCompile`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal Turing.MultiTapeTM

/-- Binary cell coordinates together with a fixed finite ordinary-port or crossover tag. -/
noncomputable def encVariable : Variable ↪ List Bool :=
  encPair encPoint (encFinite ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))

/-- A clause and its binary position and incidence-route data. -/
noncomputable def encPlacedClause : PlacedClause ↪ List Bool :=
  encPair (encList (encPair encVariable encBool)) (encPair encPoint (encList encRoute))

private theorem computable_natCast :
    ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_natCast.comp
    ComputableTidilyInPolyTime.unary_to_binary)

attribute [local fun_prop] computable_natCast ComputableInPolyTime.tidy

private theorem computable_layoutCenter :
    ComputableInPolyTime Layout.center encUnary encPoint := by
  refine .of_tidy ?_
  unfold Layout.center encPoint
  fun_prop

private theorem computable_side :
    ComputableInPolyTime (fun p : Point × Point => side p.1 p.2)
      (encPair encPoint encPoint) (encFinite (Fin 4)) := by
  refine .of_tidy ?_
  unfold side PlanarCompile.side encPoint
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

private theorem computable_dropLast :
    ComputableInPolyTime (List.dropLast (α := Point)) encRoute encRoute := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun r : Route => r.dropLast) encRoute encRoute
  simp only [List.dropLast_eq_take]
  unfold encRoute
  fun_prop

attribute [local fun_prop] computable_layoutCenter computable_side computable_cellOrigin
  computable_center computable_translate computable_pointAdd computable_dropLast

private theorem computable_distinctPoints :
    ComputableInPolyTime (fun l : Route => selectDistinct l (List.replicate l.length true))
      encRoute encRoute := by
  have hrep : ComputableTidilyInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    ComputableTidilyInPolyTime.of_linear (.of_eq fun _ => rfl)
  refine .of_tidy ?_
  unfold selectDistinct encRoute
  fun_prop

/-- Ordinary cells are selected from polynomial-size retained paths, without enumerating a
coordinate box or a domain depending on the numeric magnitude of an input label. -/
@[fun_prop]
theorem computableInPolyTime_ordinaryCells :
    ComputableInPolyTime ordinaryCells encCNF encRoute := by
  have hp := PlanarCompile.computableInPolyTime_paths.tidy
  have hs := PlanarCompile.computableInPolyTime_crossingSites.tidy
  have hd := computable_dropLast.tidy.comp
    (ComputableTidilyInPolyTime.snd encCNF encRoute)
  have hl := ComputableTidilyInPolyTime.flatMapWithInput
    (f := fun (_ : CNF ℕ) (r : Route) => r.dropLast) (encB := encPoint) hp hd
  have ht : ComputableTidilyInPolyTime (fun p : CNF ℕ × Point =>
      decide (p.2 ∉ crossingSites p.1)) (encPair encCNF encPoint) encBool :=
    .decide_not (.decide_mem (hs.comp (.fst _ _)) (.snd _ _))
  have ho : ComputableTidilyInPolyTime (fun φ : CNF ℕ =>
      ((paths φ).flatMap List.dropLast).filter fun p => decide (p ∉ crossingSites φ))
      encCNF encRoute := .filterWithInput hl ht
  change ComputableInPolyTime (fun φ => ordinaryCells φ) _ _
  simpa only [ordinaryCells, Function.comp_def] using
    computable_distinctPoints.comp (.of_tidy ho)

private theorem computable_port :
    ComputableInPolyTime (fun p : List Point × Point × Fin 4 × Fin 2 =>
      port p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint
        (encPair (encFinite (Fin 4)) (encFinite (Fin 2))))) encVariable := by
  have hi : ComputableTidilyInPolyTime
      (fun p : Fin 4 × Fin 2 => (Sum.inl p : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))
      (encPair (encFinite (Fin 4)) (encFinite (Fin 2)))
      (encFinite ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  have ht : ComputableTidilyInPolyTime
      (fun p : Fin 4 × Fin 2 =>
        (Sum.inr (PairedCrossover.terminal p.1 p.2) : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))
      (encPair (encFinite (Fin 4)) (encFinite (Fin 2)))
      (encFinite ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  let input := encPair encRoute (encPair encPoint
    (encPair (encFinite (Fin 4)) (encFinite (Fin 2))))
  have hs : ComputableTidilyInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => p.1) input encRoute := .fst _ _
  have hp : ComputableTidilyInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => p.2.1) input encPoint := by
    unfold input
    fun_prop
  have ha : ComputableTidilyInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => (p.2.2.1, p.2.2.2)) input
      (encPair (encFinite (Fin 4)) (encFinite (Fin 2))) := by
    unfold input
    fun_prop
  have hm := ComputableTidilyInPolyTime.decide_mem hs hp
  refine .of_tidy ?_
  exact hp.prod (hm.ite_decide (ht.comp ha) (hi.comp ha))

attribute [local fun_prop] computable_port

private theorem computable_signal :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      signal p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinite (Fin 2)))))
      encVariable := by
  refine .of_tidy ?_
  unfold signal
  fun_prop

private theorem computable_variablePosition :
    ComputableInPolyTime variablePosition encVariable encPoint := by
  have hl : ComputableTidilyInPolyTime
      (fun v : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable =>
        v.elim (fun p => PairedPorts.variablePosition p.1 p.2) PairedCrossover.variablePosition)
      (encFinite ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) encPoint := .of_finite _
  refine .of_tidy ?_
  unfold variablePosition encVariable
  fun_prop

private theorem computable_boundary :
    ComputableInPolyTime (fun p : Point × Fin 4 × Fin 2 => boundary p.1 p.2.1 p.2.2)
      (encPair encPoint (encPair (encFinite (Fin 4)) (encFinite (Fin 2)))) encPoint := by
  have hb : ComputableTidilyInPolyTime
      (fun p : Fin 4 × Fin 2 => PairedPorts.boundaryPort p.1 p.2)
      (encPair (encFinite (Fin 4)) (encFinite (Fin 2))) encPoint := .of_finite _
  refine .of_tidy ?_
  unfold boundary
  fun_prop

attribute [local fun_prop] computable_signal computable_variablePosition computable_boundary

private theorem computable_access :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      access p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinite (Fin 2))))) encRoute := by
  refine .of_tidy ?_
  unfold access encRoute
  fun_prop

attribute [local fun_prop] computable_access

private theorem computable_link :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      link p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinite (Fin 2)))))
      encPlacedClause := by
  refine .of_tidy ?_
  dsimp only [link]
  unfold encPlacedClause
  fun_prop

attribute [local fun_prop] computable_link

private theorem computable_links :
    ComputableInPolyTime (fun p : List Point × Route => links p.1 p.2)
      (encPair encRoute encRoute) (encList encPlacedClause) := by
  refine .of_tidy ?_
  unfold links List.consecutivePairs
  fun_prop

private theorem computable_lastLiteral :
    ComputableInPolyTime (fun p : List Point × Route × Bool => lastLiteral p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encRoute encBool))
      (encPair (encPair encVariable encBool) encRoute) := by
  have hl : ComputableTidilyInPolyTime PairedPorts.spokeLane
      (encFinite (Fin 4)) (encFinite (Fin 2)) := .of_finite _
  have he : ComputableTidilyInPolyTime PairedPorts.spokeElbow
      (encFinite (Fin 4)) encPoint := .of_finite _
  refine .of_tidy ?_
  dsimp only [lastLiteral]
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse]
  unfold encRoute
  fun_prop

attribute [local fun_prop] computable_links computable_lastLiteral

private theorem computable_originalClauses :
    ComputableInPolyTime (fun p : CNF ℕ × List Point => originalClauses p.1 p.2)
      (encPair encCNF encRoute) (encList encPlacedClause) := by
  have hp := PlanarCompile.computableInPolyTime_occurrencePath.tidy
  refine .of_tidy ?_
  dsimp only [originalClauses]
  unfold encPlacedClause encCNF
  fun_prop

private theorem computable_templateClauses {A : Type} [Finite A]
    (tag : A → (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable) (ψ : CNF A)
    (clausePositions : List Point) (incidenceRoutes : List (ℕ × A × Route)) :
    ComputableInPolyTime (fun p : Point => ψ.zipIdx.map fun (c, i) =>
      (c.relabel (fun v => (p, tag v)),
        cellOrigin 120 p + clausePositions.getD i (0, 0),
        (incidenceRoutes.filter fun e => e.1 == i).map fun e =>
          translate (cellOrigin 120 p) e.2.2)) encPoint (encList encPlacedClause) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let rowEncoding := encPair (encList (encPair (encFinite A) encBool)) encUnary
  have htag : ComputableTidilyInPolyTime tag (encFinite A)
      (encFinite ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  have hbody : ComputableInPolyTime (fun p : Point × (Clause A × ℕ) =>
      (p.2.1.relabel (fun v => (p.1, tag v)),
        cellOrigin 120 p.1 + clausePositions.getD p.2.2 (0, 0),
        (incidenceRoutes.filter fun e => e.1 == p.2.2).map fun e =>
          translate (cellOrigin 120 p.1) e.2.2))
      (encPair encPoint rowEncoding) encPlacedClause := by
    have hpositions : ComputableTidilyInPolyTime
        (fun _ : Point × (Clause A × ℕ) => clausePositions)
        (encPair encPoint rowEncoding) encRoute := .const _
    have hposition : ComputableTidilyInPolyTime
        (fun p : Point × (Clause A × ℕ) => clausePositions.getD p.2.2 (0, 0))
        (encPair encPoint rowEncoding) encPoint := by
      unfold rowEncoding encRoute at *
      fun_prop
    refine .of_tidy ?_
    unfold rowEncoding encPlacedClause Clause.relabel encVariable Prod.map at *
    fun_prop
  have hlist : ComputableInPolyTime (fun _ : Point => ψ.zipIdx)
      encPoint (encList rowEncoding) := .of_tidy (.const _)
  simpa only [Function.comp_def] using ComputableInPolyTime.mapWithInput hlist hbody

private theorem computable_ordinaryClauses :
    ComputableInPolyTime ordinaryClauses encPoint (encList encPlacedClause) := by
  exact computable_templateClauses Sum.inl OrdinaryRing.formula
    OrdinaryRing.clausePositions OrdinaryRing.incidenceRoutes

private theorem computable_crossingClauses :
    ComputableInPolyTime crossingClauses encPoint (encList encPlacedClause) := by
  exact computable_templateClauses Sum.inr PairedCrossover.formula
    PairedCrossover.clausePositions PairedCrossover.incidenceRoutes

attribute [local fun_prop] computable_originalClauses computable_ordinaryClauses
  computable_crossingClauses

/-- The complete actual list of emitted clauses and drawing records is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_placedClauses :
    ComputableInPolyTime placedClauses encCNF (encList encPlacedClause) := by
  have hs := PlanarCompile.computableInPolyTime_crossingSites.tidy
  have hp := PlanarCompile.computableInPolyTime_occurrencePath.tidy
  have ho := (Cslib.Logic.PL.computableInPolyTime_occurrences encNat).tidy
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => placedClauses φ) _ _
  dsimp only [placedClauses]
  unfold encCNF Cslib.Logic.PL.encOccurrence at *
  fun_prop

/-- Projecting the actual records computes the structured output formula. -/
@[fun_prop]
theorem computableInPolyTime_rawFormula :
    ComputableInPolyTime rawFormula encCNF (encList (encList (encPair encVariable encBool))) := by
  have hp := computableInPolyTime_placedClauses.tidy
  refine .of_tidy ?_
  unfold rawFormula encPlacedClause at *
  fun_prop

/-- The actual compact formula compiler is native polynomial-time under binary CNF encodings.
Compact ranks are computed as unary counters and then encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_formula : ComputableInPolyTime formula encCNF encCNF := by
  have hu := (CNF.isPolyTime_compact encVariable).comp computableInPolyTime_rawFormula
  have hi : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
    .of_tidy ComputableTidilyInPolyTime.unary_to_binary
  have hr := (CNF.computableInPolyTime_relabel hi).comp hu
  have he (ψ : CNF ℕ) : ψ.relabel (fun n : ℕ => n) = ψ := CNF.relabel_id ψ
  change ComputableInPolyTime (fun φ => (rawFormula φ).compact) _ _
  simpa only [Function.comp_def, he, encCNF] using hr

/-- All actual output vertex positions are computed in polynomial time with binary coordinates. -/
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

/-- All actual clause-to-variable incidence routes are computed in polynomial time with binary
coordinates. -/
@[fun_prop]
theorem computableInPolyTime_routes :
    ComputableInPolyTime routes encCNF (encList encRoute) := by
  have hp := computableInPolyTime_placedClauses.tidy
  refine .of_tidy ?_
  unfold routes encPlacedClause at *
  fun_prop

end Cslib.Complexity.SAT.ParsimoniousPlanar
