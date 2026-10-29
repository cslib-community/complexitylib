/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

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

/-- Explicit constructive enumeration of the eight split internal crossover variables. -/
local instance : FinEnum Crossover.Internal :=
  FinEnum.ofList [.aInnerLeft, .upperLeft, .lowerLeft, .bInnerTop, .bInnerBottom,
    .upperRight, .lowerRight, .aInnerRight] fun v => by cases v <;> decide

/-- Explicit constructive enumeration of the 57 paired-crossover variables. -/
instance : FinEnum PairedCrossover.Variable :=
  FinEnum.ofEquiv ((Fin 4 × Fin 2) ⊕ Unit ⊕ (Crossover.Internal × Fin 6))
    { toFun := fun
        | .port s l => .inl (s, l)
        | .center => .inr (.inl ())
        | .copy v i => .inr (.inr (v, i))
      invFun := fun
        | .inl (s, l) => .port s l
        | .inr (.inl ()) => .center
        | .inr (.inr (v, i)) => .copy v i
      left_inv := fun
        | .port _ _ | .center | .copy _ _ => rfl
      right_inv := fun
        | .inl (_, _) | .inr (.inl ()) | .inr (.inr (_, _)) => rfl }

/-- Binary cell coordinates together with a fixed finite ordinary-port or crossover tag. -/
def encVariable : Variable ↪ List Bool :=
  encPair encPoint (encFinEnum ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))

/-- A clause and its binary position and incidence-route data. -/
def encPlacedClause : PlacedClause ↪ List Bool :=
  encPair (encList (encPair encVariable encBool)) (encPair encPoint (encList encRoute))

private theorem computable_intAdd {α : Type} {enc : α ↪ List Bool} {f g : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin)
    (hg : ComputableInPolyTime g enc encIntBin) :
    ComputableInPolyTime (fun a => f a + g a) enc encIntBin :=
  (show ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin by fun_prop).comp (hf.prod hg)

private theorem computable_intLt {α : Type} {enc : α ↪ List Bool} {f g : α → ℤ}
    (hf : ComputableInPolyTime f enc encIntBin)
    (hg : ComputableInPolyTime g enc encIntBin) :
    ComputableInPolyTime (fun a => decide (f a < g a)) enc encBool :=
  (show ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 < p.2))
    (encPair encIntBin encIntBin) encBool by fun_prop).comp (hf.prod hg)

private theorem computable_natCast :
    ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntBin :=
  ComputableInPolyTime.intBin_natCast.comp ComputableInPolyTime.unary_to_binary

attribute [local fun_prop] computable_intAdd computable_intLt computable_natCast

private theorem computable_layoutCenter :
    ComputableInPolyTime Layout.center encUnary encPoint := by
  unfold Layout.center encPoint
  fun_prop

private theorem computable_side :
    ComputableInPolyTime (fun p : Point × Point => side p.1 p.2)
      (encPair encPoint encPoint) (encFinEnum (Fin 4)) := by
  unfold side PlanarCompile.side encPoint
  fun_prop

private theorem computable_cellOrigin :
    ComputableInPolyTime (cellOrigin 120) encPoint encPoint := by
  unfold cellOrigin encPoint
  fun_prop

private theorem computable_center : ComputableInPolyTime center encPoint encPoint := by
  change ComputableInPolyTime (fun p : Point =>
    (240 * p.1 + 120, 240 * p.2 + 120)) encPoint encPoint
  unfold encPoint
  fun_prop

private theorem computable_translate :
    ComputableInPolyTime (fun p : Point × Route => translate p.1 p.2)
      (encPair encPoint encRoute) encRoute := by
  change ComputableInPolyTime (fun p : Point × Route =>
    p.2.map fun q => (q.1 + p.1.1, q.2 + p.1.2)) _ _
  unfold encPoint encRoute
  fun_prop

private theorem computable_pointAdd :
    ComputableInPolyTime (fun p : Point × Point => p.1 + p.2)
      (encPair encPoint encPoint) encPoint := by
  change ComputableInPolyTime (fun p : Point × Point =>
    (p.1.1 + p.2.1, p.1.2 + p.2.2)) _ _
  unfold encPoint
  fun_prop

private theorem computable_dropLast :
    ComputableInPolyTime (List.dropLast (α := Point)) encRoute encRoute := by
  have htake : ComputableInPolyTime (fun p : Route × ℕ => p.1.take p.2)
      (encPair encRoute encUnary) encRoute := by
    unfold encRoute
    fun_prop
  change ComputableInPolyTime (fun r : Route => r.dropLast) encRoute encRoute
  simp only [List.dropLast_eq_take]
  exact htake.comp (ComputableInPolyTime.id'.prod
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_list encPoint) (.const 1)))

attribute [local fun_prop] computable_layoutCenter computable_side computable_cellOrigin
  computable_center computable_translate computable_pointAdd computable_dropLast

private theorem computable_distinctPoints :
    ComputableInPolyTime (fun l : Route => selectDistinct l (List.replicate l.length true))
      encRoute encRoute := by
  have hrep : ComputableInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hlen : ComputableInPolyTime (fun l : Route => l.length) encRoute encUnary :=
    ComputableInPolyTime.length_list encPoint
  unfold encRoute at *
  fun_prop

/-- Ordinary cells are selected from polynomial-size retained paths, without enumerating a
coordinate box or a domain depending on the numeric magnitude of an input label. -/
@[fun_prop]
theorem computableInPolyTime_ordinaryCells :
    ComputableInPolyTime ordinaryCells encCNF encRoute := by
  have hp := PlanarCompile.computableInPolyTime_paths
  have hs := PlanarCompile.computableInPolyTime_crossingSites
  have hd := computable_dropLast.comp (ComputableInPolyTime.snd encCNF encRoute)
  have hl := ComputableInPolyTime.flatMapWithInput
    (f := fun (_ : CNF ℕ) (r : Route) => r.dropLast) (encB := encPoint) hp hd
  have ht : ComputableInPolyTime (fun p : CNF ℕ × Point =>
      decide (p.2 ∉ crossingSites p.1)) (encPair encCNF encPoint) encBool :=
    .decide_not (.decide_mem (hs.comp (.fst _ _)) (.snd _ _))
  have ho : ComputableInPolyTime (fun φ : CNF ℕ =>
      ((paths φ).flatMap List.dropLast).filter fun p => decide (p ∉ crossingSites φ))
      encCNF encRoute := .filterWithInput hl ht
  change ComputableInPolyTime (fun φ => ordinaryCells φ) _ _
  simpa only [ordinaryCells, Function.comp_def] using computable_distinctPoints.comp ho

private theorem computable_port :
    ComputableInPolyTime (fun p : List Point × Point × Fin 4 × Fin 2 =>
      port p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint
        (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2))))) encVariable := by
  have hi : ComputableInPolyTime
      (fun p : Fin 4 × Fin 2 => (Sum.inl p : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))
      (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2)))
      (encFinEnum ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  have ht : ComputableInPolyTime
      (fun p : Fin 4 × Fin 2 =>
        (Sum.inr (PairedCrossover.terminal p.1 p.2) : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))
      (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2)))
      (encFinEnum ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  let input := encPair encRoute (encPair encPoint
    (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2))))
  have hs : ComputableInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => p.1) input encRoute := .fst _ _
  have hp : ComputableInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => p.2.1) input encPoint := by
    unfold input
    fun_prop
  have ha : ComputableInPolyTime
      (fun p : List Point × Point × Fin 4 × Fin 2 => (p.2.2.1, p.2.2.2)) input
      (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2))) := by
    unfold input
    fun_prop
  have hm := ComputableInPolyTime.decide_mem hs hp
  exact hp.prod (hm.ite_decide (ht.comp ha) (hi.comp ha))

attribute [local fun_prop] computable_port

private theorem computable_signal :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      signal p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinEnum (Fin 2)))))
      encVariable := by
  unfold signal
  fun_prop

private theorem computable_variablePosition :
    ComputableInPolyTime variablePosition encVariable encPoint := by
  have hl : ComputableInPolyTime
      (fun v : (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable =>
        v.elim (fun p => PairedPorts.variablePosition p.1 p.2) PairedCrossover.variablePosition)
      (encFinEnum ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) encPoint := .of_finite _
  unfold variablePosition encVariable
  fun_prop

private theorem computable_boundary :
    ComputableInPolyTime (fun p : Point × Fin 4 × Fin 2 => boundary p.1 p.2.1 p.2.2)
      (encPair encPoint (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2)))) encPoint := by
  have hb : ComputableInPolyTime
      (fun p : Fin 4 × Fin 2 => PairedPorts.boundaryPort p.1 p.2)
      (encPair (encFinEnum (Fin 4)) (encFinEnum (Fin 2))) encPoint := .of_finite _
  unfold boundary
  fun_prop

attribute [local fun_prop] computable_signal computable_variablePosition computable_boundary

private theorem computable_access :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      access p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinEnum (Fin 2))))) encRoute := by
  unfold access encRoute
  fun_prop

attribute [local fun_prop] computable_access

private theorem computable_link :
    ComputableInPolyTime (fun p : List Point × Point × Point × Fin 2 =>
      link p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encRoute (encPair encPoint (encPair encPoint (encFinEnum (Fin 2)))))
      encPlacedClause := by
  dsimp only [link]
  unfold encPlacedClause
  fun_prop

attribute [local fun_prop] computable_link

private theorem computable_links :
    ComputableInPolyTime (fun p : List Point × Route => links p.1 p.2)
      (encPair encRoute encRoute) (encList encPlacedClause) := by
  have hzip : ComputableInPolyTime (fun p : Route × Route => p.1.zip p.2)
      (encPair encRoute encRoute) (encList (encPair encPoint encPoint)) := by
    unfold encRoute
    fun_prop
  have htail : ComputableInPolyTime (List.tail (α := Point)) encRoute encRoute := by
    unfold encRoute
    fun_prop
  have hcons : ComputableInPolyTime (List.consecutivePairs (α := Point)) encRoute
      (encList (encPair encPoint encPoint)) := by
    unfold List.consecutivePairs
    exact hzip.comp (ComputableInPolyTime.id'.prod htail)
  unfold links
  exact ComputableInPolyTime.flatMapWithInput
    (hcons.comp (computable_dropLast.comp (ComputableInPolyTime.snd _ _))) (by fun_prop)

private theorem computable_lastLiteral :
    ComputableInPolyTime (fun p : List Point × Route × Bool => lastLiteral p.1 p.2.1 p.2.2)
      (encPair encRoute (encPair encRoute encBool))
      (encPair (encPair encVariable encBool) encRoute) := by
  have hl : ComputableInPolyTime PairedPorts.spokeLane
      (encFinEnum (Fin 4)) (encFinEnum (Fin 2)) := .of_finite _
  have he : ComputableInPolyTime PairedPorts.spokeElbow
      (encFinEnum (Fin 4)) encPoint := .of_finite _
  have hr : ComputableInPolyTime (fun p : List Point × Route × Bool => p.2.1)
      (encPair encRoute (encPair encRoute encBool)) encRoute := by fun_prop
  have hrlen : ComputableInPolyTime (fun p : List Point × Route × Bool => p.2.1.length)
      (encPair encRoute (encPair encRoute encBool)) encUnary :=
    (ComputableInPolyTime.length_list encPoint).comp hr
  dsimp only [lastLiteral]
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_head?_reverse, ← List.headD_eq_head?_getD]
  unfold encRoute at *
  fun_prop

attribute [local fun_prop] computable_links computable_lastLiteral

private theorem computable_originalClauses :
    ComputableInPolyTime (fun p : CNF ℕ × List Point => originalClauses p.1 p.2)
      (encPair encCNF encRoute) (encList encPlacedClause) := by
  have hp := PlanarCompile.computableInPolyTime_occurrencePath
  have hdvlen : ComputableInPolyTime (fun p : CNF ℕ × List Point => p.1.distinctVars.length)
      (encPair encCNF encRoute) encUnary :=
    (ComputableInPolyTime.length_list encNat).comp
      ((CNF.computableInPolyTime_distinctVars encNat).comp
        (ComputableInPolyTime.fst encCNF encRoute))
  dsimp only [originalClauses]
  unfold encPlacedClause encCNF Cslib.Logic.PL.encOccurrence at *
  fun_prop

private theorem computable_templateClauses {A : Type} [FinEnum A]
    (tag : A → (Fin 4 × Fin 2) ⊕ PairedCrossover.Variable) (ψ : CNF A)
    (clausePositions : List Point) (incidenceRoutes : List (ℕ × A × Route)) :
    ComputableInPolyTime (fun p : Point => ψ.zipIdx.map fun (c, i) =>
      (c.relabel (fun v => (p, tag v)),
        cellOrigin 120 p + clausePositions.getD i (0, 0),
        (incidenceRoutes.filter fun e => e.1 == i).map fun e =>
          translate (cellOrigin 120 p) e.2.2)) encPoint (encList encPlacedClause) := by
  let rowEncoding := encPair (encList (encPair (encFinEnum A) encBool)) encUnary
  let routeEntry := encPair encUnary (encPair (encFinEnum A) encRoute)
  have htag : ComputableInPolyTime tag (encFinEnum A)
      (encFinEnum ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable)) := .of_finite _
  have hbody : ComputableInPolyTime (fun p : Point × (Clause A × ℕ) =>
      (p.2.1.relabel (fun v => (p.1, tag v)),
        cellOrigin 120 p.1 + clausePositions.getD p.2.2 (0, 0),
        (incidenceRoutes.filter fun e => e.1 == p.2.2).map fun e =>
          translate (cellOrigin 120 p.1) e.2.2))
      (encPair encPoint rowEncoding) encPlacedClause := by
    have hpositions : ComputableInPolyTime
        (fun _ : Point × (Clause A × ℕ) => clausePositions)
        (encPair encPoint rowEncoding) encRoute := .const _
    have hposition : ComputableInPolyTime
        (fun p : Point × (Clause A × ℕ) => clausePositions.getD p.2.2 (0, 0))
        (encPair encPoint rowEncoding) encPoint := by
      unfold rowEncoding encRoute at *
      fun_prop
    have hroutes : ComputableInPolyTime
        (fun _ : Point × (Clause A × ℕ) => incidenceRoutes)
        (encPair encPoint rowEncoding) (encList routeEntry) := .const _
    have hfroutes : ComputableInPolyTime
        (fun p : Point × (Clause A × ℕ) => incidenceRoutes.filter fun e => e.1 == p.2.2)
        (encPair encPoint rowEncoding) (encList routeEntry) :=
      ComputableInPolyTime.filterWithInput hroutes (by
        unfold rowEncoding routeEntry
        fun_prop)
    unfold rowEncoding routeEntry encPlacedClause Clause.relabel encVariable Prod.map at *
    fun_prop
  have hlist : ComputableInPolyTime (fun _ : Point => ψ.zipIdx)
      encPoint (encList rowEncoding) := .const _
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
  have hs := PlanarCompile.computableInPolyTime_crossingSites
  have hp := PlanarCompile.computableInPolyTime_occurrencePath
  have ho := Cslib.Logic.PL.computableInPolyTime_occurrences encNat
  change ComputableInPolyTime (fun φ => placedClauses φ) _ _
  dsimp only [placedClauses]
  unfold encCNF Cslib.Logic.PL.encOccurrence at *
  fun_prop

/-- Projecting the actual records computes the structured output formula. -/
@[fun_prop]
theorem computableInPolyTime_rawFormula :
    ComputableInPolyTime rawFormula encCNF (encList (encList (encPair encVariable encBool))) := by
  have hp := computableInPolyTime_placedClauses
  unfold rawFormula encPlacedClause at *
  fun_prop

/-- The actual compact formula compiler is native polynomial-time under binary CNF encodings.
Compact ranks are computed as unary counters and then encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_formula : ComputableInPolyTime formula encCNF encCNF := by
  have hu := (CNF.isPolyTime_compact encVariable).comp computableInPolyTime_rawFormula
  have hi : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat :=
    ComputableInPolyTime.unary_to_binary
  have hr := (CNF.computableInPolyTime_relabel hi).comp hu
  have he (ψ : CNF ℕ) : ψ.relabel (fun n : ℕ => n) = ψ := CNF.relabel_id ψ
  change ComputableInPolyTime (fun φ => (rawFormula φ).compact) _ _
  simpa only [Function.comp_def, he, encCNF] using hr

/-- All actual output vertex positions are computed in polynomial time with binary coordinates. -/
@[fun_prop]
theorem computableInPolyTime_positions : ComputableInPolyTime positions encCNF encRoute := by
  have hv := (CNF.computableInPolyTime_distinctVars encVariable).comp
    computableInPolyTime_rawFormula
  have hp := computableInPolyTime_placedClauses
  change ComputableInPolyTime (fun φ => positions φ) _ _
  dsimp only [positions]
  unfold encPlacedClause encRoute at *
  fun_prop

/-- All actual clause-to-variable incidence routes are computed in polynomial time with binary
coordinates. -/
@[fun_prop]
theorem computableInPolyTime_routes :
    ComputableInPolyTime routes encCNF (encList encRoute) := by
  have hp := computableInPolyTime_placedClauses
  unfold routes encPlacedClause at *
  fun_prop

end Cslib.Complexity.SAT.ParsimoniousPlanar
