/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSATThree
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Syntax
public import Complexity.Computability.Complexity.Problems.ThreeSATThree.Size
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PolyTime
import Complexity.Computability.Complexity.Problems.SAT.Planar.Completeness
import Complexity.Computability.Complexity.Problems.SAT.Planar.Occurrence
import Complexity.Computability.Complexity.Problems.SAT.Planar.Geometry
import Complexity.Computability.Complexity.Problems.SAT.Planar.Size
import Complexity.Computability.Complexity.Problems.SAT.Planar.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


import Diag1155.Measure
/-!
# Planar 3SAT with three literal occurrences per variable

Clauses have width at most three, including binary clauses, and each variable has at most
three literal occurrences. Planarity is witnessed by a finite integer orthogonal incidence
drawing: routes are simple, avoid nonincident vertices, and intersect only at shared endpoints,
with all contacts interpreted on full real segments. Parallel literal incidences are retained.

`DrawnPlanarThreeSATThree` supplies the drawing as part of the input. `PlanarThreeSATThree`
requires its existence. The total compiler rejects inputs outside the syntactic restrictions
by returning one empty clause and a one-vertex drawing.

## Main definitions

* `PlanarThreeSATThree`, `DrawnPlanarThreeSATThree`: formula and supplied-drawing problems.
* `toDrawnPlanarThreeSATThree`, `toPlanarThreeSATThree`: total finite compilers.

## Main results

* `PlanarThreeSATThree_npHard`, `DrawnPlanarThreeSATThree_npHard`: NP-hardness with an
  existential or supplied integer orthogonal incidence drawing.
* `computableInPolyTime_toDrawnPlanarThreeSATThree`,
  `computableInPolyTime_toPlanarThreeSATThree`: native polynomial-time computation.
* `satisfiable_toPlanarThreeSAT_iff`: total correctness after occurrence splitting.
* `toDrawnPlanarThreeSAT_fits`, `toDrawnPlanarThreeSAT_costs`: explicit linear grid sides
  and quadratic formula, incidence-route, segment and Manhattan wire costs, measured against
  the original formula's clause and literal counts.

## References

The finite tiling construction is original; the fixed crossover is credited in `Crossover`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Satisfiable width-three, occurrence-three formulas whose actual incidence graph admits an
integer orthogonal drawing with continuous endpoint-only contacts. -/
def PlanarThreeSATThree : Set (CNF ℕ) :=
  {φ | φ ∈ ThreeSATThree ∧ ∃ d, Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d}

/-- The same problem with finite vertex positions and incidence routes supplied explicitly. -/
def DrawnPlanarThreeSATThree : Set (CNF ℕ × Graph.OrthogonalDrawing) :=
  {x | x.1 ∈ ThreeSATThree ∧ Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph x.1) x.2}

/-- A total compiler, including an explicit drawing. Invalid syntactic inputs produce the
unsatisfiable empty clause with its isolated clause vertex. -/
def toDrawnPlanarThreeSATThree (φ : CNF ℕ) : CNF ℕ × Graph.OrthogonalDrawing :=
  if ThreeSATThree.syntaxCheck φ then
    (SAT.PlanarCompile.formula φ, SAT.PlanarCompile.positions φ, SAT.PlanarCompile.routes φ)
  else ([[]], [(0, 0)], [])

/-- Forget the drawing emitted by the total compiler. -/
def toPlanarThreeSATThree (φ : CNF ℕ) : CNF ℕ := (toDrawnPlanarThreeSATThree φ).1

private theorem rejection_drawing : Graph.IsPlanarOrthogonalDrawing
    (SAT.incidenceGraph ([[]] : CNF ℕ)) ([(0, 0)], []) := by
  refine ⟨rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [SAT.incidenceGraph, Cslib.Logic.PL.occurrences]

attribute [local fun_prop] ComputableInPolyTime.tidy

/-- The formula and explicit binary-coordinate drawing are computed in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toDrawnPlanarThreeSATThree :
    ComputableInPolyTime toDrawnPlanarThreeSATThree encCNF
      (encPair encCNF Graph.encOrthogonalDrawing) := by
  refine .of_tidy ?_
  change ComputableTidilyInPolyTime (fun φ => toDrawnPlanarThreeSATThree φ) _ _
  dsimp only [toDrawnPlanarThreeSATThree]
  unfold Graph.encOrthogonalDrawing
  fun_prop

/-- Dropping the computed drawing gives a native polynomial-time formula compiler. -/
@[fun_prop]
theorem computableInPolyTime_toPlanarThreeSATThree :
    ComputableInPolyTime toPlanarThreeSATThree encCNF encCNF :=
  (ComputableInPolyTime.fst encCNF Graph.encOrthogonalDrawing).comp
    computableInPolyTime_toDrawnPlanarThreeSATThree

/-- The total formula output has width at most three, including on rejected inputs. -/
theorem width_toPlanarThreeSATThree (φ : CNF ℕ) :
    ∀ c ∈ toPlanarThreeSATThree φ, c.length ≤ 3 := by
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · simpa only [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, ↓reduceIte] using
      SAT.PlanarCompile.width_formula ((ThreeSATThree.syntaxCheck_iff φ).1 hg).1
  · simp [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg]

/-- The actual total output has at most three literal positions for every variable. -/
theorem count_vars_toPlanarThreeSATThree (φ : CNF ℕ) :
    ∀ v, (toPlanarThreeSATThree φ).vars.count v ≤ 3 := by
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · have hs := (ThreeSATThree.syntaxCheck_iff φ).1 hg
    simpa only [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, ↓reduceIte] using
      SAT.PlanarCompile.count_vars_formula_le_three hs.1 hs.2
  · simp [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, CNF.vars]

/-- The total output is satisfiable exactly on the source 3SAT-3 language. -/
theorem satisfiable_toPlanarThreeSATThree_iff (φ : CNF ℕ) :
    (toPlanarThreeSATThree φ).Satisfiable ↔ φ ∈ ThreeSATThree := by
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · have hs := (ThreeSATThree.syntaxCheck_iff φ).1 hg
    have he : (toPlanarThreeSATThree φ).Satisfiable ↔ φ.Satisfiable := by
      simpa only [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, ↓reduceIte] using
        SAT.PlanarCompile.satisfiable_formula_iff hs.1 hs.2
    exact he.trans ⟨fun h => ⟨hs.1, hs.2, h⟩, fun h => h.2.2⟩
  · have hn : φ ∉ ThreeSATThree := by
      intro h
      have ht := (ThreeSATThree.syntaxCheck_iff φ).2 ⟨h.1, h.2.1⟩
      exact hg ht
    simp [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, CNF.Satisfiable, hn]

/-- Every total output, including the rejection branch, has the claimed actual drawing. -/
theorem isPlanarOrthogonalDrawing_toDrawnPlanarThreeSATThree (φ : CNF ℕ) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (toPlanarThreeSATThree φ))
      (toDrawnPlanarThreeSATThree φ).2 := by
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · have hs := (ThreeSATThree.syntaxCheck_iff φ).1 hg
    simpa only [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg, ↓reduceIte] using
      SAT.PlanarCompile.isPlanarOrthogonalDrawing hs.1 hs.2
  · simpa [toPlanarThreeSATThree, toDrawnPlanarThreeSATThree, hg] using
      rejection_drawing

/-- Correctness for the supplied-drawing target, on every source formula. -/
theorem mem_DrawnPlanarThreeSATThree_toDrawnPlanarThreeSATThree_iff (φ : CNF ℕ) :
    toDrawnPlanarThreeSATThree φ ∈ DrawnPlanarThreeSATThree ↔ φ ∈ ThreeSATThree := by
  constructor
  · intro h
    exact (satisfiable_toPlanarThreeSATThree_iff φ).1 h.1.2.2
  · intro h
    exact ⟨⟨width_toPlanarThreeSATThree φ, count_vars_toPlanarThreeSATThree φ,
      (satisfiable_toPlanarThreeSATThree_iff φ).2 h⟩,
        isPlanarOrthogonalDrawing_toDrawnPlanarThreeSATThree φ⟩

/-- Correctness when the target problem requires the drawing's existence. -/
theorem mem_PlanarThreeSATThree_toPlanarThreeSATThree_iff (φ : CNF ℕ) :
    toPlanarThreeSATThree φ ∈ PlanarThreeSATThree ↔ φ ∈ ThreeSATThree := by
  constructor
  · intro h
    exact (satisfiable_toPlanarThreeSATThree_iff φ).1 h.1.2.2
  · intro h
    exact ⟨⟨width_toPlanarThreeSATThree φ, count_vars_toPlanarThreeSATThree φ,
      (satisfiable_toPlanarThreeSATThree_iff φ).2 h⟩, (toDrawnPlanarThreeSATThree φ).2,
        isPlanarOrthogonalDrawing_toDrawnPlanarThreeSATThree φ⟩

/-- Native polynomial-time reduction to a formula with its actual orthogonal drawing. -/
theorem polyTimeReducible_ThreeSATThree_DrawnPlanarThreeSATThree :
    PolyTimeReducible encCNF (encPair encCNF Graph.encOrthogonalDrawing)
      ThreeSATThree DrawnPlanarThreeSATThree :=
  ⟨toDrawnPlanarThreeSATThree, computableInPolyTime_toDrawnPlanarThreeSATThree,
    fun φ => (mem_DrawnPlanarThreeSATThree_toDrawnPlanarThreeSATThree_iff φ).symm⟩

/-- Native polynomial-time reduction to a formula admitting an orthogonal drawing. -/
theorem polyTimeReducible_ThreeSATThree_PlanarThreeSATThree :
    PolyTimeReducible encCNF encCNF ThreeSATThree PlanarThreeSATThree :=
  ⟨toPlanarThreeSATThree, computableInPolyTime_toPlanarThreeSATThree,
    fun φ => (mem_PlanarThreeSATThree_toPlanarThreeSATThree_iff φ).symm⟩

/-- Orthogonal planar 3SAT-3 with the drawing supplied is NP-hard under binary encodings. -/
theorem DrawnPlanarThreeSATThree_npHard :
    NPHard (encPair encCNF Graph.encOrthogonalDrawing) DrawnPlanarThreeSATThree :=
  ThreeSATThree_npHard.trans polyTimeReducible_ThreeSATThree_DrawnPlanarThreeSATThree

/-- Satisfiability of occurrence-three, width-three formulas admitting an integer orthogonal
incidence drawing is NP-hard under the ordinary binary formula encoding. -/
theorem PlanarThreeSATThree_npHard : NPHard encCNF PlanarThreeSATThree :=
  ThreeSATThree_npHard.trans polyTimeReducible_ThreeSATThree_PlanarThreeSATThree

/-- Explicit linear grid sides for the total supplied-drawing compiler. -/
theorem toDrawnPlanarThreeSATThree_fits (φ : CNF ℕ) :
    Graph.drawingFits (toDrawnPlanarThreeSATThree φ).2
      (1920 * (φ.numVars + φ.length + φ.vars.length + 1))
      (1920 * (φ.numVars + φ.length + φ.vars.length + 1)) := by
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · simpa only [toDrawnPlanarThreeSATThree, hg, ↓reduceIte] using
      Graph.drawingFits_mono (SAT.PlanarCompile.drawing_fits φ)
        (SAT.PlanarCompile.gridWidth_le φ) (SAT.PlanarCompile.gridHeight_le φ)
  · have hn : (0 : ℤ) ≤ φ.numVars + φ.length + φ.vars.length + 1 := by positivity
    simpa [toDrawnPlanarThreeSATThree, hg, Graph.drawingFits] using hn

/-- Explicit quadratic formula, incidence-route, segment and Manhattan wire bounds. -/
theorem toDrawnPlanarThreeSATThree_costs (φ : CNF ℕ) :
    let out := toDrawnPlanarThreeSATThree φ
    let s := φ.numVars + φ.length + φ.vars.length + 1
    out.1.length ≤ 600 * s ^ 2 ∧ out.1.vars.length ≤ 1210 * s ^ 2 ∧
      out.2.2.length ≤ 1210 * s ^ 2 ∧ Graph.drawingSegmentCount out.2 ≤ 23000 * s ^ 2 ∧
        Graph.drawingWireLength out.2 ≤ 300000 * s ^ 2 := by
  dsimp only
  by_cases hg : ThreeSATThree.syntaxCheck φ = true
  · simp only [toDrawnPlanarThreeSATThree, hg, ↓reduceIte]
    exact ⟨SAT.PlanarCompile.length_formula_le φ, SAT.PlanarCompile.length_vars_formula_le φ,
      SAT.PlanarCompile.routes_length_le φ, SAT.PlanarCompile.drawingSegmentCount_le φ,
      SAT.PlanarCompile.drawingWireLength_le φ⟩
  · have hsize : 1 ≤ φ.numVars + φ.length + φ.vars.length + 1 := by omega
    have hvars : CNF.vars ([[]] : CNF ℕ) = [] := rfl
    simp only [toDrawnPlanarThreeSATThree, hg]
    norm_num [hvars, Graph.drawingSegmentCount, Graph.drawingWireLength]
    nlinarith

/-- The original 3SAT input first passes through the linear occurrence splitter. -/
def toDrawnPlanarThreeSAT (φ : CNF ℕ) : CNF ℕ × Graph.OrthogonalDrawing :=
  toDrawnPlanarThreeSATThree (toThreeSATThree φ)

/-- Formula projection of the total compiler from original 3SAT instances. -/
def toPlanarThreeSAT (φ : CNF ℕ) : CNF ℕ := (toDrawnPlanarThreeSAT φ).1

/-- The composed compiler retains native polynomial time under binary input labels. -/
@[fun_prop]
theorem computableInPolyTime_toDrawnPlanarThreeSAT :
    ComputableInPolyTime toDrawnPlanarThreeSAT encCNF
      (encPair encCNF Graph.encOrthogonalDrawing) :=
  computableInPolyTime_toDrawnPlanarThreeSATThree.comp computableInPolyTime_toThreeSATThree

/-- Formula output from original 3SAT is computed in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toPlanarThreeSAT :
    ComputableInPolyTime toPlanarThreeSAT encCNF encCNF :=
  (ComputableInPolyTime.fst encCNF Graph.encOrthogonalDrawing).comp
    computableInPolyTime_toDrawnPlanarThreeSAT

/-- The total output is satisfiable exactly when the original input belongs to 3SAT. -/
theorem satisfiable_toPlanarThreeSAT_iff (φ : CNF ℕ) :
    (toPlanarThreeSAT φ).Satisfiable ↔ φ ∈ ThreeSAT :=
  (satisfiable_toPlanarThreeSATThree_iff (toThreeSATThree φ)).trans
    (mem_ThreeSATThree_toThreeSATThree_iff φ)

/-- The composed output has its actual orthogonal drawing for every original CNF input. -/
theorem isPlanarOrthogonalDrawing_toDrawnPlanarThreeSAT (φ : CNF ℕ) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (toPlanarThreeSAT φ))
      (toDrawnPlanarThreeSAT φ).2 :=
  isPlanarOrthogonalDrawing_toDrawnPlanarThreeSATThree (toThreeSATThree φ)

/-- The original 3SAT language reduces to the supplied-drawing target by the composed compiler. -/
theorem mem_DrawnPlanarThreeSATThree_toDrawnPlanarThreeSAT_iff (φ : CNF ℕ) :
    toDrawnPlanarThreeSAT φ ∈ DrawnPlanarThreeSATThree ↔ φ ∈ ThreeSAT :=
  (mem_DrawnPlanarThreeSATThree_toDrawnPlanarThreeSATThree_iff (toThreeSATThree φ)).trans
    (mem_ThreeSATThree_toThreeSATThree_iff φ)

/-- The composed formula output belongs to the existential-drawing target exactly on 3SAT. -/
theorem mem_PlanarThreeSATThree_toPlanarThreeSAT_iff (φ : CNF ℕ) :
    toPlanarThreeSAT φ ∈ PlanarThreeSATThree ↔ φ ∈ ThreeSAT :=
  (mem_PlanarThreeSATThree_toPlanarThreeSATThree_iff (toThreeSATThree φ)).trans
    (mem_ThreeSATThree_toThreeSATThree_iff φ)

/-- Linear grid sides are measured against the original formula's clause/literal size. -/
theorem toDrawnPlanarThreeSAT_fits (φ : CNF ℕ) :
    Graph.drawingFits (toDrawnPlanarThreeSAT φ).2
      (13440 * (φ.length + φ.vars.length + 1))
      (13440 * (φ.length + φ.vars.length + 1)) := by
  have hb := size_toThreeSATThree_le φ
  apply Graph.drawingFits_mono (toDrawnPlanarThreeSATThree_fits (toThreeSATThree φ)) <;>
    nlinarith

/-- All output formula and drawing costs are quadratic in the original clause/literal size. -/
theorem toDrawnPlanarThreeSAT_costs (φ : CNF ℕ) :
    let out := toDrawnPlanarThreeSAT φ
    let s := φ.length + φ.vars.length + 1
    out.1.length ≤ 29400 * s ^ 2 ∧ out.1.vars.length ≤ 59290 * s ^ 2 ∧
      out.2.2.length ≤ 59290 * s ^ 2 ∧ Graph.drawingSegmentCount out.2 ≤ 1127000 * s ^ 2 ∧
        Graph.drawingWireLength out.2 ≤ 14700000 * s ^ 2 := by
  have hb := size_toThreeSATThree_le φ
  have hs : ((toThreeSATThree φ).numVars + (toThreeSATThree φ).length +
      (toThreeSATThree φ).vars.length + 1) ^ 2 ≤
      (7 * (φ.length + φ.vars.length + 1)) ^ 2 := Nat.pow_le_pow_left hb 2
  have hc := toDrawnPlanarThreeSATThree_costs (toThreeSATThree φ)
  dsimp only [toDrawnPlanarThreeSAT] at *
  exact ⟨by nlinarith [hc.1], by nlinarith [hc.2.1], by nlinarith [hc.2.2.1],
    by nlinarith [hc.2.2.2.1], by nlinarith [hc.2.2.2.2]⟩

end Cslib.Complexity
