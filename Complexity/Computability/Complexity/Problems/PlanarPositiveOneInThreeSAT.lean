/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.PlanarThreeSATThree
public import Complexity.Computability.Complexity.Problems.OneInThreeSAT.Reduction
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingValid
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingFits
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingCosts
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingPolyTime
import Complexity.Logics.Propositional.CNF.ExactOne.PolyTime
import Mathlib.Tactic.Linarith

/-!
# Positive exact-one SAT after parsimonious planarization

The compiler first uses the existing parsimonious planar 3SAT-3 construction and then the
constant-factor positive exact-three replacement. The emitted integer orthogonal drawing has
the actual output incidence graph. All route contacts concern full real supports.

Relative to a supplied planar drawing, the new replacement changes grid sides and all drawing
costs by fixed constants. Relative to the original 3SAT instance, the full composition has linear
grid sides and quadratic formula, vertex, route, segment and Manhattan wire costs. Models are
counted only on occurring variables, and every ordinary source model has a unique extension.

## Main definitions

* `PlanarPositiveOneInExactThreeSATThree`: the existential orthogonal-drawing language.
* `DrawnPlanarPositiveOneInExactThreeSATThree`: the supplied-drawing language.
* `SharpPlanarPositiveOneInExactThreeSATThree`, `SharpDrawnPlanarPositiveOneInExactThreeSATThree`:
  the positive exact-one model counts guarded by the existence, respectively the validity, of a
  planar orthogonal incidence drawing.
* `toPlanarPositiveOneInExactThreeSATThree`, `toDrawnPlanarPositiveOneInExactThreeSATThree`:
  the actual formula and supplied-drawing compilers.

## Main results

* `oneModelCount_toPlanarPositiveOneInExactThreeSATThree`: preservation of model counts.
* `parsimoniousReducible_SharpThreeSAT_SharpPlanarPositiveOneInExactThreeSATThree`,
  `parsimoniousReducible_SharpThreeSAT_SharpDrawnPlanarPositiveOneInExactThreeSATThree`: native
  parsimonious reductions from `#3SAT` to the planarity-guarded counts.
* `PlanarPositiveOneInExactThreeSATThree_npHard`, `PlanarPositiveOneInThreeSATThree_npHard`,
  `DrawnPlanarPositiveOneInExactThreeSATThree_npHard`: NP-hardness of the planar positive
  variants, including the version with the actual drawing supplied.
* `computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree`: native polynomial-time
  computation of both the actual formula and its drawing.
* `toDrawnPlanarPositiveOneInExactThreeSATThree_fits`,
  `toDrawnPlanarPositiveOneInExactThreeSATThree_costs`: explicit linear grid sides and
  quadratic formula and drawing bounds.

## References

The local clause gadgets are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8].
The quantitative composition is original.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Positive exact-three, occurrence-three exact-one formulas with an integer orthogonal
incidence drawing whose full real segments meet only at common incident endpoints. -/
def PlanarPositiveOneInExactThreeSATThree : Set (CNF ℕ) :=
  {φ | φ ∈ PositiveOneInExactThreeSATThree ∧
    ∃ d, Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d}

/-- The same language with its finite integer incidence drawing supplied as input. -/
def DrawnPlanarPositiveOneInExactThreeSATThree : Set (CNF ℕ × Graph.OrthogonalDrawing) :=
  {x | x.1 ∈ PositiveOneInExactThreeSATThree ∧
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph x.1) x.2}

/-- The width-at-most-three positive planar variant, without requiring ternary clauses. -/
def PlanarPositiveOneInThreeSATThree : Set (CNF ℕ) :=
  {φ | φ ∈ PositiveOneInThreeSATThree ∧
    ∃ d, Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d}

open Classical in
/-- Count positive exact-three, occurrence-three exact-one models of formulas that have a planar
orthogonal incidence drawing; return zero otherwise. -/
noncomputable def SharpPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) : ℕ :=
  if ∃ d, Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d then
    SharpPositiveOneInExactThreeSATThree φ else 0

open Classical in
/-- Count positive exact-three, occurrence-three exact-one models when the supplied drawing is a
planar orthogonal incidence drawing of the formula; return zero otherwise. -/
noncomputable def SharpDrawnPlanarPositiveOneInExactThreeSATThree
    (x : CNF ℕ × Graph.OrthogonalDrawing) : ℕ :=
  if Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph x.1) x.2 then
    SharpPositiveOneInExactThreeSATThree x.1 else 0

/-- Apply only the constant-factor positive compiler after the existing planarization. -/
def toPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) : CNF ℕ :=
  CNF.PositiveExactOneCompile.formula (toPlanarThreeSAT φ)

/-- Compute the actual positive incidence drawing by replacing each planar source clause box. -/
def toDrawnPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    CNF ℕ × Graph.OrthogonalDrawing :=
  (toPlanarPositiveOneInExactThreeSATThree φ,
    SAT.ExactOne.positiveDrawing (toPlanarThreeSAT φ) (toDrawnPlanarThreeSAT φ).2)

/-- The positive formula is produced in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree :
    ComputableInPolyTime toPlanarPositiveOneInExactThreeSATThree encCNF encCNF :=
  (CNF.PositiveExactOneCompile.computableInPolyTime_formula encNat).comp
    computableInPolyTime_toPlanarThreeSAT

/-- Every output clause has three distinct variables. -/
theorem exactClauses_toPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    ∀ c ∈ toPlanarPositiveOneInExactThreeSATThree φ,
      c.length = 3 ∧ (c.map Prod.fst).Nodup :=
  fun c hc => ⟨CNF.PositiveExactOneCompile.width_formula _ c hc,
    CNF.PositiveExactOneCompile.nodup_formula _ c hc⟩

/-- There are no negative output literals. -/
theorem positive_toPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    OneSAT.positiveCheck (toPlanarPositiveOneInExactThreeSATThree φ) = true :=
  (OneSAT.positiveCheck_iff _).mpr (CNF.PositiveExactOneCompile.positive_formula _)

/-- The local replacements retain the planar compiler's three-occurrence restriction. -/
theorem count_vars_toPlanarPositiveOneInExactThreeSATThree_le (φ : CNF ℕ) :
    ∀ v, (toPlanarPositiveOneInExactThreeSATThree φ).vars.count v ≤ 3 :=
  CNF.PositiveExactOneCompile.count_vars_formula_le _
    (width_toPlanarThreeSATThree (toThreeSATThree φ))
    (count_vars_toPlanarThreeSATThree (toThreeSATThree φ))

/-- Counts on occurring variables agree with the original ordinary 3SAT instance. -/
theorem oneModelCount_toPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ)
    (hw : ∀ c ∈ φ, c.length ≤ 3) :
    (toPlanarPositiveOneInExactThreeSATThree φ).oneModelCount = φ.modelCount :=
  (CNF.PositiveExactOneCompile.oneModelCount_formula _
    (width_toPlanarThreeSATThree (toThreeSATThree φ))).trans (modelCount_toPlanarThreeSAT φ hw)

/-- Total correctness of the formula compiler, including ordinary syntax rejection. -/
theorem oneSatisfiable_toPlanarPositiveOneInExactThreeSATThree_iff (φ : CNF ℕ) :
    (toPlanarPositiveOneInExactThreeSATThree φ).OneSatisfiable ↔ φ ∈ ThreeSAT :=
  (CNF.PositiveExactOneCompile.oneSatisfiable_formula _
    (width_toPlanarThreeSATThree (toThreeSATThree φ))).trans
      (satisfiable_toPlanarThreeSAT_iff φ)

/-- The new constant-factor replacements retain quadratic growth relative to original 3SAT. -/
theorem size_toPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    let s := φ.length + φ.vars.length + 1
    (toPlanarPositiveOneInExactThreeSATThree φ).length ≤ 41405000 * s ^ 2 ∧
      (toPlanarPositiveOneInExactThreeSATThree φ).vars.length ≤ 124215000 * s ^ 2 := by
  have hs := (toDrawnPlanarThreeSAT_costs φ).1
  have hc := CNF.PositiveExactOneCompile.length_formula_le (toPlanarThreeSAT φ)
  have hl := CNF.PositiveExactOneCompile.length_vars_formula_le (toPlanarThreeSAT φ)
  dsimp only [toPlanarThreeSAT] at hc hl
  dsimp only [toPlanarPositiveOneInExactThreeSATThree, toPlanarThreeSAT]
  constructor <;> nlinarith

/-- Every total output has its actual positive exact-one incidence drawing. -/
theorem isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree (φ : CNF ℕ) :
    Graph.IsPlanarOrthogonalDrawing
      (SAT.incidenceGraph (toPlanarPositiveOneInExactThreeSATThree φ))
      (toDrawnPlanarPositiveOneInExactThreeSATThree φ).2 :=
  SAT.ExactOne.positiveDrawing_isPlanarOrthogonalDrawing
    (isPlanarOrthogonalDrawing_toDrawnPlanarThreeSAT φ)

/-- Membership in the strongest positive target agrees exactly with original 3SAT. -/
theorem mem_PositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree_iff
    (φ : CNF ℕ) :
    toPlanarPositiveOneInExactThreeSATThree φ ∈ PositiveOneInExactThreeSATThree ↔
      φ ∈ ThreeSAT := by
  change (_ ∧ _ ∧ _) ∧ _ ↔ _
  rw [and_iff_right (exactClauses_toPlanarPositiveOneInExactThreeSATThree φ),
    and_iff_right (positive_toPlanarPositiveOneInExactThreeSATThree φ),
    and_iff_left (count_vars_toPlanarPositiveOneInExactThreeSATThree_le φ)]
  exact oneSatisfiable_toPlanarPositiveOneInExactThreeSATThree_iff φ

/-- Correctness for the target with its actual drawing supplied. -/
theorem mem_DrawnPlanarPositiveOneInExactThreeSATThree_toDrawn_iff (φ : CNF ℕ) :
    toDrawnPlanarPositiveOneInExactThreeSATThree φ ∈ DrawnPlanarPositiveOneInExactThreeSATThree ↔
      φ ∈ ThreeSAT := by
  change toPlanarPositiveOneInExactThreeSATThree φ ∈ PositiveOneInExactThreeSATThree ∧
    Graph.IsPlanarOrthogonalDrawing
      (SAT.incidenceGraph (toPlanarPositiveOneInExactThreeSATThree φ))
      (toDrawnPlanarPositiveOneInExactThreeSATThree φ).2 ↔ _
  rw [and_iff_left
    (isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ)]
  exact mem_PositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree_iff φ

/-- Correctness when the positive target requires the drawing's existence. -/
theorem mem_PlanarPositiveOneInExactThreeSATThree_toPlanar_iff (φ : CNF ℕ) :
    toPlanarPositiveOneInExactThreeSATThree φ ∈ PlanarPositiveOneInExactThreeSATThree ↔
      φ ∈ ThreeSAT := by
  constructor
  · intro h
    exact
      (mem_PositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree_iff φ).mp h.1
  · intro h
    refine ⟨?_,
      (toDrawnPlanarPositiveOneInExactThreeSATThree φ).2,
      isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ⟩
    exact
      (mem_PositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree_iff φ).mpr h

/-- Positive exact-three, occurrence-three planar exact-one SAT is NP-hard. -/
theorem PlanarPositiveOneInExactThreeSATThree_npHard :
    NPHard encCNF PlanarPositiveOneInExactThreeSATThree :=
  ThreeSAT_npHard.trans ⟨toPlanarPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree,
    fun φ => (mem_PlanarPositiveOneInExactThreeSATThree_toPlanar_iff φ).symm⟩

/-- The same compiler proves the positive width-three planar variant NP-hard. -/
theorem mem_PlanarPositiveOneInThreeSATThree_toPlanar_iff (φ : CNF ℕ) :
    toPlanarPositiveOneInExactThreeSATThree φ ∈ PlanarPositiveOneInThreeSATThree ↔
      φ ∈ ThreeSAT := by
  constructor
  · intro h
    exact (oneSatisfiable_toPlanarPositiveOneInExactThreeSATThree_iff φ).mp h.1.1.2.2
  · intro h
    refine ⟨⟨⟨?_, positive_toPlanarPositiveOneInExactThreeSATThree φ,
      (oneSatisfiable_toPlanarPositiveOneInExactThreeSATThree_iff φ).mpr h⟩,
      count_vars_toPlanarPositiveOneInExactThreeSATThree_le φ⟩,
      (toDrawnPlanarPositiveOneInExactThreeSATThree φ).2,
      isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ⟩
    exact fun c hc => (exactClauses_toPlanarPositiveOneInExactThreeSATThree φ c hc).1.le

/-- Positive width-three, occurrence-three planar exact-one SAT is NP-hard. -/
theorem PlanarPositiveOneInThreeSATThree_npHard :
    NPHard encCNF PlanarPositiveOneInThreeSATThree :=
  ThreeSAT_npHard.trans ⟨toPlanarPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree,
    fun φ => (mem_PlanarPositiveOneInThreeSATThree_toPlanar_iff φ).symm⟩

/-- The positive planar compiler preserves syntax-guarded counts on every source input. -/
theorem sharpPositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree
    (φ : CNF ℕ) :
    SharpPositiveOneInExactThreeSATThree (toPlanarPositiveOneInExactThreeSATThree φ) =
      SharpThreeSAT φ := by
  have hg := (PositiveOneInExactThreeSATThree.syntaxCheck_iff _).mpr
    ⟨exactClauses_toPlanarPositiveOneInExactThreeSATThree φ,
      positive_toPlanarPositiveOneInExactThreeSATThree φ,
      count_vars_toPlanarPositiveOneInExactThreeSATThree_le φ⟩
  have hplan := sharpThreeSATThree_toPlanarThreeSATThree (toThreeSATThree φ)
  have hout := (ThreeSATThree.syntaxCheck_iff _).mpr
    ⟨width_toPlanarThreeSATThree (toThreeSATThree φ),
      count_vars_toPlanarThreeSATThree (toThreeSATThree φ)⟩
  have hsource := (ThreeSATThree.syntaxCheck_iff _).mpr
    ⟨width_toThreeSATThree φ, count_vars_toThreeSATThree_le φ⟩
  simp only [SharpThreeSATThree, hout, hsource, ↓reduceIte, SharpSAT] at hplan
  simp only [SharpPositiveOneInExactThreeSATThree, hg, ↓reduceIte]
  change (CNF.PositiveExactOneCompile.formula
    (toPlanarThreeSATThree (toThreeSATThree φ))).oneModelCount = _
  rw [CNF.PositiveExactOneCompile.oneModelCount_formula _
      (width_toPlanarThreeSATThree (toThreeSATThree φ))]
  exact hplan.trans (by
    simpa only [SharpThreeSATThree, hsource, ↓reduceIte, SharpSAT] using
      sharpThreeSATThree_toThreeSATThree φ)

/-- The planar formula compiler is a native parsimonious reduction to the planarity-guarded count:
every output has a planar orthogonal incidence drawing, so the guard never discards a model. -/
theorem parsimoniousReducible_SharpThreeSAT_SharpPlanarPositiveOneInExactThreeSATThree :
    ParsimoniousReducible encCNF encCNF SharpThreeSAT
      SharpPlanarPositiveOneInExactThreeSATThree :=
  ⟨toPlanarPositiveOneInExactThreeSATThree,
    computableInPolyTime_toPlanarPositiveOneInExactThreeSATThree, fun φ => by
      rw [SharpPlanarPositiveOneInExactThreeSATThree]
      split
      · exact (sharpPositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree φ).symm
      · rename_i h
        exact
          (h ⟨_, isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ⟩).elim⟩

/-- The full compiler retains linear grid sides relative to the original ordinary 3SAT input. -/
theorem toDrawnPlanarPositiveOneInExactThreeSATThree_fits (φ : CNF ℕ) :
    let s := φ.length + φ.vars.length + 1
    Graph.drawingFits (toDrawnPlanarPositiveOneInExactThreeSATThree φ).2
      (14516280000 * s) (14516280000 * s) := by
  apply Graph.drawingFits_mono
    (SAT.ExactOne.positiveDrawing_fits (toPlanarThreeSAT φ) (toDrawnPlanarThreeSAT_fits φ)) <;>
    omega

/-- The actual output formula and drawing all have quadratic size relative to the original
ordinary 3SAT input. Segment and wire costs refer to the emitted full routes. -/
theorem toDrawnPlanarPositiveOneInExactThreeSATThree_costs (φ : CNF ℕ) :
    let out := toDrawnPlanarPositiveOneInExactThreeSATThree φ
    let s := φ.length + φ.vars.length + 1
    out.1.length ≤ 41405000 * s ^ 2 ∧ out.1.vars.length ≤ 124215000 * s ^ 2 ∧
      out.2.1.length ≤ 165620000 * s ^ 2 ∧ out.2.2.length ≤ 124215000 * s ^ 2 ∧
        Graph.drawingSegmentCount out.2 ≤ 141463000 * s ^ 2 ∧
          Graph.drawingWireLength out.2 ≤ 31029887000000 * s ^ 2 := by
  have hs := size_toPlanarPositiveOneInExactThreeSATThree φ
  have hp := toDrawnPlanarThreeSAT_costs φ
  have hc := SAT.ExactOne.positiveDrawing_costs
    (isPlanarOrthogonalDrawing_toDrawnPlanarThreeSAT φ)
    (width_toPlanarThreeSATThree (toThreeSATThree φ))
  dsimp only [toDrawnPlanarPositiveOneInExactThreeSATThree, toPlanarThreeSAT]
  dsimp only [toPlanarThreeSAT] at hc
  exact ⟨hs.1, hs.2, by nlinarith [hc.1, hp.1], by nlinarith [hc.2.1, hp.1],
    by nlinarith [hc.2.2.1, hp.1, hp.2.2.2.1],
    by nlinarith [hc.2.2.2, hp.1, hp.2.2.2.2]⟩

/-- Formula labels, vertex coordinates and route coordinates are all computed in native
polynomial time under their ordinary binary encodings. -/
@[fun_prop]
theorem computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree :
    ComputableInPolyTime toDrawnPlanarPositiveOneInExactThreeSATThree encCNF
      (encPair encCNF Graph.encOrthogonalDrawing) := by
  have hf := (CNF.PositiveExactOneCompile.computableInPolyTime_formula encNat).comp
    (ComputableInPolyTime.fst encCNF Graph.encOrthogonalDrawing)
  have h := (hf.prod SAT.ExactOne.DrawingNative.computableInPolyTime_positiveDrawing).comp
    computableInPolyTime_toDrawnPlanarThreeSAT
  exact h

/-- Ordinary 3SAT reduces natively to the positive target with its actual drawing supplied. -/
theorem polyTimeReducible_ThreeSAT_DrawnPlanarPositiveOneInExactThreeSATThree :
    PolyTimeReducible encCNF (encPair encCNF Graph.encOrthogonalDrawing)
      ThreeSAT DrawnPlanarPositiveOneInExactThreeSATThree :=
  ⟨toDrawnPlanarPositiveOneInExactThreeSATThree,
    computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree,
    fun φ => (mem_DrawnPlanarPositiveOneInExactThreeSATThree_toDrawn_iff φ).symm⟩

/-- Supplied-drawing planar positive exact-three, occurrence-three exact-one SAT is NP-hard. -/
theorem DrawnPlanarPositiveOneInExactThreeSATThree_npHard :
    NPHard (encPair encCNF Graph.encOrthogonalDrawing) DrawnPlanarPositiveOneInExactThreeSATThree :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_DrawnPlanarPositiveOneInExactThreeSATThree

/-- Supplying the emitted drawing gives a native parsimonious reduction to the count guarded by the
validity of the supplied drawing: the emitted drawing is always a planar orthogonal incidence
drawing of the emitted formula. -/
theorem parsimoniousReducible_SharpThreeSAT_SharpDrawnPlanarPositiveOneInExactThreeSATThree :
    ParsimoniousReducible encCNF (encPair encCNF Graph.encOrthogonalDrawing) SharpThreeSAT
      SharpDrawnPlanarPositiveOneInExactThreeSATThree :=
  ⟨toDrawnPlanarPositiveOneInExactThreeSATThree,
    computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree, fun φ => by
      rw [SharpDrawnPlanarPositiveOneInExactThreeSATThree]
      split
      · exact (sharpPositiveOneInExactThreeSATThree_toPlanarPositiveOneInExactThreeSATThree φ).symm
      · rename_i h
        exact (h (isPlanarOrthogonalDrawing_toDrawnPlanarPositiveOneInExactThreeSATThree φ)).elim⟩

end Cslib.Complexity
