/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
import Complexity.Computability.Complexity.Problems.SAT.Planar.Geometry
import Complexity.Computability.Complexity.Problems.SAT.Planar.Size
import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Explicit grid and wire bounds for the actual planarization compiler

For an input incidence graph with `n` vertices and `m` literal incidences, the emitted integer
points fit a rectangle of width `240 (8n + 1)` and height `240 (8n + 2m + 1)`. These are linear
in the source's combinatorial incidence size. The bounds hold for the actual emitted lists,
including empty clauses and repeated literal incidences. Writing
`S = φ.numVars + φ.length + φ.vars.length + 1`, there are at most `1210 S²` routes,
`23000 S²` segments and `300000 S²` units of Manhattan wire. The constants follow from the
fixed template costs and uniform per-route bounds.

## Main definitions

* `gridWidth`, `gridHeight`: explicit grid sides of the tiled output.

## Main results

* `drawing_fits`: bounds on every actual vertex and incidence-route point.
* `gridWidth_le`, `gridHeight_le`: common linear bounds in source incidence size.
* `routes_length_le`, `drawingSegmentCount_le`, `drawingWireLength_le`: explicit quadratic
  bounds on the actual output route data.

## References

These bounds concern the original finite compiler in `Compile` and its 240-square template.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile
open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Horizontal side of the actual tiled drawing, including its last square. -/
def gridWidth (φ : CNF ℕ) : ℕ := 240 * (8 * (SAT.incidenceGraph φ).1.length + 1)
/-- Vertical side of the actual tiled drawing, including its last square. -/
def gridHeight (φ : CNF ℕ) : ℕ :=
  240 * (8 * (SAT.incidenceGraph φ).1.length + 2 * (SAT.incidenceGraph φ).2.length + 1)

private def CellBound (φ : CNF ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 8 * ((SAT.incidenceGraph φ).1.length : ℤ) ∧
    0 ≤ p.2 ∧ p.2 ≤ 8 * ((SAT.incidenceGraph φ).1.length : ℤ) +
      2 * (SAT.incidenceGraph φ).2.length

private def OutputBound (φ : CNF ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ gridWidth φ ∧ 0 ≤ p.2 ∧ p.2 ≤ gridHeight φ

private theorem outputBound_add {φ : CNF ℕ} {p a : Point} (hp : CellBound φ p)
    (ha : 0 ≤ a.1 ∧ a.1 ≤ 240 ∧ 0 ≤ a.2 ∧ a.2 ≤ 240) :
    OutputBound φ (cellOrigin 120 p + a) := by
  simp only [OutputBound, gridWidth, gridHeight, Prod.fst_add, Prod.snd_add, cellOrigin,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  dsimp only [CellBound] at hp
  norm_num at *
  constructor
  · nlinarith [hp.1, ha.1]
  constructor
  · nlinarith [hp.2.1, ha.2.1]
  constructor <;> nlinarith [hp.2.2.1, hp.2.2.2, ha.2.2.1, ha.2.2.2]

private theorem cellBound_path {φ : CNF ℕ} {r : Route} (hr : r ∈ paths φ)
    {p : Point} (hp : p ∈ r) : CellBound φ p := by
  change r ∈ (SAT.incidenceGraph φ).unitPaths at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < (SAT.incidenceGraph φ).2.length := by simpa using hi
  have hp' : p ∈ (SAT.incidenceGraph φ).unitPath i := by
    simpa only [Graph.unitPath, List.getD_eq_getElem _ _ hi] using hp
  exact Graph.unitPath_bounds _ (fun _ he => SAT.incidenceGraph_endpoints he)
    (fun _ he => SAT.incidenceGraph_loopless he) hi' hp'

private theorem cellBound_occurrencePath {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {p : Point} (hp : p ∈ occurrencePath φ o) :
    CellBound φ p := by
  have hi : (Cslib.Logic.PL.occurrences φ).idxOf o < (paths φ).length := by
    rw [paths_length, ← Cslib.Logic.PL.length_occurrences]
    exact List.idxOf_lt_length_of_mem ho
  apply cellBound_path (r := occurrencePath φ o) _ hp
  rw [occurrencePath, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

private theorem cellBound_crossing {φ : CNF ℕ} {p : Point} (hp : p ∈ crossingSites φ) :
    CellBound φ p := by
  have hlen := (mem_crossingSites φ p).mp hp |>.2.2
  have hnonempty : ((paths φ).filter fun r => r.contains p) ≠ [] := by
    intro he
    rw [he] at hlen
    simp at hlen
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hnonempty
  obtain ⟨hr, hp⟩ := List.mem_filter.mp hr
  exact cellBound_path hr (List.contains_iff_mem.mp hp)

private theorem cellBound_clause {φ : CNF ℕ} {i : ℕ} (hi : i < φ.length) :
    CellBound φ (Layout.center (φ.distinctVars.length + i)) := by
  have hn : φ.distinctVars.length + i < (SAT.incidenceGraph φ).1.length := by
    simp only [SAT.length_vertices_incidenceGraph, CNF.length_distinctVars]
    omega
  simp only [CellBound, Layout.center, Nat.cast_add]
  omega

private theorem outputBound_variable {φ : CNF ℕ} {v : Variable} (hv : CellBound φ v.1) :
    OutputBound φ (variablePosition v) := by
  apply outputBound_add hv
  cases h : v.2 with
  | none => norm_num
  | some w =>
    have hw := Crossover.variable_bounds w
    simp only [Option.elim_some]
    omega

private theorem outputBound_access {φ : CNF ℕ} (sites : List Point) {p q a : Point}
    (hp : CellBound φ p) (ha : a ∈ access sites p q) : OutputBound φ a := by
  unfold access at ha
  split at ha
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [add_comm]
    apply outputBound_add hp
    simp only [Crossover.accessRoute, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · generalize side p q = s
      fin_cases s <;> decide
    · have hw := Crossover.variable_bounds (Crossover.splitTerminal (side p q))
      omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · unfold cellPort
      apply outputBound_add hp
      generalize side p q = s
      fin_cases s <;> decide
    · exact outputBound_add hp (by norm_num)

private theorem outputBound_center {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) :
    OutputBound φ (center p) := outputBound_add hp (by norm_num)

private theorem outputBound_port {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) (s : Fin 4) :
    OutputBound φ (cellPort 120 p s) := by
  unfold cellPort
  apply outputBound_add hp
  fin_cases s <;> decide

private theorem lastLiteral_bounds {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (sites : List Point) :
    OutputBound φ (variablePosition (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1) ∧
      ∀ a ∈ (lastLiteral sites (occurrencePath φ o) o.2.2.2).2, OutputBound φ a := by
  let r := occurrencePath φ o
  have hlen : 2 ≤ r.length := occurrencePath_length_ge_two ho
  have hp : CellBound φ (r.getD (r.length - 2) (0, 0)) := by
    apply cellBound_occurrencePath ho
    rw [List.getD_eq_getElem _ _ (show r.length - 2 < r.length by omega)]
    exact List.getElem_mem _
  have hq : CellBound φ (r.getLastD (0, 0)) := by
    rw [List.getLastD_eq_getLast?, (occurrencePath_endpoints ho).2, Option.getD_some]
    exact cellBound_clause (Cslib.Logic.PL.mem_occurrences.mp ho).1
  change OutputBound φ (variablePosition (signal sites (r.getD (r.length - 2) (0, 0))
    (r.getLastD (0, 0)))) ∧ _
  constructor
  · exact outputBound_variable hp
  · intro a ha
    change a ∈ center (r.getLastD (0, 0)) ::
      access sites (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact outputBound_center hq
    · exact outputBound_access sites hp ha

private def ClauseBound (φ : CNF ℕ) (pc : PlacedClause) : Prop :=
  OutputBound φ pc.2.1 ∧
    (∀ l ∈ pc.1, OutputBound φ (variablePosition l.1)) ∧
      ∀ r ∈ pc.2.2, ∀ a ∈ r, OutputBound φ a

private theorem originalClauses_bounds (φ : CNF ℕ) (sites : List Point) :
    ∀ pc ∈ originalClauses φ sites, ClauseBound φ pc := by
  intro pc hpc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  refine ⟨outputBound_center (cellBound_clause (List.mem_zipIdx' hci).1), ?_, ?_⟩
  · intro l hl
    obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hl
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    exact (lastLiteral_bounds ho sites).1
  · intro r hr a ha
    obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    exact (lastLiteral_bounds ho sites).2 a ha

private theorem crossingClauses_bounds {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) :
    ∀ pc ∈ crossingClauses p, ClauseBound φ pc := by
  intro pc hpc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  refine ⟨?_, ?_, ?_⟩
  · apply outputBound_add hp
    have hi : ci.2 < Crossover.clausePositions.length := by
      rw [Crossover.drawing_sizes.1]
      exact (Crossover.length_splitFormula ▸ (List.mem_zipIdx' hci).1)
    have hb := Crossover.clause_bounds _ (List.getElem_mem hi)
    rw [List.getD_eq_getElem _ _ hi]
    omega
  · intro l hl
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    exact outputBound_variable hp
  · intro r hr a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [add_comm]
    apply outputBound_add hp
    have h := Crossover.core_bounds e (List.mem_filter.mp he).1 b hb
    omega

private theorem link_bounds {φ : CNF ℕ} (sites : List Point) (positive : Bool) {p q : Point}
    (hp : CellBound φ p) (hq : CellBound φ q) : ClauseBound φ (link sites positive p q) := by
  have hvp := outputBound_variable (v := signal sites p q) hp
  have hvq := outputBound_variable (v := signal sites q p) hq
  refine ⟨outputBound_port hp _, ?_, ?_⟩
  · intro l hl
    cases positive <;>
      simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl <;> assumption
  · intro r hr a ha
    cases positive <;>
      simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl
    · exact outputBound_access sites hp ha
    · exact outputBound_access sites hq ha
    · exact outputBound_access sites hq ha
    · exact outputBound_access sites hp ha

private theorem placedClauses_bounds (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, ClauseBound φ pc := by
  intro pc hpc
  rcases List.mem_append.mp hpc with hpc | hpc
  · rcases List.mem_append.mp hpc with hpc | hpc
    · exact originalClauses_bounds φ _ pc hpc
    · obtain ⟨p, hp, hpc⟩ := List.mem_flatMap.mp hpc
      exact crossingClauses_bounds (cellBound_crossing hp) pc hpc
  · obtain ⟨o, ho, hpc⟩ := List.mem_flatMap.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    have he' := List.of_mem_zip he
    have hp := cellBound_occurrencePath ho ((List.dropLast_subset _ ) he'.1)
    have hq := cellBound_occurrencePath ho
      ((List.dropLast_subset _) (List.mem_of_mem_tail he'.2))
    exact link_bounds _ _ hp hq

/-- Every emitted vertex and route point lies in the explicit nonnegative grid rectangle.
This quantitative statement does not assert geometric planarity. -/
theorem drawing_fits (φ : CNF ℕ) :
    Graph.drawingFits (positions φ, routes φ) (gridWidth φ) (gridHeight φ) := by
  constructor
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
      obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp (CNF.mem_distinctVars.mp hv)
      obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
      exact (placedClauses_bounds φ pc hpc).2.1 (v, b) hv
    · obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
      exact (placedClauses_bounds φ pc hpc).1
  · intro r hr p hp
    obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
    exact (placedClauses_bounds φ pc hpc).2.2 r hr p hp

/-- The horizontal grid side is at most 1920 times the source incidence size plus one. -/
theorem gridWidth_le (φ : CNF ℕ) :
    gridWidth φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) := by
  unfold gridWidth
  rw [SAT.length_vertices_incidenceGraph]
  nlinarith

/-- The vertical grid side is at most 1920 times the source incidence size plus one. -/
theorem gridHeight_le (φ : CNF ℕ) :
    gridHeight φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) := by
  unfold gridHeight
  rw [SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  nlinarith

private theorem access_cost (sites : List Point) (p q : Point) :
    wireLength (access sites p q) ≤ 240 ∧
      (access sites p q).consecutivePairs.length ≤ 19 := by
  constructor
  · rw [access_wireLength]
    split_ifs <;> decide
  · rw [access_eq_pair]
    change (1 : ℕ) ≤ 19
    decide

private theorem coreRoute_cost : ∀ e ∈ Crossover.incidenceRoutes,
    wireLength e.2.2 ≤ 72 ∧ e.2.2.consecutivePairs.length ≤ 19 := by decide +kernel

private theorem routes_cost (φ : CNF ℕ) :
    ∀ r ∈ routes φ, wireLength r ≤ 240 ∧ r.consecutivePairs.length ≤ 19 := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only [lastLiteral] at hlreq
    subst r
    constructor
    · exact finalRoute_wireLength_le _ (occurrencePath_last_unit ho)
    · rw [access_eq_pair]
      change (2 : ℕ) ≤ 19
      decide
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    have hb := coreRoute_cost e he'
    constructor
    · rw [wireLength_translate]
      exact hb.1.trans (by decide)
    · simpa [translate, List.consecutivePairs] using hb.2
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl <;> exact access_cost _ _ _

/-- The actual output has at most 1210 times the squared source incidence size routes. -/
theorem routes_length_le (φ : CNF ℕ) :
    (routes φ).length ≤ 1210 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  rw [routes_length, SAT.length_edges_incidenceGraph]
  exact length_vars_formula_le φ

/-- The actual total Manhattan wire length is explicitly quadratic in source incidence size. -/
theorem drawingWireLength_le (φ : CNF ℕ) :
    Graph.drawingWireLength (positions φ, routes φ) ≤
      300000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have hb : ((routes φ).map wireLength).sum ≤ (routes φ).length * 240 := by
    calc
      _ ≤ ((routes φ).map fun _ => 240).sum :=
        List.sum_le_sum fun r hr => (routes_cost φ r hr).1
      _ = _ := by simp
  have hr := routes_length_le φ
  change ((routes φ).map wireLength).sum ≤ _
  nlinarith

/-- The actual number of listed route segments is explicitly quadratic in source incidence size. -/
theorem drawingSegmentCount_le (φ : CNF ℕ) :
    Graph.drawingSegmentCount (positions φ, routes φ) ≤
      23000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have hb : ((routes φ).map fun r => r.consecutivePairs.length).sum ≤
      (routes φ).length * 19 := by
    calc
      _ ≤ ((routes φ).map fun _ => 19).sum :=
        List.sum_le_sum fun r hr => (routes_cost φ r hr).2
      _ = _ := by simp
  have hr := routes_length_le φ
  change ((routes φ).map fun r => r.consecutivePairs.length).sum ≤ _
  nlinarith

end Cslib.Complexity.SAT.PlanarCompile
