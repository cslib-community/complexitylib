/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedSize
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathBounds
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
import Complexity.Computability.Complexity.Problems.SAT.Planar.PathGeometry
import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Quantitative bounds for the paired-port compiler

The actual output fits the unchanged 240-macrocell grid, with linear grid sides and quadratic
clause, literal, route, segment, and Manhattan-wire costs. Bounds concern the emitted lists and
all their integer points; geometric separation is proved separately.

## Main results

* `drawing_fits`, `gridWidth_le`, `gridHeight_le`: the actual drawing fits a linear grid.
* `length_routes`, `drawingSegmentCount_eq`, `drawingWireLength_eq`: exact output costs.
* `routes_length_le`, `drawingSegmentCount_le`, `drawingWireLength_le`: quadratic bounds.

## References

The unchanged path and grid estimates are reused from `Planar.Size` and `Planar.Bounds`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The unchanged horizontal side of the 240-macrocell drawing. -/
abbrev gridWidth := PlanarCompile.gridWidth

/-- The unchanged vertical side of the 240-macrocell drawing. -/
abbrev gridHeight := PlanarCompile.gridHeight

private def CellBound (φ : CNF ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 8 * ((SAT.incidenceGraph φ).1.length : ℤ) ∧
    0 ≤ p.2 ∧ p.2 ≤ 8 * ((SAT.incidenceGraph φ).1.length : ℤ) +
      2 * (SAT.incidenceGraph φ).2.length

private def OutputBound (φ : CNF ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ gridWidth φ ∧ 0 ≤ p.2 ∧ p.2 ≤ gridHeight φ

private theorem outputBound_add {φ : CNF ℕ} {p a : Point} (hp : CellBound φ p)
    (ha : 0 ≤ a.1 ∧ a.1 ≤ 240 ∧ 0 ≤ a.2 ∧ a.2 ≤ 240) :
    OutputBound φ (cellOrigin 120 p + a) := by
  simp only [OutputBound, gridWidth, gridHeight, PlanarCompile.gridWidth, PlanarCompile.gridHeight,
    Prod.fst_add, Prod.snd_add, cellOrigin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
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
    CellBound φ p :=
  cellBound_path (PlanarCompile.occurrencePath_mem_paths ho) hp

private theorem cellBound_crossing {φ : CNF ℕ} {p : Point} (hp : p ∈ crossingSites φ) :
    CellBound φ p := by
  have hlen := (PlanarCompile.mem_crossingSites φ p).mp hp |>.2.2
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

private theorem crossover_variable_bounds : ∀ v,
    20 ≤ (PairedCrossover.variablePosition v).1 ∧ (PairedCrossover.variablePosition v).1 ≤ 220 ∧
      20 ≤ (PairedCrossover.variablePosition v).2 ∧ (PairedCrossover.variablePosition v).2 ≤ 220 :=
  by decide +kernel

private theorem crossover_clause_bounds : ∀ p ∈ PairedCrossover.clausePositions,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 := by decide +kernel

private theorem crossover_core_bounds : ∀ e ∈ PairedCrossover.incidenceRoutes, ∀ p ∈ e.2.2,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 := by decide +kernel

private theorem outputBound_variable {φ : CNF ℕ} {v : Variable} (hv : CellBound φ v.1) :
    OutputBound φ (variablePosition v) := by
  apply outputBound_add hv
  cases h : v.2 with
  | inl w =>
    have hw := PairedPorts.variable_bounds w.1 w.2
    simp only [Sum.elim_inl]
    omega
  | inr w =>
    have hw := crossover_variable_bounds w
    simp only [Sum.elim_inr]
    omega

private theorem outputBound_center {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) :
    OutputBound φ (center p) := outputBound_add hp (by norm_num)

private theorem outputBound_boundary {φ : CNF ℕ} {p : Point} (hp : CellBound φ p)
    (s : Fin 4) (lane : Fin 2) : OutputBound φ (boundary p s lane) := by
  unfold boundary
  apply outputBound_add hp
  fin_cases s <;> fin_cases lane <;> decide

private theorem outputBound_access {φ : CNF ℕ} (sites : List Point) {p q a : Point}
    (hp : CellBound φ p) (lane : Fin 2) (ha : a ∈ access sites p q lane) :
    OutputBound φ a := by
  simp only [access, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact outputBound_boundary hp _ _
  · exact outputBound_variable hp

private theorem lastLiteral_bounds {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (sites : List Point) :
    OutputBound φ (variablePosition (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1) ∧
      ∀ a ∈ (lastLiteral sites (occurrencePath φ o) o.2.2.2).2, OutputBound φ a := by
  let r := occurrencePath φ o
  have hlen : 2 ≤ r.length := PlanarCompile.occurrencePath_length_ge_two ho
  have hp : CellBound φ (r.getD (r.length - 2) (0, 0)) := by
    apply cellBound_occurrencePath ho
    rw [List.getD_eq_getElem _ _ (show r.length - 2 < r.length by omega)]
    exact List.getElem_mem _
  have hq : CellBound φ (r.getLastD (0, 0)) := by
    rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2,
      Option.getD_some]
    exact cellBound_clause (Cslib.Logic.PL.mem_occurrences.mp ho).1
  constructor
  · exact outputBound_variable hp
  · intro a ha
    simp only [lastLiteral, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact outputBound_center hq
    · apply outputBound_add hq
      generalize side (r.getLastD (0, 0)) (r.getD (r.length - 2) (0, 0)) = s
      fin_cases s <;> decide
    · exact outputBound_boundary hq _ _
    · exact outputBound_variable hp

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

private theorem ordinaryClauses_bounds {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) :
    ∀ pc ∈ ordinaryClauses p, ClauseBound φ pc := by
  intro pc hpc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  refine ⟨?_, ?_, ?_⟩
  · apply outputBound_add hp
    have hi : ci.2 < OrdinaryRing.clausePositions.length := by
      rw [OrdinaryRing.drawing_sizes.1]
      exact (OrdinaryRing.formula_sizes.1 ▸ (List.mem_zipIdx' hci).1)
    have hb := OrdinaryRing.clause_bounds _ (List.getElem_mem hi)
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
    have h := OrdinaryRing.core_bounds e (List.mem_filter.mp he).1 b hb
    omega

private theorem crossingClauses_bounds {φ : CNF ℕ} {p : Point} (hp : CellBound φ p) :
    ∀ pc ∈ crossingClauses p, ClauseBound φ pc := by
  intro pc hpc
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  refine ⟨?_, ?_, ?_⟩
  · apply outputBound_add hp
    have hi : ci.2 < PairedCrossover.clausePositions.length := by
      rw [show PairedCrossover.clausePositions.length = 78 by decide +kernel]
      exact (PairedCrossover.length_formula ▸ (List.mem_zipIdx' hci).1)
    have hb := crossover_clause_bounds _ (List.getElem_mem hi)
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
    have h := crossover_core_bounds e (List.mem_filter.mp he).1 b hb
    omega


private theorem link_bounds {φ : CNF ℕ} (sites : List Point) (lane : Fin 2) {p q : Point}
    (hp : CellBound φ p) (hq : CellBound φ q) : ClauseBound φ (link sites p q lane) := by
  have hvp := outputBound_variable (v := signal sites p q lane) hp
  have hvq := outputBound_variable (v := signal sites q p lane) hq
  refine ⟨outputBound_boundary hp _ _, ?_, ?_⟩
  · intro l hl
    by_cases h : lane = 0 <;>
      simp only [link, h, ite_true, ite_false, List.mem_cons,
        List.not_mem_nil, or_false] at hl hvp hvq <;>
      rcases hl with rfl | rfl <;> assumption
  · intro r hr a ha
    by_cases h : lane = 0 <;>
      simp only [link, h, ite_true, ite_false, List.mem_cons,
        List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl
    all_goals
      first
      | exact outputBound_access sites hp _ ha
      | exact outputBound_access sites hq _ ha

private theorem cellBound_ordinary {φ : CNF ℕ} {p : Point} (hp : p ∈ ordinaryCells φ) :
    CellBound φ p := by
  obtain ⟨⟨r, hr, hp⟩, -⟩ := (mem_ordinaryCells φ p).1 hp
  exact cellBound_path hr ((List.dropLast_subset _) hp)

private theorem placedClauses_bounds (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, ClauseBound φ pc := by
  intro pc hpc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, hp, hpc⟩) | ⟨p, hp, hpc⟩) | ⟨o, ho, hpc⟩
  · exact originalClauses_bounds φ _ pc hpc
  · exact ordinaryClauses_bounds (cellBound_ordinary hp) pc hpc
  · exact crossingClauses_bounds (cellBound_crossing hp) pc hpc
  · obtain ⟨e, he, hpc⟩ := List.mem_flatMap.mp hpc
    have he' := List.of_mem_zip he
    have hp := cellBound_occurrencePath ho ((List.dropLast_subset _) he'.1)
    have hq := cellBound_occurrencePath ho
      ((List.dropLast_subset _) (List.mem_of_mem_tail he'.2))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;> exact link_bounds _ _ hp hq

/-- Every actual vertex and route point lies in the explicit nonnegative grid rectangle.
This quantitative statement does not assert geometric separation. -/
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

/-- The horizontal grid side is linear in source incidence size. -/
theorem gridWidth_le (φ : CNF ℕ) :
    gridWidth φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) :=
  PlanarCompile.gridWidth_le φ

/-- The vertical grid side is linear in source incidence size. -/
theorem gridHeight_le (φ : CNF ℕ) :
    gridHeight φ ≤ 1920 * (φ.numVars + φ.length + φ.vars.length + 1) :=
  PlanarCompile.gridHeight_le φ

/-- The position list contains the distinct structured variables followed by all output clauses. -/
theorem length_positions (φ : CNF ℕ) :
    (positions φ).length = (rawFormula φ).numVars + (formula φ).length := by
  simp [positions, CNF.length_distinctVars, formula, rawFormula]

/-- The total number of output vertex positions is explicitly quadratic. -/
theorem positions_length_le (φ : CNF ℕ) :
    (positions φ).length ≤ 15000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have hv := (rawFormula φ).numVars_le_length_vars
  have hf := length_formula_le φ
  have hl := length_vars_formula_le φ
  rw [length_positions]
  rw [length_vars_rawFormula, ← length_vars_formula] at hv
  omega

private theorem original_route_count (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun c => c.2.2.length).sum = φ.vars.length := by
  rw [CNF.length_vars]
  simp only [originalClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]
  change ((φ.zipIdx).map (List.length ∘ Prod.fst)).sum = (φ.map List.length).sum
  rw [← List.map_map, List.zipIdx_map_fst]

private theorem original_route_cost (φ : CNF ℕ) (sites : List Point) (cost : Route → ℕ)
    (k : ℕ) (h : ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      cost (lastLiteral sites (occurrencePath φ o) o.2.2.2).2 = k) :
    ((originalClauses φ sites).map fun c => (c.2.2.map cost).sum).sum = k * φ.vars.length := by
  have hm : (originalClauses φ sites).map (fun c => (c.2.2.map cost).sum) =
      (originalClauses φ sites).map (fun c => k * c.2.2.length) := by
    apply List.map_congr_left
    intro c hc
    have he : c.2.2.map cost = c.2.2.map (fun _ => k) := by
      apply List.map_congr_left
      intro r hr
      obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hc
      obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hr
      obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
      exact h (ci.2, lj.2, lj.1)
        (List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩)
    rw [he]
    simp [Nat.mul_comm]
  rw [hm, List.sum_map_mul_left, original_route_count]

private theorem total_route_cost (φ : CNF ℕ) (cost : Route → ℕ)
    (source ordinary crossing seam : ℕ)
    (hs : ((originalClauses φ (crossingSites φ)).map fun c => (c.2.2.map cost).sum).sum =
      source * φ.vars.length)
    (ho : ∀ p, ((ordinaryClauses p).map fun c => (c.2.2.map cost).sum).sum = ordinary)
    (hc : ∀ p, ((crossingClauses p).map fun c => (c.2.2.map cost).sum).sum = crossing)
    (hl : ∀ r, ((links (crossingSites φ) r).map fun c => (c.2.2.map cost).sum).sum =
      seam * (r.length - 2)) :
    ((routes φ).map cost).sum = source * φ.vars.length +
      ordinary * (ordinaryCells φ).length + crossing * (crossingSites φ).length +
        seam * PlanarCompile.linkCount φ := by
  simp only [routes, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]
  simp only [placedClauses, List.map_append, List.sum_append, List.flatMap,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  simp_rw [hs, ho, hc, hl]
  simp [PlanarCompile.linkCount, List.sum_map_mul_left, Nat.mul_comm, Nat.add_assoc]

private theorem links_stat (sites : List Point) (r : Route) (cost : PlacedClause → ℕ)
    (k : ℕ) (h : ∀ p q lane, cost (link sites p q lane) = k) :
    ((links sites r).map cost).sum = (2 * k) * (r.length - 2) := by
  have hm : (links sites r).map cost = (links sites r).map (fun _ => k) := by
    apply List.map_congr_left
    intro c hc
    obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact h _ _ _
  rw [hm]
  have he : ((links sites r).map fun _ => k).sum = k * (links sites r).length := by
    simp [Nat.mul_comm]
  rw [he, length_links, ← Nat.mul_assoc, Nat.mul_comm k 2]

private theorem segments_translate (p : Point) (r : Route) :
    (translate p r).consecutivePairs.length = r.consecutivePairs.length := by
  simp [translate, List.consecutivePairs]

private theorem ordinary_route_costs (p : Point) :
    ((ordinaryClauses p).map fun c => c.2.2.length).sum = 16 ∧
      ((ordinaryClauses p).map fun c =>
        (c.2.2.map fun r => r.consecutivePairs.length).sum).sum = 16 ∧
      ((ordinaryClauses p).map fun c => (c.2.2.map wireLength).sum).sum = 800 := by
  simp only [ordinaryClauses, List.map_map, Function.comp_def, List.length_map,
    segments_translate, wireLength_translate]
  decide +kernel

private theorem crossing_route_costs (p : Point) :
    ((crossingClauses p).map fun c => c.2.2.length).sum = 162 ∧
      ((crossingClauses p).map fun c =>
        (c.2.2.map fun r => r.consecutivePairs.length).sum).sum = 407 ∧
      ((crossingClauses p).map fun c => (c.2.2.map wireLength).sum).sum = 2192 := by
  simp only [crossingClauses, List.map_map, Function.comp_def, List.length_map,
    segments_translate, wireLength_translate]
  decide +kernel

private theorem access_wire_cost (sites : List Point) (p q : Point) (lane : Fin 2) :
    wireLength (access sites p q lane) = 20 := by
  rw [access_eq_translate, wireLength_translate]
  exact (PairedPorts.access_route_sizes _ _).2

private theorem lastLiteral_wire_cost (sites : List Point) (r : Route) (b : Bool)
    (h : Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1) :
    wireLength (lastLiteral sites r b).2 = 150 := by
  dsimp only [lastLiteral]
  rw [finalRoute_eq_translate sites h, wireLength_translate]
  generalize side (r.getLastD (0, 0)) (r.getD (r.length - 2) (0, 0)) = s
  fin_cases s <;> decide

/-- Exact route count, one per output literal position. -/
theorem length_routes (φ : CNF ℕ) :
    (routes φ).length = φ.vars.length + 16 * (ordinaryCells φ).length +
      162 * (crossingSites φ).length + 4 * PlanarCompile.linkCount φ := by
  have hs := original_route_cost φ (crossingSites φ) (fun _ => 1) 1 (fun _ _ => rfl)
  have ho (p : Point) := (ordinary_route_costs p).1
  have hc (p : Point) := (crossing_route_costs p).1
  have hl (r : Route) := links_stat (crossingSites φ) r (fun c => c.2.2.length) 2
    (by intro p q lane; by_cases h : lane = 0 <;> simp [link, h])
  have h := total_route_cost φ (fun _ => 1) 1 16 162 4 (by simpa using hs)
    (fun p => by simpa using ho p) (fun p => by simpa using hc p)
    (fun r => by simpa using hl r)
  simpa using h

/-- Exact number of listed incidence-route segments: three per source literal, sixteen per
ordinary ring, 407 per paired crossover, and four per retained path gap. -/
theorem drawingSegmentCount_eq (φ : CNF ℕ) :
    Graph.drawingSegmentCount (positions φ, routes φ) =
      3 * φ.vars.length + 16 * (ordinaryCells φ).length +
        407 * (crossingSites φ).length + 4 * PlanarCompile.linkCount φ := by
  have hs := original_route_cost φ (crossingSites φ) (fun r => r.consecutivePairs.length) 3
    (fun _ _ => rfl)
  have ho (p : Point) := (ordinary_route_costs p).2.1
  have hc (p : Point) := (crossing_route_costs p).2.1
  have hl (r : Route) := links_stat (crossingSites φ) r
    (fun c => (c.2.2.map fun r => r.consecutivePairs.length).sum) 2
    (by intro p q lane; by_cases h : lane = 0 <;> simp [link, h, access, List.consecutivePairs])
  exact total_route_cost φ _ 3 16 407 4 hs ho hc hl

/-- Exact Manhattan wire length of the actual drawing data. -/
theorem drawingWireLength_eq (φ : CNF ℕ) :
    Graph.drawingWireLength (positions φ, routes φ) =
      150 * φ.vars.length + 800 * (ordinaryCells φ).length +
        2192 * (crossingSites φ).length + 80 * PlanarCompile.linkCount φ := by
  have hs := original_route_cost φ (crossingSites φ) wireLength 150
    (fun o ho => lastLiteral_wire_cost _ _ _ (PlanarCompile.occurrencePath_last_unit ho))
  have ho (p : Point) := (ordinary_route_costs p).2.2
  have hc (p : Point) := (crossing_route_costs p).2.2
  have hl (r : Route) := links_stat (crossingSites φ) r
    (fun c => (c.2.2.map wireLength).sum) 40
    (by intro p q lane; by_cases h : lane = 0 <;> simp [link, h, access_wire_cost])
  exact total_route_cost φ _ 150 800 2192 80 hs ho hc hl

/-- The actual route count is quadratically bounded in source incidence size. -/
theorem routes_length_le (φ : CNF ℕ) :
    (routes φ).length ≤ 10000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  rw [length_routes, ← length_vars_formula]
  exact length_vars_formula_le φ

/-- The actual segment count is quadratically bounded in source incidence size. -/
theorem drawingSegmentCount_le (φ : CNF ℕ) :
    Graph.drawingSegmentCount (positions φ, routes φ) ≤
      12000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have ho := ordinaryCells_length_le φ
  have hc := crossingSites_length_le φ
  have hl := PlanarCompile.linkCount_le φ
  rw [drawingSegmentCount_eq]
  have hb : PlanarCompile.budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [PlanarCompile.budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at ho hl
  nlinarith

/-- The actual Manhattan wire length is quadratically bounded in source incidence size. -/
theorem drawingWireLength_le (φ : CNF ℕ) :
    Graph.drawingWireLength (positions φ, routes φ) ≤
      400000 * (φ.numVars + φ.length + φ.vars.length + 1) ^ 2 := by
  have ho := ordinaryCells_length_le φ
  have hc := crossingSites_length_le φ
  have hl := PlanarCompile.linkCount_le φ
  rw [drawingWireLength_eq]
  have hb : PlanarCompile.budget φ = 80 * (φ.numVars + φ.length) + 10 * φ.vars.length := by
    simp [PlanarCompile.budget, SAT.length_vertices_incidenceGraph, SAT.length_edges_incidenceGraph]
  rw [hb] at ho hl
  nlinarith

end Cslib.Complexity.SAT.ParsimoniousPlanar
