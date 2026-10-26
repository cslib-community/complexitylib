/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathGeometry
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Compact
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Geometry of the actual finite planar SAT compiler

The lemmas refer to the executable routes and positions in `PlanarCompile` and to their
complete real supports. Cell-local statements cover both the fixed crossover access and
ordinary center spokes. Their translated supports are confined to the corresponding square.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.access_eq_pair`: the actual access route endpoints.
* `Cslib.Complexity.SAT.PlanarCompile.access_orthogonal`,
  `Cslib.Complexity.SAT.PlanarCompile.access_simple`: local route certificates.
* `Cslib.Complexity.SAT.PlanarCompile.routes_regular`: all actual emitted routes are simple
  and orthogonal.
* `Cslib.Complexity.SAT.PlanarCompile.routes_length`,
  `Cslib.Complexity.SAT.PlanarCompile.positions_length`: counts match the final incidence graph.
* `Cslib.Complexity.SAT.PlanarCompile.variablePosition_injOn_rawVars`: distinct actual variable
  names have distinct displayed positions.
* `Cslib.Complexity.SAT.PlanarCompile.pathPorts_nodup`: all directed unit-cell ports of the
  actual paths are distinct under the source width and occurrence bounds.
* `Cslib.Complexity.SAT.PlanarCompile.positions_nodup`: every actual output vertex has a
  distinct displayed position under those same source bounds.
* `Cslib.Complexity.SAT.PlanarCompile.routes_endpoints`: actual incidence-order endpoints,
  including repeated literal occurrences and compact variable indices.
* `Cslib.Complexity.SAT.PlanarCompile.isPlanarOrthogonalDrawing`: the actual emitted formula,
  positions and routes form a complete planar orthogonal drawing under source clause width
  at most three and literal occurrence count at most three. Simplicity, vertex avoidance and
  contacts use full real supports, including the fixed crossing templates and final clause steps.

## References

The global assembly and coordinate arguments are original. The fixed crossover and its
continuous certificates are credited in `CrossoverLayout`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The fixed gadget and cell API use the same four geometric boundary points. -/
theorem cellPort_eq_boundaryPort (p : Point) (s : Fin 4) :
    cellPort 120 p s = cellOrigin 120 p + Crossover.boundaryPort s := by
  fin_cases s <;> rfl

/-- Every actual access route is a single segment from its cell port to its signal variable. -/
theorem access_eq_pair (sites : List Point) (p q : Point) :
    access sites p q = [cellPort 120 p (side p q), variablePosition (signal sites p q)] := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, Crossover.accessRoute, translate, List.map_cons,
      List.map_nil, signal, variablePosition, Option.elim_some, cellPort_eq_boundaryPort]
    simp only [add_comm]
  · simp [access, hp, signal, variablePosition, center]

private theorem spoke_orthogonal (s : Fin 4) :
    IsOrthogonal [Crossover.boundaryPort s, (120, 120)] := by
  fin_cases s <;> norm_num [IsOrthogonal, List.consecutivePairs, AxisAligned,
    Crossover.boundaryPort]

private theorem pair_simple (a b : Point) (h : a ≠ b) : IsSimple [a, b] := by
  simp [IsSimple, List.consecutivePairs, h]

/-- Ordinary access spokes are translates of the same four local straight segments. -/
theorem access_eq_spoke {sites : List Point} {p : Point} (hp : p ∉ sites) (q : Point) :
    access sites p q = translate (cellOrigin 120 p)
      [Crossover.boundaryPort (side p q), (120, 120)] := by
  simp [access, hp, translate, cellPort_eq_boundaryPort, center, add_comm]

/-- The actual access route is proper and orthogonal in both kinds of occupied cell. -/
theorem access_orthogonal (sites : List Point) (p q : Point) :
    IsOrthogonal (access sites p q) := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, isOrthogonal_translate_iff]
    exact (Crossover.access_endpoints (side p q)).1
  · rw [access_eq_spoke hp, isOrthogonal_translate_iff]
    exact spoke_orthogonal _

/-- The actual access route is continuously simple in both kinds of occupied cell. -/
theorem access_simple (sites : List Point) (p q : Point) : IsSimple (access sites p q) := by
  rw [access_eq_pair]
  apply pair_simple
  have h := access_orthogonal sites p q
  rw [access_eq_pair] at h
  exact (h (cellPort 120 p (side p q), variablePosition (signal sites p q))
    (by simp [List.consecutivePairs])).2

/-- Every structured output variable is strictly inside the cell named by its first coordinate.
This includes all gadget variables, not only those selected as access terminals. -/
theorem variablePosition_mem_openCell (v : Variable) :
    realPoint (variablePosition v) ∈ openCell 120 v.1 := by
  rcases v with ⟨p, v⟩
  cases v with
  | none => exact center_mem_openCell (by decide) p
  | some v =>
    rw [variablePosition, Option.elim_some, realPoint_add, add_comm,
      mem_openCell_add_origin_iff]
    have h := Crossover.variable_bounds v
    simp only [realPoint]
    norm_num
    exact_mod_cast (show 0 < (Crossover.variablePosition v).1 ∧
      (Crossover.variablePosition v).1 < 240 ∧ 0 < (Crossover.variablePosition v).2 ∧
      (Crossover.variablePosition v).2 < 240 by omega)

/-- Every translated fixed-gadget incidence stays in the open cell of that gadget. -/
theorem crossingRoute_mem_openCell {e : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c := by
  rw [support_translate] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  rw [mem_openCell_add_origin_iff]
  simpa only [Int.reduceMul, Int.cast_ofNat] using Crossover.core_support_interior he hp

private theorem mem_support_pair {a b : Point} {p : ℝ × ℝ} :
    p ∈ support [a, b] ↔ p ∈ segment a b := by
  rw [support_cons_cons]
  have hs : p ∈ support [b] ↔ p = realPoint b := by
    simp [support, List.consecutivePairs]
  rw [Set.mem_union, hs]
  exact ⟨fun h => h.elim id (fun h => h ▸ _root_.right_mem_segment ℝ _ _), Or.inl⟩

private theorem spoke_boundary_isolation (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support [Crossover.boundaryPort s, (120, 120)]) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (Crossover.boundaryPort s)) := by
  rw [mem_support_pair] at hp
  fin_cases s <;>
    norm_num [Crossover.boundaryPort, Orthogonal.segment, realPoint, mem_horizontal,
      mem_vertical, Set.mem_uIcc] at hp ⊢
  all_goals
    rcases hp with ⟨heq, hlo, hhi⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    intro h
    rcases h with h | h | h | h <;> apply Prod.ext <;> norm_num <;> linarith

private theorem access_eq_translate (sites : List Point) (p q : Point) :
    access sites p q = translate (cellOrigin 120 p)
      (if p ∈ sites then Crossover.accessRoute (side p q)
        else [Crossover.boundaryPort (side p q), (120, 120)]) := by
  by_cases hp : p ∈ sites
  · simp [access, hp]
  · simpa only [hp, ↓reduceIte] using access_eq_spoke hp q

/-- The actual access has no boundary contact except its designated midpoint port. -/
theorem access_support_cell (sites : List Point) (c q : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q)) :
    p ∈ closedCell 120 c ∧
      (p ∈ openCell 120 c ∨ p = realPoint (cellPort 120 c (side c q))) := by
  rw [access_eq_translate, support_translate] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  have hb : 0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (Crossover.boundaryPort (side c q))) := by
    by_cases hc : c ∈ sites
    · simp only [hc, ↓reduceIte] at hp
      exact Crossover.access_boundary_isolation hp
    · simp only [hc, ↓reduceIte] at hp
      exact spoke_boundary_isolation _ hp
  constructor
  · rw [mem_closedCell_add_origin_iff]
    norm_num
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩
  · by_cases h : p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240
    · right
      rw [hb.2.2.2.2 h, cellPort_eq_boundaryPort, realPoint_add, add_comm]
    · left
      rw [mem_openCell_add_origin_iff]
      norm_num
      push Not at h
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h.1), lt_of_le_of_ne hb.2.1 h.2.1,
        lt_of_le_of_ne hb.2.2.1 (Ne.symm h.2.2.1), lt_of_le_of_ne hb.2.2.2.1 h.2.2.2⟩

/-- Access routes from distinct cells can meet only at their two equal designated ports. -/
theorem access_contact_of_distinct_cells (sites otherSites : List Point)
    {c d : Point} (hcd : c ≠ d)
    (a b : Point) {p : ℝ × ℝ}
    (hc : p ∈ support (access sites c a)) (hd : p ∈ support (access otherSites d b)) :
    p = realPoint (cellPort 120 c (side c a)) ∧
      p = realPoint (cellPort 120 d (side d b)) := by
  obtain ⟨hcclosed, hcopen | hcport⟩ := access_support_cell sites c a hc
  · exact False.elim (Set.disjoint_left.mp
      (disjoint_openCell_closedCell (by decide) hcd) hcopen
      (access_support_cell otherSites d b hd).1)
  · refine ⟨hcport, ?_⟩
    obtain ⟨_, hdopen | hdport⟩ := access_support_cell otherSites d b hd
    · exact False.elim (Set.disjoint_left.mp
        (disjoint_openCell_closedCell (by decide) hcd.symm) hdopen hcclosed)
    · exact hdport

private theorem spoke_contact_check : ∀ i j : Fin 4, i ≠ j →
    routeContactCheck [(120, 120)] [Crossover.boundaryPort i, (120, 120)]
      [Crossover.boundaryPort j, (120, 120)] = true := by decide

/-- Distinct sides of an ordinary cell contact only at its signal center. -/
theorem ordinary_access_contact {sites : List Point} {c : Point} (hc : c ∉ sites)
    (a b : Point) (hs : side c a ≠ side c b) {p : ℝ × ℝ}
    (ha : p ∈ support (access sites c a)) (hb : p ∈ support (access sites c b)) :
    p = realPoint (center c) := by
  rw [access_eq_spoke hc, support_translate] at ha
  obtain ⟨p, ha, rfl⟩ := ha
  rw [access_eq_spoke hc] at hb
  have hb' := (mem_support_translate_iff _ _ _).mp hb
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound
    (spoke_contact_check _ _ hs) ha hb'
  have : q = (120, 120) := List.mem_singleton.mp hq
  subst q
  rw [hpq, center, realPoint_add, add_comm]

/-- Distinct access sides of a crossing cell have disjoint real supports. -/
theorem crossing_access_disjoint {sites : List Point} {c : Point} (hc : c ∈ sites)
    (a b : Point) (hs : side c a ≠ side c b) :
    Disjoint (support (access sites c a)) (support (access sites c b)) := by
  rw [Set.disjoint_left]
  intro p ha hb
  simp only [access, hc, ↓reduceIte] at ha hb
  have ha' := (mem_support_translate_iff (cellOrigin 120 c) (Crossover.accessRoute (side c a))
    (p - realPoint (cellOrigin 120 c))).mp
    (by simpa only [sub_add_cancel] using ha)
  have hb' := (mem_support_translate_iff (cellOrigin 120 c) (Crossover.accessRoute (side c b))
    (p - realPoint (cellOrigin 120 c))).mp
    (by simpa only [sub_add_cancel] using hb)
  exact Set.disjoint_left.mp (Crossover.access_disjoint hs) ha' hb'

/-- Compact labels retain the compiler's structured variable order and displayed positions. -/
theorem positions_getD_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    (positions φ).getD ((formula φ).distinctVars.idxOf ((rawFormula φ).vars.idxOf v)) (0, 0) =
      variablePosition v := by
  rw [formula, CNF.idxOf_distinctVars_compact _ hv]
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  rw [positions, List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

private theorem three_simple {a b c : Point} (hn : [a, b, c].Nodup)
    (hc : segmentContactCheck [b] a b b c = true) : IsSimple [a, b, c] := by
  have hcontact : EndpointContacts a b b c := by
    intro p hp hq
    obtain ⟨q, hq, hpq⟩ := segmentContactCheck_sound hc hp hq
    have hqb : q = b := List.mem_singleton.mp hq
    exact ⟨Or.inr (hqb ▸ hpq), Or.inl (hqb ▸ hpq)⟩
  refine ⟨hn, ?_⟩
  intro e he f hf hne
  simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact False.elim (hne rfl)
  · exact hcontact
  · exact hcontact.symm
  · exact False.elim (hne rfl)

private def finalLocalRoute (s : Fin 4) (crossing : Bool) : Route :=
  [2 • Crossover.boundaryPort s - (120, 120), Crossover.boundaryPort s,
    if crossing then Crossover.variablePosition (Crossover.splitTerminal s) else (120, 120)]

private theorem finalLocalRoute_simple (s : Fin 4) (crossing : Bool) :
    IsSimple (finalLocalRoute s crossing) := by
  unfold finalLocalRoute
  apply three_simple
  · fin_cases s <;> cases crossing <;> decide
  · fin_cases s <;> cases crossing <;> decide

private theorem finalLocalRoute_orthogonal (s : Fin 4) (crossing : Bool) :
    IsOrthogonal (finalLocalRoute s crossing) := by
  fin_cases s <;> cases crossing <;>
    norm_num [finalLocalRoute, Crossover.boundaryPort, Crossover.variablePosition,
      Crossover.splitTerminal, IsOrthogonal, List.consecutivePairs, AxisAligned]

private theorem neighbor_center {p q : Point} (h : Orthogonal.length p q = 1) :
    center q = 2 • Crossover.boundaryPort (side p q) - (120, 120) + cellOrigin 120 p := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    norm_num [center, side, Crossover.boundaryPort, cellOrigin, two_nsmul,
      Prod.ext_iff] <;> omega

/-- The final-literal route is a translated straight three-point route for every unit step. -/
private theorem finalRoute_eq_translate (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    center q :: access sites p q = translate (cellOrigin 120 p)
      (finalLocalRoute (side p q) (decide (p ∈ sites))) := by
  rw [neighbor_center h]
  by_cases hp : p ∈ sites <;>
    simp [access, hp, translate, finalLocalRoute, Crossover.accessRoute,
      cellPort_eq_boundaryPort, center, add_comm]

/-- The actual final incidence across a unit step is continuously simple. -/
theorem finalRoute_simple (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) : IsSimple (center q :: access sites p q) := by
  rw [finalRoute_eq_translate sites h, isSimple_translate_iff]
  exact finalLocalRoute_simple _ _

/-- The actual final incidence across a unit step is proper and orthogonal. -/
theorem finalRoute_orthogonal (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) : IsOrthogonal (center q :: access sites p q) := by
  rw [finalRoute_eq_translate sites h, isOrthogonal_translate_iff]
  exact finalLocalRoute_orthogonal _ _

/-- Access length is exactly 20 inside a crossing cell and 120 inside an ordinary cell. -/
theorem access_wireLength (sites : List Point) (p q : Point) :
    wireLength (access sites p q) = if p ∈ sites then 20 else 120 := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, wireLength_translate]
    exact (Crossover.access_route_sizes _).2
  · rw [access_eq_spoke hp, wireLength_translate]
    simp only [hp, ↓reduceIte]
    generalize side p q = s
    fin_cases s <;> decide

/-- A final literal route across one unit step uses at most 240 units of wire. -/
theorem finalRoute_wireLength_le (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    wireLength (center q :: access sites p q) ≤ 240 := by
  rw [finalRoute_eq_translate sites h, wireLength_translate]
  generalize side p q = s
  generalize decide (p ∈ sites) = crossing
  fin_cases s <;> cases crossing <;> decide

/-- A final literal route is the ordinary clause-cell spoke followed by its neighbor's access.
This equality concerns the full real supports and includes the shared boundary midpoint. -/
theorem support_finalRoute (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    support (center q :: access sites p q) =
      support (access [] q p) ∪ support (access sites p q) := by
  rw [access_eq_pair sites p q, access_eq_pair [] q p, support_cons_cons]
  have hs (a b : Point) : support [a, b] = segment a b :=
    Set.ext fun _ => mem_support_pair
  rw [hs (cellPort 120 q (side q p))]
  simp only [signal, List.not_mem_nil, ↓reduceIte, variablePosition, Option.elim_none]
  rw [← shared_cellPort h]
  congr 1
  exact _root_.segment_symm ℝ _ _

/-- The final route starts at its original clause center and ends at the presented signal. -/
theorem finalRoute_endpoints (sites : List Point) (p q : Point) :
    (center q :: access sites p q).head? = some (center q) ∧
      (center q :: access sites p q).getLast? =
        some (variablePosition (signal sites p q)) := by
  rw [access_eq_pair]
  exact ⟨rfl, rfl⟩

/-- The two binary-link incidences are simple actual access routes. -/
theorem link_routes_simple (sites : List Point) (positive : Bool) (p q : Point) :
    ∀ r ∈ (link sites positive p q).2.2, IsSimple r := by
  cases positive <;> simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;>
    exact ⟨access_simple _ _ _, access_simple _ _ _⟩

/-- The two binary-link incidences are proper actual orthogonal access routes. -/
theorem link_routes_orthogonal (sites : List Point) (positive : Bool) (p q : Point) :
    ∀ r ∈ (link sites positive p q).2.2, IsOrthogonal r := by
  cases positive <;> simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;>
    exact ⟨access_orthogonal _ _ _, access_orthogonal _ _ _⟩

/-- Literal and route ordering in an actual binary link gives the declared geometric endpoints. -/
theorem link_endpoints (sites : List Point) (positive : Bool) {p q : Point}
    (h : Orthogonal.length p q = 1) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ (link sites positive p q).1.zip (link sites positive p q).2.2) :
    r.head? = some (link sites positive p q).2.1 ∧
      r.getLast? = some (variablePosition l.1) := by
  cases positive <;>
    simp only [link, Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_right,
      List.mem_cons, List.not_mem_nil, or_false] at hlr ⊢ <;>
    rcases hlr with e | e <;> cases e <;>
    simp [access_eq_pair, ← shared_cellPort h]

/-- An ordinary signal name occurs exactly in an ordinary cell. -/
theorem signal_none_iff (sites : List Point) (p q : Point) :
    (signal sites p q).2 = none ↔ p ∉ sites := by
  simp [signal]

/-- Every variable actually emitted by the compiler has the appropriate cell kind.
In particular, the ordinary center name is never emitted inside a crossover cell. -/
theorem raw_variable_cell_kind (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.2 = none ↔ v.1 ∉ crossingSites φ := by
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, hp, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hv
    obtain ⟨lj, _, rfl⟩ := List.mem_map.mp hlr
    have heq := congrArg Prod.fst hlreq
    simp only [lastLiteral] at heq
    subst v
    exact signal_none_iff _ _ _
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hv
    have heq := congrArg Prod.fst hl
    dsimp only at heq
    subst v
    simp [hp]
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hv <;>
      rcases hv with hv | hv <;>
      have heq := congrArg Prod.fst hv <;> dsimp only at heq <;> subst v <;>
      exact signal_none_iff _ _ _

/-- Actual structured variable names have distinct positions, including across different cells. -/
theorem variablePosition_injOn_rawVars (φ : CNF ℕ) :
    Set.InjOn variablePosition {v | v ∈ (rawFormula φ).vars} := by
  intro v hv w hw heq
  have hreal := congrArg realPoint heq
  have hvcell := variablePosition_mem_openCell v
  have hwcell := variablePosition_mem_openCell w
  rw [← hreal] at hwcell
  have hcell : v.1 = w.1 := cell_eq_of_mem_open_closed (by decide) hvcell
    ⟨hwcell.1.le, hwcell.2.1.le, hwcell.2.2.1.le, hwcell.2.2.2.le⟩
  rcases v with ⟨p, v⟩
  rcases w with ⟨q, w⟩
  change p = q at hcell
  subst q
  have hvkind := raw_variable_cell_kind φ hv
  have hwkind := raw_variable_cell_kind φ hw
  cases v <;> cases w
  · rfl
  · cases hwkind.mpr (hvkind.mp rfl)
  · cases hvkind.mpr (hwkind.mp rfl)
  · simp only [variablePosition, Option.elim_some, add_right_inj] at heq
    exact congrArg (fun x => (p, some x)) (Crossover.variablePosition_injective heq)

private theorem idxOf_range_eq {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

/-- Every route actually emitted by the compiler is proper, orthogonal and continuously simple.
The source degree bounds are needed for global separation, not for this local certificate. -/
theorem routes_regular (φ : CNF ℕ) :
    ∀ r ∈ routes φ, IsOrthogonal r ∧ IsSimple r := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ := by
      exact List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only [lastLiteral] at hlreq
    subst r
    exact ⟨finalRoute_orthogonal _ (occurrencePath_last_unit ho),
      finalRoute_simple _ (occurrencePath_last_unit ho)⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    exact ⟨(isOrthogonal_translate_iff _ _).mpr (Crossover.incidence_orthogonal e he'),
      (isSimple_translate_iff _ _).mpr (Crossover.incidence_isSimple he')⟩
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    exact ⟨link_routes_orthogonal _ _ _ _ r hr, link_routes_simple _ _ _ _ r hr⟩

private theorem crossing_route_count : ∀ i : Fin 74,
    (Crossover.incidenceRoutes.filter fun e => e.1 == i.val).length =
      (Crossover.splitFormula.getD i.val []).length := by decide +kernel

/-- Every actual placed clause supplies exactly one route for each of its literal occurrences. -/
theorem placedClause_route_count (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, pc.2.2.length = pc.1.length := by
  intro pc hpc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    simp
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : ci.2 < 74 := by
      have h := (List.mem_zipIdx hci).2.1
      simpa only [Nat.zero_add, Crossover.length_splitFormula] using h
    have hc := (List.mem_zipIdx hci).2.2
    simp only [Nat.sub_zero] at hc
    have hcount := crossing_route_count ⟨ci.2, hi⟩
    rw [List.getD_eq_getElem Crossover.splitFormula []
      (by simpa only [Crossover.length_splitFormula] using hi)] at hcount
    simpa only [List.length_map, Clause.length_relabel, hc] using hcount
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases o.2.2.2 <;> rfl

/-- The actual route count matches the listed edges of the final compact incidence graph. -/
theorem routes_length (φ : CNF ℕ) :
    (routes φ).length = (SAT.incidenceGraph (formula φ)).2.length := by
  rw [SAT.length_edges_incidenceGraph]
  rw [formula, CNF.compact, CNF.vars_relabel, List.length_map]
  simp only [routes, List.length_flatMap, CNF.vars, List.length_map,
    List.length_flatten, rawFormula, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  exact fun pc hpc => placedClause_route_count φ pc hpc

/-- The actual position list has exactly the final compact graph's declared vertex count. -/
theorem positions_length (φ : CNF ℕ) :
    (positions φ).length = (SAT.incidenceGraph (formula φ)).1.length := by
  simp [positions, SAT.incidenceGraph, formula, CNF.distinctVars_compact, rawFormula]

/-- The final compact output has exactly the same ordered incidence graph as the raw output. -/
theorem incidenceGraph_formula (φ : CNF ℕ) :
    SAT.incidenceGraph (formula φ) = SAT.incidenceGraph (rawFormula φ) :=
  SAT.incidenceGraph_compact _

/-- The actual displayed variable positions have no repetitions. -/
theorem variablePositions_nodup (φ : CNF ℕ) :
    ((rawFormula φ).distinctVars.map variablePosition).Nodup :=
  (CNF.nodup_distinctVars _).map_on (fun _ hv _ hw =>
    variablePosition_injOn_rawVars φ (CNF.mem_distinctVars.mp hv) (CNF.mem_distinctVars.mp hw))

/-- Every geometric side midpoint lies in its own closed real cell. -/
theorem cellPort_mem_closedCell (c : Point) (s : Fin 4) :
    realPoint (cellPort 120 c s) ∈ closedCell 120 c := by
  rw [cellPort_eq_boundaryPort, realPoint_add, add_comm, mem_closedCell_add_origin_iff]
  fin_cases s <;> norm_num [Crossover.boundaryPort, realPoint]

/-- A geometric side midpoint is outside every open cell, including both cells sharing it. -/
theorem cellPort_not_mem_openCell (c d : Point) (s : Fin 4) :
    realPoint (cellPort 120 c s) ∉ openCell 120 d := by
  intro hp
  have heq : d = c := cell_eq_of_mem_open_closed (by decide) hp (cellPort_mem_closedCell c s)
  subst d
  rw [cellPort_eq_boundaryPort, realPoint_add, add_comm, mem_openCell_add_origin_iff] at hp
  fin_cases s <;> norm_num [Crossover.boundaryPort, realPoint] at hp

/-- No binary-link clause position is a variable position, even in a neighboring cell. -/
theorem link_position_ne_variable (sites : List Point) (positive : Bool) (p q : Point)
    (v : Variable) : (link sites positive p q).2.1 ≠ variablePosition v := by
  intro h
  apply cellPort_not_mem_openCell p v.1 (side p q)
  rw [show cellPort 120 p (side p q) = variablePosition v from h]
  exact variablePosition_mem_openCell v

/-- Every translated crossover clause position lies strictly inside its gadget cell. -/
theorem crossingClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) : realPoint pc.2.1 ∈ openCell 120 c := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : ci.2 < Crossover.clausePositions.length := by
    have h := (List.mem_zipIdx hci).2.1
    simpa only [Nat.zero_add, Crossover.length_splitFormula, Crossover.drawing_sizes.1] using h
  have hp : Crossover.clausePositions.getD ci.2 (0, 0) ∈ Crossover.clausePositions := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hb := Crossover.clause_bounds _ hp
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff]
  simp only [realPoint]
  norm_num
  exact_mod_cast (show 0 < (Crossover.clausePositions.getD ci.2 (0, 0)).1 ∧
    (Crossover.clausePositions.getD ci.2 (0, 0)).1 < 240 ∧
      0 < (Crossover.clausePositions.getD ci.2 (0, 0)).2 ∧
      (Crossover.clausePositions.getD ci.2 (0, 0)).2 < 240 by omega)

/-- Original clause positions are pairwise distinct, including repeated and empty clauses. -/
theorem originalPositions_nodup (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun pc => pc.2.1).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [originalClauses, List.getElem_map, List.getElem_zipIdx] at heq
  have hc := center_injective heq
  have hx := congrArg Prod.fst hc
  simp only [Layout.center] at hx
  omega

/-- Each translated crossover keeps the fixed clause-position order. -/
theorem crossingClause_positions (c : Point) :
    (crossingClauses c).map (fun pc => pc.2.1) =
      Crossover.clausePositions.map (cellOrigin 120 c + ·) := by
  apply List.ext_getElem
  · simp [crossingClauses, Crossover.length_splitFormula, Crossover.drawing_sizes.1]
  · intro i hi hj
    simp only [crossingClauses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]

/-- Every crossover has pairwise distinct actual clause positions. -/
theorem crossingClause_positions_nodup (c : Point) :
    ((crossingClauses c).map fun pc => pc.2.1).Nodup := by
  rw [crossingClause_positions]
  exact Crossover.clausePositions_nodup.map (fun _ _ h => add_left_cancel h)

/-- Different selected crossing cells contribute disjoint lists of interior clause positions. -/
theorem crossingPositions_nodup {sites : List Point} (hn : sites.Nodup) :
    ((sites.flatMap crossingClauses).map fun pc => pc.2.1).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun c _ => crossingClause_positions_nodup c, hn.imp ?_⟩
  intro c d hcd p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  have hc := crossingClause_mem_openCell hpc
  have hd := crossingClause_mem_openCell hpd
  rw [heq] at hd
  exact Set.disjoint_left.mp (disjoint_openCell (by decide) hcd) hc hd

/-- Original and crossover clause positions cannot coincide. -/
theorem original_crossing_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      (((crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨c, hc, hpd⟩ := List.mem_flatMap.mp hpd
  have hpos := crossingClause_mem_openCell hpd
  rw [heq] at hpos
  have hcenter := center_mem_openCell (r := 120) (by decide)
    (Layout.center (φ.distinctVars.length + ci.2))
  have hcell := cell_eq_of_mem_open_closed (by decide) hcenter
    ⟨hpos.1.le, hpos.2.1.le, hpos.2.2.1.le, hpos.2.2.2.le⟩
  have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  exact clause_cell_not_mem_crossingSites φ hi (hcell ▸ hc)

private theorem consecutivePairs_dropLast (r : Route) :
    r.dropLast.consecutivePairs = r.consecutivePairs.dropLast := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      cases r with
      | nil => rfl
      | cons c r =>
        simp only [List.dropLast_cons_cons, List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons] at ih ⊢
        exact congrArg ((a, b) :: ·) ih

/-- Binary-clause positions are a sublist of the distinct actual unit-step midpoints. -/
theorem linkPositions_sublist_midpoints (φ : CNF ℕ) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1).Sublist
    ((paths φ).flatMap fun r => r.consecutivePairs.map fun e =>
      cellPort 120 e.1 (side e.1 e.2)) := by
  rw [← occurrencePaths_eq_paths φ, List.flatMap_map]
  simp only [List.map_flatMap, links, List.map_map, Function.comp_def, link]
  apply List.Sublist.flatMap_right
  intro o _
  apply List.Sublist.map
  rw [consecutivePairs_dropLast]
  exact List.dropLast_sublist _

/-- All actual binary-link clauses have distinct positions, including between parallel paths. -/
theorem linkPositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1)).Nodup :=
  (pathMidpoints_nodup hw hv).sublist (linkPositions_sublist_midpoints φ)

private theorem link_position_not_open {sites : List Point} {positive : Bool} {r : Route}
    {pc : PlacedClause} (hpc : pc ∈ links sites positive r) (c : Point) :
    realPoint pc.2.1 ∉ openCell 120 c := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
  exact cellPort_not_mem_openCell _ c _

private theorem original_link_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd (Layout.center (φ.distinctVars.length + ci.2))
  rw [heq]
  exact center_mem_openCell (by decide) _

private theorem crossing_link_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint (((crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨c, _, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd c
  rw [heq]
  exact crossingClause_mem_openCell hpc

/-- All actual output clauses have distinct displayed positions. Boundary clauses, interior
crossover clauses and original source clauses are separated in the full real-cell geometry. -/
theorem clausePositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((placedClauses φ).map fun pc => pc.2.1).Nodup := by
  simp only [placedClauses, List.map_append]
  apply List.Nodup.append
  · exact (originalPositions_nodup φ _).append
      (crossingPositions_nodup (crossingSites_nodup φ)) (original_crossing_positions_disjoint φ)
  · exact linkPositions_nodup hw hv
  · intro p hp hq
    rcases List.mem_append.mp hp with hp | hp
    · exact original_link_positions_disjoint φ hp hq
    · exact crossing_link_positions_disjoint φ hp hq

private theorem penultimate_mem_dropLast {r : Route} (h : 2 ≤ r.length) :
    r.getD (r.length - 2) (0, 0) ∈ r.dropLast := by
  have hk : r.length - 2 < r.dropLast.length := by simp only [List.length_dropLast]; omega
  rw [List.getD_eq_getElem _ _ (by omega), ← List.getElem_dropLast hk]
  exact List.getElem_mem hk

/-- Every emitted variable cell is a selected crossing or lies before the final clause point
of an actual source occurrence path. -/
theorem raw_variable_cell_membership (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.1 ∈ crossingSites φ ∨ ∃ o ∈ Cslib.Logic.PL.occurrences φ,
      v.1 ∈ (occurrencePath φ o).dropLast := by
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, hp, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hv
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    have heq := congrArg Prod.fst hlreq
    dsimp only [lastLiteral] at heq
    subst v
    exact Or.inr ⟨_, ho, penultimate_mem_dropLast (occurrencePath_length_ge_two ho)⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hv
    have heq := congrArg Prod.fst hl
    dsimp only at heq
    subst v
    exact Or.inl hp
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hv <;>
      rcases hv with hv | hv <;>
      have heq := congrArg Prod.fst hv <;> dsimp only at heq <;> subst v
    all_goals first
      | exact Or.inr ⟨o, ho, (List.of_mem_zip he).1⟩
      | exact Or.inr ⟨o, ho, List.mem_of_mem_tail (List.of_mem_zip he).2⟩

/-- Actual output variables never occupy a source clause cell. -/
theorem raw_variable_not_clause_cell {φ : CNF ℕ} {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) {i : ℕ} (hi : i < φ.length) :
    v.1 ≠ Layout.center (φ.distinctVars.length + i) := by
  intro h
  rcases raw_variable_cell_membership φ hv with hsite | ⟨o, ho, hp⟩
  · exact clause_cell_not_mem_crossingSites φ hi (h ▸ hsite)
  · exact clause_cell_not_mem_path_dropLast ho hi (h ▸ hp)

private theorem crossing_position_ne_raw_variable {φ : CNF ℕ} {c : Point}
    (hc : c ∈ crossingSites φ) {pc : PlacedClause} (hpc : pc ∈ crossingClauses c)
    {v : Variable} (hv : v ∈ (rawFormula φ).vars) : pc.2.1 ≠ variablePosition v := by
  intro hpos
  have hpcopen := crossingClause_mem_openCell hpc
  have hvopen := variablePosition_mem_openCell v
  rw [hpos] at hpcopen
  have hcell : c = v.1 := cell_eq_of_mem_open_closed (by decide) hpcopen
    ⟨hvopen.1.le, hvopen.2.1.le, hvopen.2.2.1.le, hvopen.2.2.2.le⟩
  rcases v with ⟨p, v⟩
  change c = p at hcell
  subst p
  cases v with
  | none => exact (raw_variable_cell_kind φ hv).mp rfl hc
  | some v =>
    have hmem : pc.2.1 ∈ (crossingClauses c).map (fun pc => pc.2.1) :=
      List.mem_map_of_mem hpc
    rw [crossingClause_positions] at hmem
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
    have heq' : q = Crossover.variablePosition v := add_left_cancel (heq.trans hpos)
    exact Crossover.variablePosition_not_mem_clauses v (heq' ▸ hq)

/-- The actual variable and clause position lists are disjoint. This includes empty original
clauses and excludes variable vertices from all binary-clause boundary positions. -/
theorem variable_clause_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((rawFormula φ).distinctVars.map variablePosition)
      ((placedClauses φ).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  have hv' := CNF.mem_distinctVars.mp hv
  obtain ⟨pc, hpc, hpos⟩ := List.mem_map.mp hq
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨c, hc, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    dsimp only at hpos
    have hcenter := center_mem_openCell (r := 120) (by decide)
      (Layout.center (φ.distinctVars.length + i))
    change realPoint (center (Layout.center (φ.distinctVars.length + i))) ∈ _ at hcenter
    rw [hpos] at hcenter
    have hvopen := variablePosition_mem_openCell v
    have hcell : Layout.center (φ.distinctVars.length + i) = v.1 :=
      cell_eq_of_mem_open_closed (by decide) hcenter
        ⟨hvopen.1.le, hvopen.2.1.le, hvopen.2.2.1.le, hvopen.2.2.2.le⟩
    have hi : i < φ.length := by
      simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    exact raw_variable_not_clause_cell hv' hi hcell.symm
  · exact crossing_position_ne_raw_variable hc hpc hv' hpos
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    exact link_position_ne_variable _ _ _ _ v hpos

/-- All actual displayed output vertices have distinct integer positions. -/
theorem positions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (positions φ).Nodup :=
  (variablePositions_nodup φ).append (clausePositions_nodup hw hv)
    (variable_clause_positions_disjoint φ)

private theorem originalClause_endpoints {φ : CNF ℕ} {sites : List Point}
    {pc : PlacedClause} (hpc : pc ∈ originalClauses φ sites)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  dsimp only at hlr ⊢
  rw [← List.zip_of_prod rfl rfl] at hlr
  obtain ⟨⟨sourceLiteral, j⟩, hlj, heq⟩ := List.mem_map.mp hlr
  have ho : (i, j, sourceLiteral) ∈ Cslib.Logic.PL.occurrences φ :=
    List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨(sourceLiteral, j), hlj, rfl⟩⟩
  dsimp only [lastLiteral] at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hlast : (occurrencePath φ (i, j, sourceLiteral)).getLastD (0, 0) =
      Layout.center (φ.distinctVars.length + i) := by
    rw [List.getLastD_eq_getLast?, (occurrencePath_endpoints ho).2]
    rfl
  simpa only [hlast] using finalRoute_endpoints sites
    ((occurrencePath φ (i, j, sourceLiteral)).getD
      ((occurrencePath φ (i, j, sourceLiteral)).length - 2) (0, 0))
    ((occurrencePath φ (i, j, sourceLiteral)).getLastD (0, 0))

private theorem crossing_literal_routes_cover : ∀ i : Fin 74,
    ((Crossover.splitFormula.getD i.val []).zip
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2)).all
        (fun lr => decide ((i.val, lr.1.1, lr.2) ∈ Crossover.incidenceRoutes)) = true := by
  decide +kernel

private theorem crossingClause_endpoints {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < 74 := by
    simpa only [Nat.zero_add, Crossover.length_splitFormula] using (List.mem_zipIdx hci).2.1
  have hc : sourceClause = Crossover.splitFormula.getD i [] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [Crossover.length_splitFormula] using hi)]
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2
  change (l, r) ∈
    (sourceClause.map (Prod.map (fun v => (c, some v)) id)).zip
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map
        (fun e => translate (cellOrigin 120 c) e.2.2)) at hlr
  have hmap : ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) =
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map fun e => e.2.2).map
        (translate (cellOrigin 120 c)) := by rw [List.map_map]; rfl
  rw [hmap, List.zip_map] at hlr
  obtain ⟨⟨oldLiteral, oldRoute⟩, hold, heq⟩ := List.mem_map.mp hlr
  rw [hc] at hold
  have he : (i, oldLiteral.1, oldRoute) ∈ Crossover.incidenceRoutes :=
    of_decide_eq_true (List.all_eq_true.mp (crossing_literal_routes_cover ⟨i, hi⟩) _ hold)
  change (((c, some oldLiteral.1), oldLiteral.2),
    translate (cellOrigin 120 c) oldRoute) = (l, r) at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hend := Crossover.incidence_endpoints _ he
  constructor
  · simp only [translate, List.head?_map, hend.2.1, Option.map_some]
    congr 1
    exact add_comm _ _
  · simp only [translate, List.getLast?_map, hend.2.2, Option.map_some,
      variablePosition, Option.elim_some]
    congr 1
    exact add_comm _ _

/-- Every literal/route pair in every actual placed clause has the declared endpoints.
The statement retains literal order, including all original repeated literal occurrences. -/
theorem placedClause_endpoints (φ : CNF ℕ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨_, _, hpc⟩) | ⟨o, ho, hpc⟩
  · exact originalClause_endpoints hpc hlr
  · exact crossingClause_endpoints hpc hlr
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    have he' : e ∈ (occurrencePath φ o).consecutivePairs := by
      rw [consecutivePairs_dropLast] at he
      exact (List.dropLast_sublist _).subset he
    exact link_endpoints _ _ (occurrencePath_unit ho he') hlr

private theorem positions_getD_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    (positions φ).getD ((rawFormula φ).distinctVars.idxOf v) (0, 0) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  rw [positions, List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

/-- The graph's actual variable vertex index resolves to its emitted structured position. -/
theorem drawingPosition_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.idxOf v) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.idxOf v))
    (0, 0) = _
  rw [idxOf_range_eq (by omega)]
  exact positions_getD_raw_variable φ hv

/-- The graph's actual clause vertex index resolves to the placed clause at that index. -/
theorem drawingPosition_raw_clause (φ : CNF ℕ) {i : ℕ} (hi : i < (placedClauses φ).length) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.length + i) = ((placedClauses φ)[i]).2.1 := by
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.length + i))
    (0, 0) = _
  have hlen : (rawFormula φ).length = (placedClauses φ).length := by
    simp only [rawFormula, List.length_map]
  rw [idxOf_range_eq (by omega), positions,
    List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]

private theorem forall₂_flatMap_same {A B C : Type*} {R : B → C → Prop}
    (xs : List A) (f : A → List B) (g : A → List C)
    (h : ∀ a ∈ xs, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a xs ih =>
    exact List.rel_append (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem map_zipIdx_ignore {A B : Type*} (xs : List A) (f : A → B) :
    (xs.zipIdx.map fun a => f a.1) = xs.map f := by
  calc
    _ = (xs.zipIdx.map Prod.fst).map f := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]

private theorem raw_edges_eq (φ : CNF ℕ) :
    (SAT.incidenceGraph (rawFormula φ)).2 =
      (placedClauses φ).zipIdx.flatMap fun pci => pci.1.1.map fun l =>
        ((rawFormula φ).distinctVars.idxOf l.1, (rawFormula φ).distinctVars.length + pci.2) := by
  simp only [SAT.incidenceGraph, Cslib.Logic.PL.occurrences, rawFormula, List.zipIdx_map,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, List.idxOf, beq_eq_decide]
  congr 1
  funext pci
  simpa only [rawFormula, List.idxOf, beq_eq_decide] using
    map_zipIdx_ignore pci.1.1 (fun l =>
      ((rawFormula φ).distinctVars.idxOf l.1, (rawFormula φ).distinctVars.length + pci.2))

private theorem raw_routes_eq (φ : CNF ℕ) :
    routes φ = (placedClauses φ).zipIdx.flatMap (fun pci => pci.1.2.2) := by
  calc
    _ = ((placedClauses φ).zipIdx.map Prod.fst).flatMap (fun pc => pc.2.2) := by
      rw [List.zipIdx_map_fst]
      rfl
    _ = _ := by rw [List.flatMap_map]

private theorem raw_routes_endpoints (φ : CNF ℕ) :
    List.Forall₂ (fun e r =>
      r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.2) ∧
      r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.1))
      (SAT.incidenceGraph (rawFormula φ)).2 (routes φ) := by
  rw [raw_edges_eq, raw_routes_eq]
  apply forall₂_flatMap_same
  intro pci hpci
  rcases pci with ⟨pc, i⟩
  have hpc := List.fst_mem_of_mem_zipIdx hpci
  have hi : i < (placedClauses φ).length := by
    simpa only [Nat.zero_add] using (List.mem_zipIdx hpci).2.1
  have hget : pc = (placedClauses φ)[i] := by
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hpci).2.2
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_iff_zip.mpr
  refine ⟨(placedClause_route_count φ pc hpc).symm, ?_⟩
  intro l r hlr
  have hends := placedClause_endpoints φ hpc hlr
  have hvar : l.1 ∈ (rawFormula φ).vars := by
    exact CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, l.2, (List.of_mem_zip hlr).1⟩
  change r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.length + i)) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.idxOf l.1))
  rw [drawingPosition_raw_clause φ hi, drawingPosition_raw_variable φ hvar, ← hget]
  exact hends

/-- Every actual indexed route has its actual incident graph vertices as endpoints, in
clause-to-variable order. Compaction and repeated edge occurrences preserve that order. -/
theorem routes_endpoints (φ : CNF ℕ) {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    let r := (routes φ).getD i []
    r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].2) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].1) := by
  simp only [incidenceGraph_formula] at hi ⊢
  have hir : i < (routes φ).length := by
    rwa [routes_length, incidenceGraph_formula]
  have h := (raw_routes_endpoints φ).get hi hir
  simpa only [List.get_eq_getElem, List.getD_eq_getElem _ _ hir] using h

private theorem access_variable_contact {sites : List Point} {c q : Point} {v : Variable}
    (hkind : v.2 = none ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈ support (access sites c q)) :
    v = signal sites c q := by
  have hcell : v.1 = c := cell_eq_of_mem_open_closed (by decide)
    (variablePosition_mem_openCell v) (access_support_cell sites c q hp).1
  rcases v with ⟨a, v⟩
  change a = c at hcell
  subst a
  by_cases hc : c ∈ sites
  · cases v with
    | none => exact False.elim (hkind.mp rfl hc)
    | some v =>
      simp only [access, hc, ↓reduceIte, variablePosition, Option.elim_some,
        realPoint_add, add_comm (realPoint (cellOrigin 120 c))] at hp
      have hp' := (mem_support_translate_iff _ _ _).mp hp
      have hv : v = Crossover.splitTerminal (side c q) := by
        by_contra h
        exact Crossover.access_variable_not_mem h hp'
      simp [signal, hc, hv]
  · have hv := hkind.mpr hc
    simp only at hv
    subst v
    simp [signal, hc]

private theorem core_variable_contact {sites : List Point} {c : Point}
    (hc : c ∈ sites) {e : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) {v : Variable}
    (hkind : v.2 = none ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈
      support (translate (cellOrigin 120 c) e.2.2)) : v = (c, some e.2.1) := by
  have hcell : c = v.1 := cell_eq_of_mem_open_closed (by decide)
    (crossingRoute_mem_openCell he c hp)
    (let h := variablePosition_mem_openCell v
     ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩)
  rcases v with ⟨a, v⟩
  change c = a at hcell
  subst a
  cases v with
  | none => exact False.elim (hkind.mp rfl hc)
  | some v =>
    simp only [variablePosition, Option.elim_some, realPoint_add,
      add_comm (realPoint (cellOrigin 120 c))] at hp
    have hp' := (mem_support_translate_iff _ _ _).mp hp
    have hv : v = e.2.1 := by
      by_contra h
      exact Crossover.variable_not_mem_support he h hp'
    exact congrArg (fun v => (c, some v)) hv

/-- An actual route can meet a displayed variable only at its variable endpoint. -/
theorem route_variable_contact (φ : CNF ℕ) {r : Route} (hr : r ∈ routes φ)
    {v : Variable} (hv : v ∈ (rawFormula φ).vars)
    (hp : realPoint (variablePosition v) ∈ support r) :
    r.getLast? = some (variablePosition v) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨c, hc, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨⟨l, j⟩, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (i, j, l) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨(l, j), hlj, rfl⟩⟩
    dsimp only [lastLiteral] at heq
    subst r
    rw [support_finalRoute _ (occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · have hcell : v.1 = (occurrencePath φ (i, j, l)).getLastD (0, 0) :=
        cell_eq_of_mem_open_closed (by decide) (variablePosition_mem_openCell v)
          (access_support_cell [] _ _ hp).1
      have hend := (occurrencePath_endpoints ho).2
      rw [List.getLastD_eq_getLast?, hend] at hcell
      have hi : i < φ.length := by
        simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
      exact False.elim (raw_variable_not_clause_cell hv hi hcell)
    · have heq := access_variable_contact (raw_variable_cell_kind φ hv) hp
      exact heq ▸ (finalRoute_endpoints _ _ _).2
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    have heq := core_variable_contact hc he' (raw_variable_cell_kind φ hv) hp
    subst v
    simp only [translate, List.getLast?_map, (Crossover.incidence_endpoints _ he').2.2,
      Option.map_some, variablePosition, Option.elim_some, add_comm]
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl <;>
      have heq := access_variable_contact (raw_variable_cell_kind φ hv) hp <;>
      rw [heq, access_eq_pair] <;> rfl

private def lastStep (r : Route) : Point × Point :=
  (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0))

private theorem lastStep_mem {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∈ (occurrencePath φ o).consecutivePairs := by
  let r := occurrencePath φ o
  have hlen : 2 ≤ r.length := occurrencePath_length_ge_two ho
  have hk : r.length - 2 < r.consecutivePairs.length := by
    simp only [List.consecutivePairs, List.length_zip, List.length_tail]
    omega
  have heq : r.consecutivePairs[r.length - 2] = lastStep r := by
    simp only [List.consecutivePairs, List.getElem_zip, List.getElem_tail, lastStep]
    rw [List.getD_eq_getElem _ _ (by omega), List.getLastD_eq_getLast?,
      List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    congr 1
    omega
  rw [← heq]
  exact List.getElem_mem hk

private theorem occurrence_step_unique {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {e f : Point × Point}
    (he : e ∈ (occurrencePath φ o).consecutivePairs)
    (hf : f ∈ (occurrencePath φ t).consecutivePairs)
    (h : cellPort 120 e.1 (side e.1 e.2) = cellPort 120 f.1 (side f.1 f.2)) :
    o = t ∧ e = f := by
  let mids := fun o => (occurrencePath φ o).consecutivePairs.map fun e =>
    cellPort 120 e.1 (side e.1 e.2)
  have hn : ((Cslib.Logic.PL.occurrences φ).flatMap mids).Nodup := by
    simpa only [← occurrencePaths_eq_paths φ, List.flatMap_map] using
      pathMidpoints_nodup hw hv
  have houter := (List.nodup_flatMap.mp hn).2
  have hme : cellPort 120 e.1 (side e.1 e.2) ∈ mids o := List.mem_map_of_mem he
  have hmf : cellPort 120 e.1 (side e.1 e.2) ∈ mids t := h ▸ List.mem_map_of_mem hf
  have hot : o = t := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ho
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ht
    rcases Nat.lt_trichotomy i j with hij | rfl | hji
    · exact False.elim ((List.pairwise_iff_getElem.mp houter i j hi hj hij) hme hmf)
    · rfl
    · exact False.elim ((List.pairwise_iff_getElem.mp houter j i hj hi hji) hmf hme)
  refine ⟨hot, ?_⟩
  subst t
  have hlocal := (List.nodup_flatMap.mp hn).1 o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
  have hi' : i < (mids o).length := by simpa only [mids, List.length_map] using hi
  have hj' : j < (mids o).length := by simpa only [mids, List.length_map] using hj
  have hij := hlocal.eq_of_getElem_eq hi' hj' (by simpa only [mids, List.getElem_map] using h)
  subst j
  rfl

private theorem lastStep_not_prefix {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∉ (occurrencePath φ o).dropLast.consecutivePairs := by
  intro he
  have hp : (occurrencePath φ o).getLastD (0, 0) ∈ (occurrencePath φ o).dropLast :=
    List.mem_of_mem_tail (List.of_mem_zip he).2
  rw [List.getLastD_eq_getLast?, (occurrencePath_endpoints ho).2] at hp
  exact clause_cell_not_mem_path_dropLast ho (Cslib.Logic.PL.mem_occurrences.mp ho).1 hp

private def RouteEnd (r : Route) (a : Point) : Prop :=
  r.head? = some a ∨ r.getLast? = some a

private inductive AccessPiece (φ : CNF ℕ) : Route → Point → Point → Prop where
  | link {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
      (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) :
      AccessPiece φ (access (crossingSites φ) e.1 e.2) e.1 e.2
  | reverseLink {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
      {e : Point × Point} (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) :
      AccessPiece φ (access (crossingSites φ) e.2 e.1) e.2 e.1
  | finalIn {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      AccessPiece φ
        (center (lastStep (occurrencePath φ o)).2 ::
          access (crossingSites φ) (lastStep (occurrencePath φ o)).1
            (lastStep (occurrencePath φ o)).2)
        (lastStep (occurrencePath φ o)).1 (lastStep (occurrencePath φ o)).2
  | finalOut {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      AccessPiece φ
        (center (lastStep (occurrencePath φ o)).2 ::
          access (crossingSites φ) (lastStep (occurrencePath φ o)).1
            (lastStep (occurrencePath φ o)).2)
        (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1

private theorem prefixStep_mem {φ : CNF ℕ} {o : Occurrence ℕ} {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) :
    e ∈ (occurrencePath φ o).consecutivePairs := by
  rw [consecutivePairs_dropLast] at he
  exact (List.dropLast_sublist _).subset he

private theorem lastStep_target_not_crossing {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (lastStep (occurrencePath φ o)).2 ∉ crossingSites φ := by
  change (occurrencePath φ o).getLastD (0, 0) ∉ crossingSites φ
  rw [List.getLastD_eq_getLast?, (occurrencePath_endpoints ho).2]
  exact clause_cell_not_mem_crossingSites φ (Cslib.Logic.PL.mem_occurrences.mp ho).1

private theorem AccessPiece.inner_endpoint {φ : CNF ℕ} {r : Route} {c q : Point}
    (h : AccessPiece φ r c q) : RouteEnd r (variablePosition (signal (crossingSites φ) c q)) := by
  cases h with
  | link ho he => exact Or.inr (by rw [access_eq_pair]; rfl)
  | reverseLink ho he => exact Or.inr (by rw [access_eq_pair]; rfl)
  | finalIn ho => exact Or.inr (finalRoute_endpoints _ _ _).2
  | finalOut ho =>
    exact Or.inl (by simp [signal, lastStep_target_not_crossing ho, variablePosition, center])

private theorem AccessPiece.source {φ : CNF ℕ} {r : Route} {c q : Point}
    (h : AccessPiece φ r c q) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, ∃ e ∈ (occurrencePath φ o).consecutivePairs,
      cellPort 120 c (side c q) = cellPort 120 e.1 (side e.1 e.2) ∧
      ((e ∈ (occurrencePath φ o).dropLast.consecutivePairs ∧
          r = access (crossingSites φ) c q) ∨
        (e = lastStep (occurrencePath φ o) ∧
          r = center e.2 :: access (crossingSites φ) e.1 e.2)) := by
  cases h with
  | link ho he => exact ⟨_, ho, _, prefixStep_mem he, rfl, Or.inl ⟨he, rfl⟩⟩
  | reverseLink ho he =>
    exact ⟨_, ho, _, prefixStep_mem he,
      (shared_cellPort (occurrencePath_unit ho (prefixStep_mem he))).symm,
      Or.inl ⟨he, rfl⟩⟩
  | finalIn ho => exact ⟨_, ho, _, lastStep_mem ho, rfl, Or.inr ⟨rfl, rfl⟩⟩
  | finalOut ho =>
    exact ⟨_, ho, _, lastStep_mem ho, (shared_cellPort (occurrencePath_last_unit ho)).symm,
      Or.inr ⟨rfl, rfl⟩⟩

private theorem accessPieces_same_port {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} (hr : AccessPiece φ r c q) (hs : AccessPiece φ s d t)
    (h : cellPort 120 c (side c q) = cellPort 120 d (side d t)) :
    (r = access (crossingSites φ) c q ∧ s = access (crossingSites φ) d t) ∨ r = s := by
  obtain ⟨o, ho, e, he, hport, hr⟩ := hr.source
  obtain ⟨u, hu, f, hf, hport', hs⟩ := hs.source
  obtain ⟨rfl, rfl⟩ := occurrence_step_unique hw hv ho hu he hf
    (hport.symm.trans (h.trans hport'))
  rcases hr with ⟨hprefix, hr⟩ | ⟨hfinal, hr⟩ <;>
    rcases hs with ⟨hprefix', hs⟩ | ⟨hfinal', hs⟩
  · exact Or.inl ⟨hr, hs⟩
  · exact False.elim (lastStep_not_prefix ho (hfinal' ▸ hprefix))
  · exact False.elim (lastStep_not_prefix ho (hfinal ▸ hprefix'))
  · exact Or.inr (hr.trans hs.symm)

private theorem route_support_cases {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {p : ℝ × ℝ} (hp : p ∈ support r) :
    (∃ c ∈ crossingSites φ, ∃ e ∈ Crossover.incidenceRoutes,
      r = translate (cellOrigin 120 c) e.2.2) ∨
      ∃ c q, AccessPiece φ r c q ∧ p ∈ support (access (crossingSites φ) c q) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨c, hc, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only [lastLiteral] at heq
    subst r
    rw [support_finalRoute _ (occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · have heq : access [] (lastStep (occurrencePath φ (ci.2, lj.2, lj.1))).2
          (lastStep (occurrencePath φ (ci.2, lj.2, lj.1))).1 =
        access (crossingSites φ) (lastStep (occurrencePath φ (ci.2, lj.2, lj.1))).2
          (lastStep (occurrencePath φ (ci.2, lj.2, lj.1))).1 := by
        simp [access, lastStep_target_not_crossing ho]
      exact Or.inr ⟨_, _, AccessPiece.finalOut ho, heq ▸ hp⟩
    · exact Or.inr ⟨_, _, AccessPiece.finalIn ho, hp⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨c, hc, e, (List.mem_filter.mp he).1, rfl⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
    all_goals first
      | exact Or.inr ⟨_, _, AccessPiece.link ho he, hp⟩
      | exact Or.inr ⟨_, _, AccessPiece.reverseLink ho he, hp⟩

private theorem accessPieces_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} (hr : AccessPiece φ r c q) (hs : AccessPiece φ s d t)
    (hne : r ≠ s) {p : ℝ × ℝ}
    (hp : p ∈ support (access (crossingSites φ) c q))
    (hq : p ∈ support (access (crossingSites φ) d t)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  by_cases hcd : c = d
  · subst d
    by_cases hside : side c q = side c t
    · have hport : cellPort 120 c (side c q) = cellPort 120 c (side c t) := congrArg _ hside
      rcases accessPieces_same_port hw hv hr hs hport with ⟨hr', hs'⟩ | heq
      · apply False.elim
        apply hne
        rw [hr', hs', access_eq_pair, access_eq_pair]
        simp only [signal, hside]
      · exact False.elim (hne heq)
    · by_cases hc : c ∈ crossingSites φ
      · exact False.elim (Set.disjoint_left.mp (crossing_access_disjoint hc q t hside) hp hq)
      · have hp' := ordinary_access_contact hc q t hside hp hq
        refine ⟨center c, hp', ?_, ?_⟩
        · simpa only [signal, hc, ↓reduceIte, variablePosition, Option.elim_none, center] using
            hr.inner_endpoint
        · simpa only [signal, hc, ↓reduceIte, variablePosition, Option.elim_none, center] using
            hs.inner_endpoint
  · have hcontact := access_contact_of_distinct_cells (crossingSites φ) (crossingSites φ)
      hcd q t hp hq
    have hport := realPoint_injective (hcontact.1.symm.trans hcontact.2)
    rcases accessPieces_same_port hw hv hr hs hport with ⟨hr', hs'⟩ | heq
    · refine ⟨cellPort 120 c (side c q), hcontact.1, Or.inl ?_, Or.inl ?_⟩
      · rw [hr', access_eq_pair]; rfl
      · rw [hs', access_eq_pair, ← hport]; rfl
    · exact False.elim (hne heq)

private theorem RouteEnd.translate {r : Route} {a : Point} (h : RouteEnd r a) (v : Point) :
    RouteEnd (translate v r) (a + v) := by
  rcases h with h | h
  · exact Or.inl (by simp only [Orthogonal.translate, List.head?_map, h, Option.map_some])
  · exact Or.inr (by simp only [Orthogonal.translate, List.getLast?_map, h, Option.map_some])

private theorem core_local_contact {e f : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) (hf : f ∈ Crossover.incidenceRoutes) (hne : e ≠ f)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support f.2.2) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd e.2.2 a ∧ RouteEnd f.2.2 a := by
  obtain ⟨a, ha, hpa⟩ := Crossover.routes_contact he hf hne hp hq
  refine ⟨a, hpa, ?_⟩
  simp only [Crossover.commonEndpoints, List.mem_append] at ha
  rcases ha with ha | ha
  · split_ifs at ha with hclause
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨Or.inl (Crossover.incidence_endpoints _ he).2.1,
        Or.inl (by simpa only [hclause] using (Crossover.incidence_endpoints _ hf).2.1)⟩
    · exact False.elim (List.not_mem_nil ha)
  · split_ifs at ha with hvar
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨Or.inr (Crossover.incidence_endpoints _ he).2.2,
        Or.inr (by simpa only [hvar] using (Crossover.incidence_endpoints _ hf).2.2)⟩
    · exact False.elim (List.not_mem_nil ha)

private theorem core_core_contact {c d : Point} {e f : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) (hf : f ∈ Crossover.incidenceRoutes)
    (hne : translate (cellOrigin 120 c) e.2.2 ≠ translate (cellOrigin 120 d) f.2.2)
    {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2))
    (hq : p ∈ support (translate (cellOrigin 120 d) f.2.2)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd (translate (cellOrigin 120 c) e.2.2) a ∧
      RouteEnd (translate (cellOrigin 120 d) f.2.2) a := by
  have hpc := crossingRoute_mem_openCell he c hp
  have hqc := crossingRoute_mem_openCell hf d hq
  have hcd : c = d := cell_eq_of_mem_open_closed (by decide) hpc
    ⟨hqc.1.le, hqc.2.1.le, hqc.2.2.1.le, hqc.2.2.2.le⟩
  subst d
  have hef : e ≠ f := fun h => hne (h ▸ rfl)
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hp' : x ∈ support e.2.2 :=
    (mem_support_translate_iff _ _ _).mp (hx ▸ hp)
  have hq' : x ∈ support f.2.2 :=
    (mem_support_translate_iff _ _ _).mp (hx ▸ hq)
  obtain ⟨a, hxa, ha, hb⟩ := core_local_contact he hf hef hp' hq'
  refine ⟨a + cellOrigin 120 c, ?_, ha.translate _, hb.translate _⟩
  rw [realPoint_add, ← hxa, hx]

private theorem core_access_contact {φ : CNF ℕ} {r : Route} {c d q : Point}
    (hc : c ∈ crossingSites φ) {e : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) (hr : AccessPiece φ r d q)
    {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2))
    (hq : p ∈ support (access (crossingSites φ) d q)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd (translate (cellOrigin 120 c) e.2.2) a ∧
      RouteEnd r a := by
  have hcd : c = d := cell_eq_of_mem_open_closed (by decide)
    (crossingRoute_mem_openCell he c hp) (access_support_cell _ _ _ hq).1
  subst d
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hp' : x ∈ support e.2.2 :=
    (mem_support_translate_iff _ _ _).mp (hx ▸ hp)
  have hq' : x ∈ support (Crossover.accessRoute (side c q)) := by
    apply (mem_support_translate_iff (cellOrigin 120 c) _ _).mp
    simpa only [access, hc, ↓reduceIte, hx] using hq
  obtain ⟨hevar, hxp⟩ := Crossover.access_contact he hq' hp'
  refine ⟨variablePosition (signal (crossingSites φ) c q), ?_, ?_, hr.inner_endpoint⟩
  · simp only [signal, hc, ↓reduceIte, variablePosition, Option.elim_some, realPoint_add]
    rw [← hxp, add_comm, hx]
  · have hend : RouteEnd e.2.2 (Crossover.variablePosition (Crossover.splitTerminal (side c q))) :=
      Or.inr (by simpa only [hevar] using (Crossover.incidence_endpoints _ he).2.2)
    simpa only [signal, hc, ↓reduceIte, variablePosition, Option.elim_some, add_comm] using
      hend.translate (cellOrigin 120 c)

/-- Distinct actual routes meet only at endpoints of both routes, over the complete real plane.
The proof uses actual unit-step ownership, including the omitted final binary link. -/
theorem route_contacts {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} (hr : r ∈ routes φ) (hs : s ∈ routes φ) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ a : Point, p = realPoint a ∧
      (r.head? = some a ∨ r.getLast? = some a) ∧
      (s.head? = some a ∨ s.getLast? = some a) := by
  rcases route_support_cases hr hp with ⟨c, hc, e, he, rfl⟩ | ⟨c, q, hr', hp'⟩
  · rcases route_support_cases hs hq with ⟨d, _, f, hf, rfl⟩ | ⟨d, t, hs', hq'⟩
    · exact core_core_contact he hf hne hp hq
    · exact core_access_contact hc he hs' hp hq'
  · rcases route_support_cases hs hq with ⟨d, hd, f, hf, rfl⟩ | ⟨d, t, hs', hq'⟩
    · obtain ⟨a, hpa, hfend, hrend⟩ := core_access_contact hd hf hr' hq hp'
      exact ⟨a, hpa, hrend, hfend⟩
    · exact accessPieces_contact hw hv hr' hs' hne hp' hq'

private theorem lastLiteral_route_injective {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {b b' : Bool}
    (h : (lastLiteral (crossingSites φ) (occurrencePath φ o) b).2 =
      (lastLiteral (crossingSites φ) (occurrencePath φ t) b').2) : o = t := by
  have hmid := congrArg (fun r : Route => r.getD 1 (0, 0)) h
  simp only [lastLiteral, access_eq_pair, List.getD_cons_succ,
    List.getD_cons_zero] at hmid
  exact (occurrence_step_unique hw hv ho ht (lastStep_mem ho) (lastStep_mem ht) hmid).1

private theorem originalClause_routes_nodup_at {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {c : Clause ℕ} {i : ℕ} (hci : (c, i) ∈ φ.zipIdx) :
    ((c.zipIdx.map fun lj =>
      lastLiteral (crossingSites φ) (occurrencePath φ (i, lj.2, lj.1)) lj.1.2).map
        Prod.snd).Nodup := by
  rw [List.map_map]
  have hn : c.zipIdx.Nodup := by
    apply List.Nodup.of_map Prod.snd
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  apply hn.map_on
  intro lj hlj mk hmk heq
  have ho : (i, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
    List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
  have ht : (i, mk.2, mk.1) ∈ Cslib.Logic.PL.occurrences φ :=
    List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨mk, hmk, rfl⟩⟩
  have hot := lastLiteral_route_injective hw hv ho ht (b := lj.1.2) (b' := mk.1.2) heq
  have hjl := Prod.mk.inj (Prod.mk.inj hot).2
  exact Prod.ext hjl.2 hjl.1

private theorem originalClause_routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {pc : PlacedClause} (hpc : pc ∈ originalClauses φ (crossingSites φ)) : pc.2.2.Nodup := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  exact originalClause_routes_nodup_at hw hv hci

private theorem crossing_routes_nodup_check : ∀ i : Fin 74,
    ((Crossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2).Nodup := by
  decide +kernel

private theorem crossingClause_routes_nodup {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) : pc.2.2.Nodup := by
  obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < 74 := by
    simpa only [Nat.zero_add, Crossover.length_splitFormula] using (List.mem_zipIdx hci).2.1
  change ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map
    (fun e => translate (cellOrigin 120 c) e.2.2)).Nodup
  have hn := (crossing_routes_nodup_check ⟨i, hi⟩).map
    (f := translate (cellOrigin 120 c))
    (fun _ _ h => (List.map_inj_right (fun _ _ h => add_right_cancel h)).mp h)
  simpa only [List.map_map, Function.comp_def] using hn

private theorem access_reverse_ne {sites : List Point} {p q : Point}
    (h : Orthogonal.length p q = 1) : access sites p q ≠ access sites q p := by
  intro heq
  have hvar := congrArg List.getLast? heq
  simp only [access_eq_pair, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq] at hvar
  have hp := variablePosition_mem_openCell (signal sites p q)
  have hq := variablePosition_mem_openCell (signal sites q p)
  rw [← hvar] at hq
  have hpq : p = q := cell_eq_of_mem_open_closed (by decide) hp
    ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩
  subst q
  simp [Orthogonal.length] at h

private theorem placedClause_routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) : pc.2.2.Nodup := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨_, _, hpc⟩) | ⟨o, ho, hpc⟩
  · exact originalClause_routes_nodup hw hv hpc
  · exact crossingClause_routes_nodup hpc
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    have hne := access_reverse_ne (sites := crossingSites φ)
      (occurrencePath_unit ho (prefixStep_mem he))
    cases o.2.2.2 <;> simp [link, hne, Ne.symm hne]

/-- Distinct incidence occurrences have distinct actual route lists. -/
theorem routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (routes φ).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun _ hpc => placedClause_routes_nodup hw hv hpc, ?_⟩
  have hn := clausePositions_nodup hw hv
  rw [List.Nodup, List.pairwise_map] at hn
  apply hn.imp_of_mem
  intro pc pd hpc hpd hpos r hr hs
  have hhead (pc : PlacedClause) (hpc : pc ∈ placedClauses φ) (hr : r ∈ pc.2.2) :
      r.head? = some pc.2.1 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < pc.1.length := by rwa [← placedClause_route_count φ pc hpc]
    have hzip : (pc.1[i], pc.2.2[i]) ∈ pc.1.zip pc.2.2 := by
      have hk : i < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
      simpa only [List.getElem_zip] using (List.getElem_mem hk)
    exact (placedClause_endpoints φ hpc hzip).1
  exact hpos (Option.some.inj ((hhead pc hpc hr).symm.trans (hhead pd hpd hs)))

private theorem route_declared_endpoints (φ : CNF ℕ) {r : Route} (hr : r ∈ routes φ) :
    ∃ pc ∈ placedClauses φ, ∃ v ∈ (rawFormula φ).vars,
      r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition v) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < pc.1.length := by rwa [← placedClause_route_count φ pc hpc]
  have hzip : (pc.1[i], pc.2.2[i]) ∈ pc.1.zip pc.2.2 := by
    have hk : i < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
    simpa only [List.getElem_zip] using (List.getElem_mem hk)
  refine ⟨pc, hpc, (pc.1[i]).1, ?_, placedClause_endpoints φ hpc hzip⟩
  exact CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, (pc.1[i]).2,
    List.getElem_mem hi'⟩

private theorem variable_ne_clause {φ : CNF ℕ} {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) :
    variablePosition v ≠ pc.2.1 := by
  intro h
  apply variable_clause_positions_disjoint φ
    (List.mem_map_of_mem (CNF.mem_distinctVars.mpr hv))
  rw [h]
  exact List.mem_map_of_mem hpc

private theorem routeEnd_clause_is_head {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) (hend : RouteEnd r pc.2.1) :
    r.head? = some pc.2.1 := by
  rcases hend with h | h
  · exact h
  · obtain ⟨_, _, v, hv, _, hlast⟩ := route_declared_endpoints φ hr
    exact False.elim (variable_ne_clause hv hpc (Option.some.inj (hlast.symm.trans h)))

private theorem route_originalClause_contact {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {pc : PlacedClause} (hpc : pc ∈ originalClauses φ (crossingSites φ))
    (hp : realPoint pc.2.1 ∈ support r) : r.head? = some pc.2.1 := by
  have hpc' : pc ∈ placedClauses φ := List.mem_append_left _ (List.mem_append_left _ hpc)
  apply routeEnd_clause_is_head hr hpc'
  obtain ⟨⟨clause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < φ.length := by
    simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  have hsite := clause_cell_not_mem_crossingSites φ hi
  change realPoint (center (Layout.center (φ.distinctVars.length + i))) ∈ support r at hp
  change RouteEnd r (center (Layout.center (φ.distinctVars.length + i)))
  rcases route_support_cases hr hp with ⟨c, hc, e, he, rfl⟩ | ⟨c, q, hpiece, hp'⟩
  · have hcore := crossingRoute_mem_openCell he c hp
    have hcenter := center_mem_openCell (r := 120) (by decide)
      (Layout.center (φ.distinctVars.length + i))
    have heq : Layout.center (φ.distinctVars.length + i) = c :=
      cell_eq_of_mem_open_closed (by decide) hcenter
        ⟨hcore.1.le, hcore.2.1.le, hcore.2.2.1.le, hcore.2.2.2.le⟩
    exact False.elim (hsite (heq ▸ hc))
  · have heq := access_variable_contact
      (v := (Layout.center (φ.distinctVars.length + i), none))
      (sites := crossingSites φ) (by simp [hsite]) hp'
    have hend := hpiece.inner_endpoint
    rw [← heq] at hend
    simpa only [variablePosition, Option.elim_none, center] using hend

private theorem splitClause_nonempty : ∀ c ∈ Crossover.splitFormula, c ≠ [] := by
  decide +kernel

private theorem placedClause_nonempty_or_original {φ : CNF ℕ} {pc : PlacedClause}
    (hpc : pc ∈ placedClauses φ) :
    pc.1 ≠ [] ∨ pc ∈ originalClauses φ (crossingSites φ) := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩
  · exact Or.inr hpc
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    exact Or.inl (by
      simpa only [Clause.relabel, ne_eq, List.map_eq_nil_iff] using
        splitClause_nonempty c (List.fst_mem_of_mem_zipIdx hci))
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    exact Or.inl (by cases ‹Occurrence ℕ›.2.2.2 <;> simp [link])

/-- An actual route can meet a displayed clause only at its clause endpoint.
The source bounds are used by the global contact certificate; empty original clauses are
handled separately by their source-center geometry. -/
theorem route_clause_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r : Route} (hr : r ∈ routes φ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    (hp : realPoint pc.2.1 ∈ support r) : r.head? = some pc.2.1 := by
  rcases placedClause_nonempty_or_original hpc with hne | horg
  · have hi : 0 < pc.2.2.length := by
      rw [placedClause_route_count φ pc hpc]
      exact List.length_pos_iff.mpr hne
    have hi' : 0 < pc.1.length := List.length_pos_iff.mpr hne
    let s := pc.2.2[0]
    have hs : s ∈ routes φ := List.mem_flatMap.mpr ⟨pc, hpc, List.getElem_mem hi⟩
    have hzip : (pc.1[0], s) ∈ pc.1.zip pc.2.2 := by
      have hk : 0 < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
      simpa only [List.getElem_zip] using (List.getElem_mem hk)
    have hhead := (placedClause_endpoints φ hpc hzip).1
    by_cases hrs : r = s
    · exact hrs ▸ hhead
    · have hq : realPoint pc.2.1 ∈ support s :=
        Or.inl ⟨pc.2.1, List.mem_of_head? hhead, rfl⟩
      obtain ⟨a, hpa, hend, _⟩ := route_contacts hw hv hr hs hrs hp hq
      have heq := realPoint_injective hpa
      exact routeEnd_clause_is_head hr hpc (heq ▸ hend)
  · exact route_originalClause_contact hr horg hp

private theorem drawingPosition_eq_getD {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ (SAT.incidenceGraph (formula φ)).1) :
    Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v =
      (positions φ).getD v (0, 0) := by
  simp only [SAT.incidenceGraph, List.mem_range] at hv
  simp only [Graph.drawingPosition, SAT.incidenceGraph]
  rw [idxOf_range_eq hv]

private theorem declared_position_index_lt {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ (SAT.incidenceGraph (formula φ)).1) : v < (positions φ).length := by
  rw [positions_length]
  simpa only [SAT.incidenceGraph, List.mem_range, List.length_range] using hv

private theorem drawingPosition_mem {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ (SAT.incidenceGraph (formula φ)).1) :
    Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v ∈
      positions φ := by
  rw [drawingPosition_eq_getD hv, List.getD_eq_getElem _ _ (declared_position_index_lt hv)]
  exact List.getElem_mem _

private theorem drawingPosition_injective {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {a b : ℕ} (ha : a ∈ (SAT.incidenceGraph (formula φ)).1)
    (hb : b ∈ (SAT.incidenceGraph (formula φ)).1)
    (heq : Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) a =
      Graph.drawingPosition (SAT.incidenceGraph (formula φ))
        (positions φ, routes φ) b) : a = b := by
  have hi := declared_position_index_lt ha
  have hj := declared_position_index_lt hb
  rw [drawingPosition_eq_getD ha, drawingPosition_eq_getD hb,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at heq
  exact (positions_nodup hw hv).eq_of_getElem_eq hi hj heq

private theorem indexed_route_mem {φ : CNF ℕ} {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    (routes φ).getD i [] ∈ routes φ := by
  have hir : i < (routes φ).length := by rwa [routes_length]
  rw [List.getD_eq_getElem _ _ hir]
  exact List.getElem_mem hir

/-- Every actual indexed route avoids all nonincident displayed vertices. -/
theorem routes_avoid_vertices {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i : ℕ} (hi : i < (SAT.incidenceGraph (formula φ)).2.length)
    {v : ℕ} (hvertex : v ∈ (SAT.incidenceGraph (formula φ)).1)
    (hp : realPoint (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) v) ∈ support ((routes φ).getD i [])) :
    v = (SAT.incidenceGraph (formula φ)).2[i].1 ∨
      v = (SAT.incidenceGraph (formula φ)).2[i].2 := by
  have hend := routes_endpoints φ hi
  have hdecl := SAT.incidenceGraph_endpoints (List.getElem_mem hi)
  have hmem := drawingPosition_mem hvertex
  change Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v ∈
    (rawFormula φ).distinctVars.map variablePosition ++
      (placedClauses φ).map (fun pc => pc.2.1) at hmem
  simp only [List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨w, hwmem, heq⟩ | ⟨pc, hpc, heq⟩
  · rw [← heq] at hp
    have hlast := route_variable_contact φ (indexed_route_mem hi)
      (CNF.mem_distinctVars.mp hwmem) hp
    apply Or.inl
    apply drawingPosition_injective hw hv hvertex hdecl.1
    exact heq.symm.trans (Option.some.inj (hlast.symm.trans hend.2))
  · rw [← heq] at hp
    have hhead := route_clause_contact hw hv (indexed_route_mem hi) hpc hp
    apply Or.inr
    apply drawingPosition_injective hw hv hvertex hdecl.2
    exact heq.symm.trans (Option.some.inj (hhead.symm.trans hend.1))

private theorem indexed_endpoint_declared {φ : CNF ℕ} {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) {a : Point}
    (ha : RouteEnd ((routes φ).getD i []) a) :
    ∃ v ∈ (SAT.incidenceGraph (formula φ)).1,
      (v = (SAT.incidenceGraph (formula φ)).2[i].1 ∨
        v = (SAT.incidenceGraph (formula φ)).2[i].2) ∧
      a = Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v := by
  have hend := routes_endpoints φ hi
  have hdecl := SAT.incidenceGraph_endpoints (List.getElem_mem hi)
  rcases ha with ha | ha
  · exact ⟨_, hdecl.2, Or.inr rfl, Option.some.inj (ha.symm.trans hend.1)⟩
  · exact ⟨_, hdecl.1, Or.inl rfl, Option.some.inj (ha.symm.trans hend.2)⟩

/-- Contacts between distinct incidence indices are exactly at common displayed graph vertices. -/
theorem routes_contacts {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i : ℕ} (hi : i < (SAT.incidenceGraph (formula φ)).2.length)
    {j : ℕ} (hj : j < (SAT.incidenceGraph (formula φ)).2.length) (hij : i ≠ j)
    {p : ℝ × ℝ} (hp : p ∈ support ((routes φ).getD i []))
    (hq : p ∈ support ((routes φ).getD j [])) :
    ∃ v ∈ (SAT.incidenceGraph (formula φ)).1,
      (v = (SAT.incidenceGraph (formula φ)).2[i].1 ∨
        v = (SAT.incidenceGraph (formula φ)).2[i].2) ∧
      (v = (SAT.incidenceGraph (formula φ)).2[j].1 ∨
        v = (SAT.incidenceGraph (formula φ)).2[j].2) ∧
      p = realPoint (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
        (positions φ, routes φ) v) := by
  have hir : i < (routes φ).length := by rwa [routes_length]
  have hjr : j < (routes φ).length := by rwa [routes_length]
  have hne : (routes φ).getD i [] ≠ (routes φ).getD j [] := by
    rw [List.getD_eq_getElem _ _ hir, List.getD_eq_getElem _ _ hjr]
    exact fun h => hij ((routes_nodup hw hv).eq_of_getElem_eq hir hjr h)
  obtain ⟨a, hpa, ha, hb⟩ := route_contacts hw hv
    (indexed_route_mem hi) (indexed_route_mem hj) hne hp hq
  obtain ⟨v, hv', hvi, hav⟩ := indexed_endpoint_declared hi ha
  obtain ⟨w, hw', hwj, haw⟩ := indexed_endpoint_declared hj hb
  have heq : v = w := drawingPosition_injective hw hv hv' hw' (hav.symm.trans haw)
  exact ⟨v, hv', hvi, heq ▸ hwj, hpa.trans (congrArg realPoint hav)⟩

/-- The executable planar SAT compiler supplies an actual planar orthogonal drawing.
Only the source clause-width and literal-occurrence bounds are assumed. Every contact,
avoidance and simplicity assertion uses full real segment support. -/
theorem isPlanarOrthogonalDrawing {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) where
  vertexCount := positions_length φ
  edgeCount := routes_length φ
  labelsNodup := List.nodup_range
  positionsNodup := positions_nodup hw hv
  endpointsDeclared := fun _ => SAT.incidenceGraph_endpoints
  loopless := fun _ => SAT.incidenceGraph_loopless
  endpoints := fun _ hi => Or.inr (routes_endpoints φ hi)
  orthogonal := fun _ hi => (routes_regular φ _ (indexed_route_mem hi)).1
  simple := fun _ hi => (routes_regular φ _ (indexed_route_mem hi)).2
  avoidsVertices := fun _ hi _ hvertex => routes_avoid_vertices hw hv hi hvertex
  contacts := fun _ hi _ hj hij _ hp hq => routes_contacts hw hv hi hj hij hp hq

end Cslib.Complexity.SAT.PlanarCompile
