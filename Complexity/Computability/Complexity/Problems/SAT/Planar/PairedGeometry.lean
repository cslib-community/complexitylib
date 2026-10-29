/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathGeometry
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy
public import Complexity.Foundations.Geometry.Orthogonal.PairedBoundary
import Complexity.Computability.Complexity.Problems.SAT.Incidence.Compact
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Geometry of the paired-port compiler

The compiler reuses the canonical unit paths. Paired accesses have disjoint supports,
and their only boundary contacts identify the same lane of the same unit grid edge.
All geometric assertions concern entire real supports.

## Main results

* `access_eq_translate`: every actual access uses the common fixed paired-port interface.
* `route_contacts`, `routes_contacts`: continuous endpoint-only contacts of the actual routes.
* `isPlanarOrthogonalDrawing`: the actual compact formula's continuous drawing certificate.

## References

The paired macrocell assembly is original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Within one cell, boundary positions identify both the side and the lane. -/
theorem boundary_injective (c : Point) :
    Function.Injective (fun p : PairedPorts.Port => boundary c p.1 p.2) := by
  intro p q h
  apply PairedPorts.boundaryPort_injective
  exact add_left_cancel h

/-- Opposite facing sides of unit neighbors match in the same lane. -/
theorem shared_boundary {p q : Point} (h : Orthogonal.length p q = 1) (l : Fin 2) :
    boundary p (side p q) l = boundary q (side q p) l := by
  rcases p with ⟨x, y⟩
  rcases PlanarCompile.unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    fin_cases l <;>
    ext <;> norm_num [boundary, side, PlanarCompile.side, cellOrigin, PairedPorts.boundaryPort,
      PairedPorts.offset] <;> omega

/-- The compiler's presented signal always has the shared inner access position. -/
theorem signal_position (sites : List Point) (p q : Point) (l : Fin 2) :
    variablePosition (signal sites p q l) =
      cellOrigin 120 p + PairedPorts.variablePosition (side p q) l := by
  simp only [signal, port, variablePosition]
  split_ifs <;> rfl

/-- Actual accesses are translations of the fixed paired-port accesses. -/
theorem access_eq_translate (sites : List Point) (p q : Point) (l : Fin 2) :
    access sites p q l = translate (cellOrigin 120 p) (PairedPorts.accessRoute (side p q) l) := by
  rw [access, signal_position]
  simp only [boundary, PairedPorts.accessRoute, translate, List.map_cons, List.map_nil]
  simp only [add_comm]

/-- Every actual access is proper and orthogonal. -/
theorem access_orthogonal (sites : List Point) (p q : Point) (l : Fin 2) :
    IsOrthogonal (access sites p q l) := by
  rw [access_eq_translate, isOrthogonal_translate_iff]
  exact (PairedPorts.access_endpoints _ _).1

/-- Every actual access is continuously simple. -/
theorem access_simple (sites : List Point) (p q : Point) (l : Fin 2) :
    IsSimple (access sites p q l) := by
  rw [access_eq_translate, isSimple_translate_iff]
  exact PairedPorts.access_isSimple _ _

/-- All actual access routes have the same fixed cost. -/
theorem access_cost (sites : List Point) (p q : Point) (l : Fin 2) :
    wireLength (access sites p q l) = 20 ∧ (access sites p q l).consecutivePairs.length = 1 := by
  rw [access_eq_translate, wireLength_translate]
  exact ⟨(PairedPorts.access_route_sizes _ _).2, rfl⟩

/-- The translated paired boundary belongs to its own closed cell. -/
theorem boundary_mem_closedCell (c : Point) (s : Fin 4) (l : Fin 2) :
    realPoint (boundary c s l) ∈ closedCell 120 c := by
  rw [boundary, realPoint_add, add_comm, mem_closedCell_add_origin_iff]
  fin_cases s <;> fin_cases l <;> norm_num [PairedPorts.boundaryPort, PairedPorts.offset, realPoint]

/-- A paired boundary point is outside every open grid cell. -/
theorem boundary_not_mem_openCell (c d : Point) (s : Fin 4) (l : Fin 2) :
    realPoint (boundary c s l) ∉ openCell 120 d := by
  intro hp
  have hdc := cell_eq_of_mem_open_closed (by decide) hp (boundary_mem_closedCell c s l)
  subst d
  rw [boundary, realPoint_add, add_comm, mem_openCell_add_origin_iff] at hp
  fin_cases s <;> fin_cases l <;>
    norm_num [PairedPorts.boundaryPort, PairedPorts.offset, realPoint] at hp

/-- Every actual access stays in its closed cell and touches its boundary only at its port. -/
theorem access_support_cell (sites : List Point) (c q : Point) (l : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q l)) :
    p ∈ closedCell 120 c ∧
      (p ∉ openCell 120 c → p = realPoint (boundary c (side c q) l)) := by
  rw [access_eq_translate] at hp
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hlocal : x ∈ support (PairedPorts.accessRoute (side c q) l) :=
    (mem_support_translate_iff _ _ _).1 (hx ▸ hp)
  obtain ⟨h₀, h₁, h₂, h₃, hb⟩ := PairedPorts.access_boundary_isolation hlocal
  constructor
  · rw [← hx, mem_closedCell_add_origin_iff]
    exact ⟨h₀, h₁, h₂, h₃⟩
  · intro hnot
    have hn : ¬ (0 < x.1 ∧ x.1 < 240 ∧ 0 < x.2 ∧ x.2 < 240) := by
      intro h
      apply hnot
      rw [← hx, mem_openCell_add_origin_iff]
      exact h
    have hboundary : x.1 = 0 ∨ x.1 = 240 ∨ x.2 = 0 ∨ x.2 = 240 := by
      by_contra h
      apply hn
      push Not at h
      exact ⟨lt_of_le_of_ne h₀ (Ne.symm h.1), lt_of_le_of_ne h₁ h.2.1,
        lt_of_le_of_ne h₂ (Ne.symm h.2.2.1), lt_of_le_of_ne h₃ h.2.2.2⟩
    rw [← hx, hb hboundary, boundary, realPoint_add, add_comm]

/-- Contacts between accesses in different cells occur at both designated boundary ports. -/
theorem access_contact_of_distinct_cells (sites otherSites : List Point)
    {c d : Point} (hcd : c ≠ d) (q t : Point) (l k : Fin 2) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q l)) (hq : p ∈ support (access otherSites d t k)) :
    p = realPoint (boundary c (side c q) l) ∧ p = realPoint (boundary d (side d t) k) := by
  have hc := access_support_cell sites c q l hp
  have hd := access_support_cell otherSites d t k hq
  constructor
  · apply hc.2
    intro ho
    exact hcd (cell_eq_of_mem_open_closed (by decide) ho hd.1)
  · apply hd.2
    intro ho
    exact hcd (cell_eq_of_mem_open_closed (by decide) ho hc.1).symm

/-- Distinct paired ports of one cell have disjoint continuous accesses. -/
theorem access_disjoint_same_cell (sites : List Point) (c q t : Point) (l k : Fin 2)
    (hne : (side c q, l) ≠ (side c t, k)) :
    Disjoint (support (access sites c q l)) (support (access sites c t k)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [access_eq_translate] at hp hq
  have hp' := (mem_support_translate_iff (cellOrigin 120 c) _
    (p - realPoint (cellOrigin 120 c))).1 (by simpa only [sub_add_cancel] using hp)
  have hq' := (mem_support_translate_iff (cellOrigin 120 c) _
    (p - realPoint (cellOrigin 120 c))).1 (by simpa only [sub_add_cancel] using hq)
  exact Set.disjoint_left.mp (PairedPorts.access_disjoint hne) hp' hq'

/-- Equality of paired seam points identifies the lane and the old single seam midpoint. -/
theorem boundary_step_midpoint_eq {p q a b : Point} {l k : Fin 2}
    (hpq : Orthogonal.length p q = 1) (hab : Orthogonal.length a b = 1)
    (h : boundary p (side p q) l = boundary a (side a b) k) :
    l = k ∧ cellPort 120 p (side p q) = cellPort 120 a (side a b) := by
  rcases p with ⟨px, py⟩
  rcases a with ⟨ax, ay⟩
  rcases PlanarCompile.unit_neighbor_cases hpq with rfl | rfl | rfl | rfl <;>
    rcases PlanarCompile.unit_neighbor_cases hab with rfl | rfl | rfl | rfl <;>
    fin_cases l <;> fin_cases k <;>
    norm_num [boundary, side, PlanarCompile.side, cellPort, cellOrigin,
      PairedPorts.boundaryPort, PairedPorts.offset, Prod.ext_iff] at h ⊢ <;> omega

/-- All actual unit steps are proper; this includes final steps into clause cells. -/
theorem path_step_unit {φ : CNF ℕ} {e : Point × Point}
    (he : e ∈ (paths φ).flatMap List.consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [PlanarCompile.paths_eq_unitPaths, Graph.unitPaths_length] using hi
  apply Graph.unitPath_unit _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) hi'
  change e ∈ ((paths φ).getD i []).consecutivePairs
  rwa [List.getD_eq_getElem _ _ hi]

/-- Paired seam points of every actual path step are all distinct, including final steps. -/
theorem pathBoundaries_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]).Nodup := by
  let steps := (paths φ).flatMap List.consecutivePairs
  let mid : Point × Point → Point := fun e => cellPort 120 e.1 (side e.1 e.2)
  have hn : (steps.map mid).Nodup := by
    simpa only [steps, mid, List.map_flatMap] using PlanarCompile.pathMidpoints_nodup hw hv
  have hp : steps.Pairwise (fun e f => mid e ≠ mid f) := List.pairwise_map.mp hn
  have hlocal (e : Point × Point) :
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1].Nodup := by
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil,
      not_false_eq_true, and_true]
    intro h
    have he := boundary_injective e.1 (a₁ := (side e.1 e.2, 0))
      (a₂ := (side e.1 e.2, 1)) h
    have hh : (0 : Fin 2) ≠ 1 := by decide
    exact hh (congrArg Prod.snd he)
  have hn' : (steps.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨fun e _ => hlocal e, ?_⟩
    apply hp.imp_of_mem
    intro e f he hf hmid x hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with hy | hy <;>
      exact hmid (boundary_step_midpoint_eq (path_step_unit he) (path_step_unit hf) hy).2
  simpa only [steps, List.flatMap_assoc] using hn'

/-- The actual ordinary-cell list has no repetitions. -/
private theorem ordinaryCells_nodup (φ : CNF ℕ) : (ordinaryCells φ).Nodup :=
  nodup_selectDistinct _ _

/-- Ordinary tiles are emitted exactly at retained occupied cells outside crossing sites. -/
private theorem mem_ordinaryCells (φ : CNF ℕ) (p : Point) :
    p ∈ ordinaryCells φ ↔ p ∈ (paths φ).flatMap List.dropLast ∧ p ∉ crossingSites φ := by
  simp [ordinaryCells, mem_selectDistinct_replicate]

/-- Every original clause cell is disjoint from all ordinary tiles. -/
theorem clause_cell_not_ordinary {φ : CNF ℕ} {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ ordinaryCells φ := by
  intro hp
  obtain ⟨r, hr, hp⟩ := List.mem_flatMap.mp ((mem_ordinaryCells φ _).1 hp).1
  change r ∈ PlanarCompile.paths φ at hr
  rw [← PlanarCompile.occurrencePaths_eq_paths φ] at hr
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
  exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi hp

private def finalLocalRoute (s : Fin 4) : Route :=
  [(120, 120), PairedPorts.spokeElbow s, PairedPorts.boundaryPort s (PairedPorts.spokeLane s),
    cellOrigin 120 (PairedPorts.neighbor s) +
      PairedPorts.variablePosition (PairedPorts.oppositeSide s) (PairedPorts.spokeLane s)]

private theorem finalLocalRoute_orthogonal : ∀ s, IsOrthogonal (finalLocalRoute s) := by
  decide +kernel

private theorem finalLocalRoute_nodup : ∀ s, (finalLocalRoute s).Nodup := by decide +kernel

private theorem finalLocalRoute_simple_check : ∀ s, ∀ a ∈ (finalLocalRoute s).consecutivePairs,
    ∀ b ∈ (finalLocalRoute s).consecutivePairs, a ≠ b →
      segmentContactCheck (consecutiveContact a b) a.1 a.2 b.1 b.2 = true := by decide +kernel

private theorem finalLocalRoute_simple (s : Fin 4) : IsSimple (finalLocalRoute s) := by
  refine ⟨finalLocalRoute_nodup s, ?_⟩
  intro a ha b hb hne p hp hq
  obtain ⟨q, hq, hpq⟩ := segmentContactCheck_sound
    (finalLocalRoute_simple_check s a ha b hb hne) hp hq
  unfold consecutiveContact at hq
  split_ifs at hq with h h'
  · have hqa : q = a.2 := List.mem_singleton.mp hq
    subst q
    exact ⟨Or.inr hpq, Or.inl (hpq.trans (congrArg realPoint h))⟩
  · have hqa : q = a.1 := List.mem_singleton.mp hq
    subst q
    exact ⟨Or.inl hpq, Or.inr (hpq.trans (congrArg realPoint h'.symm))⟩
  · exact False.elim (List.not_mem_nil hq)

private theorem finalRoute_eq_translate (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    [center q, cellOrigin 120 q + PairedPorts.spokeElbow (side q p),
      boundary q (side q p) (PairedPorts.spokeLane (side q p)),
      variablePosition (signal sites p q (PairedPorts.spokeLane (side q p)))] =
      translate (cellOrigin 120 q) (finalLocalRoute (side q p)) := by
  rw [signal_position]
  have hrev : Orthogonal.length q p = 1 := by
    simp only [Orthogonal.length] at h ⊢
    omega
  rcases q with ⟨x, y⟩
  rcases PlanarCompile.unit_neighbor_cases hrev with rfl | rfl | rfl | rfl <;>
    norm_num [translate, finalLocalRoute, side, PlanarCompile.side, center, PlanarCompile.center,
      boundary, cellOrigin, PairedPorts.neighbor, PairedPorts.oppositeSide,
      PairedPorts.variablePosition, PairedPorts.boundaryPort, PairedPorts.spokeLane,
      PairedPorts.spokeElbow, PairedPorts.offset, Prod.ext_iff] <;> omega

/-- Every actual final literal route is proper, orthogonal and continuously simple. -/
theorem lastLiteral_route_regular (sites : List Point) (r : Route) (b : Bool)
    (h : Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1) :
    IsOrthogonal (lastLiteral sites r b).2 ∧ IsSimple (lastLiteral sites r b).2 := by
  dsimp only [lastLiteral]
  rw [finalRoute_eq_translate sites h, isOrthogonal_translate_iff, isSimple_translate_iff]
  exact ⟨finalLocalRoute_orthogonal _, finalLocalRoute_simple _⟩

/-- The final incidence starts at its clause center and ends at its actual signal variable. -/
theorem lastLiteral_endpoints (sites : List Point) (r : Route) (b : Bool) :
    (lastLiteral sites r b).2.head? = some (center (r.getLastD (0, 0))) ∧
      (lastLiteral sites r b).2.getLast? = some (variablePosition (lastLiteral sites r b).1.1) :=
  ⟨rfl, rfl⟩

/-- Every route in a placed seam clause is an actual paired access. -/
theorem link_routes_cases (sites : List Point) (p q : Point) (l : Fin 2) {r : Route}
    (hr : r ∈ (link sites p q l).2.2) : r = access sites p q l ∨ r = access sites q p l := by
  by_cases hl : l = 0
  · simpa only [link, hl, ite_true, List.mem_cons, List.not_mem_nil, or_false] using hr
  · simpa only [link, hl, ite_false, List.mem_cons, List.not_mem_nil, or_false, false_or,
      or_comm] using hr

/-- Every route in a seam clause is proper, orthogonal and continuously simple. -/
theorem link_routes_regular (sites : List Point) (p q : Point) (l : Fin 2) {r : Route}
    (hr : r ∈ (link sites p q l).2.2) : IsOrthogonal r ∧ IsSimple r := by
  rcases link_routes_cases sites p q l hr with rfl | rfl <;>
    exact ⟨access_orthogonal _ _ _ _, access_simple _ _ _ _⟩

/-- Seam incidence routes match their literal variables in both lane orientations. -/
theorem link_endpoints (sites : List Point) {p q : Point} (h : Orthogonal.length p q = 1)
    (lane : Fin 2) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ (link sites p q lane).1.zip (link sites p q lane).2.2) :
    r.head? = some (link sites p q lane).2.1 ∧
      r.getLast? = some (variablePosition l.1) := by
  by_cases hl : lane = 0
  · subst lane
    change (l, r) ∈ [((signal sites p q 0, false), access sites p q 0),
      ((signal sites q p 0, true), access sites q p 0)] at hlr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlr
    rcases hlr with heq | heq
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨congrArg some (shared_boundary h 0).symm, rfl⟩
  · simp only [link, hl, ite_false] at hlr
    change (l, r) ∈ [((signal sites q p lane, false), access sites q p lane),
      ((signal sites p q lane, true), access sites p q lane)] at hlr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlr
    rcases hlr with heq | heq
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨congrArg some (shared_boundary h lane).symm, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨rfl, rfl⟩

/-- Every seam literal uses one of its two actual presented signals. -/
theorem link_literal_cases (sites : List Point) (p q : Point) (lane : Fin 2)
    {lit : Literal Variable} (h : lit ∈ (link sites p q lane).1) :
    lit.1 = signal sites p q lane ∨ lit.1 = signal sites q p lane := by
  by_cases hl : lane = 0
  · simp only [link, hl, ite_true, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [link, hl, ite_false, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Every structured variable lies strictly inside its indexed macrocell. -/
theorem variablePosition_mem_openCell (v : Variable) :
    realPoint (variablePosition v) ∈ openCell 120 v.1 := by
  rcases v with ⟨p, v⟩
  cases v with
  | inl v =>
    obtain ⟨h₀, h₁, h₂, h₃⟩ := PairedPorts.variable_bounds v.1 v.2
    rw [variablePosition, Sum.elim_inl, realPoint_add, add_comm, mem_openCell_add_origin_iff]
    have h : 0 < (PairedPorts.variablePosition v.1 v.2).1 ∧
        (PairedPorts.variablePosition v.1 v.2).1 < 240 ∧
        0 < (PairedPorts.variablePosition v.1 v.2).2 ∧
        (PairedPorts.variablePosition v.1 v.2).2 < 240 := by omega
    norm_num [realPoint]
    exact_mod_cast h
  | inr v =>
    obtain ⟨h₀, h₁, h₂, h₃⟩ := PairedCrossover.variable_bounds v
    rw [variablePosition, Sum.elim_inr, realPoint_add, add_comm, mem_openCell_add_origin_iff]
    have h : 0 < (PairedCrossover.variablePosition v).1 ∧
        (PairedCrossover.variablePosition v).1 < 240 ∧
        0 < (PairedCrossover.variablePosition v).2 ∧
        (PairedCrossover.variablePosition v).2 < 240 := by omega
    norm_num [realPoint]
    exact_mod_cast h

/-- Every raw variable has the tag prescribed by its cell's kind. -/
theorem raw_variable_cell_kind (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) : v.2.isLeft = true ↔ v.1 ∉ crossingSites φ := by
  have hsignal (p q : Point) (l : Fin 2) :
      (signal (crossingSites φ) p q l).2.isLeft = true ↔ p ∉ crossingSites φ := by
    by_cases hp : p ∈ crossingSites φ <;> simp [signal, port, hp, Sum.isLeft]
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, hp, hpc⟩) | ⟨p, hp, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hv
    obtain ⟨lj, _, rfl⟩ := List.mem_map.mp hlr
    have heq' := congrArg Prod.fst heq
    dsimp only [lastLiteral] at heq'
    subst v
    exact hsignal _ _ _
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, heq⟩ := List.mem_map.mp hv
    have heq' := congrArg Prod.fst heq
    change (p, Sum.inl l.1) = v at heq'
    subst v
    simpa using ((mem_ordinaryCells φ p).1 hp).2
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, heq⟩ := List.mem_map.mp hv
    have heq' := congrArg Prod.fst heq
    change (p, Sum.inr l.1) = v at heq'
    subst v
    simp [hp]
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      rcases link_literal_cases _ _ _ _ hv with heq | heq <;> dsimp only at heq <;> subst v <;>
      exact hsignal _ _ _

/-- Actual variable positions identify their structured names. -/
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
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      simp only [variablePosition, Sum.elim_inl, add_right_inj] at heq
      exact congrArg (fun x => (p, Sum.inl x)) (PairedPorts.variablePosition_injective heq)
    | inr w =>
      have hn := hvkind.mp rfl
      have hf := hwkind.mpr hn
      contradiction
  | inr v =>
    cases w with
    | inl w =>
      have hn := hwkind.mp rfl
      have hf := hvkind.mpr hn
      contradiction
    | inr w =>
      simp only [variablePosition, Sum.elim_inr, add_right_inj] at heq
      exact congrArg (fun x => (p, Sum.inr x)) (PairedCrossover.variablePosition_injective heq)

/-- The variable-position prefix of the actual drawing has no repetitions. -/
theorem variablePositions_nodup (φ : CNF ℕ) :
    ((rawFormula φ).distinctVars.map variablePosition).Nodup :=
  (CNF.nodup_distinctVars _).map_on (fun _ hv _ hw =>
    variablePosition_injOn_rawVars φ (CNF.mem_distinctVars.mp hv) (CNF.mem_distinctVars.mp hw))

/-- The actual drawing has exactly the compact incidence graph's number of vertices. -/
theorem positions_length (φ : CNF ℕ) :
    (positions φ).length = (SAT.incidenceGraph (formula φ)).1.length := by
  simp [positions, SAT.incidenceGraph, formula, CNF.distinctVars_compact, rawFormula]

/-- Compaction preserves the ordered incidence graph. -/
theorem incidenceGraph_formula (φ : CNF ℕ) :
    SAT.incidenceGraph (formula φ) = SAT.incidenceGraph (rawFormula φ) :=
  SAT.incidenceGraph_compact _

/-- Every actual output route is proper, orthogonal and continuously simple. -/
theorem routes_regular (φ : CNF ℕ) :
    ∀ r ∈ routes φ, IsOrthogonal r ∧ IsSimple r := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, _, hpc⟩) | ⟨p, _, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only at heq
    subst r
    exact lastLiteral_route_regular _ _ _ (PlanarCompile.occurrencePath_last_unit ho)
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    exact ⟨(isOrthogonal_translate_iff _ _).2 (OrdinaryRing.incidence_orthogonal e he'),
      (isSimple_translate_iff _ _).2 (OrdinaryRing.incidence_isSimple he')⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    exact ⟨(isOrthogonal_translate_iff _ _).2 (PairedCrossover.incidence_orthogonal e he'),
      (isSimple_translate_iff _ _).2 (PairedCrossover.incidence_isSimple he')⟩
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;> exact link_routes_regular _ _ _ _ hr

private theorem ordinary_route_count : ∀ i : Fin 8,
    (OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i.val).length =
      (OrdinaryRing.formula.getD i.val []).length := by decide +kernel

private theorem crossing_route_count : ∀ i : Fin 78,
    (PairedCrossover.incidenceRoutes.filter fun e => e.1 == i.val).length =
      (PairedCrossover.formula.getD i.val []).length := by decide +kernel

/-- Each actual placed clause supplies exactly one route per literal, in literal order. -/
theorem placedClause_route_count (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, pc.2.2.length = pc.1.length := by
  intro pc hpc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, _, hpc⟩) | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    simp
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : ci.2 < 8 := by
      simpa only [Nat.zero_add, OrdinaryRing.formula_sizes.1] using (List.mem_zipIdx hci).2.1
    have hc := (List.mem_zipIdx hci).2.2
    simp only [Nat.sub_zero] at hc
    have hcount := ordinary_route_count ⟨ci.2, hi⟩
    rw [List.getD_eq_getElem OrdinaryRing.formula []
      (by simpa only [OrdinaryRing.formula_sizes.1] using hi)] at hcount
    simpa only [List.length_map, Clause.length_relabel, hc] using hcount
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : ci.2 < 78 := by
      simpa only [Nat.zero_add, PairedCrossover.length_formula] using (List.mem_zipIdx hci).2.1
    have hc := (List.mem_zipIdx hci).2.2
    simp only [Nat.sub_zero] at hc
    have hcount := crossing_route_count ⟨ci.2, hi⟩
    rw [List.getD_eq_getElem PairedCrossover.formula []
      (by simpa only [PairedCrossover.length_formula] using hi)] at hcount
    simpa only [List.length_map, Clause.length_relabel, hc] using hcount
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;> rfl

/-- The actual route count is the edge count of the final compact incidence graph. -/
theorem routes_length (φ : CNF ℕ) :
    (routes φ).length = (SAT.incidenceGraph (formula φ)).2.length := by
  rw [SAT.length_edges_incidenceGraph]
  rw [formula, CNF.compact, CNF.vars_relabel, List.length_map]
  simp only [routes, List.length_flatMap, CNF.vars, List.length_map,
    List.length_flatten, rawFormula, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  exact fun pc hpc => placedClause_route_count φ pc hpc

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
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hlast : (occurrencePath φ (i, j, sourceLiteral)).getLastD (0, 0) =
      Layout.center (φ.distinctVars.length + i) := by
    rw [List.getLastD_eq_getLast?, PlanarCompile.occurrencePath_endpoints ho |>.2]
    rfl
  simpa only [lastLiteral, hlast] using lastLiteral_endpoints sites
    (occurrencePath φ (i, j, sourceLiteral))
    sourceLiteral.2

private theorem ordinary_literal_routes_cover : ∀ i : Fin 8,
    ((OrdinaryRing.formula.getD i.val []).zip
      ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2)).all
        (fun lr => decide ((i.val, lr.1.1, lr.2) ∈ OrdinaryRing.incidenceRoutes)) = true := by
  decide +kernel

private theorem crossing_literal_routes_cover : ∀ i : Fin 78,
    ((PairedCrossover.formula.getD i.val []).zip
      ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2)).all
        (fun lr => decide ((i.val, lr.1.1, lr.2) ∈ PairedCrossover.incidenceRoutes)) = true := by
  decide +kernel

private theorem ordinaryClause_endpoints {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ ordinaryClauses c) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < 8 := by
    simpa only [Nat.zero_add, OrdinaryRing.formula_sizes.1] using (List.mem_zipIdx hci).2.1
  have hc : sourceClause = OrdinaryRing.formula.getD i [] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [OrdinaryRing.formula_sizes.1] using hi)]
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2
  change (l, r) ∈ (sourceClause.map (Prod.map (fun v => (c, Sum.inl v)) id)).zip
    ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) at hlr
  have hmap : ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) =
      ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i).map fun e => e.2.2).map
        (translate (cellOrigin 120 c)) := by rw [List.map_map]; rfl
  rw [hmap, List.zip_map] at hlr
  obtain ⟨⟨oldLiteral, oldRoute⟩, hold, heq⟩ := List.mem_map.mp hlr
  rw [hc] at hold
  have he : (i, oldLiteral.1, oldRoute) ∈ OrdinaryRing.incidenceRoutes :=
    of_decide_eq_true (List.all_eq_true.mp (ordinary_literal_routes_cover ⟨i, hi⟩) _ hold)
  change (((c, Sum.inl oldLiteral.1), oldLiteral.2),
    translate (cellOrigin 120 c) oldRoute) = (l, r) at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hend := OrdinaryRing.incidence_endpoints _ he
  constructor
  · simp only [translate, List.head?_map, hend.2.1, Option.map_some]
    congr 1
    exact add_comm _ _
  · simp only [translate, List.getLast?_map, hend.2.2, Option.map_some, variablePosition,
      Sum.elim_inl, OrdinaryRing.variablePosition]
    congr 1
    exact add_comm _ _

private theorem crossingClause_endpoints {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < 78 := by
    simpa only [Nat.zero_add, PairedCrossover.length_formula] using (List.mem_zipIdx hci).2.1
  have hc : sourceClause = PairedCrossover.formula.getD i [] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [PairedCrossover.length_formula] using hi)]
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2
  change (l, r) ∈ (sourceClause.map (Prod.map (fun v => (c, Sum.inr v)) id)).zip
    ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) at hlr
  have hmap : ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) =
      ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i).map fun e => e.2.2).map
        (translate (cellOrigin 120 c)) := by rw [List.map_map]; rfl
  rw [hmap, List.zip_map] at hlr
  obtain ⟨⟨oldLiteral, oldRoute⟩, hold, heq⟩ := List.mem_map.mp hlr
  rw [hc] at hold
  have he : (i, oldLiteral.1, oldRoute) ∈ PairedCrossover.incidenceRoutes :=
    of_decide_eq_true (List.all_eq_true.mp (crossing_literal_routes_cover ⟨i, hi⟩) _ hold)
  change (((c, Sum.inr oldLiteral.1), oldLiteral.2),
    translate (cellOrigin 120 c) oldRoute) = (l, r) at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hend := PairedCrossover.incidence_endpoints _ he
  constructor
  · simp only [translate, List.head?_map, hend.2.1, Option.map_some]
    congr 1
    exact add_comm _ _
  · simp only [translate, List.getLast?_map, hend.2.2, Option.map_some, variablePosition,
      Sum.elim_inr]
    congr 1
    exact add_comm _ _

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

/-- Every actual literal/route pair has the clause and variable endpoints in its record. -/
theorem placedClause_endpoints (φ : CNF ℕ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩) | ⟨o, ho, hpc⟩
  · exact originalClause_endpoints hpc hlr
  · exact ordinaryClause_endpoints hpc hlr
  · exact crossingClause_endpoints hpc hlr
  · obtain ⟨e, he, hpc⟩ := List.mem_flatMap.mp hpc
    have he' : e ∈ (occurrencePath φ o).consecutivePairs := by
      rw [consecutivePairs_dropLast] at he
      exact (List.dropLast_sublist _).subset he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      exact link_endpoints _ (PlanarCompile.occurrencePath_unit ho he') _ hlr

private theorem support_pair (a b : Point) : support [a, b] = segment a b := by
  ext p
  rw [support_cons_cons]
  change (p ∈ segment a b ∨ p ∈ support [b]) ↔ _
  have hright : realPoint b ∈ segment a b := _root_.right_mem_segment ℝ _ _
  have hs : p ∈ support [b] ↔ p = realPoint b := by simp [support, List.consecutivePairs]
  rw [hs]
  exact ⟨fun h => h.elim id (fun h => h ▸ hright), Or.inl⟩

private theorem support_four (a b c d : Point) :
    support [a, b, c, d] = support [a, b, c] ∪ support [c, d] := by
  have hl : support [a, b, c, d] = segment a b ∪ (segment b c ∪ segment c d) := by
    rw [support_cons_cons, support_cons_cons, support_pair]
  have hr : support [a, b, c] = segment a b ∪ segment b c := by
    rw [support_cons_cons, support_pair]
  rw [hl, hr, support_pair, Set.union_assoc]

/-- The final incidence is exactly one translated clause spoke and one neighboring access. -/
theorem support_lastLiteral (sites : List Point) (r : Route) (b : Bool)
    (h : Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1) :
    let p := r.getD (r.length - 2) (0, 0)
    let q := r.getLastD (0, 0)
    let s := side q p
    support (lastLiteral sites r b).2 =
      support (translate (cellOrigin 120 q) (PairedPorts.spokeRoute s)) ∪
        support (access sites p q (PairedPorts.spokeLane s)) := by
  dsimp only
  have hspoke (p q : Point) :
      translate (cellOrigin 120 q) (PairedPorts.spokeRoute (side q p)) =
        [center q, cellOrigin 120 q + PairedPorts.spokeElbow (side q p),
          boundary q (side q p) (PairedPorts.spokeLane (side q p))] := by
    simp only [translate, PairedPorts.spokeRoute, List.map_cons, List.map_nil, center,
      PlanarCompile.center, boundary, add_comm]
  rw [hspoke, access, shared_boundary h]
  exact support_four _ _ _ _

/-- Matching paired boundaries of actual occurrence steps identify the whole occurrence and
oriented step, as well as the lane. -/
theorem boundary_occurrence_step_unique {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {e f : Point × Point} {l k : Fin 2}
    (he : e ∈ (occurrencePath φ o).consecutivePairs)
    (hf : f ∈ (occurrencePath φ t).consecutivePairs)
    (h : boundary e.1 (side e.1 e.2) l = boundary f.1 (side f.1 f.2) k) :
    l = k ∧ o = t ∧ e = f := by
  obtain ⟨hl, hmid⟩ := boundary_step_midpoint_eq (PlanarCompile.occurrencePath_unit ho he)
    (PlanarCompile.occurrencePath_unit ht hf) h
  refine ⟨hl, ?_⟩
  let mids := fun o => (occurrencePath φ o).consecutivePairs.map fun e =>
    cellPort 120 e.1 (side e.1 e.2)
  have hn : ((Cslib.Logic.PL.occurrences φ).flatMap mids).Nodup := by
    simpa only [← PlanarCompile.occurrencePaths_eq_paths φ, List.flatMap_map, mids] using
      PlanarCompile.pathMidpoints_nodup hw hv
  have houter := (List.nodup_flatMap.mp hn).2
  have hme : cellPort 120 e.1 (side e.1 e.2) ∈ mids o := List.mem_map_of_mem he
  have hmf : cellPort 120 e.1 (side e.1 e.2) ∈ mids t := hmid ▸ List.mem_map_of_mem hf
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
  have hij := hlocal.eq_of_getElem_eq hi' hj' (by
    simpa only [mids, List.getElem_map] using hmid)
  subst j
  rfl

private theorem idxOf_range_eq {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

private theorem positions_getD_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    (positions φ).getD ((rawFormula φ).distinctVars.idxOf v) (0, 0) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  rw [positions, List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

/-- A raw variable's incidence-graph index resolves to its actual geometric position. -/
theorem drawingPosition_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.idxOf v) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.idxOf v))
    (0, 0) = _
  rw [idxOf_range_eq (by omega)]
  exact positions_getD_raw_variable φ hv

/-- A raw clause's incidence-graph index resolves to its actual placed clause position. -/
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
  have hvar : l.1 ∈ (rawFormula φ).vars :=
    CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, l.2, (List.of_mem_zip hlr).1⟩
  change r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.length + i)) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.idxOf l.1))
  rw [drawingPosition_raw_clause φ hi, drawingPosition_raw_variable φ hvar, ← hget]
  exact hends

/-- Actual indexed routes have the final compact incidence graph's endpoints, in clause-to-
variable order, including repeated literal incidences. -/
theorem routes_endpoints (φ : CNF ℕ) {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    let r := (routes φ).getD i []
    r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].2) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].1) := by
  simp only [incidenceGraph_formula] at hi ⊢
  have hir : i < (routes φ).length := by rwa [routes_length, incidenceGraph_formula]
  have h := (raw_routes_endpoints φ).get hi hir
  simpa only [List.get_eq_getElem, List.getD_eq_getElem _ _ hir] using h

private theorem occurrencePath_mem_paths {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ∈ paths φ := by
  change occurrencePath φ o ∈ PlanarCompile.paths φ
  rw [← PlanarCompile.occurrencePaths_eq_paths φ]
  exact List.mem_map_of_mem ho

private theorem penultimate_mem_dropLast {r : Route} (h : 2 ≤ r.length) :
    r.getD (r.length - 2) (0, 0) ∈ r.dropLast := by
  have hk : r.length - 2 < r.dropLast.length := by simp only [List.length_dropLast]; omega
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_dropLast] at hk; omega)]
  rw [← List.getElem_dropLast hk]
  exact List.getElem_mem hk

/-- Every emitted variable lies in a selected crossing or a retained occupied path cell. -/
theorem raw_variable_cell_membership (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.1 ∈ crossingSites φ ∨ ∃ r ∈ paths φ, v.1 ∈ r.dropLast := by
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨p, hp, hpc⟩) | ⟨p, hp, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hv
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    have heq' := congrArg Prod.fst heq
    dsimp only [lastLiteral] at heq'
    subst v
    exact Or.inr ⟨_, occurrencePath_mem_paths ho,
      penultimate_mem_dropLast (PlanarCompile.occurrencePath_length_ge_two ho)⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, heq⟩ := List.mem_map.mp hv
    have heq' := congrArg Prod.fst heq
    change (p, Sum.inl l.1) = v at heq'
    subst v
    exact Or.inr (List.mem_flatMap.mp ((mem_ordinaryCells φ p).1 hp).1)
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, heq⟩ := List.mem_map.mp hv
    have heq' := congrArg Prod.fst heq
    change (p, Sum.inr l.1) = v at heq'
    subst v
    exact Or.inl hp
  · obtain ⟨e, he, hpc⟩ := List.mem_flatMap.mp hpc
    have hpair := List.of_mem_zip he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      rcases link_literal_cases _ _ _ _ hv with heq | heq <;> dsimp only at heq <;> subst v
    all_goals
      apply Or.inr
      refine ⟨_, occurrencePath_mem_paths ho, ?_⟩
      first | exact hpair.1 | exact List.mem_of_mem_tail hpair.2

/-- No actual variable is placed in an original clause cell. -/
theorem raw_variable_not_clause_cell {φ : CNF ℕ} {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) {i : ℕ} (hi : i < φ.length) :
    v.1 ≠ Layout.center (φ.distinctVars.length + i) := by
  intro heq
  rcases raw_variable_cell_membership φ hv with hc | ⟨r, hr, hmem⟩
  · exact PlanarCompile.clause_cell_not_mem_crossingSites φ hi (heq ▸ hc)
  · change r ∈ PlanarCompile.paths φ at hr
    rw [← PlanarCompile.occurrencePaths_eq_paths φ] at hr
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi (heq ▸ hmem)

private theorem spoke_bounds : ∀ s, ∀ p ∈ PairedPorts.spokeRoute s,
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 := by decide +kernel

/-- Every translated original-clause spoke stays in its clause cell. -/
theorem spoke_support_cell (c : Point) (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s))) :
    p ∈ closedCell 120 c := by
  apply support_subset_closedCell (r := 120) (c := c) (a :=
    translate (cellOrigin 120 c) (PairedPorts.spokeRoute s)) ?_ hp
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  rw [realPoint_add, mem_closedCell_add_origin_iff]
  have h := spoke_bounds s a ha
  norm_num [realPoint]
  exact_mod_cast h

private theorem translated_core_mem_openCell {r : Route}
    (hi : ∀ p ∈ support r, 0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240)
    (c : Point) {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) r)) :
    p ∈ openCell 120 c := by
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hlocal := (mem_support_translate_iff (cellOrigin 120 c) r x).1 (hx ▸ hp)
  rw [← hx, mem_openCell_add_origin_iff]
  exact hi x hlocal

/-- Every translated ordinary core incidence is strictly inside its cell. -/
theorem ordinaryRoute_mem_openCell {e : ℕ × OrdinaryRing.Variable × Route}
    (he : e ∈ OrdinaryRing.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c :=
  translated_core_mem_openCell (fun _ hp => OrdinaryRing.core_support_interior he hp) c hp

/-- Every translated crossover core incidence is strictly inside its cell. -/
theorem crossingRoute_mem_openCell {e : ℕ × PairedCrossover.Variable × Route}
    (he : e ∈ PairedCrossover.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c :=
  translated_core_mem_openCell (fun _ hp => PairedCrossover.core_support_interior he hp) c hp

/-- An actual access visits a correctly tagged variable only at its own endpoint. -/
theorem access_variable_contact {sites : List Point} {c q : Point} {lane : Fin 2} {v : Variable}
    (hkind : v.2.isLeft = true ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈ support (access sites c q lane)) :
    v = signal sites c q lane := by
  have hcell : v.1 = c := cell_eq_of_mem_open_closed (by decide)
    (variablePosition_mem_openCell v) (access_support_cell sites c q lane hp).1
  rcases v with ⟨d, v⟩
  change d = c at hcell
  subst d
  cases v with
  | inl v =>
    have hn : c ∉ sites := hkind.mp rfl
    have hlocal : realPoint (OrdinaryRing.variablePosition v) ∈
        support (PairedPorts.accessRoute (side c q) lane) := by
      apply (mem_support_translate_iff (cellOrigin 120 c) _ _).1
      simpa only [access_eq_translate, variablePosition, Sum.elim_inl, realPoint_add,
        add_comm, OrdinaryRing.variablePosition] using hp
    have hv : v = (side c q, lane) := by
      by_contra hv
      exact OrdinaryRing.access_variable_not_mem hv hlocal
    subst v
    simp [signal, port, hn]
  | inr v =>
    have hc : c ∈ sites := by
      by_contra hn
      have hf := hkind.mpr hn
      contradiction
    have hlocal : realPoint (PairedCrossover.variablePosition v) ∈
        support (PairedCrossover.accessRoute (side c q) lane) := by
      apply (mem_support_translate_iff (cellOrigin 120 c) _ _).1
      simpa only [access_eq_translate, variablePosition, Sum.elim_inr, realPoint_add,
        add_comm, PairedCrossover.accessRoute] using hp
    have hv : v = PairedCrossover.terminal (side c q) lane := by
      by_contra hv
      exact PairedCrossover.access_variable_not_mem hv hlocal
    subst v
    simp [signal, port, hc]

private theorem ordinary_core_variable_contact {sites : List Point} {c : Point}
    (hc : c ∉ sites) {e : ℕ × OrdinaryRing.Variable × Route}
    (he : e ∈ OrdinaryRing.incidenceRoutes) {v : Variable}
    (hkind : v.2.isLeft = true ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈ support (translate (cellOrigin 120 c) e.2.2)) :
    v = (c, Sum.inl e.2.1) := by
  have hecell := ordinaryRoute_mem_openCell he c hp
  have hcell : v.1 = c := cell_eq_of_mem_open_closed (by decide)
    (variablePosition_mem_openCell v)
    ⟨hecell.1.le, hecell.2.1.le, hecell.2.2.1.le, hecell.2.2.2.le⟩
  rcases v with ⟨d, v⟩
  change d = c at hcell
  subst d
  cases v with
  | inl v =>
    have hlocal : realPoint (OrdinaryRing.variablePosition v) ∈ support e.2.2 := by
      apply (mem_support_translate_iff (cellOrigin 120 c) _ _).1
      simpa only [variablePosition, Sum.elim_inl, OrdinaryRing.variablePosition,
        realPoint_add, add_comm] using hp
    have hv : v = e.2.1 := by
      by_contra hv
      exact OrdinaryRing.variable_not_mem_support he hv hlocal
    exact congrArg (fun w => (c, Sum.inl w)) hv
  | inr v =>
    have hf := hkind.mpr hc
    contradiction

private theorem crossing_core_variable_contact {sites : List Point} {c : Point}
    (hc : c ∈ sites) {e : ℕ × PairedCrossover.Variable × Route}
    (he : e ∈ PairedCrossover.incidenceRoutes) {v : Variable}
    (hkind : v.2.isLeft = true ↔ v.1 ∉ sites)
    (hp : realPoint (variablePosition v) ∈ support (translate (cellOrigin 120 c) e.2.2)) :
    v = (c, Sum.inr e.2.1) := by
  have hvcell := variablePosition_mem_openCell v
  have hecell := crossingRoute_mem_openCell he c hp
  have hcell : v.1 = c := cell_eq_of_mem_open_closed (by decide) hvcell
    ⟨hecell.1.le, hecell.2.1.le, hecell.2.2.1.le, hecell.2.2.2.le⟩
  rcases v with ⟨d, v⟩
  change d = c at hcell
  subst d
  cases v with
  | inl v => exact False.elim (hkind.mp rfl hc)
  | inr v =>
    have hlocal : realPoint (PairedCrossover.variablePosition v) ∈ support e.2.2 := by
      apply (mem_support_translate_iff (cellOrigin 120 c) _ _).1
      simpa only [variablePosition, Sum.elim_inr, realPoint_add, add_comm] using hp
    have hv : v = e.2.1 := by
      by_contra hv
      exact PairedCrossover.variable_not_mem_support he hv hlocal
    exact congrArg (fun w => (c, Sum.inr w)) hv

/-- Every actual route can meet an emitted variable only at its variable endpoint. -/
theorem route_variable_contact (φ : CNF ℕ) {r : Route} (hr : r ∈ routes φ)
    {v : Variable} (hv : v ∈ (rawFormula φ).vars)
    (hp : realPoint (variablePosition v) ∈ support r) :
    r.getLast? = some (variablePosition v) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨c, hc, hpc⟩) | ⟨c, hc, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨⟨l, j⟩, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (i, j, l) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨(l, j), hlj, rfl⟩⟩
    dsimp only at heq
    subst r
    rw [support_lastLiteral _ _ _ (PlanarCompile.occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · have hcell : v.1 = (occurrencePath φ (i, j, l)).getLastD (0, 0) :=
        cell_eq_of_mem_open_closed (by decide) (variablePosition_mem_openCell v)
          (spoke_support_cell _ _ hp)
      have hend := (PlanarCompile.occurrencePath_endpoints ho).2
      rw [List.getLastD_eq_getLast?, hend] at hcell
      have hi : i < φ.length := by
        simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
      exact False.elim (raw_variable_not_clause_cell hv hi hcell)
    · have heq := access_variable_contact (raw_variable_cell_kind φ hv) hp
      exact heq ▸ (lastLiteral_endpoints _ _ _).2
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    have heq := ordinary_core_variable_contact ((mem_ordinaryCells φ c).1 hc).2 he'
      (raw_variable_cell_kind φ hv) hp
    subst v
    simp only [translate, List.getLast?_map, (OrdinaryRing.incidence_endpoints _ he').2.2,
      Option.map_some, variablePosition, Sum.elim_inl, OrdinaryRing.variablePosition, add_comm]
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    have heq := crossing_core_variable_contact hc he' (raw_variable_cell_kind φ hv) hp
    subst v
    simp only [translate, List.getLast?_map, (PairedCrossover.incidence_endpoints _ he').2.2,
      Option.map_some, variablePosition, Sum.elim_inr, add_comm]
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      rcases link_routes_cases _ _ _ _ hr with rfl | rfl <;>
      have heq := access_variable_contact (raw_variable_cell_kind φ hv) hp <;>
      rw [heq] <;> rfl

private theorem translated_point_mem_openCell (c p : Point)
    (h : 20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220) :
    realPoint (cellOrigin 120 c + p) ∈ openCell 120 c := by
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff]
  have h' : 0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240 := by omega
  norm_num [realPoint]
  exact_mod_cast h'

/-- Ordinary clause positions are strictly inside their cell. -/
theorem ordinaryClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ ordinaryClauses c) : realPoint pc.2.1 ∈ openCell 120 c := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : ci.2 < OrdinaryRing.clausePositions.length := by
    rw [OrdinaryRing.drawing_sizes.1]
    simpa only [Nat.zero_add, OrdinaryRing.formula_sizes.1] using (List.mem_zipIdx hci).2.1
  apply translated_point_mem_openCell
  apply OrdinaryRing.clause_bounds
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- Crossover clause positions are strictly inside their cell. -/
theorem crossingClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) : realPoint pc.2.1 ∈ openCell 120 c := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : ci.2 < PairedCrossover.clausePositions.length := by
    rw [PairedCrossover.drawing_sizes.1]
    simpa only [Nat.zero_add, PairedCrossover.length_formula] using (List.mem_zipIdx hci).2.1
  apply translated_point_mem_openCell
  apply PairedCrossover.clause_bounds
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- An ordinary tile retains the fixed ring's clause-position order. -/
theorem ordinaryClause_positions (c : Point) :
    (ordinaryClauses c).map (fun pc => pc.2.1) =
      OrdinaryRing.clausePositions.map (cellOrigin 120 c + ·) := by
  apply List.ext_getElem
  · simp [ordinaryClauses, OrdinaryRing.formula_sizes.1, OrdinaryRing.drawing_sizes.1]
  · intro i hi hj
    simp only [ordinaryClauses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]

/-- A crossover tile retains the fixed paired crossover's clause-position order. -/
theorem crossingClause_positions (c : Point) :
    (crossingClauses c).map (fun pc => pc.2.1) =
      PairedCrossover.clausePositions.map (cellOrigin 120 c + ·) := by
  apply List.ext_getElem
  · simp [crossingClauses, PairedCrossover.length_formula, PairedCrossover.drawing_sizes.1]
  · intro i hi hj
    simp only [crossingClauses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]

private theorem ordinaryClause_positions_nodup (c : Point) :
    ((ordinaryClauses c).map fun pc => pc.2.1).Nodup := by
  rw [ordinaryClause_positions]
  exact OrdinaryRing.clausePositions_nodup.map (fun _ _ h => add_left_cancel h)

private theorem crossingClause_positions_nodup (c : Point) :
    ((crossingClauses c).map fun pc => pc.2.1).Nodup := by
  rw [crossingClause_positions]
  exact PairedCrossover.clausePositions_nodup.map (fun _ _ h => add_left_cancel h)

private theorem interior_positions_nodup (cells : List Point) (hn : cells.Nodup)
    (pcs : Point → List PlacedClause)
    (hlocal : ∀ c, ((pcs c).map fun pc => pc.2.1).Nodup)
    (hinterior : ∀ c, ∀ pc ∈ pcs c, realPoint pc.2.1 ∈ openCell 120 c) :
    ((cells.flatMap pcs).map fun pc => pc.2.1).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun c _ => hlocal c, hn.imp ?_⟩
  intro c d hcd p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  have hc := hinterior c pc hpc
  have hd := hinterior d pd hpd
  rw [heq] at hd
  exact Set.disjoint_left.mp (disjoint_openCell (by decide) hcd) hc hd

private theorem originalPositions_nodup (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun pc => pc.2.1).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [originalClauses, List.getElem_map, List.getElem_zipIdx] at heq
  have hc := PlanarCompile.center_injective heq
  have hx := congrArg Prod.fst hc
  simp only [Layout.center] at hx
  omega

/-- Emitted seam clause positions are a sublist of all paired path boundaries. -/
theorem linkPositions_sublist_boundaries (φ : CNF ℕ) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1).Sublist
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1]) := by
  change List.Sublist _ ((PlanarCompile.paths φ).flatMap fun r =>
    r.consecutivePairs.flatMap fun e =>
      [boundary e.1 (side e.1 e.2) 0, boundary e.1 (side e.1 e.2) 1])
  rw [← PlanarCompile.occurrencePaths_eq_paths φ, List.flatMap_map]
  simp only [List.map_flatMap, links, List.map_cons, List.map_nil, link]
  apply List.Sublist.flatMap_right
  intro o _
  apply List.Sublist.flatMap
  rw [consecutivePairs_dropLast]
  exact List.dropLast_sublist _

/-- All actual paired-link clauses have distinct positions. -/
theorem linkPositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1).Nodup :=
  (pathBoundaries_nodup hw hv).sublist (linkPositions_sublist_boundaries φ)

private theorem link_position_not_open {sites : List Point} {r : Route}
    {pc : PlacedClause} (hpc : pc ∈ links sites r) (c : Point) :
    realPoint pc.2.1 ∉ openCell 120 c := by
  obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl <;> exact boundary_not_mem_openCell _ c _ _

private theorem original_interior_positions_disjoint (φ : CNF ℕ) (cells : List Point)
    (pcs : Point → List PlacedClause)
    (hinterior : ∀ c, ∀ pc ∈ pcs c, realPoint pc.2.1 ∈ openCell 120 c)
    (hexclude : ∀ i < φ.length, Layout.center (φ.distinctVars.length + i) ∉ cells) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      ((cells.flatMap pcs).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨c, hc, hpd⟩ := List.mem_flatMap.mp hpd
  have hpos := hinterior c pd hpd
  rw [heq] at hpos
  have hcenter := center_mem_openCell (r := 120) (by decide)
    (Layout.center (φ.distinctVars.length + ci.2))
  have hcell := cell_eq_of_mem_open_closed (by decide) hcenter
    ⟨hpos.1.le, hpos.2.1.le, hpos.2.2.1.le, hpos.2.2.2.le⟩
  have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  exact hexclude ci.2 hi (hcell ▸ hc)

private theorem interior_link_positions_disjoint (φ : CNF ℕ) (cells : List Point)
    (pcs : Point → List PlacedClause)
    (hinterior : ∀ c, ∀ pc ∈ pcs c, realPoint pc.2.1 ∈ openCell 120 c) :
    List.Disjoint ((cells.flatMap pcs).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨c, _, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd c
  rw [heq]
  exact hinterior c pc hpc

private theorem ordinary_crossing_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint (((ordinaryCells φ).flatMap ordinaryClauses).map fun pc => pc.2.1)
      (((crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨c, hc, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨d, hd, hpd⟩ := List.mem_flatMap.mp hpd
  have hcpos := ordinaryClause_mem_openCell hpc
  have hdpos := crossingClause_mem_openCell hpd
  rw [heq] at hdpos
  have hcd := cell_eq_of_mem_open_closed (by decide) hcpos
    ⟨hdpos.1.le, hdpos.2.1.le, hdpos.2.2.1.le, hdpos.2.2.2.le⟩
  exact ((mem_ordinaryCells φ c).1 hc).2 (hcd.symm ▸ hd)

private theorem original_link_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd (Layout.center (φ.distinctVars.length + ci.2))
  rw [heq]
  exact center_mem_openCell (by decide) _

/-- All actual original, ordinary, crossover and paired-seam clause positions are distinct. -/
theorem clausePositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((placedClauses φ).map fun pc => pc.2.1).Nodup := by
  have ho := interior_positions_nodup (ordinaryCells φ) (ordinaryCells_nodup φ)
    ordinaryClauses ordinaryClause_positions_nodup (fun _ _ => ordinaryClause_mem_openCell)
  have hc := interior_positions_nodup (crossingSites φ) (PlanarCompile.crossingSites_nodup φ)
    crossingClauses crossingClause_positions_nodup (fun _ _ => crossingClause_mem_openCell)
  have hoo := original_interior_positions_disjoint φ (ordinaryCells φ) ordinaryClauses
    (fun _ _ => ordinaryClause_mem_openCell) (fun _ hi => clause_cell_not_ordinary hi)
  have hoc := original_interior_positions_disjoint φ (crossingSites φ) crossingClauses
    (fun _ _ => crossingClause_mem_openCell)
    (fun _ hi => PlanarCompile.clause_cell_not_mem_crossingSites φ hi)
  have hol := interior_link_positions_disjoint φ (ordinaryCells φ) ordinaryClauses
    (fun _ _ => ordinaryClause_mem_openCell)
  have hcl := interior_link_positions_disjoint φ (crossingSites φ) crossingClauses
    (fun _ _ => crossingClause_mem_openCell)
  simp only [placedClauses, List.map_append]
  apply List.Nodup.append
  · apply List.Nodup.append
    · exact (originalPositions_nodup φ _).append ho hoo
    · exact hc
    · intro p hp hq
      rcases List.mem_append.mp hp with hp | hp
      · exact hoc hp hq
      · exact ordinary_crossing_positions_disjoint φ hp hq
  · exact linkPositions_nodup hw hv
  · intro p hp hq
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact original_link_positions_disjoint φ hp hq
      · exact hol hp hq
    · exact hcl hp hq

private theorem crossingRoute_length : ∀ e ∈ PairedCrossover.incidenceRoutes,
    2 ≤ e.2.2.length := by decide +kernel

/-- Every actual incidence route contains at least two distinct endpoint positions. -/
theorem routes_length_ge_two (φ : CNF ℕ) : ∀ r ∈ routes φ, 2 ≤ r.length := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨lj, _, rfl⟩ := List.mem_map.mp hlr
    dsimp only [lastLiteral] at heq
    subst r
    simp
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    rw [translate, List.length_map, OrdinaryRing.incidence_pair e (List.mem_filter.mp he).1]
    simp
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    rw [translate, List.length_map]
    exact crossingRoute_length e (List.mem_filter.mp he).1
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      rcases link_routes_cases _ _ _ _ hr with rfl | rfl <;> simp [access]

private theorem placedClause_nonempty_or_original {φ : CNF ℕ} {pc : PlacedClause}
    (hpc : pc ∈ placedClauses φ) : pc.1 ≠ [] ∨ pc ∈ originalClauses φ (crossingSites φ) := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩) | ⟨_, _, hpc⟩
  · exact Or.inr hpc
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    apply Or.inl
    have hw := (OrdinaryRing.formula_sizes.2 ci.1 (List.fst_mem_of_mem_zipIdx hci))
    intro heq
    have hlen := congrArg List.length heq
    simp only [Clause.length_relabel, hw, List.length_nil] at hlen
    contradiction
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    have hnonempty : ∀ c ∈ PairedCrossover.formula, c ≠ [] := by decide +kernel
    apply Or.inl
    intro heq
    apply hnonempty ci.1 (List.fst_mem_of_mem_zipIdx hci)
    exact List.map_eq_nil_iff.mp heq
  · obtain ⟨e, _, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;> exact Or.inl (by simp [link])

private theorem simple_head_ne_last {r : Route} (hn : r.Nodup) (hlen : 2 ≤ r.length)
    {p : Point} (hhead : r.head? = some p) (hlast : r.getLast? = some p) : False := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
  have heq := hn.eq_of_getElem_eq (by omega) (by omega)
    (Option.some.inj (hhead.trans hlast.symm))
  omega

/-- Actual variable and clause position lists are disjoint. -/
theorem variable_clause_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((rawFormula φ).distinctVars.map variablePosition)
      ((placedClauses φ).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pc, hpc, heq⟩ := List.mem_map.mp hq
  have hv' := CNF.mem_distinctVars.mp hv
  rcases placedClause_nonempty_or_original hpc with hne | horiginal
  · have hlen : 0 < pc.1.length := List.length_pos_iff.mpr hne
    have hrlen : 0 < pc.2.2.length := by rw [placedClause_route_count φ pc hpc]; exact hlen
    have hz : 0 < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
    have hzmem := List.getElem_mem hz
    rw [List.getElem_zip] at hzmem
    have hr : pc.2.2[0] ∈ routes φ := List.mem_flatMap.mpr
      ⟨pc, hpc, List.getElem_mem hrlen⟩
    have hends := placedClause_endpoints φ hpc hzmem
    have hpoint : realPoint (variablePosition v) ∈ support pc.2.2[0] := by
      apply Or.inl
      refine ⟨variablePosition v, ?_, rfl⟩
      rw [← heq]
      obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hends.1
      rw [htail]
      exact List.mem_cons_self
    have hlast := route_variable_contact φ hr hv' hpoint
    apply simple_head_ne_last (routes_regular φ _ hr).2.1 (routes_length_ge_two φ _ hr)
      (hends.1.trans (congrArg some heq)) hlast
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp horiginal
    change center (Layout.center (φ.distinctVars.length + ci.2)) = variablePosition v at heq
    have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    have hpos := variablePosition_mem_openCell v
    have hcenter := center_mem_openCell (r := 120) (by decide)
      (Layout.center (φ.distinctVars.length + ci.2))
    change realPoint (center (Layout.center (φ.distinctVars.length + ci.2))) ∈
      openCell 120 (Layout.center (φ.distinctVars.length + ci.2)) at hcenter
    rw [heq] at hcenter
    have hcell := cell_eq_of_mem_open_closed (by decide) hpos
      ⟨hcenter.1.le, hcenter.2.1.le, hcenter.2.2.1.le, hcenter.2.2.2.le⟩
    exact raw_variable_not_clause_cell hv' hi hcell

/-- Every actual displayed graph vertex has its own position. -/
theorem positions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (positions φ).Nodup :=
  (variablePositions_nodup φ).append (clausePositions_nodup hw hv)
    (variable_clause_positions_disjoint φ)

private def lastStep (r : Route) : Point × Point :=
  (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0))

private theorem lastStep_mem {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∈ (occurrencePath φ o).consecutivePairs := by
  let r := occurrencePath φ o
  have hlen : 2 ≤ r.length := PlanarCompile.occurrencePath_length_ge_two ho
  have hk : r.length - 2 < r.consecutivePairs.length := by
    simp only [List.consecutivePairs, List.length_zip, List.length_tail]
    omega
  have heq : r.consecutivePairs[r.length - 2] = lastStep r := by
    rw [List.getElem_zip, List.getElem_tail]
    apply Prod.ext
    · change r[r.length - 2] = r.getD (r.length - 2) (0, 0)
      rw [List.getD_eq_getElem _ _ (by omega)]
    · change r[r.length - 2 + 1] = r.getLastD (0, 0)
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      change r[r.length - 2 + 1] = r[r.length - 1]
      congr 1
      omega
  rw [← heq]
  exact List.getElem_mem hk

private theorem lastStep_not_prefix {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    lastStep (occurrencePath φ o) ∉ (occurrencePath φ o).dropLast.consecutivePairs := by
  intro he
  have hp : (occurrencePath φ o).getLastD (0, 0) ∈ (occurrencePath φ o).dropLast :=
    List.mem_of_mem_tail (List.of_mem_zip he).2
  rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2] at hp
  exact PlanarCompile.clause_cell_not_mem_path_dropLast ho
    (Cslib.Logic.PL.mem_occurrences.mp ho).1 hp

private def RouteEnd (r : Route) (a : Point) : Prop :=
  r.head? = some a ∨ r.getLast? = some a

private inductive AccessPiece (φ : CNF ℕ) : Route → Point → Point → Fin 2 → Prop where
  | link {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
      (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) (l : Fin 2) :
      AccessPiece φ (access (crossingSites φ) e.1 e.2 l) e.1 e.2 l
  | reverseLink {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
      (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) (l : Fin 2) :
      AccessPiece φ (access (crossingSites φ) e.2 e.1 l) e.2 e.1 l
  | final {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      AccessPiece φ (lastLiteral (crossingSites φ) (occurrencePath φ o) o.2.2.2).2
        (lastStep (occurrencePath φ o)).1 (lastStep (occurrencePath φ o)).2
        (PairedPorts.spokeLane
          (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1))

private theorem prefixStep_mem {φ : CNF ℕ} {o : Occurrence ℕ} {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).dropLast.consecutivePairs) :
    e ∈ (occurrencePath φ o).consecutivePairs := by
  rw [consecutivePairs_dropLast] at he
  exact (List.dropLast_sublist _).subset he

private theorem AccessPiece.inner_endpoint {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) :
    r.getLast? = some (variablePosition (signal (crossingSites φ) c q l)) := by
  cases h with
  | link ho he l => rfl
  | reverseLink ho he l => rfl
  | final ho => rfl

private theorem AccessPiece.retained {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) : ∃ o ∈ Cslib.Logic.PL.occurrences φ,
      c ∈ (occurrencePath φ o).dropLast := by
  cases h with
  | link ho he l => exact ⟨_, ho, (List.of_mem_zip he).1⟩
  | reverseLink ho he l => exact ⟨_, ho, List.mem_of_mem_tail (List.of_mem_zip he).2⟩
  | final ho =>
    exact ⟨_, ho, penultimate_mem_dropLast (PlanarCompile.occurrencePath_length_ge_two ho)⟩

private theorem AccessPiece.not_clause_cell {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) {i : ℕ} (hi : i < φ.length) :
    c ≠ Layout.center (φ.distinctVars.length + i) := by
  obtain ⟨o, ho, hc⟩ := h.retained
  intro heq
  exact PlanarCompile.clause_cell_not_mem_path_dropLast ho hi (heq ▸ hc)

private theorem AccessPiece.source {φ : CNF ℕ} {r : Route} {c q : Point} {l : Fin 2}
    (h : AccessPiece φ r c q l) :
    ∃ o ∈ Cslib.Logic.PL.occurrences φ, ∃ e ∈ (occurrencePath φ o).consecutivePairs,
      boundary c (side c q) l = boundary e.1 (side e.1 e.2) l ∧
      ((e ∈ (occurrencePath φ o).dropLast.consecutivePairs ∧
          r = access (crossingSites φ) c q l) ∨
        (e = lastStep (occurrencePath φ o) ∧
          r = (lastLiteral (crossingSites φ) (occurrencePath φ o) o.2.2.2).2)) := by
  cases h with
  | link ho he l => exact ⟨_, ho, _, prefixStep_mem he, rfl, Or.inl ⟨he, rfl⟩⟩
  | reverseLink ho he l =>
    exact ⟨_, ho, _, prefixStep_mem he,
      (shared_boundary (PlanarCompile.occurrencePath_unit ho (prefixStep_mem he)) l).symm,
      Or.inl ⟨he, rfl⟩⟩
  | final ho => exact ⟨_, ho, _, lastStep_mem ho, rfl, Or.inr ⟨rfl, rfl⟩⟩

private theorem accessPieces_same_boundary {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} {l k : Fin 2}
    (hr : AccessPiece φ r c q l) (hs : AccessPiece φ s d t k)
    (h : boundary c (side c q) l = boundary d (side d t) k) :
    (r = access (crossingSites φ) c q l ∧ s = access (crossingSites φ) d t k) ∨ r = s := by
  obtain ⟨o, ho, e, he, hport, hr⟩ := hr.source
  obtain ⟨u, hu, f, hf, hport', hs⟩ := hs.source
  obtain ⟨_, rfl, rfl⟩ := boundary_occurrence_step_unique hw hv ho hu he hf
    (hport.symm.trans (h.trans hport'))
  rcases hr with ⟨hprefix, hr⟩ | ⟨hfinal, hr⟩ <;>
    rcases hs with ⟨hprefix', hs⟩ | ⟨hfinal', hs⟩
  · exact Or.inl ⟨hr, hs⟩
  · exact False.elim (lastStep_not_prefix ho (hfinal' ▸ hprefix))
  · exact False.elim (lastStep_not_prefix ho (hfinal ▸ hprefix'))
  · exact Or.inr (hr.trans hs.symm)

private theorem accessPieces_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c q d t : Point} {l k : Fin 2}
    (hr : AccessPiece φ r c q l) (hs : AccessPiece φ s d t k) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support (access (crossingSites φ) c q l))
    (hq : p ∈ support (access (crossingSites φ) d t k)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  by_cases hcd : c = d
  · subst d
    by_cases hport : (side c q, l) = (side c t, k)
    · have hb : boundary c (side c q) l = boundary c (side c t) k :=
        congrArg (fun x : PairedPorts.Port => boundary c x.1 x.2) hport
      rcases accessPieces_same_boundary hw hv hr hs hb with ⟨hr', hs'⟩ | heq
      · apply False.elim
        apply hne
        rw [hr', hs', access_eq_translate, access_eq_translate]
        exact congrArg (translate (cellOrigin 120 c))
          (congrArg (fun x : PairedPorts.Port => PairedPorts.accessRoute x.1 x.2) hport)
      · exact False.elim (hne heq)
    · exact False.elim (Set.disjoint_left.mp (access_disjoint_same_cell _ _ _ _ _ _ hport) hp hq)
  · have hcontact := access_contact_of_distinct_cells (crossingSites φ) (crossingSites φ)
      hcd q t l k hp hq
    have hport := realPoint_injective (hcontact.1.symm.trans hcontact.2)
    rcases accessPieces_same_boundary hw hv hr hs hport with ⟨hr', hs'⟩ | heq
    · refine ⟨boundary c (side c q) l, hcontact.1, Or.inl ?_, Or.inl ?_⟩
      · rw [hr', access]
        rfl
      · rw [hs', access, ← hport]
        rfl
    · exact False.elim (hne heq)

private theorem spoke_boundary_isolation {s : Fin 4} {p : ℝ × ℝ}
    (hp : p ∈ support (PairedPorts.spokeRoute s)) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (PairedPorts.boundaryPort s (PairedPorts.spokeLane s))) := by
  unfold PairedPorts.spokeRoute at hp
  rw [support_cons_cons, support_pair] at hp
  fin_cases s <;> rcases hp with hp | hp <;>
    norm_num [PairedPorts.spokeElbow, PairedPorts.spokeLane, PairedPorts.boundaryPort,
      PairedPorts.offset, Orthogonal.segment, realPoint, mem_horizontal, mem_vertical,
      Set.mem_uIcc] at hp ⊢
  all_goals
    rcases hp with ⟨heq, hlo, hhi⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    intro h
    rcases h with h | h | h | h <;> apply Prod.ext <;> norm_num <;> linarith

/-- A translated clause spoke touches its cell boundary only at the chosen paired port. -/
theorem spoke_support_boundary (c : Point) (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s)))
    (hnot : p ∉ openCell 120 c) :
    p = realPoint (boundary c s (PairedPorts.spokeLane s)) := by
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hlocal : x ∈ support (PairedPorts.spokeRoute s) :=
    (mem_support_translate_iff _ _ _).1 (hx ▸ hp)
  obtain ⟨h₀, h₁, h₂, h₃, hb⟩ := spoke_boundary_isolation hlocal
  have hn : ¬ (0 < x.1 ∧ x.1 < 240 ∧ 0 < x.2 ∧ x.2 < 240) := by
    intro h
    apply hnot
    rw [← hx, mem_openCell_add_origin_iff]
    exact h
  have hboundary : x.1 = 0 ∨ x.1 = 240 ∨ x.2 = 0 ∨ x.2 = 240 := by
    by_contra h
    apply hn
    push Not at h
    exact ⟨lt_of_le_of_ne h₀ (Ne.symm h.1), lt_of_le_of_ne h₁ h.2.1,
      lt_of_le_of_ne h₂ (Ne.symm h.2.2.1), lt_of_le_of_ne h₃ h.2.2.2⟩
  rw [← hx, hb hboundary, boundary, realPoint_add, add_comm]

private inductive SpokePiece (φ : CNF ℕ) : Route → Point → Fin 4 → Prop where
  | final {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      SpokePiece φ (lastLiteral (crossingSites φ) (occurrencePath φ o) o.2.2.2).2
        (lastStep (occurrencePath φ o)).2
        (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1)

private theorem SpokePiece.outer_endpoint {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) : r.head? = some (center c) := by
  cases h
  rfl

private theorem SpokePiece.clause_cell {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) : ∃ i < φ.length,
      c = Layout.center (φ.distinctVars.length + i) := by
  cases h with
  | final ho =>
    refine ⟨_, (Cslib.Logic.PL.mem_occurrences.mp ho).1, ?_⟩
    change (occurrencePath φ _).getLastD (0, 0) = _
    rw [List.getLastD_eq_getLast?, (PlanarCompile.occurrencePath_endpoints ho).2]
    rfl

private theorem SpokePiece.access {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) :
    ∃ q, AccessPiece φ r q c (PairedPorts.spokeLane s) ∧
      boundary c s (PairedPorts.spokeLane s) = boundary q (side q c) (PairedPorts.spokeLane s) := by
  cases h with
  | final ho =>
    refine ⟨_, AccessPiece.final ho, ?_⟩
    exact (shared_boundary (PlanarCompile.occurrencePath_last_unit ho) _).symm

private theorem SpokePiece.length {φ : CNF ℕ} {r : Route} {c : Point} {s : Fin 4}
    (h : SpokePiece φ r c s) : r.length = 4 := by
  cases h
  rfl

private theorem spoke_access_same_boundary {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d t : Point} {i : Fin 4} {k : Fin 2}
    (hr : SpokePiece φ r c i) (hs : AccessPiece φ s d t k)
    (hb : boundary c i (PairedPorts.spokeLane i) = boundary d (side d t) k) : r = s := by
  obtain ⟨q, haccess, hport⟩ := hr.access
  rcases accessPieces_same_boundary hw hv haccess hs (hport.symm.trans hb) with
    ⟨hr', _⟩ | heq
  · have hlen := congrArg List.length hr'
    rw [hr.length] at hlen
    change 4 = 2 at hlen
    contradiction
  · exact heq

private theorem spoke_access_disjoint {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d t : Point} {i : Fin 4} {k : Fin 2}
    (hr : SpokePiece φ r c i) (hs : AccessPiece φ s d t k) (hne : r ≠ s) :
    Disjoint (support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute i)))
      (support (access (crossingSites φ) d t k)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  by_cases hcd : c = d
  · obtain ⟨j, hj, hcell⟩ := hr.clause_cell
    exact hs.not_clause_cell hj (hcd.symm.trans hcell)
  · have hc := spoke_support_cell c i hp
    have hd := (access_support_cell (crossingSites φ) d t k hq).1
    have hp' := spoke_support_boundary c i hp (fun ho =>
      hcd (cell_eq_of_mem_open_closed (by decide) ho hd))
    have hq' := (access_support_cell (crossingSites φ) d t k hq).2 (fun ho =>
      hcd (cell_eq_of_mem_open_closed (by decide) ho hc).symm)
    exact hne (spoke_access_same_boundary hw hv hr hs (realPoint_injective (hp'.symm.trans hq')))

private theorem spokePieces_same_boundary {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d : Point} {i j : Fin 4}
    (hr : SpokePiece φ r c i) (hs : SpokePiece φ s d j)
    (hb : boundary c i (PairedPorts.spokeLane i) =
      boundary d j (PairedPorts.spokeLane j)) : r = s := by
  obtain ⟨t, haccess, hport⟩ := hs.access
  exact spoke_access_same_boundary hw hv hr haccess (hb.trans hport)

private theorem spokePieces_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} {c d : Point} {i j : Fin 4}
    (hr : SpokePiece φ r c i) (hs : SpokePiece φ s d j) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute i)))
    (hq : p ∈ support (translate (cellOrigin 120 d) (PairedPorts.spokeRoute j))) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  by_cases hcd : c = d
  · subst d
    by_cases hij : i = j
    · subst j
      exact False.elim (hne (spokePieces_same_boundary hw hv hr hs rfl))
    · let x := p - realPoint (cellOrigin 120 c)
      have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
      have hp' := (mem_support_translate_iff _ _ _).1 (hx ▸ hp)
      have hq' := (mem_support_translate_iff _ _ _).1 (hx ▸ hq)
      have hcenter := PairedPorts.spokes_contact hij hp' hq'
      refine ⟨center c, ?_, Or.inl hr.outer_endpoint, Or.inl hs.outer_endpoint⟩
      rw [← hx, hcenter, center, PlanarCompile.center, realPoint_add, add_comm]
  · have hc := spoke_support_cell c i hp
    have hd := spoke_support_cell d j hq
    have hp' := spoke_support_boundary c i hp (fun ho =>
      hcd (cell_eq_of_mem_open_closed (by decide) ho hd))
    have hq' := spoke_support_boundary d j hq (fun ho =>
      hcd (cell_eq_of_mem_open_closed (by decide) ho hc).symm)
    exact False.elim (hne (spokePieces_same_boundary hw hv hr hs
      (realPoint_injective (hp'.symm.trans hq'))))

private inductive CorePiece (φ : CNF ℕ) : Route → Point → Prop where
  | ordinary {c : Point} (hc : c ∈ ordinaryCells φ) {e : ℕ × OrdinaryRing.Variable × Route}
      (he : e ∈ OrdinaryRing.incidenceRoutes) :
      CorePiece φ (translate (cellOrigin 120 c) e.2.2) c
  | crossing {c : Point} (hc : c ∈ crossingSites φ) {e : ℕ × PairedCrossover.Variable × Route}
      (he : e ∈ PairedCrossover.incidenceRoutes) :
      CorePiece φ (translate (cellOrigin 120 c) e.2.2) c

private theorem CorePiece.interior {φ : CNF ℕ} {r : Route} {c : Point}
    (h : CorePiece φ r c) {p : ℝ × ℝ} (hp : p ∈ support r) : p ∈ openCell 120 c := by
  cases h with
  | ordinary hc he => exact ordinaryRoute_mem_openCell he _ hp
  | crossing hc he => exact crossingRoute_mem_openCell he _ hp

private theorem CorePiece.not_clause_cell {φ : CNF ℕ} {r : Route} {c : Point}
    (h : CorePiece φ r c) {i : ℕ} (hi : i < φ.length) :
    c ≠ Layout.center (φ.distinctVars.length + i) := by
  intro heq
  cases h with
  | ordinary hc he => exact clause_cell_not_ordinary hi (heq ▸ hc)
  | crossing hc he => exact PlanarCompile.clause_cell_not_mem_crossingSites φ hi (heq ▸ hc)

private theorem RouteEnd.translate {r : Route} {a : Point} (h : RouteEnd r a) (v : Point) :
    RouteEnd (translate v r) (a + v) := by
  rcases h with h | h
  · exact Or.inl (by simp only [Orthogonal.translate, List.head?_map, h, Option.map_some])
  · exact Or.inr (by simp only [Orthogonal.translate, List.getLast?_map, h, Option.map_some])

private theorem local_core_contact {A : Type*} [DecidableEq A]
    (cp : ℕ → Point) (vp : A → Point) {e f : ℕ × A × Route}
    (he : e.2.2.head? = some (cp e.1) ∧ e.2.2.getLast? = some (vp e.2.1))
    (hf : f.2.2.head? = some (cp f.1) ∧ f.2.2.getLast? = some (vp f.2.1))
    {p : ℝ × ℝ}
    (hcontact : ∃ a ∈ (if e.1 = f.1 then [cp e.1] else []) ++
      (if e.2.1 = f.2.1 then [vp e.2.1] else []), p = realPoint a) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd e.2.2 a ∧ RouteEnd f.2.2 a := by
  obtain ⟨a, ha, hpa⟩ := hcontact
  refine ⟨a, hpa, ?_⟩
  simp only [List.mem_append] at ha
  rcases ha with ha | ha
  · split_ifs at ha with hclause
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨Or.inl he.1, Or.inl (by simpa only [hclause] using hf.1)⟩
    · exact False.elim (List.not_mem_nil ha)
  · split_ifs at ha with hvar
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨Or.inr he.2, Or.inr (by simpa only [hvar] using hf.2)⟩
    · exact False.elim (List.not_mem_nil ha)

private theorem translated_local_contact {r s : Route} (v : Point)
    (hlocal : ∀ p ∈ support r, p ∈ support s →
      ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a)
    {p : ℝ × ℝ} (hp : p ∈ support (translate v r)) (hq : p ∈ support (translate v s)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd (translate v r) a ∧ RouteEnd (translate v s) a := by
  let x := p - realPoint v
  have hx : x + realPoint v = p := sub_add_cancel _ _
  have hp' := (mem_support_translate_iff v r x).1 (hx ▸ hp)
  have hq' := (mem_support_translate_iff v s x).1 (hx ▸ hq)
  obtain ⟨a, hxa, ha, hb⟩ := hlocal x hp' hq'
  refine ⟨a + v, ?_, ha.translate v, hb.translate v⟩
  rw [realPoint_add, ← hxa, hx]

private theorem corePieces_contact {φ : CNF ℕ} {r s : Route} {c d : Point}
    (hr : CorePiece φ r c) (hs : CorePiece φ s d) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  have hc := hr.interior hp
  have hd := hs.interior hq
  have hcd := cell_eq_of_mem_open_closed (by decide) hc
    ⟨hd.1.le, hd.2.1.le, hd.2.2.1.le, hd.2.2.2.le⟩
  subst d
  cases hr with
  | @ordinary c hc e he =>
    cases hs with
    | @ordinary _ hd f hf =>
      apply translated_local_contact _ ?_ hp hq
      intro x hx hy
      have hef : e ≠ f := fun heq => hne (heq ▸ rfl)
      exact local_core_contact OrdinaryRing.clausePosition OrdinaryRing.variablePosition
        (OrdinaryRing.incidence_endpoints _ he).2 (OrdinaryRing.incidence_endpoints _ hf).2
        (OrdinaryRing.routes_contact he hf hef hx hy)
    | crossing hd hf => exact False.elim (((mem_ordinaryCells φ _).1 hc).2 hd)
  | @crossing c hc e he =>
    cases hs with
    | ordinary hd hf => exact False.elim (((mem_ordinaryCells φ _).1 hd).2 hc)
    | @crossing _ hd f hf =>
      apply translated_local_contact _ ?_ hp hq
      intro x hx hy
      have hef : e ≠ f := fun heq => hne (heq ▸ rfl)
      exact local_core_contact PairedCrossover.clausePosition PairedCrossover.variablePosition
        (PairedCrossover.incidence_endpoints _ he).2 (PairedCrossover.incidence_endpoints _ hf).2
        (PairedCrossover.routes_contact he hf hef hx hy)

private theorem core_spoke_disjoint {φ : CNF ℕ} {r s : Route} {c d : Point} {i : Fin 4}
    (hr : CorePiece φ r c) (hs : SpokePiece φ s d i) :
    Disjoint (support r) (support (translate (cellOrigin 120 d) (PairedPorts.spokeRoute i))) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hcd := cell_eq_of_mem_open_closed (by decide) (hr.interior hp) (spoke_support_cell d i hq)
  obtain ⟨j, hj, hd⟩ := hs.clause_cell
  exact hr.not_clause_cell hj (hcd.trans hd)

private theorem core_access_contact {φ : CNF ℕ} {r s : Route} {c d q : Point} {l : Fin 2}
    (hr : CorePiece φ r c) (hs : AccessPiece φ s d q l) {p : ℝ × ℝ}
    (hp : p ∈ support r) (hq : p ∈ support (access (crossingSites φ) d q l)) :
    ∃ a : Point, p = realPoint a ∧ RouteEnd r a ∧ RouteEnd s a := by
  have hcd := cell_eq_of_mem_open_closed (by decide) (hr.interior hp)
    (access_support_cell (crossingSites φ) d q l hq).1
  subst d
  let x := p - realPoint (cellOrigin 120 c)
  have hx : x + realPoint (cellOrigin 120 c) = p := sub_add_cancel _ _
  have hq' : x ∈ support (PairedPorts.accessRoute (side c q) l) := by
    apply (mem_support_translate_iff (cellOrigin 120 c) (PairedPorts.accessRoute (side c q) l) x).1
    rw [access_eq_translate] at hq
    exact hx ▸ hq
  cases hr with
  | ordinary hc he =>
    have hp' := (mem_support_translate_iff _ _ _).1 (hx ▸ hp)
    obtain ⟨hevar, hxp⟩ := OrdinaryRing.access_contact he hq' hp'
    refine ⟨cellOrigin 120 c + PairedPorts.variablePosition (side c q) l, ?_, Or.inr ?_, Or.inr ?_⟩
    · rw [← hx, hxp, OrdinaryRing.variablePosition, realPoint_add, add_comm]
    · simp only [translate, List.getLast?_map, (OrdinaryRing.incidence_endpoints _ he).2.2,
        hevar, OrdinaryRing.variablePosition, Option.map_some, add_comm]
    · rw [hs.inner_endpoint, signal_position]
  | crossing hc he =>
    have hp' := (mem_support_translate_iff _ _ _).1 (hx ▸ hp)
    obtain ⟨hevar, hxp⟩ := PairedCrossover.access_contact he hq' hp'
    refine ⟨cellOrigin 120 c + PairedPorts.variablePosition (side c q) l, ?_, Or.inr ?_, Or.inr ?_⟩
    · change x = realPoint (PairedPorts.variablePosition (side c q) l) at hxp
      rw [← hx, hxp, realPoint_add, add_comm]
    · simp only [translate, List.getLast?_map, (PairedCrossover.incidence_endpoints _ he).2.2,
        hevar, Option.map_some, PairedCrossover.terminal, PairedCrossover.variablePosition,
        add_comm]
    · rw [hs.inner_endpoint, signal_position]

private theorem route_support_cases {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {p : ℝ × ℝ} (hp : p ∈ support r) :
    (∃ c, CorePiece φ r c) ∨
      (∃ c q l, AccessPiece φ r c q l ∧ p ∈ support (access (crossingSites φ) c q l)) ∨
        ∃ c s, SpokePiece φ r c s ∧
          p ∈ support (translate (cellOrigin 120 c) (PairedPorts.spokeRoute s)) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨c, hc, hpc⟩) | ⟨c, hc, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, heq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only at heq
    subst r
    rw [support_lastLiteral _ _ _ (PlanarCompile.occurrencePath_last_unit ho)] at hp
    rcases hp with hp | hp
    · exact Or.inr (Or.inr ⟨_, _, SpokePiece.final ho, hp⟩)
    · exact Or.inr (Or.inl ⟨_, _, _, AccessPiece.final ho, hp⟩)
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨c, CorePiece.ordinary hc (List.mem_filter.mp he).1⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact Or.inl ⟨c, CorePiece.crossing hc (List.mem_filter.mp he).1⟩
  · obtain ⟨e, he, hpc⟩ := List.mem_flatMap.mp hpc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;>
      rcases link_routes_cases _ _ _ _ hr with rfl | rfl
    all_goals
      apply Or.inr
      apply Or.inl
      first
      | exact ⟨_, _, _, AccessPiece.link ho he _, hp⟩
      | exact ⟨_, _, _, AccessPiece.reverseLink ho he _, hp⟩

/-- Distinct actual route values meet only at endpoints of both routes, over the complete
real plane. Unit-step ownership includes the omitted final binary link. -/
theorem route_contacts {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r s : Route} (hr : r ∈ routes φ) (hs : s ∈ routes φ) (hne : r ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ support r) (hq : p ∈ support s) :
    ∃ a : Point, p = realPoint a ∧
      (r.head? = some a ∨ r.getLast? = some a) ∧
      (s.head? = some a ∨ s.getLast? = some a) := by
  rcases route_support_cases hr hp with ⟨c, hr'⟩ | ⟨c, q, l, hr', hp'⟩ | ⟨c, i, hr', hp'⟩
  · rcases route_support_cases hs hq with ⟨d, hs'⟩ | ⟨d, t, k, hs', hq'⟩ | ⟨d, j, hs', hq'⟩
    · exact corePieces_contact hr' hs' hne hp hq
    · exact core_access_contact hr' hs' hp hq'
    · exact False.elim (Set.disjoint_left.mp (core_spoke_disjoint hr' hs') hp hq')
  · rcases route_support_cases hs hq with ⟨d, hs'⟩ | ⟨d, t, k, hs', hq'⟩ | ⟨d, j, hs', hq'⟩
    · obtain ⟨a, ha, hsEnd, hrEnd⟩ := core_access_contact hs' hr' hq hp'
      exact ⟨a, ha, hrEnd, hsEnd⟩
    · exact accessPieces_contact hw hv hr' hs' hne hp' hq'
    · exact False.elim (Set.disjoint_left.mp (spoke_access_disjoint hw hv hs' hr' hne.symm) hq' hp')
  · rcases route_support_cases hs hq with ⟨d, hs'⟩ | ⟨d, t, k, hs', hq'⟩ | ⟨d, j, hs', hq'⟩
    · exact False.elim (Set.disjoint_left.mp (core_spoke_disjoint hs' hr') hq hp')
    · exact False.elim (Set.disjoint_left.mp (spoke_access_disjoint hw hv hr' hs' hne) hp' hq')
    · exact spokePieces_contact hw hv hr' hs' hne hp' hq'

private theorem lastLiteral_route_injective {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {b b' : Bool}
    (h : (lastLiteral (crossingSites φ) (occurrencePath φ o) b).2 =
      (lastLiteral (crossingSites φ) (occurrencePath φ t) b').2) : o = t := by
  have hb := congrArg (fun r : Route => r.getD 2 (0, 0)) h
  simp only [lastLiteral, List.getD_cons_succ, List.getD_cons_zero] at hb
  have ho' := shared_boundary (PlanarCompile.occurrencePath_last_unit ho)
    (PairedPorts.spokeLane
      (side (lastStep (occurrencePath φ o)).2 (lastStep (occurrencePath φ o)).1))
  have ht' := shared_boundary (PlanarCompile.occurrencePath_last_unit ht)
    (PairedPorts.spokeLane
      (side (lastStep (occurrencePath φ t)).2 (lastStep (occurrencePath φ t)).1))
  exact (boundary_occurrence_step_unique hw hv ho ht (lastStep_mem ho) (lastStep_mem ht)
    (ho'.trans (hb.trans ht'.symm))).2.1

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

private theorem ordinary_routes_nodup_check : ∀ i : Fin 8,
    ((OrdinaryRing.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2).Nodup := by
  decide +kernel

private theorem crossing_routes_nodup_check : ∀ i : Fin 78,
    ((PairedCrossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2).Nodup := by
  decide +kernel

private theorem access_reverse_ne {sites : List Point} {p q : Point} {l : Fin 2}
    (h : Orthogonal.length p q = 1) : access sites p q l ≠ access sites q p l := by
  intro heq
  have hvar := congrArg List.getLast? heq
  change some (variablePosition (signal sites p q l)) =
    some (variablePosition (signal sites q p l)) at hvar
  have hp := variablePosition_mem_openCell (signal sites p q l)
  have hq := variablePosition_mem_openCell (signal sites q p l)
  rw [← Option.some.inj hvar] at hq
  have hpq : p = q := cell_eq_of_mem_open_closed (by decide) hp
    ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩
  subst q
  simp [Orthogonal.length] at h

private theorem placedClause_routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) : pc.2.2.Nodup := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with ((hpc | ⟨c, _, hpc⟩) | ⟨c, _, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    exact originalClause_routes_nodup_at hw hv hci
  · obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : i < 8 := by
      simpa only [Nat.zero_add, OrdinaryRing.formula_sizes.1] using (List.mem_zipIdx hci).2.1
    have hn := (ordinary_routes_nodup_check ⟨i, hi⟩).map
      (f := Orthogonal.translate (cellOrigin 120 c))
      (fun _ _ h => (List.map_inj_right (fun _ _ h => add_right_cancel h)).mp h)
    simpa only [List.map_map, Function.comp_def] using hn
  · obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : i < 78 := by
      simpa only [Nat.zero_add, PairedCrossover.length_formula] using (List.mem_zipIdx hci).2.1
    have hn := (crossing_routes_nodup_check ⟨i, hi⟩).map
      (f := Orthogonal.translate (cellOrigin 120 c))
      (fun _ _ h => (List.map_inj_right (fun _ _ h => add_right_cancel h)).mp h)
    simpa only [List.map_map, Function.comp_def] using hn
  · obtain ⟨e, he, hpc⟩ := List.mem_flatMap.mp hpc
    have hne (l : Fin 2) := access_reverse_ne (sites := crossingSites φ) (l := l)
      (PlanarCompile.occurrencePath_unit ho (prefixStep_mem he))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl <;> simp [link, hne, Ne.symm (hne _)]

private theorem placedClause_route_head (φ : CNF ℕ) {r : Route} (pc : PlacedClause)
    (hpc : pc ∈ placedClauses φ) (hr : r ∈ pc.2.2) : r.head? = some pc.2.1 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < pc.1.length := by rwa [← placedClause_route_count φ pc hpc]
  have hzip : (pc.1[i], pc.2.2[i]) ∈ pc.1.zip pc.2.2 := by
    have hk : i < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
    simpa only [List.getElem_zip] using (List.getElem_mem hk)
  exact (placedClause_endpoints φ hpc hzip).1

/-- Distinct actual incidence occurrences have distinct polygonal route lists. -/
theorem routes_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (routes φ).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun _ hpc => placedClause_routes_nodup hw hv hpc, ?_⟩
  have hn := clausePositions_nodup hw hv
  rw [List.Nodup, List.pairwise_map] at hn
  apply hn.imp_of_mem
  intro pc pd hpc hpd hpos r hr hs
  exact hpos (Option.some.inj ((placedClause_route_head φ pc hpc hr).symm.trans
    (placedClause_route_head φ pd hpd hs)))

private theorem route_declared_endpoints (φ : CNF ℕ) {r : Route} (hr : r ∈ routes φ) :
    ∃ pc ∈ placedClauses φ, ∃ v ∈ (rawFormula φ).vars,
      r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition v) := by
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < pc.1.length := by rwa [← placedClause_route_count φ pc hpc]
  have hz : i < (pc.1.zip pc.2.2).length := by simp only [List.length_zip]; omega
  have hzip : (pc.1[i], pc.2.2[i]) ∈ pc.1.zip pc.2.2 := by
    simpa only [List.getElem_zip] using (List.getElem_mem hz)
  have hv : pc.1[i].1 ∈ (rawFormula φ).vars := CNF.mem_vars.mpr
    ⟨pc.1, List.mem_map_of_mem hpc, pc.1[i].2, List.getElem_mem hi'⟩
  exact ⟨pc, hpc, _, hv, placedClause_endpoints φ hpc hzip⟩

private theorem variable_ne_clause {φ : CNF ℕ} {v : Variable} {pc : PlacedClause}
    (hv : v ∈ (rawFormula φ).vars) (hpc : pc ∈ placedClauses φ) :
    variablePosition v ≠ pc.2.1 := by
  intro heq
  apply variable_clause_positions_disjoint φ
    (List.mem_map_of_mem (CNF.mem_distinctVars.mpr hv))
  rw [heq]
  exact List.mem_map_of_mem hpc

private theorem routeEnd_clause_is_head {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {pc : PlacedClause} (hpc : pc ∈ placedClauses φ) (hend : RouteEnd r pc.2.1) :
    r.head? = some pc.2.1 := by
  rcases hend with hend | hend
  · exact hend
  · obtain ⟨pd, _, v, hv, _, hlast⟩ := route_declared_endpoints φ hr
    exact False.elim (variable_ne_clause hv hpc (Option.some.inj (hlast.symm.trans hend)))

private theorem route_originalClause_contact {φ : CNF ℕ} {r : Route} (hr : r ∈ routes φ)
    {i : ℕ} (hi : i < φ.length)
    (hp : realPoint (center (Layout.center (φ.distinctVars.length + i))) ∈ support r) :
    r.head? = some (center (Layout.center (φ.distinctVars.length + i))) := by
  have hcenter := center_mem_openCell (r := 120) (by decide)
    (Layout.center (φ.distinctVars.length + i))
  rcases route_support_cases hr hp with ⟨c, hcore⟩ | ⟨c, q, l, haccess, hp⟩ | ⟨c, s, hspoke, hp⟩
  · have hc := hcore.interior hp
    have hcell := cell_eq_of_mem_open_closed (by decide) hcenter
      ⟨hc.1.le, hc.2.1.le, hc.2.2.1.le, hc.2.2.2.le⟩
    exact False.elim (hcore.not_clause_cell hi hcell.symm)
  · have hcell := cell_eq_of_mem_open_closed (by decide) hcenter
      (access_support_cell (crossingSites φ) c q l hp).1
    exact False.elim (haccess.not_clause_cell hi hcell.symm)
  · have hcell := cell_eq_of_mem_open_closed (by decide) hcenter (spoke_support_cell c s hp)
    simpa only [hcell] using hspoke.outer_endpoint

/-- Every actual route meets an actual clause vertex only at its own clause endpoint.
The original-clause case includes isolated empty clauses. -/
theorem route_clause_contact {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {r : Route} (hr : r ∈ routes φ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    (hp : realPoint pc.2.1 ∈ support r) : r.head? = some pc.2.1 := by
  rcases placedClause_nonempty_or_original hpc with hne | horiginal
  · have hlen : 0 < pc.2.2.length := by
      rw [placedClause_route_count φ pc hpc]
      exact List.length_pos_iff.mpr hne
    let s := pc.2.2[0]
    have hsmem : s ∈ pc.2.2 := List.getElem_mem hlen
    have hs : s ∈ routes φ := List.mem_flatMap.mpr ⟨pc, hpc, hsmem⟩
    have hshead := placedClause_route_head φ pc hpc hsmem
    by_cases hrs : r = s
    · exact hrs ▸ hshead
    · have hps : realPoint pc.2.1 ∈ support s := by
        apply Or.inl
        refine ⟨pc.2.1, ?_, rfl⟩
        obtain ⟨tail, ht⟩ := List.head?_eq_some_iff.mp hshead
        rw [ht]
        exact List.mem_cons_self
      obtain ⟨a, hpa, hrEnd, _⟩ := route_contacts hw hv hr hs hrs hp hps
      have ha : pc.2.1 = a := realPoint_injective hpa
      rw [← ha] at hrEnd
      exact routeEnd_clause_is_head hr hpc hrEnd
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp horiginal
    have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    exact route_originalClause_contact hr hi hp

private theorem drawingPosition_eq_getD {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ (SAT.incidenceGraph (formula φ)).1) :
    Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) v =
      (positions φ).getD v (0, 0) := by
  have hi : v < (formula φ).distinctVars.length + (formula φ).length := by
    simpa only [SAT.incidenceGraph, List.mem_range] using hv
  simp only [Graph.drawingPosition, SAT.incidenceGraph]
  rw [idxOf_range_eq hi]

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
      Graph.drawingPosition (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) b) :
    a = b := by
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

/-- Actual indexed routes avoid all nonincident declared graph vertices. -/
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

/-- Actual indexed incidence routes meet only at their shared declared graph endpoints. -/
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

/-- The actual paired-port compiler supplies a continuous planar orthogonal drawing.
The only assumptions are source width and literal-occurrence bounds of three. -/
theorem isPlanarOrthogonalDrawing {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph (formula φ)) (positions φ, routes φ) where
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

end Cslib.Complexity.SAT.ParsimoniousPlanar
