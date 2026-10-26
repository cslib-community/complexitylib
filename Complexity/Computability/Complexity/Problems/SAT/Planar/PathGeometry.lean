/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
import Complexity.Foundations.Data.List.Range
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Tactic.NormNum

/-!
# Geometry of canonical incidence paths

Shared unit-step, directed-port and midpoint uniqueness certificates support the paired
compiler without retaining the obsolete directed-output formula or its drawing.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.paths_shared_step_index`.
* `Cslib.Complexity.SAT.PlanarCompile.pathPorts_nodup`.
* `Cslib.Complexity.SAT.PlanarCompile.pathMidpoints_nodup`.
* `Cslib.Complexity.SAT.PlanarCompile.clause_cell_not_mem_crossingSites`.
* `Cslib.Complexity.SAT.PlanarCompile.clause_cell_not_mem_path_dropLast`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Unit-adjacent integer cells differ by exactly one of the four cardinal displacements. -/
theorem unit_neighbor_cases {p q : Point} (h : Orthogonal.length p q = 1) :
    q = p + (-1, 0) ∨ q = p + (1, 0) ∨ q = p + (0, -1) ∨ q = p + (0, 1) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [Orthogonal.length] at h
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- Neighboring unit cells use exactly the same geometric midpoint for their shared port. -/
theorem shared_cellPort {p q : Point} (h : Orthogonal.length p q = 1) :
    cellPort 120 p (side p q) = cellPort 120 q (side q p) := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    norm_num [side, cellPort, cellOrigin, Prod.ext_iff] <;> omega

private theorem consecutivePair_index {r : Route} {a b : Point}
    (h : (a, b) ∈ r.consecutivePairs) :
    ∃ (k : ℕ) (hk : k + 1 < r.length), r[k] = a ∧ r[k + 1] = b := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp h
  have hk' : k + 1 < r.length := by
    simpa only [List.consecutivePairs, List.length_zip, List.length_tail,
      min_eq_right (Nat.sub_le _ _), Nat.lt_sub_iff_add_lt] using hk
  simp only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] at heq
  exact ⟨k, hk', congrArg Prod.fst heq, congrArg Prod.snd heq⟩

private theorem mem_of_adjacent {r : Route} {p q : Point}
    (h : (p, q) ∈ r.consecutivePairs ∨ (q, p) ∈ r.consecutivePairs) : p ∈ r := by
  rcases h with h | h
  · exact (List.of_mem_zip h).1
  · exact List.mem_of_mem_tail (List.of_mem_zip h).2

private theorem neighbor_of_straight {r : Route} {p q d : Point}
    (ht : StraightThrough r p d) (hn : r.Nodup)
    (h : (p, q) ∈ r.consecutivePairs ∨ (q, p) ∈ r.consecutivePairs) :
    q = p - d ∨ q = p + d := by
  rcases h with h | h
  · obtain ⟨k, hk, hp, hq⟩ := consecutivePair_index h
    have hh := ht.getD_neighbors hn (by omega) hp
    have hd : r.getD (k + 1) p = q := by rw [List.getD_eq_getElem _ _ hk]; exact hq
    rcases hh.2.2 with ⟨_, hnext⟩ | ⟨_, hnext⟩
    · exact Or.inr (hd.symm.trans hnext)
    · exact Or.inl (hd.symm.trans hnext)
  · obtain ⟨k, hk, hq, hp⟩ := consecutivePair_index h
    have hh := ht.getD_neighbors hn hk hp
    have hd : r.getD (k + 1 - 1) p = q := by
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
      exact hq
    rcases hh.2.2 with ⟨hprev, _⟩ | ⟨hprev, _⟩
    · exact Or.inl (hd.symm.trans hprev)
    · exact Or.inr (hd.symm.trans hprev)

private theorem horizontal_vertical_neighbors {p q : Point}
    (hx : q = p - (1, 0) ∨ q = p + (1, 0))
    (hy : q = p - (0, 1) ∨ q = p + (0, 1)) : False := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    have h := hx.symm.trans hy <;>
    have h' := congrArg Prod.fst h <;> simp at h'

private theorem canonical_neighbor_unique (G : Graph)
    (hG : ∀ e ∈ G.2, e.1 ∈ G.1 ∧ e.2 ∈ G.1)
    (hloop : ∀ e ∈ G.2, e.1 ≠ e.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p q : Point}
    (hcenter : p ∉ G.orthogonalPositions)
    (hiadj : (p, q) ∈ (G.unitPath i).consecutivePairs ∨
      (q, p) ∈ (G.unitPath i).consecutivePairs)
    (hjadj : (p, q) ∈ (G.unitPath j).consecutivePairs ∨
      (q, p) ∈ (G.unitPath j).consecutivePairs) : False := by
  have hn := Graph.unitPath_nodup G hG hloop hi
  have hm := Graph.unitPath_nodup G hG hloop hj
  rcases Graph.unitPath_crossing_neighbors G hG hloop hdeg hi hj hij hcenter
      (mem_of_adjacent hiadj) (mem_of_adjacent hjadj) with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact horizontal_vertical_neighbors (neighbor_of_straight hx hn hiadj)
      (neighbor_of_straight hy hm hjadj)
  · exact horizontal_vertical_neighbors (neighbor_of_straight hx hm hjadj)
      (neighbor_of_straight hy hn hiadj)

private theorem unit_not_both_centers (G : Graph) {p q : Point}
    (hunit : Orthogonal.length p q = 1) (hp : p ∈ G.orthogonalPositions)
    (hq : q ∈ G.orthogonalPositions) : False := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  simp only [Orthogonal.length, Layout.center] at hunit
  omega

/-- Two actual canonical paths cannot share a unit grid edge, even in opposite directions.
This count-free uniqueness statement also applies to the final step into a clause cell. -/
theorem paths_shared_step_index {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i j : ℕ} (hi : i < (paths φ).length) (hj : j < (paths φ).length) {p q : Point}
    (he : (p, q) ∈ ((paths φ).getD i []).consecutivePairs)
    (hf : (p, q) ∈ ((paths φ).getD j []).consecutivePairs ∨
      (q, p) ∈ ((paths φ).getD j []).consecutivePairs) : i = j := by
  by_contra hij
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have hj' : j < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hj
  change (p, q) ∈ ((SAT.incidenceGraph φ).unitPath i).consecutivePairs at he
  change (p, q) ∈ ((SAT.incidenceGraph φ).unitPath j).consecutivePairs ∨
    (q, p) ∈ ((SAT.incidenceGraph φ).unitPath j).consecutivePairs at hf
  have hG : ∀ e ∈ (SAT.incidenceGraph φ).2,
      e.1 ∈ (SAT.incidenceGraph φ).1 ∧ e.2 ∈ (SAT.incidenceGraph φ).1 :=
    fun _ => SAT.incidenceGraph_endpoints
  have hloop : ∀ e ∈ (SAT.incidenceGraph φ).2, e.1 ≠ e.2 :=
    fun _ => SAT.incidenceGraph_loopless
  have hdeg := SAT.incidenceGraph_degree_le hw hv
  by_cases hp : p ∈ (SAT.incidenceGraph φ).orthogonalPositions
  · have hq : q ∉ (SAT.incidenceGraph φ).orthogonalPositions := fun hq =>
      unit_not_both_centers _ (Graph.unitPath_unit _ hG hloop hi' he) hp hq
    exact canonical_neighbor_unique _ hG hloop hdeg hi' hj' hij hq (Or.inr he) hf.symm
  · exact canonical_neighbor_unique _ hG hloop hdeg hi' hj' hij hp (Or.inl he) hf

/-- At a unit neighbor, the facing side determines the neighbor itself. -/
theorem side_injective_on_unit_neighbors {p q t : Point}
    (hq : Orthogonal.length p q = 1) (ht : Orthogonal.length p t = 1)
    (hside : side p q = side p t) : q = t := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases hq with rfl | rfl | rfl | rfl <;>
    rcases unit_neighbor_cases ht with rfl | rfl | rfl | rfl <;>
    first | rfl | norm_num [side] at hside

private def stepPorts (e : Point × Point) : List (Point × Fin 4) :=
  [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]

private theorem unit_reverse {p q : Point} (h : Orthogonal.length p q = 1) :
    Orthogonal.length q p = 1 := by
  simp only [Orthogonal.length] at h ⊢
  omega

private theorem stepPorts_inter {e f : Point × Point} {x : Point × Fin 4}
    (he : Orthogonal.length e.1 e.2 = 1) (hf : Orthogonal.length f.1 f.2 = 1)
    (hx : x ∈ stepPorts e) (hy : x ∈ stepPorts f) :
    e = f ∨ e = (f.2, f.1) := by
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  simp only [stepPorts, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst c
    have hb := side_injective_on_unit_neighbors he hf hs
    exact Or.inl (Prod.ext rfl hb)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst d
    have hb := side_injective_on_unit_neighbors he (unit_reverse hf) hs
    exact Or.inr (Prod.ext rfl hb)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst c
    have ha := side_injective_on_unit_neighbors (unit_reverse he) hf hs
    exact Or.inr (Prod.ext ha rfl)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst d
    have ha := side_injective_on_unit_neighbors (unit_reverse he) (unit_reverse hf) hs
    exact Or.inl (Prod.ext ha rfl)

private theorem routePorts_nodup {r : Route} (hn : r.Nodup)
    (hu : ∀ e ∈ r.consecutivePairs, Orthogonal.length e.1 e.2 = 1) :
    (r.consecutivePairs.flatMap stepPorts).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    have hne := (axisAligned_of_length_eq_one (hu e he)).2
    simp only [stepPorts, List.nodup_cons, List.not_mem_nil, List.nodup_nil,
      List.mem_singleton, not_false_eq_true, and_true]
    exact fun h => hne (congrArg Prod.fst h)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx hy
    have hi' : i + 1 < r.length := by
      simp only [List.consecutivePairs, List.length_zip, List.length_tail] at hi
      omega
    have hj' : j + 1 < r.length := by
      simp only [List.consecutivePairs, List.length_zip, List.length_tail] at hj
      omega
    rcases stepPorts_inter (hu _ (List.getElem_mem hi)) (hu _ (List.getElem_mem hj)) hx hy
        with heq | heq
    · have heq' : r[i] = r[j] := by
        simpa only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] using
          congrArg Prod.fst heq
      have := hn.eq_of_getElem_eq (by omega) (by omega) heq'
      omega
    · have heq' : r[i] = r[j + 1] := by
        simpa only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] using
          congrArg Prod.fst heq
      have := hn.eq_of_getElem_eq (by omega) hj' heq'
      omega

/-- All directed cell ports in the actual canonical paths are distinct. Both halves of every
unit step are included, even the final clause-directed half. No path witness is assumed. -/
theorem pathPorts_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]).Nodup := by
  have hi_edge {i : ℕ} (hi : i < (paths φ).length) :
      i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have hn {i : ℕ} (hi : i < (paths φ).length) : ((paths φ)[i]).Nodup := by
    have h := Graph.unitPath_nodup (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) (hi_edge hi)
    change ((paths φ).getD i []).Nodup at h
    rwa [List.getD_eq_getElem _ _ hi] at h
  have hu {i : ℕ} (hi : i < (paths φ).length) {e : Point × Point}
      (he : e ∈ ((paths φ)[i]).consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
    apply Graph.unitPath_unit (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) (hi_edge hi)
    change e ∈ ((paths φ).getD i []).consecutivePairs
    rwa [List.getD_eq_getElem _ _ hi]
  change ((paths φ).flatMap fun r => r.consecutivePairs.flatMap stepPorts).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    exact routePorts_nodup (hn hi) (fun _ he => hu hi he)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx hy
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨f, hf, hy⟩ := List.mem_flatMap.mp hy
    have hi_step : e ∈ ((paths φ).getD i []).consecutivePairs := by
      rwa [List.getD_eq_getElem _ _ hi]
    have hj_step : (e.1, e.2) ∈ ((paths φ).getD j []).consecutivePairs ∨
        (e.2, e.1) ∈ ((paths φ).getD j []).consecutivePairs := by
      rw [List.getD_eq_getElem _ _ hj]
      rcases stepPorts_inter (hu hi he) (hu hj hf) hx hy with heq | heq
      · exact Or.inl (heq.symm ▸ hf)
      · exact Or.inr (by simpa only [heq] using hf)
    have := paths_shared_step_index hw hv hi hj hi_step hj_step
    omega

/-- Equal boundary midpoints identify the same unordered unit grid edge. -/
theorem cellPort_step_eq_cases {p q a b : Point}
    (hpq : Orthogonal.length p q = 1) (hab : Orthogonal.length a b = 1)
    (h : cellPort 120 p (side p q) = cellPort 120 a (side a b)) :
    (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
  rcases p with ⟨px, py⟩
  rcases a with ⟨ax, ay⟩
  rcases unit_neighbor_cases hpq with rfl | rfl | rfl | rfl <;>
    rcases unit_neighbor_cases hab with rfl | rfl | rfl | rfl <;>
    norm_num [side, cellPort, cellOrigin, Prod.ext_iff] at h ⊢ <;> omega

/-- One geometric midpoint per actual unit step gives a duplicate-free list.
This includes final steps, so any prefix selection used for binary clauses remains distinct. -/
theorem pathMidpoints_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.map fun e =>
      cellPort 120 e.1 (side e.1 e.2)).Nodup := by
  let steps := (paths φ).flatMap List.consecutivePairs
  have hu {e : Point × Point} (he : e ∈ steps) : Orthogonal.length e.1 e.2 = 1 := by
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < (SAT.incidenceGraph φ).2.length := by
      simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
    apply Graph.unitPath_unit (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi'
    change e ∈ ((paths φ).getD i []).consecutivePairs
    rwa [List.getD_eq_getElem _ _ hi]
  have hp : (steps.flatMap stepPorts).Nodup := by
    have h := pathPorts_nodup hw hv
    change ((paths φ).flatMap fun r => r.consecutivePairs.flatMap stepPorts).Nodup at h
    simpa only [steps, List.flatMap_assoc] using h
  have hpair := (List.nodup_flatMap.mp hp).2
  have hmid : (steps.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
    apply List.pairwise_map.mpr
    apply hpair.imp_of_mem
    intro e f he hf hd heq
    have hx : (e.1, side e.1 e.2) ∈ stepPorts e := by simp [stepPorts]
    rcases cellPort_step_eq_cases (hu he) (hu hf) heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have heq' : e = f := Prod.ext h₁ h₂
      exact hd hx (heq' ▸ hx)
    · have heq' : e = (f.2, f.1) := Prod.ext h₁ h₂
      exact hd hx (by simp [stepPorts, heq'])
  simpa only [steps, List.map_flatMap] using hmid

/-- Distinct integer cells have distinct displayed centers. -/
theorem center_injective : Function.Injective center := by
  intro p q h
  have hp := center_mem_openCell (r := 120) (by decide) p
  have hq := center_mem_openCell (r := 120) (by decide) q
  change realPoint (center p) ∈ openCell 120 p at hp
  change realPoint (center q) ∈ openCell 120 q at hq
  rw [← h] at hq
  exact cell_eq_of_mem_open_closed (by decide) hp
    ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩

/-- Original clause cells are declared source centers and are never selected as crossings. -/
theorem clause_cell_not_mem_crossingSites (φ : CNF ℕ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ crossingSites φ := by
  intro h
  apply ((mem_crossingSites φ _).mp h).2.1
  refine List.mem_map.mpr ⟨φ.distinctVars.length + i, List.mem_range.mpr ?_, rfl⟩
  simp only [SAT.incidenceGraph, List.length_range]
  omega

private theorem occurrencePath_clause_center_iff {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∈ occurrencePath φ o ↔ i = o.1 := by
  have hoidx := occurrence_index_lt ho
  have h := Graph.unitPath_center_iff (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hoidx
    (w := φ.distinctVars.length + i) (by simp only [SAT.incidenceGraph, List.length_range]; omega)
  have he : (SAT.incidenceGraph φ).2[(Cslib.Logic.PL.occurrences φ).idxOf o] =
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]
  have hb := SAT.incidenceGraph_bipartite (List.getElem_mem hoidx)
  rw [he] at hb h
  change Layout.center (φ.distinctVars.length + i) ∈ occurrencePath φ o ↔
    φ.distinctVars.length + i = (List.range _).idxOf (φ.distinctVars.idxOf o.2.2.1) ∨
      φ.distinctVars.length + i = (List.range _).idxOf (φ.distinctVars.length + o.1) at h
  rw [List.idxOf_range_of_lt (by omega), List.idxOf_range_of_lt hb.2.2] at h
  exact h.trans (by omega)

/-- No source clause center is used as a signal cell before a path's final endpoint. -/
theorem clause_cell_not_mem_path_dropLast {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ (occurrencePath φ o).dropLast := by
  intro hp
  have hi' := (occurrencePath_clause_center_iff ho hi).mp
    ((List.dropLast_sublist _).subset hp)
  subst i
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hp
  have hlen := occurrencePath_length_ge_two ho
  have hend := (occurrencePath_endpoints ho).2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hend
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have heq : (occurrencePath φ o)[k] =
      (occurrencePath φ o)[(occurrencePath φ o).length - 1] := by
    rw [Option.some.inj hend]
    simpa only [List.getElem_dropLast] using hget
  have hidx := (occurrencePath_nodup ho).eq_of_getElem_eq hk' (by omega) heq
  simp only [List.length_dropLast] at hk
  omega

end Cslib.Complexity.SAT.PlanarCompile
