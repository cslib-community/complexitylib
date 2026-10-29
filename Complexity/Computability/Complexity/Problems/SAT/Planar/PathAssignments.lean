/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Logics.Propositional.CNF.Planar.CrossoverSplit
import Complexity.Foundations.Data.List.Filter
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Compatible assignments on canonical paths

The optional crossover tags are retained only as a logical assignment bridge for the
paired compiler. There is no second output formula or drawing. A compatible assignment
carries each source value along its path and satisfies each selected fixed crossover.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.Variable`, `.signal`, `.wire`: the logical path bridge.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.occurrencePath_crossing_straight`.
* `Cslib.Complexity.SAT.PlanarCompile.source_center_not_crossing`.
* `Cslib.Complexity.SAT.PlanarCompile.ordinary_cell_source_eq`.
* `Cslib.Complexity.SAT.PlanarCompile.crossing_axis_occurrence_eq`.
* `Cslib.Complexity.SAT.PlanarCompile.exists_compatible_assignment`.

## References

These are the shared canonical incidence-path constructions and certificates.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- A cell's ordinary signal, or a local variable of its crossover. -/
abbrev Variable := Point × Option Crossover.SplitVariable

/-- The signal presented by a cell toward a neighboring cell. -/
def signal (sites : List Point) (p q : Point) : Variable :=
  (p, if p ∈ sites then some (Crossover.splitTerminal (side p q)) else none)

/-- Every cell before the original clause vertex contributes an entry/exit signal pair.
At the source endpoint the unused entry defaults to the source's own ordinary signal. -/
def wire (sites : List Point) (r : Route) : List (Variable × Variable) :=
  r.dropLast.zipIdx.map fun (p, i) =>
    (signal sites p (r.getD (i - 1) p), signal sites p (r.getD (i + 1) p))

/-- A path contributes one signal cell for each point before its final clause vertex. -/
theorem length_wire (sites : List Point) (r : Route) :
    (wire sites r).length = r.length - 1 := by simp [wire]

/-- Every path of at least two points yields a nonempty cell wire. -/
theorem wire_ne_nil (sites : List Point) (r : Route) (h : 2 ≤ r.length) : wire sites r ≠ [] := by
  intro he
  have hl := length_wire sites r
  rw [he, List.length_nil] at hl
  omega

/-- Exact indexed cell signals in the executable wire list. -/
theorem getElem_wire (sites : List Point) (r : Route) (i : ℕ) (hi : i < r.length - 1) :
    (wire sites r)[i]'(by simpa [wire] using hi) =
      (signal sites r[i] (r.getD (i - 1) r[i]),
        signal sites r[i] (r.getD (i + 1) r[i])) := by
  simp only [wire, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.getElem_dropLast]

/-- The actual graph edge has the occurrence's original variable and clause labels. -/
theorem occurrence_edgeEndpoint {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (side : Bool) :
    (SAT.incidenceGraph φ).edgeEndpoint ((Cslib.Logic.PL.occurrences φ).idxOf o) side =
      if side then φ.distinctVars.length + o.1 else φ.distinctVars.idxOf o.2.2.1 := by
  unfold Graph.edgeEndpoint
  rw [List.getD_eq_getElem _ _ (occurrence_index_lt ho)]
  simp only [SAT.incidenceGraph, List.getElem_map,
    List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]

/-- A selected crossing is traversed straight along one coordinate axis by each occupying path. -/
theorem occurrencePath_crossing_straight {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    {p : Point} (hp : p ∈ crossingSites φ) (hpi : p ∈ occurrencePath φ o) :
    StraightThrough (occurrencePath φ o) p (1, 0) ∨
      StraightThrough (occurrencePath φ o) p (0, 1) := by
  have hsite := (mem_crossingSites φ p).1 hp
  let G := SAT.incidenceGraph φ
  have hG : ∀ e ∈ G.2, e.1 ∈ G.1 ∧ e.2 ∈ G.1 :=
    fun _ he => SAT.incidenceGraph_endpoints he
  have hloop : ∀ e ∈ G.2, e.1 ≠ e.2 := fun _ he => SAT.incidenceGraph_loopless he
  have hdeg : ∀ v, G.incidenceVertices.count v ≤ 3 := SAT.incidenceGraph_degree_le hw hv
  have hi := occurrence_index_lt ho
  obtain ⟨j, hj, hji, hpj⟩ := List.exists_other_index_of_two_le_filter_contains (paths φ) p
    ((Cslib.Logic.PL.occurrences φ).idxOf o) hsite.2.2
  have hj' : j < G.2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hj
  have hpi' : p ∈ G.unitPath ((Cslib.Logic.PL.occurrences φ).idxOf o) := by
    simpa only [occurrencePath_eq_unitPath] using hpi
  have hpj' : p ∈ G.unitPath j := by
    unfold Graph.unitPath
    change p ∈ (SAT.incidenceGraph φ).unitPaths.getD j []
    rw [← paths_eq_unitPaths, List.getD_eq_getElem _ _ hj]
    exact hpj
  have hnb := Graph.unitPath_crossing_neighbors G hG hloop hdeg hi hj' (Ne.symm hji)
    hsite.2.1 hpi' hpj'
  rcases hnb with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl (by simpa only [occurrencePath_eq_unitPath] using h)
  · exact Or.inr (by simpa only [occurrencePath_eq_unitPath] using h)

/-- The initial source center is excluded from the actual selected crossing list. -/
theorem source_center_not_crossing {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    Layout.center (φ.distinctVars.idxOf o.2.2.1) ∉ crossingSites φ := by
  intro hp
  have hvar := List.idxOf_lt_length_of_mem
    (CNF.mem_distinctVars.mpr (variable_mem_of_mem_occurrences ho))
  apply ((mem_crossingSites φ _).1 hp).2.1
  apply List.mem_map.mpr
  refine ⟨φ.distinctVars.idxOf o.2.2.1, ?_, rfl⟩
  apply List.mem_range.mpr
  simp only [SAT.incidenceGraph, List.length_range]
  omega

/-- The executable first entry is the original variable's ordinary cell signal. -/
theorem wire_first_entry {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (fallback : Variable) :
    ((wire (crossingSites φ) (occurrencePath φ o)).headD (fallback, fallback)).1 =
      (Layout.center (φ.distinctVars.idxOf o.2.2.1), none) := by
  have hlen := occurrencePath_length_ge_two ho
  have hwpos : 0 < (wire (crossingSites φ) (occurrencePath φ o)).length := by
    rw [length_wire]
    omega
  have hhead : (wire (crossingSites φ) (occurrencePath φ o)).headD (fallback, fallback) =
      (wire (crossingSites φ) (occurrencePath φ o))[0] := by
    generalize hc : wire (crossingSites φ) (occurrencePath φ o) = xs at hwpos ⊢
    cases xs with
    | nil => simp at hwpos
    | cons a rest => rfl
  rw [hhead, getElem_wire _ _ 0 (by omega)]
  simp only [Nat.zero_sub]
  rw [List.getD_eq_getElem _ _ (by omega)]
  have hp := (occurrencePath_endpoints ho).1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hp
  rw [Option.some.inj hp]
  simp only [signal, source_center_not_crossing ho, ite_false]

private theorem path_mem_paths_get {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {p : Point} (hp : p ∈ occurrencePath φ o) :
    p ∈ (paths φ)[(Cslib.Logic.PL.occurrences φ).idxOf o]'(by
      simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ho) := by
  unfold occurrencePath at hp
  rwa [List.getD_eq_getElem _ _ (by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ho)] at hp

/-- Two different occurrence paths sharing an ordinary cell meet at a declared vertex center. -/
theorem shared_ordinary_cell_center {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) (hot : o ≠ t) {p : Point}
    (hp : p ∉ crossingSites φ) (hpo : p ∈ occurrencePath φ o)
    (hpt : p ∈ occurrencePath φ t) : p ∈ (SAT.incidenceGraph φ).orthogonalPositions := by
  by_contra hc
  have hij : (Cslib.Logic.PL.occurrences φ).idxOf o ≠
      (Cslib.Logic.PL.occurrences φ).idxOf t := fun he => hot ((List.idxOf_inj ho).1 he)
  have hcandidate := Graph.unitPath_shared_mem_crossingCandidates (SAT.incidenceGraph φ)
    (fun _ he => SAT.incidenceGraph_endpoints he)
    (fun _ he => SAT.incidenceGraph_loopless he) (SAT.incidenceGraph_degree_le hw hv)
    (occurrence_index_lt ho) (occurrence_index_lt ht) hij hc
    (by simpa only [occurrencePath_eq_unitPath] using hpo)
    (by simpa only [occurrencePath_eq_unitPath] using hpt)
  apply hp
  apply (mem_crossingSites φ p).2
  refine ⟨hcandidate, hc, ?_⟩
  exact (List.two_le_filter_contains_iff (paths φ) p).2
    ⟨_, _,
      by simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ho,
      by simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ht,
      hij, path_mem_paths_get ho hpo, path_mem_paths_get ht hpt⟩

/-- No retained wire cell is the clause-center endpoint removed by `dropLast`. -/
theorem clause_center_not_mem_dropLast {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    Layout.center (φ.distinctVars.length + o.1) ∉ (occurrencePath φ o).dropLast := by
  intro hp
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hp
  have hlen := occurrencePath_length_ge_two ho
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have hlast := (occurrencePath_endpoints ho).2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
  have heq' : (occurrencePath φ o)[k] =
      (occurrencePath φ o)[(occurrencePath φ o).length - 1] := by
    rw [← List.getElem_dropLast hk, heq, Option.some.inj hlast]
  have hidx := (occurrencePath_nodup ho).getElem_inj_iff.1 heq'
  simp only [List.length_dropLast] at hk
  omega

/-- A retained cell at a declared center is the source-variable center of its occurrence. -/
theorem dropLast_center_eq_source {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {p : Point}
    (hp : p ∈ (occurrencePath φ o).dropLast)
    (hc : p ∈ (SAT.incidenceGraph φ).orthogonalPositions) :
    p = Layout.center (φ.distinctVars.idxOf o.2.2.1) := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  have hw' := List.mem_range.mp hw
  have hwmem : w ∈ (SAT.incidenceGraph φ).1 := by
    apply List.mem_range.mpr
    simpa only [SAT.incidenceGraph, List.length_range] using hw'
  have hi := List.idxOf_lt_length_of_mem hwmem
  have hidx : (SAT.incidenceGraph φ).1.idxOf w = w := by
    simpa only [SAT.incidenceGraph, List.getElem_range] using List.getElem_idxOf hi
  have h := (Graph.unitPath_declared_center_iff (SAT.incidenceGraph φ)
    (fun _ he => SAT.incidenceGraph_endpoints he)
    (fun _ he => SAT.incidenceGraph_loopless he) (occurrence_index_lt ho) hwmem).1
    (by rw [hidx]; simpa only [occurrencePath_eq_unitPath] using List.dropLast_subset _ hp)
  simp only [SAT.incidenceGraph, List.getElem_map,
    List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)] at h
  rcases h with h | h
  · rw [h]
  · exact False.elim (clause_center_not_mem_dropLast ho (h ▸ hp))

/-- All occurrences using an ordinary retained cell have the same original variable. -/
theorem ordinary_cell_source_eq {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {p : Point} (hp : p ∉ crossingSites φ)
    (hpo : p ∈ (occurrencePath φ o).dropLast)
    (hpt : p ∈ (occurrencePath φ t).dropLast) : o.2.2.1 = t.2.2.1 := by
  by_cases hot : o = t
  · rw [hot]
  have hc := shared_ordinary_cell_center hw hv ho ht hot hp
    (List.dropLast_subset _ hpo) (List.dropLast_subset _ hpt)
  have he := (dropLast_center_eq_source ho hpo hc).symm.trans
    (dropLast_center_eq_source ht hpt hc)
  have hx := congrArg Prod.fst he
  simp only [Layout.center] at hx
  have hi : φ.distinctVars.idxOf o.2.2.1 = φ.distinctVars.idxOf t.2.2.1 := by omega
  apply (List.idxOf_inj ?_).1 hi
  apply CNF.mem_distinctVars.mpr
  rw [← Cslib.Logic.PL.map_occurrences]
  exact List.mem_map_of_mem ho

private theorem not_both_straight {r : Route} (hn : r.Nodup) {p : Point} (hp : p ∈ r)
    (hh : StraightThrough r p (1, 0)) (hv : StraightThrough r p (0, 1)) : False := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hp
  obtain ⟨_, _, hhn⟩ := hh.getD_neighbors hn hk heq
  obtain ⟨_, _, hvn⟩ := hv.getD_neighbors hn hk heq
  rcases hhn with ⟨hh, _⟩ | ⟨hh, _⟩ <;> rcases hvn with ⟨hv, _⟩ | ⟨hv, _⟩
  all_goals
    have hx := congrArg Prod.fst (hh.symm.trans hv)
    simp only [Prod.fst_sub, Prod.fst_add] at hx
    omega

/-- The occurrence carrying either coordinate-axis signal at a crossing is unique. -/
theorem crossing_axis_occurrence_eq {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {o t : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ)
    (ht : t ∈ Cslib.Logic.PL.occurrences φ) {p d : Point}
    (hp : p ∈ crossingSites φ) (hpo : p ∈ occurrencePath φ o)
    (hpt : p ∈ occurrencePath φ t) (hd : d = (1, 0) ∨ d = (0, 1))
    (hs : StraightThrough (occurrencePath φ o) p d)
    (hts : StraightThrough (occurrencePath φ t) p d) : o = t := by
  by_contra hot
  have hij : (Cslib.Logic.PL.occurrences φ).idxOf o ≠
      (Cslib.Logic.PL.occurrences φ).idxOf t := fun he => hot ((List.idxOf_inj ho).1 he)
  have hn := Graph.unitPath_crossing_neighbors (SAT.incidenceGraph φ)
    (fun _ he => SAT.incidenceGraph_endpoints he)
    (fun _ he => SAT.incidenceGraph_loopless he) (SAT.incidenceGraph_degree_le hw hv)
    (occurrence_index_lt ho) (occurrence_index_lt ht) hij
    ((mem_crossingSites φ p).1 hp).2.1
    (by simpa only [occurrencePath_eq_unitPath] using hpo)
    (by simpa only [occurrencePath_eq_unitPath] using hpt)
  rw [← occurrencePath_eq_unitPath, ← occurrencePath_eq_unitPath] at hn
  rcases hd with rfl | rfl
  · rcases hn with ⟨_, htvert⟩ | ⟨hovert, _⟩
    · exact not_both_straight (occurrencePath_nodup ht) hpt hts htvert
    · exact not_both_straight (occurrencePath_nodup ho) hpo hs hovert
  · rcases hn with ⟨hohor, _⟩ | ⟨_, hthor⟩
    · exact not_both_straight (occurrencePath_nodup ho) hpo hohor hs
    · exact not_both_straight (occurrencePath_nodup ht) hpt hthor hts

open Classical in
private noncomputable def chosenValue (τ : ℕ → Bool) (P : Occurrence ℕ → Prop) : Bool :=
  if h : ∃ o, P o then τ (Classical.choose h).2.2.1 else false

private theorem chosenValue_eq (τ : ℕ → Bool) (P : Occurrence ℕ → Prop)
    {o : Occurrence ℕ} (ho : P o) (heq : ∀ t, P t → t.2.2.1 = o.2.2.1) :
    chosenValue τ P = τ o.2.2.1 := by
  classical
  have h : ∃ t, P t := ⟨o, ho⟩
  simp only [chosenValue, dite_eq_left h]
  rw [heq _ (Classical.choose_spec h)]

/-- Every source assignment extends compatibly to all actual wire cells and crossover blocks.
The choice of auxiliary values is logical; this theorem makes no computational claim. -/
theorem exists_compatible_assignment {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) (τ : ℕ → Bool) :
    ∃ σ : Variable → Bool,
      (∀ o ∈ Cslib.Logic.PL.occurrences φ,
        ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o),
          σ c.1 = τ o.2.2.1 ∧ σ c.2 = τ o.2.2.1) ∧
      (∀ p ∈ crossingSites φ, Crossover.splitFormula.eval (fun v => σ (p, some v)) = true) := by
  classical
  let ordinary (p : Point) := chosenValue τ (fun o =>
    o ∈ Cslib.Logic.PL.occurrences φ ∧ p ∈ (occurrencePath φ o).dropLast)
  let axis (p d : Point) := chosenValue τ (fun o =>
    o ∈ Cslib.Logic.PL.occurrences φ ∧ p ∈ occurrencePath φ o ∧
      StraightThrough (occurrencePath φ o) p d)
  have hord {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {p : Point}
      (hp : p ∉ crossingSites φ) (hpo : p ∈ (occurrencePath φ o).dropLast) :
      ordinary p = τ o.2.2.1 := by
    apply chosenValue_eq τ _ ⟨ho, hpo⟩
    intro t ht
    exact ordinary_cell_source_eq hw hv ht.1 ho hp ht.2 hpo
  have haxis {o : Occurrence ℕ} (ho : o ∈ Cslib.Logic.PL.occurrences φ) {p d : Point}
      (hp : p ∈ crossingSites φ) (hpo : p ∈ occurrencePath φ o)
      (hd : d = (1, 0) ∨ d = (0, 1)) (hs : StraightThrough (occurrencePath φ o) p d) :
      axis p d = τ o.2.2.1 := by
    apply chosenValue_eq τ _ ⟨ho, hpo, hs⟩
    intro t ht
    rw [crossing_axis_occurrence_eq hw hv ht.1 ho hp ht.2.1 hpo hd ht.2.2 hs]
  let cross (p : Point) : Crossover.SplitVariable → Bool :=
    Classical.choose (Crossover.exists_split_holds (axis p (1, 0)) (axis p (0, 1)))
  have hcross (p : Point) :=
    Classical.choose_spec (Crossover.exists_split_holds (axis p (1, 0)) (axis p (0, 1)))
  let σ : Variable → Bool := fun v => match v.2 with
    | none => ordinary v.1
    | some a => cross v.1 a
  refine ⟨σ, ?_, fun p _ => (hcross p).1⟩
  intro o ho c hc
  unfold wire at hc
  obtain ⟨⟨p, k⟩, hpk, rfl⟩ := List.mem_map.mp hc
  have hget := List.mem_zipIdx_iff_getElem?.mp hpk
  obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hget
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have heq' : (occurrencePath φ o)[k] = p := by
    rw [← List.getElem_dropLast hk]
    exact heq
  have hpo : p ∈ occurrencePath φ o := heq' ▸ List.getElem_mem hk'
  change (List.dropLast (occurrencePath φ o))[k] = p at heq
  have hpod : p ∈ (occurrencePath φ o).dropLast := by
    rw [← heq]
    exact List.getElem_mem hk
  by_cases hp : p ∈ crossingSites φ
  · have hl : side p (p - (1, 0)) = 0 := by
      rcases p with ⟨x, y⟩
      simp only [side, Prod.fst_sub, Prod.snd_sub]
      split_ifs <;> first | rfl | omega
    have hr : side p (p + (1, 0)) = 1 := by
      rcases p with ⟨x, y⟩
      simp only [side, Prod.fst_add, Prod.snd_add]
      split_ifs <;> first | rfl | omega
    have ht : side p (p - (0, 1)) = 2 := by
      rcases p with ⟨x, y⟩
      simp only [side, Prod.fst_sub, Prod.snd_sub]
      split_ifs <;> first | rfl | omega
    have hb : side p (p + (0, 1)) = 3 := by
      rcases p with ⟨x, y⟩
      simp only [side, Prod.fst_add, Prod.snd_add]
      split_ifs <;> first | rfl | omega
    rcases occurrencePath_crossing_straight hw hv ho hp hpo with hs | hs
    · have hav := haxis ho hp hpo (Or.inl rfl) hs
      have hports := (hcross p).2
      obtain ⟨_, _, hnb⟩ := hs.getD_neighbors (occurrencePath_nodup ho) hk' heq'
      rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
      all_goals
        simp only [hprev, hnext, signal, hp, ite_true, hl, hr, Crossover.splitTerminal]
        exact ⟨by simpa only [σ, cross, hports.1, hports.2.1] using hav,
          by simpa only [σ, cross, hports.1, hports.2.1] using hav⟩
    · have hav := haxis ho hp hpo (Or.inr rfl) hs
      have hports := (hcross p).2.2.2
      obtain ⟨_, _, hnb⟩ := hs.getD_neighbors (occurrencePath_nodup ho) hk' heq'
      rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
      all_goals
        simp only [hprev, hnext, signal, hp, ite_true, ht, hb, Crossover.splitTerminal]
        exact ⟨by simpa only [σ, cross, hports.1, hports.2] using hav,
          by simpa only [σ, cross, hports.1, hports.2] using hav⟩
  · simpa only [signal, hp, ite_false, σ] using
      And.intro (hord ho hp hpod) (hord ho hp hpod)

end Cslib.Complexity.SAT.PlanarCompile
