/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Correctness
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Compatible assignments for the actual planar compiler

An ordinary occupied cell carries its source variable's value. At a selected crossing the
horizontal and vertical source values independently extend through the fixed crossover.

## Main definitions

Compiler data and CNF semantics are reused unchanged.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.exists_compatible_assignment`: compatible actual wires
  and independent satisfying crossover blocks for every source assignment.
* `Cslib.Complexity.SAT.PlanarCompile.satisfiable_formula_iff`: actual satisfiability equivalence
  under source width and literal-occurrence bounds of three.

## References

These are original logical composition proofs for the finite compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

private theorem two_paths_filter_length (rs : List Route) (p : Point) {i j : ℕ}
    (hi : i < rs.length) (hj : j < rs.length) (hij : i ≠ j)
    (hpi : p ∈ rs[i]) (hpj : p ∈ rs[j]) :
    2 ≤ (rs.filter fun r => r.contains p).length := by
  induction rs generalizing i j with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hij rfl)
      | succ j =>
        have hj' : j < rs.length := by simpa using hj
        have hm : rs[j] ∈ rs.filter (fun r => r.contains p) :=
          List.mem_filter.mpr ⟨List.getElem_mem (by simpa using hj),
            List.contains_iff_mem.mpr hpj⟩
        obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp hm
        have hphead : p ∈ r := hpi
        simp only [List.filter_cons, List.contains_iff_mem.mpr hphead,
          ite_true, List.length_cons]
        omega
    | succ i =>
      cases j with
      | zero =>
        have hi' : i < rs.length := by simpa using hi
        have hm : rs[i] ∈ rs.filter (fun r => r.contains p) :=
          List.mem_filter.mpr ⟨List.getElem_mem (by simpa using hi),
            List.contains_iff_mem.mpr hpi⟩
        obtain ⟨k, hk, _⟩ := List.mem_iff_getElem.mp hm
        have hphead : p ∈ r := hpj
        simp only [List.filter_cons, List.contains_iff_mem.mpr hphead,
          ite_true, List.length_cons]
        omega
      | succ j =>
        have ht := ih (by simpa using hi) (by simpa using hj) (by omega) hpi hpj
        rw [List.filter_cons]
        split_ifs
        · simp only [List.length_cons]
          omega
        · exact ht

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
  exact two_paths_filter_length (paths φ) p
    (by simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ho)
    (by simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using occurrence_index_lt ht)
    hij (path_mem_paths_get ho hpo) (path_mem_paths_get ht hpt)

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

/-- An actual raw compiler output has a satisfying extension of every source model. -/
theorem satisfiable_rawFormula_of_source {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (h : φ.Satisfiable) : (rawFormula φ).Satisfiable := by
  obtain ⟨τ, hτ⟩ := h
  obtain ⟨σ, hcompat, hcross⟩ := exists_compatible_assignment hw hv τ
  exact ⟨σ, eval_rawFormula_complete_of_compatible φ τ σ
    (fun _ ho => occurrencePath_length_ge_two ho) hcompat hcross hτ⟩

/-- The actual compact compiler preserves satisfiability under source width and literal-count
bounds of three. Geometry, degree bounds, and running time are separate compiler properties. -/
theorem satisfiable_formula_iff {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (formula φ).Satisfiable ↔ φ.Satisfiable :=
  ⟨satisfiable_source_of_formula hw hv, fun h =>
    (CNF.satisfiable_compact (rawFormula φ)).2 (satisfiable_rawFormula_of_source hw hv h)⟩

end Cslib.Complexity.SAT.PlanarCompile
