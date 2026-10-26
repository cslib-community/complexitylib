/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Semantics
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
import Mathlib.Data.List.GetD
import Mathlib.Tactic.SplitIfs

/-!
# Logical correctness along the actual incidence paths

The actual compiler's occurrence paths are the canonical graph unit paths. This module uses
those path certificates to discharge endpoint and local signal conditions of the wire semantics.

## Main definitions

All compiler data and CNF operations are reused from their existing modules.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.satisfiable_source_of_formula`: actual compiler soundness
  under source width and literal-occurrence bounds of three.

## References

These are original logical composition proofs for the finite compiler.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

private theorem occurrence_var_mem {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : o.2.2.1 ∈ φ.vars := by
  rw [← Cslib.Logic.PL.map_occurrences]
  exact List.mem_map_of_mem ho

/-- The actual graph edge has the occurrence's original variable and clause labels. -/
theorem occurrence_edgeEndpoint {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) (side : Bool) :
    (SAT.incidenceGraph φ).edgeEndpoint ((Cslib.Logic.PL.occurrences φ).idxOf o) side =
      if side then φ.distinctVars.length + o.1 else φ.distinctVars.idxOf o.2.2.1 := by
  unfold Graph.edgeEndpoint
  rw [List.getD_eq_getElem _ _ (occurrence_index_lt ho)]
  simp only [SAT.incidenceGraph, List.getElem_map,
    List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]

private theorem other_path_index (rs : List Route) (p : Point) (i : ℕ) (hi : i < rs.length)
    (hcount : 2 ≤ (rs.filter fun r => r.contains p).length) :
    ∃ j, ∃ hj : j < rs.length, j ≠ i ∧ p ∈ rs[j] := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero =>
      have hpos : 0 < (rs.filter fun r => r.contains p).length := by
        rw [List.filter_cons] at hcount
        split_ifs at hcount
        · simp only [List.length_cons] at hcount
          omega
        · omega
      obtain ⟨s, hs⟩ := List.exists_mem_of_length_pos hpos
      have hm := List.mem_filter.mp hs
      obtain ⟨j, hj, hsj⟩ := List.mem_iff_getElem.mp hm.1
      refine ⟨j + 1, by simp only [List.length_cons]; omega, by omega, ?_⟩
      simp only [List.getElem_cons_succ]
      rw [hsj]
      exact List.contains_iff_mem.mp hm.2
    | succ i =>
      by_cases hmem : r.contains p = true
      · exact ⟨0, by simp, by omega, by simpa using List.contains_iff_mem.mp hmem⟩
      · have ht : 2 ≤ (rs.filter fun r => r.contains p).length := by
          have hp : p ∉ r := fun hp => hmem (List.contains_iff_mem.mpr hp)
          simpa [List.filter_cons, hp] using hcount
        obtain ⟨j, hj, hji, hp⟩ := ih i (by simp only [List.length_cons] at hi; omega) ht
        exact ⟨j + 1, by simp only [List.length_cons]; omega, by omega, by simpa using hp⟩

/-- An actual crossover whose path goes straight through a cell equates the two signals read
by the executable neighbor lookups, in either traversal direction. -/
theorem signals_eq_of_straight {φ : CNF ℕ} {σ : Variable → Bool}
    (hraw : (rawFormula φ).eval σ = true) {p : Point} (hp : p ∈ crossingSites φ)
    {r : Route} (hn : r.Nodup) {k : ℕ} (hk : k < r.length) (heq : r[k] = p)
    (hstraight : StraightThrough r p (1, 0) ∨ StraightThrough r p (0, 1)) :
    σ (signal (crossingSites φ) p (r.getD (k - 1) p)) =
      σ (signal (crossingSites φ) p (r.getD (k + 1) p)) := by
  rcases hstraight with hs | hs
  · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors hn hk heq
    rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
    · rw [hprev, hnext]
      exact horizontal_signal_eq hraw hp
    · rw [hprev, hnext]
      exact (horizontal_signal_eq hraw hp).symm
  · obtain ⟨_, _, hnb⟩ := hs.getD_neighbors hn hk heq
    rcases hnb with ⟨hprev, hnext⟩ | ⟨hprev, hnext⟩
    · rw [hprev, hnext]
      exact vertical_signal_eq hraw hp
    · rw [hprev, hnext]
      exact (vertical_signal_eq hraw hp).symm

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
  obtain ⟨j, hj, hji, hpj⟩ := other_path_index (paths φ) p
    ((Cslib.Logic.PL.occurrences φ).idxOf o)
    (by simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi) hsite.2.2
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

/-- Actual cell entry/exit values agree: ordinary cells share one variable, while selected
crossings use the certified opposite ports of the fixed crossover. -/
theorem wire_cells_agree {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (hraw : (rawFormula φ).eval σ = true) :
    ∀ o ∈ Cslib.Logic.PL.occurrences φ,
      ∀ c ∈ wire (crossingSites φ) (occurrencePath φ o), σ c.1 = σ c.2 := by
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
  have hpi : p ∈ occurrencePath φ o := by
    rw [← heq']
    exact List.getElem_mem hk'
  by_cases hp : p ∈ crossingSites φ
  · exact signals_eq_of_straight hraw hp (occurrencePath_nodup ho) hk' heq'
      (occurrencePath_crossing_straight hw hv ho hp hpi)
  · simp only [signal, hp, ite_false]

/-- The initial source center is excluded from the actual selected crossing list. -/
theorem source_center_not_crossing {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    Layout.center (φ.distinctVars.idxOf o.2.2.1) ∉ crossingSites φ := by
  intro hp
  have hvar := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr (occurrence_var_mem ho))
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

/-- Under the actual source width and literal-incidence bounds, raw output satisfaction
implies source satisfaction. No local wire equality or endpoint assumption remains. -/
theorem eval_source_of_rawFormula {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {σ : Variable → Bool} (hraw : (rawFormula φ).eval σ = true) :
    φ.eval (fun v => σ (Layout.center (φ.distinctVars.idxOf v), none)) = true := by
  apply eval_rawFormula_sound_of_cells φ _ σ
    (fun _ ho => occurrencePath_length_ge_two ho) (wire_cells_agree hw hv hraw) ?_ hraw
  intro o ho
  rw [wire_first_entry ho]

/-- Compaction preserves the soundness direction for the actual natural-labelled output. -/
theorem satisfiable_source_of_formula {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (h : (formula φ).Satisfiable) : φ.Satisfiable := by
  obtain ⟨σ, hσ⟩ := (CNF.satisfiable_compact (rawFormula φ)).1 h
  exact ⟨_, eval_source_of_rawFormula hw hv hσ⟩

end Cslib.Complexity.SAT.PlanarCompile
