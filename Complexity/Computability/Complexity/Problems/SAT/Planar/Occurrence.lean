/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Geometry
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD

/-!
# Literal occurrences in the actual planarization output

All bounds count literal positions, including repetitions within one clause. External incidences
are compared with the directed halves of the actual canonical unit paths. The final clause-cell
half is permitted in this comparison, so the comparison only overcounts the emitted variables.
The existing `CNF.vars` counts literal positions; `ClauseSet.occurrences` counts mentioning clauses
and does not suffice when a source clause repeats a variable.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.pathHalfEdges`: both directed halves of each unit step.
* `Cslib.Complexity.SAT.PlanarCompile.pathSignals`: signal names presented by these halves.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.count_vars_rawFormula_le_three`,
  `.count_vars_formula_le_three`: the actual structured and compact outputs preserve the bound
  of three literal occurrences under the source width and literal-count bounds.
* `Cslib.Complexity.SAT.PlanarCompile.count_links_lastLiteral_le`: every emitted external literal
  is bounded by the corresponding actual path halves.

## References

This literal-position accounting is original and uses the imported fixed crossover template.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Both directed cell halves of every consecutive step, in path order. -/
def pathHalfEdges (r : Route) : List (Point × Point) :=
  r.consecutivePairs.flatMap fun e => [e, e.swap]

/-- The actual signal presented by every directed cell half of a path. -/
def pathSignals (sites : List Point) (r : Route) : List Variable :=
  (pathHalfEdges r).map fun e => signal sites e.1 e.2

private theorem pathSignals_cons_cons (sites : List Point) (a b : Point) (r : Route) :
    pathSignals sites (a :: b :: r) =
      [signal sites a b, signal sites b a] ++ pathSignals sites (b :: r) := rfl

private theorem links_cons_cons_cons (sites : List Point) (positive : Bool)
    (a b c : Point) (r : Route) :
    links sites positive (a :: b :: c :: r) =
      link sites positive a b :: links sites positive (b :: c :: r) := rfl

private theorem lastLiteral_cons_cons_cons (sites : List Point) (positive : Bool)
    (a b c : Point) (r : Route) :
    lastLiteral sites (a :: b :: c :: r) positive =
      lastLiteral sites (b :: c :: r) positive := by
  simp [lastLiteral]

private theorem count_link (sites : List Point) (positive : Bool) (a b : Point) (v : Variable) :
    ((link sites positive a b).1.map Prod.fst).count v =
      ([signal sites a b, signal sites b a]).count v := by
  cases positive <;> simp [link, List.count_cons, Nat.add_comm]

/-- Links and the final original literal use only the corresponding actual path halves.
The unused reverse half at the original clause center is intentionally retained on the right. -/
theorem count_links_lastLiteral_le (sites : List Point) (positive : Bool) (r : Route)
    (hlen : 2 ≤ r.length) (v : Variable) :
    (CNF.vars ((links sites positive r).map Prod.fst)).count v +
      [(lastLiteral sites r positive).1.1].count v ≤ (pathSignals sites r).count v := by
  induction r with
  | nil => simp at hlen
  | cons a r ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      cases r with
      | nil =>
        simp [links, lastLiteral, pathSignals, pathHalfEdges, List.consecutivePairs,
          CNF.vars, List.count_cons]
      | cons c r =>
        have ht := ih (by simp : 2 ≤ (b :: c :: r).length)
        rw [links_cons_cons_cons, List.map_cons, CNF.vars, List.flatten_cons,
          List.map_append, List.count_append, lastLiteral_cons_cons_cons,
          pathSignals_cons_cons, List.count_append]
        change ((link sites positive a b).1.map Prod.fst).count v +
          (CNF.vars ((links sites positive (b :: c :: r)).map Prod.fst)).count v +
          [(lastLiteral sites (b :: c :: r) positive).1.1].count v ≤ _
        rw [count_link]
        omega

private theorem signal_eq_none_iff (sites : List Point) (a b p : Point) :
    signal sites a b = (p, none) ↔ a = p ∧ p ∉ sites := by
  by_cases h : a = p
  · subst a
    simp [signal]
  · simp [signal, Prod.mk.injEq, h]

private theorem signal_beq_none (sites : List Point) (a b p : Point) (hp : p ∉ sites) :
    (signal sites a b == (p, none)) = (a == p) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, signal_eq_none_iff, hp, not_false_eq_true, and_true]

/-- Ordinary-cell path occurrences are exactly its incoming and outgoing adjacency positions. -/
theorem count_pathSignals_none (sites : List Point) (r : Route) (p : Point) (hp : p ∉ sites) :
    (pathSignals sites r).count (p, none) = r.dropLast.count p + r.tail.count p := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => simp [pathSignals, pathHalfEdges, List.consecutivePairs]
    | cons b r =>
      rw [pathSignals_cons_cons, List.count_append]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, signal_beq_none sites _ _ p hp,
        List.dropLast_cons_cons, List.tail_cons] at *
      omega

/-- A simple path contributes at most two literal halves at one ordinary cell. -/
theorem count_pathSignals_none_le_two (sites : List Point) (r : Route) (p : Point)
    (hp : p ∉ sites) (hn : r.Nodup) : (pathSignals sites r).count (p, none) ≤ 2 := by
  rw [count_pathSignals_none sites r p hp]
  have hd := List.nodup_iff_count_le_one.mp (hn.sublist (List.dropLast_sublist _)) p
  have ht := List.nodup_iff_count_le_one.mp hn.tail p
  omega

private theorem pathSignals_cell_mem {sites : List Point} {r : Route} {v : Variable}
    (hv : v ∈ pathSignals sites r) : v.1 ∈ r := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  obtain ⟨f, hf, he⟩ := List.mem_flatMap.mp he
  have hm := List.of_mem_zip hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact hm.1
  · exact List.mem_of_mem_tail hm.2

private theorem count_pathSignals_eq_zero_of_not_mem {sites : List Point} {r : Route}
    {p : Point} (hp : p ∉ r) (v : Option Crossover.SplitVariable) :
    (pathSignals sites r).count (p, v) = 0 := by
  rw [List.count_eq_zero]
  exact fun h => hp (pathSignals_cell_mem h)

private theorem count_pathSignals_none_of_site {sites : List Point} {r : Route}
    {p : Point} (hp : p ∈ sites) : (pathSignals sites r).count (p, none) = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨e, _, he⟩ := List.mem_map.mp hm
  exact (signal_eq_none_iff sites e.1 e.2 p).mp he |>.2 hp

private theorem count_pathSignals_none_head {sites : List Point} {r : Route} {p : Point}
    (hp : p ∉ sites) (hn : r.Nodup) (hh : r.head? = some p) :
    (pathSignals sites r).count (p, none) ≤ 1 := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hh
  rw [count_pathSignals_none _ _ _ hp]
  have ht : tail.count p = 0 := List.count_eq_zero.mpr (List.nodup_cons.mp hn).1
  have hd := List.nodup_iff_count_le_one.mp
    (hn.sublist (List.dropLast_sublist _)) p
  simp only [List.tail_cons, ht, Nat.add_zero]
  exact hd

private theorem count_pathSignals_none_last {sites : List Point} {r : Route} {p : Point}
    (hp : p ∉ sites) (hn : r.Nodup) (hh : r.getLast? = some p) :
    (pathSignals sites r).count (p, none) ≤ 1 := by
  obtain ⟨initial, rfl⟩ := List.getLast?_eq_some_iff.mp hh
  rw [count_pathSignals_none _ _ _ hp]
  have hm : p ∉ initial := by
    have hdis := (List.nodup_append.mp hn).2.2
    exact fun h => hdis p h p (by simp) rfl
  have hd : (initial ++ [p]).dropLast.count p = 0 := by simp [List.count_eq_zero.mpr hm]
  rw [hd, Nat.zero_add]
  exact List.nodup_iff_count_le_one.mp hn.tail p

private theorem vars_originalClauses (φ : CNF ℕ) (sites : List Point) :
    CNF.vars ((originalClauses φ sites).map Prod.fst) =
      (Cslib.Logic.PL.occurrences φ).map
        (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1) := by
  simp [originalClauses, Cslib.Logic.PL.occurrences, CNF.vars, List.map_flatten,
    List.map_map, Function.comp_def, List.flatMap_def]

private theorem vars_crossingClauses (p : Point) :
    CNF.vars ((crossingClauses p).map Prod.fst) =
      Crossover.splitFormula.vars.map (fun v => (p, some v)) := by
  have h : (crossingClauses p).map Prod.fst =
      Crossover.splitFormula.relabel (fun v => (p, some v)) := by
    simpa only [crossingClauses, CNF.relabel, List.map_map, Function.comp_def] using
      congrArg (List.map (fun c : Clause Crossover.SplitVariable =>
        c.relabel (fun v => (p, some v))))
        (List.zipIdx_map_fst (l := Crossover.splitFormula) 0)
  rw [h, CNF.vars_relabel]

private theorem count_vars_append (φ ψ : CNF Variable) (v : Variable) :
    (φ ++ ψ).vars.count v = φ.vars.count v + ψ.vars.count v := by
  simp [CNF.vars]

private theorem count_external_blocks_le {φ : CNF ℕ} (sites : List Point) (os : List (Occurrence ℕ))
    (hpaths : ∀ o ∈ os, 2 ≤ (occurrencePath φ o).length) (v : Variable) :
    (CNF.vars ((os.flatMap fun o => links sites o.2.2.2 (occurrencePath φ o)).map
      Prod.fst)).count v +
      (os.map (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1)).count v ≤
      (os.flatMap fun o => pathSignals sites (occurrencePath φ o)).count v := by
  induction os with
  | nil => simp [CNF.vars]
  | cons o os ih =>
    have ht := ih (fun a ha => hpaths a (List.mem_cons_of_mem _ ha))
    have ho := count_links_lastLiteral_le sites o.2.2.2 (occurrencePath φ o)
      (hpaths o List.mem_cons_self) v
    rw [List.flatMap_cons, List.map_append, count_vars_append, List.map_cons,
      List.count_cons, List.flatMap_cons, List.count_append]
    have hc : [(lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1].count v =
        if (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1 == v then 1 else 0 := by
      simp [List.count_cons]
    rw [hc] at ho
    omega

/-- Internal variable names supplied by all selected translated crossover templates. -/
def crossingSignals (φ : CNF ℕ) : List Variable :=
  (crossingSites φ).flatMap fun p => Crossover.splitFormula.vars.map (fun v => (p, some v))

/-- Both directed halves of every actual source incidence path. -/
def allPathSignals (φ : CNF ℕ) : List Variable :=
  (Cslib.Logic.PL.occurrences φ).flatMap fun o =>
    pathSignals (crossingSites φ) (occurrencePath φ o)

/-- The path-half enumeration also follows the actual compiler path-list order. -/
theorem allPathSignals_eq_flatMap (φ : CNF ℕ) :
    allPathSignals φ = (paths φ).flatMap (pathSignals (crossingSites φ)) := by
  rw [← occurrencePaths_eq_paths, List.flatMap_map]
  rfl

private theorem idxOf_range_of_lt {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

/-- A source center belongs to an actual occurrence path exactly at one of its two endpoints. -/
theorem occurrencePath_center_iff {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {w : ℕ}
    (hw : w < φ.distinctVars.length + φ.length) :
    Layout.center w ∈ occurrencePath φ o ↔
      w = φ.distinctVars.idxOf o.2.2.1 ∨ w = φ.distinctVars.length + o.1 := by
  have hi : (Cslib.Logic.PL.occurrences φ).idxOf o < (SAT.incidenceGraph φ).2.length := by
    simpa only [SAT.incidenceGraph, List.length_map] using List.idxOf_lt_length_of_mem ho
  have he : (SAT.incidenceGraph φ).2[(Cslib.Logic.PL.occurrences φ).idxOf o] =
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]
  have hb := SAT.incidenceGraph_bipartite (List.getElem_mem hi)
  rw [he] at hb
  have h := Graph.unitPath_center_iff (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi
    (by simpa [SAT.incidenceGraph] using hw)
  rw [he] at h
  change Layout.center w ∈ occurrencePath φ o ↔
    w = (List.range _).idxOf (φ.distinctVars.idxOf o.2.2.1) ∨
      w = (List.range _).idxOf (φ.distinctVars.length + o.1) at h
  rw [idxOf_range_of_lt (by omega), idxOf_range_of_lt hb.2.2] at h
  exact h

/-- At every source center, all path-half incidences are bounded by its actual graph degree. -/
theorem count_allPathSignals_center_le (φ : CNF ℕ) {w : ℕ}
    (hw : w < φ.distinctVars.length + φ.length) :
    (allPathSignals φ).count (Layout.center w, none) ≤
      (SAT.incidenceGraph φ).incidenceVertices.count w := by
  have hsite : Layout.center w ∉ crossingSites φ := by
    intro hm
    have hc := (mem_crossingSites φ _).mp hm |>.2.1
    apply hc
    simp only [Graph.orthogonalPositions, List.mem_map]
    exact ⟨w, by simpa [SAT.incidenceGraph] using hw, rfl⟩
  have hpath (o : Occurrence ℕ) (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
      (pathSignals (crossingSites φ) (occurrencePath φ o)).count (Layout.center w, none) ≤
        [φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1].count w := by
    by_cases hm : Layout.center w ∈ occurrencePath φ o
    · rcases (occurrencePath_center_iff ho hw).mp hm with he | he
      · have hc := count_pathSignals_none_head hsite (occurrencePath_nodup ho)
          (he.symm ▸ (occurrencePath_endpoints ho).1)
        have hpos : 0 < [φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1].count w :=
          List.count_pos_iff.mpr (by simp [he])
        omega
      · have hc := count_pathSignals_none_last hsite (occurrencePath_nodup ho)
          (he.symm ▸ (occurrencePath_endpoints ho).2)
        have hpos : 0 < [φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1].count w :=
          List.count_pos_iff.mpr (by simp [he])
        omega
    · rw [count_pathSignals_eq_zero_of_not_mem hm]
      exact Nat.zero_le _
  simp only [allPathSignals, Graph.incidenceVertices, SAT.incidenceGraph, List.flatMap_map,
    List.count_flatMap]
  exact List.sum_le_sum hpath

private theorem paths_nodup {φ : CNF ℕ} {r : Route} (hr : r ∈ paths φ) : r.Nodup := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have h := Graph.unitPath_nodup (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi'
  change ((paths φ).getD i []).Nodup at h
  rwa [List.getD_eq_getElem _ _ hi] at h

private theorem count_pathSignals_filter_le (sites : List Point) (rs : List Route)
    (hn : ∀ r ∈ rs, r.Nodup) (p : Point) (hp : p ∉ sites) :
    (rs.flatMap (pathSignals sites)).count (p, none) ≤
      2 * (rs.filter fun r => r.contains p).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have ht := ih (fun s hs => hn s (List.mem_cons_of_mem _ hs))
    rw [List.flatMap_cons, List.count_append]
    by_cases hm : p ∈ r
    · have hc := count_pathSignals_none_le_two sites r p hp (hn r List.mem_cons_self)
      have hf : ((r :: rs).filter fun r => r.contains p) =
          r :: rs.filter (fun r => r.contains p) := by simp [hm]
      rw [hf, List.length_cons]
      omega
    · rw [count_pathSignals_eq_zero_of_not_mem hm, Nat.zero_add]
      have hf : ((r :: rs).filter fun r => r.contains p) = rs.filter (fun r => r.contains p) := by
        simp [hm]
      rwa [hf]

/-- An ordinary nonvertex cell contributes at most two actual path halves in total. -/
theorem count_allPathSignals_nonvertex_le_two {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) {p : Point}
    (hp : p ∉ crossingSites φ) (hc : p ∉ (SAT.incidenceGraph φ).orthogonalPositions) :
    (allPathSignals φ).count (p, none) ≤ 2 := by
  rw [allPathSignals_eq_flatMap]
  have h := count_pathSignals_filter_le (crossingSites φ) (paths φ)
    (fun _ => paths_nodup) p hp
  have hf := paths_filter_length_le_one hw hv hp hc
  omega

private theorem count_allPathSignals_none_of_site {φ : CNF ℕ} {p : Point}
    (hp : p ∈ crossingSites φ) : (allPathSignals φ).count (p, none) = 0 := by
  rw [allPathSignals_eq_flatMap]
  induction paths φ with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, List.count_append, count_pathSignals_none_of_site hp, ih]

/-- Ordinary variables in the actual output path list have at most three literal incidences. -/
theorem count_allPathSignals_none_le_three {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) (p : Point) :
    (allPathSignals φ).count (p, none) ≤ 3 := by
  by_cases hs : p ∈ crossingSites φ
  · rw [count_allPathSignals_none_of_site hs]
    decide
  · by_cases hc : p ∈ (SAT.incidenceGraph φ).orthogonalPositions
    · obtain ⟨w, hwmem, rfl⟩ := List.mem_map.mp hc
      have hw' : w < φ.distinctVars.length + φ.length := by
        simpa [SAT.incidenceGraph] using List.mem_range.mp hwmem
      exact (count_allPathSignals_center_le φ hw').trans (SAT.incidenceGraph_degree_le hw hv w)
    · exact (count_allPathSignals_nonvertex_le_two hw hv hs hc).trans (by decide)

/-- Every directed cell side in the actual source paths, including clause endpoints. -/
def allPathPorts (φ : CNF ℕ) : List (Point × Fin 4) :=
  (paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
    [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]

private def portSignal (sites : List Point) (e : Point × Fin 4) : Variable :=
  (e.1, if e.1 ∈ sites then some (Crossover.splitTerminal e.2) else none)

private theorem allPathSignals_eq_map (φ : CNF ℕ) :
    allPathSignals φ = (allPathPorts φ).map (portSignal (crossingSites φ)) := by
  have h : allPathSignals φ =
      ((Cslib.Logic.PL.occurrences φ).map (occurrencePath φ)).flatMap
        (pathSignals (crossingSites φ)) := by
    rw [List.flatMap_map]
    rfl
  rw [h, occurrencePaths_eq_paths]
  unfold pathSignals pathHalfEdges allPathPorts portSignal signal
  simp [List.map_flatMap]

private theorem splitTerminal_injective : Function.Injective Crossover.splitTerminal := by decide

private theorem count_portSignal_terminal (sites : List Point) (p : Point) (i : Fin 4)
    (hp : p ∈ sites) (l : List (Point × Fin 4)) :
    (l.map (portSignal sites)).count (p, some (Crossover.splitTerminal i)) = l.count (p, i) := by
  have he (e : Point × Fin 4) :
      (portSignal sites e == (p, some (Crossover.splitTerminal i))) = (e == (p, i)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rcases e with ⟨q, j⟩
    by_cases hq : q = p
    · subst q
      simp [portSignal, hp, splitTerminal_injective.eq_iff]
    · simp [portSignal, Prod.mk.injEq, hq]
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, List.count_cons, he, ih]

/-- A selected crossover terminal has at most one external literal half in the actual paths. -/
theorem count_allPathSignals_terminal_le_one {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (p : Point) (i : Fin 4) (hp : p ∈ crossingSites φ) :
    (allPathSignals φ).count (p, some (Crossover.splitTerminal i)) ≤ 1 := by
  rw [allPathSignals_eq_map, count_portSignal_terminal _ _ _ hp]
  exact List.nodup_iff_count_le_one.mp (pathPorts_nodup hw hv) _

private theorem tagged_template_count (p q : Point) (v : Crossover.SplitVariable) :
    (Crossover.splitFormula.vars.map (fun w => (q, some w))).count (p, some v) =
      if q = p then Crossover.splitFormula.vars.count v else 0 := by
  by_cases h : q = p
  · subst q
    rw [ite_eq_left rfl]
    exact List.count_map_of_injective _ (fun w => (p, some w))
      (fun _ _ he => Option.some.inj (congrArg Prod.snd he)) _
  · rw [ite_eq_right h, List.count_eq_zero]
    intro hm
    obtain ⟨w, _, he⟩ := List.mem_map.mp hm
    exact h (congrArg Prod.fst he)

private theorem count_tagged_templates (ps : List Point) (p : Point)
    (v : Crossover.SplitVariable) :
    (ps.flatMap fun q => Crossover.splitFormula.vars.map (fun w => (q, some w))).count
      (p, some v) = ps.count p * Crossover.splitFormula.vars.count v := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    rw [List.flatMap_cons, List.count_append, tagged_template_count, List.count_cons, ih]
    by_cases h : q = p <;> simp [h, beq_iff_eq, Nat.add_mul, Nat.add_comm]

/-- Translated templates have the exact literal counts of one template at a selected site. -/
theorem count_crossingSignals_some (φ : CNF ℕ) (p : Point) (v : Crossover.SplitVariable) :
    (crossingSignals φ).count (p, some v) =
      (crossingSites φ).count p * Crossover.splitFormula.vars.count v :=
  count_tagged_templates _ _ _

/-- Ordinary signal names never occur inside a crossover template. -/
theorem count_crossingSignals_none (φ : CNF ℕ) (p : Point) :
    (crossingSignals φ).count (p, none) = 0 := by
  rw [List.count_eq_zero]
  simp [crossingSignals]

/-- The comparison uses the actual emitted formula. It only adds unused clause-cell halves. -/
theorem count_vars_rawFormula_le (φ : CNF ℕ) (v : Variable) :
    (rawFormula φ).vars.count v ≤ (crossingSignals φ).count v + (allPathSignals φ).count v := by
  have he := count_external_blocks_le (φ := φ) (crossingSites φ)
    (Cslib.Logic.PL.occurrences φ) (fun _ => occurrencePath_length_ge_two) v
  have hc : (CNF.vars (((crossingSites φ).flatMap crossingClauses).map Prod.fst)).count v =
      (crossingSignals φ).count v := by
    unfold crossingSignals
    induction crossingSites φ with
    | nil => simp [CNF.vars]
    | cons p ps ih =>
      rw [List.flatMap_cons, List.map_append, count_vars_append, vars_crossingClauses,
        List.flatMap_cons, List.count_append, ih]
  simp only [rawFormula, placedClauses, List.map_append, count_vars_append,
    vars_originalClauses, hc]
  unfold allPathSignals
  omega

/-- The fixed template has at most three literal positions per internal variable. -/
theorem count_vars_splitFormula : ∀ v, Crossover.splitFormula.vars.count v ≤ 3 := by
  decide +kernel

/-- Every terminal has exactly two internal literal positions, leaving one external incidence. -/
theorem count_vars_splitTerminal :
    ∀ i, Crossover.splitFormula.vars.count (Crossover.splitTerminal i) = 2 := by
  decide +kernel

private theorem count_allPathSignals_nonterminal {φ : CNF ℕ} (p : Point)
    (v : Crossover.SplitVariable) (hv : ¬ ∃ i, Crossover.splitTerminal i = v) :
    (allPathSignals φ).count (p, some v) = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨o, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨e, _, he⟩ := List.mem_map.mp hm
  have hs := congrArg Prod.snd he
  by_cases hp : e.1 ∈ crossingSites φ
  · have heq : Crossover.splitTerminal (side e.1 e.2) = v := by
      simpa [signal, hp] using hs
    exact hv ⟨_, heq⟩
  · simp [signal, hp] at hs

private theorem count_allPathSignals_some_of_not_site {φ : CNF ℕ} {p : Point}
    (hp : p ∉ crossingSites φ) (v : Crossover.SplitVariable) :
    (allPathSignals φ).count (p, some v) = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨o, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨e, _, he⟩ := List.mem_map.mp hm
  have hcell : e.1 = p := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  simp [signal, hcell, hp] at hs

/-- The actual structured planarization formula has at most three literal occurrences of
any variable, counting repetitions within clauses. No drawing or degree certificate is assumed. -/
theorem count_vars_rawFormula_le_three {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (rawFormula φ).vars.count v ≤ 3 := by
  rintro ⟨p, v⟩
  have hcompare := count_vars_rawFormula_le φ (p, v)
  cases v with
  | none =>
    rw [count_crossingSignals_none, Nat.zero_add] at hcompare
    exact hcompare.trans (count_allPathSignals_none_le_three hw hv p)
  | some v =>
    have hsite : (crossingSites φ).count p ≤ 1 :=
      List.nodup_iff_count_le_one.mp (crossingSites_nodup φ) p
    rw [count_crossingSignals_some] at hcompare
    by_cases ht : ∃ i, Crossover.splitTerminal i = v
    · obtain ⟨i, rfl⟩ := ht
      rw [count_vars_splitTerminal] at hcompare
      by_cases hp : p ∈ crossingSites φ
      · have hext := count_allPathSignals_terminal_le_one hw hv p i hp
        omega
      · rw [List.count_eq_zero.mpr hp, count_allPathSignals_some_of_not_site hp] at hcompare
        omega
    · rw [count_allPathSignals_nonterminal p v ht, Nat.add_zero] at hcompare
      exact hcompare.trans ((Nat.mul_le_mul hsite (count_vars_splitFormula v)).trans (by simp))

/-- Injective compaction preserves the actual three-literal-occurrence bound. -/
theorem count_vars_formula_le_three {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (formula φ).vars.count v ≤ 3 :=
  CNF.count_vars_compact_le (rawFormula φ) (count_vars_rawFormula_le_three hw hv)

end Cslib.Complexity.SAT.PlanarCompile
