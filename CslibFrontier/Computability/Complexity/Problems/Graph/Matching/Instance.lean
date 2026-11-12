/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Incidence
public import CslibFrontier.Logics.Propositional.CSP.Table.DeltaMatroid
public import CslibFrontier.Logics.Propositional.CSP.Table.CyclicDifference
public import CslibFrontier.Logics.Propositional.CSP.Edge.Selected

/-!
# Matching as minimum-defect edge CSP

Each distinct declared vertex chooses exactly one incident edge or its private unmatched port.
Original edges use the even names `2 * i`, where `i` is their normalized edge-list position;
the private port of a vertex named `v` uses `2 * v + 1`. A second unary constraint pins each
private port false. Every scope is nonempty, including isolated vertices. Names are retained
in binary; no interval below a raw vertex name is enumerated.

Mutually true original edges form a matching. Counting true endpoints gives
`2 * matched edges + defects = distinct vertices`, so minimizing defects maximizes matching
cardinality. The solver is the even-delta-matroid algorithm of [KazdaKolmogorovRolinek2018].
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL

/-- Nonempty choice scope: one private unmatched port and the incident normalized edges. -/
@[expose] def matchingScope (G : Graph) (v : ℕ) : List ℕ :=
  (2 * v + 1) :: (((List.range G.edgeList.length).filter fun i =>
    incident (G.edgeList.getD i (0, 0)) v).map fun i => 2 * i)

/-- An exactly-one choice at every vertex, with every private unmatched port pinned false.
This instance always has a valid local labeling; consistency is not required by optimization. -/
@[expose] def matchingInstance (G : Graph) : CSP CSP.Table ℕ :=
  (G.distinctVertices.map fun v => (CSP.Table.exactlyOne (G.matchingScope v), G.matchingScope v)) ++
    (G.distinctVertices.map fun v => (CSP.Table.pinTable false, [2 * v + 1]))

/-- An original edge belongs to a choice scope precisely at its two original endpoints. -/
theorem mem_matchingScope_even (G : Graph) (v i : ℕ) :
    2 * i ∈ G.matchingScope v ↔
      i < G.edgeList.length ∧ incident (G.edgeList.getD i (0, 0)) v = true := by
  simp only [matchingScope, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro (h | ⟨j, hj, he⟩)
    · omega
    · have : j = i := by omega
      subst j
      exact hj
  · exact fun h => Or.inr ⟨i, h, rfl⟩

/-- An unmatched port appears in exactly its own vertex's choice scope. -/
theorem mem_matchingScope_odd (G : Graph) (v w : ℕ) :
    2 * w + 1 ∈ G.matchingScope v ↔ w = v := by
  simp only [matchingScope, List.mem_cons, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro (h | ⟨j, _, he⟩) <;> omega
  · intro h
    subst w
    exact Or.inl rfl

/-- All generated choice scopes are duplicate-free, for arbitrary raw graph data. -/
theorem nodup_matchingScope (G : Graph) (v : ℕ) : (G.matchingScope v).Nodup := by
  rw [matchingScope, List.nodup_cons]
  constructor
  · simp only [List.mem_map, List.mem_filter, List.mem_range, not_exists, not_and]
    intro i _ h
    omega
  · exact (List.nodup_range.filter _).map (fun i j h => by omega)

end Cslib.Complexity.Graph

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL

/-- Original edge positions have the same occurrence count under even tagging. -/
theorem count_vars_matchingInstance_even (G : Graph) (i : ℕ) :
    G.matchingInstance.vars.count (2 * i) = G.perfectMatchingInstance.vars.count i := by
  have hc (v : ℕ) : (G.matchingScope v).count (2 * i) =
      (((List.range G.edgeList.length).filter fun j =>
        incident (G.edgeList.getD j (0, 0)) v).count i) := by
    rw [matchingScope, List.count_cons]
    simp only [beq_iff_eq, show 2 * v + 1 ≠ 2 * i by omega, ↓reduceIte, Nat.add_zero]
    exact List.count_map_of_injective _ _ (fun a b h => by omega) _
  simp only [matchingInstance, perfectMatchingInstance, CSP.vars, List.flatMap_append,
    List.flatMap_map, List.count_append, List.count_flatMap, Function.comp_def, hc]
  have hz : (G.distinctVertices.map fun v => ([2 * v + 1] : List ℕ).count (2 * i)).sum = 0 := by
    apply List.sum_eq_zero
    intro n hn
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hn
    simp only [List.count_singleton, beq_iff_eq,
      show 2 * v + 1 ≠ 2 * i by omega, ↓reduceIte]
  rw [hz, Nat.add_zero]

/-- Each declared vertex's private port occurs exactly twice. -/
theorem count_vars_matchingInstance_odd (G : Graph) (w : ℕ) :
    G.matchingInstance.vars.count (2 * w + 1) = if w ∈ G.vertices then 2 else 0 := by
  have hc (v : ℕ) : (G.matchingScope v).count (2 * w + 1) = if v = w then 1 else 0 := by
    have he : (((List.range G.edgeList.length).filter fun i =>
        incident (G.edgeList.getD i (0, 0)) v).map fun i => 2 * i).count (2 * w + 1) = 0 := by
      apply List.count_eq_zero_of_not_mem
      simp only [List.mem_map, List.mem_filter, List.mem_range, not_exists, not_and]
      intro i _ h
      omega
    simp only [matchingScope, List.count_cons, beq_iff_eq, he, Nat.zero_add]
    split_ifs <;> omega
  have hp (v : ℕ) : ([2 * v + 1] : List ℕ).count (2 * w + 1) = if v = w then 1 else 0 := by
    simp only [List.count_singleton, beq_iff_eq]
    split_ifs <;> omega
  simp only [matchingInstance, CSP.vars, List.flatMap_append, List.flatMap_map,
    List.count_append, List.count_flatMap, Function.comp_def, hc, hp]
  rw [← List.sum_toFinset _ G.nodup_distinctVertices, Finset.sum_ite_eq']
  simp only [List.mem_toFinset, mem_distinctVertices]
  split_ifs <;> rfl

/-- Every generated variable is an original edge position or a declared private port. -/
theorem mem_vars_matchingInstance (G : Graph) {x : ℕ} :
    x ∈ G.matchingInstance.vars ↔
      (∃ i < G.edgeList.length, x = 2 * i) ∨ ∃ v ∈ G.vertices, x = 2 * v + 1 := by
  simp only [matchingInstance, CSP.vars, List.flatMap_append, List.flatMap_map,
    List.mem_append, List.mem_flatMap, mem_distinctVertices, matchingScope, List.mem_cons,
    List.mem_map, List.mem_filter, List.mem_range, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨v, hv, h | ⟨i, ⟨hi, _⟩, he⟩⟩ | ⟨v, hv, h⟩)
    · exact Or.inr ⟨v, hv, h⟩
    · exact Or.inl ⟨i, hi, he.symm⟩
    · exact Or.inr ⟨v, hv, h⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inl ⟨_, (of_mem_edgeList (getD_edgeList_mem hi)).2.2.1,
        Or.inr ⟨i, ⟨hi, by simp [incident]⟩, rfl⟩⟩
    · exact Or.inr ⟨v, hv, rfl⟩

/-- The optimizer's two-occurrence guard follows internally on every raw graph. -/
theorem edgeInstance_matchingInstance (G : Graph) : CSP.EdgeInstance G.matchingInstance := by
  apply CSP.edgeInstance_of_count_eq_two
  · intro c hc
    simp only [matchingInstance, List.mem_append, List.mem_map, mem_distinctVertices] at hc
    rcases hc with ⟨v, _, rfl⟩ | ⟨v, _, rfl⟩
    · exact nodup_matchingScope G v
    · exact List.nodup_singleton _
  · intro x hx
    rcases (mem_vars_matchingInstance G).mp hx with ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
    · rw [count_vars_matchingInstance_even]
      exact count_vars_perfectMatchingInstance_eq_two G hi
    · simp only [count_vars_matchingInstance_odd, hv, ↓reduceIte]

/-- Each generated relation is a nonempty even delta-matroid on its actual scope positions. -/
theorem evenConstraints_matchingInstance (G : Graph) :
    CSP.EdgeInstance.EvenConstraints CSP.Table.sem G.matchingInstance := by
  have hgood (c : Constraint CSP.Table ℕ) (hc : c ∈ G.matchingInstance) :
      BitString.IsEvenDeltaMatroid {t : Fin c.2.length → Bool |
        c.1.sem (List.ofFn t) = true} := by
    simp only [matchingInstance, List.mem_append, List.mem_map, mem_distinctVertices] at hc
    rcases hc with ⟨v, _, rfl⟩ | ⟨v, _, rfl⟩
    · exact CSP.Table.isEvenDeltaMatroid_exactlyOne _ (List.cons_ne_nil _ _)
    · exact CSP.Table.isEvenDeltaMatroid_pinTable false
  exact fun i => hgood _ (List.getElem_mem i.isLt)

end Cslib.Complexity.Graph
