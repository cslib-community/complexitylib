/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PerfectMatching
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Count
import CslibFrontier.Logics.Propositional.CSP.Edge.Size

/-!
# Exact graph edge incidences

Every normalized graph edge occurs once at each of its two distinct declared endpoints.
The resulting positional CSP satisfies the existing edge-instance condition without any
canonicality assumption on the raw graph.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL

/-- Every actual edge position occurs exactly twice in the perfect-matching instance. -/
theorem count_vars_perfectMatchingInstance_eq_two (G : Graph) {x : ℕ}
    (hx : x < G.edgeList.length) : G.perfectMatchingInstance.vars.count x = 2 := by
  classical
  obtain ⟨_, hne, ha, hb⟩ := of_mem_edgeList (getD_edgeList_mem hx)
  let a := (G.edgeList.getD x (0, 0)).1
  let b := (G.edgeList.getD x (0, 0)).2
  have hcount (v : ℕ) :
      (((List.range G.edgeList.length).filter fun i =>
        incident (G.edgeList.getD i (0, 0)) v).count x) =
        (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
    by_cases hv : incident (G.edgeList.getD x (0, 0)) v = true
    · rw [List.count_filter (p := fun i => incident (G.edgeList.getD i (0, 0)) v)
        (a := x) hv, List.count_range]
      simp only [hx, ↓reduceIte]
      simp only [incident, Bool.or_eq_true, decide_eq_true_eq] at hv
      change a ≠ b at hne
      change a = v ∨ b = v at hv
      split_ifs <;> omega
    · have hn : x ∉ (List.range G.edgeList.length).filter
          (fun i => incident (G.edgeList.getD i (0, 0)) v) := by
        simpa only [List.mem_filter, List.mem_range, hx, true_and] using hv
      rw [List.count_eq_zero_of_not_mem hn]
      have hav : v ≠ a := by intro h; apply hv; simp [incident, h, a]
      have hbv : v ≠ b := by intro h; apply hv; simp [incident, h, b]
      simp only [hav, hbv, ↓reduceIte, Nat.add_zero]
  simp only [perfectMatchingInstance, CSP.vars, List.flatMap_map, List.count_flatMap,
    Function.comp_def, hcount]
  rw [← List.sum_toFinset _ G.nodup_distinctVertices]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have ha' : a ∈ G.vertices := ha
  have hb' : b ∈ G.vertices := hb
  simp only [List.mem_toFinset, mem_distinctVertices, ha', hb', ↓reduceIte]

/-- The generated perfect-matching instance is an actual positional edge instance. -/
theorem edgeInstance_perfectMatchingInstance (G : Graph) :
    CSP.EdgeInstance G.perfectMatchingInstance := by
  apply CSP.edgeInstance_of_count_eq_two
  · intro c hc
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    exact (List.nodup_range.filter _)
  · intro x hx
    exact count_vars_perfectMatchingInstance_eq_two G (mem_vars_perfectMatchingInstance.mp hx)

end Cslib.Complexity.Graph
