/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Recovery
import Mathlib.Data.List.GetD

/-!
# Exact finite split input contracts

The connector is an arbitrary nonloop edge, not necessarily a bridge. This module concerns
indexed endpoints and raw validity only. Numerical feasibility under the split requires the
separate contraction theorem and is not asserted here.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

/-- Exact complete/free entry at every declared dense vertex. -/
theorem getD_freePrefix (G : Graph) (k v : ℕ) (hd : G.1 = List.range G.1.length)
    (hv : v < G.1.length) :
    (freePrefix G k).orders.getD v none = if v < k then none else some (fiber G v) := by
  change (G.1.map fun u => if u < k then none else some (fiber G u)).getD v none = _
  rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map]
  have hvertex : G.1[v] = v := by
    have hh : G.1.getD v 0 = v := by rw [hd]; simp [hv]
    rwa [List.getD_eq_getElem _ _ hv] at hh
  rw [hvertex]

/-- Dense closed graphs produce valid complete fixed/free words after any binary free cutoff. -/
theorem valid_freePrefix (G : Graph) (k : ℕ)
    (hd : G.1 = List.range G.1.length)
    (he : ∀ v ∈ G.incidenceVertices, v < G.1.length) : Valid (freePrefix G k) := by
  refine ⟨hd, he, by simp [freePrefix], ?_⟩
  intro v word hw
  have hv : v < G.1.length := by
    by_contra hv
    have hn : (freePrefix G k).orders.length ≤ v := by simp [freePrefix]; omega
    rw [List.getD_eq_default _ _ hn] at hw
    contradiction
  rw [getD_freePrefix G k v hd hv] at hw
  split at hw
  · contradiction
  · have hword := Option.some.inj hw
    subst word
    exact ⟨nodup_fiber G v, fun _ => Iff.rfl⟩

/-- The original CSP incidence entry is valid for arbitrary relation semantics/declared arity,
including all nullary constraint positions and repeated scope occurrences. -/
theorem valid_ofCSP {Rel V : Type} [DecidableEq V] (F : Cslib.Logic.PL.CSP Rel V) :
    Valid (ofCSP F) := by
  apply valid_freePrefix
  · simp [CSP.incidenceGraph_vertices]
  · intro v hv
    have hdecl := CSP.incidenceVertices_declared F v hv
    rw [CSP.incidenceGraph_vertices, List.mem_range] at hdecl
    rwa [CSP.length_vertices_incidenceGraph]

/-- Old listed edge positions and end tags are retained exactly by split redirection. -/
theorem edgeEndpoint_split_old (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (i : ℕ) (hi : i < I.graph.2.length) (side : Bool) :
    (split I v block).graph.edgeEndpoint i side =
      redirectEnd I.graph.1.length block (2 * i + side.toNat) (I.graph.edgeEndpoint i side) := by
  unfold Graph.edgeEndpoint
  have hi' : i < (split I v block).graph.2.length := by simp; omega
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi]
  simp only [split]
  simp only [List.getElem_append, List.length_map, List.length_zipIdx, hi, ↓reduceDIte,
    List.getElem_map, List.getElem_zipIdx]
  cases side <;> simp

/-- The connector's first/false end is the fresh hub and its second/true end is the old vertex. -/
theorem edgeEndpoint_split_connector (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (side : Bool) :
    (split I v block).graph.edgeEndpoint I.graph.2.length side =
      if side then v else I.graph.1.length := by
  unfold Graph.edgeEndpoint
  have hi : I.graph.2.length < (split I v block).graph.2.length := by simp
  rw [List.getD_eq_getElem _ _ hi]
  simp only [split]
  simp only [List.getElem_append, List.length_map, List.length_zipIdx, lt_self_iff_false,
    ↓reduceDIte, Nat.sub_self, List.getElem_cons_zero]

/-- Exact binary endpoint redirection for every original dart index. -/
theorem endpoint_split_old (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (d : ℕ) (hd : d < 2 * I.graph.2.length) :
    (split I v block).graph.incidenceVertices.getD d 0 =
      redirectEnd I.graph.1.length block d (I.graph.incidenceVertices.getD d 0) := by
  let old := (Dart.indexEquiv I.graph).symm ⟨d, hd⟩
  let new : Dart (split I v block).graph :=
    (⟨old.1.val, by simp⟩, old.2)
  have hidx : old.index = d := congrArg Fin.val ((Dart.indexEquiv I.graph).apply_symm_apply ⟨d, hd⟩)
  have hnidx : new.index = d := hidx
  rw [← hnidx, Dart.vertex_index]
  change (split I v block).graph.edgeEndpoint old.1.val old.2 = _
  change (split I v block).graph.edgeEndpoint old.1.val old.2 =
    redirectEnd I.graph.1.length block old.index (I.graph.incidenceVertices.getD old.index 0)
  rw [edgeEndpoint_split_old I v block _ old.1.isLt old.2, Dart.vertex_index]
  rfl

/-- Exact binary endpoint at either end of the appended connector. -/
theorem endpoint_split_connector (I : FixedRotationInput) (v : ℕ) (block : List ℕ)
    (side : Bool) :
    (split I v block).graph.incidenceVertices.getD (2 * I.graph.2.length + side.toNat) 0 =
      if side then v else I.graph.1.length := by
  let d : Dart (split I v block).graph :=
    (⟨I.graph.2.length, by simp⟩, side)
  change (split I v block).graph.incidenceVertices.getD d.index 0 = _
  rw [Dart.vertex_index]
  exact edgeEndpoint_split_connector I v block side

private theorem endpoint_lt {I : FixedRotationInput} (hI : Valid I) {d : ℕ}
    (hd : d < 2 * I.graph.2.length) : I.graph.incidenceVertices.getD d 0 < I.graph.1.length := by
  have hd' : d < I.graph.incidenceVertices.length := by
    simpa only [incidenceVertices_length] using hd
  rw [List.getD_eq_getElem _ _ hd']
  exact hI.2.1 _ (List.getElem_mem hd')

private theorem redirectEnd_eq (hub : ℕ) (block : List ℕ) (d old : ℕ) :
    redirectEnd hub block d old = if d ∈ block then hub else old := by
  simp [redirectEnd, List.any_eq_true]

/-- The hub owns precisely the selected original ends and the connector's false end. -/
theorem mem_fiber_split_hub {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.1.length) {block : List ℕ}
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (d : ℕ) :
    d ∈ fiber (split I v block).graph I.graph.1.length ↔
      d ∈ block ∨ d = 2 * I.graph.2.length := by
  constructor
  · intro hd
    obtain ⟨hd, he⟩ := mem_fiber.mp hd
    by_cases ho : d < 2 * I.graph.2.length
    · rw [endpoint_split_old I v block d ho, redirectEnd_eq] at he
      split at he
      · exact Or.inl (by assumption)
      · have := endpoint_lt hI ho
        omega
    · have hlen := length_split_edges I v block
      have hc : d = 2 * I.graph.2.length ∨ d = 2 * I.graph.2.length + 1 := by omega
      rcases hc with rfl | rfl
      · exact Or.inr rfl
      · have hx := endpoint_split_connector I v block true
        simp only [Bool.toNat_true, ↓reduceIte] at hx
        rw [hx] at he
        omega
  · rintro (hb' | rfl)
    · have hd := (mem_fiber.mp (hb d hb')).1
      apply mem_fiber.mpr
      refine ⟨by simp; omega, ?_⟩
      rw [endpoint_split_old I v block d hd, redirectEnd_eq, ite_eq_left hb']
    · apply mem_fiber.mpr
      refine ⟨by simp, ?_⟩
      simpa only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] using
        endpoint_split_connector I v block false

/-- A different old vertex retains exactly its original dart fiber. -/
theorem mem_fiber_split_other {I : FixedRotationInput} {v u : ℕ}
    (hu : u < I.graph.1.length) (huv : u ≠ v) {block : List ℕ}
    (hb : ∀ d ∈ block, d ∈ fiber I.graph v) (d : ℕ) :
    d ∈ fiber (split I v block).graph u ↔ d ∈ fiber I.graph u := by
  have old (hd : d < 2 * I.graph.2.length) :
      (split I v block).graph.incidenceVertices.getD d 0 = u ↔
        I.graph.incidenceVertices.getD d 0 = u := by
    rw [endpoint_split_old I v block d hd, redirectEnd_eq]
    by_cases hmem : d ∈ block
    · have hvertex := (mem_fiber.mp (hb d hmem)).2
      simp only [hmem, ↓reduceIte, hvertex]
      omega
    · simp only [hmem, ↓reduceIte]
  constructor
  · intro hd
    obtain ⟨hd, he⟩ := mem_fiber.mp hd
    by_cases ho : d < 2 * I.graph.2.length
    · exact mem_fiber.mpr ⟨ho, (old ho).mp he⟩
    · have hlen := length_split_edges I v block
      have hc : d = 2 * I.graph.2.length ∨ d = 2 * I.graph.2.length + 1 := by omega
      rcases hc with rfl | rfl
      · have hx := endpoint_split_connector I v block false
        simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at hx
        rw [hx] at he
        omega
      · have hx := endpoint_split_connector I v block true
        simp only [Bool.toNat_true, ↓reduceIte] at hx
        rw [hx] at he
        exact False.elim (huv he.symm)
  · intro hd
    obtain ⟨hd, he⟩ := mem_fiber.mp hd
    exact mem_fiber.mpr ⟨by simp; omega, (old hd).mpr he⟩

/-- Raw split validity requires no numerical or geometric feasibility theorem. Prescribed old
vertices retain complete orders, and the hub receives exactly the full selected word/connector. -/
theorem valid_split {I : FixedRotationInput} (hI : Valid I) {v : ℕ}
    (hv : v < I.graph.1.length) (hfree : I.orders.getD v none = none) {block : List ℕ}
    (hnd : block.Nodup) (hb : ∀ d ∈ block, d ∈ fiber I.graph v) : Valid (split I v block) := by
  have hwidth : I.orders.length = I.graph.1.length := hI.2.2.1
  refine ⟨by simp [split], ?_, by simp [split, hwidth], ?_⟩
  · intro w hw
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hw
    have hd : i.val < 2 * (I.graph.2.length + 1) := by
      simpa only [incidenceVertices_length, length_split_edges] using i.isLt
    have hread : (split I v block).graph.incidenceVertices.getD i.val 0 = w := by
      rw [List.getD_eq_getElem _ _ i.isLt]
      simpa only [List.get_eq_getElem] using hi
    rw [length_split_vertices]
    by_cases ho : i.val < 2 * I.graph.2.length
    · rw [endpoint_split_old I v block i.val ho, redirectEnd_eq] at hread
      have hlt := endpoint_lt hI ho
      split at hread <;> omega
    · have hc : i.val = 2 * I.graph.2.length ∨ i.val = 2 * I.graph.2.length + 1 := by omega
      rcases hc with hc | hc
      · have hx := endpoint_split_connector I v block false
        simp only [Bool.toNat_false, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at hx
        rw [hc, hx] at hread
        omega
      · have hx := endpoint_split_connector I v block true
        simp only [Bool.toNat_true, ↓reduceIte] at hx
        rw [hc, hx] at hread
        omega
  · intro u word hw
    by_cases hu : u < I.graph.1.length
    · have hul : u < I.orders.length := by omega
      change (I.orders ++ [some (block ++ [2 * I.graph.2.length])]).getD u none = some word at hw
      rw [List.getD_eq_getElem _ _ (by simp; omega)] at hw
      simp only [List.getElem_append, hul, ↓reduceDIte] at hw
      have hread : I.orders.getD u none = some word := by
        rwa [List.getD_eq_getElem _ _ hul]
      have huv : u ≠ v := by rintro rfl; rw [hfree] at hread; contradiction
      obtain ⟨hn, hm⟩ := hI.2.2.2 u word hread
      exact ⟨hn, fun d => (hm d).trans (mem_fiber_split_other hu huv hb d).symm⟩
    · have hult : u < (split I v block).orders.length := by
        by_contra h
        rw [List.getD_eq_default _ _ (by omega)] at hw
        contradiction
      have heq : u = I.graph.1.length := by
        simp only [split, List.length_append, List.length_singleton, hwidth] at hult
        omega
      subst u
      change (I.orders ++ [some (block ++ [2 * I.graph.2.length])]).getD I.graph.1.length none =
        some word at hw
      rw [← hwidth] at hw
      rw [List.getD_eq_getElem _ _ (by simp)] at hw
      simp only [List.getElem_append, lt_self_iff_false, ↓reduceDIte, Nat.sub_self,
        List.getElem_cons_zero, Option.some.injEq] at hw
      subst word
      have hnew : 2 * I.graph.2.length ∉ block := by
        intro hd
        have := (mem_fiber.mp (hb _ hd)).1
        omega
      exact ⟨by simpa using hnd.concat hnew, fun d => by
        rw [List.mem_append, List.mem_singleton, mem_fiber_split_hub hI hv hb]⟩

end Cslib.Complexity.Graph.RotationRecognition
