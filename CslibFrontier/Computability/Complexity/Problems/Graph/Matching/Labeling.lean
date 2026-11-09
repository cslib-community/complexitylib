/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Instance
public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Subgraph
import CslibFrontier.Foundations.Data.List.Range
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Data.Finset.Card

/-!
# Constructive matching and minimum-defect correspondence

The choice constraints use the original normalized graph incidences. A valid local labeling
selects at most one original edge at each vertex; mutually selected edges therefore give an
actual Mathlib matching. Every Mathlib matching supplies a feasible comparison labeling, with
private unmatched ports precisely at its uncovered vertices.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL
open CSP

variable {G : Graph}

/-- A vertex's choice constraint is at its position in the distinct vertex list. -/
theorem getElem_matchingInstance_vertex {v : ℕ} (hv : v ∈ G.1) :
    G.matchingInstance[G.distinctVertices.idxOf v]'(by
      have := List.idxOf_lt_length_iff.mpr (mem_distinctVertices.mpr hv)
      simp only [matchingInstance, List.length_append, List.length_map]
      omega) = (Table.exactlyOne (G.matchingScope v), G.matchingScope v) := by
  simp [matchingInstance, List.idxOf_lt_length_iff.mpr (mem_distinctVertices.mpr hv)]

/-- The unary false pin follows all choice constraints in distinct vertex order. -/
theorem getElem_matchingInstance_pin {v : ℕ} (hv : v ∈ G.1) :
    G.matchingInstance[G.distinctVertices.length + G.distinctVertices.idxOf v]'(by
      have := List.idxOf_lt_length_iff.mpr (mem_distinctVertices.mpr hv)
      simp only [matchingInstance, List.length_append, List.length_map]
      omega) = (Table.pinTable false, [2 * v + 1]) := by
  simp [matchingInstance]

/-- The actual choice incidence of the variable `x` at vertex `v`. -/
@[expose] def choiceOccurrence (G : Graph) (v : ℕ) (hv : v ∈ G.1) (x : ℕ)
    (hx : x ∈ G.matchingScope v) : Occurrence G.matchingInstance :=
  ⟨⟨G.distinctVertices.idxOf v, by
      have := List.idxOf_lt_length_iff.mpr (mem_distinctVertices.mpr hv)
      simp only [matchingInstance, List.length_append, List.length_map]
      omega⟩,
    ⟨(G.matchingScope v).idxOf x, by
      simpa only [getElem_matchingInstance_vertex hv] using List.idxOf_lt_length_iff.mpr hx⟩⟩

/-- Choice incidence reads its supplied original variable. -/
@[simp] theorem var_choiceOccurrence (v : ℕ) (hv : v ∈ G.1) (x : ℕ)
    (hx : x ∈ G.matchingScope v) : (G.choiceOccurrence v hv x hx).var = x := by
  simp [choiceOccurrence, Occurrence.var, getElem_matchingInstance_vertex hv]

/-- The actual false-pin incidence for the private port of `v`. -/
@[expose] def pinOccurrence (G : Graph) (v : ℕ) (hv : v ∈ G.1) : Occurrence G.matchingInstance :=
  ⟨⟨G.distinctVertices.length + G.distinctVertices.idxOf v, by
      have := List.idxOf_lt_length_iff.mpr (mem_distinctVertices.mpr hv)
      simp only [matchingInstance, List.length_append, List.length_map]
      omega⟩,
    ⟨0, by simp only [getElem_matchingInstance_pin hv, List.length_singleton]; omega⟩⟩

@[simp] theorem var_pinOccurrence (v : ℕ) (hv : v ∈ G.1) :
    (G.pinOccurrence v hv).var = 2 * v + 1 := by
  simp [pinOccurrence, Occurrence.var, getElem_matchingInstance_pin hv]

/-- Every valid generated labeling labels each private port's pin false. -/
theorem pinOccurrence_false {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) (v : ℕ) (hv : v ∈ G.1) :
    f (G.pinOccurrence v hv) = false := by
  have hh := hf (G.pinOccurrence v hv).1
  have he : localTuple f (G.pinOccurrence v hv).1 = [f (G.pinOccurrence v hv)] := by
    apply List.ext_getElem
    · simp [localTuple, pinOccurrence, getElem_matchingInstance_pin hv]
    · intro j hj hk
      have hj0 : j = 0 := by
        have : j < 1 := by simpa only [List.length_singleton] using hk
        omega
      subst j
      simp [localTuple, pinOccurrence]
  rw [he] at hh
  have ht : G.matchingInstance[(G.pinOccurrence v hv).1].1 = Table.pinTable false := by
    simp [pinOccurrence, getElem_matchingInstance_pin hv]
  rw [ht, Table.sem_eq_true] at hh
  simpa only [Table.pinTable, List.mem_singleton, List.cons.injEq, and_true] using hh.2

/-- Unary pins prevent every private unmatched port from being mutually selected. -/
theorem not_selected_private {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) (v : ℕ) (hv : v ∈ G.1) :
    2 * v + 1 ∉ selectedVariables f := by
  intro hs
  have hh := (mem_selectedVariables.mp hs).2 (G.pinOccurrence v hv) (var_pinOccurrence v hv)
  rw [pinOccurrence_false hf v hv] at hh
  contradiction

/-- Two true ports in one choice constraint name the same variable. -/
theorem choice_unique {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) (v : ℕ) (hv : v ∈ G.1) (x y : ℕ)
    (hx : x ∈ G.matchingScope v) (hy : y ∈ G.matchingScope v)
    (hfx : f (G.choiceOccurrence v hv x hx) = true)
    (hfy : f (G.choiceOccurrence v hv y hy) = true) : x = y := by
  have hh := hf (G.choiceOccurrence v hv x hx).1
  have ht : G.matchingInstance[(G.choiceOccurrence v hv x hx).1].1 =
      Table.exactlyOne (G.matchingScope v) := by
    simp [choiceOccurrence, getElem_matchingInstance_vertex hv]
  rw [ht, Table.sem_exactlyOne_eq_true] at hh
  let i := (G.choiceOccurrence v hv x hx).1
  have hcard : ((Finset.univ : Finset (Fin G.matchingInstance[i.val].2.length)).filter
      fun j => f ⟨i, j⟩ = true).card = 1 := by
    simpa only [localTuple, List.count_eq_countP, List.countP_ofFn, beq_true,
      Finset.card_eq_sum_ones, Finset.sum_filter] using hh.2
  have hj : (G.choiceOccurrence v hv x hx).2 = (G.choiceOccurrence v hv y hy).2 :=
    Finset.card_le_one.mp hcard.le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfy⟩)
  have ho : G.choiceOccurrence v hv x hx = G.choiceOccurrence v hv y hy :=
    Sigma.ext rfl (heq_of_eq hj)
  simpa only [var_choiceOccurrence] using congrArg Occurrence.var ho

end Cslib.Complexity.Graph

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL CSP

variable {G : Graph}

/-- Original positions with both endpoint labels true. -/
@[expose] def positionsOfLabeling (G : Graph)
    (f : OccurrenceLabeling G.matchingInstance Bool) : Finset ℕ :=
  (Finset.range G.edgeList.length).filter fun i => 2 * i ∈ selectedVariables f

@[simp] theorem mem_positionsOfLabeling (f : OccurrenceLabeling G.matchingInstance Bool) (i : ℕ) :
    i ∈ G.positionsOfLabeling f ↔ i < G.edgeList.length ∧ 2 * i ∈ selectedVariables f := by
  simp [positionsOfLabeling]

/-- Extracting mutually selected original edges gives an actual Mathlib matching. -/
theorem isMatching_positionsOfLabeling {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) :
    (G.matchingOfPositions (G.positionsOfLabeling f)).IsMatching := by
  apply isMatching_matchingOfPositions
  intro v hv i hi j hj hinc hinc'
  obtain ⟨hi, hsi⟩ := mem_positionsOfLabeling f i |>.mp hi
  obtain ⟨hj, hsj⟩ := mem_positionsOfLabeling f j |>.mp hj
  have hxi := (G.mem_matchingScope_even v i).mpr ⟨hi, hinc⟩
  have hxj := (G.mem_matchingScope_even v j).mpr ⟨hj, hinc'⟩
  have he := choice_unique hf v hv (2 * i) (2 * j) hxi hxj
    ((mem_selectedVariables.mp hsi).2 _ (var_choiceOccurrence v hv (2 * i) hxi))
    ((mem_selectedVariables.mp hsj).2 _ (var_choiceOccurrence v hv (2 * j) hxj))
  omega

/-- Mutual selection contains only original even-tagged edges; private pins never contribute. -/
theorem selectedVariables_eq_image {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) :
    selectedVariables f = (G.positionsOfLabeling f).image (2 * ·) := by
  ext x
  constructor
  · intro hx
    rcases (mem_vars_matchingInstance G).mp (mem_selectedVariables.mp hx).1 with
      ⟨i, hi, rfl⟩ | ⟨v, hv, rfl⟩
    · exact Finset.mem_image.mpr ⟨i, (mem_positionsOfLabeling f i).mpr ⟨hi, hx⟩, rfl⟩
    · exact (not_selected_private hf v hv hx).elim
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_positionsOfLabeling f i).mp hi |>.2

/-- Every feasible generated labeling has precisely one true incidence per declared vertex. -/
theorem card_true_matchingInstance {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) :
    ((Finset.univ : Finset (Occurrence G.matchingInstance)).filter fun o => f o = true).card =
      G.distinctVertices.length := by
  have hc (i : Fin G.matchingInstance.length) :
      (localTuple f i).count true = if i.val < G.distinctVertices.length then 1 else 0 := by
    have hh := hf i
    change G.matchingInstance[i.val].1.sem (localTuple f i) = true at hh
    by_cases hi : i.val < G.distinctVertices.length
    · have ht : G.matchingInstance[i.val].1 =
          Table.exactlyOne (G.matchingScope G.distinctVertices[i.val]) := by
        simp [matchingInstance, hi]
      rw [ht] at hh
      exact (Table.sem_exactlyOne_eq_true _ _).mp hh |>.2 |>.trans (ite_eq_left hi).symm
    · have ht : G.matchingInstance[i.val].1 = Table.pinTable false := by
        simp [matchingInstance, Nat.le_of_not_gt hi]
      rw [ht, Table.sem_eq_true] at hh
      have he : localTuple f i = [false] := by
        simpa only [Table.pinTable, List.mem_singleton] using hh.2
      simp [he, hi]
  rw [card_true_eq_sum_count]
  simp only [hc]
  have hn : G.matchingInstance.length = G.distinctVertices.length + G.distinctVertices.length := by
    simp [matchingInstance]
  rw [hn, Fin.sum_univ_add]
  simp

/-- The exact objective identity, including isolates and empty graphs. -/
theorem defects_add_two_mul_positions {f : OccurrenceLabeling G.matchingInstance Bool}
    (hf : ValidLabeling Table.sem f) :
    (defects f).card + 2 * (G.positionsOfLabeling f).card = G.distinctVertices.length := by
  have h := (edgeInstance_matchingInstance G).card_true_eq f
  rw [card_true_matchingInstance hf, selectedVariables_eq_image hf,
    Finset.card_image_of_injective _ (fun i j h => by omega)] at h
  omega

end Cslib.Complexity.Graph
