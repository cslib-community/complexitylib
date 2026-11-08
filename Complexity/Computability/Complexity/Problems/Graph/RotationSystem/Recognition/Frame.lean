/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Finite reference-frame structure and storage

Prescribed full words select distinct original dart ends, hence distinct fresh star leaves.
This module checks the reference-order carriers and bounds their full framed storage. It makes
no assertion about realizing the rank crossing bits by a proper plane drawing.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

/-- The stored complete word, or the empty selection at a free/missing entry. -/
abbrev fixedWord (I : FixedRotationInput) (v : ℕ) := (I.orders.getD v none).getD []

/-- Original selected dart indices, in dense-center and prescribed-word order. -/
@[expose] def selectedDarts (I : FixedRotationInput) : List ℕ :=
  (List.range I.graph.1.length).flatMap (fixedWord I)

/-- Valid selections retain exact fiber membership and have no repeated dart. -/
theorem fixedWord_spec {I : FixedRotationInput} (hI : Valid I) (v : ℕ) :
    (fixedWord I v).Nodup ∧ ∀ d ∈ fixedWord I v, d ∈ fiber I.graph v := by
  unfold fixedWord
  cases h : I.orders.getD v none with
  | none => simp
  | some word =>
    have hs := hI.2.2.2 v word h
    exact ⟨hs.1, fun d hd => (hs.2 d).mp hd⟩

/-- Distinct original centers select disjoint darts, even when listed edges are loops/parallel. -/
theorem selectedDarts_nodup {I : FixedRotationInput} (hI : Valid I) : (selectedDarts I).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun v _ => (fixedWord_spec hI v).1, List.nodup_range.imp ?_⟩
  intro u v huv
  apply List.disjoint_left.mpr
  intro d hu hv
  have hu' := (mem_fiber.mp ((fixedWord_spec hI u).2 d hu)).2
  have hv' := (mem_fiber.mp ((fixedWord_spec hI v).2 d hv)).2
  exact huv (hu'.symm.trans hv')

/-- At most one selected leaf per actual original dart. -/
theorem length_selectedDarts_le {I : FixedRotationInput} (hI : Valid I) :
    (selectedDarts I).length ≤ 2 * I.graph.2.length := by
  have hsub : selectedDarts I ⊆ List.range (2 * I.graph.2.length) := by
    intro d hd
    obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hd
    exact List.mem_range.mpr (mem_fiber.mp ((fixedWord_spec hI v).2 d hv)).1
  simpa only [List.length_range] using (selectedDarts_nodup hI).length_le_of_subset hsub

/-- Centers cost one entry each; selected words cost precisely one fresh leaf per dart. -/
theorem length_centerBlocks (I : FixedRotationInput) :
    (centerBlocks I).length = I.graph.1.length + (selectedDarts I).length := by
  simp [centerBlocks, selectedDarts, fixedWord, List.length_flatMap, List.sum_map_add,
    Nat.add_comm]

/-- A raw reference order has at most the centers and two copies of the actual dart set. -/
theorem length_referenceOrder_le {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).length ≤ I.graph.1.length + 4 * I.graph.2.length := by
  have hs := length_selectedDarts_le hI
  have hf := List.length_filter_le
    (fun v => !(centerBlocks I).any fun w => decide (w = v))
    ((List.range (2 * I.graph.2.length)).map fun d => I.graph.1.length + d)
  simp only [List.length_map, List.length_range] at hf
  simp only [referenceOrder, List.length_append, length_centerBlocks]
  omega

/-- Every reference-order entry is an actual declared subdivision vertex. -/
theorem mem_referenceOrder_lt {I : FixedRotationInput} (hI : Valid I) {x : ℕ}
    (hx : x ∈ referenceOrder I) : x < subdivisionSize I := by
  rcases List.mem_append.mp hx with hc | hr
  · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hc
    have hv' := List.mem_range.mp hv
    rcases List.mem_cons.mp hx with rfl | hx
    · unfold subdivisionSize
      omega
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      have hm := (fixedWord_spec hI v).2 d (List.mem_reverse.mp hd)
      have hwidth := (mem_fiber.mp hm).1
      unfold subdivisionSize
      omega
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hr).1
    have hwidth := List.mem_range.mp hd
    unfold subdivisionSize
    omega

/-- Center blocks have distinct original centers and distinct fresh selected leaves. -/
theorem centerBlocks_nodup {I : FixedRotationInput} (hI : Valid I) : (centerBlocks I).Nodup := by
  let block (v : ℕ) := v :: ((fixedWord I v).reverse.map fun d => I.graph.1.length + d)
  have hword (v : ℕ) : ((fixedWord I v).reverse.map fun d => I.graph.1.length + d).Nodup := by
    have hr : (fixedWord I v).reverse.Nodup := by simpa using (fixedWord_spec hI v).1
    exact hr.map (fun _ _ h => Nat.add_left_cancel h)
  apply List.nodup_flatMap.mpr
  constructor
  · intro v hv
    have hv' := List.mem_range.mp hv
    apply List.nodup_cons.mpr
    refine ⟨?_, hword v⟩
    intro hmem
    obtain ⟨d, _, he⟩ := List.mem_map.mp hmem
    omega
  · apply List.Pairwise.imp_of_mem (p := List.nodup_range)
    intro u v hu hv huv
    have hu' := List.mem_range.mp hu
    have hv' := List.mem_range.mp hv
    apply List.disjoint_left.mpr
    intro x hx hy
    change x ∈ block u at hx
    change x ∈ block v at hy
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases List.mem_cons.mp hy with he | hy
      · exact huv he
      · obtain ⟨d, _, he⟩ := List.mem_map.mp hy
        omega
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_cons.mp hy with he | hy
      · omega
      · obtain ⟨e, he, hde⟩ := List.mem_map.mp hy
        have heq : e = d := Nat.add_left_cancel hde
        subst e
        have hud := (mem_fiber.mp ((fixedWord_spec hI u).2 d (List.mem_reverse.mp hd))).2
        have hvd := (mem_fiber.mp ((fixedWord_spec hI v).2 d (List.mem_reverse.mp he))).2
        exact huv (hud.symm.trans hvd)

/-- The reference order contains every subdivision vertex exactly once, including isolates. -/
theorem referenceOrder_enumerates {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).Nodup ∧
      ∀ x, x ∈ referenceOrder I ↔ x ∈ List.range (subdivisionSize I) := by
  constructor
  · apply List.nodup_append'.mpr
    refine ⟨centerBlocks_nodup hI, ?_, ?_⟩
    · exact (List.nodup_range.map (fun _ _ h => Nat.add_left_cancel h)).filter _
    · apply List.disjoint_left.mpr
      intro x hx hy
      have hnot := (List.mem_filter.mp hy).2
      have hany : (centerBlocks I).any (fun w => decide (w = x)) = true := by
        exact List.any_eq_true.mpr ⟨x, hx, by simp⟩
      rw [hany] at hnot
      contradiction
  · intro x
    constructor
    · exact fun hx => List.mem_range.mpr (mem_referenceOrder_lt hI hx)
    · intro hx
      have hx' := List.mem_range.mp hx
      by_cases hb : x ∈ centerBlocks I
      · exact List.mem_append_left _ hb
      · apply List.mem_append_right
        apply List.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · have hn : I.graph.1.length ≤ x := by
            by_contra h
            have hm : x ∈ centerBlocks I := List.mem_flatMap.mpr
              ⟨x, List.mem_range.mpr (by omega), List.mem_cons_self ..⟩
            exact hb hm
          apply List.mem_map.mpr
          refine ⟨x - I.graph.1.length, List.mem_range.mpr ?_, ?_⟩
          · unfold subdivisionSize at hx'
            omega
          · omega
        · simp only [Bool.not_eq_true', List.any_eq_false]
          intro w hw he
          have he' := of_decide_eq_true he
          cases he'
          exact hb hw

/-- The complete rank table has precisely the declared subdivided vertex count. -/
theorem length_referenceOrder {I : FixedRotationInput} (hI : Valid I) :
    (referenceOrder I).length = subdivisionSize I := by
  obtain ⟨hn, hm⟩ := referenceOrder_enumerates hI
  have hp := (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr hm
  simpa using hp.length_eq

/-- Spanning frozen subgraph on every subdivision vertex, retaining precisely flagged segments. -/
@[expose] def frozenGraph (I : FixedRotationInput) : Graph :=
  (List.range (subdivisionSize I), ((subdivide I).filter fun e => e.2).map fun e => e.1)

/-- Every frozen segment joins an original center to its own occurrence-indexed fresh leaf.
The original endpoint reader fixes the center uniquely from that leaf. Middle edges are absent. -/
theorem frozen_edge_shape {I : FixedRotationInput} (hI : Valid I) {e : ℕ × ℕ}
    (he : e ∈ (frozenGraph I).2) :
    ∃ center leaf, center < I.graph.1.length ∧ I.graph.1.length ≤ leaf ∧
      leaf < subdivisionSize I ∧ (e = (center, leaf) ∨ e = (leaf, center)) ∧
      (I.orders.getD center none).isSome = true ∧
      I.graph.incidenceVertices.getD (leaf - I.graph.1.length) 0 = center := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
  obtain ⟨hs, hf⟩ := List.mem_filter.mp hs
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
  have hem : entry.1 ∈ I.graph.2 := hv ▸ List.getElem_mem hi
  have hu : entry.1.1 < I.graph.1.length :=
    hI.2.1 _ (List.mem_flatMap.mpr ⟨entry.1, hem, by simp⟩)
  have hw : entry.1.2 < I.graph.1.length :=
    hI.2.1 _ (List.mem_flatMap.mpr ⟨entry.1, hem, by simp⟩)
  change s ∈ [((entry.1.1, I.graph.1.length + 2 * entry.2), _),
    ((I.graph.1.length + 2 * entry.2, I.graph.1.length + 2 * entry.2 + 1), false),
    ((I.graph.1.length + 2 * entry.2 + 1, entry.1.2), _)] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · refine ⟨entry.1.1, I.graph.1.length + 2 * entry.2, hu, by omega, ?_, Or.inl rfl, hf, ?_⟩
    · unfold subdivisionSize
      omega
    · have hr := getD_incidenceVertices_even I.graph entry.2
      rw [List.getD_eq_getElem _ _ hi, hv] at hr
      simpa using hr
  · contradiction
  · refine ⟨entry.1.2, I.graph.1.length + 2 * entry.2 + 1, hw, by omega, ?_, Or.inr rfl, hf, ?_⟩
    · unfold subdivisionSize
      omega
    · have hr := getD_incidenceVertices_odd I.graph entry.2
      rw [List.getD_eq_getElem _ _ hi, hv] at hr
      have hindex : I.graph.1.length + 2 * entry.2 + 1 - I.graph.1.length = 2 * entry.2 + 1 := by
        omega
      simpa only [hindex] using hr

/-- Every selected subdivision leaf belongs to exactly one center. Together with
`frozen_edge_shape`, this describes disjoint spanning stars and isolated points. -/
theorem frozen_leaf_unique {I : FixedRotationInput} (hI : Valid I) {leaf u v : ℕ}
    (hl : I.graph.1.length ≤ leaf)
    (hu : (u, leaf) ∈ (frozenGraph I).2 ∨ (leaf, u) ∈ (frozenGraph I).2)
    (hv : (v, leaf) ∈ (frozenGraph I).2 ∨ (leaf, v) ∈ (frozenGraph I).2) : u = v := by
  have center (x : ℕ) (hx : (x, leaf) ∈ (frozenGraph I).2 ∨ (leaf, x) ∈ (frozenGraph I).2) :
      I.graph.incidenceVertices.getD (leaf - I.graph.1.length) 0 = x := by
    rcases hx with hx | hx
    · obtain ⟨c, l, hc, _, _, he, _, hread⟩ := frozen_edge_shape hI hx
      rcases he with he | he
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact hread
      · have : leaf = c := (Prod.mk.inj he).2
        omega
    · obtain ⟨c, l, hc, _, _, he, _, hread⟩ := frozen_edge_shape hI hx
      rcases he with he | he
      · have : leaf = c := (Prod.mk.inj he).1
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact hread
  exact (center u hu).symm.trans (center v hv)

/-- Full framed algebraic-frame storage is quadratically bounded in uniform original graph
sizes. Unary stride, binary endpoint pairs, frozen flags, and binary reference entries count. -/
theorem length_encFrame_le {I : FixedRotationInput} (hI : Valid I) {K : ℕ} (hK : 1 ≤ K)
    (hn : I.graph.1.length ≤ K) (hm : I.graph.2.length ≤ K) :
    (encFrame (frame I)).length ≤ 400 * K ^ 2 := by
  have hsize : subdivisionSize I ≤ 3 * K := by unfold subdivisionSize; omega
  have hcount : (frame I).vertexCount ≤ 3 * K := hsize
  have hF := boundedEndpoints_frame hI
  have hsegment : ∀ s ∈ (frame I).segments, (encSegment s).length ≤ 18 * K + 4 := by
    intro s hs
    obtain ⟨ha, hb⟩ := hF s hs
    have hbit (x : ℕ) (hx : x < (frame I).vertexCount) : (encNat x).length ≤ 3 * K := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_self _).trans (hx.le.trans hsize)
    have ha' := hbit _ ha
    have hb' := hbit _ hb
    simp only [encSegment, length_encPair, encBool_apply, List.length_singleton]
    omega
  have hsegments := length_encList_le encSegment (frame I).segments hsegment
  have hseglen : (frame I).segments.length ≤ 3 * K := by
    simpa only [frame, length_subdivide] using Nat.mul_le_mul_left 3 hm
  have hsegments' : (encList encSegment (frame I).segments).length ≤ 3 * K * (36 * K + 9) :=
    hsegments.trans (by nlinarith)
  have horder : ∀ x ∈ (frame I).order, (encNat x).length ≤ 3 * K := by
    intro x hx
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans ((mem_referenceOrder_lt hI hx).le.trans hsize)
  have href := length_encList_le encNat (frame I).order horder
  have hrefLen : (frame I).order.length ≤ 5 * K := (length_referenceOrder_le hI).trans (by omega)
  have href' : (encList encNat (frame I).order).length ≤ 5 * K * (6 * K + 1) :=
    href.trans (by nlinarith)
  simp only [encFrame_apply, encFrameFields, length_encPair, encUnary_apply, List.length_replicate]
  nlinarith [Nat.mul_self_le_mul_self hK]

end Cslib.Complexity.Graph.RotationRecognition
