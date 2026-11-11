/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Subdivision.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Subdivisions of metric graphs and piecewise-affine distance

This module constructs arbitrary finite vertex subdivisions of a `WeightedGraph`, establishes the
isometric equivalence `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`, and proves that the
distance from any fixed point `p : MetricGraph W` is affine along every subdivided edge once the
subdivision includes the distance breakpoints (at most three per edge). The STOC 2027
submission 1056 reference (Definition 5.1 / Lemma 5.2) comes from Issue #4324 context and was
not verified against the primary manuscript.

## Main definitions

* `SimpleGraph.MetricGraph.subdivide`: subdivide a weighted graph `W` at a finite set of points
  `B : Finset (MetricGraph W)` containing all original vertices.
* `SimpleGraph.MetricGraph.subdivideEquiv`: the isometric equivalence
  `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`.
* `SimpleGraph.MetricGraph.pointBreakpoints`: a finite set containing all vertices and at most
  three interior breakpoints per edge where `t ↦ dist p (edgePoint d t)` changes slope.

## Main results

* `SimpleGraph.MetricGraph.vertexDist_subdivide`: vertex distances in `subdivide W B hV` agree
  with geodesic distances in `MetricGraph W`.
* `SimpleGraph.MetricGraph.subdivideEquiv_vertex`,
  `SimpleGraph.MetricGraph.subdivideEquiv_edgePoint`: explicit evaluation of `subdivideEquiv`.
* `SimpleGraph.MetricGraph.dist_subdivide_edgePoint_affine`: for any subdivision containing
  `pointBreakpoints W p`, the distance from `p` is affine along every subdivided edge.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Subdivision graph and weights -/

/-- Two distinct points `x, y ∈ B` are adjacent in the `B`-subdivision if they lie at `s < t`
along some dart `d` of `W` with no point of `B` strictly between them on `d`. -/
@[expose] def SubAdj (W : WeightedGraph V) (B : Finset (MetricGraph W))
    (x y : { z : MetricGraph W // z ∈ B }) : Prop :=
  x ≠ y ∧ ∃ (d : W.graph.Dart) (s t : unitInterval),
    (s : ℝ) < t ∧ edgePoint d s = x.1 ∧ edgePoint d t = y.1 ∧
      ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B

theorem subAdj_symm {B : Finset (MetricGraph W)}
    {x y : { z : MetricGraph W // z ∈ B }} (h : SubAdj W B x y) :
    SubAdj W B y x := by
  rcases h with ⟨hne, d, s, t, hst, hs, ht, hmid⟩
  refine ⟨hne.symm, d.symm, unitInterval.symm t, unitInterval.symm s, ?_, ?_, ?_, ?_⟩
  · change 1 - (t : ℝ) < 1 - s
    linarith
  · simpa only [edgePoint_symm] using ht
  · simpa only [edgePoint_symm] using hs
  · intro r hr1 hr2 hrB
    change 1 - (t : ℝ) < r at hr1
    change (r : ℝ) < 1 - s at hr2
    have hr1' : (s : ℝ) < (unitInterval.symm r : ℝ) := by change (s : ℝ) < 1 - r; linarith
    have hr2' : (unitInterval.symm r : ℝ) < t := by change 1 - (r : ℝ) < t; linarith
    refine hmid (unitInterval.symm r) hr1' hr2' ?_
    simpa only [edgePoint_symm'] using hrB

/-- Two strictly ordered endpoint witnesses along darts of `W` that represent the same ordered
pair of points must agree on the dart and both parameters. -/
theorem subAdj_witness_eq {d₁ d₂ : W.graph.Dart} {s₁ t₁ s₂ t₂ : unitInterval}
    (hs₁ : (s₁ : ℝ) < t₁) (hs₂ : (s₂ : ℝ) < t₂)
    (heq₁ : edgePoint d₁ s₁ = (edgePoint d₂ s₂ : MetricGraph W))
    (heq₂ : edgePoint d₁ t₁ = (edgePoint d₂ t₂ : MetricGraph W)) :
    d₁ = d₂ ∧ s₁ = s₂ ∧ t₁ = t₂ := by
  have ht10 : 0 < (t₁ : ℝ) := lt_of_le_of_lt s₁.2.1 hs₁
  have hs11 : (s₁ : ℝ) < 1 := lt_of_lt_of_le hs₁ t₁.2.2
  have he : d₁.edge = d₂.edge := by
    by_cases ht1 : (t₁ : ℝ) < 1
    · rcases edgePoint_eq_edgePoint_iff.mp heq₂ with
        ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, _, _, _, ⟨heq, _⟩ | ⟨hsym, _⟩⟩
      · exact absurd (congrArg Subtype.val h1) ht10.ne'
      · exact absurd (congrArg Subtype.val h2) ht1.ne
      · rw [heq]
      · exact hsym ▸ d₂.edge_symm
    · have ht1eq : t₁ = 1 := Subtype.ext (le_antisymm t₁.2.2 (not_lt.mp ht1))
      by_cases hs10 : 0 < (s₁ : ℝ)
      · rcases edgePoint_eq_edgePoint_iff.mp heq₁ with
          ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, _, _, _, ⟨heq, _⟩ | ⟨hsym, _⟩⟩
        · exact absurd (congrArg Subtype.val h1) hs10.ne'
        · exact absurd (congrArg Subtype.val h2) hs11.ne
        · rw [heq]
        · exact hsym ▸ d₂.edge_symm
      · have hs1eq : s₁ = 0 := Subtype.ext (le_antisymm (not_lt.mp hs10) s₁.2.1)
        subst hs1eq ht1eq
        have hfst : (vertex d₁.fst : MetricGraph W) = edgePoint d₂ s₂ := by
          simpa only [edgePoint_zero] using heq₁
        have hsnd : (vertex d₁.snd : MetricGraph W) = edgePoint d₂ t₂ := by
          simpa only [edgePoint_one] using heq₂
        rcases edgePoint_eq_vertex_iff.mp hfst.symm with ⟨rfl, hf1⟩ | ⟨rfl, hf2⟩
        · rcases edgePoint_eq_vertex_iff.mp hsnd.symm with ⟨h0, _⟩ | ⟨rfl, hs2⟩
          · rw [h0, show ((0 : unitInterval) : ℝ) = 0 from rfl] at hs₂
            exact absurd hs₂ (lt_irrefl _)
          · rw [← Dart.sym2Mk_fst_snd d₁, ← Dart.sym2Mk_fst_snd d₂, hf1, hs2]
        · rcases edgePoint_eq_vertex_iff.mp hsnd.symm with ⟨h0, _⟩ | ⟨h1, _⟩
          · rw [h0, show ((0 : unitInterval) : ℝ) = 0 from rfl,
              show ((1 : unitInterval) : ℝ) = 1 from rfl] at hs₂
            linarith
          · rw [h1, show ((1 : unitInterval) : ℝ) = 1 from rfl] at hs₂
            exact absurd hs₂ (lt_irrefl _)
  rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | rfl
  · exact ⟨rfl, edgePoint_injective d₁ heq₁, edgePoint_injective d₁ heq₂⟩
  · rw [← edgePoint_symm d₂ s₂] at heq₁
    rw [← edgePoint_symm d₂ t₂] at heq₂
    have hs' := edgePoint_injective d₂.symm heq₁
    have ht' := edgePoint_injective d₂.symm heq₂
    have hlt : 1 - (s₂ : ℝ) < 1 - (t₂ : ℝ) := by
      simpa only [← unitInterval.coe_symm_eq, ← hs', ← ht'] using hs₁
    linarith

private theorem subAdj_witness_sym2_len {x y : MetricGraph W} (_hne : x ≠ y)
    {d₁ d₂ : W.graph.Dart} {s₁ t₁ s₂ t₂ : unitInterval}
    (hs₁ : (s₁ : ℝ) < t₁) (hs₂ : (s₂ : ℝ) < t₂)
    (heq₁ : s(edgePoint d₁ s₁, edgePoint d₁ t₁) = s(x, y))
    (heq₂ : s(edgePoint d₂ s₂, edgePoint d₂ t₂) = s(x, y)) :
    ((t₁ : ℝ) - s₁) * W.weight d₁.edge = ((t₂ : ℝ) - s₂) * W.weight d₂.edge := by
  have heq : s(edgePoint d₁ s₁, edgePoint d₁ t₁) = s(edgePoint d₂ s₂, edgePoint d₂ t₂) :=
    heq₁.trans heq₂.symm
  rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨rfl, rfl, rfl⟩ := subAdj_witness_eq hs₁ hs₂ ha hb
    rfl
  · rw [← edgePoint_symm d₂ s₂] at hb
    rw [← edgePoint_symm d₂ t₂] at ha
    have hs₂' : (unitInterval.symm t₂ : ℝ) < unitInterval.symm s₂ := by
      change 1 - (t₂ : ℝ) < 1 - s₂; linarith
    obtain ⟨rfl, rfl, rfl⟩ := subAdj_witness_eq hs₁ hs₂' ha hb
    simp only [unitInterval.coe_symm_eq, Dart.edge_symm]
    ring

open Classical in
/-- Weight of a subdivided edge in `subdivide`: `(t - s) * W.weight d.edge`. -/
noncomputable def subWeight (W : WeightedGraph V) (B : Finset (MetricGraph W))
    (e : Sym2 { z : MetricGraph W // z ∈ B }) : ℝ :=
  if h : ∃ (d : W.graph.Dart) (s t : unitInterval),
      (s : ℝ) < t ∧ s(edgePoint d s, edgePoint d t) = Sym2.map Subtype.val e
  then
    let d := Classical.choose h
    let s := Classical.choose (Classical.choose_spec h)
    let t := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
    ((t : ℝ) - s) * W.weight d.edge
  else 1

theorem subWeight_eq_of_witness {B : Finset (MetricGraph W)}
    {x y : { z : MetricGraph W // z ∈ B }} (hne : x.1 ≠ y.1)
    {d : W.graph.Dart} {s t : unitInterval} (hst : (s : ℝ) < t)
    (hs : edgePoint d s = x.1) (ht : edgePoint d t = y.1) :
    subWeight W B s(x, y) = ((t : ℝ) - s) * W.weight d.edge := by
  classical
  have hex : ∃ (d₀ : W.graph.Dart) (s₀ t₀ : unitInterval),
      (s₀ : ℝ) < t₀ ∧ s(edgePoint d₀ s₀, edgePoint d₀ t₀) = Sym2.map Subtype.val s(x, y) :=
    ⟨d, s, t, hst, by change s(edgePoint d s, edgePoint d t) = s(x.1, y.1); rw [hs, ht]⟩
  simp only [subWeight, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex))
  have hsym2 : s(edgePoint (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)),
      edgePoint (Classical.choose hex)
        (Classical.choose (Classical.choose_spec (Classical.choose_spec hex)))) =
      s(x.1, y.1) := by
    change _ = Sym2.map Subtype.val s(x, y)
    exact hspec.2
  exact subAdj_witness_sym2_len hne hspec.1 hst hsym2 (by rw [hs, ht])

private def subdivideGraph (W : WeightedGraph V) (B : Finset (MetricGraph W)) :
    SimpleGraph { z : MetricGraph W // z ∈ B } where
  Adj := SubAdj W B
  symm := ⟨fun _ _ h => subAdj_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Along dart `d`, there is a walk in the `B`-subdivision between any two points `s ≤ t`
of `B` on `d`, of total length `(t - s) * W.weight d.edge`. -/
private theorem exists_walk_along_dart {B : Finset (MetricGraph W)}
    (d : W.graph.Dart) :
    ∀ (n : ℕ) (s t : unitInterval),
      (hs : edgePoint d s ∈ B) → (ht : edgePoint d t ∈ B) → (hle : (s : ℝ) ≤ t) →
      ∀ [DecidablePred (fun p => ∃ r : unitInterval,
        (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p)],
      (B.filter (fun p => ∃ r : unitInterval,
        (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p)).card ≤ n →
      ∃ p : (subdivideGraph W B).Walk ⟨edgePoint d s, hs⟩ ⟨edgePoint d t, ht⟩,
        walkLength (subWeight W B) p = ((t : ℝ) - s) * W.weight d.edge := by
  classical
  intro n
  induction n with
  | zero =>
    intro s t hs ht hle _ hcard
    have hlt : ¬((s : ℝ) < t) := by
      intro hst
      have hmem : edgePoint d t ∈ B.filter (fun p =>
          ∃ r : unitInterval, (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p) :=
        Finset.mem_filter.mpr ⟨ht, t, hst, le_rfl, rfl⟩
      have hpos : 0 < (Finset.filter _ B).card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    have heq : s = t := Subtype.ext (le_antisymm hle (not_lt.mp hlt))
    subst heq
    exact ⟨Walk.nil, by simp⟩
  | succ n ih =>
    intro s t hs ht hle _ hcard
    by_cases hst : (s : ℝ) < t
    · let F := B.filter (fun p =>
        ∃ r : unitInterval, (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p)
      let S : Finset ℝ := F.image (fun p =>
        if h : ∃ r : unitInterval, (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p
        then ((Classical.choose h : unitInterval) : ℝ) else 2)
      have htS : (t : ℝ) ∈ S := by
        refine Finset.mem_image.mpr ⟨edgePoint d t,
          Finset.mem_filter.mpr ⟨ht, t, hst, le_rfl, rfl⟩, ?_⟩
        have hex :
            ∃ r : unitInterval, (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = edgePoint d t :=
          ⟨t, hst, le_rfl, rfl⟩
        simp only [hex, ↓reduceDIte]
        have hr := Classical.choose_spec hex
        exact congrArg Subtype.val (edgePoint_injective d hr.2.2)
      let rminReal := S.min' ⟨t, htS⟩
      have hmin_mem : rminReal ∈ S := S.min'_mem ⟨t, htS⟩
      dsimp only [S] at hmin_mem
      obtain ⟨pmin, hpminF, hpminEq⟩ := Finset.mem_image.mp hmin_mem
      obtain ⟨hpminB, rmin0, hr1, hr2, hpminE⟩ := Finset.mem_filter.mp hpminF
      have hexm : ∃ r : unitInterval, (s : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = pmin :=
        ⟨rmin0, hr1, hr2, hpminE⟩
      simp only [hexm, ↓reduceDIte] at hpminEq
      let rmin := Classical.choose hexm
      have hrminSpec := Classical.choose_spec hexm
      have hrmin_eq : (rmin : ℝ) = rminReal := hpminEq
      have hrmin_mem : edgePoint d rmin ∈ B := hrminSpec.2.2 ▸ hpminB
      have hsr : (s : ℝ) < rmin := hrminSpec.1
      have hrt : (rmin : ℝ) ≤ t := hrminSpec.2.1
      have hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < rmin → edgePoint d r ∉ B := by
        intro r hsr' hrr' hrB
        have hrS : (r : ℝ) ∈ S := by
          refine Finset.mem_image.mpr ⟨edgePoint d r,
            Finset.mem_filter.mpr ⟨hrB, r, hsr', hrr'.le.trans hrt, rfl⟩, ?_⟩
          have hex : ∃ q : unitInterval,
              (s : ℝ) < q ∧ (q : ℝ) ≤ t ∧ edgePoint d q = edgePoint d r :=
            ⟨r, hsr', hrr'.le.trans hrt, rfl⟩
          simp only [hex, ↓reduceDIte]
          exact congrArg Subtype.val (edgePoint_injective d (Classical.choose_spec hex).2.2)
        have hmin_le : rminReal ≤ r := Finset.min'_le S _ hrS
        linarith [hrmin_eq]
      have hneV :
          (⟨edgePoint d s, hs⟩ : { z : MetricGraph W // z ∈ B }) ≠ ⟨edgePoint d rmin, hrmin_mem⟩ :=
        fun h => hsr.ne (congrArg Subtype.val (edgePoint_injective d (congrArg Subtype.val h)))
      have hadj : (subdivideGraph W B).Adj ⟨edgePoint d s, hs⟩ ⟨edgePoint d rmin, hrmin_mem⟩ :=
        ⟨hneV, d, s, rmin, hsr, rfl, rfl, hno⟩
      have hsub : B.filter (fun p =>
          ∃ r : unitInterval, (rmin : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p) ⊂ F := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpB, r, hrr1, hrr2, hre⟩
          exact Finset.mem_filter.mpr ⟨hpB, r, hsr.trans hrr1, hrr2, hre⟩
        · intro heq
          have hmem : edgePoint d rmin ∈ F :=
            Finset.mem_filter.mpr ⟨hrmin_mem, rmin, hsr, hrt, rfl⟩
          rw [← heq] at hmem
          rcases Finset.mem_filter.mp hmem with ⟨_, r, hrr1, _, hre⟩
          have hr_eq : r = rmin := edgePoint_injective d hre
          linarith [congrArg Subtype.val hr_eq]
      have hcard' : (B.filter (fun p =>
          ∃ r : unitInterval, (rmin : ℝ) < r ∧ (r : ℝ) ≤ t ∧ edgePoint d r = p)).card ≤ n :=
        Nat.lt_succ_iff.mp ((Finset.card_lt_card hsub).trans_le hcard)
      obtain ⟨q, hq⟩ := ih rmin t hrmin_mem ht hrt hcard'
      refine ⟨Walk.cons hadj q, ?_⟩
      rw [walkLength_cons, hq]
      have hne' : (edgePoint d s : MetricGraph W) ≠ edgePoint d rmin :=
        fun h => hsr.ne (congrArg Subtype.val (edgePoint_injective d h))
      rw [subWeight_eq_of_witness hne' hsr rfl rfl]
      ring
    · have heq : s = t := Subtype.ext (le_antisymm hle (not_lt.mp hst))
      subst heq
      exact ⟨Walk.nil, by simp⟩

/-- Subdivide a connected weighted graph `W` at a finite set of points `B` containing
all original vertices. -/
noncomputable def subdivide (W : WeightedGraph V)
    (B : Finset (MetricGraph W)) (hV : ∀ v : V, vertex v ∈ B) :
    WeightedGraph { z : MetricGraph W // z ∈ B } where
  graph := subdivideGraph W B
  weight := subWeight W B
  weight_pos {x y} h := by
    rcases h with ⟨hne, d, s, t, hst, hs, ht, _⟩
    have hne' : x.1 ≠ y.1 := fun h1 => hne (Subtype.ext h1)
    rw [subWeight_eq_of_witness hne' hst hs ht]
    exact mul_pos (sub_pos.mpr hst) (W.dart_weight_pos d)
  connected := by
    classical
    rw [connected_iff_exists_forall_reachable]
    obtain ⟨v₀⟩ := W.connected.nonempty
    refine ⟨⟨vertex v₀, hV v₀⟩, fun ⟨x, hx⟩ => ?_⟩
    have hVreach : ∀ u : V,
        (subdivideGraph W B).Reachable ⟨vertex v₀, hV v₀⟩ ⟨vertex u, hV u⟩ := by
      intro u
      obtain ⟨p⟩ := W.connected v₀ u
      induction p with
      | nil => exact Reachable.refl _
      | cons h _ ih =>
        let d : W.graph.Dart := ⟨(_, _), h⟩
        have h0 : edgePoint d 0 = (vertex d.fst : MetricGraph W) := edgePoint_zero d
        have h1 : edgePoint d 1 = (vertex d.snd : MetricGraph W) := edgePoint_one d
        obtain ⟨q, _⟩ := exists_walk_along_dart d B.card 0 1 (h0 ▸ hV d.fst) (h1 ▸ hV d.snd)
          zero_le_one (Finset.card_filter_le B _)
        have hq' : (subdivideGraph W B).Reachable ⟨edgePoint d 0, h0 ▸ hV d.fst⟩
            ⟨edgePoint d 1, h1 ▸ hV d.snd⟩ := ⟨q⟩
        have hs0 : (⟨edgePoint d 0, h0 ▸ hV d.fst⟩ : { z // z ∈ B }) =
            ⟨vertex d.fst, hV d.fst⟩ := Subtype.ext h0
        have hs1 : (⟨edgePoint d 1, h1 ▸ hV d.snd⟩ : { z // z ∈ B }) =
            ⟨vertex d.snd, hV d.snd⟩ := Subtype.ext h1
        rw [hs0, hs1] at hq'
        exact hq'.trans ih
    induction x using ind_simple with
    | vertex u => exact hVreach u
    | edgePoint d s =>
      have h0 : edgePoint d 0 = (vertex d.fst : MetricGraph W) := edgePoint_zero d
      obtain ⟨q, _⟩ := exists_walk_along_dart d B.card 0 s (h0 ▸ hV d.fst) hx s.2.1
        (Finset.card_filter_le B _)
      exact (hVreach d.fst).trans ⟨by simpa only [h0] using q⟩

@[simp]
theorem subdivide_adj_iff {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    {x y : { z : MetricGraph W // z ∈ B }} :
    (subdivide W B hV).graph.Adj x y ↔ SubAdj W B x y := Iff.rfl

private theorem walk_in_subdivide_to_metric [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} {x y : { z : MetricGraph W // z ∈ B }}
    (p : (subdivide W B hV).graph.Walk x y) :
    dist x.1 y.1 ≤ walkLength (subdivide W B hV).weight p := by
  induction p with
  | nil => simp
  | cons hadj q ih =>
    rename_i a c z
    have hhadj := hadj
    rcases hhadj with ⟨hne, d, s, t, hst, hs, ht, _⟩
    have hstep : dist a.1 c.1 ≤ (subdivide W B hV).weight s(a, c) := by
      have hne' : a.1 ≠ c.1 := fun h1 => hne (Subtype.ext h1)
      change dist a.1 c.1 ≤ subWeight W B s(a, c)
      rw [subWeight_eq_of_witness hne' hst hs ht, ← hs, ← ht]
      exact (dist_edgePoint_self_le d s t).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst.le), mul_comm])
    change dist a.1 z.1 ≤ walkLength (subdivide W B hV).weight (Walk.cons hadj q)
    rw [walkLength_cons]
    exact (dist_triangle a.1 c.1 z.1).trans (add_le_add hstep ih)

private theorem vertexDist_subdivide_le_of_walk {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} {u v : V} (p : W.graph.Walk u v) :
    vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
        ⟨vertex u, hV u⟩ ⟨vertex v, hV v⟩ ≤ walkLength W.weight p := by
  classical
  induction p with
  | nil => simp [vertexDist_self (subdivide W B hV).weight_nonneg]
  | cons h q ih =>
    rename_i a c z
    rw [walkLength_cons]
    let d : W.graph.Dart := ⟨(a, c), h⟩
    have h0 : edgePoint d 0 = (vertex a : MetricGraph W) := edgePoint_zero d
    have h1 : edgePoint d 1 = (vertex c : MetricGraph W) := edgePoint_one d
    obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d B.card 0 1 (h0 ▸ hV a) (h1 ▸ hV c)
      zero_le_one (Finset.card_filter_le B _)
    have hstep : vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
        ⟨vertex a, hV a⟩ ⟨vertex c, hV c⟩ ≤ W.weight s(a, c) := by
      have hle : vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d 0, h0 ▸ hV a⟩ ⟨edgePoint d 1, h1 ▸ hV c⟩ ≤ W.weight s(a, c) := by
        refine (vertexDist_le (subdivide W B hV).weight_nonneg p').trans_eq ?_
        change walkLength (subWeight W B) p' = _
        rw [hp']
        simp [d]
      simpa only [h0, h1] using hle
    exact (vertexDist_triangle (subdivide W B hV).weight_nonneg
      ((subdivide W B hV).connected _ _) ((subdivide W B hV).connected _ _)).trans
      (add_le_add hstep ih)

/-- Vertex shortest-path distance in `subdivide W B hV` equals geodesic distance in
`MetricGraph W`. -/
theorem vertexDist_subdivide [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (x y : { z : MetricGraph W // z ∈ B }) :
    vertexDist (subdivide W B hV).graph (subdivide W B hV).weight x y = dist x.1 y.1 := by
  classical
  refine le_antisymm ?_ ?_
  · have hVdist : ∀ u v : V,
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨vertex u, hV u⟩ ⟨vertex v, hV v⟩ ≤ vertexDist W.graph W.weight u v := by
      intro u v
      obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
      rw [← hp]
      exact (vertexDist_subdivide_le_of_walk p)
    have hWalk {x y : { z : MetricGraph W // z ∈ B }}
        (p' : (subdivideGraph W B).Walk x y) :
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight x y ≤
          walkLength (subWeight W B) p' :=
      vertexDist_le (subdivide W B hV).weight_nonneg p'
    have hDartToEnd : ∀ (d : W.graph.Dart) (s : unitInterval) (hs : edgePoint d s ∈ B),
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d s, hs⟩ ⟨vertex d.fst, hV d.fst⟩ ≤ (s : ℝ) * W.weight d.edge ∧
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d s, hs⟩ ⟨vertex d.snd, hV d.snd⟩ ≤ (1 - (s : ℝ)) * W.weight d.edge := by
      intro d s hs
      constructor
      · have h0 : edgePoint d 0 = (vertex d.fst : MetricGraph W) := edgePoint_zero d
        obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d B.card 0 s (h0 ▸ hV d.fst) hs
          s.2.1 (Finset.card_filter_le B _)
        rw [vertexDist_comm]
        have hle := (hWalk p').trans_eq hp'
        have hsub0 : (⟨edgePoint d 0, h0 ▸ hV d.fst⟩ : { z // z ∈ B }) =
            ⟨vertex d.fst, hV d.fst⟩ := Subtype.ext h0
        rw [hsub0, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero] at hle
        exact hle
      · have h1 : edgePoint d 1 = (vertex d.snd : MetricGraph W) := edgePoint_one d
        obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d B.card s 1 hs (h1 ▸ hV d.snd)
          s.2.2 (Finset.card_filter_le B _)
        have hle := (hWalk p').trans_eq hp'
        have hsub1 : (⟨edgePoint d 1, h1 ▸ hV d.snd⟩ : { z // z ∈ B }) =
            ⟨vertex d.snd, hV d.snd⟩ := Subtype.ext h1
        rw [hsub1, show ((1 : unitInterval) : ℝ) = 1 from rfl] at hle
        exact hle
    have hSameEdge : ∀ (d : W.graph.Dart) (s t : unitInterval)
        (hs : edgePoint d s ∈ B) (ht : edgePoint d t ∈ B),
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d s, hs⟩ ⟨edgePoint d t, ht⟩ ≤ |(s : ℝ) - t| * W.weight d.edge := by
      intro d s t hs ht
      by_cases hst : (s : ℝ) ≤ t
      · obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d B.card s t hs ht hst
          (Finset.card_filter_le B _)
        refine (hWalk p').trans_eq ?_
        rw [hp', abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      · have hts : (t : ℝ) ≤ s := le_of_not_ge hst
        obtain ⟨p', hp'⟩ := exists_walk_along_dart (B := B) d B.card t s ht hs hts
          (Finset.card_filter_le B _)
        rw [vertexDist_comm]
        refine (hWalk p').trans_eq ?_
        rw [hp', abs_of_nonneg (sub_nonneg.mpr hts)]
    have hVia : ∀ (d₁ : W.graph.Dart) (t₁ : unitInterval) (ht₁ : edgePoint d₁ t₁ ∈ B)
        (d₂ : W.graph.Dart) (t₂ : unitInterval) (ht₂ : edgePoint d₂ t₂ ∈ B),
        vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
          ⟨edgePoint d₁ t₁, ht₁⟩ ⟨edgePoint d₂ t₂, ht₂⟩ ≤
        min
          (min ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.fst +
                  (t₂ : ℝ) * W.weight d₂.edge)
               ((t₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.snd +
                  (1 - (t₂ : ℝ)) * W.weight d₂.edge))
          (min ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.fst +
                  (t₂ : ℝ) * W.weight d₂.edge)
               ((1 - (t₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.snd +
                  (1 - (t₂ : ℝ)) * W.weight d₂.edge)) := by
      intro d₁ t₁ ht₁ d₂ t₂ ht₂
      obtain ⟨h10, h11⟩ := hDartToEnd d₁ t₁ ht₁
      obtain ⟨h20, h21⟩ := hDartToEnd d₂ t₂ ht₂
      have step : ∀ u₁ u₂ : V,
          vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
            ⟨edgePoint d₁ t₁, ht₁⟩ ⟨edgePoint d₂ t₂, ht₂⟩ ≤
          vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
            ⟨edgePoint d₁ t₁, ht₁⟩ ⟨vertex u₁, hV u₁⟩ +
          vertexDist W.graph W.weight u₁ u₂ +
          vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
            ⟨edgePoint d₂ t₂, ht₂⟩ ⟨vertex u₂, hV u₂⟩ := by
        intro u₁ u₂
        have ht1 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨edgePoint d₁ t₁, ht₁⟩ ⟨vertex u₁, hV u₁⟩)
          ((subdivide W B hV).connected ⟨vertex u₁, hV u₁⟩ ⟨edgePoint d₂ t₂, ht₂⟩)
        have ht2 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨vertex u₁, hV u₁⟩ ⟨vertex u₂, hV u₂⟩)
          ((subdivide W B hV).connected ⟨vertex u₂, hV u₂⟩ ⟨edgePoint d₂ t₂, ht₂⟩)
        have hcomm :
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨vertex u₂, hV u₂⟩ ⟨edgePoint d₂ t₂, ht₂⟩ =
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨edgePoint d₂ t₂, ht₂⟩ ⟨vertex u₂, hV u₂⟩ := by rw [vertexDist_comm]
        rw [hcomm] at ht2
        linarith [hVdist u₁ u₂]
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> linarith [step d₁.fst d₂.fst,
        step d₁.fst d₂.snd, step d₁.snd d₂.fst, step d₁.snd d₂.snd]
    rcases x with ⟨px, hx⟩; rcases y with ⟨py, hy⟩
    induction px using ind_simple with
    | vertex u =>
      induction py using ind_simple with
      | vertex v => simpa only [dist_vertex] using hVdist u v
      | edgePoint d₂ t₂ =>
        rw [dist_vertex_edgePoint]
        obtain ⟨h20, h21⟩ := hDartToEnd d₂ t₂ hy
        have ht1 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨vertex u, hx⟩ ⟨vertex d₂.fst, hV d₂.fst⟩)
          ((subdivide W B hV).connected ⟨vertex d₂.fst, hV d₂.fst⟩ ⟨edgePoint d₂ t₂, hy⟩)
        have ht2 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨vertex u, hx⟩ ⟨vertex d₂.snd, hV d₂.snd⟩)
          ((subdivide W B hV).connected ⟨vertex d₂.snd, hV d₂.snd⟩ ⟨edgePoint d₂ t₂, hy⟩)
        have hc1 :
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨vertex d₂.fst, hV d₂.fst⟩ ⟨edgePoint d₂ t₂, hy⟩ =
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨edgePoint d₂ t₂, hy⟩ ⟨vertex d₂.fst, hV d₂.fst⟩ := by rw [vertexDist_comm]
        have hc2 :
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨vertex d₂.snd, hV d₂.snd⟩ ⟨edgePoint d₂ t₂, hy⟩ =
            vertexDist (subdivide W B hV).graph (subdivide W B hV).weight
              ⟨edgePoint d₂ t₂, hy⟩ ⟨vertex d₂.snd, hV d₂.snd⟩ := by rw [vertexDist_comm]
        rw [hc1] at ht1
        rw [hc2] at ht2
        refine le_min ?_ ?_ <;> linarith [hVdist u d₂.fst, hVdist u d₂.snd]
    | edgePoint d₁ t₁ =>
      induction py using ind_simple with
      | vertex v =>
        rw [dist_edgePoint_vertex]
        obtain ⟨h10, h11⟩ := hDartToEnd d₁ t₁ hx
        have ht1 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨edgePoint d₁ t₁, hx⟩ ⟨vertex d₁.fst, hV d₁.fst⟩)
          ((subdivide W B hV).connected ⟨vertex d₁.fst, hV d₁.fst⟩ ⟨vertex v, hy⟩)
        have ht2 := vertexDist_triangle (subdivide W B hV).weight_nonneg
          ((subdivide W B hV).connected ⟨edgePoint d₁ t₁, hx⟩ ⟨vertex d₁.snd, hV d₁.snd⟩)
          ((subdivide W B hV).connected ⟨vertex d₁.snd, hV d₁.snd⟩ ⟨vertex v, hy⟩)
        refine le_min ?_ ?_ <;> linarith [hVdist d₁.fst v, hVdist d₁.snd v]
      | edgePoint d₂ t₂ =>
        by_cases he : d₁.edge = d₂.edge
        · rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | hsym
          · rw [dist_edgePoint_edgePoint_same]
            exact le_min (hSameEdge d₁ t₁ t₂ hx hy) (hVia d₁ t₁ hx d₁ t₂ hy)
          · subst hsym
            have heq :
                (edgePoint d₂.symm t₁ : MetricGraph W) = edgePoint d₂ (unitInterval.symm t₁) :=
              (edgePoint_symm' d₂ t₁).symm
            have hx' : edgePoint d₂ (unitInterval.symm t₁) ∈ B := heq ▸ hx
            have hsub_eq : (⟨edgePoint d₂.symm t₁, hx⟩ : { z // z ∈ B }) =
                ⟨edgePoint d₂ (unitInterval.symm t₁), hx'⟩ := Subtype.ext heq
            rw [hsub_eq]
            dsimp only
            rw [dist_edgePoint_edgePoint_same]
            exact le_min (hSameEdge d₂ (unitInterval.symm t₁) t₂ hx' hy)
              (hVia d₂ (unitInterval.symm t₁) hx' d₂ t₂ hy)
        · rw [dist_edgePoint_edgePoint_of_edge_ne he]
          exact hVia d₁ t₁ hx d₂ t₂ hy
  · obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist
      (subdivide W B hV).weight_nonneg ((subdivide W B hV).connected x y)
    rw [← hp]
    exact walk_in_subdivide_to_metric p

/-! ### Isometric equivalence between a subdivision and the original metric graph -/

private noncomputable def interpUnit (s t r : unitInterval) (hst : (s : ℝ) ≤ t) : unitInterval :=
  ⟨(1 - (r : ℝ)) * s + r * t,
    add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg r) s.2.1) (mul_nonneg r.2.1 t.2.1),
    by nlinarith [r.2.1, r.2.2, s.2.2, t.2.2]⟩

private theorem interpUnit_zero (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    interpUnit s t 0 hst = s := by
  ext; simp [interpUnit]

private theorem interpUnit_one (s t : unitInterval) (hst : (s : ℝ) ≤ t) :
    interpUnit s t 1 hst = t := by
  ext; simp [interpUnit]

private theorem interpUnit_symm (s t r : unitInterval) (hst : (s : ℝ) ≤ t)
    (hst' : (unitInterval.symm t : ℝ) ≤ unitInterval.symm s) :
    interpUnit (unitInterval.symm t) (unitInterval.symm s) (unitInterval.symm r) hst' =
      unitInterval.symm (interpUnit s t r hst) := by
  ext
  change (1 - (1 - (r : ℝ))) * (1 - t) + (1 - r) * (1 - s) = 1 - ((1 - r) * s + r * t)
  ring

private theorem interpUnit_mem_Icc (s t r : unitInterval) (hst : (s : ℝ) ≤ t) :
    (s : ℝ) ≤ interpUnit s t r hst ∧ (interpUnit s t r hst : ℝ) ≤ t := by
  constructor <;> dsimp only [interpUnit] <;> nlinarith [r.2.1, r.2.2, hst]

private noncomputable def subDartOrigin {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : W.graph.Dart :=
  Classical.choose d'.adj.2

private noncomputable def subDartStart {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : unitInterval :=
  Classical.choose (Classical.choose_spec d'.adj.2)

private noncomputable def subDartEnd {B : Finset (MetricGraph W)}
    {hV : ∀ v, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) : unitInterval :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec d'.adj.2))

private theorem subDart_spec {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    (subDartStart d' : ℝ) < subDartEnd d' ∧
    edgePoint (subDartOrigin d') (subDartStart d') = d'.fst.1 ∧
    edgePoint (subDartOrigin d') (subDartEnd d') = d'.snd.1 ∧
    ∀ r : unitInterval, (subDartStart d' : ℝ) < r → (r : ℝ) < subDartEnd d' →
      edgePoint (subDartOrigin d') r ∉ B :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec d'.adj.2))

private theorem subDart_weight {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    (subdivide W B hV).weight d'.edge =
      ((subDartEnd d' : ℝ) - subDartStart d') * W.weight (subDartOrigin d').edge := by
  have hsp := subDart_spec d'
  have hne : d'.fst.1 ≠ d'.snd.1 := fun h => d'.fst_ne_snd (Subtype.ext h)
  exact subWeight_eq_of_witness hne hsp.1 hsp.2.1 hsp.2.2.1

private theorem subDartStart_lt_end {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) : (subDartStart d' : ℝ) < subDartEnd d' :=
  (subDart_spec d').1

private theorem subDart_symm {B : Finset (MetricGraph W)} {hV : ∀ v, vertex v ∈ B}
    (d' : (subdivide W B hV).graph.Dart) :
    subDartOrigin d'.symm = (subDartOrigin d').symm ∧
    subDartStart d'.symm = unitInterval.symm (subDartEnd d') ∧
    subDartEnd d'.symm = unitInterval.symm (subDartStart d') := by
  have h1 := subDart_spec d'
  have h2 := subDart_spec d'.symm
  refine subAdj_witness_eq h2.1
    (by change 1 - (subDartEnd d' : ℝ) < 1 - subDartStart d'; linarith [h1.1]) ?_ ?_
  · rw [h2.2.1, edgePoint_symm]
    exact h1.2.2.1.symm
  · rw [h2.2.2.1, edgePoint_symm]
    exact h1.2.1.symm

private noncomputable def subdivideToMetric {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) :
    MetricGraph (subdivide W B hV) → MetricGraph W :=
  lift (fun x => x.1)
    (fun d' r => edgePoint (subDartOrigin d')
      (interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le))
    (fun d' => by simp only [interpUnit_zero]; exact (subDart_spec d').2.1)
    (fun d' => by simp only [interpUnit_one]; exact (subDart_spec d').2.2.1)
    (fun d' r => by
      obtain ⟨hO, hS, hE⟩ := subDart_symm d'
      have hst := (subDartStart_lt_end d').le
      have hst' := (subDartStart_lt_end d'.symm).le
      have hcongr :
          interpUnit (subDartStart d'.symm) (subDartEnd d'.symm) (unitInterval.symm r) hst' =
          unitInterval.symm (interpUnit (subDartStart d') (subDartEnd d') r hst) := by
        simp only [hS, hE]
        exact interpUnit_symm _ _ r hst _
      rw [hcongr, hO, edgePoint_symm])

private theorem subdivideToMetric_dist_le [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (p q : MetricGraph (subdivide W B hV)) :
    dist (subdivideToMetric hV p) (subdivideToMetric hV q) ≤ dist p q := by
  refine dist_map_le_of_edgePoint_dist_le (subdivideToMetric hV) (fun d' r₁ r₂ => ?_) p q
  simp only [subdivideToMetric, lift_edgePoint]
  rw [subDart_weight d']
  refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
  have heq : |(interpUnit (subDartStart d') (subDartEnd d') r₁ (subDartStart_lt_end d').le : ℝ) -
      (interpUnit (subDartStart d') (subDartEnd d') r₂ (subDartStart_lt_end d').le : ℝ)| =
      |(r₁ : ℝ) - r₂| * ((subDartEnd d' : ℝ) - subDartStart d') := by
    change |((1 - (r₁ : ℝ)) * subDartStart d' + r₁ * subDartEnd d') -
        ((1 - (r₂ : ℝ)) * subDartStart d' + r₂ * subDartEnd d')| = _
    have hsub : ((1 - (r₁ : ℝ)) * subDartStart d' + r₁ * subDartEnd d') -
        ((1 - (r₂ : ℝ)) * subDartStart d' + r₂ * subDartEnd d') =
        ((r₁ : ℝ) - r₂) * ((subDartEnd d' : ℝ) - subDartStart d') := by ring
    rw [hsub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (subDartStart_lt_end d').le)]
  rw [heq]; ring

private theorem subInterval_outside_of_mem {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart)
    {r : unitInterval} (hrB : edgePoint (subDartOrigin d') r ∈ B) :
    (r : ℝ) ≤ subDartStart d' ∨ (subDartEnd d' : ℝ) ≤ r := by
  by_contra hnot
  push Not at hnot
  exact (subDart_spec d').2.2.2 r hnot.1 hnot.2 hrB

private theorem subInterval_disjoint_of_edge_ne {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} {d₁' d₂' : (subdivide W B hV).graph.Dart}
    (hne : d₁'.edge ≠ d₂'.edge) (heq : subDartOrigin d₁' = subDartOrigin d₂') :
    (subDartEnd d₁' : ℝ) ≤ subDartStart d₂' ∨ (subDartEnd d₂' : ℝ) ≤ subDartStart d₁' := by
  have hsp1 := subDart_spec d₁'
  have hsp2 := subDart_spec d₂'
  have h1a : (subDartStart d₁' : ℝ) ≤ subDartStart d₂' ∨
      (subDartEnd d₂' : ℝ) ≤ subDartStart d₁' :=
    subInterval_outside_of_mem d₂' (heq ▸ hsp1.2.1 ▸ d₁'.fst.2)
  have h1b : (subDartEnd d₁' : ℝ) ≤ subDartStart d₂' ∨
      (subDartEnd d₂' : ℝ) ≤ subDartEnd d₁' :=
    subInterval_outside_of_mem d₂' (heq ▸ hsp1.2.2.1 ▸ d₁'.snd.2)
  have h2a : (subDartStart d₂' : ℝ) ≤ subDartStart d₁' ∨
      (subDartEnd d₁' : ℝ) ≤ subDartStart d₂' :=
    subInterval_outside_of_mem d₁' (heq.symm ▸ hsp2.2.1 ▸ d₂'.fst.2)
  have h2b : (subDartEnd d₂' : ℝ) ≤ subDartStart d₁' ∨
      (subDartEnd d₁' : ℝ) ≤ subDartEnd d₂' :=
    subInterval_outside_of_mem d₁' (heq.symm ▸ hsp2.2.2.1 ▸ d₂'.snd.2)
  rcases h1a with h1a | h1a
  · rcases h2a with h2a | h2a
    · have hs : subDartStart d₁' = subDartStart d₂' := Subtype.ext (le_antisymm h1a h2a)
      rcases h1b with h1b | h1b
      · exact Or.inl h1b
      · rcases h2b with h2b | h2b
        · exact Or.inr h2b
        · have ht : subDartEnd d₁' = subDartEnd d₂' := Subtype.ext (le_antisymm h2b h1b)
          have hfst : d₁'.fst = d₂'.fst := Subtype.ext (by rw [← hsp1.2.1, ← hsp2.2.1, heq, hs])
          have hsnd : d₁'.snd = d₂'.snd := Subtype.ext (by rw [← hsp1.2.2.1, ← hsp2.2.2.1, heq, ht])
          exact absurd (by rw [← Dart.sym2Mk_fst_snd d₁', ← Dart.sym2Mk_fst_snd d₂', hfst, hsnd])
            hne
    · exact Or.inl h2a
  · exact Or.inr h1a

private theorem subEdge_dist_fst_le {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) :
    dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex d'.fst) ≤
      ((interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le : ℝ) -
        subDartStart d') * W.weight (subDartOrigin d').edge := by
  rw [← edgePoint_zero d']
  refine (dist_edgePoint_self_le d' r 0).trans_eq ?_
  rw [subDart_weight d', show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero,
    abs_of_nonneg r.2.1]
  dsimp only [interpUnit]
  ring

private theorem subEdge_dist_snd_le {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) :
    dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex d'.snd) ≤
      ((subDartEnd d' : ℝ) -
        interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le) *
        W.weight (subDartOrigin d').edge := by
  rw [← edgePoint_one d']
  refine (dist_edgePoint_self_le d' r 1).trans_eq ?_
  rw [subDart_weight d', show ((1 : unitInterval) : ℝ) = 1 from rfl,
    abs_sub_comm, abs_of_nonneg (unitInterval.one_sub_nonneg r)]
  dsimp only [interpUnit]
  ring

private theorem subEdge_dist_edge_le_of_sameOrigin [Finite V] {B : Finset (MetricGraph W)}
    {hV : ∀ v : V, vertex v ∈ B} {d₁' d₂' : (subdivide W B hV).graph.Dart}
    (hne : d₁'.edge ≠ d₂'.edge) (hO : subDartOrigin d₁' = subDartOrigin d₂')
    (r₁ r₂ : unitInterval) :
    dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
      |(interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le : ℝ) -
        interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le| *
        W.weight (subDartOrigin d₁').edge := by
  have hmem1 := interpUnit_mem_Icc
    (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le
  have hmem2 := interpUnit_mem_Icc
    (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le
  have h_step : ∀ {a' b' : (subdivide W B hV).graph.Dart} {ra rb : unitInterval},
      subDartOrigin a' = subDartOrigin b' → (subDartEnd a' : ℝ) ≤ subDartStart b' →
      dist (edgePoint a' ra : MetricGraph (subdivide W B hV)) (edgePoint b' rb) ≤
        ((interpUnit (subDartStart b') (subDartEnd b') rb (subDartStart_lt_end b').le : ℝ) -
          interpUnit (subDartStart a') (subDartEnd a') ra (subDartStart_lt_end a').le) *
          W.weight (subDartOrigin a').edge := by
    intro a' b' ra rb hOO hab
    have hmid : dist (vertex a'.snd : MetricGraph (subdivide W B hV)) (vertex b'.fst) ≤
        ((subDartStart b' : ℝ) - subDartEnd a') * W.weight (subDartOrigin a').edge := by
      rw [dist_vertex, vertexDist_subdivide]
      rw [← (subDart_spec a').2.2.1, ← (subDart_spec b').2.1, hOO]
      refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm]
    have htri := dist_triangle4 (edgePoint a' ra : MetricGraph (subdivide W B hV))
      (vertex a'.snd) (vertex b'.fst) (edgePoint b' rb)
    rw [dist_comm (vertex b'.fst) (edgePoint b' rb)] at htri
    have hs1 := subEdge_dist_snd_le a' ra
    have hs2 := subEdge_dist_fst_le b' rb
    rw [← hOO] at hs2
    linarith
  rcases subInterval_disjoint_of_edge_ne hne hO with h12 | h21
  · have hle :
        (interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le : ℝ) ≤
        interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le :=
      hmem1.2.trans (h12.trans hmem2.1)
    rw [abs_sub_comm (interpUnit _ _ r₁ _ : ℝ), abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h_step hO h12
  · have hle :
        (interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le : ℝ) ≤
        interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le :=
      hmem2.2.trans (h21.trans hmem1.1)
    rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hle), hO]
    exact h_step hO.symm h21

private theorem dist_le_subdivideToMetric [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (p q : MetricGraph (subdivide W B hV)) :
    dist p q ≤ dist (subdivideToMetric hV p) (subdivideToMetric hV q) := by
  have hToOrigV : ∀ (d' : (subdivide W B hV).graph.Dart) (r : unitInterval),
      let u := interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le
      dist (edgePoint d' r : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex (subDartOrigin d').fst, hV _⟩) ≤
        (u : ℝ) * W.weight (subDartOrigin d').edge ∧
      dist (edgePoint d' r : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex (subDartOrigin d').snd, hV _⟩) ≤
        (1 - (u : ℝ)) * W.weight (subDartOrigin d').edge := by
    intro d' r u
    have h0 : edgePoint (subDartOrigin d') 0 = (vertex (subDartOrigin d').fst : MetricGraph W) :=
      edgePoint_zero _
    have h1 : edgePoint (subDartOrigin d') 1 = (vertex (subDartOrigin d').snd : MetricGraph W) :=
      edgePoint_one _
    constructor
    · refine (dist_triangle _ (vertex d'.fst) _).trans ?_
      have hd1 := subEdge_dist_fst_le d' r
      have hd2 : dist (vertex d'.fst : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex (subDartOrigin d').fst, hV _⟩) ≤
          (subDartStart d' : ℝ) * W.weight (subDartOrigin d').edge := by
        rw [dist_vertex, vertexDist_subdivide]
        change dist d'.fst.1 (vertex (subDartOrigin d').fst) ≤ _
        rw [← (subDart_spec d').2.1, ← h0]
        refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero,
          abs_of_nonneg (subDartStart d').2.1, mul_comm]
      linarith
    · refine (dist_triangle _ (vertex d'.snd) _).trans ?_
      have hd1 := subEdge_dist_snd_le d' r
      have hd2 : dist (vertex d'.snd : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex (subDartOrigin d').snd, hV _⟩) ≤
          (1 - (subDartEnd d' : ℝ)) * W.weight (subDartOrigin d').edge := by
        rw [dist_vertex, vertexDist_subdivide]
        change dist d'.snd.1 (vertex (subDartOrigin d').snd) ≤ _
        rw [← (subDart_spec d').2.2.1, ← h1]
        refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
        rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
          abs_sub_comm (subDartEnd d' : ℝ) 1,
          abs_of_nonneg (unitInterval.one_sub_nonneg (subDartEnd d')), mul_comm]
      linarith
  have hFromVertex : ∀ (d' : (subdivide W B hV).graph.Dart) (r : unitInterval) (x : { z // z ∈ B }),
      dist (vertex x : MetricGraph (subdivide W B hV)) (edgePoint d' r) ≤
        dist x.1 (subdivideToMetric hV (edgePoint d' r)) := by
    intro d' r ⟨x, hx⟩
    simp only [subdivideToMetric, lift_edgePoint]
    let u := interpUnit (subDartStart d') (subDartEnd d') r (subDartStart_lt_end d').le
    obtain ⟨h0, h1⟩ := hToOrigV d' r
    have hVbound : ∀ (z : { z : MetricGraph W // z ∈ B }) (v : V) (off : ℝ),
        dist (edgePoint d' r : MetricGraph (subdivide W B hV)) (vertex ⟨vertex v, hV v⟩) ≤ off →
        dist (vertex z : MetricGraph (subdivide W B hV)) (edgePoint d' r) ≤
          dist z.1 (vertex v) + off := by
      intro z v off hoff
      have hv : dist (vertex z : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex v, hV v⟩) = dist z.1 (vertex v) := by
        rw [dist_vertex, vertexDist_subdivide]
      rw [dist_comm] at hoff
      linarith [dist_triangle (vertex z : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex v, hV v⟩) (edgePoint d' r)]
    have sameDartCase : ∀ (s₀ : unitInterval) (hs₀ : edgePoint (subDartOrigin d') s₀ ∈ B),
        dist (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ : MetricGraph (subdivide W B hV))
          (edgePoint d' r) ≤
        |(s₀ : ℝ) - u| * W.weight (subDartOrigin d').edge := by
      intro s₀ hs₀
      have hmem := interpUnit_mem_Icc (subDartStart d') (subDartEnd d') r
        (subDartStart_lt_end d').le
      rcases subInterval_outside_of_mem d' hs₀ with hs0 | hs0
      · have h1' : dist (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ :
            MetricGraph (subdivide W B hV)) (vertex d'.fst) ≤
            ((subDartStart d' : ℝ) - s₀) * W.weight (subDartOrigin d').edge := by
          rw [dist_vertex, vertexDist_subdivide]
          change dist (edgePoint (subDartOrigin d') s₀) d'.fst.1 ≤ _
          rw [← (subDart_spec d').2.1]
          refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs0), mul_comm]
        have h2' := subEdge_dist_fst_le d' r
        rw [dist_comm] at h2'
        have hle_su : (s₀ : ℝ) ≤ u := hs0.trans hmem.1
        rw [abs_sub_comm (s₀ : ℝ) u, abs_of_nonneg (sub_nonneg.mpr hle_su)]
        linarith [dist_triangle (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ :
          MetricGraph (subdivide W B hV)) (vertex d'.fst) (edgePoint d' r)]
      · have h1' : dist (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ :
            MetricGraph (subdivide W B hV)) (vertex d'.snd) ≤
            ((s₀ : ℝ) - subDartEnd d') * W.weight (subDartOrigin d').edge := by
          rw [dist_vertex, vertexDist_subdivide]
          change dist (edgePoint (subDartOrigin d') s₀) d'.snd.1 ≤ _
          rw [← (subDart_spec d').2.2.1]
          refine (dist_edgePoint_self_le _ _ _).trans_eq ?_
          rw [abs_of_nonneg (sub_nonneg.mpr hs0), mul_comm]
        have h2' := subEdge_dist_snd_le d' r
        rw [dist_comm] at h2'
        have hle_us : (u : ℝ) ≤ s₀ := hmem.2.trans hs0
        rw [abs_of_nonneg (sub_nonneg.mpr hle_us)]
        linarith [dist_triangle (vertex ⟨edgePoint (subDartOrigin d') s₀, hs₀⟩ :
          MetricGraph (subdivide W B hV)) (vertex d'.snd) (edgePoint d' r)]
    induction x using ind_simple with
    | vertex v =>
      rw [dist_vertex_edgePoint (W := W)]
      refine le_min ?_ ?_
      · rw [← dist_vertex (W := W)]
        exact hVbound _ _ _ h0
      · rw [← dist_vertex (W := W)]
        exact hVbound _ _ _ h1
    | edgePoint d₀ s₀ =>
      by_cases he : d₀.edge = (subDartOrigin d').edge
      · rcases (dart_edge_eq_iff d₀ (subDartOrigin d')).mp he with rfl | hsym
        · rw [dist_edgePoint_eq_min_same (W := W)]
          exact le_min (sameDartCase s₀ hx)
            (le_min (hVbound _ _ _ h0) (hVbound _ _ _ h1))
        · subst hsym
          have heq : (edgePoint (subDartOrigin d').symm s₀ : MetricGraph W) =
              edgePoint (subDartOrigin d') (unitInterval.symm s₀) := (edgePoint_symm' _ s₀).symm
          have hx' : edgePoint (subDartOrigin d') (unitInterval.symm s₀) ∈ B := heq ▸ hx
          have hsub_eq : (⟨edgePoint (subDartOrigin d').symm s₀, hx⟩ : { z // z ∈ B }) =
              ⟨edgePoint (subDartOrigin d') (unitInterval.symm s₀), hx'⟩ := Subtype.ext heq
          rw [hsub_eq, show (edgePoint (subDartOrigin d').symm s₀ : MetricGraph W) =
              edgePoint (subDartOrigin d') (unitInterval.symm s₀) from heq,
            dist_edgePoint_eq_min_same (W := W)]
          exact le_min (sameDartCase (unitInterval.symm s₀) hx')
            (le_min (hVbound _ _ _ h0) (hVbound _ _ _ h1))
      · rw [dist_edgePoint_eq_min_of_edge_ne (W := W) he]
        exact le_min (hVbound _ _ _ h0) (hVbound _ _ _ h1)
  have hViaEdge : ∀ (d₁' d₂' : (subdivide W B hV).graph.Dart) (r₁ r₂ : unitInterval),
      dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
        let u₁ := interpUnit (subDartStart d₁') (subDartEnd d₁') r₁ (subDartStart_lt_end d₁').le
        let u₂ := interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le
        min
          (min ((u₁ : ℝ) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').fst (subDartOrigin d₂').fst +
                  (u₂ : ℝ) * W.weight (subDartOrigin d₂').edge)
               ((u₁ : ℝ) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').fst (subDartOrigin d₂').snd +
                  (1 - (u₂ : ℝ)) * W.weight (subDartOrigin d₂').edge))
          (min ((1 - (u₁ : ℝ)) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').snd (subDartOrigin d₂').fst +
                  (u₂ : ℝ) * W.weight (subDartOrigin d₂').edge)
               ((1 - (u₁ : ℝ)) * W.weight (subDartOrigin d₁').edge +
                  vertexDist W.graph W.weight (subDartOrigin d₁').snd (subDartOrigin d₂').snd +
                  (1 - (u₂ : ℝ)) * W.weight (subDartOrigin d₂').edge)) := by
    intro d₁' d₂' r₁ r₂
    obtain ⟨h10, h11⟩ := hToOrigV d₁' r₁
    obtain ⟨h20, h21⟩ := hToOrigV d₂' r₂
    have step : ∀ (v₁ v₂ : V) (off₁ off₂ : ℝ),
        dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex v₁, hV v₁⟩) ≤ off₁ →
        dist (edgePoint d₂' r₂ : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex v₂, hV v₂⟩) ≤ off₂ →
        dist (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV)) (edgePoint d₂' r₂) ≤
          off₁ + vertexDist W.graph W.weight v₁ v₂ + off₂ := by
      intro v₁ v₂ off₁ off₂ ho₁ ho₂
      have hv : dist (vertex ⟨vertex v₁, hV v₁⟩ : MetricGraph (subdivide W B hV))
          (vertex ⟨vertex v₂, hV v₂⟩) ≤ vertexDist W.graph W.weight v₁ v₂ := by
        rw [dist_vertex, vertexDist_subdivide, dist_vertex]
      have htri := dist_triangle4 (edgePoint d₁' r₁ : MetricGraph (subdivide W B hV))
        (vertex ⟨vertex v₁, hV v₁⟩) (vertex ⟨vertex v₂, hV v₂⟩) (edgePoint d₂' r₂)
      rw [dist_comm (vertex ⟨vertex v₂, hV v₂⟩) (edgePoint d₂' r₂)] at htri
      linarith
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact step _ _ _ _ h10 h20
    · exact step _ _ _ _ h10 h21
    · exact step _ _ _ _ h11 h20
    · exact step _ _ _ _ h11 h21
  induction p using ind_simple with
  | vertex x =>
    induction q using ind_simple with
    | vertex y =>
      simp only [subdivideToMetric, lift_vertex, dist_vertex, vertexDist_subdivide, le_refl]
    | edgePoint d' r =>
      simp only [subdivideToMetric, lift_vertex]
      exact hFromVertex d' r x
  | edgePoint d₁' r₁ =>
    induction q using ind_simple with
    | vertex y =>
      rw [dist_comm, dist_comm (subdivideToMetric hV (edgePoint d₁' r₁))]
      simp only [subdivideToMetric, lift_vertex]
      exact hFromVertex d₁' r₁ y
    | edgePoint d₂' r₂ =>
      simp only [subdivideToMetric, lift_edgePoint]
      by_cases he : (subDartOrigin d₁').edge = (subDartOrigin d₂').edge
      · rcases (dart_edge_eq_iff (subDartOrigin d₁') (subDartOrigin d₂')).mp he with hO | hO
        · rw [← hO, dist_edgePoint_edgePoint_same (W := W)]
          refine le_min ?_ (by simpa only [← hO] using hViaEdge d₁' d₂' r₁ r₂)
          by_cases hde : d₁'.edge = d₂'.edge
          · rcases (dart_edge_eq_iff d₁' d₂').mp hde with rfl | hsym
            · refine (dist_edgePoint_self_le d₁' r₁ r₂).trans_eq ?_
              rw [subDart_weight d₁']
              dsimp only [interpUnit]
              have halg : ((1 - (r₁ : ℝ)) * subDartStart d₁' + r₁ * subDartEnd d₁') -
                  ((1 - (r₂ : ℝ)) * subDartStart d₁' + r₂ * subDartEnd d₁') =
                  ((r₁ : ℝ) - r₂) * ((subDartEnd d₁' : ℝ) - subDartStart d₁') := by ring
              rw [halg, abs_mul, abs_of_nonneg (sub_nonneg.mpr (subDartStart_lt_end d₁').le)]
              ring
            · have h := congrArg subDartOrigin hsym
              rw [hO, (subDart_symm d₂').1] at h
              exact absurd h.symm (subDartOrigin d₂').symm_ne
          · exact subEdge_dist_edge_le_of_sameOrigin hde hO r₁ r₂
        · have hds2 := subDart_symm d₂'
          have hO2' : subDartOrigin d₂'.symm = subDartOrigin d₁' := by
            rw [hds2.1, ← hO]
          have he2 : (edgePoint (subDartOrigin d₂') (interpUnit (subDartStart d₂')
              (subDartEnd d₂') r₂ (subDartStart_lt_end d₂').le) : MetricGraph W) =
              edgePoint (subDartOrigin d₁') (interpUnit (subDartStart d₂'.symm)
                (subDartEnd d₂'.symm) (unitInterval.symm r₂)
                (subDartStart_lt_end d₂'.symm).le) := by
            have hst2 := (subDartStart_lt_end d₂').le
            have hst2' := (subDartStart_lt_end d₂'.symm).le
            have hin : interpUnit (subDartStart d₂'.symm) (subDartEnd d₂'.symm)
                (unitInterval.symm r₂) hst2' =
                unitInterval.symm (interpUnit (subDartStart d₂') (subDartEnd d₂') r₂ hst2) := by
              simpa only [hds2.2.1, hds2.2.2] using
                (interpUnit_symm (subDartStart d₂') (subDartEnd d₂') r₂ hst2
                  (by simp only [← hds2.2.1, ← hds2.2.2]; exact hst2'))
            rw [← hO2', hds2.1, hin, edgePoint_symm]
          rw [he2, ← edgePoint_symm d₂' r₂, dist_edgePoint_edgePoint_same (W := W)]
          refine le_min ?_
            (by simpa only [hO2'] using hViaEdge d₁' d₂'.symm r₁ (unitInterval.symm r₂))
          by_cases hde : d₁'.edge = d₂'.symm.edge
          · rcases (dart_edge_eq_iff d₁' d₂'.symm).mp hde with rfl | hsym
            · refine (dist_edgePoint_self_le d₂'.symm r₁ (unitInterval.symm r₂)).trans_eq ?_
              rw [subDart_weight d₂'.symm]
              dsimp only [interpUnit]
              have halg : ((1 - (r₁ : ℝ)) * subDartStart d₂'.symm + r₁ * subDartEnd d₂'.symm) -
                  ((1 - (unitInterval.symm r₂ : ℝ)) * subDartStart d₂'.symm +
                    unitInterval.symm r₂ * subDartEnd d₂'.symm) =
                  ((r₁ : ℝ) - unitInterval.symm r₂) *
                    ((subDartEnd d₂'.symm : ℝ) - subDartStart d₂'.symm) := by ring
              rw [halg, abs_mul, abs_of_nonneg (sub_nonneg.mpr (subDartStart_lt_end d₂'.symm).le)]
              ring
            · have hcontr : (subDartOrigin d₂').symm = subDartOrigin d₂' := by
                have h := congrArg subDartOrigin hsym
                rw [hO, (subDart_symm d₂'.symm).1, hds2.1, Dart.symm_symm] at h
                exact h
              exact absurd hcontr (subDartOrigin d₂').symm_ne
          · exact subEdge_dist_edge_le_of_sameOrigin hde hO2'.symm r₁ (unitInterval.symm r₂)
      · rw [dist_edgePoint_edgePoint_of_edge_ne he]
        exact hViaEdge d₁' d₂' r₁ r₂

/-- The isometric equivalence `MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W`. -/
noncomputable def subdivideEquiv [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) :
    MetricGraph (subdivide W B hV) ≃ᵢ MetricGraph W where
  toEquiv := Equiv.ofBijective (subdivideToMetric hV) ⟨by
    intro p q hpq
    apply dist_eq_zero.mp
    refine le_antisymm ?_ dist_nonneg
    simpa only [hpq, dist_self] using dist_le_subdivideToMetric hV p q, by
    intro y
    induction y using ind_simple with
    | vertex v =>
      refine ⟨vertex ⟨vertex v, hV v⟩, ?_⟩
      simp only [subdivideToMetric, lift_vertex]
    | edgePoint d u =>
      by_cases hu : edgePoint d u ∈ B
      · refine ⟨vertex ⟨edgePoint d u, hu⟩, ?_⟩
        simp only [subdivideToMetric, lift_vertex]
      · classical
        let P : Finset unitInterval :=
          B.filterMap (fun q => if h : ∃ r : unitInterval, edgePoint d r = q
            then some (Classical.choose h) else none) (by
            intro a b c ha hb
            split_ifs at ha hb with h1 h2
            · have h1' : Classical.choose h1 = c := Option.some.inj ha
              have h2' : Classical.choose h2 = c := Option.some.inj hb
              rw [← Classical.choose_spec h1, ← Classical.choose_spec h2, h1', h2']
            · simp at hb
            · simp at ha
            · simp at ha)
        have hP_mem : ∀ r : unitInterval, r ∈ P ↔ edgePoint d r ∈ B := by
          intro r
          simp only [P, Finset.mem_filterMap]
          constructor
          · rintro ⟨q, hq, hreq⟩
            split_ifs at hreq with hq'
            · simp only [Option.some.injEq] at hreq
              subst hreq
              exact (Classical.choose_spec hq').symm ▸ hq
          · intro hrB
            refine ⟨edgePoint d r, hrB, ?_⟩
            have hq : ∃ q : unitInterval, edgePoint d q = edgePoint d r := ⟨r, rfl⟩
            simp only [hq, ↓reduceDIte, Option.some.injEq]
            exact edgePoint_injective d (Classical.choose_spec hq)
        have h0P : (0 : unitInterval) ∈ P := (hP_mem 0).mpr (by rw [edgePoint_zero]; exact hV d.fst)
        have h1P : (1 : unitInterval) ∈ P := (hP_mem 1).mpr (by rw [edgePoint_one]; exact hV d.snd)
        have hu0 : (0 : ℝ) < u := by
          refine lt_of_le_of_ne u.2.1 (fun h => hu ?_)
          have : u = 0 := Subtype.ext h.symm
          rw [this, edgePoint_zero]; exact hV d.fst
        have hu1 : (u : ℝ) < 1 := by
          refine lt_of_le_of_ne u.2.2 (fun h => hu ?_)
          have : u = 1 := Subtype.ext h
          rw [this, edgePoint_one]; exact hV d.snd
        let P_lt := P.filter (fun q : unitInterval => (q : ℝ) < (u : ℝ))
        let P_gt := P.filter (fun q : unitInterval => (u : ℝ) < (q : ℝ))
        have hlt_ne : P_lt.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0P, hu0⟩⟩
        have hgt_ne : P_gt.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1P, hu1⟩⟩
        let s : unitInterval := P_lt.max' hlt_ne
        let t : unitInterval := P_gt.min' hgt_ne
        have hsF := Finset.mem_filter.mp (P_lt.max'_mem hlt_ne)
        have htF := Finset.mem_filter.mp (P_gt.min'_mem hgt_ne)
        have hsu : (s : ℝ) < u := hsF.2
        have hut : (u : ℝ) < t := htF.2
        have hst : (s : ℝ) < t := hsu.trans hut
        have hsB : edgePoint d s ∈ B := (hP_mem s).mp hsF.1
        have htB : edgePoint d t ∈ B := (hP_mem t).mp htF.1
        have hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B := by
          intro r hsr hrt hrB
          have hrP := (hP_mem r).mpr hrB
          rcases lt_trichotomy (r : ℝ) u with hru | hru | hur
          · have hle : r ≤ s := Finset.le_max' P_lt r (Finset.mem_filter.mpr ⟨hrP, hru⟩)
            exact absurd hle (not_le_of_gt hsr)
          · exact hu ((congrArg (edgePoint d) (Subtype.ext hru)).symm ▸ hrB)
          · have hle : t ≤ r := Finset.min'_le P_gt r (Finset.mem_filter.mpr ⟨hrP, hur⟩)
            exact absurd hle (not_le_of_gt hrt)
        have hneV : (⟨edgePoint d s, hsB⟩ : { z // z ∈ B }) ≠ ⟨edgePoint d t, htB⟩ :=
          fun h => hst.ne (congrArg Subtype.val (edgePoint_injective d (congrArg Subtype.val h)))
        let d' : (subdivide W B hV).graph.Dart :=
          ⟨(⟨edgePoint d s, hsB⟩, ⟨edgePoint d t, htB⟩), ⟨hneV, d, s, t, hst, rfl, rfl, hno⟩⟩
        have hdr := subDart_spec d'
        obtain ⟨rfl_d, rfl_s, rfl_t⟩ := subAdj_witness_eq hdr.1 hst hdr.2.1 hdr.2.2.1
        let τ : unitInterval :=
          ⟨((u : ℝ) - s) / (t - s),
            div_nonneg (sub_nonneg.mpr hsu.le) (sub_nonneg.mpr hst.le),
            div_le_one_of_le₀ (by linarith) (sub_nonneg.mpr hst.le)⟩
        refine ⟨edgePoint d' τ, ?_⟩
        simp only [subdivideToMetric, lift_edgePoint]
        congr 1
        ext
        change (1 - (((u : ℝ) - s) / (t - s))) * subDartStart d' +
            (((u : ℝ) - s) / (t - s)) * subDartEnd d' = (u : ℝ)
        rw [rfl_s, rfl_t]
        field_simp [sub_ne_zero.mpr hst.ne']
        ring⟩
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    le_antisymm (subdivideToMetric_dist_le hV p q) (dist_le_subdivideToMetric hV p q)

@[simp]
theorem subdivideEquiv_vertex [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (x : { z : MetricGraph W // z ∈ B }) :
    subdivideEquiv hV (vertex x) = x.1 := by
  change subdivideToMetric hV (vertex x) = x.1
  simp only [subdivideToMetric, lift_vertex]

theorem subdivideEquiv_edgePoint [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    ∃ (d : W.graph.Dart) (s t : unitInterval) (_hst : (s : ℝ) < t),
      edgePoint d s = (d'.fst : MetricGraph W) ∧ edgePoint d t = (d'.snd : MetricGraph W) ∧
      (∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ∉ B) ∧
      (subdivide W B hV).weight d'.edge = ((t : ℝ) - s) * W.weight d.edge ∧
      subdivideEquiv hV (edgePoint d' τ) =
        edgePoint d ⟨(1 - (τ : ℝ)) * s + τ * t,
          add_nonneg
            (mul_nonneg (unitInterval.one_sub_nonneg τ) (unitInterval.nonneg s))
            (mul_nonneg (unitInterval.nonneg τ) (unitInterval.nonneg t)),
          (add_le_add
            (mul_le_of_le_one_right (unitInterval.one_sub_nonneg τ) (unitInterval.le_one s))
            (mul_le_of_le_one_right (unitInterval.nonneg τ) (unitInterval.le_one t))).trans_eq
            (sub_add_cancel 1 (τ : ℝ))⟩ := by
  have hsp := subDart_spec d'
  refine ⟨subDartOrigin d', subDartStart d', subDartEnd d', hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2,
    subDart_weight d', ?_⟩
  change subdivideToMetric hV (edgePoint d' τ) = _
  simp only [subdivideToMetric, lift_edgePoint, interpUnit]

/-! ### Per-subdivided-edge affine distance from a point -/


/-- Choose a canonical dart orienting an undirected edge `e : G.edgeSet`. -/
noncomputable def edgeDartOfSym2 {G : SimpleGraph V} (e : G.edgeSet) : G.Dart :=
  ⟨Quot.out e.1, by
    have hmem : Quot.mk (Sym2.Rel V) (Quot.out e.1) ∈ G.edgeSet := by
      rw [Quot.out_eq]
      exact e.2
    exact G.mem_edgeSet.mp hmem⟩

/-- The chosen canonical dart `edgeDartOfSym2 e` lies on edge `e`. -/
@[simp]
theorem edgeDartOfSym2_edge {G : SimpleGraph V} (e : G.edgeSet) :
    (edgeDartOfSym2 e).edge = e.1 :=
  Quot.out_eq e.1

/-- If `c` is strictly interior to `[0, 1]` and `edgePoint (edgeDartOfSym2 e) u` agrees with
`edgePoint (edgeDartOfSym2 e') c`, then `e = e'` and `u = c`. -/
theorem edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo {e e' : W.graph.edgeSet}
    {u c : unitInterval} (hc0 : (0 : ℝ) < c) (hc1 : (c : ℝ) < 1) :
    edgePoint (edgeDartOfSym2 e) u = (edgePoint (edgeDartOfSym2 e') c : MetricGraph W) ↔
      e = e' ∧ u = c := by
  constructor
  · intro heq
    rcases edgePoint_eq_edgePoint_iff.mp heq with
      ⟨_, ⟨hc0', _⟩ | ⟨hc1', _⟩⟩ | ⟨_, ⟨hc0', _⟩ | ⟨hc1', _⟩⟩ |
      ⟨_, _, _, _, ⟨hd, hu⟩ | ⟨hsym, _⟩⟩
    · exact absurd (congrArg Subtype.val hc0') hc0.ne'
    · exact absurd (congrArg Subtype.val hc1') hc1.ne
    · exact absurd (congrArg Subtype.val hc0') hc0.ne'
    · exact absurd (congrArg Subtype.val hc1') hc1.ne
    · have h' := congrArg Dart.edge hd
      rw [edgeDartOfSym2_edge, edgeDartOfSym2_edge] at h'
      exact ⟨Subtype.ext h', hu⟩
    · have h' := congrArg Dart.edge hsym
      rw [edgeDartOfSym2_edge, Dart.edge_symm, edgeDartOfSym2_edge] at h'
      have he : e = e' := Subtype.ext h'
      subst he
      exact absurd hsym.symm (edgeDartOfSym2 e).symm_ne
  · rintro ⟨rfl, rfl⟩
    rfl

open Classical in
/-- At most three breakpoints along dart `d` where `t ↦ dist p (edgePoint d t)` changes slope. -/
noncomputable def dartBreakpoints [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : Finset (MetricGraph W) :=
  let a := dist p (vertex d.fst)
  let b := dist p (vertex d.snd)
  let w := W.weight d.edge
  if h : ∃ s₀ : unitInterval, edgePoint d s₀ = p then
    let s₀ := Classical.choose h
    let c₁ := min ((s₀ : ℝ) * w) (b + w)
    let c₂ := min (-(s₀ : ℝ) * w) a
    let t₂ := Set.projIcc 0 1 zero_le_one ((c₁ - a) / (2 * w))
    let t₃ := Set.projIcc 0 1 zero_le_one ((b + w - c₂) / (2 * w))
    {edgePoint d s₀, edgePoint d t₂, edgePoint d t₃}
  else
    {edgePoint d (Set.projIcc 0 1 zero_le_one ((b + w - a) / (2 * w)))}

theorem dartBreakpoints_card_le [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : (dartBreakpoints W p d).card ≤ 3 := by
  classical
  unfold dartBreakpoints
  split_ifs
  · exact (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
  · simp

theorem dartBreakpoints_symm [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (d : W.graph.Dart) : dartBreakpoints W p d.symm = dartBreakpoints W p d := by
  classical
  have hw := W.dart_weight_pos d
  have hboth : (∃ s₀ : unitInterval, edgePoint d.symm s₀ = p) ↔
      (∃ s₀ : unitInterval, edgePoint d s₀ = p) :=
    ⟨fun ⟨s₀, hs⟩ => ⟨unitInterval.symm s₀, by simpa only [edgePoint_symm'] using hs⟩,
     fun ⟨s₀, hs⟩ => ⟨unitInterval.symm s₀, (edgePoint_symm d s₀).trans hs⟩⟩
  by_cases h : ∃ s₀ : unitInterval, edgePoint d s₀ = p
  · have hs : ∃ s₀ : unitInterval, edgePoint d.symm s₀ = p := hboth.mpr h
    simp only [dartBreakpoints, hs, h, ↓reduceDIte]
    set s := Classical.choose h
    set s' := Classical.choose hs
    have hs_eq : s' = unitInterval.symm s := by
      apply edgePoint_injective d.symm
      rw [Classical.choose_spec hs, edgePoint_symm, Classical.choose_spec h]
    let a := dist p (vertex d.fst)
    let b := dist p (vertex d.snd)
    let w := W.weight d.edge
    have hsym_t2 : Set.projIcc 0 1 zero_le_one ((min ((s' : ℝ) * W.weight d.symm.edge)
          (dist p (vertex d.symm.snd) + W.weight d.symm.edge) - dist p (vertex d.symm.fst)) /
          (2 * W.weight d.symm.edge)) =
        unitInterval.symm
          (Set.projIcc 0 1 zero_le_one ((b + w - min (-(s : ℝ) * w) a) / (2 * w))) := by
      rw [unitInterval.symm_projIcc]
      congr 1
      have hsnd : d.symm.snd = d.fst := rfl
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm, hs_eq, unitInterval.coe_symm_eq]
      change (min ((1 - (s : ℝ)) * w) (a + w) - b) / (2 * w) =
        1 - (b + w - min (-(s : ℝ) * w) a) / (2 * w)
      have hmin_eq : min ((1 - (s : ℝ)) * w) (a + w) - b =
          w - b + min (-(s : ℝ) * w) a := by
        have : min ((1 - (s : ℝ)) * w) (a + w) = w + min (-(s : ℝ) * w) a := by
          rw [← min_add_add_left]; congr 1 <;> ring
        linarith
      rw [hmin_eq]
      field_simp [show w ≠ 0 from hw.ne']
      ring
    have hsym_t3 : Set.projIcc 0 1 zero_le_one
        ((dist p (vertex d.symm.snd) + W.weight d.symm.edge -
          min (-(s' : ℝ) * W.weight d.symm.edge) (dist p (vertex d.symm.fst))) /
          (2 * W.weight d.symm.edge)) =
        unitInterval.symm
          (Set.projIcc 0 1 zero_le_one ((min ((s : ℝ) * w) (b + w) - a) / (2 * w))) := by
      rw [unitInterval.symm_projIcc]
      congr 1
      have hsnd : d.symm.snd = d.fst := rfl
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm, hs_eq, unitInterval.coe_symm_eq]
      change (a + w - min (-(1 - (s : ℝ)) * w) b) / (2 * w) =
        1 - (min ((s : ℝ) * w) (b + w) - a) / (2 * w)
      have hmin_eq : min (-(1 - (s : ℝ)) * w) b = min ((s : ℝ) * w) (b + w) - w := by
        rw [← min_sub_sub_right]; congr 1 <;> ring
      rw [hmin_eq]
      field_simp [show w ≠ 0 from hw.ne']
      ring
    have hsym_s : edgePoint d.symm s' = edgePoint d s := by rw [hs_eq, edgePoint_symm]
    rw [hsym_s, hsym_t2, edgePoint_symm, hsym_t3, edgePoint_symm]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hns : ¬ ∃ s₀ : unitInterval, edgePoint d.symm s₀ = p := by
      rwa [hboth]
    simp only [dartBreakpoints, h, hns, ↓reduceDIte]
    have hsym_eq : Set.projIcc 0 1 zero_le_one
        ((dist p (vertex d.symm.snd) + W.weight d.symm.edge -
          dist p (vertex d.symm.fst)) / (2 * W.weight d.symm.edge)) =
        unitInterval.symm (Set.projIcc 0 1 zero_le_one ((dist p (vertex d.snd) + W.weight d.edge -
          dist p (vertex d.fst)) / (2 * W.weight d.edge))) := by
      rw [unitInterval.symm_projIcc]
      congr 1
      have hsnd : d.symm.snd = d.fst := rfl
      simp only [Dart.fst_symm, hsnd, Dart.edge_symm]
      field_simp [hw.ne']
      ring
    rw [hsym_eq, edgePoint_symm]

open Classical in
/-- Finite set of all original vertices together with at most three breakpoints per edge for
`p : MetricGraph W`. -/
noncomputable def pointBreakpoints [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) : Finset (MetricGraph W) :=
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  (Finset.univ.image vertex) ∪
    (Finset.univ.biUnion fun e : W.graph.edgeSet => dartBreakpoints W p (edgeDartOfSym2 e))

theorem vertex_mem_pointBreakpoints [Finite V] (W : WeightedGraph V) (p : MetricGraph W)
    (v : V) : vertex v ∈ pointBreakpoints W p := by
  classical
  simp only [pointBreakpoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨v, rfl⟩

theorem dartBreakpoints_subset_pointBreakpoints [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) (d : W.graph.Dart) :
    dartBreakpoints W p d ⊆ pointBreakpoints W p := by
  classical
  intro q hq
  simp only [pointBreakpoints, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine Or.inr ⟨⟨d.edge, d.edge_mem⟩, ?_⟩
  rcases (dart_edge_eq_iff (edgeDartOfSym2 ⟨d.edge, d.edge_mem⟩) d).mp
      (edgeDartOfSym2_edge _) with he | he
  · rwa [he]
  · rwa [he, dartBreakpoints_symm]

open Classical in
theorem pointBreakpoints_sdiff_card_le [Finite V] (W : WeightedGraph V) (p : MetricGraph W) :
    let : Fintype V := Fintype.ofFinite V
    (pointBreakpoints W p \ Finset.univ.image vertex).card ≤
      3 * Nat.card W.graph.edgeSet := by
  intro _
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  refine (Finset.card_le_card (t := Finset.univ.biUnion
      fun e : W.graph.edgeSet => dartBreakpoints W p (edgeDartOfSym2 e)) ?_).trans ?_
  · intro q hq
    simp only [Finset.mem_sdiff, pointBreakpoints, Finset.mem_union] at hq
    exact hq.1.resolve_left hq.2
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ e : W.graph.edgeSet, (dartBreakpoints W p (edgeDartOfSym2 e)).card
        ≤ ∑ _ : W.graph.edgeSet, 3 :=
          Finset.sum_le_sum fun e _ => dartBreakpoints_card_le W p _
      _ = 3 * Nat.card W.graph.edgeSet := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Fintype.card_eq_nat_card]

private theorem dist_point_edgePoint_piecewise_affine [Finite V] (W : WeightedGraph V)
    (p : MetricGraph W) (d : W.graph.Dart) {s t : unitInterval} (_hst : (s : ℝ) < t)
    (hno : ∀ q ∈ dartBreakpoints W p d, ∀ r : unitInterval,
      (s : ℝ) < r → (r : ℝ) < t → edgePoint d r ≠ q) :
    ∃ α β : ℝ, ∀ r : unitInterval, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
      dist p (edgePoint d r) = α + β * r := by
  classical
  have hw := W.dart_weight_pos d
  let a := dist p (vertex d.fst)
  let b := dist p (vertex d.snd)
  let w := W.weight d.edge
  have hab_diff : |a - b| ≤ w := by
    have hwd : dist (vertex d.fst : MetricGraph W) (vertex d.snd) ≤ w := by
      rw [← edgePoint_zero d, ← edgePoint_one d]
      refine (dist_edgePoint_self_le d 0 1).trans_eq ?_
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl,
        show ((1 : unitInterval) : ℝ) = 1 from rfl, zero_sub, abs_neg, abs_one, mul_one]
    have h1 := dist_triangle p (vertex d.snd) (vertex d.fst)
    have h2 := dist_triangle p (vertex d.fst) (vertex d.snd)
    rw [dist_comm (vertex d.snd) (vertex d.fst)] at h1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have avoids : ∀ u : unitInterval, edgePoint d u ∈ dartBreakpoints W p d →
      (u : ℝ) ≤ s ∨ (t : ℝ) ≤ u := by
    intro u hu
    by_contra hnot
    push Not at hnot
    exact hno (edgePoint d u) hu u hnot.1 hnot.2 rfl
  by_cases hp : ∃ s₀ : unitInterval, edgePoint d s₀ = p
  · let s₀ := Classical.choose hp
    have hs₀ : edgePoint d s₀ = p := Classical.choose_spec hp
    have hp_eq : p = edgePoint d s₀ := hs₀.symm
    let c₁ := min ((s₀ : ℝ) * w) (b + w)
    let c₂ := min (-(s₀ : ℝ) * w) a
    let t₂ := Set.projIcc 0 1 zero_le_one ((c₁ - a) / (2 * w))
    let t₃ := Set.projIcc 0 1 zero_le_one ((b + w - c₂) / (2 * w))
    have ht₂_mem : edgePoint d t₂ ∈ dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]
      split_ifs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl rfl)
    have ht₃_mem : edgePoint d t₃ ∈ dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]
      split_ifs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr rfl)
    have hs₀_mem : edgePoint d s₀ ∈ dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]
      split_ifs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl rfl
    have ha_le : a ≤ (s₀ : ℝ) * w := by
      rw [show a = dist p (vertex d.fst) from rfl, hp_eq, ← edgePoint_zero d, dist_comm]
      refine (dist_edgePoint_self_le d 0 s₀).trans_eq ?_
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_sub, abs_neg, abs_of_nonneg s₀.2.1,
        mul_comm]
    have hb_le : b ≤ (1 - (s₀ : ℝ)) * w := by
      rw [show b = dist p (vertex d.snd) from rfl, hp_eq, ← edgePoint_one d, dist_comm]
      refine (dist_edgePoint_self_le d 1 s₀).trans_eq ?_
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl,
        abs_of_nonneg (unitInterval.one_sub_nonneg s₀), mul_comm]
    have ht₂_val : (t₂ : ℝ) = (c₁ - a) / (2 * w) := by
      refine congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨?_, ?_⟩)
      · exact div_nonneg (sub_nonneg.mpr (le_min ha_le (by linarith [abs_le.mp hab_diff])))
          (by linarith)
      · rw [div_le_one (by linarith)]
        have : c₁ ≤ w := (min_le_left _ _).trans (mul_le_of_le_one_left hw.le s₀.2.2)
        linarith [dist_nonneg (x := p) (y := vertex d.fst)]
    have ht₃_val : (t₃ : ℝ) = (b + w - c₂) / (2 * w) := by
      refine congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨?_, ?_⟩)
      · exact div_nonneg (by have : c₂ ≤ a := min_le_right _ _; linarith [abs_le.mp hab_diff])
          (by linarith)
      · rw [div_le_one (by linarith)]
        rcases min_cases (-(s₀ : ℝ) * w) a with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
          change b + w - min (-(s₀ : ℝ) * w) a ≤ 2 * w <;>
          rw [hm] <;> linarith [abs_le.mp hab_diff]
    have hformula : ∀ r : unitInterval,
        dist p (edgePoint d r) =
          min (|(s₀ : ℝ) - r| * w) (min (a + (r : ℝ) * w) (b + (1 - (r : ℝ)) * w)) := by
      intro r
      dsimp only [a, b, w]
      rw [hp_eq]
      exact dist_edgePoint_eq_min_same d s₀ r
    have hmin_le : ∀ r : unitInterval, (r : ℝ) ≤ s₀ →
        dist p (edgePoint d r) = min (c₁ - (r : ℝ) * w) (a + (r : ℝ) * w) := by
      intro r hr
      rw [hformula r, abs_of_nonneg (sub_nonneg.mpr hr)]
      have hc1eq : c₁ - (r : ℝ) * w = min (((s₀ : ℝ) - r) * w) (b + (1 - (r : ℝ)) * w) := by
        dsimp only [c₁]
        rw [← min_sub_sub_right]
        congr 1 <;> ring
      rw [hc1eq, min_comm (a + (r : ℝ) * w), ← min_assoc]
    have hmin_ge : ∀ r : unitInterval, (s₀ : ℝ) ≤ r →
        dist p (edgePoint d r) = min (c₂ + (r : ℝ) * w) (b + (1 - (r : ℝ)) * w) := by
      intro r hr
      rw [hformula r, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hr)]
      have hc2eq : c₂ + (r : ℝ) * w = min (((r : ℝ) - s₀) * w) (a + (r : ℝ) * w) := by
        dsimp only [c₂]
        rw [← min_add_add_right]
        congr 1; ring
      rw [hc2eq, ← min_assoc]
    rcases avoids s₀ hs₀_mem with hs₀s | hts₀
    · rcases avoids t₃ ht₃_mem with ht3s | htt3
      · refine ⟨b + w, -w, fun r hrs hrt => ?_⟩
        have hrt3 : (t₃ : ℝ) ≤ r := ht3s.trans hrs
        rw [ht₃_val, div_le_iff₀ (by linarith)] at hrt3
        rw [hmin_ge r (hs₀s.trans hrs), min_eq_right (by linarith)]
        ring
      · refine ⟨c₂, w, fun r hrs hrt => ?_⟩
        have hrt3 : (r : ℝ) ≤ t₃ := hrt.trans htt3
        rw [ht₃_val, le_div_iff₀ (by linarith)] at hrt3
        rw [hmin_ge r (hs₀s.trans hrs), min_eq_left (by linarith)]
        ring
    · rcases avoids t₂ ht₂_mem with ht2s | htt2
      · refine ⟨c₁, -w, fun r hrs hrt => ?_⟩
        have hrt2 : (t₂ : ℝ) ≤ r := ht2s.trans hrs
        rw [ht₂_val, div_le_iff₀ (by linarith)] at hrt2
        rw [hmin_le r (hrt.trans hts₀), min_eq_left (by linarith)]
        ring
      · refine ⟨a, w, fun r hrs hrt => ?_⟩
        have hrt2 : (r : ℝ) ≤ t₂ := hrt.trans htt2
        rw [ht₂_val, le_div_iff₀ (by linarith)] at hrt2
        rw [hmin_le r (hrt.trans hts₀), min_eq_right (by linarith)]
        ring
  · have hformula : ∀ r : unitInterval,
        dist p (edgePoint d r) = min (a + (r : ℝ) * w) (b + (1 - (r : ℝ)) * w) := by
      intro r
      induction p using ind_simple with
      | vertex u =>
        rw [dist_vertex_edgePoint]
        dsimp only [a, b, w]
        rw [dist_vertex, dist_vertex]
      | edgePoint d₀ s₀ =>
        have hne : d₀.edge ≠ d.edge := by
          intro he
          rcases (dart_edge_eq_iff d₀ d).mp he with rfl | hsym
          · exact hp ⟨s₀, rfl⟩
          · exact hp ⟨unitInterval.symm s₀, by rw [hsym, edgePoint_symm']⟩
        exact dist_edgePoint_eq_min_of_edge_ne hne s₀ r
    let t_mid := Set.projIcc 0 1 zero_le_one ((b + w - a) / (2 * w))
    have h0 : 0 ≤ (b + w - a) / (2 * w) :=
      div_nonneg (by linarith [abs_le.mp hab_diff]) (by linarith)
    have h1 : (b + w - a) / (2 * w) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith [abs_le.mp hab_diff]
    have htm_val : (t_mid : ℝ) = (b + w - a) / (2 * w) :=
      congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨h0, h1⟩)
    have htm_mem : edgePoint d t_mid ∈ dartBreakpoints W p d := by
      dsimp only [dartBreakpoints]
      split_ifs
      exact Finset.mem_singleton_self _
    rcases avoids t_mid htm_mem with hle | hle
    · refine ⟨b + w, -w, fun r hrs hrt => ?_⟩
      rw [hformula r, min_eq_right]
      · ring
      · have hrtm : (t_mid : ℝ) ≤ r := hle.trans hrs
        rw [htm_val, div_le_iff₀ (by linarith)] at hrtm
        linarith
    · refine ⟨a, w, fun r hrs hrt => ?_⟩
      rw [hformula r, min_eq_left]
      · ring
      · have hrtm : (r : ℝ) ≤ t_mid := hrt.trans hle
        rw [htm_val, le_div_iff₀ (by linarith)] at hrtm
        linarith

/-- On any subdivision containing `pointBreakpoints W p`, the distance from `p` is affine
along every subdivided edge. -/
theorem dist_subdivide_edgePoint_affine [Finite V] {p : MetricGraph W}
    {B : Finset (MetricGraph W)} (hV : ∀ v : V, vertex v ∈ B) (hBp : pointBreakpoints W p ⊆ B)
    (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    dist p (subdivideEquiv hV (edgePoint d' τ)) =
      (1 - (τ : ℝ)) * dist p (subdivideEquiv hV (vertex d'.fst)) +
        (τ : ℝ) * dist p (subdivideEquiv hV (vertex d'.snd)) := by
  obtain ⟨d, s, t, hst, hs, ht, hno, _, heq⟩ := subdivideEquiv_edgePoint hV d' τ
  have hsub := dartBreakpoints_subset_pointBreakpoints W p d |>.trans hBp
  obtain ⟨α, β, haff⟩ := dist_point_edgePoint_piecewise_affine W p d hst
    (fun q hq r hsr hrt => fun hreq => hno r hsr hrt (hreq ▸ hsub hq))
  let u : unitInterval := ⟨(1 - (τ : ℝ)) * s + τ * t,
    add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) s.2.1) (mul_nonneg τ.2.1 t.2.1),
    by nlinarith [τ.2.1, τ.2.2, s.2.2, t.2.2]⟩
  have hu_mem : (s : ℝ) ≤ u ∧ (u : ℝ) ≤ t := by
    constructor <;> dsimp only [u] <;> nlinarith [τ.2.1, τ.2.2, hst]
  have h1 := haff s le_rfl hst.le
  have h2 := haff t hst.le le_rfl
  have h3 := haff u hu_mem.1 hu_mem.2
  rw [heq, subdivideEquiv_vertex, subdivideEquiv_vertex, ← hs, ← ht]
  have h1s : dist p (edgePoint d s) = α + β * s := h1
  have h2t : dist p (edgePoint d t) = α + β * t := h2
  have h3u : dist p (edgePoint d ⟨(1 - (τ : ℝ)) * s + τ * t,
      add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) s.2.1) (mul_nonneg τ.2.1 t.2.1),
      by nlinarith [τ.2.1, τ.2.2, s.2.2, t.2.2]⟩) =
      α + β * u := h3
  rw [h1s, h2t, h3u]
  dsimp only [u]
  ring

theorem dist_subdivide_edgePoint_affine' [Finite V] {B : Finset (MetricGraph W)}
    (hV : ∀ v : V, vertex v ∈ B) {p' : MetricGraph (subdivide W B hV)}
    (hBp : pointBreakpoints W (subdivideEquiv hV p') ⊆ B)
    (d' : (subdivide W B hV).graph.Dart) (τ : unitInterval) :
    dist p' (edgePoint d' τ) =
      (1 - (τ : ℝ)) * dist p' (vertex d'.fst) +
        (τ : ℝ) * dist p' (vertex d'.snd) := by
  have hiso := (subdivideEquiv hV).isometry
  rw [← hiso.dist_eq, ← hiso.dist_eq p' (vertex d'.fst), ← hiso.dist_eq p' (vertex d'.snd)]
  exact dist_subdivide_edgePoint_affine hV hBp d' τ

end MetricGraph

end SimpleGraph
