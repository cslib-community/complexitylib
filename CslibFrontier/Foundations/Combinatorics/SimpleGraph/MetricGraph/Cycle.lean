/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Cycle.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

/-!
# Cycle metric graphs and shortest cycles

Any weighted finite simple graph `W` that is not acyclic contains a cycle minimizing total edge
weight. This module establishes the existence of shortest cycles `IsShortestCycle`, defines the
arc-length parameterization `circleMap` of any cycle into `MetricGraph W`, proves that
`circleMap` of a shortest cycle is an isometric embedding of the circle of circumference `L`
(with metric `circleDist L`), and shows `circleMap` is surjective onto `MetricGraph W` whenever
`W.graph` is isomorphic to `cycleGraph (n + 3)`.

## Main definitions

* `SimpleGraph.MetricGraph.IsShortestCycle`: predicate that a cycle minimizes `walkLength W.weight`
  among all cycles in `W.graph`.
* `SimpleGraph.MetricGraph.circleDist`: geodesic distance `(s, t) ↦ min (fract ((t - s)/L) * L) ...`
  on a circle of circumference `L > 0`.
* `SimpleGraph.MetricGraph.circleMap`: arc-length periodic parameterization `ℝ → MetricGraph W` of a
  cycle `c`.

## Main results

* `SimpleGraph.MetricGraph.exists_isShortestCycle`: every non-acyclic finite weighted graph has a
  shortest cycle.
* `SimpleGraph.MetricGraph.circleMap_dist_eq_circleDist`,
  `SimpleGraph.MetricGraph.circleMap_dist_eq_of_le`: `circleMap` of a shortest cycle preserves
  `circleDist L` globally and `|s - t|` on arcs of length `≤ L / 2`.
* `SimpleGraph.MetricGraph.circleMap_surjective_of_cycleGraph`: every cycle in a graph isomorphic
  to `cycleGraph (n + 3)` parameterizes all of `MetricGraph W`.
* `SimpleGraph.MetricGraph.circleMap_local_dichotomy`: every parameter `s` lies either strictly
  inside a cycle dart or at a cycle vertex whose two incident cycle edges are distinct.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u} {W : WeightedGraph V}

/-! ### Walk lengths and shortest cycles -/

section ShortestCycle

private lemma sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α] (f : α → ℝ) (l : List α)
    (hl : l.Nodup) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert
      (by simpa only [List.mem_toFinset] using hl.1), ih hl.2]

private lemma walkLength_perm_eq {G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u₁ v₁ u₂ v₂ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂} (hp : p₁.edges.Perm p₂.edges) :
    walkLength w p₁ = walkLength w p₂ :=
  (hp.map w).sum_eq

private lemma weight_le_walkLength_of_mem_edges : ∀ {u v : V} (p : W.graph.Walk u v)
    {e : Sym2 V}, e ∈ p.edges → W.weight e ≤ walkLength W.weight p
  | _, _, .cons hadj q, e, he => by
    rw [Walk.edges_cons, List.mem_cons] at he
    rw [walkLength_cons]
    rcases he with rfl | he'
    · linarith [walkLength_nonneg W.weight W.weight_nonneg q]
    · have hnn : 0 ≤ W.weight s(_, _) := (W.dart_weight_pos ⟨(_, _), hadj⟩).le
      linarith [weight_le_walkLength_of_mem_edges q he']

theorem walkLength_pos_of_not_nil {u v : V} {p : W.graph.Walk u v} (hp : ¬ p.Nil) :
    0 < walkLength W.weight p := by
  cases p with
  | nil => exact absurd .nil hp
  | cons hadj q =>
    rw [walkLength_cons]
    have h1 : 0 < W.weight s(_, _) := W.dart_weight_pos ⟨(_, _), hadj⟩
    have h2 : 0 ≤ walkLength W.weight q := walkLength_nonneg W.weight W.weight_nonneg q
    linarith

theorem walkLength_take_add_drop {u v : V} (p : W.graph.Walk u v) (k : ℕ) :
    walkLength W.weight (p.take k) + walkLength W.weight (p.drop k) = walkLength W.weight p := by
  dsimp only [walkLength]
  rw [Walk.edges_take, Walk.edges_drop, ← List.sum_append, ← List.map_append, List.take_append_drop]

/-- A cycle `c` in `W.graph` is a shortest cycle if it minimizes `walkLength W.weight` among all
cycles in `W.graph`. -/
@[expose] def IsShortestCycle (W : WeightedGraph V) {v₀ : V} (c : W.graph.Walk v₀ v₀) : Prop :=
  c.IsCycle ∧ ∀ {u : V} (c' : W.graph.Walk u u), c'.IsCycle →
    walkLength W.weight c ≤ walkLength W.weight c'

theorem exists_isShortestCycle [Finite V] (hc : ¬ W.graph.IsAcyclic) :
    ∃ (v₀ : V) (c : W.graph.Walk v₀ v₀), IsShortestCycle W c := by
  classical
  obtain ⟨_⟩ := nonempty_fintype V
  let S : Set ℝ :=
    { r | ∃ (u : V) (c : W.graph.Walk u u), c.IsCycle ∧ walkLength W.weight c = r }
  have hsub : S ⊆ Set.range (fun F : Finset (Sym2 V) => ∑ e ∈ F, W.weight e) := by
    rintro r ⟨u, c, hc_cyc, rfl⟩
    refine ⟨c.edges.toFinset, ?_⟩
    exact (sum_map_eq_sum_toFinset W.weight c.edges hc_cyc.isTrail.edges_nodup).symm
  have hfin : Set.Finite S := (Set.finite_range _).subset hsub
  obtain ⟨v₁, c₁, hc₁⟩ := not_isAcyclic_iff_exists_isCycle.mp hc
  have hne : S.Nonempty := ⟨walkLength W.weight c₁, v₁, c₁, hc₁, rfl⟩
  obtain ⟨rmin, hrmin_mem, hrmin_le⟩ :=
    hfin.toFinset.exists_min_image id (hfin.toFinset_nonempty.mpr hne)
  obtain ⟨v₀, c, hc_cyc, hc_len⟩ := hfin.mem_toFinset.mp hrmin_mem
  refine ⟨v₀, c, hc_cyc, fun {u} c' hc' => ?_⟩
  rw [hc_len]
  exact hrmin_le (walkLength W.weight c') (hfin.mem_toFinset.mpr ⟨u, c', hc', rfl⟩)

end ShortestCycle

/-! ### Geodesic distance on the circle of circumference `L` -/

section CircleDist

/-- Shortest arc-length distance between `s` and `t` on a circle of circumference `L > 0`. -/
@[expose] noncomputable def circleDist (L s t : ℝ) : ℝ :=
  min (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L)

theorem circleDist_nonneg {L : ℝ} (hL : 0 < L) (s t : ℝ) : 0 ≤ circleDist L s t :=
  le_min (mul_nonneg (Int.fract_nonneg _) hL.le)
    (mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le) hL.le)

theorem circleDist_le_half {L : ℝ} (_hL : 0 < L) (s t : ℝ) : circleDist L s t ≤ L / 2 := by
  dsimp only [circleDist]
  have h1 := min_le_left (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L)
  have h2 : min (Int.fract ((t - s) / L) * L) ((1 - Int.fract ((t - s) / L)) * L) ≤
      L - Int.fract ((t - s) / L) * L :=
    (min_le_right _ _).trans_eq (by ring)
  linarith

@[simp]
theorem circleDist_self {L : ℝ} (hL : 0 < L) (s : ℝ) : circleDist L s s = 0 := by
  simp [circleDist, hL.le]

theorem circleDist_add_int_right {L : ℝ} (hL : 0 < L) (s t : ℝ) (k : ℤ) :
    circleDist L s (t + (k : ℝ) * L) = circleDist L s t := by
  have hdiv : ((t + (k : ℝ) * L) - s) / L = (t - s) / L + (k : ℝ) := by
    rw [add_sub_right_comm, add_div, mul_div_cancel_right₀ _ hL.ne']
  simp only [circleDist, hdiv, Int.fract_add_intCast]

theorem circleDist_symm {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    circleDist L s t = circleDist L t s := by
  by_cases hf : Int.fract ((t - s) / L) = 0
  · obtain ⟨k, hk⟩ := Int.fract_eq_zero_iff.mp hf
    have hts : (s - t) / L = ((-k : ℤ) : ℝ) := by
      rw [← neg_sub t s, neg_div, ← hk, Int.cast_neg]
    have hf' : Int.fract ((s - t) / L) = 0 := hts ▸ Int.fract_intCast (-k)
    simp only [circleDist, hf, hf', zero_mul, sub_zero, one_mul, min_eq_left hL.le]
  · have hneg : (s - t) / L = -((t - s) / L) := by rw [← neg_sub t s, neg_div]
    simp only [circleDist, hneg, Int.fract_neg hf, sub_sub_cancel]
    exact min_comm _ _

theorem circleDist_add_int_left {L : ℝ} (hL : 0 < L) (s t : ℝ) (k : ℤ) :
    circleDist L (s + (k : ℝ) * L) t = circleDist L s t := by
  rw [circleDist_symm hL, circleDist_add_int_right hL, circleDist_symm hL]

theorem circleDist_eq_abs_of_abs_le {L : ℝ} (hL : 0 < L) {s t : ℝ} (hst : |s - t| ≤ L / 2) :
    circleDist L s t = |s - t| := by
  have hab : |t - s| ≤ L / 2 := abs_sub_comm s t ▸ hst
  rcases le_or_gt 0 (t - s) with h0 | h0
  · have hu0 : 0 ≤ (t - s) / L := div_nonneg h0 hL.le
    have hu1 : (t - s) / L < 1 := by
      rw [div_lt_one hL]
      linarith [abs_of_nonneg h0]
    have hfl : ⌊(t - s) / L⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simpa using hu0, by simpa using hu1⟩
    have hf : Int.fract ((t - s) / L) = (t - s) / L := by
      rw [Int.fract, hfl, Int.cast_zero, sub_zero]
    rw [circleDist, hf, div_mul_cancel₀ _ hL.ne', one_sub_mul, div_mul_cancel₀ _ hL.ne']
    rw [abs_sub_comm, abs_of_nonneg h0]
    exact min_eq_left (by linarith [abs_of_nonneg h0])
  · have hu_lo : (-1 : ℝ) ≤ (t - s) / L := by
      rw [le_div_iff₀ hL]
      linarith [neg_le_abs (t - s)]
    have hu_hi : (t - s) / L < 0 := div_neg_of_neg_of_pos h0 hL
    have hfl : ⌊(t - s) / L⌋ = -1 :=
      Int.floor_eq_iff.mpr ⟨by simpa using hu_lo, by simpa using hu_hi⟩
    have hf : Int.fract ((t - s) / L) = (t - s) / L + 1 := by
      rw [Int.fract, hfl, Int.cast_neg, Int.cast_one]
      ring
    rw [circleDist, hf, add_mul, one_mul, div_mul_cancel₀ _ hL.ne', sub_add_cancel_right]
    rw [neg_mul, div_mul_cancel₀ _ hL.ne']
    have h0' : 0 < s - t := by linarith
    rw [abs_of_pos h0', min_eq_right (by linarith [abs_of_neg h0])]
    ring

theorem circleDist_le_abs {L : ℝ} (hL : 0 < L) (s t : ℝ) : circleDist L s t ≤ |s - t| := by
  rcases le_or_gt |s - t| (L / 2) with h | h
  · exact (circleDist_eq_abs_of_abs_le hL h).le
  · exact (circleDist_le_half hL s t).trans h.le

theorem exists_eq_add_int_mul_dist {L : ℝ} (hL : 0 < L) (s t : ℝ) :
    ∃ k : ℤ, |s - (t + (k : ℝ) * L)| = circleDist L s t := by
  let n : ℤ := ⌊(t - s) / L⌋
  have hfract : Int.fract ((t - s) / L) * L = t - (n : ℝ) * L - s := by
    dsimp only [n]
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  rcases le_or_gt (Int.fract ((t - s) / L)) (1 / 2) with h | h
  · refine ⟨-n, ?_⟩
    have hcd : circleDist L s t = Int.fract ((t - s) / L) * L :=
      min_eq_left (by nlinarith)
    have heq : t + ((-n : ℤ) : ℝ) * L - s = Int.fract ((t - s) / L) * L := by
      rw [hfract, Int.cast_neg]
      ring
    rw [abs_sub_comm, heq, abs_of_nonneg (mul_nonneg (Int.fract_nonneg _) hL.le), hcd]
  · refine ⟨-(n + 1), ?_⟩
    have hcd : circleDist L s t = (1 - Int.fract ((t - s) / L)) * L :=
      min_eq_right (by nlinarith)
    have heq : s - (t + ((-(n + 1) : ℤ) : ℝ) * L) = (1 - Int.fract ((t - s) / L)) * L := by
      rw [one_sub_mul, hfract, Int.cast_neg, Int.cast_add, Int.cast_one]
      ring
    rw [heq, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le) hL.le), hcd]

theorem circleDist_triangle {L : ℝ} (hL : 0 < L) (r s t : ℝ) :
    circleDist L r t ≤ circleDist L r s + circleDist L s t := by
  obtain ⟨k₁, hk₁⟩ := exists_eq_add_int_mul_dist hL r s
  obtain ⟨k₂, hk₂⟩ := exists_eq_add_int_mul_dist hL (s + (k₁ : ℝ) * L) t
  have hr : circleDist L r t = circleDist L r (t + (k₂ : ℝ) * L) :=
    (circleDist_add_int_right hL r t k₂).symm
  have hs : circleDist L s t = circleDist L (s + (k₁ : ℝ) * L) t :=
    (circleDist_add_int_left hL s t k₁).symm
  rw [hr, hs, ← hk₁, ← hk₂]
  exact (circleDist_le_abs hL r (t + (k₂ : ℝ) * L)).trans (abs_sub_le _ (s + (k₁ : ℝ) * L) _)

end CircleDist

/-! ### Arc-length parameterization of walks and cycles -/

section CircleMap

/-- Arc-length parameterization of a walk `p : W.graph.Walk u v` into `MetricGraph W`, clamped at
`vertex u` for `s ≤ 0` and at `vertex v` for `walkLength W.weight p ≤ s`. -/
noncomputable def walkPoint : ∀ {u v : V}, W.graph.Walk u v → ℝ → MetricGraph W
  | u, _, .nil, _ => vertex u
  | u, _, .cons (v := b) hadj q, s =>
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    let w := W.weight d.edge
    if s ≤ w then
      let t : unitInterval :=
        ⟨max 0 (min s w) / w,
          div_nonneg (le_max_left 0 _) (W.dart_weight_pos d).le,
          (div_le_one (W.dart_weight_pos d)).mpr
            (max_le (W.dart_weight_pos d).le (min_le_right _ _))⟩
      edgePoint d t
    else
      walkPoint q (s - w)

private lemma walkPoint_cons_of_le {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩)
    {s : ℝ} (hs0 : 0 ≤ s) (hsw : s ≤ W.weight d.edge)
    (h0 : 0 ≤ s / W.weight d.edge) (h1 : s / W.weight d.edge ≤ 1) :
    walkPoint (.cons hadj q) s = edgePoint d ⟨s / W.weight d.edge, h0, h1⟩ := by
  subst hd
  have hsw' : s ≤ W.weight s(u, b) := hsw
  dsimp only [walkPoint]
  split_ifs
  congr 1
  ext
  simp [min_eq_left hsw', max_eq_right hs0]

private lemma walkPoint_cons_mul {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) (t : unitInterval) :
    walkPoint (.cons hadj q) ((t : ℝ) * W.weight d.edge) = edgePoint d t := by
  have hw := W.dart_weight_pos d
  have h0 : 0 ≤ (t : ℝ) * W.weight d.edge := mul_nonneg t.2.1 hw.le
  have hle : (t : ℝ) * W.weight d.edge ≤ W.weight d.edge := mul_le_of_le_one_left hw.le t.2.2
  rw [walkPoint_cons_of_le hadj q d hd h0 hle (div_nonneg h0 hw.le) ((div_le_one hw).mpr hle)]
  congr 1
  ext
  exact mul_div_cancel_right₀ (t : ℝ) hw.ne'

private lemma walkPoint_cons_of_gt {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) {s : ℝ} (hs : W.weight d.edge < s) :
    walkPoint (.cons hadj q) s = walkPoint q (s - W.weight d.edge) := by
  subst hd
  have hns : ¬ s ≤ W.weight (⟨(u, b), hadj⟩ : W.graph.Dart).edge := not_le.mpr hs
  dsimp only [walkPoint]
  split_ifs
  rfl

private lemma walkPoint_cons_eq_end {u b v : V} (hadj : W.graph.Adj u b) (q : W.graph.Walk b v)
    (d : W.graph.Dart) (hd : d = ⟨(u, b), hadj⟩) {s : ℝ} (hs : s = W.weight d.edge) :
    walkPoint (.cons hadj q) s = vertex b := by
  have hw := W.dart_weight_pos d
  have h0 : 0 ≤ s / W.weight d.edge := div_nonneg (hs ▸ hw.le) hw.le
  have h1 : s / W.weight d.edge ≤ 1 := (div_le_one hw).mpr hs.le
  rw [walkPoint_cons_of_le hadj q d hd (hs ▸ hw.le) hs.le h0 h1]
  have ht : (⟨s / W.weight d.edge, h0, h1⟩ : unitInterval) = 1 := by
    ext
    exact (div_eq_one_iff_eq hw.ne').mpr hs
  have hdb : d.snd = b := by rw [hd]
  rw [ht, edgePoint_one, hdb]

theorem walkPoint_nonpos : ∀ {u v : V} (p : W.graph.Walk u v) {s : ℝ},
    s ≤ 0 → walkPoint p s = vertex u
  | _, _, .nil, _, _ => rfl
  | u, _, .cons (v := b) hadj q, s, hs => by
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    have hsw : s ≤ W.weight d.edge := hs.trans hw.le
    dsimp only [walkPoint]
    split_ifs with h
    · have h0 : (⟨max 0 (min s (W.weight d.edge)) / W.weight d.edge,
          div_nonneg (le_max_left 0 _) hw.le,
          (div_le_one hw).mpr (max_le hw.le (min_le_right _ _))⟩ : unitInterval) = 0 := by
        ext
        simp [min_eq_left hsw, max_eq_left hs]
      rw [h0, edgePoint_zero]
    · exact absurd hsw h

theorem walkPoint_ge : ∀ {u v : V} (p : W.graph.Walk u v) {s : ℝ},
    walkLength W.weight p ≤ s → walkPoint p s = vertex v
  | _, _, .nil, _, _ => rfl
  | u, v, .cons (v := b) hadj q, s, hs => by
    rw [walkLength_cons] at hs
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hwe : W.weight s(u, b) = W.weight d.edge := rfl
    rw [hwe] at hs
    have hq_nn : 0 ≤ walkLength W.weight q := walkLength_nonneg W.weight W.weight_nonneg q
    by_cases hsw : s ≤ W.weight d.edge
    · have hq_len : walkLength W.weight q = 0 := le_antisymm (by linarith) hq_nn
      have hq_nil : q.Nil := by
        by_contra hnn
        linarith [walkLength_pos_of_not_nil (W := W) hnn]
      cases hq_nil
      rw [walkLength_nil, add_zero] at hs
      exact walkPoint_cons_eq_end hadj .nil d rfl (le_antisymm hsw hs)
    · rw [walkPoint_cons_of_gt hadj q d rfl (lt_of_not_ge hsw)]
      exact walkPoint_ge q (by linarith)

theorem walkPoint_append_of_le : ∀ {u v w : V} (p : W.graph.Walk u v) (q : W.graph.Walk v w)
    {s : ℝ}, s ≤ walkLength W.weight p → walkPoint (p.append q) s = walkPoint p s
  | _, _, _, .nil, q, s, hs => by
    rw [walkLength_nil] at hs
    rw [Walk.nil_append, walkPoint_nonpos q hs]
    rfl
  | u, v, w, .cons (v := b) hadj p', q, s, hs => by
    rw [walkLength_cons] at hs
    have hwe : W.weight (⟨(u, b), hadj⟩ : W.graph.Dart).edge = W.weight s(u, b) := rfl
    dsimp only [Walk.cons_append, walkPoint]
    split_ifs with hsw
    · rfl
    · exact walkPoint_append_of_le p' q (by linarith)

theorem walkPoint_append_of_ge : ∀ {u v w : V} (p : W.graph.Walk u v) (q : W.graph.Walk v w)
    {r : ℝ}, 0 ≤ r → walkPoint (p.append q) (walkLength W.weight p + r) = walkPoint q r
  | _, _, _, .nil, q, r, _ => by
    rw [Walk.nil_append, walkLength_nil, zero_add]
  | u, v, w, .cons (v := b) hadj p', q, r, hr => by
    rw [walkLength_cons, add_assoc]
    dsimp only [Walk.cons_append]
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hwe : W.weight s(u, b) = W.weight d.edge := rfl
    rw [hwe]
    have hp'_nn : 0 ≤ walkLength W.weight p' := walkLength_nonneg W.weight W.weight_nonneg p'
    by_cases hsum : walkLength W.weight p' + r = 0
    · have hp'0 : walkLength W.weight p' = 0 := by linarith
      have hr0 : r = 0 := by linarith
      have hp'_nil : p'.Nil := by
        by_contra hnn
        linarith [walkLength_pos_of_not_nil (W := W) hnn]
      cases hp'_nil
      subst hr0
      rw [walkLength_nil, add_zero, add_zero,
        walkPoint_cons_eq_end hadj (Walk.nil.append q) d rfl rfl, walkPoint_nonpos q le_rfl]
    · have hgt : W.weight d.edge < W.weight d.edge + (walkLength W.weight p' + r) := by
        have : 0 < walkLength W.weight p' + r := lt_of_le_of_ne (by linarith) (Ne.symm hsum)
        linarith
      rw [walkPoint_cons_of_gt hadj (p'.append q) d rfl hgt, add_sub_cancel_left]
      exact walkPoint_append_of_ge p' q hr

theorem dist_walkPoint_le [Finite V] {u v : V} (p : W.graph.Walk u v) (s t : ℝ) :
    Dist.dist (walkPoint p s) (walkPoint p t) ≤ |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [_root_.dist_comm, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  induction p generalizing s t with
  | nil => simp [walkPoint, hst]
  | @cons a b c hadj q ih =>
    let d : W.graph.Dart := ⟨(a, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    dsimp only [walkPoint]
    split_ifs with hsw htw htw
    · refine (dist_edgePoint_self_le d _ _).trans ?_
      dsimp only
      rw [min_eq_left hsw, min_eq_left htw, ← sub_div, abs_div, abs_of_pos hw,
        mul_div_cancel₀ _ hw.ne']
      rcases le_or_gt 0 s with hs0 | hs0
      · rw [max_eq_right hs0, max_eq_right (hs0.trans hst), abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr hst)]
      · rw [max_eq_left hs0.le]
        rcases le_or_gt 0 t with ht0 | ht0
        · rw [max_eq_right ht0, zero_sub, abs_neg, abs_of_nonneg ht0]
          linarith
        · rw [max_eq_left ht0.le, sub_self, abs_zero]
          linarith
    · have h1 : Dist.dist (edgePoint d ⟨max 0 (min s (W.weight d.edge)) / W.weight d.edge,
          div_nonneg (le_max_left 0 _) hw.le,
          (div_le_one hw).mpr (max_le hw.le (min_le_right _ _))⟩)
          (vertex b) ≤ W.weight d.edge - s := by
        have : (vertex b : MetricGraph W) = edgePoint d 1 := (edgePoint_one d).symm
        rw [this]
        refine (dist_edgePoint_self_le d _ 1).trans ?_
        dsimp only
        have h1_coe : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1_coe, min_eq_left hsw, abs_sub_comm]
        have hle1 : max 0 s / W.weight d.edge ≤ 1 := (div_le_one hw).mpr (max_le hw.le hsw)
        rw [abs_of_nonneg (sub_nonneg.mpr hle1), mul_sub, mul_one, mul_div_cancel₀ _ hw.ne']
        linarith [le_max_right 0 s]
      have h2 : Dist.dist (vertex b : MetricGraph W) (walkPoint q (t - W.weight d.edge)) ≤
          t - W.weight d.edge := by
        rw [← walkPoint_nonpos q (s := 0) le_rfl]
        exact (ih 0 (t - W.weight d.edge) (by linarith)).trans_eq (by ring)
      exact (_root_.dist_triangle _ (vertex b) _).trans (by linarith)
    · exact absurd (hst.trans htw) hsw
    · exact (ih (s - W.weight d.edge) (t - W.weight d.edge) (by linarith)).trans_eq (by ring)

private lemma walkPoint_dart_decomp : ∀ {u v : V} (p : W.graph.Walk u v), ¬ p.Nil →
    ∀ {s : ℝ}, 0 ≤ s → s ≤ walkLength W.weight p →
    ∃ (d : W.graph.Dart) (q₁ : W.graph.Walk u d.fst) (q₂ : W.graph.Walk d.snd v)
      (hadj : W.graph.Adj d.fst d.snd) (t : unitInterval),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ p = q₁.append (.cons hadj q₂) ∧
      walkPoint p s = edgePoint d t ∧ s = walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge
  | _, _, .nil, hp, _, _, _ => absurd .nil hp
  | u, v, .cons (v := b) hadj q, _, s, hs0, hsl => by
    let d : W.graph.Dart := ⟨(u, b), hadj⟩
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    by_cases hsw : s ≤ W.weight d.edge
    · let t : unitInterval :=
        ⟨s / W.weight d.edge, div_nonneg hs0 hw.le, (div_le_one hw).mpr hsw⟩
      refine ⟨d, .nil, q, hadj, t, rfl, rfl, ?_, ?_⟩
      · exact walkPoint_cons_of_le hadj q d rfl hs0 hsw
          (div_nonneg hs0 hw.le) ((div_le_one hw).mpr hsw)
      · simp [t, walkLength_nil, div_mul_cancel₀ _ hw.ne']
    · have hq_nn : ¬ q.Nil := by
        intro hqn
        cases hqn
        rw [walkLength_cons, walkLength_nil, add_zero] at hsl
        exact hsw hsl
      rw [walkLength_cons] at hsl
      have hwe : W.weight s(u, b) = W.weight d.edge := rfl
      rw [hwe] at hsl
      obtain ⟨d', q₁', q₂', hadj', t, hd', hq_eq, hpt, hs_eq⟩ :=
        walkPoint_dart_decomp q hq_nn (s := s - W.weight d.edge) (by linarith) (by linarith)
      refine ⟨d', .cons hadj q₁', q₂', hadj', t, hd', ?_, ?_, ?_⟩
      · conv_lhs => rw [hq_eq]
        rfl
      · rw [walkPoint_cons_of_gt hadj q d rfl (lt_of_not_ge hsw), hpt]
      · simp only [walkLength_cons]
        linarith

private lemma walkPoint_last_sub : ∀ {u v : V} (p : W.graph.Walk u v), ¬ p.Nil →
    ∃ (d : W.graph.Dart), d.fst = v ∧ d.edge ∈ p.edges ∧
      ∀ {r : ℝ}, 0 < r → r ≤ W.weight d.edge →
        ∀ (hr0 : 0 ≤ r / W.weight d.edge) (hr1 : r / W.weight d.edge ≤ 1),
          walkPoint p (walkLength W.weight p - r) =
            edgePoint d ⟨r / W.weight d.edge, hr0, hr1⟩
  | _, _, .nil, hp => absurd .nil hp
  | u, _, .cons hadj .nil, _ => by
    let d : W.graph.Dart := ⟨(_, u), hadj.symm⟩
    refine ⟨d, rfl, by simp [d, Sym2.eq_swap], fun {r} hr hrw hr0 hr1 => ?_⟩
    rw [walkLength_cons, walkLength_nil, add_zero]
    have hw : 0 < W.weight d.edge := W.dart_weight_pos d
    let d₀ : W.graph.Dart := ⟨(u, _), hadj⟩
    have hd_symm : W.weight d₀.edge = W.weight d.edge := by simp [d, d₀, Sym2.eq_swap]
    have hwe : W.weight s(u, _) = W.weight d₀.edge := rfl
    rw [hwe, hd_symm]
    rw [walkPoint_cons_of_le hadj .nil d₀ rfl (by linarith) (by linarith [hd_symm])
      (div_nonneg (by linarith) (hd_symm ▸ hw.le))
      ((div_le_one (hd_symm ▸ hw)).mpr (by linarith [hd_symm])),
      ← edgePoint_symm d₀]
    congr 1
    ext
    simp only [unitInterval.coe_symm_eq, hd_symm]
    field_simp
    ring
  | u, v, .cons (v := b) hadj (.cons (v := b₂) hadj2 q2), _ => by
    obtain ⟨d, hdv, hde, hwalk⟩ := walkPoint_last_sub (.cons hadj2 q2) Walk.not_nil_cons
    refine ⟨d, hdv, List.mem_cons_of_mem _ hde, fun {r} hr hrw hr0 hr1 => ?_⟩
    let d₀ : W.graph.Dart := ⟨(u, b), hadj⟩
    have hw₀ : 0 < W.weight d₀.edge := W.dart_weight_pos d₀
    have hq_len : W.weight d.edge ≤ walkLength W.weight (.cons hadj2 q2) :=
      weight_le_walkLength_of_mem_edges (.cons hadj2 q2) hde
    rw [walkLength_cons]
    have hwe0 : W.weight s(u, b) = W.weight d₀.edge := rfl
    rw [hwe0]
    by_cases hrl : r < walkLength W.weight (.cons hadj2 q2)
    · have hgt : W.weight d₀.edge <
          W.weight d₀.edge + walkLength W.weight (.cons hadj2 q2) - r := by linarith
      rw [walkPoint_cons_of_gt hadj (.cons hadj2 q2) d₀ rfl hgt,
        show W.weight d₀.edge + walkLength W.weight (.cons hadj2 q2) - r -
          W.weight d₀.edge = walkLength W.weight (.cons hadj2 q2) - r by ring]
      exact hwalk hr hrw hr0 hr1
    · have hreq : r = W.weight d.edge := le_antisymm hrw (le_trans hq_len (not_lt.mp hrl))
      have hqeq : walkLength W.weight (.cons hadj2 q2) = W.weight d.edge :=
        le_antisymm (hreq ▸ not_lt.mp hrl) hq_len
      have hq2_nil : q2.Nil := by
        cases q2 with
        | nil => exact .nil
        | cons hadj3 q3 =>
          exfalso
          have hw2 : 0 < W.weight s(b, b₂) := W.dart_weight_pos ⟨(b, b₂), hadj2⟩
          have hq2_pos : 0 < walkLength W.weight (Walk.cons hadj3 q3) :=
            walkLength_pos_of_not_nil Walk.not_nil_cons
          rw [walkLength_cons] at hqeq
          rw [Walk.edges_cons, List.mem_cons] at hde
          rcases hde with hde | hde
          · rw [hde] at hqeq
            linarith
          · have : W.weight d.edge ≤ walkLength W.weight (Walk.cons hadj3 q3) :=
              weight_le_walkLength_of_mem_edges (Walk.cons hadj3 q3) hde
            linarith
      cases hq2_nil
      have hde_edge : d.edge = s(b, v) := by
        simpa [Walk.edges_cons] using hde
      have hd_snd : d.snd = b := by
        have hm : d.snd ∈ s(b, v) := hde_edge ▸ Sym2.mem_mk_right d.fst d.snd
        rw [Sym2.mem_iff] at hm
        rcases hm with h | h
        · exact h
        · exact absurd (h.trans hdv.symm) d.snd_ne_fst
      have hsub_eq : W.weight d₀.edge + walkLength W.weight (.cons hadj2 .nil) - r =
          W.weight d₀.edge := by linarith
      rw [hsub_eq, walkPoint_cons_eq_end hadj (.cons hadj2 .nil) d₀ rfl rfl]
      have ht2 : (⟨r / W.weight d.edge, hr0, hr1⟩ : unitInterval) = 1 := by
        ext
        simp [hreq, (W.dart_weight_pos d).ne']
      rw [ht2, edgePoint_one, hd_snd]


/-- Periodic arc-length parameterization of a cycle `c : W.graph.Walk v₀ v₀` into
`MetricGraph W`. -/
@[expose] noncomputable def circleMap {v₀ : V} {c : W.graph.Walk v₀ v₀} (_ : c.IsCycle)
    (s : ℝ) : MetricGraph W :=
  walkPoint c (Int.fract (s / walkLength W.weight c) * walkLength W.weight c)

theorem circleMap_periodic {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) :
    circleMap hc (s + walkLength W.weight c) = circleMap hc s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  simp only [circleMap, add_div, div_self hL.ne', Int.fract_add_one]

theorem circleMap_add_int_mul {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) (k : ℤ) :
    circleMap hc (s + (k : ℝ) * walkLength W.weight c) = circleMap hc s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  simp only [circleMap, add_div, mul_div_cancel_right₀ _ hL.ne', Int.fract_add_intCast]

theorem circleMap_eq_walkPoint {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) {s : ℝ}
    (hs0 : 0 ≤ s) (hsl : s ≤ walkLength W.weight c) :
    circleMap hc s = walkPoint c s := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  rcases eq_or_lt_of_le hsl with rfl | hlt
  · have hper := circleMap_periodic hc 0
    rw [zero_add] at hper
    rw [hper, circleMap, zero_div, Int.fract_zero, zero_mul, walkPoint_nonpos c le_rfl,
      walkPoint_ge c le_rfl]
  · have hfl : ⌊s / walkLength W.weight c⌋ = 0 :=
      Int.floor_eq_iff.mpr ⟨by simpa using div_nonneg hs0 hL.le,
        by simpa using (div_lt_one hL).mpr hlt⟩
    have hf : Int.fract (s / walkLength W.weight c) = s / walkLength W.weight c := by
      rw [Int.fract, hfl, Int.cast_zero, sub_zero]
    rw [circleMap, hf, div_mul_cancel₀ _ hL.ne']

@[simp]
theorem circleMap_zero {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    circleMap hc 0 = vertex v₀ := by
  rw [circleMap_eq_walkPoint hc le_rfl (walkLength_nonneg W.weight W.weight_nonneg c),
    walkPoint_nonpos c le_rfl]

theorem circleMap_dist_le [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    (s t : ℝ) :
    Dist.dist (circleMap hc s) (circleMap hc t) ≤ |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [_root_.dist_comm, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  let L := walkLength W.weight c
  let k : ℤ := ⌊(t - s) / L⌋
  have ht_shift : s ≤ t + (-k : ℤ) * L := by
    have hle : (k : ℝ) * L ≤ t - s := (le_div_iff₀ hL).mp (Int.floor_le _)
    rw [Int.cast_neg]
    linarith
  have hlt_shift : t + (-k : ℤ) * L - s < L := by
    have hlt : (t - s) / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hmul := (div_lt_iff₀ hL).mp hlt
    rw [Int.cast_neg]
    linarith
  rw [← circleMap_add_int_mul hc t (-k)]
  have hk_nn : 0 ≤ (k : ℝ) * L := by
    have : 0 ≤ (k : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr hst) hL.le)
    exact mul_nonneg this hL.le
  refine le_trans ?_ (by rw [Int.cast_neg]; linarith : t + (-k : ℤ) * L - s ≤ t - s)
  let t' := t + (-k : ℤ) * L
  let r := Int.fract (s / L) * L
  have hr0 : 0 ≤ r := mul_nonneg (Int.fract_nonneg _) hL.le
  have hrl : r < L := (mul_lt_iff_lt_one_left hL).mpr (Int.fract_lt_one _)
  have hs_shift : s = r + (⌊s / L⌋ : ℝ) * L := by
    dsimp only [r]
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  have hsm : circleMap hc s = walkPoint c r := rfl
  by_cases hsum : r + (t' - s) ≤ L
  · have ht'_eq : t' = (r + (t' - s)) + (⌊s / L⌋ : ℝ) * L := by linarith
    have htm : circleMap hc t' = walkPoint c (r + (t' - s)) := by
      conv_lhs => rw [ht'_eq]
      rw [circleMap_add_int_mul hc (r + (t' - s)) ⌊s / L⌋]
      exact circleMap_eq_walkPoint hc (by linarith) hsum
    rw [hsm, htm]
    exact (dist_walkPoint_le c r (r + (t' - s))).trans_eq (by
      rw [abs_sub_comm, abs_of_nonneg (by linarith), add_sub_cancel_left])
  · have h1 : Dist.dist (circleMap hc s) (vertex v₀) ≤ L - r := by
      rw [hsm, ← walkPoint_ge c (s := L) le_rfl]
      exact (dist_walkPoint_le c r L).trans_eq (by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hrl.le)])
    have ht'_sub : 0 ≤ r + (t' - s) - L := by linarith
    have ht'_sub_lt : r + (t' - s) - L ≤ L := by linarith
    have ht'_eq : t' = (r + (t' - s) - L) + ((⌊s / L⌋ + 1 : ℤ) : ℝ) * L := by
      push_cast
      linarith
    have h2 : Dist.dist (vertex v₀) (circleMap hc t') ≤ r + (t' - s) - L := by
      conv_lhs => arg 2; rw [ht'_eq]
      rw [circleMap_add_int_mul hc _ (⌊s / L⌋ + 1),
        circleMap_eq_walkPoint hc ht'_sub ht'_sub_lt, ← walkPoint_nonpos c (s := 0) le_rfl]
      exact (dist_walkPoint_le c 0 (r + (t' - s) - L)).trans_eq (by
        rw [zero_sub, abs_neg, abs_of_nonneg ht'_sub])
    exact (_root_.dist_triangle _ (vertex v₀) _).trans (by linarith)

theorem circleMap_continuous [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    Continuous (circleMap hc) :=
  continuous_iff_continuousAt.mpr fun _ =>
    Metric.continuousAt_iff.mpr fun ε hε =>
      ⟨ε, hε, fun {y} hy => (circleMap_dist_le hc y _).trans_lt (by simpa [Real.dist_eq] using hy)⟩

theorem circleMap_dist_le_circleDist [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    (s t : ℝ) :
    Dist.dist (circleMap hc s) (circleMap hc t) ≤ circleDist (walkLength W.weight c) s t := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  obtain ⟨k, hk⟩ := exists_eq_add_int_mul_dist hL s t
  rw [← hk, ← circleMap_add_int_mul hc t k]
  exact circleMap_dist_le hc s (t + (k : ℝ) * walkLength W.weight c)

end CircleMap

/-! ### Isometric shortest cycles -/

section ShortestCycleIsometry

private lemma isCycle_append_chord {u w : V}
    {q : W.graph.Walk u w} {r : W.graph.Walk w u} (hq : q.IsPath) (hr : r.IsPath)
    (huw : u ≠ w) (hdisj : ∀ x ∈ q.support, x ∈ r.support → x = u ∨ x = w)
    (hlen : 3 ≤ q.length + r.length) :
    (q.append r).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, by rw [Walk.length_append]; exact hlen⟩
  have hqn : ¬ q.Nil := Walk.not_nil_of_ne huw
  have hrn : ¬ r.Nil := Walk.not_nil_of_ne huw.symm
  cases q with
  | nil => exact absurd .nil hqn
  | cons hadj q' =>
    rw [Walk.cons_append]
    simp only [Walk.tail_cons]
    refine (Walk.isPath_copy (q'.append r) _ _).mpr
      ((Walk.isPath_append q' r).mpr ⟨hq.of_cons, hr.tail, ?_⟩)
    rw [List.disjoint_left]
    intro x hxq' hxr
    have hxq : x ∈ (Walk.cons hadj q').support := List.mem_cons_of_mem _ hxq'
    have hxr' : x ∈ r.support := List.mem_of_mem_tail hxr
    rcases hdisj x hxq hxr' with rfl | rfl
    · exact (Walk.cons_isPath_iff hadj q').mp hq |>.2 hxq'
    · rw [← Walk.support_tail_of_not_nil r hrn] at hxr
      have hrnd := hr.support_nodup
      rw [← Walk.cons_tail_eq r hrn, Walk.support_cons, List.nodup_cons] at hrnd
      exact hrnd.1 hxr

private noncomputable def cycCoord [DecidableEq V] {v₀ : V} (c : W.graph.Walk v₀ v₀) (u : V) : ℝ :=
  if h : u ∈ c.support then walkLength W.weight (c.takeUntil u h) else 0

private lemma cycCoord_of_mem [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀} {u : V}
    (hu : u ∈ c.support) : cycCoord c u = walkLength W.weight (c.takeUntil u hu) := by
  dsimp only [cycCoord]
  split_ifs
  rfl

private lemma takeUntil_walkLength_congr [DecidableEq V] {a b x : V} {p q : W.graph.Walk a b}
    (h : p = q) (hp : x ∈ p.support) :
    walkLength W.weight (p.takeUntil x hp) = walkLength W.weight (q.takeUntil x (h ▸ hp)) := by
  subst h
  rfl

private lemma takeUntil_append_of_not_mem_left [DecidableEq V] {a b d : V} {x : V}
    (p : W.graph.Walk a b) (q : W.graph.Walk b d) (hxp : x ∉ p.support)
    (hxq : x ∈ q.support) :
    (p.append q).takeUntil x (Walk.support_subset_support_append_right _ _ hxq) =
      p.append (q.takeUntil x hxq) := by
  induction p with
  | nil => simp
  | cons hadj p' ih =>
    have hne : _ ≠ x := fun h => hxp (h ▸ Walk.start_mem_support _)
    have hxp' : x ∉ p'.support := fun h => hxp (List.mem_cons_of_mem _ h)
    simp only [Walk.cons_append, Walk.takeUntil]
    split_ifs with h
    · exact absurd h hne
    · rw [ih q hxp']

private lemma takeUntil_self_of_isPath [DecidableEq V] {a b : V} (p : W.graph.Walk a b)
    (hp : p.IsPath) : p.takeUntil b p.end_mem_support = p := by
  induction p with
  | nil => rfl
  | @cons u v w hadj q ih =>
    have hne : u ≠ w := by
      rintro rfl
      exact (Walk.cons_isPath_iff hadj q).mp hp |>.2 q.end_mem_support
    simp only [Walk.takeUntil]
    split_ifs with h
    · exact absurd h hne
    · rw [ih hp.of_cons]

private lemma cycCoord_append_eq [DecidableEq V] {v₀ u : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) {p : W.graph.Walk v₀ u} {q : W.graph.Walk u v₀}
    (hc_eq : c = p.append q) (hq : ¬ q.Nil) :
    cycCoord c u = walkLength W.weight p := by
  have hc' : (p.append q).IsCycle := hc_eq ▸ hc
  have hp_path : p.IsPath := hc'.isPath_of_append_left hq
  have hu : u ∈ c.support := hc_eq ▸ Walk.support_subset_support_append_left _ _ p.end_mem_support
  rw [cycCoord_of_mem hu, takeUntil_walkLength_congr hc_eq hu,
    Walk.takeUntil_append_of_mem_left _ _ p.end_mem_support, takeUntil_self_of_isPath p hp_path]

private lemma takeUntil_rotate_length_start [DecidableEq V] {v₀ a : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (ha : a ∈ c.support) (hav0 : a ≠ v₀) :
    circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c v₀) ≤
      min
        (walkLength W.weight
          ((c.rotate a ha).takeUntil v₀
            ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c))))
        (walkLength W.weight
          ((c.rotate a ha).dropUntil v₀
            ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c)))) := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let c₁ := c.takeUntil a ha
  let c₂ := c.dropUntil a ha
  have hc_eq : c₁.append c₂ = c := c.take_spec ha
  have hlen12 : walkLength W.weight c₁ + walkLength W.weight c₂ = L := by
    rw [← walkLength_append, hc_eq]
  have ha_coord : cycCoord c a = walkLength W.weight c₁ := cycCoord_of_mem ha
  have hlen_arc : walkLength W.weight
        ((c.rotate a ha).takeUntil v₀
          ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c))) +
      walkLength W.weight
        ((c.rotate a ha).dropUntil v₀
          ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c))) = L := by
    rw [← walkLength_append, Walk.take_spec]
    exact walkLength_perm_eq W.weight (c.rotate_edges a ha).perm
  have hc1_nn : ¬ c₁.Nil := by
    intro hnil
    exact hav0 (Walk.nil_takeUntil c ha |>.mp hnil).symm
  have hc0 : cycCoord c v₀ = 0 := by
    rw [cycCoord_of_mem (Walk.start_mem_support c), Walk.takeUntil_first, walkLength_nil]
  have hv0_c2 : v₀ ∈ c₂.support := Walk.end_mem_support _
  have harc1_eq : (c.rotate a ha).takeUntil v₀
      ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c)) =
      c₂.takeUntil v₀ hv0_c2 := by
    dsimp only [Walk.rotate]
    exact Walk.takeUntil_append_of_mem_left c₂ c₁ hv0_c2
  have hdrop2 : (c₂.dropUntil v₀ hv0_c2).Nil := by
    by_contra hnn
    have hcnt1 : 1 ≤ c₁.support.dropLast.count v₀ := by
      rw [List.one_le_count_iff]
      cases hc1c : c₁ with
      | nil =>
        rw [hc1c] at hc1_nn
        exact absurd .nil hc1_nn
      | cons _ p₁ =>
        rw [Walk.support_cons, List.dropLast_cons_of_ne_nil (Walk.support_ne_nil p₁)]
        exact List.mem_cons_self
    have hcnt2 : 2 ≤ c₂.support.count v₀ := by
      have hsp := congrArg Walk.support (c₂.take_spec hv0_c2)
      rw [Walk.support_append] at hsp
      have h1 : v₀ ∈ (c₂.takeUntil v₀ hv0_c2).support := Walk.end_mem_support _
      have h2 : v₀ ∈ (c₂.dropUntil v₀ hv0_c2).support.tail := by
        cases hdl : c₂.dropUntil v₀ hv0_c2 with
        | nil =>
          rw [hdl] at hnn
          exact absurd .nil hnn
        | cons _ q₂ =>
          rw [Walk.support_cons, List.tail_cons]
          exact Walk.end_mem_support q₂
      have hsum : c₂.support.count v₀ =
          (c₂.takeUntil v₀ hv0_c2).support.count v₀ +
          (c₂.dropUntil v₀ hv0_c2).support.tail.count v₀ := by
        rw [← hsp, List.count_append]
      have := List.one_le_count_iff.mpr h1
      have := List.one_le_count_iff.mpr h2
      omega
    have hsup : c.support.count v₀ = c₁.support.dropLast.count v₀ + c₂.support.count v₀ := by
      have hsp := congrArg Walk.support hc_eq
      rw [Walk.support_append_eq_support_dropLast_append] at hsp
      rw [← hsp, List.count_append]
    have := hc.count_support
    omega
  have harc1_len : walkLength W.weight
      ((c.rotate a ha).takeUntil v₀
        ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c))) =
      walkLength W.weight c₂ := by
    have hsp := c₂.take_spec hv0_c2
    have hln : walkLength W.weight (c₂.takeUntil v₀ hv0_c2) +
        walkLength W.weight (c₂.dropUntil v₀ hv0_c2) = walkLength W.weight c₂ := by
      rw [← walkLength_append, hsp]
    have hnil_len : walkLength W.weight (c₂.dropUntil v₀ hv0_c2) = 0 := by
      rw [Walk.Nil.eq_nil hdrop2]
      exact walkLength_nil W.weight
    rw [harc1_eq]
    linarith
  have harc2_len : walkLength W.weight
      ((c.rotate a ha).dropUntil v₀
        ((c.mem_support_rotate_iff a ha).mpr (Walk.start_mem_support c))) =
      walkLength W.weight c₁ := by linarith
  rw [ha_coord, hc0]
  refine le_min ?_ ?_
  · rw [← circleDist_add_int_right hL _ 0 1, zero_add, Int.cast_one, one_mul, harc1_len]
    refine (circleDist_le_abs hL _ _).trans_eq ?_
    rw [← hlen12, sub_add_cancel_left, abs_neg,
      abs_of_nonneg (walkLength_nonneg _ W.weight_nonneg _)]
  · rw [harc2_len]
    refine (circleDist_le_abs hL _ _).trans_eq ?_
    rw [sub_zero, abs_of_nonneg (walkLength_nonneg _ W.weight_nonneg _)]

private lemma takeUntil_rotate_length [DecidableEq V] {v₀ a w : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (ha : a ∈ c.support) (hw : w ∈ c.support) (haw : a ≠ w) :
    circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c w) ≤
      min (walkLength W.weight
          ((c.rotate a ha).takeUntil w ((c.mem_support_rotate_iff a ha).mpr hw)))
        (walkLength W.weight
          ((c.rotate a ha).dropUntil w ((c.mem_support_rotate_iff a ha).mpr hw))) := by
  by_cases hwv0 : w = v₀
  · subst hwv0
    exact takeUntil_rotate_length_start hc ha haw
  · let L := walkLength W.weight c
    have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
    let c₁ := c.takeUntil a ha
    let c₂ := c.dropUntil a ha
    have hc_eq : c₁.append c₂ = c := c.take_spec ha
    have hlen12 : walkLength W.weight c₁ + walkLength W.weight c₂ = L := by
      rw [← walkLength_append, hc_eq]
    have ha_coord : cycCoord c a = walkLength W.weight c₁ := cycCoord_of_mem ha
    let hw_rot := (c.mem_support_rotate_iff a ha).mpr hw
    let arc₁ := (c.rotate a ha).takeUntil w hw_rot
    let arc₂ := (c.rotate a ha).dropUntil w hw_rot
    have hlen_arc : walkLength W.weight arc₁ + walkLength W.weight arc₂ = L := by
      rw [← walkLength_append, Walk.take_spec]
      exact walkLength_perm_eq W.weight (c.rotate_edges a ha).perm
    have hw_cnt : c.support.count w = 1 := hc.count_support_of_mem hw hwv0
    have hsup : c.support.count w = c₁.support.dropLast.count w + c₂.support.count w := by
      have hsp := congrArg Walk.support hc_eq
      rw [Walk.support_append_eq_support_dropLast_append] at hsp
      rw [← hsp, List.count_append]
    by_cases hwc1 : w ∈ c₁.support
    · have hwc1_drop : w ∈ c₁.support.dropLast := by
        have hsp : c₁.support = c₁.support.dropLast ++ [a] := by
          simpa only [Walk.append_nil, Walk.support_nil] using
            Walk.support_append_eq_support_dropLast_append c₁ (.nil : W.graph.Walk a a)
        rw [hsp, List.mem_append, List.mem_singleton] at hwc1
        exact hwc1.resolve_right haw.symm
      have hcnt1 : 1 ≤ c₁.support.dropLast.count w := List.one_le_count_iff.mpr hwc1_drop
      have hwc2 : w ∉ c₂.support := by
        rw [← List.count_eq_zero]
        omega
      have hcw_eq : cycCoord c w = walkLength W.weight (c₁.takeUntil w hwc1) := by
        rw [cycCoord_of_mem hw, takeUntil_walkLength_congr hc_eq.symm hw,
          Walk.takeUntil_append_of_mem_left c₁ c₂ hwc1]
      have harc1_eq : arc₁ = c₂.append (c₁.takeUntil w hwc1) := by
        dsimp only [arc₁, Walk.rotate]
        exact takeUntil_append_of_not_mem_left c₂ c₁ hwc2 hwc1
      have hle_c1 : walkLength W.weight (c₁.takeUntil w hwc1) ≤ walkLength W.weight c₁ := by
        have := congrArg (walkLength W.weight) (c₁.take_spec hwc1)
        rw [walkLength_append] at this
        linarith [walkLength_nonneg W.weight W.weight_nonneg (c₁.dropUntil w hwc1)]
      have harc1_len : walkLength W.weight arc₁ = walkLength W.weight c₂ + cycCoord c w := by
        rw [harc1_eq, walkLength_append, hcw_eq]
      have harc2_len : walkLength W.weight arc₂ = cycCoord c a - cycCoord c w := by
        linarith [hlen12, hlen_arc, ha_coord]
      have hcw_nn : 0 ≤ cycCoord c w := by
        rw [hcw_eq]
        exact walkLength_nonneg W.weight W.weight_nonneg _
      have hc2_nn : 0 ≤ walkLength W.weight c₂ := walkLength_nonneg W.weight W.weight_nonneg c₂
      rw [← hcw_eq] at hle_c1
      refine le_min ?_ ?_
      · rw [← circleDist_add_int_right hL _ _ 1, Int.cast_one, one_mul]
        refine (circleDist_le_abs hL _ _).trans_eq ?_
        rw [abs_sub_comm, abs_of_nonneg (by linarith [ha_coord])]
        linarith [hlen12, ha_coord, harc1_len]
      · rw [harc2_len]
        refine (circleDist_le_abs hL _ _).trans_eq ?_
        rw [abs_of_nonneg (by linarith [ha_coord])]
    · have hwc2 : w ∈ c₂.support := by
        rw [← hc_eq, Walk.support_append, List.mem_append] at hw
        exact List.mem_of_mem_tail (hw.resolve_left hwc1)
      have hcw_eq : cycCoord c w =
          walkLength W.weight c₁ + walkLength W.weight (c₂.takeUntil w hwc2) := by
        rw [cycCoord_of_mem hw, takeUntil_walkLength_congr hc_eq.symm hw,
          takeUntil_append_of_not_mem_left c₁ c₂ hwc1 hwc2, walkLength_append]
      have harc1_eq : arc₁ = c₂.takeUntil w hwc2 := by
        dsimp only [arc₁, Walk.rotate]
        exact Walk.takeUntil_append_of_mem_left c₂ c₁ hwc2
      have harc1_len : walkLength W.weight arc₁ = cycCoord c w - cycCoord c a := by
        rw [harc1_eq, ha_coord, hcw_eq]
        ring
      have harc1_le_L : walkLength W.weight arc₁ ≤ L := by
        linarith [hlen_arc, walkLength_nonneg W.weight W.weight_nonneg arc₂]
      refine le_min ?_ ?_
      · rw [harc1_len]
        refine (circleDist_le_abs hL _ _).trans_eq ?_
        rw [abs_sub_comm,
          abs_of_nonneg (by linarith [walkLength_nonneg W.weight W.weight_nonneg arc₁])]
      · rw [← circleDist_add_int_right hL _ _ (-1), Int.cast_neg, Int.cast_one, neg_one_mul]
        refine (circleDist_le_abs hL _ _).trans_eq ?_
        rw [abs_of_nonneg (by linarith)]
        linarith

private lemma walkLength_eq_of_length_one : ∀ {u v : V} (p : W.graph.Walk u v),
    p.length = 1 → walkLength W.weight p = W.weight s(u, v)
  | _, _, .cons _ .nil, _ => by simp [walkLength_cons, walkLength_nil]

private lemma mem_edges_of_length_eq_one : ∀ {u v : V} (p : W.graph.Walk u v),
    p.length = 1 → s(u, v) ∈ p.edges
  | _, _, .cons _ .nil, _ => List.mem_cons_self

private lemma takeUntil_vert_walkLength_congr [DecidableEq V] {u v : V} (p : W.graph.Walk u v)
    {x y : V} (hxy : x = y) (hx : x ∈ p.support) (hy : y ∈ p.support) :
    walkLength W.weight (p.takeUntil x hx) = walkLength W.weight (p.takeUntil y hy) := by
  subst hxy
  rfl

private lemma takeUntil_snd_walkLength [DecidableEq V] {u : V} (p : W.graph.Walk u u)
    (hp : p.IsCycle) (h : p.snd ∈ p.support) :
    walkLength W.weight (p.takeUntil p.snd h) = W.weight s(u, p.snd) := by
  cases p with
  | nil => exact absurd .nil hp.not_nil
  | @cons _ b _ hadj q =>
    have hsnd : (Walk.cons hadj q).snd = b := by simp
    have hb : b ∈ (Walk.cons hadj q).support := by simpa only [hsnd] using h
    have hcongr : walkLength W.weight ((Walk.cons hadj q).takeUntil (Walk.cons hadj q).snd h) =
        walkLength W.weight ((Walk.cons hadj q).takeUntil b hb) :=
      takeUntil_vert_walkLength_congr (Walk.cons hadj q) hsnd h hb
    rw [hcongr, hsnd, Walk.takeUntil]
    split_ifs with heq
    · exact absurd heq hadj.ne
    · rw [Walk.takeUntil_first, walkLength_cons, walkLength_nil, add_zero]

private lemma isCycle_chord_le [DecidableEq V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) :
    ∀ (n : ℕ) {a b : V} (p : W.graph.Walk a b),
      p.length = n → p.IsPath → a ∈ c.support → b ∈ c.support →
        circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c b) ≤
          walkLength W.weight p := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a b p hlen hp ha hb
    let L := walkLength W.weight c
    have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · cases p with
      | nil =>
        rw [circleDist_self hL]
        exact walkLength_nonneg W.weight W.weight_nonneg _
      | cons _ _ =>
        rw [Walk.length_cons] at hlen
        omega
    · have hex : ∃ k : ℕ, 0 < k ∧ k ≤ p.length ∧ p.getVert k ∈ c.support :=
        ⟨p.length, hlen ▸ hn_pos, le_rfl, by simpa only [Walk.getVert_length] using hb⟩
      classical
      let k := Nat.find hex
      have hk := Nat.find_spec hex
      let w := p.getVert k
      have hw : w ∈ c.support := hk.2.2
      let q₁ := p.take k
      let q₂ := p.drop k
      have hq1_path : q₁.IsPath := hp.take k
      have hq2_path : q₂.IsPath := hp.drop k
      have hq1_len : q₁.length = k := by
        rw [Walk.take_length]
        exact min_eq_left hk.2.1
      have hq2_len : q₂.length = p.length - k := Walk.drop_length p k
      have hq2_lt : q₂.length < n := by omega
      have hlen_sum : walkLength W.weight q₁ + walkLength W.weight q₂ = walkLength W.weight p :=
        walkLength_take_add_drop p k
      have hih := ih q₂.length hq2_lt q₂ rfl hq2_path hw hb
      suffices h1 : circleDist L (cycCoord c a) (cycCoord c w) ≤ walkLength W.weight q₁ by
        exact (circleDist_triangle hL (cycCoord c a) (cycCoord c w) (cycCoord c b)).trans
          (by linarith)
      by_cases haw : a = w
      · rw [← haw, circleDist_self hL]
        exact walkLength_nonneg W.weight W.weight_nonneg q₁
      · let cₐ := c.rotate a ha
        have hcₐ : cₐ.IsCycle := (c.isCycle_rotate ha).mpr hs.1
        have hLₐ : walkLength W.weight cₐ = L :=
          walkLength_perm_eq W.weight (c.rotate_edges a ha).perm
        have hw' : w ∈ cₐ.support := (c.mem_support_rotate_iff a ha).mpr hw
        let arc₁ := cₐ.takeUntil w hw'
        let arc₂ := cₐ.dropUntil w hw'
        have harc_sum : walkLength W.weight arc₁ + walkLength W.weight arc₂ = L := by
          rw [← walkLength_append, Walk.take_spec, hLₐ]
        have hcd_min : circleDist L (cycCoord c a) (cycCoord c w) ≤
            min (walkLength W.weight arc₁) (walkLength W.weight arc₂) :=
          takeUntil_rotate_length hs.1 ha hw haw
        refine hcd_min.trans ?_
        by_cases hsub1 : q₁.length = 1 ∧ s(a, w) ∈ cₐ.edges
        · have hq1_w : walkLength W.weight q₁ = W.weight s(a, w) :=
            walkLength_eq_of_length_one q₁ hsub1.1
          rcases hcₐ.isPath_dropLast.eq_snd_or_eq_penultimate_of_start_mem_edges hsub1.2 with
            hwsnd | hwpen
          · refine (min_le_left _ _).trans ?_
            have harc1_w : walkLength W.weight arc₁ = W.weight s(a, w) := by
              have htu := takeUntil_snd_walkLength cₐ hcₐ (hwsnd ▸ hw')
              rw [takeUntil_vert_walkLength_congr cₐ hwsnd hw' (hwsnd ▸ hw'), htu, hwsnd]
            linarith
          · refine (min_le_right _ _).trans ?_
            have hpen_eq : cₐ.getVert (cₐ.length - 1) = w := by
              have hrev := Walk.getVert_reverse cₐ 1
              have hsnd1 : cₐ.reverse.getVert 1 = cₐ.reverse.snd := by
                cases cₐ.reverse <;> rfl
              rw [hsnd1, Walk.snd_reverse] at hrev
              exact hrev.symm.trans hwpen.symm
            have harc1_len_lt : arc₁.length < cₐ.length :=
              Walk.length_takeUntil_lt_length hw' (Ne.symm haw)
            have hl3 := hcₐ.three_le_length
            have harc1_len_eq : arc₁.length = cₐ.length - 1 := by
              have hinj := hcₐ.getVert_injOn'
                (by simp only [Set.mem_ofPred_eq]; dsimp only [arc₁] at harc1_len_lt; omega)
                (by simp only [Set.mem_ofPred_eq]; omega)
                ((Walk.getVert_length_takeUntil hw').trans hpen_eq.symm)
              exact hinj
            have harc2_len : arc₂.length = 1 := by
              have h := congrArg Walk.length (cₐ.take_spec hw')
              rw [Walk.length_append] at h
              change arc₁.length + arc₂.length = cₐ.length at h
              omega
            have harc2_w : walkLength W.weight arc₂ = W.weight s(a, w) := by
              rw [walkLength_eq_of_length_one arc₂ harc2_len, Sym2.eq_swap]
            linarith
        · have harc_disj : ∀ x ∈ q₁.support, x ∈ cₐ.support → x = a ∨ x = w := by
            intro x hxq hxc
            rw [c.mem_support_rotate_iff a ha] at hxc
            by_contra hne
            push Not at hne
            obtain ⟨i, hi_eq, hi_le⟩ := Walk.mem_support_iff_exists_getVert.mp hxq
            rw [hq1_len] at hi_le
            have hi0 : 0 < i := by
              rcases Nat.eq_zero_or_pos i with rfl | hi0
              · dsimp only [q₁] at hi_eq
                rw [Walk.take_getVert, min_zero, Walk.getVert_zero] at hi_eq
                exact absurd hi_eq.symm hne.1
              · exact hi0
            have hik : i < k := by
              rcases eq_or_lt_of_le hi_le with rfl | hik
              · dsimp only [q₁] at hi_eq
                rw [Walk.take_getVert, min_self] at hi_eq
                exact absurd hi_eq.symm hne.2
              · exact hik
            have hgi : p.getVert i = x := by
              dsimp only [q₁] at hi_eq
              rw [Walk.take_getVert, min_eq_right hi_le] at hi_eq
              exact hi_eq
            exact Nat.find_min hex hik ⟨hi0, hi_le.trans hk.2.1, hgi ▸ hxc⟩
          have hcₐ_app : (arc₁.append arc₂).IsCycle := (cₐ.take_spec hw').symm ▸ hcₐ
          have harc1_path : arc₁.IsPath :=
            hcₐ_app.isPath_of_append_left (Walk.not_nil_of_ne (Ne.symm haw))
          have harc2_path : arc₂.IsPath :=
            hcₐ_app.isPath_of_append_right (Walk.not_nil_of_ne haw)
          have harc1_pos : 0 < arc₁.length :=
            Nat.pos_of_ne_zero (Walk.length_eq_zero_iff.not.mpr (Walk.not_nil_of_ne haw))
          have harc2_pos : 0 < arc₂.length :=
            Nat.pos_of_ne_zero (Walk.length_eq_zero_iff.not.mpr (Walk.not_nil_of_ne (Ne.symm haw)))
          have harc1_len_ge : q₁.length = 1 → 2 ≤ arc₁.length := by
            intro hq11
            have hne1 : arc₁.length ≠ 1 := by
              intro h1
              apply hsub1 ⟨hq11, ?_⟩
              exact Walk.edges_takeUntil_subset_edges cₐ hw' (mem_edges_of_length_eq_one arc₁ h1)
            omega
          have harc2_len_ge : q₁.length = 1 → 2 ≤ arc₂.length := by
            intro hq11
            have hne1 : arc₂.length ≠ 1 := by
              intro h1
              apply hsub1 ⟨hq11, ?_⟩
              rw [Sym2.eq_swap]
              exact Walk.edges_dropUntil_subset_edges cₐ hw' (mem_edges_of_length_eq_one arc₂ h1)
            omega
          have hcyc1 : (q₁.append arc₂).IsCycle := by
            refine isCycle_append_chord hq1_path harc2_path haw (fun x hx1 hx2 =>
              harc_disj x hx1 (Walk.support_dropUntil_subset_support _ _ hx2)) ?_
            rcases eq_or_lt_of_le (by omega : 1 ≤ q₁.length) with h1 | h2
            · have := harc2_len_ge h1.symm; omega
            · omega
          have hs1 := hs.2 (q₁.append arc₂) hcyc1
          have hc_L : walkLength W.weight c = L := rfl
          rw [walkLength_append, hc_L] at hs1
          exact (min_le_left _ _).trans (by linarith)

private lemma circleDist_le_vertexDist [Finite V] [DecidableEq V] {v₀ : V}
    {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) {a b : V}
    (ha : a ∈ c.support) (hb : b ∈ c.support) :
    circleDist (walkLength W.weight c) (cycCoord c a) (cycCoord c b) ≤
      vertexDist W.graph W.weight a b := by
  obtain ⟨p, hp, hlen⟩ :=
    exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected a b)
  rw [← hlen]
  exact isCycle_chord_le hs p.length p rfl hp ha hb

private lemma walk_cons_tail_eq {u b₁ b₂ v : V} {h₁ : W.graph.Adj u b₁} {h₂ : W.graph.Adj u b₂}
    {p₁ : W.graph.Walk b₁ v} {p₂ : W.graph.Walk b₂ v}
    (he : Walk.cons h₁ p₁ = Walk.cons h₂ p₂) :
    ∃ hb : b₁ = b₂, p₁.copy hb rfl = p₂ := by
  cases he
  exact ⟨rfl, rfl⟩

private lemma walk_decomp_unique_of_isTrail :
    ∀ {u v : V} (p : W.graph.Walk u v), p.IsTrail →
      ∀ {u₁ v₁ u₂ v₂ : V} (q₁ : W.graph.Walk u u₁) (r₁ : W.graph.Walk v₁ v)
        (h₁ : W.graph.Adj u₁ v₁) (q₂ : W.graph.Walk u u₂) (r₂ : W.graph.Walk v₂ v)
        (h₂ : W.graph.Adj u₂ v₂),
        p = q₁.append (.cons h₁ r₁) → p = q₂.append (.cons h₂ r₂) →
        s(u₁, v₁) = s(u₂, v₂) → u₁ = u₂ ∧ v₁ = v₂ ∧ walkLength W.weight q₁ = walkLength W.weight q₂
  | _, _, .nil, _, _, _, _, _, .nil, _, _, _, _, _, hp1, _, _ => by
    rw [Walk.nil_append] at hp1
    exact absurd hp1 (fun h => by cases h)
  | _, _, .nil, _, _, _, _, _, .cons _ _, _, _, _, _, _, hp1, _, _ => by
    rw [Walk.cons_append] at hp1
    exact absurd hp1 (fun h => by cases h)
  | u, v, .cons (v := b) hadj p', ht, u₁, v₁, u₂, v₂, q₁, r₁, h₁, q₂, r₂, h₂, hp1, hp2, hedge => by
    cases q₁ with
    | nil =>
      cases q₂ with
      | nil =>
        rw [Walk.nil_append] at hp1 hp2
        obtain ⟨hv, _⟩ := walk_cons_tail_eq (hp1.symm.trans hp2)
        exact ⟨rfl, hv, rfl⟩
      | cons hadj2 q₂' =>
        exfalso
        rename_i w₂
        rw [Walk.nil_append] at hp1
        rw [Walk.cons_append] at hp2
        have hp_eq := hp1.symm.trans hp2
        have hnd := ht.edges_nodup
        rw [hp2, Walk.edges_cons, List.nodup_cons] at hnd
        have hmem : s(u, v₁) ∈ (q₂'.append (Walk.cons h₂ r₂)).edges := by
          rw [hedge, Walk.edges_append, List.mem_append, Walk.edges_cons]
          exact Or.inr List.mem_cons_self
        have heq : s(u, w₂) = s(u, v₁) := by
          have hed := congrArg Walk.edges hp_eq
          simp only [Walk.edges_cons, List.cons.injEq] at hed
          exact hed.1.symm
        exact hnd.1 (heq ▸ hmem)
    | cons hadj1 q₁' =>
      cases q₂ with
      | nil =>
        exfalso
        rename_i w₁
        rw [Walk.nil_append] at hp2
        rw [Walk.cons_append] at hp1
        have hp_eq := hp2.symm.trans hp1
        have hnd := ht.edges_nodup
        rw [hp1, Walk.edges_cons, List.nodup_cons] at hnd
        have hmem : s(u, v₂) ∈ (q₁'.append (Walk.cons h₁ r₁)).edges := by
          rw [← hedge, Walk.edges_append, List.mem_append, Walk.edges_cons]
          exact Or.inr List.mem_cons_self
        have heq : s(u, w₁) = s(u, v₂) := by
          have hed := congrArg Walk.edges hp_eq
          simp only [Walk.edges_cons, List.cons.injEq] at hed
          exact hed.1.symm
        exact hnd.1 (heq ▸ hmem)
      | cons hadj2 q₂' =>
        rw [Walk.cons_append] at hp1 hp2
        obtain ⟨hb1, hp1'⟩ := walk_cons_tail_eq hp1
        obtain ⟨hb2, hp2'⟩ := walk_cons_tail_eq hp2
        subst hb1 hb2
        rw [Walk.copy_rfl_rfl] at hp1' hp2'
        obtain ⟨hu, hv, hlen⟩ :=
          walk_decomp_unique_of_isTrail p' ht.of_cons q₁' r₁ h₁ q₂' r₂ h₂ hp1' hp2' hedge
        refine ⟨hu, hv, ?_⟩
        simp only [walkLength_cons, hlen]

theorem circleMap_dist_eq_circleDist [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) (s₁ s₂ : ℝ) :
    Dist.dist (circleMap hs.1 s₁) (circleMap hs.1 s₂) =
      circleDist (walkLength W.weight c) s₁ s₂ := by
  classical
  refine le_antisymm (circleMap_dist_le_circleDist hs.1 s₁ s₂) ?_
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  have decomp : ∀ s : ℝ, ∃ (d : W.graph.Dart) (q₁ : W.graph.Walk v₀ d.fst)
      (q₂ : W.graph.Walk d.snd v₀) (hadj : W.graph.Adj d.fst d.snd) (t : unitInterval),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ c = q₁.append (.cons hadj q₂) ∧
      circleMap hs.1 s = edgePoint d t ∧
      circleDist L s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) = 0 ∧
      d.fst ∈ c.support ∧ d.snd ∈ c.support ∧
      circleDist L (walkLength W.weight q₁) (cycCoord c d.fst) = 0 ∧
      circleDist L (walkLength W.weight q₁ + W.weight d.edge) (cycCoord c d.snd) = 0 := by
    intro s
    let r := Int.fract (s / L) * L
    have hr0 : 0 ≤ r := mul_nonneg (Int.fract_nonneg _) hL.le
    have hrl : r < L := (mul_lt_iff_lt_one_left hL).mpr (Int.fract_lt_one _)
    obtain ⟨d, q₁, q₂, hadj, t, hd, hc_eq, hpt, hr_eq⟩ :=
      walkPoint_dart_decomp c hs.1.not_nil hr0 hrl.le
    have hfst : d.fst ∈ c.support :=
      hc_eq ▸ Walk.support_subset_support_append_left _ _ q₁.end_mem_support
    have hsnd : d.snd ∈ c.support := by
      have : d.snd ∈ (Walk.cons hadj q₂).support :=
        List.mem_cons_of_mem _ (Walk.start_mem_support _)
      exact hc_eq ▸ Walk.support_subset_support_append_right _ _ this
    have hs_r : s = r + (⌊s / L⌋ : ℝ) * L := by
      dsimp only [r]
      rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
      ring
    have hcd_s : circleDist L s (walkLength W.weight q₁ + (t : ℝ) * W.weight d.edge) = 0 := by
      rw [← hr_eq, hs_r, circleDist_add_int_left hL, circleDist_self hL]
    have hcd_fst : circleDist L (walkLength W.weight q₁) (cycCoord c d.fst) = 0 := by
      rw [cycCoord_append_eq hs.1 hc_eq Walk.not_nil_cons, circleDist_self hL]
    have hcd_snd : circleDist L (walkLength W.weight q₁ + W.weight d.edge) (cycCoord c d.snd) =
        0 := by
      cases q₂ with
      | nil =>
        have hlen_tot : walkLength W.weight q₁ + W.weight d.edge = L := by
          have h := congrArg (walkLength W.weight) hc_eq
          rw [walkLength_append, walkLength_cons, walkLength_nil, add_zero] at h
          have hwe : W.weight s(d.fst, d.snd) = W.weight d.edge := rfl
          rw [hwe] at h
          exact h.symm
        have hc0 : cycCoord c d.snd = 0 := by
          rw [cycCoord_of_mem (Walk.start_mem_support c), Walk.takeUntil_first, walkLength_nil]
        rw [hlen_tot, hc0, ← circleDist_add_int_right hL L 0 1, zero_add, Int.cast_one,
          one_mul, circleDist_self hL]
      | cons hadj2 q₂' =>
        have hc_eq2 : c = (q₁.concat hadj).append (Walk.cons hadj2 q₂') := by
          rw [hc_eq, Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append,
            Walk.nil_append]
        have hlen2 : walkLength W.weight (q₁.concat hadj) =
            walkLength W.weight q₁ + W.weight d.edge := by
          rw [Walk.concat_eq_append, walkLength_append, walkLength_cons, walkLength_nil,
            add_zero]
          rfl
        rw [cycCoord_append_eq hs.1 hc_eq2 Walk.not_nil_cons, hlen2, circleDist_self hL]
    exact ⟨d, q₁, q₂, hadj, t, hd, hc_eq, hpt, hcd_s, hfst, hsnd, hcd_fst, hcd_snd⟩
  obtain ⟨d₁, q₁₁, q₁₂, h₁, t₁, hd₁, hc₁, hpt₁, hcds₁, hfst₁, hsnd₁, hcdf₁, hcdsnd₁⟩ := decomp s₁
  obtain ⟨d₂, q₂₁, q₂₂, h₂, t₂, hd₂, hc₂, hpt₂, hcds₂, hfst₂, hsnd₂, hcdf₂, hcdsnd₂⟩ := decomp s₂
  have hpair : ∀ u₁ ∈ ({d₁.fst, d₁.snd} : Set V), ∀ u₂ ∈ ({d₂.fst, d₂.snd} : Set V),
      circleDist L s₁ s₂ ≤
        (if u₁ = d₁.fst then (t₁ : ℝ) * W.weight d₁.edge else (1 - (t₁ : ℝ)) * W.weight d₁.edge) +
        vertexDist W.graph W.weight u₁ u₂ +
        (if u₂ = d₂.fst then (t₂ : ℝ) * W.weight d₂.edge
          else (1 - (t₂ : ℝ)) * W.weight d₂.edge) := by
    intro u₁ hu₁ u₂ hu₂
    have h1_bound : circleDist L s₁ (cycCoord c u₁) ≤
        (if u₁ = d₁.fst then (t₁ : ℝ) * W.weight d₁.edge else (1 - (t₁ : ℝ)) * W.weight d₁.edge) ∧
        u₁ ∈ c.support := by
      rcases hu₁ with rfl | rfl
      · refine ⟨?_, hfst₁⟩
        split_ifs with h
        · refine (circleDist_triangle hL _
              (walkLength W.weight q₁₁ + (t₁ : ℝ) * W.weight d₁.edge) _).trans ?_
          rw [hcds₁, zero_add]
          refine (circleDist_triangle hL _ (walkLength W.weight q₁₁) _).trans ?_
          rw [hcdf₁, add_zero]
          refine (circleDist_le_abs hL _ _).trans_eq ?_
          rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg t₁.2.1 (W.dart_weight_pos d₁).le)]
        · exact absurd rfl h
      · refine ⟨?_, hsnd₁⟩
        split_ifs with h
        · exact absurd h d₁.snd_ne_fst
        · refine (circleDist_triangle hL _
              (walkLength W.weight q₁₁ + (t₁ : ℝ) * W.weight d₁.edge) _).trans ?_
          rw [hcds₁, zero_add]
          refine (circleDist_triangle hL _ (walkLength W.weight q₁₁ + W.weight d₁.edge) _).trans ?_
          rw [hcdsnd₁, add_zero]
          refine (circleDist_le_abs hL _ _).trans_eq ?_
          have hneg : (walkLength W.weight q₁₁ + (t₁ : ℝ) * W.weight d₁.edge) -
              (walkLength W.weight q₁₁ + W.weight d₁.edge) =
              -((1 - (t₁ : ℝ)) * W.weight d₁.edge) := by ring
          rw [hneg, abs_neg,
            abs_of_nonneg (mul_nonneg (unitInterval.one_sub_nonneg t₁) (W.dart_weight_pos d₁).le)]
    have h2_bound : circleDist L (cycCoord c u₂) s₂ ≤
        (if u₂ = d₂.fst then (t₂ : ℝ) * W.weight d₂.edge else (1 - (t₂ : ℝ)) * W.weight d₂.edge) ∧
        u₂ ∈ c.support := by
      rcases hu₂ with rfl | rfl
      · refine ⟨?_, hfst₂⟩
        split_ifs with h
        · rw [circleDist_symm hL]
          refine (circleDist_triangle hL _
              (walkLength W.weight q₂₁ + (t₂ : ℝ) * W.weight d₂.edge) _).trans ?_
          rw [hcds₂, zero_add]
          refine (circleDist_triangle hL _ (walkLength W.weight q₂₁) _).trans ?_
          rw [hcdf₂, add_zero]
          refine (circleDist_le_abs hL _ _).trans_eq ?_
          rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg t₂.2.1 (W.dart_weight_pos d₂).le)]
        · exact absurd rfl h
      · refine ⟨?_, hsnd₂⟩
        split_ifs with h
        · exact absurd h d₂.snd_ne_fst
        · rw [circleDist_symm hL]
          refine (circleDist_triangle hL _
              (walkLength W.weight q₂₁ + (t₂ : ℝ) * W.weight d₂.edge) _).trans ?_
          rw [hcds₂, zero_add]
          refine (circleDist_triangle hL _ (walkLength W.weight q₂₁ + W.weight d₂.edge) _).trans ?_
          rw [hcdsnd₂, add_zero]
          refine (circleDist_le_abs hL _ _).trans_eq ?_
          have hneg : (walkLength W.weight q₂₁ + (t₂ : ℝ) * W.weight d₂.edge) -
              (walkLength W.weight q₂₁ + W.weight d₂.edge) =
              -((1 - (t₂ : ℝ)) * W.weight d₂.edge) := by ring
          rw [hneg, abs_neg,
            abs_of_nonneg (mul_nonneg (unitInterval.one_sub_nonneg t₂) (W.dart_weight_pos d₂).le)]
    have hvd := circleDist_le_vertexDist hs h1_bound.2 h2_bound.2
    linarith [h1_bound.1, h2_bound.1,
      circleDist_triangle hL s₁ (cycCoord c u₁) s₂,
      circleDist_triangle hL (cycCoord c u₁) (cycCoord c u₂) s₂]
  have hff := hpair d₁.fst (Or.inl rfl) d₂.fst (Or.inl rfl)
  have hfs := hpair d₁.fst (Or.inl rfl) d₂.snd (Or.inr rfl)
  have hsf := hpair d₁.snd (Or.inr rfl) d₂.fst (Or.inl rfl)
  have hss := hpair d₁.snd (Or.inr rfl) d₂.snd (Or.inr rfl)
  simp only [↓reduceIte, d₁.snd_ne_fst, d₂.snd_ne_fst] at hff hfs hsf hss
  rw [hpt₁, hpt₂]
  by_cases he : d₁.edge = d₂.edge
  · have he' : s(d₁.fst, d₁.snd) = s(d₂.fst, d₂.snd) := he
    obtain ⟨hu, hv, hq_len⟩ :=
      walk_decomp_unique_of_isTrail c hs.1.isTrail q₁₁ q₁₂ h₁ q₂₁ q₂₂ h₂ hc₁ hc₂ he'
    have hd_eq : d₁ = d₂ := by
      cases d₁; cases d₂; congr 1; exact Prod.ext hu hv
    have hdir : circleDist L s₁ s₂ ≤ |(t₁ : ℝ) - t₂| * W.weight d₁.edge := by
      refine (circleDist_triangle hL _
          (walkLength W.weight q₁₁ + (t₁ : ℝ) * W.weight d₁.edge) _).trans ?_
      rw [hcds₁, zero_add]
      refine (circleDist_triangle hL _
          (walkLength W.weight q₂₁ + (t₂ : ℝ) * W.weight d₂.edge) _).trans ?_
      rw [circleDist_symm hL _ s₂, hcds₂, add_zero]
      refine (circleDist_le_abs hL _ _).trans_eq ?_
      rw [hq_len, hd_eq, add_sub_add_left_eq_sub, ← sub_mul, abs_mul,
        abs_of_nonneg (W.dart_weight_pos d₂).le]
    rw [hd_eq, dist_edgePoint_edgePoint_same]
    refine le_min (hdir.trans_eq (by rw [hd_eq])) (le_min (le_min ?_ ?_) (le_min ?_ ?_))
    · simpa [hd_eq] using hff
    · simpa [hd_eq] using hfs
    · simpa [hd_eq] using hsf
    · simpa [hd_eq] using hss
  · rw [dist_edgePoint_edgePoint_of_edge_ne he]
    exact le_min (le_min hff hfs) (le_min hsf hss)

theorem circleMap_dist_eq_of_le [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) {s₁ s₂ : ℝ} (hle : |s₁ - s₂| ≤ walkLength W.weight c / 2) :
    Dist.dist (circleMap hs.1 s₁) (circleMap hs.1 s₂) = |s₁ - s₂| := by
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hs.1.not_nil
  rw [circleMap_dist_eq_circleDist hs s₁ s₂, circleDist_eq_abs_of_abs_le hL hle]

theorem circleMap_injOn [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) :
    Set.InjOn (circleMap hs.1) (Set.Ico 0 (walkLength W.weight c)) := by
  intro s₁ hs₁ s₂ hs₂ heq
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hs.1.not_nil
  have hcd0 : circleDist (walkLength W.weight c) s₁ s₂ = 0 := by
    rw [← circleMap_dist_eq_circleDist hs s₁ s₂, heq, _root_.dist_self]
  wlog hle : s₁ ≤ s₂ generalizing s₁ s₂
  · exact (this hs₂ hs₁ heq.symm ((circleDist_symm hL s₁ s₂).symm.trans hcd0)
      (le_of_not_ge hle)).symm
  have hu0 : 0 ≤ (s₂ - s₁) / walkLength W.weight c := div_nonneg (sub_nonneg.mpr hle) hL.le
  have hu1 : (s₂ - s₁) / walkLength W.weight c < 1 := by
    rw [div_lt_one hL]
    linarith [hs₁.1, hs₂.2]
  have hfl : ⌊(s₂ - s₁) / walkLength W.weight c⌋ = 0 :=
    Int.floor_eq_iff.mpr ⟨by simpa using hu0, by simpa using hu1⟩
  have hf : Int.fract ((s₂ - s₁) / walkLength W.weight c) =
      (s₂ - s₁) / walkLength W.weight c := by
    rw [Int.fract, hfl, Int.cast_zero, sub_zero]
  dsimp only [circleDist] at hcd0
  rw [hf, div_mul_cancel₀ _ hL.ne', one_sub_mul, div_mul_cancel₀ _ hL.ne'] at hcd0
  rcases min_choice (s₂ - s₁) (walkLength W.weight c - (s₂ - s₁)) with hm | hm
  · linarith
  · exfalso
    have : walkLength W.weight c = s₂ - s₁ := by linarith
    linarith [hs₁.1, hs₂.2]

end ShortestCycleIsometry

/-! ### Pure cycle graphs and local dichotomy along a cycle -/

section CycleStructure

private lemma cycleGraph_adj_eq_add_or_sub {n : ℕ} {a b : Fin (n + 3)}
    (h : (cycleGraph (n + 3)).Adj a b) : b = a - 1 ∨ b = a + 1 := by
  rw [cycleGraph_adj] at h
  rcases h with h | h
  · left
    exact eq_sub_of_add_eq ((add_comm b 1).trans (sub_eq_iff_eq_add.mp h).symm)
  · right
    exact (eq_add_of_sub_eq h).trans (add_comm 1 a)

private lemma cycleGraph_support_of_isCycle {n : ℕ} (e : W.graph ≃g cycleGraph (n + 3))
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    (∀ v : V, v ∈ c.support) ∧ ∀ {u v : V}, W.graph.Adj u v → s(u, v) ∈ c.edges := by
  classical
  have hstep : ∀ x ∈ c.support, ∀ y : V, W.graph.Adj x y → s(x, y) ∈ c.edges := by
    intro x hx y hadj
    let cₓ := c.rotate x hx
    have hcₓ : cₓ.IsCycle := (c.isCycle_rotate hx).mpr hc
    have h1 : W.graph.Adj x cₓ.snd := Walk.adj_snd hcₓ.not_nil
    have h2 : W.graph.Adj x cₓ.penultimate := by
      have : (W.graph).Adj cₓ.penultimate x := Walk.adj_penultimate hcₓ.not_nil
      exact this.symm
    have hne : cₓ.snd ≠ cₓ.penultimate := hcₓ.snd_ne_penultimate
    have ha1 := cycleGraph_adj_eq_add_or_sub (e.map_adj_iff.mpr h1)
    have ha2 := cycleGraph_adj_eq_add_or_sub (e.map_adj_iff.mpr h2)
    have ha3 := cycleGraph_adj_eq_add_or_sub (e.map_adj_iff.mpr hadj)
    have hy_mem : y = cₓ.snd ∨ y = cₓ.penultimate := by
      rcases ha1 with h1' | h1' <;> rcases ha2 with h2' | h2'
      · exact absurd (e.injective (h1'.trans h2'.symm)) hne
      · rcases ha3 with h3' | h3'
        · left; exact e.injective (h3'.trans h1'.symm)
        · right; exact e.injective (h3'.trans h2'.symm)
      · rcases ha3 with h3' | h3'
        · right; exact e.injective (h3'.trans h2'.symm)
        · left; exact e.injective (h3'.trans h1'.symm)
      · exact absurd (e.injective (h1'.trans h2'.symm)) hne
    have hmem_cx : s(x, y) ∈ cₓ.edges := by
      rcases hy_mem with rfl | rfl
      · exact Walk.mk_start_snd_mem_edges hcₓ.not_nil
      · rw [Sym2.eq_swap]
        exact Walk.mk_penultimate_end_mem_edges hcₓ.not_nil
    exact (c.rotate_edges x hx).perm.mem_iff.mp hmem_cx
  have hsup : ∀ v : V, v ∈ c.support := by
    intro v
    obtain ⟨p⟩ := W.connected v₀ v
    suffices h : ∀ {u w : V} (q : W.graph.Walk u w), u ∈ c.support → w ∈ c.support from
      h p (Walk.start_mem_support c)
    intro u w q hu
    induction q with
    | nil => exact hu
    | @cons a b d hadj q' ih =>
      have hed := hstep a hu b hadj
      exact ih (Walk.snd_mem_support_of_mem_edges _ hed)
  refine ⟨hsup, fun {u v} hadj => hstep u (hsup u) v hadj⟩

private lemma mem_darts_iff_exists_append {u v : V} {p : W.graph.Walk u v} {d : W.graph.Dart} :
    d ∈ p.darts ↔ ∃ (q₁ : W.graph.Walk u d.fst) (q₂ : W.graph.Walk d.snd v)
      (hadj : W.graph.Adj d.fst d.snd),
      d = ⟨(d.fst, d.snd), hadj⟩ ∧ p = q₁.append (.cons hadj q₂) := by
  constructor
  · induction p with
    | nil => simp
    | @cons a b c hadj p' ih =>
      intro hd
      rw [Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd'
      · exact ⟨.nil, p', hadj, rfl, rfl⟩
      · obtain ⟨q₁, q₂, hadj', hd_eq, hp'⟩ := ih hd'
        exact ⟨.cons hadj q₁, q₂, hadj', hd_eq, hp' ▸ (Walk.cons_append hadj q₁ _).symm⟩
  · rintro ⟨q₁, q₂, hadj, hd_eq, rfl⟩
    rw [Walk.darts_append, List.mem_append, Walk.darts_cons]
    exact Or.inr (List.mem_cons.mpr (Or.inl hd_eq))

theorem circleMap_surjective_of_cycleGraph {n : ℕ}
    (e : W.graph ≃g cycleGraph (n + 3)) {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) :
    Function.Surjective (circleMap hc) := by
  classical
  have hL : 0 < walkLength W.weight c := walkLength_pos_of_not_nil hc.not_nil
  obtain ⟨hsup, hedges⟩ := cycleGraph_support_of_isCycle e hc
  intro p
  induction p using ind with
  | vertex v =>
    have hv := hsup v
    refine ⟨cycCoord c v, ?_⟩
    rw [cycCoord_of_mem hv]
    have hle : walkLength W.weight (c.takeUntil v hv) ≤ walkLength W.weight c := by
      have := congrArg (walkLength W.weight) (c.take_spec hv)
      rw [walkLength_append] at this
      linarith [walkLength_nonneg W.weight W.weight_nonneg (c.dropUntil v hv)]
    rw [circleMap_eq_walkPoint hc (walkLength_nonneg W.weight W.weight_nonneg _) hle]
    conv_lhs =>
      arg 1
      rw [← c.take_spec hv]
    rw [← add_zero (walkLength W.weight (c.takeUntil v hv)),
      walkPoint_append_of_ge _ _ le_rfl, walkPoint_nonpos _ le_rfl]
  | edgePoint d t ht0 ht1 =>
    have hed : d.edge ∈ c.edges := hedges d.adj
    rw [Walk.edges, List.mem_map] at hed
    obtain ⟨d', hd'_mem, hd'_edge⟩ := hed
    obtain ⟨q₁, q₂, hadj, hd'_eq, hc_eq⟩ := mem_darts_iff_exists_append.mp hd'_mem
    have hw_eq : W.weight d'.edge = W.weight d.edge := congrArg W.weight hd'_edge
    have hsum_le : walkLength W.weight q₁ + W.weight d'.edge ≤ walkLength W.weight c := by
      have := congrArg (walkLength W.weight) hc_eq
      rw [walkLength_append, walkLength_cons] at this
      have hq2_nn : 0 ≤ walkLength W.weight q₂ := walkLength_nonneg W.weight W.weight_nonneg q₂
      have hw' : W.weight s(d'.fst, d'.snd) = W.weight d'.edge := rfl
      linarith
    rcases (dart_edge_eq_iff d' d).mp hd'_edge with rfl | hsymm
    · refine ⟨walkLength W.weight q₁ + (t : ℝ) * W.weight d'.edge, ?_⟩
      have hs0 : 0 ≤ walkLength W.weight q₁ + (t : ℝ) * W.weight d'.edge :=
        add_nonneg (walkLength_nonneg _ W.weight_nonneg _)
          (mul_nonneg t.2.1 (W.dart_weight_pos d').le)
      have hsl : walkLength W.weight q₁ + (t : ℝ) * W.weight d'.edge ≤ walkLength W.weight c := by
        nlinarith [t.2.2, (W.dart_weight_pos d').le]
      rw [circleMap_eq_walkPoint hc hs0 hsl]
      conv_lhs => arg 1; rw [hc_eq]
      rw [walkPoint_append_of_ge _ _ (mul_nonneg t.2.1 (W.dart_weight_pos d').le)]
      exact walkPoint_cons_mul hadj q₂ d' hd'_eq t
    · let t' := unitInterval.symm t
      refine ⟨walkLength W.weight q₁ + (t' : ℝ) * W.weight d'.edge, ?_⟩
      have hs0 : 0 ≤ walkLength W.weight q₁ + (t' : ℝ) * W.weight d'.edge :=
        add_nonneg (walkLength_nonneg _ W.weight_nonneg _)
          (mul_nonneg t'.2.1 (W.dart_weight_pos d').le)
      have hsl : walkLength W.weight q₁ + (t' : ℝ) * W.weight d'.edge ≤ walkLength W.weight c := by
        nlinarith [t'.2.2, (W.dart_weight_pos d').le]
      rw [circleMap_eq_walkPoint hc hs0 hsl]
      conv_lhs => arg 1; rw [hc_eq]
      rw [walkPoint_append_of_ge _ _ (mul_nonneg t'.2.1 (W.dart_weight_pos d').le),
        walkPoint_cons_mul hadj q₂ d' hd'_eq t', hsymm, edgePoint_symm d t]

private lemma circleMap_rotate_eq [DecidableEq V] {v₀ v : V} {c : W.graph.Walk v₀ v₀}
    (hc : c.IsCycle) (hv : v ∈ c.support) (r : ℝ) :
    circleMap hc (cycCoord c v + r) = circleMap ((c.isCycle_rotate hv).mpr hc) r := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let c_v := c.rotate v hv
  have hc_v : c_v.IsCycle := (c.isCycle_rotate hv).mpr hc
  have hLv : walkLength W.weight c_v = L := walkLength_perm_eq W.weight (c.rotate_edges v hv).perm
  have hshift : ∀ r' : ℝ, 0 ≤ r' → r' < L →
      circleMap hc (cycCoord c v + r') = circleMap hc_v r' := by
    intro r' hr0 hrL
    let c₁ := c.takeUntil v hv
    let c₂ := c.dropUntil v hv
    have hc_eq : c₁.append c₂ = c := c.take_spec hv
    have hcv_eq : c_v = c₂.append c₁ := rfl
    have hsum : walkLength W.weight c₁ + walkLength W.weight c₂ = L := by
      rw [← walkLength_append, hc_eq]
    have hcv_coord : cycCoord c v = walkLength W.weight c₁ := cycCoord_of_mem hv
    have hc₁_le : walkLength W.weight c₁ ≤ L := by
      linarith [walkLength_nonneg W.weight W.weight_nonneg c₂]
    rw [circleMap_eq_walkPoint hc_v hr0 (hrL.le.trans hLv.symm.le)]
    by_cases hsum_lt : walkLength W.weight c₁ + r' < L
    · have hr'_le : r' ≤ walkLength W.weight c₂ := by linarith
      rw [hcv_coord,
        circleMap_eq_walkPoint hc (by linarith [walkLength_nonneg W.weight W.weight_nonneg c₁])
          hsum_lt.le]
      conv_lhs => arg 1; rw [← hc_eq]
      rw [walkPoint_append_of_ge c₁ c₂ hr0, hcv_eq, walkPoint_append_of_le c₂ c₁ hr'_le]
    · have hc2_le : walkLength W.weight c₂ ≤ r' := by linarith
      have hr'_sub0 : 0 ≤ r' - walkLength W.weight c₂ := sub_nonneg.mpr hc2_le
      have hr'_sub_le : r' - walkLength W.weight c₂ ≤ walkLength W.weight c₁ := by linarith
      have hcoord_sub : cycCoord c v + r' = (r' - walkLength W.weight c₂) + (1 : ℤ) * L := by
        rw [hcv_coord]
        push_cast
        linarith
      rw [hcoord_sub, circleMap_add_int_mul hc _ 1,
        circleMap_eq_walkPoint hc hr'_sub0 (hr'_sub_le.trans hc₁_le)]
      conv_lhs => arg 1; rw [← hc_eq]
      rw [walkPoint_append_of_le c₁ c₂ hr'_sub_le, hcv_eq]
      have hrew : r' = walkLength W.weight c₂ + (r' - walkLength W.weight c₂) := by ring
      conv_rhs => rw [hrew]
      rw [walkPoint_append_of_ge c₂ c₁ hr'_sub0]
  let q := Int.fract (r / L) * L
  have hq0 : 0 ≤ q := mul_nonneg (Int.fract_nonneg _) hL.le
  have hqL : q < L := (mul_lt_iff_lt_one_left hL).mpr (Int.fract_lt_one _)
  have hr_eq : r = q + (⌊r / L⌋ : ℝ) * L := by
    dsimp only [q]
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  have hr_lhs : circleMap hc (cycCoord c v + r) = circleMap hc (cycCoord c v + q) := by
    rw [hr_eq, ← add_assoc, circleMap_add_int_mul hc _ ⌊r / L⌋]
  have hr_rhs : circleMap hc_v r = circleMap hc_v q := by
    have hper := circleMap_add_int_mul hc_v q ⌊r / L⌋
    rw [hLv] at hper
    rw [hr_eq, hper]
  rw [hr_lhs, hr_rhs]
  exact hshift q hq0 hqL

/-- Every parameter `s : ℝ` along a cycle `c` maps either to the interior of a unique cycle dart
(where `circleMap hc` is locally affine along that dart) or to a vertex `v ∈ c.support` whose
incoming and outgoing cycle darts carry distinct edges. -/
theorem circleMap_local_dichotomy {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle) (s : ℝ) :
    (∃ (d : W.graph.Dart) (t δ : ℝ), d ∈ c.darts ∧ 0 < t ∧ t < 1 ∧ 0 < δ ∧
      ∀ r ∈ Set.Icc (-δ) δ, 0 < t + r / W.weight d.edge ∧ t + r / W.weight d.edge < 1 ∧
        ∃ h0 : 0 ≤ t + r / W.weight d.edge, ∃ h1 : t + r / W.weight d.edge ≤ 1,
          circleMap hc (s + r) = edgePoint d ⟨t + r / W.weight d.edge, h0, h1⟩) ∨
    (∃ (v : V) (d₁ d₂ : W.graph.Dart) (δ : ℝ),
      v ∈ c.support ∧ d₁.fst = v ∧ d₂.fst = v ∧ d₁.edge ≠ d₂.edge ∧
      d₁.edge ∈ c.edges ∧ d₂.edge ∈ c.edges ∧ circleMap hc s = vertex v ∧ 0 < δ ∧
      ∀ r ∈ Set.Ioc 0 δ, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
        ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
          (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
          circleMap hc (s - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
          circleMap hc (s + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩) := by
  classical
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hc.not_nil
  let r₀ := Int.fract (s / L) * L
  have hr₀0 : 0 ≤ r₀ := mul_nonneg (Int.fract_nonneg _) hL.le
  have hr₀L : r₀ < L := (mul_lt_iff_lt_one_left hL).mpr (Int.fract_lt_one _)
  obtain ⟨d, q₁, q₂, hadj, t, hd, hc_eq, hpt, hr_eq⟩ :=
    walkPoint_dart_decomp c hc.not_nil hr₀0 hr₀L.le
  have hwpos : 0 < W.weight d.edge := W.dart_weight_pos d
  have hs_r₀ : s = r₀ + (⌊s / L⌋ : ℝ) * L := by
    dsimp only [r₀]
    rw [Int.fract, sub_mul, div_mul_cancel₀ _ hL.ne']
    ring
  have vertex_case : ∀ (v : V) (hv : v ∈ c.support) (k : ℤ), s = cycCoord c v + (k : ℝ) * L →
      ∃ (v' : V) (d₁ d₂ : W.graph.Dart) (δ : ℝ),
        v' ∈ c.support ∧ d₁.fst = v' ∧ d₂.fst = v' ∧ d₁.edge ≠ d₂.edge ∧
        d₁.edge ∈ c.edges ∧ d₂.edge ∈ c.edges ∧ circleMap hc s = vertex v' ∧ 0 < δ ∧
        ∀ r ∈ Set.Ioc 0 δ, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
          ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
            (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
            circleMap hc (s - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
            circleMap hc (s + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩ := by
    intro v hv k hcoord
    let c_v := c.rotate v hv
    have hc_v : c_v.IsCycle := (c.isCycle_rotate hv).mpr hc
    have hLv : walkLength W.weight c_v = L := walkLength_perm_eq W.weight (c.rotate_edges v hv).perm
    cases hc_v_c : c_v with
    | nil =>
      exfalso
      have := hc_v.not_nil
      rw [hc_v_c] at this
      exact this .nil
    | @cons _ b₀ _ hadj2 q_v =>
      let d₂ : W.graph.Dart := ⟨(v, b₀), hadj2⟩
      have hq_v_nn : ¬ q_v.Nil := Walk.not_nil_of_isCycle_cons (hc_v_c ▸ hc_v)
      obtain ⟨d₁, hd₁_fst, hd₁_edge, hlast⟩ := walkPoint_last_sub q_v hq_v_nn
      have hnd := (hc_v_c ▸ hc_v).isTrail.edges_nodup
      rw [Walk.edges_cons, List.nodup_cons] at hnd
      have hd₁₂ : d₁.edge ≠ d₂.edge := fun he => by
        rw [he] at hd₁_edge
        exact hnd.1 hd₁_edge
      have hd₁_c : d₁.edge ∈ c.edges := by
        refine (c.rotate_edges v hv).perm.mem_iff.mp ?_
        change d₁.edge ∈ c_v.edges
        rw [hc_v_c, Walk.edges_cons]
        exact List.mem_cons_of_mem _ hd₁_edge
      have hd₂_c : d₂.edge ∈ c.edges := by
        refine (c.rotate_edges v hv).perm.mem_iff.mp ?_
        change d₂.edge ∈ c_v.edges
        rw [hc_v_c, Walk.edges_cons]
        exact List.mem_cons_self
      let δ := min (W.weight d₁.edge) (W.weight d₂.edge) / 2
      have hw1 : 0 < W.weight d₁.edge := W.dart_weight_pos d₁
      have hw2 : 0 < W.weight d₂.edge := W.dart_weight_pos d₂
      have hδ : 0 < δ := by
        dsimp only [δ]
        positivity
      have hq_ge1 : W.weight d₁.edge ≤ walkLength W.weight q_v :=
        weight_le_walkLength_of_mem_edges q_v hd₁_edge
      have hs_v : circleMap hc s = vertex v := by
        rw [hcoord, circleMap_add_int_mul hc _ k, ← add_zero (cycCoord c v),
          circleMap_rotate_eq hc hv, circleMap_zero]
      refine ⟨v, d₁, d₂, δ, hv, hd₁_fst, rfl, hd₁₂, hd₁_c, hd₂_c, hs_v, hδ, fun r hr => ?_⟩
      dsimp only [δ, Set.mem_Ioc] at hr
      have hr1 : r < W.weight d₁.edge := by
        linarith [hr.1, hr.2, min_le_left (W.weight d₁.edge) (W.weight d₂.edge)]
      have hr2 : r < W.weight d₂.edge := by
        linarith [hr.1, hr.2, min_le_right (W.weight d₁.edge) (W.weight d₂.edge)]
      refine ⟨hr1, hr2, div_nonneg hr.1.le hw1.le, (div_le_one hw1).mpr hr1.le,
        div_nonneg hr.1.le hw2.le, (div_le_one hw2).mpr hr2.le, ?_, ?_⟩
      · have hsub_eq : s - r = cycCoord c v + (-r) + (k : ℝ) * L := by
          rw [hcoord]; ring
        rw [hsub_eq, circleMap_add_int_mul hc _ k, circleMap_rotate_eq hc hv,
          ← circleMap_add_int_mul hc_v (-r) 1, Int.cast_one, one_mul, hLv]
        have hL_tot : walkLength W.weight c_v = W.weight d₂.edge + walkLength W.weight q_v := by
          rw [hc_v_c, walkLength_cons]
          rfl
        have hlr0 : 0 ≤ -r + walkLength W.weight c_v := by linarith
        have hlrL : -r + walkLength W.weight c_v ≤ walkLength W.weight c_v := by linarith [hr.1]
        rw [← hLv, circleMap_eq_walkPoint hc_v hlr0 hlrL, neg_add_eq_sub, hc_v_c]
        have hgt : W.weight s(v, b₀) < walkLength W.weight (Walk.cons hadj2 q_v) - r := by
          rw [walkLength_cons]
          linarith
        have hwalk_step : walkPoint (Walk.cons hadj2 q_v)
            (walkLength W.weight (Walk.cons hadj2 q_v) - r) =
            walkPoint q_v (walkLength W.weight q_v - r) := by
          have hwe2 : W.weight s(v, b₀) = W.weight d₂.edge := rfl
          rw [walkLength_cons] at hgt ⊢
          rw [walkPoint_cons_of_gt hadj2 q_v d₂ rfl hgt, hwe2,
            add_sub_assoc, add_sub_cancel_left]
        rw [hwalk_step]
        exact hlast hr.1 hr1.le (div_nonneg hr.1.le hw1.le) ((div_le_one hw1).mpr hr1.le)
      · have hadd_eq : s + r = cycCoord c v + r + (k : ℝ) * L := by
          rw [hcoord]; ring
        rw [hadd_eq, circleMap_add_int_mul hc _ k, circleMap_rotate_eq hc hv]
        have hrL : r ≤ walkLength W.weight c_v := by
          rw [show walkLength W.weight c_v = W.weight d₂.edge + walkLength W.weight q_v by
            rw [hc_v_c, walkLength_cons]; rfl]
          linarith [walkLength_nonneg W.weight W.weight_nonneg q_v]
        rw [circleMap_eq_walkPoint hc_v hr.1.le hrL, hc_v_c]
        exact walkPoint_cons_of_le hadj2 q_v d₂ rfl hr.1.le hr2.le
          (div_nonneg hr.1.le hw2.le) ((div_le_one hw2).mpr hr2.le)
  by_cases ht0 : (t : ℝ) = 0
  · right
    have hv : d.fst ∈ c.support :=
      hc_eq ▸ Walk.support_subset_support_append_left _ _ q₁.end_mem_support
    have hcoord : s = cycCoord c d.fst + (⌊s / L⌋ : ℝ) * L := by
      conv_lhs => rw [hs_r₀]
      rw [hr_eq, ht0, zero_mul, add_zero, cycCoord_append_eq hc hc_eq Walk.not_nil_cons]
    exact vertex_case d.fst hv ⌊s / L⌋ hcoord
  · by_cases ht1 : (t : ℝ) = 1
    · right
      have hv : d.snd ∈ c.support := by
        have : d.snd ∈ (Walk.cons hadj q₂).support :=
          List.mem_cons_of_mem _ (Walk.start_mem_support _)
        exact hc_eq ▸ Walk.support_subset_support_append_right _ _ this
      cases hq2c : q₂ with
      | nil =>
        exfalso
        have hlen_c : L = walkLength W.weight q₁ + W.weight d.edge := by
          have h := congrArg (walkLength W.weight) hc_eq
          rw [hq2c, walkLength_append, walkLength_cons, walkLength_nil, add_zero] at h
          have hwe : W.weight s(d.fst, d.snd) = W.weight d.edge := rfl
          rw [hwe] at h
          exact h
        rw [ht1, one_mul] at hr_eq
        linarith
      | cons hadj2 q₂' =>
        have hc_eq2 : c = (q₁.concat hadj).append (Walk.cons hadj2 q₂') := by
          rw [hc_eq, hq2c, Walk.concat_eq_append, ← Walk.append_assoc, Walk.cons_append,
            Walk.nil_append]
        have hlen2 : walkLength W.weight (q₁.concat hadj) =
            walkLength W.weight q₁ + W.weight d.edge := by
          rw [Walk.concat_eq_append, walkLength_append, walkLength_cons, walkLength_nil,
            add_zero]
          rfl
        have hcoord : s = cycCoord c d.snd + (⌊s / L⌋ : ℝ) * L := by
          conv_lhs => rw [hs_r₀]
          rw [hr_eq, ht1, one_mul, ← hlen2, cycCoord_append_eq hc hc_eq2 Walk.not_nil_cons]
        exact vertex_case d.snd hv ⌊s / L⌋ hcoord
    · left
      have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      have ht_lt1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
      let δ := min ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge) / 2
      have hδ : 0 < δ := by
        dsimp only [δ]
        have : 0 < (1 - (t : ℝ)) * W.weight d.edge := mul_pos (sub_pos.mpr ht_lt1) hwpos
        positivity
      have hd_mem : d ∈ c.darts := mem_darts_iff_exists_append.mpr ⟨q₁, q₂, hadj, hd, hc_eq⟩
      refine ⟨d, (t : ℝ), δ, hd_mem, ht_pos, ht_lt1, hδ, fun r hr => ?_⟩
      dsimp only [δ, Set.mem_Icc] at hr
      have hr_lo : -((t : ℝ) * W.weight d.edge / 2) ≤ r := by
        linarith [hr.1, min_le_left ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge)]
      have hr_hi : r ≤ (1 - (t : ℝ)) * W.weight d.edge / 2 := by
        linarith [hr.2, min_le_right ((t : ℝ) * W.weight d.edge) ((1 - (t : ℝ)) * W.weight d.edge)]
      have hdiv_lo : 0 < (t : ℝ) + r / W.weight d.edge := by
        have h1 : -((t : ℝ) / 2) ≤ r / W.weight d.edge := (le_div_iff₀ hwpos).mpr (by linarith)
        linarith
      have hdiv_hi : (t : ℝ) + r / W.weight d.edge < 1 := by
        have h1 : r / W.weight d.edge ≤ (1 - (t : ℝ)) / 2 := (div_le_iff₀ hwpos).mpr (by linarith)
        linarith
      refine ⟨hdiv_lo, hdiv_hi, hdiv_lo.le, hdiv_hi.le, ?_⟩
      have hr₀_eq : r₀ + r =
          walkLength W.weight q₁ + ((t : ℝ) + r / W.weight d.edge) * W.weight d.edge := by
        rw [hr_eq, add_mul, div_mul_cancel₀ _ hwpos.ne']
        ring
      have hr₀_nn : 0 ≤ r₀ + r := by
        rw [hr₀_eq]
        exact add_nonneg (walkLength_nonneg _ W.weight_nonneg _) (mul_nonneg hdiv_lo.le hwpos.le)
      have hr₀_le : r₀ + r ≤ L := by
        have hlen_c : L = walkLength W.weight q₁ + W.weight d.edge + walkLength W.weight q₂ := by
          have h := congrArg (walkLength W.weight) hc_eq
          rw [walkLength_append, walkLength_cons] at h
          have hwe : W.weight s(d.fst, d.snd) = W.weight d.edge := rfl
          rw [hwe] at h
          linarith
        have hq2_nn : 0 ≤ walkLength W.weight q₂ := walkLength_nonneg W.weight W.weight_nonneg q₂
        rw [hr₀_eq]
        nlinarith
      have hs_add : s + r = (r₀ + r) + (⌊s / L⌋ : ℝ) * L := by linarith
      rw [hs_add, circleMap_add_int_mul hc _ ⌊s / L⌋, circleMap_eq_walkPoint hc hr₀_nn hr₀_le]
      conv_lhs => arg 1; rw [hc_eq]
      rw [hr₀_eq, walkPoint_append_of_ge _ _ (mul_nonneg hdiv_lo.le hwpos.le)]
      exact walkPoint_cons_mul hadj q₂ d hd ⟨(t : ℝ) + r / W.weight d.edge, hdiv_lo.le, hdiv_hi.le⟩

end CycleStructure

end MetricGraph

end SimpleGraph
