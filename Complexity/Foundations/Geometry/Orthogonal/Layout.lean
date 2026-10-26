/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Aesop
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Diagonal boxes and upper tracks for finite orthogonal layouts

Vertex `v` is centered at `(8v+4,8v+4)`. Its three ports leave to the left, up, and right,
and then rise on columns `8v+2`, `8v+4`, and `8v+6`. Edge `e` travels horizontally on row
`8n+2e+2`, above all `n` vertex boxes. All data are explicit finite lists.

## Main definitions

* `Cslib.Orthogonal.Layout.center`, `Cslib.Orthogonal.Layout.column`: vertex centers and ports.
* `Cslib.Orthogonal.Layout.route`: six listed points defining a five-segment route.

## Main results

* `Cslib.Orthogonal.Layout.route_orthogonal`: the routes are proper and orthogonal.
* `Cslib.Orthogonal.Layout.route_bounds`: explicit linear grid sides.
* `Cslib.Orthogonal.Layout.route_simple`: continuous simplicity.
* `Cslib.Orthogonal.Layout.route_contact`: shared endpoint or strict transverse crossing.
* `Cslib.Orthogonal.Layout.center_mem_support_iff`: no incidental vertex contacts.

## References

The box/track construction and its proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal.Layout

/-- Vertex center inside its diagonal box of side eight. -/
def center (v : ℕ) : Point := (8 * (v : ℤ) + 4, 8 * (v : ℤ) + 4)

/-- The three distinct upward port columns, ordered left to right. -/
def column (v : ℕ) (s : Fin 3) : ℤ := 8 * (v : ℤ) + 2 * (s : ℕ) + 2

/-- A two-unit initial step to the left, up, or right. -/
def elbow (v : ℕ) (s : Fin 3) : Point :=
  (column v s, (center v).2 + if s = 1 then 2 else 0)

/-- A private upper horizontal row for the indexed edge. -/
def track (n e : ℕ) : ℤ := 8 * (n : ℤ) + 2 * (e : ℤ) + 2

/-- A route from port `s` at vertex `u` to port `t` at vertex `v`, on edge track `e`.
The middle port has two consecutive collinear vertical segments. -/
def route (n e u v : ℕ) (s t : Fin 3) : Route :=
  [center u, elbow u s, (column u s, track n e),
    (column v t, track n e), elbow v t, center v]

/-- The local initial segment inside one vertex box. -/
def fan (v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) := segment (center v) (elbow v s)

/-- The upward part of a port, from its local elbow to the private edge track. -/
def stem (n e v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) :=
  segment (elbow v s) (column v s, track n e)

/-- The upper horizontal part of an edge. -/
def bridge (n e u v : ℕ) (s t : Fin 3) : Set (ℝ × ℝ) :=
  segment (column u s, track n e) (column v t, track n e)

/-- Decompose the continuous route into its two local fans, two stems, and upper bridge. -/
theorem support_route (n e u v : ℕ) (s t : Fin 3) :
    support (route n e u v s t) =
      fan u s ∪ stem n e u s ∪ bridge n e u v s t ∪ stem n e v t ∪ fan v t := by
  simp only [route, support_cons_cons]
  have hstem : segment (column v t, track n e) (elbow v t) = stem n e v t :=
    segment_symm ℝ _ _
  have hfan : segment (elbow v t) (center v) = fan v t := segment_symm ℝ _ _
  rw [hstem, hfan]
  ext p
  have hc : realPoint (center v) ∈ fan v t := left_mem_segment ℝ _ _
  simp only [fan, stem, bridge, support, List.consecutivePairs, List.tail_cons,
    List.zip_nil_right, List.not_mem_nil, List.mem_singleton,
    exists_eq_left, Set.mem_ofPred_eq, Set.mem_union] at *
  aesop

/-- Port columns uniquely identify both the vertex and the port. -/
theorem column_injective {u v : ℕ} {s t : Fin 3} (h : column u s = column v t) :
    u = v ∧ s = t := by
  have hs := s.isLt
  have ht := t.isLt
  simp only [column] at h
  have huv : u = v := by omega
  subst v
  exact ⟨rfl, Fin.ext (by omega)⟩

/-- All points of the local fan stay in its vertex's small diagonal box. -/
theorem fan_bounds {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} (hp : p ∈ fan v s) :
    8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6 ∧
    8 * (v : ℝ) + 4 ≤ p.2 ∧ p.2 ≤ 8 * (v : ℝ) + 6 := by
  have hb := mem_segment_bounds hp
  have hs : (s : ℕ) ≤ 2 := by omega
  have hs' : (s : ℝ) ≤ 2 := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := by positivity
  simp only [center, elbow, column, Set.mem_uIcc] at hb
  push_cast at hb
  split_ifs at hb <;> rcases hb with ⟨hx, hy⟩ <;>
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> constructor <;> try linarith
  all_goals constructor <;> try linarith
  all_goals constructor <;> linarith

/-- Distinct vertex boxes have disjoint local fans. -/
theorem fan_disjoint {u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    Disjoint (fan u s) (fan v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := fan_bounds hp
  have hq' := fan_bounds hq
  rcases lt_or_gt_of_ne huv with h | h
  · have h' : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
    linarith
  · have h' : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
    linarith

/-- Membership in a stem fixes its column and its closed vertical interval. -/
theorem mem_stem {n e v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ stem n e v s ↔ p.1 = (column v s : ℝ) ∧
      p.2 ∈ Set.uIcc ((elbow v s).2 : ℝ) (track n e : ℝ) := by
  exact mem_vertical

/-- Membership in a bridge fixes its row and its closed horizontal interval. -/
theorem mem_bridge {n e u v : ℕ} {s t : Fin 3} {p : ℝ × ℝ} :
    p ∈ bridge n e u v s t ↔ p.2 = (track n e : ℝ) ∧
      p.1 ∈ Set.uIcc (column u s : ℝ) (column v t : ℝ) := by
  exact mem_horizontal

/-- The three local fans, in left/up/right order, have these explicit real supports. -/
theorem mem_fan {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ fan v s ↔
      (s = 0 ∧ p.2 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 4) ∨
      (s = 1 ∧ p.1 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 4 ≤ p.2 ∧ p.2 ≤ 8 * (v : ℝ) + 6) ∨
      (s = 2 ∧ p.2 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 4 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6) := by
  fin_cases s <;> norm_num only [fan, segment, realPoint, center, elbow, column,
    Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
    Int.cast_add, Int.cast_mul, Int.cast_natCast,
    and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals ring_nf
  all_goals first | rw [mem_horizontal] | rw [mem_vertical]
  all_goals simp only [Set.mem_uIcc]
  all_goals
    constructor
    · rintro ⟨h, h' | h'⟩ <;> exact ⟨h, by constructor <;> linarith⟩
    · rintro ⟨h, h'⟩
      first
      | exact ⟨h, Or.inl h'⟩
      | exact ⟨h, Or.inr h'⟩

/-- Every edge row lies strictly above every vertex box. -/
theorem elbow_below_track {n e v : ℕ} (hv : v < n) (s : Fin 3) :
    (elbow v s).2 < track n e := by
  simp only [elbow, center, track]
  split_ifs <;> omega

/-- The fixed initial segment is proper and orthogonal. -/
theorem center_elbow_axisAligned (v : ℕ) (s : Fin 3) : AxisAligned (center v) (elbow v s) := by
  fin_cases s <;> norm_num only [AxisAligned, center, elbow, column, ne_eq, Prod.mk.injEq,
    Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte]
  all_goals omega

/-- The complete route has exactly five segments. -/
theorem route_segments_length (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).consecutivePairs.length = 5 := by
  rfl

/-- The route starts and ends at the specified centers. -/
@[simp] theorem route_head (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).head? = some (center u) := rfl

/-- The route starts and ends at the specified centers. -/
@[simp] theorem route_last (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).getLast? = some (center v) := rfl

/-- Proper orthogonality uses only distinct vertices and the vertex range bounds. -/
theorem route_orthogonal {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : IsOrthogonal (route n e u v s t) := by
  have hus := center_elbow_axisAligned u s
  have hvt := center_elbow_axisAligned v t
  have hut := elbow_below_track (e := e) hu s
  have hvt' := elbow_below_track (e := e) hv t
  intro a ha
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact hus
  · exact ⟨Or.inl rfl, fun h => (ne_of_lt hut) (congrArg Prod.snd h)⟩
  · refine ⟨Or.inr rfl, fun h => huv ?_⟩
    exact (column_injective (congrArg Prod.fst h)).1
  · exact ⟨Or.inl rfl, fun h => (ne_of_gt hvt') (congrArg Prod.snd h)⟩
  · exact ⟨hvt.1.imp Eq.symm Eq.symm, hvt.2.symm⟩

/-- All six listed points lie in a rectangle with width `8n` and height `8n+2m`.
The convention permits an empty graph and uses only edges `e < m`. -/
theorem route_bounds {n m e u v : ℕ} (he : e < m) (hu : u < n) (hv : v < n)
    (s t : Fin 3) {p : Point} (hp : p ∈ route n e u v s t) :
    0 ≤ p.1 ∧ p.1 ≤ 8 * (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ 8 * (n : ℤ) + 2 * m := by
  have hs := s.isLt
  have ht := t.isLt
  simp only [route, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [center, elbow, column, track] <;> (try split_ifs) <;> omega

/-- One edge has wire length at most `80n+10m`, with no assumption on degree. -/
theorem route_wireLength_le {n m e u v : ℕ} (he : e < m) (hu : u < n) (hv : v < n)
    (s t : Fin 3) : wireLength (route n e u v s t) ≤ 80 * n + 10 * m := by
  have hb := wireLength_le_box (w := 8 * n) (h := 8 * n + 2 * m)
    (r := route n e u v s t) (fun p hp => by
      exact_mod_cast route_bounds he hu hv s t hp)
  rw [route_segments_length] at hb
  omega

/-- A route visits no vertex center except its two prescribed endpoints. This concerns the
whole real segment support, not only its six listed points. -/
theorem center_mem_support_iff {n e u v w : ℕ} (hu : u < n) (hv : v < n)
    (hw : w < n) (huv : u ≠ v) (s t : Fin 3) :
    realPoint (center w) ∈ support (route n e u v s t) ↔ w = u ∨ w = v := by
  rw [realPoint_mem_support_iff (route_orthogonal hu hv huv s t)]
  fin_cases s <;> fin_cases t <;>
    simp only [route, center, elbow, column, track, List.consecutivePairs, List.tail_cons,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false, or_and_right, exists_or, exists_eq_left, Fin.reduceFinMk, Fin.isValue,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, mul_one, add_zero,
      ↓reduceIte, Prod.mk.injEq] <;> omega

/-- Two different ports in a single vertex box meet only at the vertex center. -/
theorem fan_contact {v : ℕ} {s t : Fin 3} (hst : s ≠ t) {p : ℝ × ℝ}
    (hs : p ∈ fan v s) (ht : p ∈ fan v t) : p = realPoint (center v) := by
  rw [mem_fan] at hs ht
  rcases hs with ⟨hs, hy, hx⟩ | ⟨hs, hx, hy⟩ | ⟨hs, hy, hx⟩ <;>
    rcases ht with ⟨ht, hy', hx'⟩ | ⟨ht, hx', hy'⟩ | ⟨ht, hy', hx'⟩ <;>
    subst s <;> subst t <;> try contradiction
  all_goals apply Prod.ext <;> simp only [realPoint, center] <;> push_cast <;> linarith

/-- A fan can contact a stem only when both belong to the same port. -/
theorem fan_stem_port_eq {n e u v : ℕ} (hv : v < n) {s t : Fin 3} {p : ℝ × ℝ}
    (hp : p ∈ fan u s) (hq : p ∈ stem n e v t) : u = v ∧ s = t := by
  have hb := fan_bounds hp
  have hcol := (mem_stem.1 hq).1
  have ht : (t : ℝ) ≤ 2 := by exact_mod_cast (show (t : ℕ) ≤ 2 by omega)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have huv : u = v := by
    by_contra h
    simp only [column] at hcol
    push_cast at hcol
    rcases lt_or_gt_of_ne h with h | h
    · have h' : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
      linarith
    · have h' : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
      linarith
  subst v
  refine ⟨rfl, ?_⟩
  have hhigh : ((elbow u t).2 : ℝ) < track n e := by
    exact_mod_cast elbow_below_track (e := e) hv t
  rw [mem_stem, Set.uIcc_of_le hhigh.le] at hq
  rw [mem_fan] at hp
  rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
    fin_cases t <;> norm_num only [column, elbow, center, Fin.ext_iff, Fin.val_mk, Fin.val_zero,
      Fin.val_one, Fin.val_two, ↓reduceIte,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, Set.mem_Icc] at hq ⊢ <;> linarith

/-- Different port columns give disjoint stems, independently of their edge heights. -/
theorem stem_disjoint {n e f u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t)) :
    Disjoint (stem n e u s) (stem n f v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hx := (mem_stem.1 hp).1.symm.trans (mem_stem.1 hq).1
  have hcol : column u s = column v t := by exact_mod_cast hx
  obtain ⟨rfl, rfl⟩ := column_injective hcol
  exact h rfl

/-- A local fan lies strictly below every upper bridge. -/
theorem fan_bridge_disjoint {n e u v w : ℕ} (hw : w < n) (s t q : Fin 3) :
    Disjoint (fan w q) (bridge n e u v s t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hb := fan_bounds hp
  have hy := (mem_bridge.1 hq).1
  have hw' : (w : ℝ) + 1 ≤ n := by exact_mod_cast hw
  have he : (0 : ℝ) ≤ e := by positivity
  simp only [track] at hy
  push_cast at hy
  linarith

/-- Distinct edge tracks give disjoint upper bridges. -/
theorem bridge_disjoint {n e f u v a b : ℕ} (hef : e ≠ f) (s t q r : Fin 3) :
    Disjoint (bridge n e u v s t) (bridge n f a b q r) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hy := (mem_bridge.1 hp).1.symm.trans (mem_bridge.1 hq).1
  have htrack : track n e = track n f := by exact_mod_cast hy
  simp only [track] at htrack
  exact hef (by omega)

/-- Fans and stems at distinct ports are disjoint, even within one vertex box. -/
theorem fan_stem_disjoint {n e u v : ℕ} (hv : v < n) {s t : Fin 3}
    (h : (u, s) ≠ (v, t)) : Disjoint (fan u s) (stem n e v t) := by
  rw [Set.disjoint_left]
  intro p hp hq
  obtain ⟨huv, hst⟩ := fan_stem_port_eq hv hp hq
  exact h (Prod.ext huv hst)

/-- The two consecutive parts of one port meet only at their common elbow. -/
theorem fan_stem_endpointContacts {n e v : ℕ} (hv : v < n) (s : Fin 3) :
    EndpointContacts (center v) (elbow v s) (elbow v s) (column v s, track n e) := by
  intro p hp hq
  have ht := elbow_below_track (e := e) hv s
  change p ∈ fan v s at hp
  change p ∈ stem n e v s at hq
  rw [mem_stem, Set.uIcc_of_le (show ((elbow v s).2 : ℝ) ≤ track n e by
    exact_mod_cast ht.le)] at hq
  have heq : p = realPoint (elbow v s) := by
    apply Prod.ext hq.1
    rw [mem_fan] at hp
    rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
      norm_num only [realPoint, elbow, center, column, Fin.ext_iff, Fin.val_mk, Fin.val_zero,
        Fin.val_one, Fin.val_two, ↓reduceIte,
        Int.cast_add, Int.cast_mul, Int.cast_natCast, Set.mem_Icc] at hq ⊢ <;> linarith
  exact ⟨Or.inr heq, Or.inl heq⟩

/-- A stem meets its own bridge only at their common upper endpoint. -/
theorem stem_bridge_endpointContacts (n e u v : ℕ) (s t : Fin 3) :
    EndpointContacts (elbow u s) (column u s, track n e)
      (column u s, track n e) (column v t, track n e) := by
  intro p hp hq
  have heq : p = realPoint (column u s, track n e) :=
    Prod.ext (mem_stem.1 hp).1 (mem_bridge.1 hq).1
  exact ⟨Or.inr heq, Or.inl heq⟩

/-- The six listed points are distinct for an edge with distinct endpoints. -/
theorem route_nodup {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : (route n e u v s t).Nodup := by
  fin_cases s <;> fin_cases t <;>
    norm_num only [route, center, elbow, column, track, List.nodup_cons, Prod.mk.injEq,
      Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, and_true, List.nodup_nil] <;> omega

/-- The whole real polygonal route is simple: distinct consecutive segments contact only at
their common listed endpoints, and no listed point is repeated. -/
theorem route_simple {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : IsSimple (route n e u v s t) := by
  have hport : (u, s) ≠ (v, t) := fun h => huv (congrArg Prod.fst h)
  have h01 := fan_stem_endpointContacts (e := e) hu s
  have h02 := endpointContacts_of_disjoint (fan_bridge_disjoint (e := e) (u := u) (v := v) hu s t s)
  have h03 := (endpointContacts_of_disjoint (fan_stem_disjoint (e := e) hv hport)).reverse_right
  have h04 := (endpointContacts_of_disjoint (fan_disjoint huv s t)).reverse_right
  have h12 := stem_bridge_endpointContacts n e u v s t
  have h13 := (endpointContacts_of_disjoint
    (stem_disjoint (n := n) (e := e) (f := e) hport)).reverse_right
  have h14 := (endpointContacts_of_disjoint
    (fan_stem_disjoint (e := e) hu hport.symm).symm).reverse_right
  have h23 := (stem_bridge_endpointContacts n e v u t s).reverse_right.symm.reverse_right
  have h24 := (endpointContacts_of_disjoint
    (fan_bridge_disjoint (e := e) (u := u) (v := v) hv s t t).symm).reverse_right
  have h34 := (fan_stem_endpointContacts (e := e) hv t).symm.reverse_left.reverse_right
  refine ⟨route_nodup hu hv huv s t, ?_⟩
  intro first hf second hg hne
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hf hg
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h01.symm
  · exact False.elim (hne rfl)
  · exact h12
  · exact h13
  · exact h14
  · exact h02.symm
  · exact h12.symm
  · exact False.elim (hne rfl)
  · exact h23
  · exact h24
  · exact h03.symm
  · exact h13.symm
  · exact h23.symm
  · exact False.elim (hne rfl)
  · exact h34
  · exact h04.symm
  · exact h14.symm
  · exact h24.symm
  · exact h34.symm
  · exact False.elim (hne rfl)

/-- Every contact of an upper bridge with another edge's distinct port stem is a genuine
transverse crossing, strictly inside both segments. In particular it is never at a bend. -/
theorem bridge_stem_transverse {n e f u v w : ℕ} (hw : w < n) (hef : e ≠ f)
    {s t q : Fin 3} (hu : (w, q) ≠ (u, s)) (hv : (w, q) ≠ (v, t)) {p : ℝ × ℝ}
    (hp : p ∈ bridge n e u v s t) (hq : p ∈ stem n f w q) :
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow w q) (column w q, track n f) p := by
  have hb := mem_bridge.1 hp
  have hs := mem_stem.1 hq
  have hcu : column w q ≠ column u s := by
    intro h
    obtain ⟨rfl, rfl⟩ := column_injective h
    exact hu rfl
  have hcv : column w q ≠ column v t := by
    intro h
    obtain ⟨rfl, rfl⟩ := column_injective h
    exact hv rfl
  have hx : min (column u s) (column v t) < column w q ∧
      column w q < max (column u s) (column v t) := by
    have hmem := hb.2
    rw [hs.1, Set.mem_uIcc] at hmem
    norm_cast at hmem
    omega
  have hlow := elbow_below_track (e := e) hw q
  have hfhigh := elbow_below_track (e := f) hw q
  have hy : (elbow w q).2 < track n e ∧ track n e < track n f := by
    have hmem := hs.2
    rw [Set.uIcc_of_le (show ((elbow w q).2 : ℝ) ≤ track n f by exact_mod_cast hfhigh.le),
      hb.1] at hmem
    have hupper : track n e ≤ track n f := by exact_mod_cast hmem.2
    have hne : track n e ≠ track n f := by
      simp only [track]
      intro h
      exact hef (by omega)
    exact ⟨hlow, lt_of_le_of_ne hupper hne⟩
  refine Or.inl ⟨rfl, rfl, Prod.ext hs.1 hb.1, hx.1, hx.2, ?_, ?_⟩
  · change min (elbow w q).2 (track n f) < track n e
    omega
  · change track n e < max (elbow w q).2 (track n f)
    omega

/-- A bridge/stem transverse crossing has its exact integer column/row coordinates. -/
theorem bridge_stem_crossing_point {n e f u v w : ℕ} {s t q : Fin 3} {p : ℝ × ℝ}
    (h : Transverse (column u s, track n e) (column v t, track n e)
      (elbow w q) (column w q, track n f) p) :
    p = realPoint (column w q, track n e) := by
  rcases h with ⟨_, _, hp, _⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · exact hp
  · simp only [elbow, min_self, max_self] at hlo hhi
    omega

/-- Distinct ports' fans can contact only at their common graph endpoint. -/
theorem fan_pair_contact {u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t))
    {p : ℝ × ℝ} (hp : p ∈ fan u s) (hq : p ∈ fan v t) :
    u = v ∧ p = realPoint (center u) := by
  by_cases huv : u = v
  · subst v
    exact ⟨rfl, fan_contact (fun hst => h (Prod.ext rfl hst)) hp hq⟩
  · exact False.elim (Set.disjoint_left.1 (fan_disjoint huv s t) hp hq)

/-- Any pairwise route contact is either a shared graph endpoint or a strict transverse
bridge/stem crossing. The four port inequalities require different edge incidences to use
different ports, including at a shared vertex. All statements concern continuous real supports. -/
theorem route_contact {n e f u v a b : ℕ}
    (hu : u < n) (hv : v < n) (ha : a < n) (hb : b < n) (hef : e ≠ f)
    {s t q r : Fin 3} (huaq : (u, s) ≠ (a, q)) (hubr : (u, s) ≠ (b, r))
    (hvaq : (v, t) ≠ (a, q)) (hvbr : (v, t) ≠ (b, r)) {p : ℝ × ℝ}
    (hp : p ∈ support (route n e u v s t)) (hq : p ∈ support (route n f a b q r)) :
    (∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ p = realPoint (center w)) ∨
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow a q) (column a q, track n f) p ∨
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow b r) (column b r, track n f) p ∨
    Transverse (column a q, track n f) (column b r, track n f)
      (elbow u s) (column u s, track n e) p ∨
    Transverse (column a q, track n f) (column b r, track n f)
      (elbow v t) (column v t, track n e) p := by
  rw [support_route] at hp hq
  simp only [Set.mem_union] at hp hq
  rcases hp with (((hp | hp) | hp) | hp) | hp <;>
    rcases hq with (((hq | hq) | hq) | hq) | hq
  · exact Or.inl ⟨u, Or.inl rfl, Or.inl (fan_pair_contact huaq hp hq).1,
       (fan_pair_contact huaq hp hq).2⟩
  · exact False.elim (huaq (Prod.ext (fan_stem_port_eq ha hp hq).1 (fan_stem_port_eq ha hp hq).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint hu _ _ _) hp hq)
  · exact False.elim (hubr (Prod.ext (fan_stem_port_eq hb hp hq).1 (fan_stem_port_eq hb hp hq).2))
  · exact Or.inl ⟨u, Or.inl rfl, Or.inr (fan_pair_contact hubr hp hq).1,
       (fan_pair_contact hubr hp hq).2⟩
  · exact False.elim (huaq.symm
      (Prod.ext (fan_stem_port_eq hu hq hp).1 (fan_stem_port_eq hu hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint huaq) hp hq)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (bridge_stem_transverse hu hef.symm huaq hubr hq hp))))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hubr) hp hq)
  · exact False.elim (hubr.symm
      (Prod.ext (fan_stem_port_eq hu hq hp).1 (fan_stem_port_eq hu hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint ha _ _ _) hq hp)
  · exact Or.inr (Or.inl (bridge_stem_transverse ha hef huaq.symm hvaq.symm hp hq))
  · exact False.elim (Set.disjoint_left.1 (bridge_disjoint hef _ _ _ _) hp hq)
  · exact Or.inr (Or.inr (Or.inl (bridge_stem_transverse hb hef hubr.symm hvbr.symm hp hq)))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint hb _ _ _) hq hp)
  · exact False.elim (hvaq.symm
      (Prod.ext (fan_stem_port_eq hv hq hp).1 (fan_stem_port_eq hv hq hp).2))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hvaq) hp hq)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (bridge_stem_transverse hv hef.symm hvaq hvbr hq hp))))
  · exact False.elim (Set.disjoint_left.1 (stem_disjoint hvbr) hp hq)
  · exact False.elim (hvbr.symm
      (Prod.ext (fan_stem_port_eq hv hq hp).1 (fan_stem_port_eq hv hq hp).2))
  · exact Or.inl ⟨v, Or.inr rfl, Or.inl (fan_pair_contact hvaq hp hq).1,
       (fan_pair_contact hvaq hp hq).2⟩
  · exact False.elim (hvaq (Prod.ext (fan_stem_port_eq ha hp hq).1 (fan_stem_port_eq ha hp hq).2))
  · exact False.elim (Set.disjoint_left.1 (fan_bridge_disjoint hv _ _ _) hp hq)
  · exact False.elim (hvbr (Prod.ext (fan_stem_port_eq hb hp hq).1 (fan_stem_port_eq hb hp hq).2))
  · exact Or.inl ⟨v, Or.inr rfl, Or.inr (fan_pair_contact hvbr hp hq).1,
       (fan_pair_contact hvbr hp hq).2⟩

end Cslib.Orthogonal.Layout
