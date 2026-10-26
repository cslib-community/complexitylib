/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Translation and separation of square grid cells

All separation statements concern real points, including nonintegral points on routes.
The integer cell indices may be negative. A positive integer radius `r` gives cells of side
`2 * r`; in particular, radius 120 gives cells of side 240.

## Main definitions

* `Cslib.Orthogonal.translate`: translate the listed integer points of a route.
* `Cslib.Orthogonal.cellOrigin`, `Cslib.Orthogonal.openCell`, `Cslib.Orthogonal.closedCell`:
  square cells of the integer grid, interpreted in the real plane.
* `Cslib.Orthogonal.cellPort`: the four side midpoints of a cell.

## Main results

* Translation preserves continuous support, orthogonality, simplicity and wire length.
* An open cell is disjoint from every distinct closed cell.
* Equal ports of distinct cells are on opposite sides of adjacent cells.

## References

These are elementary coordinate facts, independent of any SAT encoding or gadget.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- Translate every listed point by the same integer displacement. -/
def translate (v : Point) (r : Route) : Route := r.map (· + v)

/-- Integer translation agrees with real translation. -/
theorem realPoint_add (a b : Point) : realPoint (a + b) = realPoint a + realPoint b := by
  ext <;> simp [realPoint]

/-- Translation preserves membership in the entire continuous segment. -/
theorem mem_segment_translate_iff (v a b : Point) (p : ℝ × ℝ) :
    p + realPoint v ∈ segment (a + v) (b + v) ↔ p ∈ segment a b := by
  simp only [segment, realPoint_add, add_comm _ (realPoint v)]
  exact _root_.mem_segment_translate (𝕜 := ℝ) _

private theorem consecutivePairs_translate (v : Point) (r : Route) :
    (translate v r).consecutivePairs =
      r.consecutivePairs.map (fun e => (e.1 + v, e.2 + v)) := by
  simp only [translate, List.consecutivePairs, ← List.map_tail, List.zip_map]
  rfl

/-- Membership in a translated support is precisely translated membership. -/
theorem mem_support_translate_iff (v : Point) (r : Route) (p : ℝ × ℝ) :
    p + realPoint v ∈ support (translate v r) ↔ p ∈ support r := by
  simp only [support, Set.mem_ofPred_eq, consecutivePairs_translate]
  simp only [translate, List.mem_map]
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, hp⟩ | ⟨_, ⟨e, he, rfl⟩, hp⟩)
    · exact Or.inl ⟨a, ha, add_right_cancel (hp.trans (realPoint_add a v))⟩
    · exact Or.inr ⟨e, he, (mem_segment_translate_iff v _ _ p).1 hp⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨e, he, hp⟩)
    · exact Or.inl ⟨a + v, ⟨a, ha, rfl⟩, (realPoint_add a v).symm⟩
    · exact Or.inr ⟨(e.1 + v, e.2 + v), ⟨e, he, rfl⟩,
        (mem_segment_translate_iff v _ _ p).2 hp⟩

/-- Translation of a route translates its entire real support. -/
theorem support_translate (v : Point) (r : Route) :
    support (translate v r) = (fun p => p + realPoint v) '' support r := by
  ext p
  constructor
  · intro hp
    refine ⟨p - realPoint v, ?_, sub_add_cancel _ _⟩
    exact (mem_support_translate_iff v r _).1 (by simpa only [sub_add_cancel] using hp)
  · rintro ⟨p, hp, rfl⟩
    exact (mem_support_translate_iff v r p).2 hp

/-- Translation preserves proper axis alignment. -/
theorem axisAligned_add_iff (v a b : Point) :
    AxisAligned (a + v) (b + v) ↔ AxisAligned a b := by
  simp [AxisAligned, Prod.fst_add, Prod.snd_add]

/-- Translation preserves orthogonality. -/
theorem isOrthogonal_translate_iff (v : Point) (r : Route) :
    IsOrthogonal (translate v r) ↔ IsOrthogonal r := by
  simp only [IsOrthogonal, consecutivePairs_translate, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, axisAligned_add_iff]

/-- Translation preserves Manhattan segment length. -/
theorem length_add (v a b : Point) : length (a + v) (b + v) = length a b := by
  simp [length]

/-- Translation preserves total wire length. -/
theorem wireLength_translate (v : Point) (r : Route) :
    wireLength (translate v r) = wireLength r := by
  simp only [wireLength, consecutivePairs_translate, List.map_map, Function.comp_def, length_add]

/-- Translation preserves endpoint-only contact certificates. -/
theorem endpointContacts_add_iff (v a b c d : Point) :
    EndpointContacts (a + v) (b + v) (c + v) (d + v) ↔ EndpointContacts a b c d := by
  constructor
  · intro h p hp hq
    have hh := h (p + realPoint v) ((mem_segment_translate_iff v a b p).2 hp)
      ((mem_segment_translate_iff v c d p).2 hq)
    simpa only [realPoint_add, add_left_inj] using hh
  · intro h p hp hq
    have hh := h (p - realPoint v)
      ((mem_segment_translate_iff v a b _).1 (by simpa only [sub_add_cancel] using hp))
      ((mem_segment_translate_iff v c d _).1 (by simpa only [sub_add_cancel] using hq))
    simpa only [sub_eq_iff_eq_add, realPoint_add] using hh

/-- Translation preserves continuous simplicity. -/
theorem isSimple_translate_iff (v : Point) (r : Route) :
    IsSimple (translate v r) ↔ IsSimple r := by
  have hinj : Function.Injective (fun p : Point => p + v) := fun _ _ h => add_right_cancel h
  simp only [IsSimple, consecutivePairs_translate]
  simp only [translate, List.nodup_map_iff hinj,
    List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, endpointContacts_add_iff]
  simp only [ne_eq, Prod.mk.injEq, add_left_inj, ← Prod.ext_iff]

/-- The lower-left corner of a square cell of side `2 * r`. -/
def cellOrigin (r : ℤ) (c : Point) : Point := (2 * r * c.1, 2 * r * c.2)

/-- The open real square belonging to integer cell `c`. -/
def openCell (r : ℤ) (c : Point) : Set (ℝ × ℝ) :=
  {p | (2 * r * c.1 : ℤ) < p.1 ∧ p.1 < (2 * r * (c.1 + 1) : ℤ) ∧
    (2 * r * c.2 : ℤ) < p.2 ∧ p.2 < (2 * r * (c.2 + 1) : ℤ)}

/-- The closed real square belonging to integer cell `c`. -/
def closedCell (r : ℤ) (c : Point) : Set (ℝ × ℝ) :=
  {p | (2 * r * c.1 : ℤ) ≤ p.1 ∧ p.1 ≤ (2 * r * (c.1 + 1) : ℤ) ∧
    (2 * r * c.2 : ℤ) ≤ p.2 ∧ p.2 ≤ (2 * r * (c.2 + 1) : ℤ)}

private theorem support_subset_convex {s : Set (ℝ × ℝ)} (hs : Convex ℝ s)
    {r : Route} (hr : ∀ a ∈ r, realPoint a ∈ s) : support r ⊆ s := by
  rintro p (⟨a, ha, rfl⟩ | ⟨e, he, hp⟩)
  · exact hr a ha
  · have he' := List.of_mem_zip he
    exact hs.segment_subset (hr e.1 he'.1) (hr e.2 (List.mem_of_mem_tail he'.2)) hp

/-- Bounds on the listed vertices control the entire continuous support in an open cell. -/
theorem support_subset_openCell {r : ℤ} {c : Point} {a : Route}
    (h : ∀ q ∈ a, realPoint q ∈ openCell r c) : support a ⊆ openCell r c := by
  have hc : Convex ℝ (openCell r c) := by
    have heq : openCell r c =
        Set.Ioo ((2 * r * c.1 : ℤ) : ℝ) ((2 * r * (c.1 + 1) : ℤ) : ℝ) ×ˢ
        Set.Ioo ((2 * r * c.2 : ℤ) : ℝ) ((2 * r * (c.2 + 1) : ℤ) : ℝ) := by
      ext p
      simp only [openCell, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioo, and_assoc]
    rw [heq]
    exact
      (convex_Ioo (𝕜 := ℝ) ((2 * r * c.1 : ℤ) : ℝ)
        ((2 * r * (c.1 + 1) : ℤ) : ℝ)).prod
        (convex_Ioo (𝕜 := ℝ) ((2 * r * c.2 : ℤ) : ℝ)
          ((2 * r * (c.2 + 1) : ℤ) : ℝ))
  exact support_subset_convex hc h

/-- Bounds on the listed vertices control the entire continuous support in a closed cell. -/
theorem support_subset_closedCell {r : ℤ} {c : Point} {a : Route}
    (h : ∀ q ∈ a, realPoint q ∈ closedCell r c) : support a ⊆ closedCell r c := by
  have hc : Convex ℝ (closedCell r c) := by
    have heq : closedCell r c =
        Set.Icc ((2 * r * c.1 : ℤ) : ℝ) ((2 * r * (c.1 + 1) : ℤ) : ℝ) ×ˢ
        Set.Icc ((2 * r * c.2 : ℤ) : ℝ) ((2 * r * (c.2 + 1) : ℤ) : ℝ) := by
      ext p
      simp only [closedCell, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, and_assoc]
    rw [heq]
    exact
      (convex_Icc (𝕜 := ℝ) ((2 * r * c.1 : ℤ) : ℝ)
        ((2 * r * (c.1 + 1) : ℤ) : ℝ)).prod
        (convex_Icc (𝕜 := ℝ) ((2 * r * c.2 : ℤ) : ℝ)
          ((2 * r * (c.2 + 1) : ℤ) : ℝ))
  exact support_subset_convex hc h

private theorem index_eq_of_open_closed {r i j : ℤ} (hr : 0 < r) {x : ℝ}
    (hi : (2 * r * i : ℤ) < x ∧ x < (2 * r * (i + 1) : ℤ))
    (hj : (2 * r * j : ℤ) ≤ x ∧ x ≤ (2 * r * (j + 1) : ℤ)) : i = j := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hij : ¬ i < j := by
    intro h
    have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    nlinarith [hi.2, hj.1]
  have hji : ¬ j < i := by
    intro h
    have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    nlinarith [hi.1, hj.2]
  omega

/-- A point in one open cell and another closed cell forces equal integer indices. -/
theorem cell_eq_of_mem_open_closed {r : ℤ} (hr : 0 < r) {c d : Point} {p : ℝ × ℝ}
    (hc : p ∈ openCell r c) (hd : p ∈ closedCell r d) : c = d :=
  Prod.ext (index_eq_of_open_closed hr ⟨hc.1, hc.2.1⟩ ⟨hd.1, hd.2.1⟩)
    (index_eq_of_open_closed hr hc.2.2 hd.2.2)

/-- Distinct cells have no real contact between an open cell and a closed cell. -/
theorem disjoint_openCell_closedCell {r : ℤ} (hr : 0 < r) {c d : Point} (hcd : c ≠ d) :
    Disjoint (openCell r c) (closedCell r d) := by
  rw [Set.disjoint_left]
  exact fun _ hc hd => hcd (cell_eq_of_mem_open_closed hr hc hd)

/-- Distinct open cells are disjoint in the real plane. -/
theorem disjoint_openCell {r : ℤ} (hr : 0 < r) {c d : Point} (hcd : c ≠ d) :
    Disjoint (openCell r c) (openCell r d) := by
  rw [Set.disjoint_left]
  intro p hc hd
  exact hcd (cell_eq_of_mem_open_closed hr hc
    ⟨hd.1.le, hd.2.1.le, hd.2.2.1.le, hd.2.2.2.le⟩)

/-- Side midpoints, in order left, right, bottom, top. -/
def cellPort (r : ℤ) (c : Point) (s : Fin 4) : Point :=
  cellOrigin r c + if s = 0 then (0, r) else if s = 1 then (2 * r, r)
    else if s = 2 then (r, 0) else (r, 2 * r)

private def unitPort (s : Fin 4) : Point :=
  if s = 0 then (0, 1) else if s = 1 then (2, 1)
    else if s = 2 then (1, 0) else (1, 2)

private theorem cellPort_coordinates (r : ℤ) (c : Point) (s : Fin 4) :
    cellPort r c s = (r * (2 * c.1 + (unitPort s).1),
      r * (2 * c.2 + (unitPort s).2)) := by
  fin_cases s <;> ext <;> norm_num [cellPort, cellOrigin, unitPort] <;> ring

/-- Equal side midpoints in distinct cells identify the adjacent cell and opposite side.
The displacements refer to the integer cell indices, not scaled drawing coordinates. -/
theorem cellPort_eq_cases {r : ℤ} (hr : 0 < r) {c d : Point} {s t : Fin 4}
    (hcd : c ≠ d) (h : cellPort r c s = cellPort r d t) :
    (s = 0 ∧ t = 1 ∧ d = c + (-1, 0)) ∨
    (s = 1 ∧ t = 0 ∧ d = c + (1, 0)) ∨
    (s = 2 ∧ t = 3 ∧ d = c + (0, -1)) ∨
    (s = 3 ∧ t = 2 ∧ d = c + (0, 1)) := by
  rcases c with ⟨cx, cy⟩
  rcases d with ⟨dx, dy⟩
  have hcd' : ¬ (cx = dx ∧ cy = dy) := fun h => hcd (Prod.ext h.1 h.2)
  rw [cellPort_coordinates, cellPort_coordinates, Prod.mk.injEq] at h
  have hx := mul_left_cancel₀ (ne_of_gt hr) h.1
  have hy := mul_left_cancel₀ (ne_of_gt hr) h.2
  fin_cases s <;> fin_cases t <;>
    norm_num [unitPort, Prod.ext_iff] at hx hy ⊢ <;> omega

/-- The port classification also applies to equality in the real plane. -/
theorem realPoint_cellPort_eq_cases {r : ℤ} (hr : 0 < r) {c d : Point} {s t : Fin 4}
    (hcd : c ≠ d) (h : realPoint (cellPort r c s) = realPoint (cellPort r d t)) :
    (s = 0 ∧ t = 1 ∧ d = c + (-1, 0)) ∨
    (s = 1 ∧ t = 0 ∧ d = c + (1, 0)) ∨
    (s = 2 ∧ t = 3 ∧ d = c + (0, -1)) ∨
    (s = 3 ∧ t = 2 ∧ d = c + (0, 1)) :=
  cellPort_eq_cases hr hcd (realPoint_injective h)

/-- Translating a point from the open local square puts it in the corresponding grid cell. -/
theorem mem_openCell_add_origin_iff (r : ℤ) (c : Point) (p : ℝ × ℝ) :
    p + realPoint (cellOrigin r c) ∈ openCell r c ↔
      0 < p.1 ∧ p.1 < (2 * r : ℤ) ∧ 0 < p.2 ∧ p.2 < (2 * r : ℤ) := by
  simp only [openCell, Set.mem_ofPred_eq, realPoint, cellOrigin, Prod.fst_add, Prod.snd_add]
  push_cast
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Translating a point from the closed local square puts it in the corresponding grid cell. -/
theorem mem_closedCell_add_origin_iff (r : ℤ) (c : Point) (p : ℝ × ℝ) :
    p + realPoint (cellOrigin r c) ∈ closedCell r c ↔
      0 ≤ p.1 ∧ p.1 ≤ (2 * r : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (2 * r : ℤ) := by
  simp only [closedCell, Set.mem_ofPred_eq, realPoint, cellOrigin, Prod.fst_add, Prod.snd_add]
  push_cast
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Positive-radius cells have an interior center, at the translated point `(r,r)`. -/
theorem center_mem_openCell {r : ℤ} (hr : 0 < r) (c : Point) :
    realPoint (cellOrigin r c + (r, r)) ∈ openCell r c := by
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  simp only [realPoint, Int.cast_mul, Int.cast_ofNat]
  exact ⟨hr', by linarith, hr', by linarith⟩

/-- Route supports in distinct open/closed cells are disjoint, including nonintegral points. -/
theorem disjoint_support_of_cells {r : ℤ} (hr : 0 < r) {c d : Point} (hcd : c ≠ d)
    {a b : Route} (ha : support a ⊆ openCell r c) (hb : support b ⊆ closedCell r d) :
    Disjoint (support a) (support b) :=
  (disjoint_openCell_closedCell hr hcd).mono ha hb

end Cslib.Orthogonal
