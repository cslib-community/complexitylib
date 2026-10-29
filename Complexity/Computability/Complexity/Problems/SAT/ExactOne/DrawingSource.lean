/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Foundations.Geometry.Orthogonal.Directions
public import Complexity.Foundations.Geometry.Orthogonal.Reverse
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup

/-!
# Exterior routes for clause-box replacement

An incidence edge is normalized from its second endpoint (the clause vertex) to its first
endpoint (the variable vertex), independently of the supplied route orientation. Dilation and
initial trimming provide an exterior route with a single contact with its clause box. The
normalization changes neither route support nor geometric costs.

## Main definitions

* `sourceRoute`, `sourceDirection`: the normalized source incidence and its exit direction.
* `exteriorRoute`, `exteriorPort`: the scaled, trimmed incidence and its designated box port.

## Main results

* `sourceRoute_endpoints`, `sourceRoute_regular`: normalized source-route correctness.
* `sourceDirection_ne`: distinct incidences at a clause use distinct cardinal directions.
* `exteriorRoute_box_contact`: the exterior route meets its own closed box only at the port.
* `exteriorRoute_avoids_box`: nonincident source vertices have disjoint replacement boxes.

## References

The source normalization and geometric assembly proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- The clause endpoint of a listed incidence, with a fixed fallback for invalid indices. -/
def sourceStart (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  Graph.drawingPosition G d (G.2.getD i (0, 0)).2

/-- The variable endpoint of a listed incidence, with a fixed fallback for invalid indices. -/
def sourceFinish (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  Graph.drawingPosition G d (G.2.getD i (0, 0)).1

/-- Normalize the supplied incidence route to begin at its clause endpoint. -/
def sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Route :=
  if (d.2.getD i []).head? = some (sourceStart G d i) then d.2.getD i []
  else (d.2.getD i []).reverse

/-- Declared vertices with equal positions are equal in a valid drawing. -/
theorem drawingPosition_injOn {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {v w : ℕ} (hv : v ∈ G.1) (hw : w ∈ G.1)
    (he : Graph.drawingPosition G d v = Graph.drawingPosition G d w) : v = w := by
  have hi := List.idxOf_lt_length_of_mem hv
  have hj := List.idxOf_lt_length_of_mem hw
  have hi' : G.1.idxOf v < d.1.length := by rw [hd.vertexCount]; exact hi
  have hj' : G.1.idxOf w < d.1.length := by rw [hd.vertexCount]; exact hj
  simp only [Graph.drawingPosition, List.getD_eq_getElem _ _ hi',
    List.getD_eq_getElem _ _ hj'] at he
  have he' := hd.positionsNodup.getElem_inj_iff.mp he
  exact (List.idxOf_inj hv).mp he'

/-- Normalization preserves the complete continuous support of each supplied route. -/
theorem support_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    support (sourceRoute G d i) = support (d.2.getD i []) := by
  unfold sourceRoute
  split
  · rfl
  · exact support_reverse _

/-- Normalization preserves the number of route points. -/
theorem length_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    (sourceRoute G d i).length = (d.2.getD i []).length := by
  unfold sourceRoute
  split <;> simp

/-- Normalization preserves the number of segments. -/
theorem consecutivePairs_length_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing)
    (i : ℕ) :
    (sourceRoute G d i).consecutivePairs.length = (d.2.getD i []).consecutivePairs.length := by
  unfold sourceRoute
  split
  · rfl
  · exact consecutivePairs_length_reverse _

/-- Normalization preserves the total Manhattan wire cost. -/
theorem wireLength_sourceRoute (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    wireLength (sourceRoute G d i) = wireLength (d.2.getD i []) := by
  unfold sourceRoute
  split
  · rfl
  · exact wireLength_reverse _

/-- The normalized route begins at the clause and ends at the variable. -/
theorem sourceRoute_endpoints {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length) :
    (sourceRoute G d i).head? = some (sourceStart G d i) ∧
      (sourceRoute G d i).getLast? = some (sourceFinish G d i) := by
  have he := hd.endpoints i hi
  dsimp only at he
  have hs : sourceStart G d i = Graph.drawingPosition G d G.2[i].2 := by
    rw [sourceStart, List.getD_eq_getElem _ _ hi]
  have hf : sourceFinish G d i = Graph.drawingPosition G d G.2[i].1 := by
    rw [sourceFinish, List.getD_eq_getElem _ _ hi]
  rw [← hs, ← hf] at he
  unfold sourceRoute
  split_ifs with hh
  · rcases he with ⟨h₁, h₂⟩ | he
    · have heq : sourceFinish G d i = sourceStart G d i := Option.some.inj (h₁.symm.trans hh)
      exact ⟨hh, heq ▸ h₂⟩
    · exact he
  · rcases he with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
    · simpa only [List.head?_reverse, List.getLast?_reverse] using And.intro h₂ h₁
    · exact False.elim (hh h₁)

/-- The clause and variable endpoints occupy different points. -/
theorem sourceStart_ne_finish {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length) :
    sourceStart G d i ≠ sourceFinish G d i := by
  have hm := hd.endpointsDeclared _ (List.getElem_mem hi)
  have hn := hd.loopless _ (List.getElem_mem hi)
  unfold sourceStart sourceFinish
  rw [List.getD_eq_getElem _ _ hi]
  exact fun h => hn (drawingPosition_injOn hd hm.1 hm.2 h.symm)

/-- Every normalized valid incidence has at least two listed points. -/
theorem sourceRoute_length_ge_two {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length) :
    2 ≤ (sourceRoute G d i).length := by
  have he := sourceRoute_endpoints hd hi
  have hn := sourceStart_ne_finish hd hi
  generalize hr : sourceRoute G d i = r at he ⊢
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩
  · simp at he
  · simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at he
    exact False.elim (hn (he.1.symm.trans he.2))
  · simp

/-- Normalization preserves proper orthogonality and continuous simplicity. -/
theorem sourceRoute_regular {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length) :
    IsOrthogonal (sourceRoute G d i) ∧ IsSimple (sourceRoute G d i) := by
  unfold sourceRoute
  split
  · exact ⟨hd.orthogonal i hi, hd.simple i hi⟩
  · exact ⟨(isOrthogonal_reverse_iff _).mpr (hd.orthogonal i hi),
      (isSimple_reverse_iff _).mpr (hd.simple i hi)⟩

/-- A normalized incidence starts with its actual clause vertex and a proper next point. -/
theorem sourceRoute_shape {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length) :
    ∃ b r, sourceRoute G d i = sourceStart G d i :: b :: r := by
  have hh := (sourceRoute_endpoints hd hi).1
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp hh
  cases r with
  | nil => have hlen := sourceRoute_length_ge_two hd hi; simp [hr] at hlen
  | cons b r => exact ⟨b, r, hr⟩

/-- The cardinal exit direction of a normalized source incidence. -/
def sourceDirection (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  direction (sourceStart G d i) ((sourceRoute G d i).getD 1 (0, 0))

/-- Incidences at the same clause vertex leave in different cardinal directions. -/
theorem sourceDirection_ne {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j)
    (hc : G.2[i].2 = G.2[j].2) : sourceDirection G d i ≠ sourceDirection G d j := by
  obtain ⟨b, r, hr⟩ := sourceRoute_shape hd hi
  obtain ⟨c, s, hs⟩ := sourceRoute_shape hd hj
  have he : sourceStart G d i = sourceStart G d j := by
    unfold sourceStart
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj, hc]
  have ho₁ := (sourceRoute_regular hd hi).1
  have ho₂ := (sourceRoute_regular hd hj).1
  rw [hr] at ho₁
  rw [hs, ← he] at ho₂
  have h₁ := ho₁ (sourceStart G d i, b) (by simp [List.consecutivePairs])
  have h₂ := ho₂ (sourceStart G d i, c) (by simp [List.consecutivePairs])
  have hdir := direction_ne_of_grid_contacts h₁ h₂ (fun p hp hq => ?_)
  · simpa [sourceDirection, hr, hs, he, List.getD] using hdir
  · have hp' : p ∈ support (d.2.getD i []) := by
      rw [← support_sourceRoute, hr, support_cons_cons]
      exact Or.inl hp
    have hq' : p ∈ support (d.2.getD j []) := by
      rw [← support_sourceRoute, hs, ← he, support_cons_cons]
      exact Or.inl hq
    obtain ⟨v, _, _, _, hv⟩ := hd.contacts i hi j hj hij p hp' hq'
    exact ⟨Graph.drawingPosition G d v, hv⟩

/-- Scale and trim the clause end of a normalized source incidence. -/
def exteriorRoute (k radius : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Route :=
  cutStart k radius (sourceRoute G d i)

/-- The designated contact with the boundary of the local clause box. -/
def exteriorPort (k radius : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) : Point :=
  k • sourceStart G d i + radius • sourceDirection G d i

/-- The trimmed exterior incidence is proper and continuously simple. -/
theorem exteriorRoute_regular {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    {k radius : ℕ} (hr : radius < k) :
    IsOrthogonal (exteriorRoute k radius G d i) ∧ IsSimple (exteriorRoute k radius G d i) :=
  ⟨isOrthogonal_cutStart (sourceRoute_regular hd hi).1 hr,
    isSimple_cutStart (sourceRoute_regular hd hi).1 (sourceRoute_regular hd hi).2 hr⟩

/-- The exterior incidence has its designated box port and the original scaled variable endpoint. -/
theorem exteriorRoute_endpoints {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    (k radius : ℕ) :
    (exteriorRoute k radius G d i).head? = some (exteriorPort k radius G d i) ∧
      (exteriorRoute k radius G d i).getLast? = some (k • sourceFinish G d i) := by
  obtain ⟨b, r, hr⟩ := sourceRoute_shape hd hi
  have hlast := (sourceRoute_endpoints hd hi).2
  rw [hr, List.getLast?_cons_cons] at hlast
  constructor
  · simp [exteriorRoute, exteriorPort, sourceDirection, hr, cutStart, cutPoint, List.getD]
  · change (cutStart k radius (sourceRoute G d i)).getLast? = _
    rw [hr]
    change (cutPoint k radius (sourceStart G d i) b :: k • b :: dilateRoute k r).getLast? = _
    rw [List.getLast?_cons_cons]
    change ((b :: r).map (k • ·)).getLast? = _
    rw [List.getLast?_map, hlast, Option.map_some]

/-- Cutting removes exactly the radius from the scaled Manhattan cost. -/
theorem exteriorRoute_wireLength {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    {k radius : ℕ} (hr : radius < k) :
    wireLength (exteriorRoute k radius G d i) + radius =
      k * wireLength (d.2.getD i []) := by
  rw [← wireLength_sourceRoute G d i]
  exact wireLength_cutStart (sourceRoute_regular hd hi).1 (sourceRoute_length_ge_two hd hi) hr

/-- Exterior incidence routes keep the original number of listed segments. -/
theorem exteriorRoute_segmentCount (k radius : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing)
    (i : ℕ) :
    (exteriorRoute k radius G d i).consecutivePairs.length =
      (d.2.getD i []).consecutivePairs.length := by
  rw [exteriorRoute, consecutivePairs_length_cutStart, consecutivePairs_length_sourceRoute]

/-- The exterior route meets its own closed clause box only at the designated port. -/
theorem exteriorRoute_box_contact {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    {k radius : ℕ} (hr : radius < k) {p : ℝ × ℝ}
    (hp : p ∈ support (exteriorRoute k radius G d i))
    (hb : inPointBox (k • sourceStart G d i) radius p) :
    p = realPoint (exteriorPort k radius G d i) := by
  obtain ⟨b, r, he⟩ := sourceRoute_shape hd hi
  have ho := (sourceRoute_regular hd hi).1
  have hs := (sourceRoute_regular hd hi).2
  rw [he] at ho hs
  change p ∈ support (cutStart k radius (sourceRoute G d i)) at hp
  rw [he] at hp
  have hport := cutStart_box_contact ho hs hr hp hb
  simpa [exteriorPort, sourceDirection, he, cutPoint, List.getD] using hport

/-- A nonincident declared vertex has a closed replacement box disjoint from an exterior route. -/
theorem exteriorRoute_avoids_box {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    {v : ℕ} (hv : v ∈ G.1) (hv₁ : v ≠ G.2[i].1) (hv₂ : v ≠ G.2[i].2)
    {k radius : ℕ} (hr : radius < k) {p : ℝ × ℝ}
    (hp : p ∈ support (exteriorRoute k radius G d i)) :
    ¬ inPointBox (k • Graph.drawingPosition G d v) radius p := by
  intro hb
  have hp' := support_cutStart_subset (sourceRoute_regular hd hi).1 hr hp
  rw [support_dilateRoute] at hp'
  obtain ⟨q, hq, rfl⟩ := hp'
  have hnear := near_of_scaled_box hr hb
  have hvertex := gridPoint_mem_support_of_near (sourceRoute_regular hd hi).1 hq hnear
  rw [support_sourceRoute] at hvertex
  exact (hd.avoidsVertices i hi v hv hvertex).elim hv₁ hv₂

/-- The exit direction is one of the four cardinal unit vectors. -/
theorem sourceDirection_unit (G : Graph) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    UnitVector (sourceDirection G d i) := direction_unit _ _

/-- A positive-radius port is different from the removed source clause center. -/
theorem exteriorPort_ne_center (k radius : ℕ) (hr : 0 < radius) (G : Graph)
    (d : Graph.OrthogonalDrawing) (i : ℕ) :
    exteriorPort k radius G d i ≠ k • sourceStart G d i := by
  intro he
  have hz : radius • sourceDirection G d i = (0 : Point) :=
    add_left_cancel (he.trans (add_zero _).symm)
  change radius • sourceDirection G d i = (0, 0) at hz
  have hd := sourceDirection_unit G d i
  rcases hd with hd | hd | hd | hd
  all_goals
    simp only [hd, Prod.smul_mk, Int.nsmul_eq_mul, Prod.mk.injEq,
      mul_one, mul_zero, mul_neg_one] at hz
    omega

/-- A trimmed incidence no longer contains the scaled source clause vertex. -/
theorem exteriorRoute_not_mem_center {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i : ℕ} (hi : i < G.2.length)
    {k radius : ℕ} (hr₀ : 0 < radius) (hr : radius < k) :
    realPoint (k • sourceStart G d i) ∉ support (exteriorRoute k radius G d i) := by
  intro hp
  have hb : inPointBox (k • sourceStart G d i) radius
      (realPoint (k • sourceStart G d i)) := by
    simp only [inPointBox, realPoint]
    have hn : (0 : ℝ) ≤ radius := Nat.cast_nonneg _
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have he := exteriorRoute_box_contact hd hi hr hp hb
  exact exteriorPort_ne_center k radius hr₀ G d i (realPoint_injective he.symm)

private theorem real_dilation_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (fun p : ℝ × ℝ => (k : ℝ) • p) := by
  rintro ⟨ax, ay⟩ ⟨bx, by'⟩ he
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at he
  exact Prod.ext (mul_left_cancel₀ hk' he.1) (mul_left_cancel₀ hk' he.2)

/-- Different exterior incidences can meet only at their shared scaled variable endpoint.
The common source clause endpoint has been removed by the positive-radius cut. -/
theorem exteriorRoute_contacts {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j)
    {k radius : ℕ} (hr₀ : 0 < radius) (hr : radius < k) {p : ℝ × ℝ}
    (hp : p ∈ support (exteriorRoute k radius G d i))
    (hq : p ∈ support (exteriorRoute k radius G d j)) :
    G.2[i].1 = G.2[j].1 ∧ p = realPoint (k • sourceFinish G d i) := by
  have hp' := support_cutStart_subset (sourceRoute_regular hd hi).1 hr hp
  have hq' := support_cutStart_subset (sourceRoute_regular hd hj).1 hr hq
  rw [support_dilateRoute] at hp' hq'
  obtain ⟨q, hq₁, he₁⟩ := hp'
  obtain ⟨r, hr₁, he₂⟩ := hq'
  have hqr : q = r := real_dilation_injective (by omega : k ≠ 0) (he₁.trans he₂.symm)
  subst r
  rw [support_sourceRoute] at hq₁ hr₁
  obtain ⟨v, _, hvi, hvj, hv⟩ := hd.contacts i hi j hj hij q hq₁ hr₁
  have hpv : p = realPoint (k • Graph.drawingPosition G d v) := by
    rw [← he₁, hv, realPoint_nsmul]
  have hvi₂ : v ≠ G.2[i].2 := by
    intro he
    have hs : sourceStart G d i = Graph.drawingPosition G d v := by
      rw [sourceStart, List.getD_eq_getElem _ _ hi, ← he]
    exact exteriorRoute_not_mem_center hd hi hr₀ hr (by simpa only [hs, hpv] using hp)
  have hvj₂ : v ≠ G.2[j].2 := by
    intro he
    have hs : sourceStart G d j = Graph.drawingPosition G d v := by
      rw [sourceStart, List.getD_eq_getElem _ _ hj, ← he]
    exact exteriorRoute_not_mem_center hd hj hr₀ hr (by simpa only [hs, hpv] using hq)
  have hvi₁ := hvi.resolve_right hvi₂
  have hvj₁ := hvj.resolve_right hvj₂
  refine ⟨hvi₁.symm.trans hvj₁, ?_⟩
  rw [hpv, sourceFinish, List.getD_eq_getElem _ _ hi, ← hvi₁]

/-- A different source vertex center lies outside the closed local replacement box. -/
theorem sourceVertex_not_mem_box {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing G d) {v w : ℕ} (hv : v ∈ G.1) (hw : w ∈ G.1)
    (hvw : v ≠ w) {k radius : ℕ} (hr : radius < k) :
    ¬ inPointBox (k • Graph.drawingPosition G d v) radius
      (realPoint (k • Graph.drawingPosition G d w)) := by
  intro hb
  rw [realPoint_nsmul] at hb
  have he := eq_of_nearGridPoint (near_of_scaled_box hr hb)
  exact hvw (drawingPosition_injOn hd hv hw he.symm)

end Cslib.Complexity.SAT.ExactOne
