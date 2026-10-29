/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Scale
public import Complexity.Foundations.Geometry.Orthogonal.Isolation
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-distance cutting of dilated incidence routes

After dilation by `k`, every original proper integer segment has length at least `k`.
Consequently a fixed `radius < k` can be removed from the initial segment of every route.
The operation preserves the original list length, proper orthogonality, and continuous
simplicity, shrinks the dilated support, and removes exactly `radius` units of wire.

## Main definitions

* `cutPoint`: the point at a fixed distance along a dilated first segment.
* `cutStart`: dilate a route and remove a fixed initial distance.

## Main results

* `isOrthogonal_cutStart`, `isSimple_cutStart`, `support_cutStart_subset`.
* `length_cutStart`, `wireLength_cutStart`.

## References

The integer-grid endpoint refinement and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal


/-- A point at a fixed distance along a dilated segment's cardinal direction. -/
def cutPoint (k radius : ℕ) (a b : Point) : Point :=
  k • a + radius • direction a b

/-- Dilate a route and cut a fixed length from its first segment. Degenerate input lists
are merely dilated; geometric correctness is stated for proper routes of length at least two. -/
def cutStart (k radius : ℕ) : Route → Route
  | a :: b :: r => cutPoint k radius a b :: k • b :: dilateRoute k r
  | r => dilateRoute k r

/-- A proper integer segment has positive Manhattan length. -/
theorem length_pos_of_axisAligned {a b : Point} (hab : AxisAligned a b) :
    0 < length a b := by
  have hn := hab.2
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [length, ne_eq, Prod.mk.injEq] at hn ⊢
  omega

/-- Multiples along a cardinal ray have their expected Manhattan distances. -/
theorem length_add_nsmul_unit (a d : Point) (n : ℕ) (hd : UnitVector d) :
    length a (a + n • d) = n := by
  rcases a with ⟨ax, ay⟩
  rcases hd with rfl | rfl | rfl | rfl <;>
    simp [length, Prod.smul_mk]

/-- Distinct natural distances specify distinct points along a cardinal ray. -/
theorem nsmul_unit_injective (a d : Point) (hd : UnitVector d) :
    Function.Injective (fun n : ℕ => a + n • d) := by
  intro i j hij
  have hi := length_add_nsmul_unit a d i hd
  have hj := length_add_nsmul_unit a d j hd
  change a + i • d = a + j • d at hij
  rw [hij] at hi
  exact hi.symm.trans hj

private theorem dilated_endpoint {a b : Point} (hab : a.1 = b.1 ∨ a.2 = b.2) (k : ℕ) :
    k • b = k • a + (k * length a b) • direction a b := by
  calc
    k • b = k • (a + length a b • direction a b) :=
      congrArg (k • ·) (add_length_direction hab).symm
    _ = k • a + (k * length a b) • direction a b := by rw [smul_add, smul_smul]

/-- A cut shorter than the dilation factor lies on every dilated proper first segment. -/
theorem cutPoint_mem_segment {a b : Point} (hab : AxisAligned a b)
    {k radius : ℕ} (hr : radius < k) :
    realPoint (cutPoint k radius a b) ∈ segment (k • a) (k • b) := by
  have hlen := length_pos_of_axisAligned hab
  have hrad : radius < k * length a b := by nlinarith
  have hm : cutPoint k radius a b ∈ walk (k • a) (direction a b) (k * length a b) := by
    rw [walk_eq_map_range]
    exact List.mem_map.mpr ⟨radius, List.mem_range.mpr (by omega), rfl⟩
  have hp : realPoint (cutPoint k radius a b) ∈
      support (walk (k • a) (direction a b) (k * length a b)) := Or.inl ⟨_, hm, rfl⟩
  rw [support_walk _ _ _ (direction_unit a b), ← dilated_endpoint hab.1] at hp
  exact hp

/-- A short cut never reaches the other endpoint of a proper dilated first segment. -/
theorem cutPoint_ne_endpoint {a b : Point} (hab : AxisAligned a b)
    {k radius : ℕ} (hr : radius < k) : cutPoint k radius a b ≠ k • b := by
  have hlen := length_pos_of_axisAligned hab
  have hrad : radius < k * length a b := by nlinarith
  intro h
  rw [dilated_endpoint hab.1] at h
  have he := nsmul_unit_injective (k • a) (direction a b) (direction_unit a b) h
  omega

/-- Cutting never changes the number of listed route points. -/
theorem length_cutStart (k radius : ℕ) (r : Route) : (cutStart k radius r).length = r.length := by
  cases r with
  | nil => rfl
  | cons a r =>
    cases r with
    | nil => rfl
    | cons b r => simp [cutStart, dilateRoute]

/-- Cutting never changes the number of listed segments. -/
theorem consecutivePairs_length_cutStart (k radius : ℕ) (r : Route) :
    (cutStart k radius r).consecutivePairs.length = r.consecutivePairs.length := by
  simp only [List.consecutivePairs, List.length_zip, List.length_tail, length_cutStart]

/-- The fixed cut preserves proper orthogonality. -/
theorem isOrthogonal_cutStart {r : Route} (ho : IsOrthogonal r)
    {k radius : ℕ} (hr : radius < k) : IsOrthogonal (cutStart k radius r) := by
  have hk : k ≠ 0 := by omega
  cases r with
  | nil => exact (isOrthogonal_dilateRoute_iff hk []).2 ho
  | cons a r =>
    cases r with
    | nil => exact (isOrthogonal_dilateRoute_iff hk [a]).2 ho
    | cons b r =>
      have hab := ho (a, b) (by simp [List.consecutivePairs])
      exact isOrthogonal_cut_first ((isOrthogonal_dilateRoute_iff hk _).2 ho)
        (cutPoint_mem_segment hab hr) (cutPoint_ne_endpoint hab hr)

/-- The fixed cut preserves continuous route simplicity. -/
theorem isSimple_cutStart {r : Route} (ho : IsOrthogonal r) (hs : IsSimple r)
    {k radius : ℕ} (hr : radius < k) : IsSimple (cutStart k radius r) := by
  have hk : k ≠ 0 := by omega
  cases r with
  | nil => exact (isSimple_dilateRoute_iff hk []).2 hs
  | cons a r =>
    cases r with
    | nil => exact (isSimple_dilateRoute_iff hk [a]).2 hs
    | cons b r =>
      have hab := ho (a, b) (by simp [List.consecutivePairs])
      exact isSimple_cut_first ((isSimple_dilateRoute_iff hk _).2 hs)
        (cutPoint_mem_segment hab hr) (cutPoint_ne_endpoint hab hr)

/-- Every point of the cut route still belongs to the original dilated route. -/
theorem support_cutStart_subset {r : Route} (ho : IsOrthogonal r)
    {k radius : ℕ} (hr : radius < k) :
    support (cutStart k radius r) ⊆ support (dilateRoute k r) := by
  cases r with
  | nil => exact Set.Subset.rfl
  | cons a r =>
    cases r with
    | nil => exact Set.Subset.rfl
    | cons b r =>
      have hab := ho (a, b) (by simp [List.consecutivePairs])
      exact support_cut_first_subset (cutPoint_mem_segment hab hr)

/-- The removed initial segment has precisely the chosen radius. -/
theorem length_cutPoint (k radius : ℕ) (a b : Point) :
    length (k • a) (cutPoint k radius a b) = radius :=
  length_add_nsmul_unit _ _ _ (direction_unit a b)

/-- A proper route loses exactly the chosen radius from its dilated wire length. -/
theorem wireLength_cutStart {r : Route} (ho : IsOrthogonal r) (hlen : 2 ≤ r.length)
    {k radius : ℕ} (hr : radius < k) :
    wireLength (cutStart k radius r) + radius = k * wireLength r := by
  cases r with
  | nil => simp at hlen
  | cons a r =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      have hab := ho (a, b) (by simp [List.consecutivePairs])
      have hm := cutPoint_mem_segment hab hr
      have hk : k ≠ 0 := by omega
      have ha' : (k • a).1 = (k • b).1 ∨ (k • a).2 = (k • b).2 :=
        ((axisAligned_nsmul_iff hk a b).2 hab).1
      have he := wireLength_cut_first (r := dilateRoute k r) ha' hm
      simpa only [length_cutPoint, ← wireLength_dilateRoute, cutStart, dilateRoute,
        List.map_cons] using he

/-- A closed real square centered on an integer grid point. -/
def inPointBox (a : Point) (radius : ℕ) (p : ℝ × ℝ) : Prop :=
  (a.1 : ℝ) - radius ≤ p.1 ∧ p.1 ≤ (a.1 : ℝ) + radius ∧
    (a.2 : ℝ) - radius ≤ p.2 ∧ p.2 ≤ (a.2 : ℝ) + radius

private theorem ray_segment_box_contact {a d : Point} (hd : UnitVector d)
    {radius n : ℕ} (hr : radius ≤ n) {p : ℝ × ℝ}
    (hp : p ∈ segment (a + radius • d) (a + n • d)) (hb : inPointBox a radius p) :
    p = realPoint (a + radius • d) := by
  have hr' : (radius : ℝ) ≤ n := by exact_mod_cast hr
  have hp' := mem_segment_bounds hp
  rcases a with ⟨ax, ay⟩
  rcases hd with rfl | rfl | rfl | rfl
  all_goals
    simp only [Prod.smul_mk, Int.nsmul_eq_mul, Prod.mk_add_mk, Int.cast_add,
      Int.cast_natCast, Int.cast_neg, mul_one, mul_zero, mul_neg_one, add_zero] at hp'
    rcases hp' with ⟨hx, hy⟩
    rw [Set.mem_uIcc] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    all_goals
      apply Prod.ext <;>
        simp only [realPoint, Prod.smul_mk, Int.nsmul_eq_mul, Prod.mk_add_mk,
          Int.cast_add, Int.cast_natCast, Int.cast_neg, mul_one, mul_zero,
          mul_neg_one, add_zero] <;>
        simp only [inPointBox] at hb <;> linarith

/-- A box smaller than the integer dilation factor lies within the original open unit box
after dividing by that factor. -/
theorem near_of_scaled_box {a : Point} {q : ℝ × ℝ} {k radius : ℕ}
    (hr : radius < k) (hb : inPointBox (k • a) radius ((k : ℝ) • q)) :
    nearGridPoint a q := by
  have hr' : (radius : ℝ) < k := by exact_mod_cast hr
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_le radius).trans_lt hr
  change ((k • a).1 : ℝ) - radius ≤ (k : ℝ) * q.1 ∧
    (k : ℝ) * q.1 ≤ ((k • a).1 : ℝ) + radius ∧
    ((k • a).2 : ℝ) - radius ≤ (k : ℝ) * q.2 ∧
    (k : ℝ) * q.2 ≤ ((k • a).2 : ℝ) + radius at hb
  simp only [Prod.smul_fst, Prod.smul_snd, Int.nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at hb
  unfold nearGridPoint
  constructor
  · nlinarith [hb.1]
  constructor
  · nlinarith [hb.2.1]
  constructor <;> nlinarith [hb.2.2.1, hb.2.2.2]

/-- The trimmed exterior route meets the closed local clause box only at its designated
cut port. This controls all real points of the route. -/
theorem cutStart_box_contact {a b : Point} {r : Route}
    (ho : IsOrthogonal (a :: b :: r)) (hs : IsSimple (a :: b :: r))
    {k radius : ℕ} (hr : radius < k) {p : ℝ × ℝ}
    (hp : p ∈ support (cutStart k radius (a :: b :: r)))
    (hb : inPointBox (k • a) radius p) : p = realPoint (cutPoint k radius a b) := by
  have hab := ho (a, b) (by simp [List.consecutivePairs])
  have hlen := length_pos_of_axisAligned hab
  have hrad : radius ≤ k * length a b := by nlinarith
  change p ∈ support (cutPoint k radius a b :: k • b :: dilateRoute k r) at hp
  rw [support_cons_cons] at hp
  rcases hp with hp | hp
  · rw [dilated_endpoint hab.1] at hp
    exact ray_segment_box_contact (direction_unit a b) hrad hp hb
  · change p ∈ support (dilateRoute k (b :: r)) at hp
    rw [support_dilateRoute] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact False.elim ((not_near_head_tail ho hs hq) (near_of_scaled_box hr hb))

/-- Closed local boxes about distinct integer source vertices cannot meet when the
dilation factor is larger than twice their radius. -/
theorem eq_of_inPointBoxes {a b : Point} {k radius : ℕ} (hr : 2 * radius < k)
    {p : ℝ × ℝ} (ha : inPointBox (k • a) radius p) (hb : inPointBox (k • b) radius p) :
    a = b := by
  have hr' : 2 * (radius : ℝ) < k := by exact_mod_cast hr
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [inPointBox, Prod.smul_mk, Int.nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at ha hb
  apply Prod.ext
  · by_contra h
    have hd : ax + 1 ≤ bx ∨ bx + 1 ≤ ax := by omega
    rcases hd with hd | hd
    · have hd' : (ax : ℝ) + 1 ≤ bx := by exact_mod_cast hd
      nlinarith [ha.2.1, hb.1]
    · have hd' : (bx : ℝ) + 1 ≤ ax := by exact_mod_cast hd
      nlinarith [hb.2.1, ha.1]
  · by_contra h
    have hd : ay + 1 ≤ by' ∨ by' + 1 ≤ ay := by omega
    rcases hd with hd | hd
    · have hd' : (ay : ℝ) + 1 ≤ by' := by exact_mod_cast hd
      nlinarith [ha.2.2.2, hb.2.2.1]
    · have hd' : (by' : ℝ) + 1 ≤ ay := by exact_mod_cast hd
      nlinarith [hb.2.2.2, ha.2.2.1]

/-- Distinct source vertices have disjoint closed local boxes under a sufficiently large
integer dilation. -/
theorem pointBoxes_disjoint {a b : Point} (hab : a ≠ b) {k radius : ℕ}
    (hr : 2 * radius < k) :
    Disjoint {p | inPointBox (k • a) radius p} {p | inPointBox (k • b) radius p} := by
  rw [Set.disjoint_left]
  exact fun _ ha hb => hab (eq_of_inPointBoxes hr ha hb)

end Cslib.Orthogonal
