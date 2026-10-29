/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Complexity.Foundations.Data.List.Counting
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Unit subdivision of finite orthogonal routes

## Main definitions

* `Cslib.Orthogonal.walk`: a finite sequence of repeated integer vector steps.
* `Cslib.Orthogonal.segmentWalk`, `Cslib.Orthogonal.subdivide`: unit subdivision of a segment
  or an entire polygonal route, listing a shared endpoint only once.
* `Cslib.Orthogonal.subdivideWithin`: finite enumeration capped by a per-segment step budget.

## Main results

* `Cslib.Orthogonal.walk_length`, `Cslib.Orthogonal.walk_head`,
  `Cslib.Orthogonal.walk_last`: size and endpoint formulas.
* `Cslib.Orthogonal.subdivide_head`, `Cslib.Orthogonal.subdivide_last`: endpoint preservation.
* `Cslib.Orthogonal.subdivide_length`: exact point count from original Manhattan wire length.
* `Cslib.Orthogonal.subdivide_unit`: every subdivided segment has Manhattan length one.
* `Cslib.Orthogonal.support_subdivide`: equality of the complete continuous real supports.
* `Cslib.Orthogonal.wireLength_subdivide`: exact wire-length preservation.
* `Cslib.Orthogonal.subdivide_nodup`: continuously simple orthogonal routes subdivide without
  repeating lattice points.
* `Cslib.Orthogonal.subdivideWithin_eq_of_wireLength_le`: recover full subdivision from a
  sufficient total-wire budget.
* `Cslib.Orthogonal.subdivideWithin_length_le`: explicit bounded output size.

## References

The unit-walk construction and bounded enumeration are original.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- The `k+1` lattice points obtained by taking `k` copies of vector `d` from `a`. -/
def walk (a d : Point) : ℕ → Route
  | 0 => [a]
  | k + 1 => a :: walk (a + d) d k

/-- One more listed point than steps. -/
@[simp] theorem walk_length (a d : Point) (k : ℕ) : (walk a d k).length = k + 1 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [walk, ih]

/-- The walk always starts at its prescribed first point. -/
@[simp] theorem walk_head (a d : Point) (k : ℕ) : (walk a d k).head? = some a := by
  cases k <;> rfl

/-- The walk ends after precisely `k` copies of the step vector. -/
@[simp] theorem walk_last (a d : Point) (k : ℕ) :
    (walk a d k).getLast? = some (a + k • d) := by
  induction k generalizing a with
  | zero => simp [walk]
  | succ k ih =>
    rw [walk, List.getLast?_cons, ih]
    simp only [Option.getD_some]
    congr 1
    rw [add_smul, one_smul]
    abel

private theorem support_cons_of_head (a b : Point) {r : Route} (h : r.head? = some b) :
    support (a :: r) = segment a b ∪ support r := by
  cases r with
  | nil => simp at h
  | cons c r =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst c
    exact support_cons_cons a b r

/-- A step vector in one of the four cardinal unit directions. -/
def UnitVector (d : Point) : Prop :=
  d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

private theorem segment_step_union (a d : Point) (k : ℕ) (hd : UnitVector d) :
    segment a (a + d) ∪ segment (a + d) (a + (k + 1) • d) =
      segment a (a + (k + 1) • d) := by
  rcases a with ⟨x, y⟩
  rcases hd with rfl | rfl | rfl | rfl
  all_goals ext p
  all_goals norm_num only [segment, realPoint, Prod.smul_mk, nsmul_eq_mul,
    Prod.fst_add, Prod.snd_add, mul_one, mul_zero, mul_neg_one, add_zero, Int.cast_add,
    Int.cast_one, Int.cast_zero, Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
    Set.mem_union]
  all_goals
    first
    | rw [mem_horizontal, mem_horizontal, mem_horizontal]
    | rw [mem_vertical, mem_vertical, mem_vertical]
  all_goals have hk : (0 : ℝ) ≤ k := by positivity
  all_goals simp only [Set.mem_uIcc]
  all_goals grind

/-- Cardinal walks cover exactly the original continuous segment. -/
theorem support_walk (a d : Point) (k : ℕ) (hd : UnitVector d) :
    support (walk a d k) = segment a (a + k • d) := by
  induction k generalizing a with
  | zero => simp [walk, support, segment, List.consecutivePairs]
  | succ k ih =>
    rw [walk, support_cons_of_head a (a + d) (walk_head _ _ _), ih]
    have heq : a + d + k • d = a + (k + 1) • d := by rw [add_smul, one_smul]; abel
    rw [heq]
    exact segment_step_union a d k hd

private theorem consecutivePairs_walk (a d : Point) (k : ℕ) :
    (walk a d (k + 1)).consecutivePairs =
      (a, a + d) :: (walk (a + d) d k).consecutivePairs := by
  cases k <;> rfl

/-- Every consecutive pair in a repeated walk is exactly one prescribed step. -/
theorem walk_step {a d : Point} {k : ℕ} {e : Point × Point}
    (he : e ∈ (walk a d k).consecutivePairs) : e.2 = e.1 + d := by
  induction k generalizing a with
  | zero => simp [walk, List.consecutivePairs] at he
  | succ k ih =>
    rw [consecutivePairs_walk] at he
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact ih he

/-- Cardinal steps have Manhattan length one. -/
theorem length_add_unit (a d : Point) (hd : UnitVector d) : length a (a + d) = 1 := by
  rcases a with ⟨x, y⟩
  rcases hd with rfl | rfl | rfl | rfl <;> simp [length]

/-- Every consecutive pair of a cardinal walk is unit-adjacent. -/
theorem walk_unit {a d : Point} {k : ℕ} (hd : UnitVector d) {e : Point × Point}
    (he : e ∈ (walk a d k).consecutivePairs) : length e.1 e.2 = 1 := by
  rw [walk_step he]
  exact length_add_unit _ _ hd

/-- A `k`-step cardinal walk has exactly `k` units of wire. -/
theorem wireLength_walk (a d : Point) (k : ℕ) (hd : UnitVector d) :
    wireLength (walk a d k) = k := by
  induction k generalizing a with
  | zero => simp [walk, wireLength, List.consecutivePairs]
  | succ k ih =>
    simp only [wireLength, consecutivePairs_walk, List.map_cons, List.sum_cons]
    rw [length_add_unit a d hd, ← wireLength, ih]
    omega

/-- Cardinal direction from `a` toward `b`; equal points use an arbitrary unit direction. -/
def direction (a b : Point) : Point :=
  if a.1 < b.1 then (1, 0) else if b.1 < a.1 then (-1, 0) else
    if a.2 < b.2 then (0, 1) else (0, -1)

/-- The chosen direction is always a cardinal unit vector. -/
theorem direction_unit (a b : Point) : UnitVector (direction a b) := by
  unfold direction UnitVector
  split_ifs <;> simp

/-- An axis-aligned displacement is its Manhattan length times its chosen unit direction. -/
theorem add_length_direction {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    a + length a b • direction a b = b := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  unfold direction
  split_ifs <;> ext <;>
    norm_num only [length, Prod.smul_mk, Int.nsmul_eq_mul, Nat.cast_add, Nat.cast_natAbs,
    Int.cast_abs, Int.cast_sub, Int.cast_eq, mul_one, nsmul_zero, mul_neg_one,
    Prod.mk_add_mk, add_zero] <;>
    (try simp only [abs_eq_max_neg]) <;> omega

/-- Unit subdivision of one segment, including both endpoints. -/
def segmentWalk (a b : Point) : Route := walk a (direction a b) (length a b)

/-- Segment subdivision uses exactly one more point than its Manhattan length. -/
@[simp] theorem segmentWalk_length (a b : Point) :
    (segmentWalk a b).length = length a b + 1 := walk_length ..

/-- Segment subdivision preserves the first endpoint. -/
@[simp] theorem segmentWalk_head (a b : Point) : (segmentWalk a b).head? = some a := walk_head ..

/-- Segment subdivision preserves the last endpoint of every axis-aligned segment. -/
theorem segmentWalk_last {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    (segmentWalk a b).getLast? = some b := by
  rw [segmentWalk, walk_last, add_length_direction h]

/-- The subdivision covers the entire original real segment, without adding points. -/
theorem support_segmentWalk {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    support (segmentWalk a b) = segment a b := by
  rw [segmentWalk, support_walk _ _ _ (direction_unit _ _), add_length_direction h]

/-- Each subdivided segment has unit Manhattan length. -/
theorem segmentWalk_unit (a b : Point) {e : Point × Point}
    (he : e ∈ (segmentWalk a b).consecutivePairs) : length e.1 e.2 = 1 :=
  walk_unit (direction_unit a b) he

/-- Segment subdivision preserves wire length exactly. -/
theorem wireLength_segmentWalk (a b : Point) : wireLength (segmentWalk a b) = length a b :=
  wireLength_walk _ _ _ (direction_unit _ _)

/-- Joining routes at a common endpoint, listing that endpoint once, concatenates their
segment lists. -/
theorem consecutivePairs_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    (q ++ r.tail).consecutivePairs = q.consecutivePairs ++ r.consecutivePairs := by
  induction q with
  | nil => simp at hq
  | cons a q ih =>
    cases q with
    | nil =>
      cases r with
      | nil => simp at hr
      | cons b r =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hq
        simp only [List.head?_cons, Option.some.injEq] at hr
        subst a
        subst b
        rfl
    | cons b q =>
      have hq' : (b :: q).getLast? = some p := by
        simpa only [List.getLast?_cons_cons] using hq
      change (a, b) :: ((b :: q) ++ r.tail).consecutivePairs =
        (a, b) :: ((b :: q).consecutivePairs ++ r.consecutivePairs)
      rw [ih hq']

/-- Joining routes at their common endpoint takes the union of their full real supports. -/
theorem support_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    support (q ++ r.tail) = support q ∪ support r := by
  have hmem := List.mem_of_getLast? hq
  have hpairs := consecutivePairs_join hq hr
  cases r with
  | nil => simp at hr
  | cons b r =>
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst b
    ext z
    simp only [support, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
      List.tail_cons, Set.mem_union, or_and_right, exists_or, exists_eq_left]
    aesop

/-- A route joined at a common endpoint has the last endpoint of the second route. -/
theorem last_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    (q ++ r.tail).getLast? = r.getLast? := by
  cases r with
  | nil => simp at hr
  | cons b r =>
    cases r with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst b
      simpa using hq
    | cons c r =>
      simp [List.getLast?_append,
        List.getLast?_eq_some_getLast (l := c :: r) (by simp)]

/-- Joining at a common endpoint adds the two Manhattan wire lengths. -/
theorem wireLength_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    wireLength (q ++ r.tail) = wireLength q + wireLength r := by
  simp only [wireLength, consecutivePairs_join hq hr, List.map_append, List.sum_append]

/-- Replace each consecutive segment by its unit walk, retaining a shared endpoint once. -/
def subdivide : Route → Route
  | [] => []
  | [a] => [a]
  | a :: b :: r => segmentWalk a b ++ (subdivide (b :: r)).tail

/-- Subdivision preserves the first listed point, including the empty-route convention. -/
@[simp] theorem subdivide_head (r : Route) : (subdivide r).head? = r.head? := by
  cases r with
  | nil => rfl
  | cons a r =>
    cases r with
    | nil => rfl
    | cons b r => simp [subdivide, List.head?_append]

/-- The exact point count is wire length plus one for a nonempty route. -/
theorem subdivide_length (r : Route) :
    (subdivide r).length = wireLength r + if r = [] then 0 else 1 := by
  induction r with
  | nil => simp [subdivide, wireLength, List.consecutivePairs]
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide, wireLength, List.consecutivePairs]
    | cons b r =>
      have hwire : wireLength (a :: b :: r) = length a b + wireLength (b :: r) := rfl
      simp only [subdivide, List.length_append, List.length_tail, segmentWalk_length,
        List.cons_ne_nil, ↓reduceIte] at ih ⊢
      rw [hwire]
      omega

/-- Subdivision preserves the final endpoint of an orthogonal route. -/
theorem subdivide_last {r : Route} (hr : IsOrthogonal r) :
    (subdivide r).getLast? = r.getLast? := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      rw [subdivide, last_join (segmentWalk_last hab) (subdivide_head (b :: r)), ih htail,
        List.getLast?_cons_cons]

/-- Subdivision preserves the complete real support of every orthogonal route. -/
theorem support_subdivide {r : Route} (hr : IsOrthogonal r) :
    support (subdivide r) = support r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      rw [subdivide, support_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        support_segmentWalk hab, ih htail, support_cons_cons]

/-- Every consecutive pair in the subdivided orthogonal route is a unit grid step. -/
theorem subdivide_unit {r : Route} (hr : IsOrthogonal r) {e : Point × Point}
    (he : e ∈ (subdivide r).consecutivePairs) : length e.1 e.2 = 1 := by
  induction r with
  | nil => simp [subdivide, List.consecutivePairs] at he
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide, List.consecutivePairs] at he
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      rw [subdivide, consecutivePairs_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        List.mem_append] at he
      rcases he with he | he
      · exact segmentWalk_unit a b he
      · exact ih htail he

/-- Unit subdivision preserves total Manhattan wire length exactly. -/
theorem wireLength_subdivide {r : Route} (hr : IsOrthogonal r) :
    wireLength (subdivide r) = wireLength r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      rw [subdivide, wireLength_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        wireLength_segmentWalk, ih htail]
      rfl

/-- Unit subdivision is itself a proper orthogonal route. -/
theorem subdivide_orthogonal {r : Route} (hr : IsOrthogonal r) : IsOrthogonal (subdivide r) :=
  fun _ he => axisAligned_of_length_eq_one (subdivide_unit hr he)

/-- The recursive walk is also an explicit range enumeration. -/
theorem walk_eq_map_range (a d : Point) (k : ℕ) :
    walk a d k = (List.range (k + 1)).map fun i => a + i • d := by
  induction k generalizing a with
  | zero => simp [walk]
  | succ k ih =>
    rw [walk, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    simp only [zero_smul, add_zero]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, succ_nsmul]
    abel

/-- Omitting the final endpoint gives exactly the strict prefix of the range enumeration. -/
theorem walk_dropLast_eq_map_range (a d : Point) (k : ℕ) :
    (walk a d k).dropLast = (List.range k).map fun i => a + i • d := by
  rw [walk_eq_map_range, List.range_succ, List.map_append]
  simp

private theorem join_eq_dropLast_append {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    q ++ r.tail = q.dropLast ++ r := by
  obtain ⟨initial, rfl⟩ := List.getLast?_eq_some_iff.1 hq
  cases r with
  | nil => simp at hr
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst a
    simp

/-- A flat enumeration of the unit subdivision: emit each segment without its last point, then
emit the route's final endpoint. This form supports bounded polynomial-time implementations. -/
theorem subdivide_eq_flatMap {r : Route} (hr : IsOrthogonal r) :
    subdivide r =
      (r.consecutivePairs.flatMap fun e => (segmentWalk e.1 e.2).dropLast) ++
        r.getLast?.toList := by
  induction r with
  | nil => simp [subdivide, List.consecutivePairs]
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide, List.consecutivePairs]
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      rw [subdivide, join_eq_dropLast_append (segmentWalk_last hab) (subdivide_head (b :: r)),
        ih htail]
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.flatMap_cons,
        List.getLast?_cons_cons, List.append_assoc]

/-- Enumerate at most `budget` strict unit-prefix points per listed segment, then the last
endpoint. The result agrees with `subdivide` when every segment fits in the budget. -/
def subdivideWithin (budget : ℕ) (r : Route) : Route :=
  (r.consecutivePairs.flatMap fun e =>
    (List.range (min (length e.1 e.2) budget)).map fun i => e.1 + i • direction e.1 e.2) ++
      r.getLast?.toList

/-- A sufficient per-segment budget recovers the complete geometric subdivision. -/
theorem subdivideWithin_eq_subdivide {r : Route} (hr : IsOrthogonal r) {budget : ℕ}
    (hbudget : ∀ e ∈ r.consecutivePairs, length e.1 e.2 ≤ budget) :
    subdivideWithin budget r = subdivide r := by
  rw [subdivide_eq_flatMap hr]
  unfold subdivideWithin
  congr 1
  apply List.flatMap_congr
  intro e he
  rw [min_eq_left (hbudget e he), segmentWalk, walk_dropLast_eq_map_range]

/-- Bounded enumeration emits at most `budget` points per segment, plus the last endpoint. -/
theorem subdivideWithin_length_le (budget : ℕ) (r : Route) :
    (subdivideWithin budget r).length ≤ budget * r.consecutivePairs.length + 1 := by
  have hb := List.length_flatMap_le (l := r.consecutivePairs) (k := budget)
    (f := fun e => (List.range (min (length e.1 e.2) budget)).map
      fun i => e.1 + i • direction e.1 e.2)
    (fun _ _ => by simpa only [List.length_map, List.length_range] using min_le_right _ _)
  have hlast : r.getLast?.toList.length ≤ 1 := by cases r.getLast? <;> simp
  unfold subdivideWithin
  rw [List.length_append, Nat.mul_comm]
  omega

/-- Each listed segment's length is bounded by the route's total wire length. -/
theorem length_le_wireLength {r : Route} {e : Point × Point} (he : e ∈ r.consecutivePairs) :
    length e.1 e.2 ≤ wireLength r :=
  List.le_sum_of_mem (List.mem_map.2 ⟨e, he, rfl⟩)

/-- A bound for the whole route's wire length is a sufficient subdivision budget. -/
theorem subdivideWithin_eq_of_wireLength_le {r : Route} (hr : IsOrthogonal r) {budget : ℕ}
    (hbudget : wireLength r ≤ budget) : subdivideWithin budget r = subdivide r :=
  subdivideWithin_eq_subdivide hr (fun _ he => (length_le_wireLength he).trans hbudget)

/-- A cardinal walk never repeats a lattice point. -/
theorem walk_nodup (a d : Point) (k : ℕ) (hd : UnitVector d) : (walk a d k).Nodup := by
  rw [walk_eq_map_range]
  apply List.Nodup.map (l := List.range (k + 1)) ?_ List.nodup_range
  intro i j hij
  rcases hd with rfl | rfl | rfl | rfl
  all_goals
    have hx := congrArg Prod.fst hij
    have hy := congrArg Prod.snd hij
    simp only [Prod.smul_mk, Int.nsmul_eq_mul, mul_one, nsmul_zero, Prod.fst_add,
      Prod.snd_add, add_zero, mul_neg_one, add_right_inj, Nat.cast_inj, neg_inj] at hx hy
    omega

/-- The unit walk along one segment has no repeated listed point. -/
theorem segmentWalk_nodup (a b : Point) : (segmentWalk a b).Nodup :=
  walk_nodup _ _ _ (direction_unit _ _)

/-- Every supported point of a route with at least two listed points belongs to one of its
consecutive segments. In this case separate degenerate pieces for listed points are redundant. -/
theorem mem_support_segment {r : Route} (hlen : 2 ≤ r.length) {p : ℝ × ℝ}
    (hp : p ∈ support r) : ∃ e ∈ r.consecutivePairs, p ∈ segment e.1 e.2 := by
  induction r with
  | nil => simp at hlen
  | cons a r ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      rw [support_cons_cons] at hp
      rcases hp with hp | hp
      · exact ⟨(a, b), by simp [List.consecutivePairs], hp⟩
      · cases r with
        | nil =>
          have hp' : p = realPoint b := by simpa [support, List.consecutivePairs] using hp
          exact ⟨(a, b), by simp [List.consecutivePairs], hp' ▸ right_mem_segment ℝ _ _⟩
        | cons c r =>
          obtain ⟨e, he, hp⟩ := ih (by simp) hp
          exact ⟨e, by simpa only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons,
            List.mem_cons] using Or.inr he, hp⟩

/-- The first segment of a continuously simple route meets its tail only at their common
listed endpoint. -/
theorem first_segment_tail_contact {a b : Point} {r : Route}
    (hs : IsSimple (a :: b :: r)) {p : ℝ × ℝ} (hp : p ∈ segment a b)
    (hq : p ∈ support (b :: r)) : p = realPoint b := by
  have hnot := (List.nodup_cons.1 hs.1).1
  cases r with
  | nil => simpa [support, List.consecutivePairs] using hq
  | cons c r =>
    obtain ⟨f, hf, hpf⟩ := mem_support_segment (by simp) hq
    have hfmem := List.of_mem_zip hf
    have hne : (a, b) ≠ f := by
      intro h
      apply hnot
      simpa only [← h] using hfmem.1
    have hf' : f ∈ (a :: b :: c :: r).consecutivePairs := by
      simpa only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons]
        using Or.inr hf
    have hc := hs.2 (a, b) (by simp [List.consecutivePairs]) f hf' hne p hp hpf
    rcases hc.1 with hpa | hpb
    · change p = realPoint a at hpa
      exfalso
      apply hnot
      rcases hc.2 with hpf | hpf
      · rw [realPoint_injective (hpa.symm.trans hpf)]
        exact hfmem.1
      · rw [realPoint_injective (hpa.symm.trans hpf)]
        exact List.mem_of_mem_tail hfmem.2
    · exact hpb

/-- Unit subdivision of a continuously simple orthogonal route has no repeated lattice points.
The proof uses the original segments' endpoint-contact certificates, not support equality alone. -/
theorem subdivide_nodup {r : Route} (hr : IsOrthogonal r) (hs : IsSimple r) :
    (subdivide r).Nodup := by
  induction r with
  | nil => simp [subdivide]
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide]
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := hr.of_cons
      have hstail : IsSimple (b :: r) := hs.of_cons
      have hnd := ih htail hstail
      obtain ⟨rest, hsub⟩ := List.head?_eq_some_iff.1 (subdivide_head (b :: r))
      have hrest : (b :: rest).Nodup := by simpa only [hsub] using hnd
      rw [subdivide, hsub]
      refine List.nodup_append.2 ⟨segmentWalk_nodup a b, hrest.tail, ?_⟩
      intro x hx y hy hxy
      subst y
      have hxq : realPoint x ∈ support (segmentWalk a b) := Or.inl ⟨x, hx, rfl⟩
      rw [support_segmentWalk hab] at hxq
      have hxt : realPoint x ∈ support (subdivide (b :: r)) := by
        refine Or.inl ⟨x, ?_, rfl⟩
        rw [hsub]
        exact List.mem_cons_of_mem _ hy
      rw [support_subdivide htail] at hxt
      have hxb := realPoint_injective (first_segment_tail_contact hs hxq hxt)
      subst x
      exact (List.nodup_cons.1 hrest).1 hy

/-- A sufficient-budget native enumeration also has no repeated points on a simple route. -/
theorem subdivideWithin_nodup {r : Route} (hr : IsOrthogonal r) (hs : IsSimple r) {budget : ℕ}
    (hbudget : wireLength r ≤ budget) : (subdivideWithin budget r).Nodup := by
  rw [subdivideWithin_eq_of_wireLength_le hr hbudget]
  exact subdivide_nodup hr hs

end Cslib.Orthogonal
