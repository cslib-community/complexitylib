/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.Neighborhood
public import Complexity.Foundations.Geometry.Orthogonal.Layout

/-!
# Unit neighbors at canonical endpoint ports

## Main definitions

* `Cslib.Orthogonal.Layout.portStep`: the left, upward and right unit port directions.

## Main results

* `Cslib.Orthogonal.infix_head_pair_getD`, `.infix_last_pair_getD`: indexed endpoint neighbors
  from a consecutive pair in a path without repetitions.
* `Cslib.Orthogonal.Layout.fanWalk`, `.returnFanWalk`: the exact two-step endpoint fans.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- A consecutive pair starting at the unique first point determines index one. -/
theorem infix_head_pair_getD {r : Route} (hn : r.Nodup) {a b : Point}
    (hp : [a, b] <:+: r) (hh : r.head? = some a) (d : Point) :
    2 ≤ r.length ∧ r.getD 1 d = b := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.1 hh
  obtain ⟨start, hlen, hitems⟩ := List.infix_iff_getElem?.1 hp
  have hs : start < (a :: tail).length := by
    simp only [List.length_cons, List.length_nil] at hlen ⊢
    omega
  have ha : (a :: tail)[start] = a := by
    have h := hitems 0 (by simp)
    change (a :: tail)[0 + start]? = some a at h
    simpa only [Nat.zero_add, List.getElem?_eq_getElem hs, Option.some.injEq] using h
  have hz : start = 0 := hn.getElem_inj_iff.1 (ha.trans (show (a :: tail)[0] = a from rfl).symm)
  subst start
  refine ⟨by simpa using hlen, ?_⟩
  have hb := hitems 1 (by simp)
  change (a :: tail)[1 + 0]? = some b at hb
  simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]

/-- A consecutive pair ending at the unique final point determines the penultimate index. -/
theorem infix_last_pair_getD {r : Route} (hn : r.Nodup) {a b : Point}
    (hp : [a, b] <:+: r) (hh : r.getLast? = some b) (d : Point) :
    2 ≤ r.length ∧ r.getD (r.length - 2) d = a := by
  obtain ⟨initial, rfl⟩ := List.getLast?_eq_some_iff.1 hh
  obtain ⟨start, hlen, hitems⟩ := List.infix_iff_getElem?.1 hp
  have hs : start + 1 < (initial ++ [b]).length := by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have hb : (initial ++ [b])[start + 1] = b := by
    have h := hitems 1 (by simp)
    change (initial ++ [b])[1 + start]? = some b at h
    simpa only [Nat.add_comm 1 start, List.getElem?_eq_getElem hs, Option.some.injEq] using h
  have hl : initial.length < (initial ++ [b]).length := by simp
  have he : (initial ++ [b])[initial.length] = b := by simp
  have hz : start + 1 = initial.length := hn.getElem_inj_iff.1 (hb.trans he.symm)
  have hk : (initial ++ [b]).length - 2 = start := by
    simp only [List.length_append, List.length_cons, List.length_nil] at *
    omega
  refine ⟨?_, ?_⟩
  · simp only [List.length_cons, List.length_nil] at hlen
    omega
  · have ha := hitems 0 (by simp)
    change (initial ++ [b])[0 + start]? = some a at ha
    rw [Nat.zero_add] at ha
    rw [hk, List.getD_eq_getElem?_getD, ha, Option.getD_some]

namespace Layout

/-- The unit directions of the left, upward and right canonical endpoint ports. -/
def portStep (s : Fin 3) : Point := if s = 0 then (-1, 0) else if s = 1 then (0, 1) else (1, 0)

/-- Distinct ports have distinct unit directions. -/
theorem portStep_injective : Function.Injective portStep := by
  intro s t h
  fin_cases s <;> fin_cases t <;> norm_num [portStep] at *

/-- The local fan has exactly two unit steps in its port's direction. -/
theorem fanWalk (v : ℕ) (s : Fin 3) :
    segmentWalk (center v) (elbow v s) =
      [center v, center v + portStep s, elbow v s] := by
  have hl : length (center v) (elbow v s) = 2 := by
    fin_cases s <;> norm_num [length, center, elbow, column]; ring_nf
  have hd : direction (center v) (elbow v s) = portStep s := by
    fin_cases s <;> norm_num [direction, center, elbow, column, portStep]; ring_nf; simp
  rw [segmentWalk, hl, hd]
  fin_cases s <;> norm_num [walk, center, elbow, column, portStep] <;>
    (try constructor) <;> omega

/-- The return fan has the same middle unit point in the reverse order. -/
theorem returnFanWalk (v : ℕ) (s : Fin 3) :
    segmentWalk (elbow v s) (center v) =
      [elbow v s, center v + portStep s, center v] := by
  have hl : length (elbow v s) (center v) = 2 := by
    fin_cases s <;> norm_num [length, center, elbow, column]; ring_nf
  have hd : direction (elbow v s) (center v) = -portStep s := by
    fin_cases s <;> norm_num [direction, center, elbow, column, portStep]; ring_nf; simp
  rw [segmentWalk, hl, hd]
  fin_cases s <;> norm_num [walk, center, elbow, column, portStep] <;>
    (try constructor) <;> omega

end Layout
end Cslib.Orthogonal
