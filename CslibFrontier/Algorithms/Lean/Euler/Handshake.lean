/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Euler.Circuit
public import Mathlib.Algebra.Ring.Parity

/-!
# The handshake lemma for list multigraphs

For a finite multigraph given by an edge list `H : List (α × α)` (parallel edges and self-loops
allowed, `Cslib.Algorithms.Lean.Euler.degree` counting a self-loop twice), the degrees sum to twice
the number of edges, so an even number of vertices have odd degree. Christofides' algorithm uses
this to find a perfect matching on the odd-degree vertices of a spanning tree
([WilliamsonShmoys2011], Section 2.4).

Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges` and
`SimpleGraph.even_card_odd_degree_vertices` prove the same for simple graphs; the statements here
cover the list multigraphs of `Cslib.Algorithms.Lean.Euler`.

## Main results

* `sum_map_degree`: summed over a duplicate-free list of vertices containing every endpoint, the
  degrees count each edge twice.
* `even_length_filter_odd_degree`: the handshake lemma; such a list has an even number of entries
  of odd degree.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
-/

public section

namespace Cslib.Algorithms.Lean.Euler

variable {α : Type*} [DecidableEq α]

private theorem sum_map_ite_eq_count (V : List α) (y : α) :
    (V.map fun x => if x = y then 1 else 0).sum = V.count y := by
  induction V with
  | nil => rfl
  | cons a V ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons, beq_iff_eq]
    omega

/-- **Degree sum** for list multigraphs: summed over a duplicate-free list of vertices containing
every endpoint, the degrees count each edge twice. -/
theorem sum_map_degree {H : List (α × α)} {V : List α} (hV : V.Nodup)
    (hH : ∀ e ∈ H, e.1 ∈ V ∧ e.2 ∈ V) : (V.map (degree H)).sum = 2 * H.length := by
  induction H with
  | nil => induction V <;> simp_all
  | cons e H ih =>
    have he := hH e List.mem_cons_self
    have h1 := sum_map_ite_eq_count V e.1
    have h2 := sum_map_ite_eq_count V e.2
    rw [List.count_eq_one_of_mem hV he.1] at h1
    rw [List.count_eq_one_of_mem hV he.2] at h2
    have hsplit : (V.map (degree (e :: H))).sum =
        (V.map fun x => if x = e.1 then 1 else 0).sum +
          (V.map fun x => if x = e.2 then 1 else 0).sum + (V.map (degree H)).sum := by
      have hd : degree (e :: H) = fun x => ends x e + degree H x := funext (degree_cons e H)
      simp only [hd, ends, ← List.sum_map_add]
    rw [hsplit, ih fun f hf => hH f (List.mem_cons_of_mem e hf), h1, h2, List.length_cons]
    omega

omit [DecidableEq α] in
/-- The list analogue of Mathlib's `Finset.even_sum_iff_even_card_odd`, for lists that may repeat
entries. -/
private theorem even_sum_iff_even_length_filter_odd (V : List α) (f : α → ℕ) :
    Even (V.map f).sum ↔ Even (V.filter fun x => Odd (f x)).length := by
  induction V with
  | nil => simp
  | cons a V ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    by_cases ha : Odd (f a)
    · simp only [ha, decide_true, ↓reduceIte, List.length_cons]
      rw [Nat.even_add, Nat.even_add_one, ih]
      simp only [Nat.not_even_iff_odd.symm] at ha
      tauto
    · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.even_add, ih]
      have : Even (f a) := Nat.not_odd_iff_even.1 ha
      tauto

/-- **The handshake lemma** for list multigraphs: among the vertices of a duplicate-free list
containing every endpoint, an even number have odd degree. -/
theorem even_length_filter_odd_degree {H : List (α × α)} {V : List α} (hV : V.Nodup)
    (hH : ∀ e ∈ H, e.1 ∈ V ∧ e.2 ∈ V) :
    Even (V.filter fun x => Odd (degree H x)).length := by
  rw [← even_sum_iff_even_length_filter_odd, sum_map_degree hV hH]
  exact even_two_mul _

end Cslib.Algorithms.Lean.Euler
