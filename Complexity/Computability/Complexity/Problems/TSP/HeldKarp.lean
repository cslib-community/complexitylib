/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.TSP.HeldKarp
public import Complexity.Computability.Complexity.Problems.TSP
import Mathlib.Data.List.Rotate

/-!
# Deciding `TSP` by the Bellman–Held–Karp algorithm

This file connects the Bellman–Held–Karp dynamic program
`Cslib.Algorithms.Lean.TSP.heldKarp` [Bellman1962] [HeldKarp1962] to the decision problem
`Cslib.Complexity.TSP` on distance matrices `D : List (List ℕ)` with budgets `b : ℕ`.

An instance `(D, b)` with `D.length = n + 1` has the cities `0, …, n` at distances
`TSP.dist D i j`, and it belongs to `TSP` when some ordering of all cities has closed tour length
at most `b`. The tour length is the closed-walk cost `cycleCost (dist D)`
(`TSP.tourLength_eq_cycleCost`), which is invariant under rotation (`cycleCost_rotate`), so such a
tour can be taken to start at city `0`, which is the normal form `heldKarp` optimizes over.
`TSP.heldKarpDecide` therefore decides `TSP` in at most `(n - 1)² · 2ⁿ⁻¹` ticks on `n` cities,
in the unit-cost model of `heldKarp`: one tick per addition-and-comparison of natural numbers,
whatever their bit length. Composing with the reduction `HamCycle.toTSP` decides Hamiltonian
cycles within the same bound in the number of distinct vertices, against the `(n - 1)!` orderings
examined by brute force.

## Main definitions

* `Cslib.Complexity.TSP.heldKarpDecide`: run `heldKarp` on the distance matrix and compare the
  optimal tour length with the budget.

## Main results

* `Cslib.Complexity.TSP.tourLength_eq_cycleCost`: tour length is the cost of the closed walk.
* `Cslib.Complexity.TSP.mem_TSP_iff_heldKarp_le`: `(D, b) ∈ TSP` exactly when the
  Bellman–Held–Karp optimum is at most `b`.
* `Cslib.Complexity.TSP.heldKarpDecide_eq_true_iff`, `Cslib.Complexity.TSP.time_heldKarpDecide_le`:
  `heldKarpDecide` decides `TSP` in at most `(n - 1)² · 2ⁿ⁻¹` ticks on `n` cities.
* `Cslib.Complexity.HamCycle.heldKarpDecide_toTSP_eq_true_iff`,
  `Cslib.Complexity.HamCycle.time_heldKarpDecide_toTSP_le`: the same for `HamCycle` through
  `HamCycle.toTSP`.

## References

* [R. Bellman, *Dynamic programming treatment of the travelling salesman problem*][Bellman1962]
* [M. Held and R. M. Karp, *A dynamic programming approach to sequencing
  problems*][HeldKarp1962]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 1.2
-/

public section

namespace Cslib.Complexity.TSP

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TSP

/-- The length of a tour is the cost of the closed walk through its cities under `dist D`. -/
theorem tourLength_eq_cycleCost (D : List (List ℕ)) (p : List ℕ) :
    tourLength D p = cycleCost (dist D) p :=
  rfl

private theorem walkCost_succ_eq_tourLength (D : List (List ℕ)) {n : ℕ} (L : List (Fin n)) :
    walkCost (fun i j : Fin (n + 1) => dist D i j) 0 (L.map Fin.succ) 0 =
      tourLength D (0 :: L.map fun i : Fin n => (i : ℕ) + 1) := by
  rw [tourLength_eq_cycleCost, cycleCost_cons,
    ← walkCost_map Fin.val (dist D) (0 : Fin (n + 1)) (L.map Fin.succ) 0]
  simp only [List.map_map, Function.comp_def, Fin.val_succ, Fin.val_zero]

/-- **`TSP` by the Bellman–Held–Karp algorithm.** An instance with `n + 1` cities belongs to
`TSP` exactly when the optimal tour computed by `heldKarp` has length at most the budget. -/
theorem mem_TSP_iff_heldKarp_le {D : List (List ℕ)} {b n : ℕ} (hn : D.length = n + 1) :
    (D, b) ∈ TSP ↔ (heldKarp fun i j : Fin (n + 1) => dist D i j).ret ≤ b := by
  set d : Fin (n + 1) → Fin (n + 1) → ℕ := fun i j => dist D i j
  constructor
  · rintro ⟨p, hp, hb⟩
    rw [hn] at hp
    obtain ⟨A, B, rfl⟩ := List.append_of_mem (hp.symm.subset (List.mem_range.2 (Nat.succ_pos n)))
    have hp' : (0 :: (B ++ A)).Perm (List.range (n + 1)) := List.perm_append_comm.symm.trans hp
    have hrot : tourLength D (A ++ 0 :: B) = tourLength D (0 :: (B ++ A)) := by
      rw [tourLength_eq_cycleCost, tourLength_eq_cycleCost,
        ← cycleCost_rotate (dist D) (A ++ 0 :: B) A.length, List.rotate_append_length_eq]
      rfl
    have hnd := hp'.nodup_iff.2 List.nodup_range
    have hpos : ∀ x ∈ B ++ A, x ≠ 0 := fun x hx h => (List.nodup_cons.1 hnd).1 (h ▸ hx)
    have hR : ∀ x ∈ B ++ A, x - 1 < n := fun x hx => by
      have h1 := List.mem_range.1 (hp'.subset (List.mem_cons_of_mem _ hx))
      have h2 := hpos x hx
      omega
    set L : List (Fin n) := (B ++ A).pmap (fun x hx => ⟨x - 1, hx⟩) hR
    have hLmap : L.map (fun i : Fin n => (i : ℕ) + 1) = B ++ A := by
      rw [List.map_pmap]
      refine List.pmap_eq_self.2 fun x hx => ?_
      have := hpos x hx
      simp only
      omega
    have hLnd : L.Nodup := by
      have h : (L.map fun i : Fin n => (i : ℕ) + 1).Nodup := hLmap ▸ (List.nodup_cons.1 hnd).2
      exact h.of_map _
    have hLuniv : L.toFinset = Finset.univ := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      have hi : (i : ℕ) + 1 ∈ B ++ A := by
        have := hp'.symm.subset (List.mem_range.2 (by omega : (i : ℕ) + 1 < n + 1))
        exact (List.mem_cons.1 this).resolve_left (by omega)
      rw [← hLmap, List.mem_map] at hi
      obtain ⟨j, hj, hji⟩ := hi
      have hij : j = i := Fin.ext (by omega)
      exact hij ▸ hj
    calc (heldKarp d).ret ≤ walkCost d 0 (L.map Fin.succ) 0 :=
          (isLeast_heldKarp d).2 ⟨L, hLnd, hLuniv, rfl⟩
      _ = tourLength D (A ++ 0 :: B) := by rw [walkCost_succ_eq_tourLength, hLmap, hrot]
      _ ≤ b := hb
  · intro h
    obtain ⟨⟨L, hnd, hL, hc⟩, -⟩ := isLeast_heldKarp d
    refine ⟨0 :: L.map fun i : Fin n => (i : ℕ) + 1, ?_, ?_⟩
    · rw [hn]
      refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun v => ?_
      · refine List.nodup_cons.2 ⟨by simp, hnd.map fun i j h => Fin.ext (by simpa using h)⟩
      · simp only [List.mem_cons, List.mem_map, List.mem_range]
        constructor
        · rintro (rfl | ⟨i, -, rfl⟩)
          · omega
          · have := i.isLt
            omega
        · intro hv
          rcases v with _ | v
          · exact Or.inl rfl
          · refine Or.inr ⟨⟨v, by omega⟩, ?_, rfl⟩
            rw [← List.mem_toFinset, hL]
            exact Finset.mem_univ _
    · change tourLength D _ ≤ b
      rw [← walkCost_succ_eq_tourLength, hc]
      exact h

/-- Decide `TSP` by the Bellman–Held–Karp algorithm [HeldKarp1962]: run `heldKarp` on the
distance matrix and compare the optimal tour length with the budget. The empty matrix is a
yes-instance, witnessed by the empty tour. -/
@[expose] def heldKarpDecide (x : List (List ℕ) × ℕ) : TimeM ℕ Bool :=
  match x.1.length with
  | 0 => pure true
  | n + 1 => do
      let c ← heldKarp fun i j : Fin (n + 1) => dist x.1 i j
      pure (decide (c ≤ x.2))

/-- `heldKarpDecide` decides `TSP`. -/
theorem heldKarpDecide_eq_true_iff (x : List (List ℕ) × ℕ) :
    (heldKarpDecide x).ret = true ↔ x ∈ TSP := by
  obtain ⟨D, b⟩ := x
  unfold heldKarpDecide
  split
  · rename_i h
    simp only [TimeM.ret_pure, true_iff]
    refine ⟨[], ?_, by simp [tourLength]⟩
    rw [h, List.range_zero]
  · rename_i n h
    simp only [TimeM.ret_bind, TimeM.ret_pure, decide_eq_true_eq]
    exact (mem_TSP_iff_heldKarp_le h).symm

/-- **`TSP` in `O(n² · 2ⁿ)` arithmetic operations** [HeldKarp1962]. On `n` cities,
`heldKarpDecide` takes at most `(n - 1)² · 2ⁿ⁻¹` ticks, one per addition-and-comparison. -/
theorem time_heldKarpDecide_le (x : List (List ℕ) × ℕ) :
    (heldKarpDecide x).time ≤ (x.1.length - 1) ^ 2 * 2 ^ (x.1.length - 1) := by
  obtain ⟨D, b⟩ := x
  unfold heldKarpDecide
  split
  · simp
  · rename_i n h
    simp only [TimeM.time_bind, TimeM.time_pure, add_zero, h]
    exact time_heldKarp_le _

end Cslib.Complexity.TSP

namespace Cslib.Complexity.HamCycle

open Cslib.Algorithms.Lean TSP

/-- Composing the reduction `toTSP` with `heldKarpDecide` decides `HamCycle`. -/
theorem heldKarpDecide_toTSP_eq_true_iff (G : Graph) :
    (heldKarpDecide (toTSP G)).ret = true ↔ G ∈ HamCycle :=
  (heldKarpDecide_eq_true_iff _).trans (toTSP_mem_iff G)

/-- **Hamiltonian cycles in `O(n² · 2ⁿ)` arithmetic operations.** On a graph with `n` distinct
declared vertices, `heldKarpDecide (toTSP G)` takes at most `(n - 1)² · 2ⁿ⁻¹` ticks; computing
`toTSP G` itself is polynomial-time (`computableInPolyTime_toTSP`). -/
theorem time_heldKarpDecide_toTSP_le (G : Graph) :
    (heldKarpDecide (toTSP G)).time ≤
      (G.distinctVertices.length - 1) ^ 2 * 2 ^ (G.distinctVertices.length - 1) := by
  refine (time_heldKarpDecide_le _).trans ?_
  unfold toTSP
  split
  · simp
  · simp only [List.length_map, le_refl]

end Cslib.Complexity.HamCycle
