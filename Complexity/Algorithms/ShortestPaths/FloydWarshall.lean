/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ShortestPaths.Power

/-!
# Correctness of Floyd–Warshall

One round of Floyd–Warshall with pivot `k` replaces `D i j` by `min (D i j) (D i k + D k j)`,
which over `MinTropical R` is `fwStep D k i j = D i j + D i k * D k j`. Starting from
`withOneDiag W` and running a round for every vertex yields the shortest-distance matrix, for any
order of the pivots and whenever `W` has no negative cycles.

The proof keeps the invariant of CLRS Section 25.2: after the pivots in `S` have been processed,
every entry is `0` or the weight of a walk, and lies below every walk without repeated vertices
whose intermediate vertices all lie in `S`.

## Main definitions

* `Cslib.Algorithms.ShortestPaths.fwStep`: one Floyd–Warshall round.

## Main results

* `Cslib.Algorithms.ShortestPaths.isShortestDistances_foldl_fwStep`: correctness of
  Floyd–Warshall for every pivot list containing all vertices.

## References

* [Floyd, *Algorithm 97: Shortest path*][Floyd1962].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 25.2.
-/

public section

open MinTropical

namespace Cslib.Algorithms.ShortestPaths

variable {R : Type*} [LinearOrderedAddCommMonoidWithTop R] {V : Type*}

/-- One round of Floyd–Warshall with pivot `k`: `D' i j = min (D i j) (D i k + D k j)`. -/
@[expose] def fwStep (D : Matrix V V (MinTropical R)) (k : V) : Matrix V V (MinTropical R) :=
  fun i j => D i j + D i k * D k j

/-- The Floyd–Warshall invariant for the set `S` of pivots processed so far. -/
private structure FWInv (W : Matrix V V (MinTropical R)) (S : Set V)
    (D : Matrix V V (MinTropical R)) : Prop where
  sound : ∀ i j, D i j = 0 ∨ ∃ l : List V, l.getLastD i = j ∧ walkWeight W i l = D i j
  complete : ∀ i (l : List V), (i :: l).Nodup → (∀ v ∈ l.dropLast, v ∈ S) →
    D i (l.getLastD i) ≤ walkWeight W i l

variable {W : Matrix V V (MinTropical R)}

private theorem fwInv_withOneDiag [DecidableEq V] : FWInv W ∅ (withOneDiag W) where
  sound i j := by
    right
    by_cases h : i = j
    · subst h
      exact ⟨[], rfl, by simp [withOneDiag]⟩
    · exact ⟨[j], rfl, by simp [withOneDiag, h]⟩
  complete i l hnd hS := by
    match l, hnd, hS with
    | [], _, _ => simp [withOneDiag]
    | [v], hnd, _ =>
      have : i ≠ v := by simpa using hnd
      simp [withOneDiag, this]
    | v :: _ :: _, _, hS => exact absurd (hS v (by simp)) (Set.notMem_empty _)

private theorem FWInv.step {S : Set V} {D : Matrix V V (MinTropical R)} (h : FWInv W S D)
    (k : V) : FWInv W (insert k S) (fwStep D k) where
  sound i j := by
    rcases add_eq_or (D i j) (D i k * D k j) with he | he <;>
      simp only [fwStep, he]
    · exact h.sound i j
    · rcases h.sound i k with h1 | ⟨l₁, hl₁, hw₁⟩
      · left
        rw [h1, zero_mul]
      rcases h.sound k j with h2 | ⟨l₂, hl₂, hw₂⟩
      · left
        rw [h2, mul_zero]
      right
      refine ⟨l₁ ++ l₂, by rw [List.getLastD_append, hl₁, hl₂], ?_⟩
      rw [walkWeight_append, hl₁, hw₁, hw₂]
  complete i l hnd hS := by
    by_cases hk : k ∈ l
    · obtain ⟨s, u, rfl⟩ := List.append_of_mem hk
      have hsplit : s ++ k :: u = (s ++ [k]) ++ u := by simp
      have hlast₁ : (s ++ [k]).getLastD i = k := by
        rw [List.getLastD_append]
        rfl
      have hnd₁ : (i :: (s ++ [k])).Nodup := hnd.sublist (by simp)
      have hnd₂ : (k :: u).Nodup := hnd.sublist (by simp)
      have hS₁ : ∀ v ∈ (s ++ [k]).dropLast, v ∈ S := by
        intro v hv
        rw [List.dropLast_concat] at hv
        have hvk : v ≠ k := by
          intro he
          rw [he] at hv
          have : (s ++ k :: u).Nodup := (List.nodup_cons.1 hnd).2
          exact (List.nodup_append.1 this).2.2 k hv k (by simp) rfl
        have := hS v (by
          rw [List.dropLast_append_of_ne_nil (by simp)]
          exact List.mem_append_left _ hv)
        simpa [hvk] using this
      have hS₂ : ∀ v ∈ u.dropLast, v ∈ S := by
        intro v hv
        have hvk : v ≠ k := by
          intro he
          rw [he] at hv
          exact (List.nodup_cons.1 hnd₂).1 (List.dropLast_subset _ hv)
        have hmem : v ∈ (s ++ k :: u).dropLast := by
          rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
          apply List.mem_append_right
          cases u with
          | nil => simp at hv
          | cons a u' =>
            rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
            exact List.mem_cons_of_mem _ hv
        simpa [hvk] using hS v hmem
      have h1 := h.complete i (s ++ [k]) hnd₁ hS₁
      have h2 := h.complete k u hnd₂ hS₂
      rw [hlast₁] at h1
      rw [hsplit, List.getLastD_append, hlast₁, walkWeight_append, hlast₁]
      exact (add_le_right _ _).trans (mul_le_mul' h1 h2)
    · have hS' : ∀ v ∈ l.dropLast, v ∈ S := by
        intro v hv
        have hvk : v ≠ k := fun h' => hk (h' ▸ List.dropLast_subset _ hv)
        simpa [hvk] using hS v hv
      exact (add_le_left _ _).trans (h.complete i l hnd hS')

private theorem FWInv.foldl {S : Set V} {D : Matrix V V (MinTropical R)} (h : FWInv W S D)
    (ks : List V) : FWInv W (S ∪ {v | v ∈ ks}) (ks.foldl fwStep D) := by
  induction ks generalizing S D with
  | nil => simpa using h
  | cons k ks ih =>
    have e : S ∪ {v | v ∈ k :: ks} = insert k S ∪ {v | v ∈ ks} := by
      ext v
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_cons]
      tauto
    rw [List.foldl_cons, e]
    exact ih (h.step k)

/-- **Correctness of Floyd–Warshall.** If `W` has no negative cycles and the pivot list `ks`
contains every vertex, then running Floyd–Warshall from `withOneDiag W` with the pivots `ks`
yields the shortest-distance matrix. -/
theorem isShortestDistances_foldl_fwStep [DecidableEq V] (hW : NoNegCycle W) {ks : List V}
    (hks : ∀ v, v ∈ ks) :
    IsShortestDistances W (ks.foldl fwStep (withOneDiag W)) := by
  have h := fwInv_withOneDiag.foldl (W := W) ks
  exact isShortestDistances_of_sound_complete hW h.sound
    (fun i l hnd => h.complete i l hnd (fun v _ => by simp [hks v]))

end Cslib.Algorithms.ShortestPaths
