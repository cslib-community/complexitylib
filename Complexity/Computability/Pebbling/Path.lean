/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Basic

/-!
# The directed path

The directed path `0 → 1 → 2 → ⋯` on `ℕ` is the computation graph of a straight-line computation
that runs for ever: vertex `n + 1` has the single predecessor `n`, and `0` is the only source.
It is the graph of Bennett's reversible simulation of an irreversible computation, where vertex
`n` stands for the checkpoint after `n + 1` segments of the computation. Its black pebbling is
trivial: two pebbles slide along it, so every vertex other than the source has black pebbling
price `2`.

## Main definitions

* `Cslib.Pebbling.pathDigraph`: the directed path on `ℕ`.

## Main results

* `Cslib.Pebbling.BlackPebblable.two_le_of_adj`: a vertex with a predecessor needs two pebbles.
* `Cslib.Pebbling.blackPebblingPrice_pathDigraph_succ`: the black pebbling price of `n + 1` is
  `2`.
-/

public section

namespace Cslib.Pebbling

/-- The directed path `0 → 1 → 2 → ⋯` on `ℕ`. -/
def pathDigraph : Digraph ℕ where
  Adj u v := u + 1 = v

@[simp] theorem pathDigraph_adj {u v : ℕ} : pathDigraph.Adj u v ↔ u + 1 = v := Iff.rfl

theorem pathDigraph_irrefl (v : ℕ) : ¬ pathDigraph.Adj v v := by
  simp

theorem pathDigraph_source {u : ℕ} : ¬ pathDigraph.Adj u 0 := by
  simp

section TwoPebbles

variable {V : Type*} [DecidableEq V] {G : Digraph V}

private theorem two_le_of_mTr {s : ℕ} {u v : V} (huv : G.Adj u v) {C D : Finset V}
    {ms : List (Move V)} (h : (blackPebbleGame G s).MTr C ms D) (hvC : v ∉ C) (hvD : v ∈ D) :
    2 ≤ s := by
  induction h with
  | refl => exact absurd hvD hvC
  | @stepL C₁ m C₂ ms C₃ htr _ ih =>
    by_cases hv₂ : v ∈ C₂
    · obtain ⟨hpred, rfl⟩ := htr.1.eq_insert_of_mem hv₂ hvC
      have huC : u ∈ C₁ := hpred u huv
      have huv' : u ≠ v := fun h => hvC (h ▸ huC)
      have hcard : 2 ≤ (insert v C₁).card := by
        rw [Finset.card_insert_of_notMem hvC]
        exact Nat.succ_le_succ (Finset.card_pos.2 ⟨u, huC⟩)
      exact hcard.trans htr.2
    · exact ih hv₂ hvD

/-- A vertex with a predecessor cannot be black-pebbled with fewer than two pebbles: when its
pebble is placed, the predecessor's pebble is still on the graph. -/
theorem BlackPebblable.two_le_of_adj {s : ℕ} {u v : V} (huv : G.Adj u v)
    (h : BlackPebblable G s v) : 2 ≤ s := by
  obtain ⟨ms, C, hC, hv⟩ := h
  exact two_le_of_mTr huv hC (Finset.notMem_empty v) hv

end TwoPebbles

theorem blackPebblable_pathDigraph (v : ℕ) : BlackPebblable pathDigraph 2 v := by
  cases v with
  | zero => exact (blackPebblable_one_of_source fun _ => pathDigraph_source).mono (by omega)
  | succ v =>
    refine BlackPebblable.of_forall_adj (s := 2) {v} (fun u hu => ?_) (fun u hu => ?_)
      (by simp) (by simp)
    · rw [pathDigraph_adj] at hu
      rw [Finset.mem_singleton]
      omega
    · rw [Finset.mem_singleton] at hu
      exact hu ▸ blackPebblable_pathDigraph v

/-- Every vertex of the directed path other than the source has black pebbling price `2`. -/
theorem blackPebblingPrice_pathDigraph_succ (v : ℕ) : blackPebblingPrice pathDigraph (v + 1) = 2 :=
  blackPebblingPrice_eq (blackPebblable_pathDigraph _) fun _ h =>
    h.two_le_of_adj (u := v) (by simp)

/-- The source of the directed path has black pebbling price `1`. -/
theorem blackPebblingPrice_pathDigraph_zero : blackPebblingPrice pathDigraph 0 = 1 :=
  blackPebblingPrice_eq_one_of_source fun _ => pathDigraph_source

end Cslib.Pebbling
