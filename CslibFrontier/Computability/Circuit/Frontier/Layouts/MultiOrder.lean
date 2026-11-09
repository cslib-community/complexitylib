/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Scores
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import Mathlib.Tactic.Linarith

/-!
# Ordering the vertices of a multigraph by scores

Sort the vertices of a multigraph of maximum degree `d` by a real score
(`Cslib.Circuits.Frontier.Layout.exists_threshold`). Fix a grid `a, a + δ, ..., a + M δ`. The
cuts below the grid thresholds and the numbers of vertices scoring in the windows between them
bound every frontier of the layout, parallel edges counted separately
(`Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_le_grid`).

Indeed, let the vertices of `P` score at most `m` and the others at least `m`. If
`a + i δ ≤ m < a + (i + 1) δ`, an edge leaving `P` either leaves the threshold set
`{v | score v < a + i δ}` too, or has its end in `P` scoring in the window
`[a + i δ, a + (i + 1) δ)`; at most `d` edges are at each vertex of the window. If `m` lies
below the grid, every edge leaving `P` is at a vertex scoring below `a`, and if `m` lies above
it, every such edge is at a vertex scoring at least `a + M δ`.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_le_grid`: the cut of a threshold set.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_vertexScore`: the layout by a vertex
  score.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

variable {V E : Type*} (G : Multigraph V E)

/-- An edge leaving `P` has an end `u` in `P` and an end `w` outside `P`. -/
private theorem exists_ends_of_mem_edgeCut {P : Set V} {e : E} (he : e ∈ G.edgeCut P) :
    ∃ u w, (G.src e = u ∧ G.tgt e = w ∨ G.src e = w ∧ G.tgt e = u) ∧ u ∈ P ∧ w ∉ P := by
  rw [mem_edgeCut] at he
  by_cases hs : G.src e ∈ P
  · exact ⟨G.src e, G.tgt e, Or.inl ⟨rfl, rfl⟩, hs, fun ht => he (iff_of_true hs ht)⟩
  · exact ⟨G.tgt e, G.src e, Or.inr ⟨rfl, rfl⟩, by tauto, hs⟩

/-- An edge with an end in `S` touches `S`. -/
private theorem mem_touching_of_ends {S : Set V} {e : E} {u w : V}
    (h : G.src e = u ∧ G.tgt e = w ∨ G.src e = w ∧ G.tgt e = u) (hu : u ∈ S) :
    e ∈ G.touching S := by
  rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩
  exacts [Or.inl hu, Or.inr hu]

/-- An edge with one end in `S` and the other outside leaves `S`. -/
private theorem mem_edgeCut_of_ends {S : Set V} {e : E} {u w : V}
    (h : G.src e = u ∧ G.tgt e = w ∨ G.src e = w ∧ G.tgt e = u) (hu : u ∈ S) (hw : w ∉ S) :
    e ∈ G.edgeCut S := by
  rw [mem_edgeCut]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

/-- **Grid control.** Let the vertices of `P` score at most `m` and the others at least `m`. If
`d` times the number of vertices scoring in each tail, and the cut below each grid threshold
plus `d` times the number of vertices scoring in the following window, are at most `B`, then at
most `B` edges leave `P`. -/
theorem ncard_edgeCut_le_grid [Finite V] [Finite E] {d : ℕ} (hd : G.MaxDegreeLE d)
    (score : V → ℝ) {P : Set V} {m a δ : ℝ} (hP : ∀ v ∈ P, score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ score v) (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * ({v | score v < a}.ncard : ℝ) ≤ B)
    (high : d * ({v | a + M * δ ≤ score v}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ((G.edgeCut {v | score v < a + i * δ}).ncard : ℝ) +
      d * ({v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ((G.edgeCut P).ncard : ℝ) ≤ B := by
  have count (S : Set V) (hsub : G.edgeCut P ⊆ G.touching S) :
      ((G.edgeCut P).ncard : ℝ) ≤ d * S.ncard := by
    exact_mod_cast (ncard_le_ncard hsub).trans (G.ncard_touching_le hd S)
  by_cases hlo : m < a
  · -- Below the grid: the end in `P` scores below `a`.
    refine (count {v | score v < a} fun e he => ?_).trans low
    obtain ⟨u, w, hends, hu, -⟩ := G.exists_ends_of_mem_edgeCut he
    exact G.mem_touching_of_ends hends ((hP u hu).trans_lt hlo)
  by_cases hhi : a + M * δ ≤ m
  · -- Above the grid: the end outside `P` scores at least `a + M δ`.
    refine (count {v | a + M * δ ≤ score v} fun e he => ?_).trans high
    obtain ⟨u, w, hends, -, hw⟩ := G.exists_ends_of_mem_edgeCut he
    exact G.mem_touching_of_ends (u := w) (w := u) (hends.elim Or.inr Or.inl)
      (hhi.trans (hPc w hw))
  -- Inside the grid: `a + i δ ≤ m < a + (i + 1) δ`.
  obtain ⟨i, hi, ht, ht'⟩ := exists_grid_index hδ (M := M) (not_lt.mp hlo) (not_le.mp hhi)
  set W := {v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}
  have hsub : G.edgeCut P ⊆ G.edgeCut {v | score v < a + i * δ} ∪ G.touching W := by
    intro e he
    obtain ⟨u, w, hends, hu, hw⟩ := G.exists_ends_of_mem_edgeCut he
    by_cases hut : score u < a + i * δ
    · exact Or.inl (G.mem_edgeCut_of_ends hends hut (not_lt.mpr (ht.trans (hPc w hw))))
    · exact Or.inr (G.mem_touching_of_ends hends ⟨not_lt.mp hut, (hP u hu).trans_lt ht'⟩)
  have hnat := (ncard_le_ncard hsub).trans ((ncard_union_le _ _).trans
    (Nat.add_le_add_left (G.ncard_touching_le hd W) _))
  have hreal : ((G.edgeCut P).ncard : ℝ) ≤
      (G.edgeCut {v | score v < a + i * δ}).ncard + d * W.ncard := by exact_mod_cast hnat
  exact hreal.trans (mid i hi)

/-- **The layout by a vertex score.** Under the grid hypotheses of `ncard_edgeCut_le_grid`,
listing the vertices by score gives a layout of width at most `B`. -/
theorem exists_width_le_of_vertexScore [Finite V] [Finite E] {d : ℕ} (hd : G.MaxDegreeLE d)
    (score : V → ℝ) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : d * ({v | score v < a}.ncard : ℝ) ≤ B)
    (high : d * ({v | a + M * δ ≤ score v}.ncard : ℝ) ≤ B)
    (mid : ∀ i < M, ((G.edgeCut {v | score v < a + i * δ}).ncard : ℝ) +
      d * ({v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}.ncard : ℝ) ≤ B) :
    ∃ π : Layout V, (G.width π : ℝ) ≤ B := by
  obtain ⟨π, hπ⟩ := Layout.exists_threshold score
  refine ⟨π, G.width_le_of_ncard_frontier_le π (le_trans (by positivity) low) fun t ht => ?_⟩
  obtain ⟨m, hP, hPc⟩ := hπ t ht
  exact G.ncard_edgeCut_le_grid hd score hP hPc hδ M low high mid

end Cslib.Circuits.Frontier.Multigraph
