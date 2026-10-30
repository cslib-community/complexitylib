/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Basic

/-!
# Reindexing the vertices of a rotation map

An explicit equivalence transports a graph to a new vertex representation, preserving its edge
labels and spectral expansion. In particular, a computable numbering turns a graph on structured
vertices into an indexed graph without choosing an enumeration.

## Main definitions

* `Cslib.RotationMap.reindex`: transport the vertex representation along an equivalence.
* `Cslib.RotationMap.reindexRot`: the functional transport program.

## Main results

* `Cslib.RotationMap.rot_reindex`: the rotation map of a reindexed graph.
* `Cslib.RotationMap.walk_reindex`: the walk operator transforms by composition.
* `Cslib.RotationMap.spectralExpansion_reindex`: spectral expansion is unchanged.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 21][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V W D : Type*}

/-- Decode a renamed vertex, rotate, and encode the resulting vertex, retaining the edge label. -/
def reindexRot (forward : V → W) (backward : W → V) (rotate : V × D → V × D)
    (p : W × D) : W × D :=
  let next := rotate (backward p.1, p.2)
  (forward next.1, next.2)

/-- Rename the vertices of a graph, retaining every outgoing and return edge label. -/
@[reducible]
def reindex (G : RotationMap V D) (e : V ≃ W) : RotationMap W D where
  rot := reindexRot e e.symm G.rot
  rot_involutive p := by simp [reindexRot]

/-- The rotation map of a reindexed graph decodes the vertex, rotates in `G`, and re-encodes the
resulting vertex. -/
@[simp]
theorem rot_reindex (G : RotationMap V D) (e : V ≃ W) (p : W × D) :
    (G.reindex e).rot p = (e (G.rot (e.symm p.1, p.2)).1, (G.rot (e.symm p.1, p.2)).2) :=
  rfl

/-- The neighbor after renaming vertices is the renamed original neighbor. -/
@[simp]
theorem neighbor_reindex (G : RotationMap V D) (e : V ≃ W) (w : W) (d : D) :
    (G.reindex e).neighbor w d = e (G.neighbor (e.symm w) d) :=
  rfl

/-- The walk on renamed vertices composes with the equivalence and its inverse. -/
theorem walk_reindex [Fintype D] (G : RotationMap V D) (e : V ≃ W) (f : W → ℝ) (w : W) :
    (G.reindex e).walk f w = G.walk (f ∘ e) (e.symm w) :=
  rfl

/-- Explicit vertex renaming preserves spectral expansion, including empty vertex types. -/
@[simp]
theorem spectralExpansion_reindex [Fintype V] [Fintype W] [Fintype D]
    (G : RotationMap V D) (e : V ≃ W) : (G.reindex e).spectralExpansion = G.spectralExpansion := by
  have he (f : W → ℝ) : (𝔼 v, f (e v)) = 𝔼 w, f w :=
    Fintype.expect_equiv e _ _ fun _ => rfl
  have hs (f : V → ℝ) : (𝔼 w, f (e.symm w)) = 𝔼 v, f v :=
    Fintype.expect_equiv e.symm _ _ fun _ => rfl
  apply le_antisymm
  · apply spectralExpansion_le G.spectralExpansion_nonneg
    intro f hf
    have h := G.expect_walk_sq_le_spectralExpansion_sq_mul
      (f := f ∘ e) (by simpa only [Function.comp_def, he] using hf)
    dsimp only [Function.comp_def] at h
    rw [he (fun w => f w ^ 2)] at h
    simp only [walk_reindex, Function.comp_def]
    rw [hs (fun v => G.walk (fun x => f (e x)) v ^ 2)]
    exact h
  · apply spectralExpansion_le (G.reindex e).spectralExpansion_nonneg
    intro f hf
    have h := (G.reindex e).expect_walk_sq_le_spectralExpansion_sq_mul
      (f := f ∘ e.symm) (by simpa only [Function.comp_def, hs] using hf)
    simp only [walk_reindex, Function.comp_def, Equiv.symm_apply_apply] at h
    rwa [hs (fun v => G.walk f v ^ 2), hs (fun v => f v ^ 2)] at h

end Cslib.RotationMap
