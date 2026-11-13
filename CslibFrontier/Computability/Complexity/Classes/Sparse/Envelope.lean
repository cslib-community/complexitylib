/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Sparse.Fortune

/-!
# SAT reductions inside a polynomial-time envelope

If SAT reduces to a set `S` inside a polynomial-time decidable set `G`, and `G \ S` is sparse,
then SAT is in P. This is the stronger endpoint of Exercise 3.12 in Goldreich's January 2007
draft (`r2.pdf`, PDF pp. 19–20/printed pp. 135–136) of *Computational Complexity: A Conceptual
Perspective* [Goldreich2007DraftR2].

The proof uses Fortune's existing theorem. If `G \ S` is nonempty, send a formula's reduction
image to itself when it lies in `G`, and otherwise to a fixed element of `G \ S`. This reduces
UNSAT to `G \ S`. If the difference is empty, `S = G` is already in P. No decidability of `S`
is assumed. The source's search-tree proof is not reimplemented.

The target may have any explicit bit encoding. `SPARSE` bounds all target encodings of length
at most `n`; the draft bounds words of each exact length. These are the same polynomial
sparseness convention after summing over lengths, but no coefficient-one census bound is claimed.

## Main results

* `Cslib.Complexity.SAT_mem_P_of_sparse_diff`: the decidable-envelope sparse-complement endpoint.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- If SAT reduces to `S ⊆ G`, where `G` is in P and `G \ S` is sparse, then SAT is in P.
The envelope need not itself be sparse; only its difference from the target is bounded. -/
theorem SAT_mem_P_of_sparse_diff {β : Type} {encB : β ↪ List Bool} {S G : Set β}
    (hSG : S ⊆ G) (hG : G ∈ P encB) (hSparse : G \ S ∈ SPARSE encB)
    (hred : PolyTimeReducible encCNF encB SAT S) : SAT ∈ P encCNF := by
  classical
  by_cases hnonempty : (G \ S).Nonempty
  · obtain ⟨z, hzG, hzS⟩ := hnonempty
    obtain ⟨v, hv, hvG⟩ := hG
    obtain ⟨f, hf, hfS⟩ := hred
    let g := fun φ => if v (f φ) then f φ else z
    have hg : ComputableInPolyTime g encCNF encB := by
      dsimp only [g]
      fun_prop
    apply Fortune.SAT_mem_P hSparse
    refine ⟨g, hg, ?_⟩
    intro φ
    change φ ∉ SAT ↔ g φ ∈ G \ S
    by_cases h : v (f φ) = true
    · have hGf : f φ ∈ G := (hvG _).mpr h
      simp only [g, h, ↓reduceIte, Set.mem_sdiff, hGf, true_and, ← hfS]
    · have hnotG : f φ ∉ G := fun hfG => h ((hvG _).mp hfG)
      have hnotS : f φ ∉ S := fun hfS => hnotG (hSG hfS)
      simp [g, h, hzG, hzS, (hfS _).not.mpr hnotS]
  · have heq : S = G := Set.Subset.antisymm hSG fun x hx => by
      by_contra hnotS
      exact hnonempty ⟨x, hx, hnotS⟩
    exact hred.mem_P (heq.symm ▸ hG)

end Cslib.Complexity
