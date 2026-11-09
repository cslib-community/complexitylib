/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Shearer

/-!
# The discrete Loomis–Whitney inequality

A finite set `A` of points in a product of `n ≥ 2` finite sets has
`|A| ^ (n - 1) ≤ ∏ i, |π_i(A)|`, where `π_i` forgets the `i`-th coordinate
[Loomis and Whitney][LoomisWhitney1949]. In three dimensions: a finite set of unit cubes has
volume at most the square root of the product of the areas of its three projections onto the
coordinate planes. Every coordinate lies in exactly `n - 1` of the sets `univ.erase i`, so this is
Shearer's lemma for counting (`card_pow_le_prod_card_image_restrict`) for that family, just as
Han's inequality is Shearer's lemma for entropy for it.

## Main results

* `Cslib.Finset.card_pow_le_prod_card_image_restrict_erase`: the discrete Loomis–Whitney
  inequality.

## References

* [L. H. Loomis, H. Whitney, *An inequality related to the isoperimetric
  inequality*][LoomisWhitney1949]
* [F. R. K. Chung, R. L. Graham, P. Frankl, J. B. Shearer, *Some intersection theorems for
  ordered sets and graphs*][ChungGrahamFranklShearer1986]
-/

@[expose] public section

open Finset

namespace Cslib.Finset

variable {ι : Type*} {α : ι → Type*} [∀ i, Finite (α i)]

/-- **Discrete Loomis–Whitney inequality**: a finite set of tuples with `n ≥ 2` coordinates has
`|A| ^ (n - 1) ≤ ∏ i, |π_i(A)|`, where `π_i` deletes the `i`-th coordinate. -/
theorem card_pow_le_prod_card_image_restrict_erase [Fintype ι] [DecidableEq ι]
    [∀ i, DecidableEq (α i)] (hι : 2 ≤ Fintype.card ι) (A : Finset (∀ i, α i)) :
    #A ^ (Fintype.card ι - 1) ≤ ∏ i, #(A.image (univ.erase i).restrict) := by
  refine card_pow_le_prod_card_image_restrict A (fun i => univ.erase i) (by omega) fun j => ?_
  rw [show (univ.filter fun i => j ∈ univ.erase i) = univ.erase j by ext; simp [eq_comm],
    card_erase_of_mem (mem_univ _), card_univ]

end Cslib.Finset
