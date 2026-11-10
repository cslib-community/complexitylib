/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.WeightedCut.Contraction

/-!
# Blocks of a contraction

A contraction keeps, for each supervertex `a`, the block `s(a)` of original vertices merged into
it [Karger and Stein, Section 2][KargerStein1996]. When a contraction step merges `v` into `u`
and moves the last supervertex into slot `v` (`Cslib.WeightedCut.contractMatrix`), the block of
`u` absorbs the block of `v` and every other supervertex keeps its block
(`Cslib.WeightedCut.contractBlocks`). For blocks given as the fibres of a supervertex map `part`,
this is the same as taking the fibres of the contracted map `Cslib.WeightedCut.contractPart`
(`Cslib.WeightedCut.contractBlocks_pullbackCut`), so a contraction that tracks blocks carries
exactly the information of a supervertex map.

## Main definitions

* `Cslib.WeightedCut.contractBlocks`: the blocks after one contraction step.

## Main results

* `Cslib.WeightedCut.contractBlocks_pullbackCut`: contracting the fibres of `part` gives the
  fibres of `contractPart part u v huv`.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

public section

namespace Cslib.WeightedCut

/-- The blocks after merging supervertex `v` into `u` and moving the last supervertex into slot
`v` (`contractMatrix`): the block of `u` absorbs the block of `v`, and the others keep theirs. -/
def contractBlocks {α : Type*} [DecidableEq α] {m : ℕ} (blocks : Fin (m + 1) → Finset α)
    (u v : Fin (m + 1)) (i : Fin m) : Finset α :=
  if embedCompact v i = u then blocks u ∪ blocks v else blocks (embedCompact v i)

/-- Contracting the fibres of a supervertex map gives the fibres of the contracted map. -/
theorem contractBlocks_pullbackCut {n m : ℕ} (part : Fin n → Fin (m + 1)) {u v : Fin (m + 1)}
    (huv : u ≠ v) :
    contractBlocks (fun i => pullbackCut part {i}) u v =
      fun i => pullbackCut (contractPart part u v huv) {i} := by
  funext i
  ext x
  have hiv : embedCompact v i ≠ v := embedCompact_ne v i
  have key : contractPart part u v huv x = i ↔
      (if part x = v then u else part x) = embedCompact v i := by
    constructor
    · rintro rfl
      exact (embedCompact_contractPart part u v huv x).symm
    · intro h
      exact embedCompact_injective v ((embedCompact_contractPart part u v huv x).trans h)
  rw [mem_pullbackCut, Finset.mem_singleton, key]
  by_cases hiu : embedCompact v i = u
  · by_cases hxv : part x = v
    · simp [contractBlocks, mem_pullbackCut, hiu, hxv]
    · simp [contractBlocks, mem_pullbackCut, hiu, hxv]
  · by_cases hxv : part x = v
    · simp [contractBlocks, mem_pullbackCut, hiu, hxv, Ne.symm hiu, Ne.symm hiv]
    · simp [contractBlocks, mem_pullbackCut, hiu, hxv]

end Cslib.WeightedCut
