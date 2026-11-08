/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.CookLevinBridge
import CslibFrontier.Computability.Complexity.Problems.SubsetSum

/-!
# Bridge for the Subset Sum formal abstract

Connects the sublist-based `SubsetSum` definition and the plain binary encodings of
`SubsetSumAbstract.lean` to `Cslib.Complexity.SubsetSum_npComplete`, reusing the plain `NP` and
reduction notions of `CookLevinBridge`.
-/

namespace CslibFrontierTests.Abstracts.SubsetSumBridge

open Turing.MultiTapeTM Cslib.Complexity

theorem bits_injective : Function.Injective Nat.bits :=
  encNat.injective

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (CookLevinBridge.encodeList enc) :=
  (encList enc).injective

theorem subsetSum_eq :
    {x : List ℕ × ℕ | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2} =
      Cslib.Complexity.SubsetSum := by
  ext x
  exact Cslib.Complexity.mem_SubsetSum_iff_sublist.symm

/-- Transfer of Karp's theorem: Subset Sum is `NP`-complete under plain polynomial-time
reductions, with numbers in binary. -/
theorem subsetSum_npComplete :
    {x : List ℕ × ℕ | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2} ∈
      CookLevinBridge.NP (encPair (encList encNat) encNat) ∧
    ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
      A ∈ CookLevinBridge.NP encA →
        CookLevinBridge.PolyTimeReducible encA (encPair (encList encNat) encNat) A
          {x : List ℕ × ℕ | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2} := by
  rw [subsetSum_eq]
  refine ⟨CookLevinBridge.mem_NP_iff.mpr SubsetSum_npComplete.1, fun α encA A hA => ?_⟩
  exact CookLevinBridge.polyTimeReducible_iff.mpr
    (SubsetSum_npComplete.2 encA A (CookLevinBridge.mem_NP_iff.mp hA))

end CslibFrontierTests.Abstracts.SubsetSumBridge
