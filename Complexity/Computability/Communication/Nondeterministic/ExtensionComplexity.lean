/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Nondeterministic.CoverNumber
public import Complexity.Foundations.Analysis.Convex.ExtendedFormulation

/-!
# The rectangle covering bound on nonnegative rank and extension complexity

If `M = T * U` is a nonnegative factorization with inner dimension `r`, then the support of `M` is
the union of the `r` rectangles `{i | T i k ≠ 0} × {j | U k j ≠ 0}`
(`Matrix.mul_apply_ne_zero_iff_of_nonneg`). So the Boolean support matrix of `M` has a `1`-cover
by `r` rectangles: its rectangle covering bound is at most the nonnegative rank `rank₊ M`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 4], a result of [Yannakakis1991]
(`Nondeterministic.coverNumberFun_ne_zero_le_nonnegRank`). Equivalently, the nondeterministic
communication complexity `N¹` of the support matrix is at most `⌈log₂ (rank₊ M)⌉`
(`Nondeterministic.ecomplexityFun_ne_zero_le_clog`).

By Yannakakis's factorization theorem (`extensionComplexity_eq_nonnegRank_slackMatrix`), the
extension complexity of a nontrivial polytope bounds the rectangle covering bound and `N¹` of the
support of its slack matrix in the same way
(`Nondeterministic.coverNumberFun_slackMatrix_le_extensionComplexity`,
`Nondeterministic.ecomplexityFun_slackMatrix_le_clog`). This is how lower bounds on
nondeterministic communication complexity give lower bounds on extension complexity
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 1]; for instance, a fooling set of `1`-entries of
the support matrix has at most `rank₊ M` pairs
(`Nondeterministic.card_le_nonnegRank_of_isFoolingSet`), and at most `xc P` pairs for a slack
matrix (`Nondeterministic.card_le_extensionComplexity_of_isFoolingSet`).

## Main results

* `Cslib.Communication.Nondeterministic.coverNumberFun_ne_zero_le_nonnegRank`: the rectangle
  covering bound.
* `Cslib.Communication.Nondeterministic.ecomplexityFun_ne_zero_le_clog`: `N¹` of the support is at
  most `⌈log₂ (rank₊ M)⌉`.
* `Cslib.Communication.Nondeterministic.coverNumberFun_slackMatrix_le_extensionComplexity`,
  `Cslib.Communication.Nondeterministic.ecomplexityFun_slackMatrix_le_clog`: the same for the
  extension complexity of a polytope and its slack matrix.
* `Cslib.Communication.Nondeterministic.card_le_nonnegRank_of_isFoolingSet`,
  `Cslib.Communication.Nondeterministic.card_le_extensionComplexity_of_isFoolingSet`: fooling-set
  lower bounds on nonnegative rank and extension complexity.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Sections 1 and 3.1
* [Yannakakis1991]
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Matrix

section NonnegRank

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R]
  [DecidableEq R] {m n : Type*}

/-- **The rectangle covering bound** [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 4],
[Yannakakis1991]: the least number of rectangles covering the support of `M`, without covering any
zero entry, is at most the nonnegative rank of `M`. -/
theorem coverNumberFun_ne_zero_le_nonnegRank (M : Matrix m n R) :
    coverNumberFun true (fun i j => decide (M i j ≠ 0)) Set.univ Set.univ ≤ M.nonnegRank :=
  le_nonnegRank_iff.2 fun r ⟨T, U, hT, hU, hTU⟩ => by
    subst hTU
    refine (IsCover.coverNumberFun_le (C := fun k : Fin r => ({i | T i k ≠ 0}, {j | U k j ≠ 0}))
      ?_).trans_eq (by rw [Fintype.card_fin])
    rw [isCover_fun_iff]
    refine ⟨fun k i _ hi j _ hj => ?_, fun i _ j _ hij => ?_⟩
    · simpa using (mul_apply_ne_zero_iff_of_nonneg hT hU i j).2 ⟨k, hi, hj⟩
    · exact (mul_apply_ne_zero_iff_of_nonneg hT hU i j).1 (by simpa using hij)

/-- **Yannakakis's communication bound on nonnegative rank**: the nondeterministic communication
complexity `N¹` of the support matrix of `M` is at most `⌈log₂ r⌉` if `rank₊ M ≤ r`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 1]. -/
theorem ecomplexityFun_ne_zero_le_clog {M : Matrix m n R} {r : ℕ} (h : M.nonnegRank ≤ r) :
    ecomplexityFun true (fun i j => decide (M i j ≠ 0)) Set.univ Set.univ ≤ Nat.clog 2 r :=
  ecomplexity_le_clog ((coverNumberFun_ne_zero_le_nonnegRank M).trans h)

/-- **The fooling-set bound on nonnegative rank**: a fooling set of nonzero entries of `M`, no two
of which span a rectangle of nonzero entries, has at most `rank₊ M` entries. -/
theorem card_le_nonnegRank_of_isFoolingSet {M : Matrix m n R} {S : Finset (m × n)}
    (hS : IsFoolingSet (fun i j => decide (M i j ≠ 0)) true S) :
    (S.card : ℕ∞) ≤ M.nonnegRank :=
  (card_le_coverNumberFun_of_isFoolingSet hS fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩).trans
    (coverNumberFun_ne_zero_le_nonnegRank M)

end NonnegRank

section ExtensionComplexity

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {ι μ ν : Type*} [Fintype ι]
  [Finite ν] {P : Set (ι → K)} {A : Matrix μ ι K} {b : μ → K} {V : ν → ι → K}

/-- **The rectangle covering bound on extension complexity**: the support of the slack matrix of a
nontrivial polytope `P = {x | A *ᵥ x ≤ b} = conv (range V)` is covered by `xc P` rectangles
avoiding its zeros. -/
theorem coverNumberFun_slackMatrix_le_extensionComplexity (hA : P = {x | A *ᵥ x ≤ b})
    (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) :
    coverNumberFun true (fun i j => decide (A.slackMatrix b V i j ≠ 0)) Set.univ Set.univ ≤
      extensionComplexity P :=
  (coverNumberFun_ne_zero_le_nonnegRank _).trans
    (nonnegRank_slackMatrix_le_extensionComplexity hA hV hP)

/-- **Yannakakis's communication bound on extension complexity**: if a nontrivial polytope
`P = {x | A *ᵥ x ≤ b} = conv (range V)` has an extended formulation with `r` inequalities, then the
nondeterministic communication complexity `N¹` of the support matrix of its slack matrix is at most
`⌈log₂ r⌉` [FioriniMassarPokuttaTiwaryDeWolf2015, Section 1]. -/
theorem ecomplexityFun_slackMatrix_le_clog (hA : P = {x | A *ᵥ x ≤ b})
    (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) {r : ℕ}
    (h : extensionComplexity P ≤ r) :
    ecomplexityFun true (fun i j => decide (A.slackMatrix b V i j ≠ 0)) Set.univ Set.univ ≤
      Nat.clog 2 r :=
  ecomplexity_le_clog ((coverNumberFun_slackMatrix_le_extensionComplexity hA hV hP).trans h)

/-- **The fooling-set bound on extension complexity**: a fooling set of nonzero entries of the
slack matrix of a nontrivial polytope `P = {x | A *ᵥ x ≤ b} = conv (range V)` has at most `xc P`
entries. -/
theorem card_le_extensionComplexity_of_isFoolingSet (hA : P = {x | A *ᵥ x ≤ b})
    (hV : P = convexHull K (Set.range V)) (hP : P.Nontrivial) {S : Finset (μ × ν)}
    (hS : IsFoolingSet (fun i j => decide (A.slackMatrix b V i j ≠ 0)) true S) :
    (S.card : ℕ∞) ≤ extensionComplexity P :=
  (card_le_nonnegRank_of_isFoolingSet hS).trans
    (nonnegRank_slackMatrix_le_extensionComplexity hA hV hP)

end ExtensionComplexity

end Nondeterministic

end Cslib.Communication
