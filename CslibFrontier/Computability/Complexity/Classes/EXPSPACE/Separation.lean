/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXPSPACE
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Polynomial space is strictly within exponential space

For problems on bit words, `PSPACE ⊊ EXPSPACE` (`Cslib.Complexity.PSPACE_ssubset_EXPSPACE`), by
the space hierarchy theorem [Stearns, Hartmanis and Lewis][StearnsHartmanisLewis1965],
[Sipser, Corollary 9.7][Sipser2013]. The diagonal within the space-constructible budget
`4 * 2 ^ n` (`Cslib.Complexity.spaceDiagonal`) is decided within space `O(2 ^ n)`, so it is in
`EXPSPACE`. The budget eventually exceeds every `c * n ^ k + c`, so the diagonal is in no class
`DSPACE (n ^ k)`, and hence not in `PSPACE`, the union of these classes.

## Main results

* `Cslib.Complexity.PSPACE_ssubset_EXPSPACE`: `PSPACE ⊊ EXPSPACE` for problems on bit words.

## References

* [R. E. Stearns, J. Hartmanis, P. M. Lewis II, *Hierarchies of memory limited
  computations*][StearnsHartmanisLewis1965]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

/-- **Polynomial space is strictly within exponential space**, for problems on bit words, by the
space hierarchy theorem [Sipser, Corollary 9.7][Sipser2013]. -/
theorem PSPACE_ssubset_EXPSPACE : PSPACE encBits ⊂ EXPSPACE encBits := by
  set G : ℕ → ℕ := fun n => 4 * 2 ^ n with hG
  have hlog : ∀ n, Nat.log2 n ≤ 2 ^ n := fun n =>
    (Nat.log2_le_self n).trans Nat.lt_two_pow_self.le
  refine (Set.ssubset_iff_of_subset PSPACE_subset_EXPSPACE).mpr
    ⟨{x | spaceDiagonal G x = true}, ?_, fun h => ?_⟩
  · refine mem_EXPSPACE_iff.mpr ⟨1, ?_⟩
    refine DSPACE_mono_of_le_mul_add (s₁ := G) (C := 4) (fun n => by simp [hG]) ?_
    exact setOf_spaceDiagonal_mem_DSPACE (spaceConstructible_two_pow.const_mul 4)
      fun n => (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  · obtain ⟨k, hk⟩ := mem_PSPACE_iff_exists_mem_DSPACE.mp h
    refine setOf_spaceDiagonal_notMem_DSPACE (f := (· ^ k))
      (fun n => Nat.mul_le_mul_left 4 (hlog n)) (fun c => ?_) hk
    filter_upwards [PolynomiallyBounded.eventually_lt_two_pow
      (f := fun n => c * n ^ k + c) (by fun_prop)] with n hn
    exact hn.le.trans (Nat.le_mul_of_pos_left _ (by norm_num))

end Cslib.Complexity
