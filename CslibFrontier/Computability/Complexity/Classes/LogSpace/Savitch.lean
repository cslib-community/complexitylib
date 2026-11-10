/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized
public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch

/-!
# Savitch's theorem for logarithmic space: `NL ⊆ DSPACE(log² n)`

A problem in `Cslib.Complexity.NL` is decided by a deterministic machine within space
`O((log₂ n) ^ 2)` [Savitch1970]. This is the case `s = log₂` of Savitch's theorem
`Cslib.Complexity.NSPACE_subset_DSPACE_sq`, through `Cslib.Complexity.NL_eq_NSPACE`; logspace
recognizers, whose branches may run forever, are covered by
`Cslib.Complexity.mem_DSPACE_sq_of_recognizesInSpace`. Since one-sided-error randomized logspace is
within `NL` (`Cslib.Complexity.RL_subset_NL`), the same bound holds for `Cslib.Complexity.RL`
[Hoza, Section 4.3][Hoza2022].

The space classes are `Cslib.Complexity.DSPACE enc fun n => Nat.log2 n ^ 2`, the problems decided
within space `c₁ * (log₂ n) ^ 2 + c₂` on encoded instances of length `n`.

## Main results

* `Cslib.Complexity.NL_subset_DSPACE_log2_sq`: `NL ⊆ DSPACE(log² n)`.
* `Cslib.Complexity.RL_subset_DSPACE_log2_sq`: `RL ⊆ DSPACE(log² n)`.

## References

* [W. J. Savitch, *Relationships between nondeterministic and deterministic tape
  complexities*][Savitch1970]; journal text not inspected (paywalled), so no theorem number or
  page is cited.
* [W. M. Hoza, *Recent Progress on Derandomizing Space-Bounded Computation*, Section 4.3][Hoza2022]
* [M. Sipser, *Introduction to the Theory of Computation*, 3rd edition, Section 8.4, final
  paragraph (p. 351)][Sipser2013]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **Savitch's theorem for logarithmic space**: `NL ⊆ DSPACE(log² n)` [Savitch1970], the case
`s = log₂` of `Cslib.Complexity.NSPACE_subset_DSPACE_sq`. -/
theorem NL_subset_DSPACE_log2_sq : NL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 := by
  rw [NL_eq_NSPACE]
  exact NSPACE_subset_DSPACE_sq fun _ => le_rfl

/-- **`RL ⊆ DSPACE(log² n)`**, through `RL ⊆ NL` [Hoza, Section 4.3][Hoza2022]. -/
theorem RL_subset_DSPACE_log2_sq : RL enc ⊆ DSPACE enc fun n => Nat.log2 n ^ 2 :=
  fun _ h => NL_subset_DSPACE_log2_sq (RL_subset_NL h)

end Cslib.Complexity
