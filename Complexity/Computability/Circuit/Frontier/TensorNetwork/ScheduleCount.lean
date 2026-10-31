/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Schedule
public import Complexity.Foundations.Data.Nat.RecursionTree

/-!
# The number of calls of the contraction recursion

Under the parameter schedule of `Cslib.Circuits.Frontier.ContractionSchedule`, a call at depth
`d` of the recursion of [OpenAI2026ETH] (Appendix D.4) has at most
`2 ^ (2 ⌊log₂ s⌋ + branchExponent C s d)` children (`ContractionSchedule.exists_activeBounds`,
`ContractionSchedule.ActiveBounds.card_modeBudget_le`), and there are at most
`⌊log₂ s⌋` levels. The excess exponents sum to `O(s / √⌊log₂ s⌋)`
(`ContractionSchedule.sum_branchExponent_le`), so the recursion has `2 ^ O(s / √⌊log₂ s⌋)` calls
(`ContractionSchedule.exists_recursionBound_le`): the count of Appendix D.4.7 (p. 64), in the
natural-number scale of the contraction interface. It bounds the nodes of the depth-first
evaluation (`Nat.recursionBound`), hence the fuel of
`Cslib.GenericRAM.StackRecursion.Scheme.certificate`.

## Main results

* `Cslib.Circuits.Frontier.ContractionSchedule.exists_recursionBound_le`: the call count.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.ContractionSchedule

/-- **The recursion has `2 ^ O(s / √⌊log₂ s⌋)` calls.** For every `C` there is `K` such that,
from `s = 2` on, a recursion of depth at most `D ≤ ⌊log₂ s⌋` whose calls at depth `d` have at
most `2 ^ (2 ⌊log₂ s⌋ + branchExponent C s d)` children has at most
`2 ^ (K s / √⌊log₂ s⌋)` nodes below its root. -/
theorem exists_recursionBound_le (C : ℕ) : ∃ K, ∀ s D, 2 ≤ s → D ≤ Nat.log 2 s →
    Nat.recursionBound (fun d => 2 ^ (2 * Nat.log 2 s + branchExponent C s d)) D 0 ≤
      2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨K, hK⟩ := Nat.exists_recursionBound_le_two_pow_div_sqrt_log_two 2 (245760 * C + 4)
  refine ⟨K, fun s D hs hD => (Nat.recursionBound_le _ D 0).trans ?_⟩
  simpa only [Nat.zero_add] using hK s D (fun d => 2 ^ (2 * Nat.log 2 s + branchExponent C s d))
    (branchExponent C s) hs hD (fun _ _ => le_rfl) (sum_branchExponent_le C hs hD)

end Cslib.Circuits.Frontier.ContractionSchedule
