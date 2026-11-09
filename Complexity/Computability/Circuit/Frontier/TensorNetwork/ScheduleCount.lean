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
(`ContractionSchedule.recursionBound_le_two_pow_div_sqrt_log_two`, with the constant
`245760 C + 37`): the count of Appendix D.4.7 (p. 64), in the
natural-number scale of the contraction interface. It bounds the nodes of the depth-first
evaluation (`Nat.recursionBound`), hence the fuel of
`Cslib.GenericRAM.StackRecursion.Scheme.certificate`.

## Main results

* `Cslib.Circuits.Frontier.ContractionSchedule.recursionBound_le_two_pow_div_sqrt_log_two`: the
  call count.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.ContractionSchedule

/-- **The recursion has `2 ^ O(s / √⌊log₂ s⌋)` calls**, with the constant `245760 C + 37`. From
`s = 2` on, a recursion of depth at most `D ≤ ⌊log₂ s⌋` whose calls at depth `d` have at most
`2 ^ (2 ⌊log₂ s⌋ + branchExponent C s d)` children has at most
`2 ^ ((245760 C + 37) s / √⌊log₂ s⌋)` nodes below its root. The constant is linear in `C`, so one
clock serves every admissibility constant at once, as a machine that does not know `C` needs. -/
theorem recursionBound_le_two_pow_div_sqrt_log_two (C : ℕ) {s D : ℕ} (hs : 2 ≤ s)
    (hD : D ≤ Nat.log 2 s) :
    Nat.recursionBound (fun d => 2 ^ (2 * Nat.log 2 s + branchExponent C s d)) D 0 ≤
      2 ^ ((245760 * C + 37) * s / Nat.sqrt (Nat.log 2 s)) := by
  have h := Nat.mul_prod_le_two_pow_div_sqrt_log_two 2 (245760 * C + 4) hs hD
    (b := fun d => 2 ^ (2 * Nat.log 2 s + branchExponent C s d)) (e := branchExponent C s)
    (fun _ _ => le_rfl) (sum_branchExponent_le C hs hD)
  rw [show 1 + 16 * 2 + (245760 * C + 4) = 245760 * C + 37 by ring] at h
  refine (Nat.recursionBound_le _ D 0).trans ?_
  simpa only [Nat.zero_add] using h

end Cslib.Circuits.Frontier.ContractionSchedule
