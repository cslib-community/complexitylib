/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Complexity.Classes.Space
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized.Amplification
import Complexity.Computability.Complexity.Classes.Promise.Probabilistic
import Complexity.Computability.Complexity.Classes.IP.PSPACE
import Complexity.Computability.Probabilistic.PPT.Composition

/-!
# Randomized logarithmic space is within randomized polynomial time

A fair-coin machine of `Cslib.Complexity.RL` or `Cslib.Complexity.BPL` halts on every branch, so
it halts within a polynomial clock (`Cslib.Complexity.exists_polyClock_of_mem_BPL`). Run for that
clock and followed by the polynomial-time test of whether its output is `[true]`, it is a
uniform strict probabilistic polynomial-time program
(`Cslib.Probability.IsPPTOn`), accepting with the probability `acceptCoins input t / 2 ^ t`
(`Turing.MultiTapePTM.acceptCoins_eq_mul_eval`). The characterizations of `RP` and `BPP` by such
programs (`Cslib.Complexity.mem_PromiseRP_iff_exists_isPPTOn`,
`Cslib.Complexity.mem_PromiseBPP_iff_exists_isPPTOn`) then give `RL ⊆ RP` and `BPL ⊆ BPP`
[Arora and Barak, Section 7.7][AroraBarak09]. With `BPP ⊆ IP ⊆ PSPACE`
(`Cslib.Complexity.BPP_subset_IP`, `Cslib.Complexity.IP_subset_PSPACE`) this gives
`BPL ⊆ PSPACE`.

The stronger inclusion `BPL ⊆ P`, by exact evaluation of the configuration matrix, is not
proved here.

## Main results

* `Cslib.Complexity.RL_subset_RP`: randomized logspace with one-sided error is within `RP`.
* `Cslib.Complexity.BPL_subset_BPP`: randomized logspace with two-sided error is within `BPP`.
* `Cslib.Complexity.BPL_subset_PSPACE`: and within polynomial space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.7][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Probability

variable {α : Type} {enc : α ↪ List Bool}

/-- The closed run of a fair-coin machine for the clock `2 * (2 * (n + 1)) ^ d`, accepting when its
output is `[true]`, is a uniform strict probabilistic polynomial-time program. -/
private theorem isPPTOn_runClosed_accepts {k : ℕ} {State : Type} [Finite State]
    (M : MultiTapePTM k Bool State) (d : ℕ) :
    IsPPTOn enc encBool fun a => (· == [true]) <$>
      M.runClosed (2 * (2 * ((enc a).length + 1)) ^ d) (enc a) := by
  have hrun : IsPPTOn enc encBits fun a =>
      M.runClosed (2 * (2 * ((enc a).length + 1)) ^ d) (enc a) :=
    ⟨k, State, inferInstance, M, 2 * 2 ^ d, d, fun a => by
      simp only [encBits, Function.Embedding.coe_refl, PMF.map_id]
      rw [mul_pow, ← mul_assoc]⟩
  exact hrun.map (ComputableInPolyTime.beq ComputableInPolyTime.id'
    (ComputableInPolyTime.const [true]))

/-- Once every branch halts within `t` steps, the run for `t` steps outputs `[true]` with
probability `acceptCoins input t / 2 ^ t`. -/
private theorem eval_runClosed_true {k : ℕ} {State : Type} (M : MultiTapePTM k Bool State)
    {input : List Bool} {t : ℕ} (ht : M.toNTM.RunsInTime input t) :
    ProbComp.eval (M.runClosed t input) [true] = (M.acceptCoins input t : ENNReal) / 2 ^ t := by
  rw [M.acceptCoins_eq_mul_eval ht, mul_comm, ENNReal.mul_div_cancel_right (by simp) (by simp)]

/-- The same probability for the test of the output, as a real number. -/
private theorem probability_runClosed_accepts {k : ℕ} {State : Type}
    (M : MultiTapePTM k Bool State) {input : List Bool} {t : ℕ}
    (ht : M.toNTM.RunsInTime input t) :
    Pr[(· == [true]) <$> M.runClosed t input] = (M.acceptCoins input t : ℝ) / 2 ^ t := by
  rw [ProbComp.probability_map_beq, eval_runClosed_true M ht, ENNReal.toReal_div]
  simp

/-- **Randomized logspace with one-sided error is within `RP`**: the polynomial-clock run of an
`RL` machine is a probabilistic polynomial-time program that accepts members with probability at
least `1/2` and never accepts non-members. -/
theorem RL_subset_RP : RL enc ⊆ RP enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, d, hM⟩ := exists_polyClock_of_mem_RL h
  rw [← ofSet_mem_PromiseRP, mem_PromiseRP_iff_exists_isPPTOn]
  refine ⟨_, isPPTOn_runClosed_accepts M d, fun a ha => ?_, fun a ha => ?_⟩
  · have h := Nat.cast_le (α := ℝ).mpr ((hM a).2.2.1 ha)
    push_cast at h
    rw [probability_runClosed_accepts M (hM a).2.1, le_div_iff₀ (by positivity)]
    linarith
  · rw [ProbComp.eval_map, PMF.support_map]
    rintro ⟨w, hw, hwt⟩
    have hw' : w = [true] := by simpa using hwt
    subst hw'
    rw [PMF.mem_support_iff, eval_runClosed_true M (hM a).2.1, (hM a).2.2.2 ha] at hw
    simp at hw

/-- **Randomized logspace with two-sided error is within `BPP`**: the polynomial-clock run of a
`BPL` machine is a probabilistic polynomial-time program with error at most `1/3`. -/
theorem BPL_subset_BPP : BPL enc ⊆ BPP enc := by
  intro A h
  obtain ⟨k, State, hfin, M, c, d, hM⟩ := exists_polyClock_of_mem_BPL h
  rw [← ofSet_mem_PromiseBPP, mem_PromiseBPP_iff_exists_isPPTOn]
  refine ⟨_, isPPTOn_runClosed_accepts M d, fun a ha => ?_, fun a ha => ?_⟩
  · have h := Nat.cast_le (α := ℝ).mpr ((hM a).2.2.1 ha)
    push_cast at h
    rw [probability_runClosed_accepts M (hM a).2.1, le_div_iff₀ (by positivity)]
    linarith
  · have h := Nat.cast_le (α := ℝ).mpr ((hM a).2.2.2 ha)
    push_cast at h
    rw [ProbComp.probability_not, probability_runClosed_accepts M (hM a).2.1]
    have hle : (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) /
        2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

/-- **Randomized logspace with two-sided error is within polynomial space**, through
`BPP ⊆ IP ⊆ PSPACE`. -/
theorem BPL_subset_PSPACE : BPL enc ⊆ PSPACE enc :=
  fun _ h => IP_subset_PSPACE enc (BPP_subset_IP enc (BPL_subset_BPP h))

end Cslib.Complexity
