/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Reachability.InductiveCounting.Semantics

/-!
# Progress of well-formed inductive-counting instructions

The controller checks a decreasing progress measure. This file proves that the check succeeds
in the intended loop ranges. The check is not an additional graph or reachability oracle.

## Main results

* `Cslib.InductiveCounting.rank_instruction_lt`: legitimate instructions decrease the measure.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Cslib.InductiveCounting

variable {N width source : ℕ} {edge : ℕ → ℕ → Bool} {bad : ℕ → Bool} {s : State}

private theorem sub_mul_step {u N : ℕ} (hu : u < N) (c : ℕ) :
    (N - u) * c = (N - u - 1) * c + c := by
  have he : N - u = (N - u - 1) + 1 := by omega
  calc
    _ = ((N - u - 1) + 1) * c := congrArg (· * c) he
    _ = _ := by rw [Nat.add_mul, Nat.one_mul]

private theorem sub_add_one (N u : ℕ) : N - (u + 1) = N - u - 1 := by omega

/-- Every unhalted instruction from a state satisfying `Invariant` strictly decreases `rank`. -/
theorem rank_instruction_lt (hi : Invariant N edge bad source s)
    (hh : halted s = false) (choice : Bool) :
    rank N width (instruction N width source s (answer edge bad s) choice) < rank N width s := by
  have hA : 0 < candidateCost N width := by unfold candidateCost; omega
  have hT : N * candidateCost N width + 4 < targetCost N width + 2 := by
    simp only [targetCost, Nat.add_mul, Nat.one_mul]
    omega
  have hR : N * targetCost N width + 2 < roundCost N width + 1 := by
    simp only [roundCost, Nat.add_mul, Nat.one_mul]
    omega
  have hRT : targetCost N width < roundCost N width := by
    have hm := Nat.le_mul_of_pos_left (targetCost N width) (show 0 < N + 1 by omega)
    unfold roundCost
    omega
  have hAT : candidateCost N width < targetCost N width := by
    have hm := Nat.le_mul_of_pos_left (candidateCost N width) (show 0 < N + 1 by omega)
    unfold targetCost
    omega
  cases hp : s.phase with
  | round =>
    simp only [Invariant, hp, RoundCorrect] at hi
    have hk : s.round < N := hi.1
    simp only [instruction, hp]
    split_ifs with hk'
    · simp only [rank, hp, Nat.sub_zero]
      rw [sub_mul_step hk]
      omega
    · have he : N - s.round = 1 := by omega
      simp only [rank, hp, ↓reduceIte, he, Nat.one_mul]
      have hNA : N * candidateCost N width + 4 < roundCost N width + 1 := by omega
      simpa only [Nat.sub_zero, Nat.zero_add] using hNA
  | target =>
    simp only [Invariant, hp] at hi
    obtain ⟨_, hf, hk, hv, _⟩ := hi
    simp only [instruction, hp]
    split_ifs with hv'
    · simp only [rank, hp, hf, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
      rw [sub_mul_step hv']
      omega
    · have hv' : s.target = N := by omega
      simp only [rank, hp, hv', Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      rw [sub_add_one N s.round]
      omega
  | candidate =>
    simp only [Invariant, hp] at hi
    obtain ⟨⟨⟨hk, _⟩, hm⟩, _, hu⟩ := hi
    have hwalk : s.round * (width + 3) + 6 < candidateCost N width + 4 := by
      have hm := Nat.mul_le_mul_right (width + 3) (show s.round + 1 ≤ N by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hm
      unfold candidateCost
      omega
    simp only [instruction, hp]
    split_ifs with hu' hb
    · simp only [rank, hp]
      rw [sub_mul_step hu']
      omega
    · simp only [rank, hp]
      rw [sub_add_one N s.candidate]
      rw [sub_mul_step hu']
      omega
    · have hu' : s.candidate = N := by omega
      simp only [rank, hp, hu', Nat.sub_self, Nat.zero_mul]
      omega
  | walk =>
    simp only [Invariant, hp] at hi
    obtain ⟨_, _, hu, hr, _⟩ := hi
    simp only [instruction, hp]
    split_ifs with hz he
    · simp only [rank, hp, hz, Nat.zero_mul, Nat.add_zero]
      omega
    · simp only [rank, hp, reject]
      omega
    · simp only [rank, hp]
      have hr' : 0 < s.remaining := Nat.pos_of_ne_zero hz
      rw [show s.remaining * (width + 3) =
        (s.remaining - 1) * (width + 3) + (width + 3) from by
          conv_lhs => rw [show s.remaining = (s.remaining - 1) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]]
      omega
  | guess =>
    simp only [instruction, hp]
    split_ifs with hz hv
    · simp only [rank, hp, hz]
      omega
    · simp only [rank, hp, reject]
      omega
    · simp only [rank, hp]
      omega
  | edge =>
    simp only [instruction, hp]
    split_ifs
    · simp only [rank, hp]
      omega
    · simp only [rank, hp, reject]
      omega
  | observe =>
    simp only [instruction, hp, rank]
    rw [sub_add_one N s.candidate]
    omega
  | done =>
    simp only [instruction, hp]
    split_ifs with he hf hh'
    · simp only [rank, hp, reject]
      omega
    · simp only [rank, hp, accept]
      omega
    · simp only [Invariant, hp, ScanContext] at hi
      have hf' : s.finalScan = false := Bool.eq_false_iff.mpr hf
      simp only [hf', Bool.false_eq_true, ↓reduceIte] at hi
      simp only [rank, hp, hf', Bool.false_eq_true, ↓reduceIte]
      rw [sub_add_one N s.target]
      omega
    · simp only [rank, hp, reject]
      omega
  | accept => simp [halted, hp] at hh
  | reject => simp [halted, hp] at hh

end Cslib.InductiveCounting
