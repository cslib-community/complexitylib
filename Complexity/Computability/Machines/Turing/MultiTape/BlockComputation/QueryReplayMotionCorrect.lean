/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayMotion
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoadCorrect

/-!
# All-head correctness of native movement verification

The finite displacement check is exactly the native block-index check, including the input
head's negative coordinate at the left blank boundary. Work origins are proof-only translations
of the stored relative positions.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Motion

variable {k : ℕ} {Q : Type} {w : List Bool}

private theorem code_cast (label : SignType) : (code label : ℤ) = (label : ℤ) + 1 := by
  cases label <;> rfl

/-- The native input-direction test checks its signed block coordinate, including position zero. -/
theorem inputMatches_iff (b positive negative position : ℕ) [NeZero b] (label : SignType) :
    inputMatches b positive negative position label = true ↔
      ((position : ℤ) - 1) / b = (positive : ℤ) - negative + (label : ℤ) := by
  have hc := code_cast label
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  by_cases hp : position = 0
  · subst position
    have hd : (-1 : ℤ) / b = -1 := by simp [Int.neg_one_ediv, Int.sign_eq_one_of_pos hb]
    simp only [inputMatches, ↓reduceIte, decide_eq_true_eq, Int.natCast_zero, zero_sub, hd]
    omega
  · have hs : ((position - 1 : ℕ) : ℤ) = (position : ℤ) - 1 := by omega
    simp only [inputMatches, hp, ↓reduceIte, decide_eq_true_eq]
    rw [← hs, ← Int.natCast_ediv]
    omega

/-- A relative work-head position checks the same block as its translated native coordinate. -/
theorem workMatches_iff (b relative : ℕ) [NeZero b] (origin : ℤ) (label : SignType) :
    workMatches b relative label = true ↔
      ((b : ℤ) * (origin - 1) + relative) / b = origin + (label : ℤ) := by
  have hc := code_cast label
  have hb : (b : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne b
  have hd : ((b : ℤ) * (origin - 1) + relative) / b =
      origin - 1 + (relative : ℤ) / b := by
    rw [add_comm, Int.add_mul_ediv_left _ _ hb, add_comm]
  rw [hd, ← Int.natCast_ediv]
  simp only [workMatches, decide_eq_true_eq]
  omega

/-- Native movement verification validates the input head and every work head against the
same expected schedule row as the functional block gate. -/
theorem valid_iff {b : ℕ} [NeZero b] (positive negative : ℕ)
    (expected : Option (Fin k) → SignType) (q : Config k Q) (c : Cfg k Bool Q w)
    (J : Option (Fin k) → ℤ) (hwidth : q.width = b)
    (hinput : J none = (positive : ℤ) - negative)
    (hrep : Represents q c (fun h => b * (J (some h) - 1))) :
    valid (positive, negative, expected, q) = true ↔
      ∀ head, c.blockIndex b head = J head + (expected head : ℤ) := by
  have hb : 0 < b := Nat.pos_of_neZero b
  simp only [valid, hwidth, hb, decide_true, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hw⟩ head
    cases head with
    | none =>
      have h := (inputMatches_iff b positive negative q.inputPos (expected none)).mp hi
      simpa only [Cfg.blockIndex, Cfg.headPos_none, hrep.inputPos, hinput] using h
    | some head =>
      have h := (workMatches_iff b (q.heads head) (J (some head))
        (expected (some head))).mp (hw head)
      simpa only [Cfg.blockIndex, Cfg.headPos_some, hrep.heads head] using h
  · intro h
    constructor
    · apply (inputMatches_iff b positive negative q.inputPos (expected none)).mpr
      simpa only [Cfg.blockIndex, Cfg.headPos_none, hrep.inputPos, hinput] using h none
    · intro head
      apply (workMatches_iff b (q.heads head) (J (some head)) (expected (some head))).mpr
      simpa only [Cfg.blockIndex, Cfg.headPos_some, hrep.heads head] using h (some head)

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Motion
