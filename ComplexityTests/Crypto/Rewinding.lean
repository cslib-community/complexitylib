/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF
import Complexity.Probability.Rewinding
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.NormNum

/-!
# Biased and state-dependent challenge tests for rewinding

A Boolean challenge with masses `3 / 4` and `1 / 4` checks the maximum-atom loss, including a
case attaining the bound. A challenge determined by the saved state checks that the hypothesis
concerns the conditional challenge law: its marginal can be uniform while rewinding never
produces distinct challenges. An unreachable state checks that the atom bound is required only
on the first-stage support.
-/

namespace ComplexityTests.Crypto.Rewinding

open Cslib.Probability

/-- A biased challenge, with the heavy atom at `true`. -/
private noncomputable def biased : PMF Bool :=
  PMF.ofFintype (fun b => cond b (3 / 4) (1 / 4)) (by
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by finiteness))

private theorem biased_atom_le (b : Bool) : (biased b).toReal ≤ 3 / 4 := by
  cases b <;> norm_num [biased]

/-! ### The uniform-cardinality loss does not apply to a biased challenge -/

theorem biased_once :
    (Rewinding.once (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ _ _ => true) true).toReal = 1 := by
  simp [Rewinding.once]

theorem biased_twice :
    (Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ _ _ => true) true).toReal = 3 / 8 := by
  norm_num [Rewinding.twice, biased, PMF.bind_apply, tsum_bool]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul]

/-- The old cardinality loss would predict `1 / 2`, exceeding the actual `3 / 8`. -/
example :
    (Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ _ _ => true) true).toReal < (1 - 1 / Fintype.card Bool : ℝ) := by
  rw [biased_twice]
  norm_num

/-- The maximum-atom theorem applies and gives the valid lower bound `1 / 4`. -/
example :
    (1 / 4 : ℝ) ≤
      (Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
        (fun _ _ _ => true) true).toReal := by
  have h := Rewinding.sq_sub_mul_le_twice (PMF.pure ()) (fun _ => biased)
    (fun _ _ => PMF.pure ()) (fun _ _ _ => true) (κ := 3 / 4)
    (fun _ _ => biased_atom_le)
  rw [biased_once] at h
  norm_num at h ⊢
  exact h

/-! ### The maximum-atom loss is sharp -/

theorem heavy_once :
    (Rewinding.once (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ b _ => b) true).toReal = 3 / 4 := by
  norm_num [Rewinding.once, biased, PMF.bind_apply, tsum_bool]

theorem heavy_twice :
    (Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ b _ => b) true).toReal = 0 := by
  norm_num [Rewinding.twice, biased, PMF.bind_apply, tsum_bool]

/-- Acceptance only at the heavy atom attains `δ = ε² - κ ε = 0`. -/
example :
    (Rewinding.once (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ b _ => b) true).toReal ^ 2 -
        (3 / 4 : ℝ) *
          (Rewinding.once (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
            (fun _ b _ => b) true).toReal =
      (Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
        (fun _ b _ => b) true).toReal := by
  rw [heavy_once, heavy_twice]
  norm_num

/-- The inverse bound also attains equality on the heavy-atom strategy. -/
example :
    (Rewinding.once (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
      (fun _ b _ => b) true).toReal ≤
        3 / 4 + Real.sqrt
          ((Rewinding.twice (PMF.pure ()) (fun _ => biased) (fun _ _ => PMF.pure ())
            (fun _ b _ => b) true).toReal) :=
  Rewinding.le_add_sqrt_twice (PMF.pure ()) (fun _ => biased)
    (fun _ _ => PMF.pure ()) (fun _ b _ => b) (fun _ _ => biased_atom_le)

/-! ### Rewinding draws fresh second-stage coins -/

/-- A fair independent response bit is accepted with probability `1 / 2`. -/
example :
    (Rewinding.once (PMF.pure ()) (fun _ => PMF.uniformOfFintype Bool)
      (fun _ _ => PMF.uniformOfFintype Bool) (fun _ _ answer => answer) true).toReal =
        1 / 2 := by
  norm_num [Rewinding.once, PMF.bind_apply, tsum_bool]

/-- Two fresh response bits and distinct fair challenges succeed with probability `1 / 8`.
Reusing the first response bit would instead give `1 / 4`. -/
example :
    (Rewinding.twice (PMF.pure ()) (fun _ => PMF.uniformOfFintype Bool)
      (fun _ _ => PMF.uniformOfFintype Bool) (fun _ _ answer => answer) true).toReal =
        1 / 8 := by
  norm_num [Rewinding.twice, PMF.bind_apply, tsum_bool]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul]

/-! ### Conditional laws, rather than marginal laws, control rewinding -/

/-- A challenge equal to a uniform saved bit has a uniform marginal. -/
example :
    (do
      let state ← PMF.uniformOfFintype Bool
      pure state) = PMF.uniformOfFintype Bool := by
  simp

theorem saved_state_once :
    (Rewinding.once (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
      (fun _ _ => PMF.pure ()) (fun _ _ _ => true) true).toReal = 1 := by
  simp [Rewinding.once]

theorem saved_state_twice :
    (Rewinding.twice (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
      (fun _ _ => PMF.pure ()) (fun _ _ _ => true) true).toReal = 0 := by
  simp [Rewinding.twice]

/-- The conditional maximum atom is one: reusing the state forces equal challenges. -/
example :
    (Rewinding.once (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
      (fun _ _ => PMF.pure ()) (fun _ _ _ => true) true).toReal ^ 2 -
        (Rewinding.once (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
          (fun _ _ => PMF.pure ()) (fun _ _ _ => true) true).toReal ≤
      (Rewinding.twice (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
        (fun _ _ => PMF.pure ()) (fun _ _ _ => true) true).toReal := by
  simpa only [one_mul] using
    Rewinding.sq_sub_mul_le_twice (PMF.uniformOfFintype Bool) (fun state => PMF.pure state)
      (fun _ _ => PMF.pure ()) (fun _ _ _ => true) (κ := 1) (by
        intro state _ challenge
        cases state <;> cases challenge <;> norm_num)

/-! ### Unreachable states need no atom bound -/

/-- The first stage always returns `false`; the deterministic law at `true` is unreachable. -/
example :
    (Rewinding.once (PMF.pure false)
      (fun state => if state then PMF.pure true else biased)
      (fun _ _ => PMF.pure ()) (fun _ b _ => b) true).toReal ^ 2 -
        (3 / 4 : ℝ) *
          (Rewinding.once (PMF.pure false)
            (fun state => if state then PMF.pure true else biased)
            (fun _ _ => PMF.pure ()) (fun _ b _ => b) true).toReal ≤
      (Rewinding.twice (PMF.pure false)
        (fun state => if state then PMF.pure true else biased)
        (fun _ _ => PMF.pure ()) (fun _ b _ => b) true).toReal := by
  apply Rewinding.sq_sub_mul_le_twice
  intro state hstate challenge
  have hstate' : state = false := (PMF.mem_support_pure_iff _ _).mp hstate
  subst state
  exact biased_atom_le challenge

end ComplexityTests.Crypto.Rewinding
