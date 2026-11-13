/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Notation

/-! The scoped notation `Pr[e]`: its two elaborated forms, `do` blocks, display and API. -/

namespace CslibFrontierTests.ProbabilityNotation

open Cslib Probability

variable (program : ProbComp Bool) (next : Fin 2 → ProbComp Bool) (μ : PMF Bool)
  (mass : Bool → ENNReal)

section Elaboration

-- `#guard_expr` checks syntactic equality of elaborated terms and is silent when it succeeds,
-- which the `#`-command linter would otherwise report.
set_option linter.hashCommand false

-- A program elaborates to exactly the real probability of `true` under its distribution, and a
-- distribution to its own real probability of `true`. No new constant appears.
#guard_expr Pr[program] =ₛ ENNReal.toReal (ProbComp.eval program true)
#guard_expr Pr[μ] =ₛ ENNReal.toReal (μ true)

-- A `do` block or a chain of binds is read as a program, not as a distribution.
#guard_expr Pr[do let b ← ProbComp.uniform Bool; return !b] =ₛ
  ENNReal.toReal (ProbComp.eval (do let b ← ProbComp.uniform Bool; return !b) true)
#guard_expr Pr[ProbComp.uniform (Fin 2) >>= next] =ₛ
  ENNReal.toReal (ProbComp.eval (ProbComp.uniform (Fin 2) >>= next) true)

end Elaboration

-- Both forms print back as `Pr[e]`; other masses of `true` and other outcomes do not.
/-- info: Pr[program] : ℝ -/
#guard_msgs in
#check ENNReal.toReal (ProbComp.eval program true)
/-- info: Pr[μ] : ℝ -/
#guard_msgs in
#check ENNReal.toReal (μ true)
/-- info: (mass true).toReal : ℝ -/
#guard_msgs in
#check ENNReal.toReal (mass true)
/-- info: (program.eval false).toReal : ℝ -/
#guard_msgs in
#check ENNReal.toReal (ProbComp.eval program false)

-- A fair coin, through the single-outcome form.
example : Pr[(· == true) <$> ProbComp.uniform Bool] = 1 / 2 := by
  rw [ProbComp.probability_map_beq, ProbComp.eval_uniform, PMF.uniformOfFintype_apply]
  simp

-- A set event of a distribution.
example (ν : PMF (Fin 3)) : Pr[(fun x => decide (x ∈ ({0} : Set (Fin 3)))) <$> ν] =
    (ν 0).toReal := by
  rw [PMF.probability_map_decide_mem, PMF.toOuterMeasure_apply_singleton]

-- The finite-average bind law and the bounds.
example : Pr[ProbComp.uniform (Fin 2) >>= next] = (Pr[next 0] + Pr[next 1]) / 2 := by
  rw [ProbComp.probability_bind]
  simp [Fin.sum_univ_two, PMF.uniformOfFintype_apply]
  ring

example : 0 ≤ Pr[program] ∧ Pr[program] ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, PMF.toReal_apply_le_one _ _⟩

-- The event bound, through the set-event form of the notation.
example (ν : PMF (Fin 3)) (s : Set (Fin 3)) [DecidablePred (· ∈ s)] :
    Pr[(fun x => decide (x ∈ s)) <$> ν] ≤ 1 := by
  rw [PMF.probability_map_decide_mem]
  exact PMF.toOuterMeasure_toReal_le_one ν s

example : Pr[pure true] = 1 := by
  rw [ProbComp.probability_pure]
  rfl

/-! ### Uniform sampling `$ᵗ α` -/

section Sampling

set_option linter.hashCommand false

-- `$ᵗ α` is exactly `ProbComp.uniform α`: no new constant.
#guard_expr ($ᵗ Fin 3) =ₛ ProbComp.uniform (Fin 3)
#guard_expr ($ᵗ (Fin 3 × Bool)) =ₛ ProbComp.uniform (Fin 3 × Bool)

end Sampling

-- It prints back, inside `do` blocks and next to other operators.
/-- info: $ᵗ Fin 3 : ProbComp (Fin 3) -/
#guard_msgs in
#check ProbComp.uniform (Fin 3)

/--
info: do
  let a ← $ᵗ Fin 3
  let b ← $ᵗ Fin 3
  pure (a * b) : ProbComp (Fin 3)
-/
#guard_msgs in
#check (do let a ← $ᵗ Fin 3; let b ← $ᵗ Fin 3; return a * b : ProbComp (Fin 3))

/-- info: (fun x => x + 1) <$> $ᵗ Fin 3 : ProbComp (Fin 3) -/
#guard_msgs in
#check (· + 1) <$> $ᵗ Fin 3

/-- info: $ᵗ (Fin 3 × Bool) : ProbComp (Fin 3 × Bool) -/
#guard_msgs in
#check $ᵗ (Fin 3 × Bool)

-- `$` application still parses next to it (repo style prefers `<|`; this checks the parser).
set_option linter.style.dollarSyntax false in
example : (id $ $ᵗ Bool) = ProbComp.uniform Bool := rfl

-- The law, `simp` and `Pr[·]` see `ProbComp.uniform`.
example : ProbComp.eval ($ᵗ Bool) = PMF.uniformOfFintype Bool := by
  rw [ProbComp.eval_uniform]

example : Pr[do let b ← $ᵗ Bool; return b] = 1 / 2 := by
  simp

end CslibFrontierTests.ProbabilityNotation

/-! Outside the `Probability` scope, `ProbComp.uniform` prints as itself. -/

namespace CslibFrontierTests.ProbabilityNotation.Unscoped

open Cslib

/-- info: ProbComp.uniform (Fin 3) : ProbComp (Fin 3) -/
#guard_msgs in
#check ProbComp.uniform (Fin 3)

end CslibFrontierTests.ProbabilityNotation.Unscoped
