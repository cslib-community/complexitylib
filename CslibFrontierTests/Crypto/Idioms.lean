/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.Hop
import CslibFrontier.Crypto.Game.Experiment
import CslibFrontier.Languages.Probabilistic.Lift

/-! Readability idioms: `$ᵗ α` sampling, `x ≈[ε] y` hop chains, and programs lifted into
distributions. -/

namespace CslibFrontierTests.Crypto.Idioms

open Cslib Cslib.Crypto Probability
open scoped NNReal

variable (q : ℕ) [NeZero q]

/-! ### `$ᵗ α` -/

section Sampling

set_option linter.hashCommand false

-- `$ᵗ α` is exactly `ProbComp.uniform α`: no new constant.
#guard_expr ($ᵗ ZMod q) =ₛ ProbComp.uniform (ZMod q)
#guard_expr ($ᵗ (ZMod q × Bool)) =ₛ ProbComp.uniform (ZMod q × Bool)

end Sampling

-- It prints back, inside `do` blocks and next to other operators.
/-- info: $ᵗ ZMod q : ProbComp (ZMod q) -/
#guard_msgs in
#check ProbComp.uniform (ZMod q)

/--
info: do
  let a ← $ᵗ ZMod q
  let b ← $ᵗ ZMod q
  pure (a * b) : ProbComp (ZMod q)
-/
#guard_msgs in
#check (do let a ← $ᵗ ZMod q; let b ← $ᵗ ZMod q; return a * b : ProbComp (ZMod q))

/-- info: (fun x => x + 1) <$> $ᵗ ZMod q : ProbComp (ZMod q) -/
#guard_msgs in
#check (· + 1) <$> $ᵗ ZMod q

/-- info: $ᵗ (ZMod q × Bool) : ProbComp (ZMod q × Bool) -/
#guard_msgs in
#check $ᵗ (ZMod q × Bool)

-- `$` application still parses next to it (repo style prefers `<|`; this checks the parser).
set_option linter.style.dollarSyntax false in
example : (id $ $ᵗ Bool) = ProbComp.uniform Bool := rfl

-- The law and `simp` see `ProbComp.uniform`.
example : ProbComp.eval ($ᵗ Bool) = PMF.uniformOfFintype Bool := by
  simp only [ProbComp.eval_uniform]

example : Pr[do let b ← $ᵗ Bool; return b] = 1 / 2 := by
  simp

/-! ### `x ≈[ε] y` -/

example (a b c d : ℝ) (h₁ : a = b) (h₂ : |b - c| ≤ 1) (h₃ : c ≈[2] d) : a ≈[1 + 2] d :=
  calc a = b := h₁
    _ ≈[1] c := h₂
    _ ≈[2] d := h₃

-- A hop sequence over experiments: one exact hop, two bounded ones, read off as an `ℝ≥0`
-- advantage bound.
example (e₀ e₁ e₂ e₃ : Experiment) (ε₁ ε₂ : ℝ≥0) (h₀₁ : ProbComp.eval e₀ = ProbComp.eval e₁)
    (h₁₂ : Experiment.advantage e₁ e₂ ≤ ε₁) (h₂₃ : Experiment.advantage e₂ e₃ ≤ ε₂) :
    Experiment.advantage e₀ e₃ ≤ ε₁ + ε₂ :=
  Game.advantage_le_of_approxEq
    (calc Pr[e₀] = Pr[e₁] := by rw [h₀₁]
      _ ≈[ε₁] Pr[e₂] := Game.approxEq_of_advantage_le h₁₂
      _ ≈[ε₂] Pr[e₃] := Game.approxEq_of_advantage_le h₂₃)
    (by exact_mod_cast le_rfl)

-- One-sided bounds come out of a chain.
example (e₀ e₁ : Experiment) (ε : ℝ≥0) (h : Experiment.advantage e₀ e₁ ≤ ε)
    (h₁ : Pr[e₁] ≤ 1 / q) : Pr[e₀] ≤ 1 / q + ε :=
  (Game.approxEq_of_advantage_le h).le_add.trans (by gcongr)

-- The one-time pad: each message gives a fair coin, so the two experiments are `0`-close.
noncomputable def otp (m : Bool) : Experiment := do
  let k ← $ᵗ Bool
  return xor m k

example : Pr[otp true] ≈[0] Pr[otp false] := by
  have h (m : Bool) : Pr[otp m] = 1 / 2 := by
    cases m <;> simp [otp]
  rw [h, h]
  exact ApproxEq.refl _

/-! ### Programs inside distributions -/

-- A distribution binds a program directly; the lift is the law.
noncomputable def liftedGame (choose : ProbComp (Bool × Bool)) (next : Bool → PMF Bool) :
    PMF Bool := do
  let (x, y) ← choose
  next (xor x y)

example (choose : ProbComp (Bool × Bool)) (next : Bool → PMF Bool) :
    liftedGame choose next = (ProbComp.eval choose).bind fun (x, y) => next (xor x y) := by
  simp only [liftedGame, pmf_norm]

-- The lifted definition is the explicit one by definition.
example (choose : ProbComp (Bool × Bool)) (next : Bool → PMF Bool) :
    liftedGame choose next = (ProbComp.eval choose).bind fun (x, y) => next (xor x y) :=
  rfl

example (program : ProbComp Bool) : (liftM program : PMF Bool) = ProbComp.eval program :=
  ProbComp.liftM_eq_eval program

-- A program where a distribution is expected is lifted silently; `simp` reads it back.
example (program : ProbComp Bool) :
    Game.advantage program (ProbComp.eval program) = 0 := by
  simp only [ProbComp.monadLift_eq_eval, Game.advantage_self]

-- `Pr[·]` still reads a program as a program, not as a lifted distribution.
set_option linter.hashCommand false in
#guard_expr Pr[$ᵗ Bool] =ₛ ENNReal.toReal (ProbComp.eval (ProbComp.uniform Bool) true)

end CslibFrontierTests.Crypto.Idioms
