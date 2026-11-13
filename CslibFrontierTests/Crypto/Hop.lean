/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.Hop

/-! Checked examples for `x ≈[ε] y` and game hops written as `calc` chains. -/

namespace CslibFrontierTests.Crypto.Hop

open Cslib Cslib.Crypto Probability
open scoped NNReal

/-! ### The relation -/

-- `=` steps, `|x - y| ≤ ε` proofs and `≈[ε]` steps compose, and the errors add.
example (a b c d : ℝ) (h₁ : a = b) (h₂ : |b - c| ≤ 1) (h₃ : c ≈[2] d) : a ≈[1 + 2] d :=
  calc a = b := h₁
    _ ≈[1] c := h₂
    _ ≈[2] d := h₃

-- A hop gives both one-sided bounds.
example (x y ε : ℝ) (h : x ≈[ε] y) : x ≤ y + ε ∧ y - ε ≤ x :=
  ⟨h.le_add, h.sub_le⟩

-- Precedence: the sides are sums, the relation is a proposition.
example (a b c ε : ℝ) (h : a + b ≈[ε] c) (hε : ε ≤ 1) : (a + b ≈[1] c) ∧ True :=
  ⟨h.mono hε, trivial⟩

/-! ### Game hops -/

-- One exact hop and two bounded hops, read off as an `ℝ≥0` advantage bound.
example (G₀ G₁ G₂ G₃ : Game) (ε₁ ε₂ : ℝ≥0) (h₀₁ : G₀ = G₁) (h₁₂ : G₁.advantage G₂ ≤ ε₁)
    (h₂₃ : G₂.advantage G₃ ≤ ε₂) : G₀.advantage G₃ ≤ ε₁ + ε₂ :=
  Game.advantage_le_of_approxEq
    (calc Pr[G₀] = Pr[G₁] := by rw [h₀₁]
      _ ≈[ε₁] Pr[G₂] := Game.approxEq_of_advantage_le h₁₂
      _ ≈[ε₂] Pr[G₃] := Game.approxEq_of_advantage_le h₂₃)

-- A looser bound than the chain's sum of errors is proved explicitly.
example (G₀ G₁ G₂ : Game) (ε : ℝ≥0) (h₀₁ : G₀.advantage G₁ ≤ ε) (h₁₂ : G₁.advantage G₂ ≤ ε) :
    G₀.advantage G₂ ≤ 3 * ε :=
  Game.advantage_le_of_approxEq
    (calc Pr[G₀] ≈[ε] Pr[G₁] := Game.approxEq_of_advantage_le h₀₁
      _ ≈[ε] Pr[G₂] := Game.approxEq_of_advantage_le h₁₂)
    (by push_cast; linarith [ε.coe_nonneg])

-- A hop of unknown cost is charged its advantage, and a reversed bound is a reversed hop.
example (G₀ M₀ M₁ G₁ : Game) (c : ℝ≥0) (h₀ : G₀.advantage M₀ ≤ c) (h₁ : G₁.advantage M₁ ≤ c) :
    Pr[G₀] ≈[c + M₀.advantage M₁ + c] Pr[G₁] :=
  calc Pr[G₀] ≈[c] Pr[M₀] := Game.approxEq_of_advantage_le h₀
    _ ≈[M₀.advantage M₁] Pr[M₁] := Game.approxEq_advantage M₀ M₁
    _ ≈[c] Pr[G₁] := (Game.approxEq_of_advantage_le h₁).symm

-- A real-valued advantage bound and a hop are the same statement.
example (G₀ G₁ : Game) (ε : ℝ) (h : (G₀.advantage G₁ : ℝ) ≤ ε) : Pr[G₀] ≈[ε] Pr[G₁] :=
  Game.approxEq_iff_advantage_le.mpr h

-- A one-sided bound comes out of a hop.
example (G₀ G₁ : Game) (q : ℕ) (ε : ℝ≥0) (h : G₀.advantage G₁ ≤ ε) (h₁ : Pr[G₁] ≤ 1 / q) :
    Pr[G₀] ≤ 1 / q + ε :=
  (Game.approxEq_of_advantage_le h).le_add.trans (by gcongr)

-- The one-time pad on one bit: both messages give a fair coin, so the games are `0`-close.
noncomputable def otp (m : Bool) : ProbComp Bool := do
  let k ← ProbComp.uniform Bool
  return xor m k

example : Pr[otp true] ≈[0] Pr[otp false] := by
  have h (m : Bool) : Pr[otp m] = 1 / 2 := by
    cases m <;> simp [otp]
  rw [h, h]
  exact ApproxEq.refl _

end CslibFrontierTests.Crypto.Hop
