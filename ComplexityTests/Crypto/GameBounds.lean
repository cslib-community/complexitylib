/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Crypto.Game

/-! Clients of pointwise and common-mixture game advantage bounds. -/

namespace ComplexityTests.GameBounds

open Cslib Cslib.Crypto
open scoped NNReal ENNReal

-- Mutual probability bounds compose through an arbitrary common first-stage sampler.
example {α : Type*} (d : PMF α) (game1 game2 : α → Game) (ε : ℝ≥0)
    (h1 : ∀ a, game1 a true ≤ game2 a true + (ε : ℝ≥0∞))
    (h2 : ∀ a, game2 a true ≤ game1 a true + (ε : ℝ≥0∞)) :
    (Game.advantage (d.bind game1) (d.bind game2) : ℝ) ≤ ε := by
  apply Game.advantage_bind_le
  intro a
  simpa using Game.advantage_le_of_apply_le (B := (ε : ℝ≥0∞)) (by simp) (h1 a) (h2 a)

-- Zero advantage is preserved without requiring a finite first-stage type.
example (d : PMF ℕ) (game : ℕ → Game) :
    (Game.advantage (d.bind game) (d.bind game) : ℝ) ≤ 0 := by
  apply Game.advantage_bind_le
  intro n
  simp

-- The finite-error premise matters: top has real value zero, but these games differ maximally.
example : ¬ ((Game.advantage (PMF.pure true) (PMF.pure false) : ℝ) ≤ (⊤ : ℝ≥0∞).toReal) := by
  simp [Game.succProbability]

-- NNReal mixture, pointwise error-averaging, support, and bind-commutativity bounds.
example {α : Type*} (d : PMF α) (game1 game2 : α → Game) {ε : ℝ≥0}
    (h : ∀ a, Game.advantage (game1 a) (game2 a) ≤ ε) :
    Game.advantage (d.bind game1) (d.bind game2) ≤ ε :=
  Game.advantage_bind_le_nnreal d game1 game2 h

example {α : Type*} (d : PMF α) (game1 game2 : α → Game) {ε : ℝ≥0}
    (h : ∀ a ∈ d.support, Game.advantage (game1 a) (game2 a) ≤ ε) :
    Game.advantage (d.bind game1) (d.bind game2) ≤ ε :=
  Game.advantage_bind_le_of_support d game1 game2 h

example {β : Type*} (μ : PMF β) (game1 game2 err : β → Game)
    (h : ∀ x, game1 x true ≤ game2 x true + err x true ∧
      game2 x true ≤ game1 x true + err x true) :
    Game.advantage (μ.bind game1) (μ.bind game2) ≤ Game.succProbability (μ.bind err) :=
  Game.advantage_bind_le_succProbability_bind μ game1 game2 err h

example {α β : Type*} (p : PMF α) (q : PMF β) (f g : α → β → Game) :
    Game.advantage (p.bind fun a => q.bind fun b => f a b)
      (p.bind fun a => q.bind fun b => g a b) =
    Game.advantage (q.bind fun b => p.bind fun a => f a b)
      (q.bind fun b => p.bind fun a => g a b) :=
  Game.advantage_bind_comm p q f g

open Cslib.Probability in
-- Concrete check of `succProbability_uniform_bool_xor`: when `g false = PMF.pure true` and
-- `g true = PMF.pure false`, `guess ^^ bit` is always `true`, so the success probability is `1`.
example :
    (Game.succProbability
      ((PMF.uniformOfFintype Bool).bind fun bit =>
        ((if bit then PMF.pure false else PMF.pure true : Game)).map
          (fun guess => guess ^^ bit)) : ℝ) = 1 := by
  rw [Game.succProbability_uniform_bool_xor]
  simp [Game.succProbability]

open Cslib.Probability in
-- Hidden-bit XOR mixture bound `advantage_le_two_mul_uniform_bool_xor`.
example (g₀ g₁ : Bool → Game) :
    Game.advantage (g₀ false) (g₀ true) ≤
      2 * Game.advantage
        ((PMF.uniformOfFintype Bool).bind fun bit => (g₀ bit).map (fun guess => guess ^^ bit))
        ((PMF.uniformOfFintype Bool).bind fun bit => (g₁ bit).map (fun guess => guess ^^ bit)) +
      Game.advantage (g₁ false) (g₁ true) :=
  Game.advantage_le_two_mul_uniform_bool_xor g₀ g₁

open Cslib.Probability in
-- Tightness / refutation test: the factor `2` in `advantage_le_two_mul_uniform_bool_xor` cannot be
-- replaced by `1`. For `g₀ bit = PMF.pure (!bit)` and `g₁ _ = PMF.pure false`, the game gap of `g₀`
-- is `1`, the game gap of `g₁` is `0`, and the hidden-bit XOR mixture advantage is `1 / 2`.
example :
    let g₀ : Bool → Game := fun bit => PMF.pure (!bit)
    let g₁ : Bool → Game := fun _ => PMF.pure false
    ¬ (Game.advantage (g₀ false) (g₀ true) ≤
      1 * Game.advantage
        ((PMF.uniformOfFintype Bool).bind fun bit => (g₀ bit).map (fun guess => guess ^^ bit))
        ((PMF.uniformOfFintype Bool).bind fun bit => (g₁ bit).map (fun guess => guess ^^ bit)) +
      Game.advantage (g₁ false) (g₁ true)) := by
  dsimp only
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, Game.coe_advantage,
    Game.succProbability_uniform_bool_xor, Game.succProbability]
  norm_num

end ComplexityTests.GameBounds
