/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the game_trans and peel_binds tactics)

public import CslibFrontier.Crypto.Game.CloseTo.Statistical
public import CslibFrontier.Tactic.GameHop

/-!
# Tests for `game_trans` and `peel_binds`
-/

public section

namespace CslibFrontierTests.GameHopTactic

open Cslib Cslib.Crypto Cslib.Interactive Cslib.Probability
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### `closeTo_of_dist_le_ofReal` bridge -/

example :
    CloseTo (PMF.pure true) (PMF.uniformOfFintype Bool) (ENNReal.ofReal (1 / 2 : ℝ)) := by
  have h : dist (PMF.pure true) (PMF.uniformOfFintype Bool) ≤ (1 / 2 : ℝ) := by
    norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
      PMF.uniformOfFintype_apply]
  exact closeTo_of_dist_le_ofReal h

/-! ### `game_trans` positive tests -/

/-- Interactive subgoal splitting over `ℝ≥0` (bracketed syntax). -/
example (g₀ g₁ g₂ g₃ : Game) (ε₀ ε₁ ε₂ : ℝ≥0)
    (h₀ : Game.advantage g₀ g₁ ≤ ε₀)
    (h₁ : Game.advantage g₁ g₂ ≤ ε₁)
    (h₂ : Game.advantage g₂ g₃ ≤ ε₂) :
    Game.advantage g₀ g₃ ≤ ε₀ + ε₁ + ε₂ := by
  game_trans [g₁, g₂]
  · exact h₀
  · exact h₁
  · exact h₂
  · rfl

/-- Unbracketed list syntax and `using` with reversed `advantage_comm`, equality `g₃ = g₂`,
pass-through `le_rfl`, and automatic `ring` bound discharge. -/
example (g₀ g₁ g₂ g₃ g₄ : Game) (ε : ℝ≥0)
    (h₀ : Game.advantage g₁ g₀ ≤ ε)
    (heq : g₃ = g₂)
    (h₃ : Game.advantage g₄ g₃ ≤ ε) :
    Game.advantage g₀ g₄ ≤ Game.advantage g₁ g₂ + 2 * ε := by
  game_trans g₁, g₂, g₃ using [h₀, le_rfl, heq, h₃]

/-- Partial `using` with a hole `_` leaves only that hop and the trailing sum bound. -/
example (g₀ g₁ g₂ : Game) (ε₀ ε₁ B : ℝ≥0)
    (h₀ : Game.advantage g₁ g₀ ≤ ε₀)
    (h₁ : Game.advantage g₁ g₂ ≤ ε₁)
    (hB : ε₀ + ε₁ ≤ B) :
    Game.advantage g₀ g₂ ≤ B := by
  game_trans [g₁] using [h₀, _]
  · exact h₁
  · exact hB

/-- Real-valued `(Game.advantage : ℝ)` hops mixing `ℝ` bounds and reversed `ℝ≥0` bounds. -/
example (g₀ g₁ g₂ g₃ : Game) (ε₁ : ℝ≥0) (ε₂ : ℝ)
    (h₀ : Game.advantage g₁ g₀ ≤ ε₁)
    (h₁ : (Game.advantage g₂ g₁ : ℝ) ≤ ε₂)
    (h₂ : Game.advantage g₂ g₃ ≤ ε₁) :
    (Game.advantage g₀ g₃ : ℝ) ≤ 2 * (ε₁ : ℝ) + ε₂ := by
  game_trans [g₁, g₂] using [h₀, h₁, h₂]

/-- `Encryption.advantage` unfolding with and without intermediate games. -/
example (exp : Bool → ℕ → ProbComp Bool) (mid : Game) (n : ℕ) (ε₀ ε₁ : ℝ≥0)
    (h₀ : Game.advantage (ProbComp.eval (exp false n)) mid ≤ ε₀)
    (h₁ : Game.advantage (ProbComp.eval (exp true n)) mid ≤ ε₁) :
    Encryption.advantage exp n ≤ ε₀ + ε₁ := by
  game_trans [mid] using [h₀, h₁]

example (exp : Bool → ℕ → ProbComp Bool) (n : ℕ) (ε : ℝ≥0)
    (h : Game.advantage (ProbComp.eval (exp true n)) (ProbComp.eval (exp false n)) ≤ ε) :
    Encryption.advantage exp n ≤ ε := by
  game_trans
  rw [Game.advantage_comm]
  exact h

/-- `Game.succProbability` hops in `ℝ≥0` and `ℝ`, both direct (reversed) and multi-hop. -/
example (g₀ g₁ : Game) (ε : ℝ≥0) (h : Game.advantage g₁ g₀ ≤ ε) :
    Game.succProbability g₀ ≤ Game.succProbability g₁ + ε := by
  game_trans using h

example (g₀ g₁ g₂ : Game) (ε₀ ε₁ : ℝ≥0)
    (h₀ : Game.advantage g₀ g₁ ≤ ε₀) (h₁ : Game.advantage g₂ g₁ ≤ ε₁) :
    Game.succProbability g₀ ≤ ε₁ + ε₀ + Game.succProbability g₂ := by
  game_trans [g₁] using [h₀, h₁]

example (g₀ g₁ g₂ : Game) (ε₀ : ℝ≥0) (ε₁ : ℝ)
    (h₀ : Game.advantage g₁ g₀ ≤ ε₀) (h₁ : (Game.advantage g₁ g₂ : ℝ) ≤ ε₁) :
    (Game.succProbability g₀ : ℝ) ≤ (Game.succProbability g₂ : ℝ) + (ε₁ + ε₀) := by
  game_trans [g₁] using [h₀, h₁]

/-- `CloseTo` hops over an infinite type `PMF ℕ` with symmetry and equality steps. -/
example (μ₀ μ₁ μ₂ μ₃ : PMF ℕ) (ε₀ ε₂ : ℝ≥0∞)
    (h₀ : CloseTo μ₁ μ₀ ε₀)
    (heq : μ₁ = μ₂)
    (h₂ : CloseTo μ₂ μ₃ ε₂) :
    CloseTo μ₀ μ₃ (ε₂ + ε₀) := by
  game_trans [μ₁, μ₂] using [h₀, heq, h₂]

-- Sibling goals remain untouched when `game_trans` closes the active goal.
set_option linter.style.multiGoal false in
example (g₀ g₁ g₂ : Game) (ε : ℝ≥0)
    (h₀ : Game.advantage g₀ g₁ ≤ ε) (h₁ : Game.advantage g₁ g₂ ≤ ε) :
    Game.advantage g₀ g₂ ≤ 2 * ε ∧ Nonempty ℕ := by
  constructor
  game_trans [g₁] using [h₀, h₁]
  exact ⟨0⟩

/-! ### `peel_binds` positive tests -/

/-- Multi-bind peeling over `ℝ≥0` using support membership hypotheses `<x>_mem` in the body,
while unused support hypotheses emit no unused-variable warnings. -/
example (μ : PMF ℕ) (ν : ℕ → PMF Bool) (f g : ℕ → Bool → Game) (ε : ℝ≥0)
    (h : ∀ x ∈ μ.support, ∀ b, Game.advantage (f x b) (g x b) ≤ ε) :
    Game.advantage
      (μ.bind fun a => (ν a).bind fun b => f a b)
      (μ.bind fun a => (ν a).bind fun b => g a b) ≤ ε := by
  peel_binds x b
  exact h x x_mem b

/-- Omitting binder names peels all shared leading stages, retaining original binder names. -/
example (μ : PMF ℕ) (ν : PMF Bool) (f g : ℕ → Bool → Game) (ε : ℝ)
    (h : ∀ a ∈ μ.support, ∀ b ∈ ν.support, (Game.advantage (f a b) (g a b) : ℝ) ≤ ε) :
    (Game.advantage
      (μ.bind fun a => ν.bind fun b => f a b)
      (μ.bind fun a => ν.bind fun b => g a b) : ℝ) ≤ ε := by
  peel_binds
  exact h a a_mem b b_mem

/-- Outer `ProbComp.eval` monadic `do`-notation is normalized at the head without unfolding `f`. -/
example (m₁ : ProbComp ℕ) (m₂ : ℕ → ProbComp Bool) (f g : ℕ → Bool → ProbComp Bool) (ε : ℝ≥0)
    (h : ∀ x ∈ (ProbComp.eval m₁).support, ∀ y ∈ (ProbComp.eval (m₂ x)).support,
      Game.advantage (ProbComp.eval (f x y)) (ProbComp.eval (g x y)) ≤ ε) :
    Game.advantage
      (ProbComp.eval (do let x ← m₁; let y ← m₂ x; f x y))
      (ProbComp.eval (do let x ← m₁; let y ← m₂ x; g x y)) ≤ ε := by
  peel_binds x y
  exact h x x_mem y y_mem

/-- One-step independent swap on RHS and on LHS, on `CloseTo` and `PMF` equality. -/
example (μ : PMF ℕ) (ν : PMF Bool) (f g : ℕ → Bool → PMF ℕ) (ε : ℝ≥0∞)
    (h : ∀ x ∈ μ.support, ∀ b ∈ ν.support, CloseTo (f x b) (g x b) ε) :
    CloseTo
      (μ.bind fun x => ν.bind fun b => f x b)
      (ν.bind fun b => μ.bind fun x => g x b) ε := by
  peel_binds x b
  exact h x x_mem b b_mem

example (μ : PMF ℕ) (ν : PMF Bool) (f : ℕ → Bool → PMF ℕ) (g : ℕ → PMF ℕ)
    (h : ∀ x ∈ μ.support, (ν.bind fun b => f x b) = g x) :
    (ν.bind fun b => μ.bind fun x => f x b) = μ.bind g := by
  peel_binds x
  exact h x x_mem

/-- Peeling and one-step independent swapping across `Game.runStatelessOracle` stages. -/
example (o₁ o₂ : List Bool → List Bool)
    (prog₁ : WordOracleComp Unit ℕ) (prog₂ : WordOracleComp Unit Bool)
    (f g : ℕ → Bool → Game) (ε : ℝ≥0)
    (h : ∀ out₁ ∈ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (fun req (s : Unit) => pure (o₁ req.2, s))) prog₁).run ())).support,
      ∀ out₂ ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (fun req (s : Unit) => pure (o₂ req.2, s))) prog₂).run ())).support,
      Game.advantage (f out₁.1 out₂.1) (g out₁.1 out₂.1) ≤ ε) :
    Game.advantage
      (Game.runStatelessOracle o₁ prog₁ fun a => Game.runStatelessOracle o₂ prog₂ fun b => f a b)
      (Game.runStatelessOracle o₂ prog₂ fun b =>
        Game.runStatelessOracle o₁ prog₁ fun a => g a b) ≤ ε := by
  peel_binds out₁ out₂
  exact h out₁ out₁_mem out₂ out₂_mem

/-- `peel_binds` composes inside a `game_trans` hop subgoal (with uninstantiated `?ε`) and sees
through local `let` definitions of games. -/
example (d₁ : PMF ℕ) (d₂ : PMF Bool) (d₃ : PMF (Fin 2))
    (f g h : ℕ → Bool → Fin 2 → Game) (ε₁ ε₂ : ℝ≥0)
    (hfg : ∀ a b c, Game.advantage (f a b c) (g a b c) ≤ ε₁)
    (hgh : ∀ a b c, Game.advantage (g a b c) (h a b c) ≤ ε₂) :
    let lhsGame : Game := d₁.bind fun a => d₂.bind fun b => d₃.bind fun c => f a b c
    Game.advantage lhsGame
      (d₁.bind fun a => d₂.bind fun b => d₃.bind fun c => h a b c) ≤ ε₁ + ε₂ := by
  intro lhsGame
  game_trans [d₁.bind fun a => d₂.bind fun b => d₃.bind fun c => g a b c]
  · peel_binds a b c
    exact hfg a b c
  · peel_binds a b c
    exact hgh a b c
  · rfl

/-- Regression (1): binderless `peel_binds` rolls back `Meta.SavedState` cleanly when a subsequent
stage normalizes (`ProbComp.eval (do ...)`) and fails to match, without leaking metavariables. -/
example (μ : PMF ℕ) (m₁ : ProbComp ℕ) (m₂ : ProbComp Bool)
    (k₁ : ℕ → ℕ → ProbComp Bool) (k₂ : ℕ → Bool → ProbComp Bool) (ε : ℝ≥0)
    (h : ∀ a ∈ μ.support,
      Game.advantage
        (ProbComp.eval (do let x ← m₁; k₁ a x))
        (ProbComp.eval (do let y ← m₂; k₂ a y)) ≤ ε) :
    Game.advantage
      (μ.bind fun a => ProbComp.eval (do let x ← m₁; k₁ a x))
      (μ.bind fun a => ProbComp.eval (do let y ← m₂; k₂ a y)) ≤ ε := by
  peel_binds
  exact h a a_mem

/-- Reducible identity alias for testing `dsimp` inside `game_trans ... using [by ...]`. -/
abbrev idGame (g : Game) : Game := g

/-- Coverage for `using [by ...]` hop proofs that need the expected type or the reversed
orientation.
These are not regression tests for review finding 2: they also pass without its logged-error/
`sorryAx` probe rollback, and no input that reaches that path has been found. -/
example (g₀ g₁ g₂ : Game) (ε₀ ε₁ : ℝ≥0)
    (h_rev : Game.advantage g₁ g₀ ≤ ε₀)
    (h₁ : Game.advantage g₁ g₂ ≤ ε₁) :
    Game.advantage g₀ g₂ ≤ ε₀ + ε₁ := by
  game_trans [idGame g₁] using [by dsimp only [idGame]; exact h_rev, h₁]

example (g₀ g₀' g₁ g₂ : Game) (ε₀ ε₁ : ℝ≥0)
    (heq : g₀ = g₀')
    (h_rev : Game.advantage g₁ g₀' ≤ ε₀)
    (h₁ : Game.advantage g₁ g₂ ≤ ε₁) :
    Game.advantage g₀ g₂ ≤ ε₀ + ε₁ := by
  game_trans [g₁] using [by subst heq; exact h_rev, h₁]

/-- Regression (3): `normalizeBindHead` pushes `(q.map g).bind f` via `PMF.bind_map` and
`ProbComp.eval (g <$> m >>= k)` via `ProbComp.eval_map` + `PMF.bind_map`. -/
example (q : PMF ℕ) (g : ℕ → Bool) (f₁ f₂ : Bool → Game) (ε : ℝ≥0)
    (h : ∀ x ∈ q.support, Game.advantage (f₁ (g x)) (f₂ (g x)) ≤ ε) :
    Game.advantage ((q.map g).bind f₁) ((q.map g).bind f₂) ≤ ε := by
  peel_binds x
  exact h x x_mem

example (m : ProbComp ℕ) (g : ℕ → Bool) (k₁ k₂ : Bool → ProbComp Bool) (ε : ℝ≥0)
    (h : ∀ x ∈ (ProbComp.eval m).support,
      Game.advantage (ProbComp.eval (k₁ (g x))) (ProbComp.eval (k₂ (g x))) ≤ ε) :
    Game.advantage
      (ProbComp.eval (do let y ← g <$> m; k₁ y))
      (ProbComp.eval (do let y ← g <$> m; k₂ y)) ≤ ε := by
  peel_binds x
  exact h x x_mem

/-- Regression (4): `peel_binds` head-beta-reduces inline `Encryption.advantage (fun b n => do ...)`
lambdas under `ProbComp.eval`. -/
example (m : ℕ → ProbComp ℕ) (k : Bool → ℕ → ℕ → ProbComp Bool) (n : ℕ) (ε : ℝ≥0)
    (h : ∀ x ∈ (ProbComp.eval (m n)).support,
      Game.advantage (ProbComp.eval (k false n x)) (ProbComp.eval (k true n x)) ≤ ε) :
    Encryption.advantage (fun b n => do let x ← m n; k b n x) n ≤ ε := by
  peel_binds x
  exact h x x_mem

/-- Binder-name preference nit: when LHS continuation is a variable `f` and RHS has an explicit
lambda `fun namedDraw => ...`, binderless `peel_binds` adopts `namedDraw`. -/
example (μ : PMF ℕ) (f g : ℕ → Game) (ε : ℝ≥0)
    (h : ∀ namedDraw ∈ μ.support, Game.advantage (f namedDraw) (g namedDraw) ≤ ε) :
    Game.advantage (μ.bind f) (μ.bind fun namedDraw => g namedDraw) ≤ ε := by
  peel_binds
  exact h namedDraw namedDraw_mem

/-- `peel_binds _` names the draw `x` and leaves its support witness inaccessible. -/
example (μ : PMF ℕ) (f g : ℕ → Game) (ε : ℝ≥0)
    (h : ∀ y ∈ μ.support, Game.advantage (f y) (g y) ≤ ε) :
    Game.advantage (μ.bind f) (μ.bind g) ≤ ε := by
  peel_binds _
  exact h x ‹_›

/-! ### Negative tests and diagnostics -/

-- `game_trans` reports `using` count mismatches clearly.
/--
error: game_trans: 1 intermediate item(s) produce 2 hop(s), but `using` supplied 1 term(s)
-/
#guard_msgs in
example (g₀ g₁ : Game) (h : Game.advantage g₀ g₁ ≤ 1) : Game.advantage g₀ g₁ ≤ 1 := by
  game_trans [g₀] using [h]

-- The only stage that could align with the right-hand `d₂ 0` is `d₂ a`, whose distribution depends
-- on the outer binder `a`, so no independent swap exists. Dependence makes the swap ineligible
-- before it is attempted, so the user-facing message is the generic alignment error.
/--
error: peel_binds: leading stages do not match and cannot be aligned by a single independent swap
  Game.advantage (d₁.bind fun a => (d₂ a).bind fun b => f a b) ((d₂ 0).bind g) ≤ 1
-/
#guard_msgs in
example (d₁ : PMF ℕ) (d₂ : ℕ → PMF Bool) (f : ℕ → Bool → Game) (g : Bool → Game) :
    Game.advantage (d₁.bind fun a => (d₂ a).bind fun b => f a b) ((d₂ 0).bind g) ≤ 1 := by
  peel_binds

-- Leading distributions differ and neither side has a matching independent second stage.
/--
error: peel_binds: leading stages do not match and cannot be aligned by a single independent swap
  Game.advantage (d₁.bind fun a => f a true) (d₃.bind fun b => g b 0) ≤ 1
-/
#guard_msgs in
example (d₁ : PMF ℕ) (d₃ : PMF Bool) (f : ℕ → Bool → Game) (g : Bool → ℕ → Game) :
    Game.advantage (d₁.bind fun a => f a true) (d₃.bind fun b => g b 0) ≤ 1 := by
  peel_binds

-- The named form reports which requested stage could not be peeled.
/--
error: peel_binds: could not peel stage `a`; leading distributions do not match and cannot be
aligned by a single independent swap
  Game.advantage (d₁.bind fun a => f a true) (d₃.bind fun b => g b 0) ≤ 1
-/
#guard_msgs in
example (d₁ : PMF ℕ) (d₃ : PMF Bool) (f : ℕ → Bool → Game) (g : Bool → ℕ → Game) :
    Game.advantage (d₁.bind fun a => f a true) (d₃.bind fun b => g b 0) ≤ 1 := by
  peel_binds a

-- `peel_binds` rejects goals outside its supported shapes.
/--
error: peel_binds: expected a `Game.advantage`, `Encryption.advantage`, `CloseTo`, or `PMF`
equality goal
  1 ≤ 2
-/
#guard_msgs in
example : (1 : ℕ) ≤ 2 := by
  peel_binds

-- A `using` term with the wrong hop endpoints is reported at that term.
/--
error: game_trans: hop proof has type
  g₀.advantage g₂ ≤ 1
which does not match expected hop (up to symmetry or equality)
  g₀.advantage g₁ ≤ ?ε_0
-/
#guard_msgs in
example (g₀ g₁ g₂ : Game) (h : Game.advantage g₀ g₂ ≤ 1) : Game.advantage g₀ g₂ ≤ 1 := by
  game_trans [g₁] using [h, h]

-- Bare `game_trans` on an already-normalized `Game.advantage` goal needs intermediates.
/--
error: game_trans: supply at least one intermediate game/distribution (e.g. `game_trans [g₁]`)
or `using [h]`
-/
#guard_msgs in
example (g₀ g₁ : Game) : Game.advantage g₀ g₁ ≤ 1 := by
  game_trans

-- `game_trans` rejects goals outside its supported shapes.
/--
error: game_trans: expected a `Game.advantage`, `Encryption.advantage`,
`Game.succProbability ≤ Game.succProbability + B`, or `CloseTo` goal
  n ≤ n
-/
#guard_msgs in
example (n : ℕ) : n ≤ n := by
  game_trans [n]

end CslibFrontierTests.GameHopTactic
end
