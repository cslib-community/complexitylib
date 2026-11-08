/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.Scheme
public import Complexity.Crypto.Game
import Complexity.Probability.PMF.Bind

/-!
# Security games for garbling schemes

The security notions of [BellareHoangRogaway2012], Sections 3.4 to 3.6, for a garbling scheme
`G` with side information `Φ`. Each game has one adversary who makes a single query and keeps a
state between its two stages, as in the single-query games of the paper; the output `⊥` of a game
on an invalid query is `none`.

* Privacy (`prv`) asks that `(F, X, d)` reveal nothing about `(f, x)` beyond `Φ(f)` and
  `ev(f, x)`. In the indistinguishability game `PrvInd` the adversary chooses `(f₀, f₁, x₀, x₁)`
  with `Φ(f₀) = Φ(f₁)` and `ev(f₀, x₀) = ev(f₁, x₁)` and must tell which pair was garbled; in the
  simulation game `PrvSim` it must tell the real `(F, X, d)` from the output of a simulator that
  only sees `ev(f, x)` and `Φ(f)`.
* Obliviousness (`obv`) withholds the decoding information `d`, so the garbled evaluation reveals
  nothing about `(f, x)` beyond `Φ(f)`; the games `ObvInd` and `ObvSim` drop the condition on
  `ev` and the simulator no longer receives `ev(f, x)`.
* Authenticity (`aut`) asks that no adversary given `(F, X)` can produce a garbled output other
  than `Ev(F, X)` that decodes successfully.

Advantages are the `Game.advantage` between the two experiments of a game, or the success
probability for authenticity. The indistinguishability games are also available with a hidden
uniform bit (`prvIndBitGame`); the advantage is twice the bias of that game, which is the
formulation `2 Pr[PrvInd = 1] − 1` of the paper up to sign. The relations between the
indistinguishability and simulation notions are in
`Complexity.Crypto.Primitives.Garbling.Foundations`.

## Main definitions

* `Cslib.Crypto.Garbling.PrvIndAdversary`, `Cslib.Crypto.Garbling.prvIndExp`,
  `Cslib.Crypto.Garbling.prvIndAdvantage`: the game `PrvInd` and its advantage.
* `Cslib.Crypto.Garbling.PrvSimAdversary`, `Cslib.Crypto.Garbling.PrvSimulator`,
  `Cslib.Crypto.Garbling.prvSimExp`, `Cslib.Crypto.Garbling.prvSimAdvantage`: the game `PrvSim`.
* `Cslib.Crypto.Garbling.obvIndExp`, `Cslib.Crypto.Garbling.obvIndAdvantage`,
  `Cslib.Crypto.Garbling.obvSimExp`, `Cslib.Crypto.Garbling.obvSimAdvantage`: the games
  `ObvInd` and `ObvSim`.
* `Cslib.Crypto.Garbling.autGame`, `Cslib.Crypto.Garbling.autAdvantage`: the game `Aut`.

## Main results

* `Cslib.Crypto.Game.succProbability_uniform_bool_beq`: the success probability of a hidden-bit
  game that outputs whether the guess equals the bit.
* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_two_mul_guessingAdvantage`: the `prv.ind` advantage
  is twice the bias of the hidden-bit game.
* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_zero_of_invalid`: an adversary whose queries are
  always invalid has no advantage.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

namespace Game

open Probability in
/-- For any Boolean-indexed family of games `g : Bool → Game`, sampling a uniform hidden bit
`bit ← PMF.uniformOfFintype Bool` and outputting `guess == bit` for `guess ← g bit` succeeds with
probability `(1 - succProbability (g false) + succProbability (g true)) / 2`. This is
`succProbability_uniform_bool_xor` with the complementary output convention. -/
theorem succProbability_uniform_bool_beq (g : Bool → Game) :
    (succProbability
      ((PMF.uniformOfFintype Bool).bind fun bit => (g bit).map (fun guess => guess == bit)) : ℝ) =
      (1 - (succProbability (g false) : ℝ) + succProbability (g true)) / 2 := by
  have hmap :
      ((PMF.uniformOfFintype Bool).bind fun bit => (g bit).map (fun guess => guess == bit)) =
        ((PMF.uniformOfFintype Bool).bind fun bit =>
          (g bit).map (fun guess => guess ^^ bit)).map Bool.not := by
    rw [PMF.map_bind]
    refine congrArg _ (funext fun bit => ?_)
    rw [PMF.map_comp]
    refine congrArg _ (funext fun guess => ?_)
    cases guess <;> cases bit <;> rfl
  rw [hmap, succProbability_not, failProbability_eq, NNReal.coe_sub (succProbability_le_one _),
    NNReal.coe_one, succProbability_uniform_bool_xor]
  ring

end Game

namespace Garbling

variable {Fn Λ σ : Type}

/-! ## Privacy: indistinguishability -/

/-- A `prv.ind` adversary: it chooses a query `(f₀, f₁, x₀, x₁)` and keeps a state, then guesses
the hidden bit from `(F, X, d)`, or from `⊥` when its query was invalid. -/
structure PrvIndAdversary (Fn σ : Type) where
  /-- Choose the query and save a state. -/
  choose : ℕ → ProbComp ((Fn × Fn × List Bool × List Bool) × σ)
  /-- Guess the hidden bit from the saved state and the answer. -/
  guess : ℕ → σ → Option (List Bool × List Bool × List Bool) → ProbComp Bool

/-- Validity of a `prv.ind` query: `Φ(f₀) = Φ(f₁)`, both inputs have `f₀.n` bits and
`ev(f₀, x₀) = ev(f₁, x₁)`. -/
def prvIndValid (G : Scheme Fn) (Φ : SideInfo Fn Λ) (f₀ f₁ : Fn) (x₀ x₁ : List Bool) : Prop :=
  Φ.phi f₀ = Φ.phi f₁ ∧ x₀.length = G.inLen f₀ ∧ x₁.length = G.inLen f₀ ∧
    G.ev f₀ x₀ = G.ev f₁ x₁

instance [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (f₀ f₁ : Fn) (x₀ x₁ : List Bool) :
    Decidable (prvIndValid G Φ f₀ f₁ x₀ x₁) := by
  unfold prvIndValid
  infer_instance

/-- Experiment `b` of the game `PrvInd`, [BellareHoangRogaway2012], Section 3.4: on a valid
query garble `f_b`, encode `x_b` and hand `(F, X, d)` to the adversary; otherwise hand it `⊥`. -/
noncomputable def prvIndExp [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (b : Bool)
    (A : PrvIndAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let ((f₀, f₁, x₀, x₁), st) ← A.choose k
  if prvIndValid G Φ f₀ f₁ x₀ x₁ then
    let g ← G.garble k (if b then f₁ else f₀)
    A.guess k st (some (g.fn, G.encode g.encInfo (if b then x₁ else x₀), g.decInfo))
  else
    A.guess k st none

/-- The `prv.ind` advantage of an adversary: the distinguishing advantage between the two
experiments of `PrvInd`. -/
noncomputable def prvIndAdvantage [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : PrvIndAdversary Fn σ) (k : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (prvIndExp G Φ false A k)) (ProbComp.eval (prvIndExp G Φ true A k))

/-- The game `PrvInd` with a hidden uniform bit: it outputs whether the adversary guessed the
bit. -/
noncomputable def prvIndBitGame [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : PrvIndAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let b ← ProbComp.uniform Bool
  let b' ← prvIndExp G Φ b A k
  return b' == b

/-! ## Privacy: simulation -/

/-- A `prv.sim` adversary: it chooses a query `(f, x)` and keeps a state, then guesses whether
`(F, X, d)` is real or simulated, or guesses from `⊥` when its query was invalid. -/
structure PrvSimAdversary (Fn σ : Type) where
  /-- Choose the query and save a state. -/
  choose : ℕ → ProbComp ((Fn × List Bool) × σ)
  /-- Guess whether the answer is real from the saved state and the answer. -/
  guess : ℕ → σ → Option (List Bool × List Bool × List Bool) → ProbComp Bool

/-- A `prv.sim` simulator `S(1^k, y, φ)`: it produces `(F, X, d)` from the output `y = ev(f, x)`
and the side information `φ = Φ(f)`. -/
abbrev PrvSimulator (Λ : Type) := ℕ → List Bool → Λ → ProbComp (List Bool × List Bool × List Bool)

/-- Experiment `b` of the game `PrvSim`, [BellareHoangRogaway2012], Section 3.4: when `x` has
`f.n` bits, `b = true` hands the adversary the real `(F, X, d)` and `b = false` the output of the
simulator on `(ev(f, x), Φ(f))`; otherwise it hands the adversary `⊥`. -/
noncomputable def prvSimExp (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : PrvSimulator Λ) (b : Bool)
    (B : PrvSimAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let ((f, x), st) ← B.choose k
  if x.length = G.inLen f then
    let answer ←
      if b then do
        let g ← G.garble k f
        pure (g.fn, G.encode g.encInfo x, g.decInfo)
      else S k (G.ev f x) (Φ.phi f)
    B.guess k st (some answer)
  else
    B.guess k st none

/-- The `prv.sim` advantage of an adversary against a simulator: the distinguishing advantage
between the two experiments of `PrvSim`. -/
noncomputable def prvSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : PrvSimulator Λ)
    (B : PrvSimAdversary Fn σ) (k : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (prvSimExp G Φ S false B k))
    (ProbComp.eval (prvSimExp G Φ S true B k))

/-! ## Obliviousness: indistinguishability -/

/-- An `obv.ind` adversary: it chooses a query `(f₀, f₁, x₀, x₁)` and keeps a state, then
guesses the hidden bit from `(F, X)`, or from `⊥` when its query was invalid. -/
structure ObvIndAdversary (Fn σ : Type) where
  /-- Choose the query and save a state. -/
  choose : ℕ → ProbComp ((Fn × Fn × List Bool × List Bool) × σ)
  /-- Guess the hidden bit from the saved state and the answer. -/
  guess : ℕ → σ → Option (List Bool × List Bool) → ProbComp Bool

/-- Validity of an `obv.ind` query: `Φ(f₀) = Φ(f₁)` and both inputs have `f₀.n` bits. The
outputs `ev(f₀, x₀)` and `ev(f₁, x₁)` need not agree. -/
def obvIndValid (G : Scheme Fn) (Φ : SideInfo Fn Λ) (f₀ f₁ : Fn) (x₀ x₁ : List Bool) : Prop :=
  Φ.phi f₀ = Φ.phi f₁ ∧ x₀.length = G.inLen f₀ ∧ x₁.length = G.inLen f₀

instance [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (f₀ f₁ : Fn) (x₀ x₁ : List Bool) :
    Decidable (obvIndValid G Φ f₀ f₁ x₀ x₁) := by
  unfold obvIndValid
  infer_instance

/-- Experiment `b` of the game `ObvInd`, [BellareHoangRogaway2012], Section 3.5: on a valid
query garble `f_b`, encode `x_b` and hand `(F, X)` to the adversary, withholding `d`; otherwise
hand it `⊥`. -/
noncomputable def obvIndExp [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (b : Bool)
    (A : ObvIndAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let ((f₀, f₁, x₀, x₁), st) ← A.choose k
  if obvIndValid G Φ f₀ f₁ x₀ x₁ then
    let g ← G.garble k (if b then f₁ else f₀)
    A.guess k st (some (g.fn, G.encode g.encInfo (if b then x₁ else x₀)))
  else
    A.guess k st none

/-- The `obv.ind` advantage of an adversary: the distinguishing advantage between the two
experiments of `ObvInd`. -/
noncomputable def obvIndAdvantage [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : ObvIndAdversary Fn σ) (k : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (obvIndExp G Φ false A k)) (ProbComp.eval (obvIndExp G Φ true A k))

/-! ## Obliviousness: simulation -/

/-- An `obv.sim` adversary: it chooses a query `(f, x)` and keeps a state, then guesses whether
`(F, X)` is real or simulated, or guesses from `⊥` when its query was invalid. -/
structure ObvSimAdversary (Fn σ : Type) where
  /-- Choose the query and save a state. -/
  choose : ℕ → ProbComp ((Fn × List Bool) × σ)
  /-- Guess whether the answer is real from the saved state and the answer. -/
  guess : ℕ → σ → Option (List Bool × List Bool) → ProbComp Bool

/-- An `obv.sim` simulator `S(1^k, φ)`: it produces `(F, X)` from the side information
`φ = Φ(f)` alone. -/
abbrev ObvSimulator (Λ : Type) := ℕ → Λ → ProbComp (List Bool × List Bool)

/-- Experiment `b` of the game `ObvSim`, [BellareHoangRogaway2012], Section 3.5: when `x` has
`f.n` bits, `b = true` hands the adversary the real `(F, X)` and `b = false` the output of the
simulator on `Φ(f)`; otherwise it hands the adversary `⊥`. -/
noncomputable def obvSimExp (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : ObvSimulator Λ) (b : Bool)
    (B : ObvSimAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let ((f, x), st) ← B.choose k
  if x.length = G.inLen f then
    let answer ←
      if b then do
        let g ← G.garble k f
        pure (g.fn, G.encode g.encInfo x)
      else S k (Φ.phi f)
    B.guess k st (some answer)
  else
    B.guess k st none

/-- The `obv.sim` advantage of an adversary against a simulator: the distinguishing advantage
between the two experiments of `ObvSim`. -/
noncomputable def obvSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : ObvSimulator Λ)
    (B : ObvSimAdversary Fn σ) (k : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (obvSimExp G Φ S false B k))
    (ProbComp.eval (obvSimExp G Φ S true B k))

/-! ## Authenticity -/

/-- An `aut` adversary: it chooses a query `(f, x)` and keeps a state, then forges a garbled
output from `(F, X)`. -/
structure AutAdversary (Fn σ : Type) where
  /-- Choose the query and save a state. -/
  choose : ℕ → ProbComp ((Fn × List Bool) × σ)
  /-- Forge a garbled output from the saved state and `(F, X)`. -/
  forge : ℕ → σ → List Bool × List Bool → ProbComp (List Bool)

/-- The game `Aut`, [BellareHoangRogaway2012], Section 3.6: when `x` has `f.n` bits, the
adversary receives `(F, X)` and wins when its forgery differs from `Ev(F, X)` and decodes
successfully; otherwise the game outputs `false`. -/
noncomputable def autGame (G : Scheme Fn) (A : AutAdversary Fn σ) (k : ℕ) : ProbComp Bool := do
  let ((f, x), st) ← A.choose k
  if x.length = G.inLen f then
    let g ← G.garble k f
    let encoded := G.encode g.encInfo x
    let forged ← A.forge k st (g.fn, encoded)
    return (forged != G.evalGarbled g.fn encoded) && (G.decode g.decInfo forged).isSome
  else
    return false

/-- The `aut` advantage of an adversary: its probability of winning `Aut`. -/
noncomputable def autAdvantage (G : Scheme Fn) (A : AutAdversary Fn σ) (k : ℕ) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (autGame G A k))

/-! ## Elementary bounds -/

section Bounds

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ)

theorem prvIndAdvantage_le_one [DecidableEq Λ] (A : PrvIndAdversary Fn σ) (k : ℕ) :
    prvIndAdvantage G Φ A k ≤ 1 :=
  Game.advantage_le_one _ _

theorem prvSimAdvantage_le_one (S : PrvSimulator Λ) (B : PrvSimAdversary Fn σ) (k : ℕ) :
    prvSimAdvantage G Φ S B k ≤ 1 :=
  Game.advantage_le_one _ _

theorem obvIndAdvantage_le_one [DecidableEq Λ] (A : ObvIndAdversary Fn σ) (k : ℕ) :
    obvIndAdvantage G Φ A k ≤ 1 :=
  Game.advantage_le_one _ _

theorem obvSimAdvantage_le_one (S : ObvSimulator Λ) (B : ObvSimAdversary Fn σ) (k : ℕ) :
    obvSimAdvantage G Φ S B k ≤ 1 :=
  Game.advantage_le_one _ _

theorem autAdvantage_le_one (A : AutAdversary Fn σ) (k : ℕ) : autAdvantage G A k ≤ 1 :=
  Game.succProbability_le_one _

open Probability in
/-- The `prv.ind` advantage is twice the bias of the hidden-bit game, the absolute value of
`2 Pr[PrvInd = 1] − 1` in [BellareHoangRogaway2012], Section 3.4. -/
theorem prvIndAdvantage_eq_two_mul_guessingAdvantage [DecidableEq Λ] (A : PrvIndAdversary Fn σ)
    (k : ℕ) :
    prvIndAdvantage G Φ A k =
      2 * Game.guessingAdvantage (ProbComp.eval (prvIndBitGame G Φ A k)) := by
  have hbit : ProbComp.eval (prvIndBitGame G Φ A k) =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (ProbComp.eval (prvIndExp G Φ bit A k)).map (fun guess => guess == bit) := by
    simp only [prvIndBitGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
    rfl
  have key : ∀ a b : ℝ, |a - b| = 2 * |(1 - a + b) / 2 - 1 / 2| := fun a b => by
    rw [show (1 - a + b) / 2 - 1 / 2 = (b - a) / 2 by ring, abs_div, Nat.abs_ofNat, abs_sub_comm]
    ring
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_guessingAdvantage, hbit,
    Game.succProbability_uniform_bool_beq, prvIndAdvantage, Game.coe_advantage]
  exact key _ _

/-- An adversary whose query is never valid has `prv.ind` advantage `0`: both experiments hand
it `⊥`. -/
theorem prvIndAdvantage_eq_zero_of_invalid [DecidableEq Λ] (A : PrvIndAdversary Fn σ) (k : ℕ)
    (h : ∀ (f₀ f₁ : Fn) (x₀ x₁ : List Bool) (st : σ),
      ((f₀, f₁, x₀, x₁), st) ∈ (ProbComp.eval (A.choose k)).support →
        ¬ prvIndValid G Φ f₀ f₁ x₀ x₁) :
    prvIndAdvantage G Φ A k = 0 := by
  have hexp : ∀ b, ProbComp.eval (prvIndExp G Φ b A k) =
      (ProbComp.eval (A.choose k)).bind fun q => ProbComp.eval (A.guess k q.2 none) := by
    intro b
    simp only [prvIndExp, ProbComp.eval_bind]
    refine Probability.PMF.bind_congr_on_support _ _ _ ?_
    rintro ⟨⟨f₀, f₁, x₀, x₁⟩, st⟩ hq
    simp only [h f₀ f₁ x₀ x₁ st hq, ↓reduceIte]
  rw [prvIndAdvantage, hexp false, hexp true, Game.advantage_self]

end Bounds

end Garbling

end Cslib.Crypto
