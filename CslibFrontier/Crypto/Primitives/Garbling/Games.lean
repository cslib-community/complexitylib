/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Scheme
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Probability.PMF.Bind

/-!
# Security games for garbling schemes

The security notions of [BellareHoangRogaway2012], Sections 3.4 to 3.6, for a garbling scheme
`G` with side information `Φ`. Each game has one two-stage adversary (`Cslib.Crypto.TwoStage`)
who makes a single query and keeps a state between its stages, as in the single-query games of
the paper. Each experiment is a program (`Cslib.Crypto.Experiment`) at a fixed security
parameter `k`. On an invalid query the adversary receives `⊥`, which is `none`.

* Privacy (`prv`) asks that the view `(F, X, d)` reveal nothing about the query `(f, x)` beyond
  `Φ(f)` and `ev(f, x)`. In the indistinguishability game `PrvInd` the adversary chooses a pair of
  queries `(f₀, x₀)` and `(f₁, x₁)` with `Φ(f₀) = Φ(f₁)` and `ev(f₀, x₀) = ev(f₁, x₁)` and must
  tell which one was garbled. In the simulation game `PrvSim` it must tell the real view from the
  output of a simulator that sees only `ev(f, x)` and `Φ(f)`.
* Obliviousness (`obv`) withholds the decoding information `d`, so the view `(F, X)` reveals
  nothing about `(f, x)` beyond `Φ(f)`. The games `ObvInd` and `ObvSim` drop the condition on
  `ev`, and the simulator no longer receives `ev(f, x)`.
* Authenticity (`aut`) asks that no adversary given `(F, X)` can produce a garbled output other
  than `Ev(F, X)` that decodes successfully.

Advantages are the `Experiment.advantage` between the two experiments of a game, or the success
probability for authenticity. The bit-guessing form `Experiment.guessBit` of an
indistinguishability game draws a uniform hidden bit; the advantage is twice its bias, which is
the formulation `2 Pr[PrvInd = 1] − 1` of the paper up to sign. The relations between the
indistinguishability and simulation notions are in
`CslibFrontier.Crypto.Primitives.Garbling.Foundations`.

## Main definitions

* `Cslib.Crypto.Garbling.PrvView`, `Cslib.Crypto.Garbling.ObvView`: the views `(F, X, d)` and
  `(F, X)` handed to the adversary, and `Cslib.Crypto.Garbling.Scheme.prvView`,
  `Cslib.Crypto.Garbling.Scheme.obvView`, the real views of a query.
* `Cslib.Crypto.Garbling.PrvIndAdversary`, `Cslib.Crypto.Garbling.prvIndExperiment`,
  `Cslib.Crypto.Garbling.prvIndAdvantage`: the game `PrvInd` and its advantage.
* `Cslib.Crypto.Garbling.PrvSimAdversary`, `Cslib.Crypto.Garbling.PrvSimulator`,
  `Cslib.Crypto.Garbling.prvSimExperiment`, `Cslib.Crypto.Garbling.prvSimAdvantage`: the game
  `PrvSim`.
* `Cslib.Crypto.Garbling.obvIndExperiment`, `Cslib.Crypto.Garbling.obvIndAdvantage`,
  `Cslib.Crypto.Garbling.obvSimExperiment`, `Cslib.Crypto.Garbling.obvSimAdvantage`: the games
  `ObvInd` and `ObvSim`.
* `Cslib.Crypto.Garbling.autExperiment`, `Cslib.Crypto.Garbling.autAdvantage`: the game `Aut`.

## Main results

* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_two_mul_guessingAdvantage`: the `prv.ind` advantage
  is twice the bias of the bit-guessing experiment.
* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_zero_of_invalid`: an adversary whose queries are
  always invalid has no advantage.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open scoped NNReal

variable {Fn Λ σ : Type}

/-! ## Views -/

/-- The view `(F, X, d)` of a privacy adversary: a garbled function, a garbled input and decoding
information. -/
structure PrvView where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The garbled input `X`. -/
  input : List Bool
  /-- The decoding information `d`. -/
  decInfo : List Bool
  deriving DecidableEq

/-- The view `(F, X)` of an obliviousness or authenticity adversary: a garbled function and a
garbled input. -/
structure ObvView where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The garbled input `X`. -/
  input : List Bool
  deriving DecidableEq

namespace Scheme

variable (G : Scheme Fn)

/-- The real privacy view of the query `q` at security parameter `k`: garble `q.fn` to
`(F, e, d)` and return `(F, En(e, q.input), d)`. -/
noncomputable def prvView (k : ℕ) (q : Query Fn) : ProbComp PrvView := do
  let g ← G.garble k q.fn
  return ⟨g.fn, G.encode g.encInfo q.input, g.decInfo⟩

/-- The real obliviousness view of the query `q` at security parameter `k`: garble `q.fn` to
`(F, e, d)` and return `(F, En(e, q.input))`. -/
noncomputable def obvView (k : ℕ) (q : Query Fn) : ProbComp ObvView := do
  let g ← G.garble k q.fn
  return ⟨g.fn, G.encode g.encInfo q.input⟩

end Scheme

/-! ## Privacy: indistinguishability -/

/-- A `prv.ind` adversary: it chooses a pair of queries and keeps a state, then guesses the hidden
bit from the view `(F, X, d)`, or from `⊥` when its pair was invalid. -/
abbrev PrvIndAdversary (Fn σ : Type) :=
  TwoStage Unit (MessagePair (Query Fn)) (Option PrvView) Bool σ

/-- Validity of a `prv.ind` pair `(f₀, x₀)`, `(f₁, x₁)`: `Φ(f₀) = Φ(f₁)`, both inputs have `f₀.n`
bits and `ev(f₀, x₀) = ev(f₁, x₁)`. -/
def prvIndValid (G : Scheme Fn) (Φ : SideInfo Fn Λ) (pair : MessagePair (Query Fn)) : Prop :=
  Φ.phi pair.msg₀.fn = Φ.phi pair.msg₁.fn ∧ pair.msg₀.input.length = G.inLen pair.msg₀.fn ∧
    pair.msg₁.input.length = G.inLen pair.msg₀.fn ∧
    G.ev pair.msg₀.fn pair.msg₀.input = G.ev pair.msg₁.fn pair.msg₁.input

instance [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (pair : MessagePair (Query Fn)) :
    Decidable (prvIndValid G Φ pair) := by
  unfold prvIndValid
  infer_instance

/-- Experiment `b` of the game `PrvInd`, [BellareHoangRogaway2012], Section 3.4: on a valid pair,
hand the adversary the real view of the query selected by `b`; otherwise hand it `⊥`. -/
noncomputable def prvIndExperiment [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (A : PrvIndAdversary Fn σ) (b : Bool) : Experiment := do
  let (pair, st) ← A.choose ()
  if prvIndValid G Φ pair then
    let view ← G.prvView k (pair.select b)
    A.guess st (some view)
  else
    A.guess st none

/-- The `prv.ind` advantage of an adversary: the distinguishing advantage between the two
experiments of `PrvInd`. -/
noncomputable def prvIndAdvantage [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (A : PrvIndAdversary Fn σ) : ℝ≥0 :=
  Experiment.advantage (prvIndExperiment G Φ k A false) (prvIndExperiment G Φ k A true)

/-! ## Privacy: simulation -/

/-- A `prv.sim` adversary: it chooses a query and keeps a state, then guesses whether the view
`(F, X, d)` is real or simulated, or guesses from `⊥` when its query was invalid. -/
abbrev PrvSimAdversary (Fn σ : Type) := TwoStage Unit (Query Fn) (Option PrvView) Bool σ

/-- A `prv.sim` simulator `S(1^k, y, φ)` at a fixed security parameter: it produces a view
`(F, X, d)` from the output `y = ev(f, x)` and the side information `φ = Φ(f)`. -/
abbrev PrvSimulator (Λ : Type) := List Bool → Λ → ProbComp PrvView

/-- Experiment `b` of the game `PrvSim`, [BellareHoangRogaway2012], Section 3.4: when `x` has
`f.n` bits, `b = true` hands the adversary the real view of `(f, x)` and `b = false` the output of
the simulator on `(ev(f, x), Φ(f))`; otherwise it hands the adversary `⊥`. -/
noncomputable def prvSimExperiment (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ) (S : PrvSimulator Λ)
    (B : PrvSimAdversary Fn σ) (b : Bool) : Experiment := do
  let (q, st) ← B.choose ()
  if q.input.length = G.inLen q.fn then
    let view ← if b then G.prvView k q else S (G.ev q.fn q.input) (Φ.phi q.fn)
    B.guess st (some view)
  else
    B.guess st none

/-- The `prv.sim` advantage of an adversary against a simulator: the distinguishing advantage
between the two experiments of `PrvSim`. -/
noncomputable def prvSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ) (S : PrvSimulator Λ)
    (B : PrvSimAdversary Fn σ) : ℝ≥0 :=
  Experiment.advantage (prvSimExperiment G Φ k S B false) (prvSimExperiment G Φ k S B true)

/-! ## Obliviousness: indistinguishability -/

/-- An `obv.ind` adversary: it chooses a pair of queries and keeps a state, then guesses the
hidden bit from the view `(F, X)`, or from `⊥` when its pair was invalid. -/
abbrev ObvIndAdversary (Fn σ : Type) :=
  TwoStage Unit (MessagePair (Query Fn)) (Option ObvView) Bool σ

/-- Validity of an `obv.ind` pair `(f₀, x₀)`, `(f₁, x₁)`: `Φ(f₀) = Φ(f₁)` and both inputs have
`f₀.n` bits. The outputs `ev(f₀, x₀)` and `ev(f₁, x₁)` need not agree. -/
def obvIndValid (G : Scheme Fn) (Φ : SideInfo Fn Λ) (pair : MessagePair (Query Fn)) : Prop :=
  Φ.phi pair.msg₀.fn = Φ.phi pair.msg₁.fn ∧ pair.msg₀.input.length = G.inLen pair.msg₀.fn ∧
    pair.msg₁.input.length = G.inLen pair.msg₀.fn

instance [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (pair : MessagePair (Query Fn)) :
    Decidable (obvIndValid G Φ pair) := by
  unfold obvIndValid
  infer_instance

/-- Experiment `b` of the game `ObvInd`, [BellareHoangRogaway2012], Section 3.5: on a valid pair,
hand the adversary the real view `(F, X)` of the query selected by `b`, withholding `d`;
otherwise hand it `⊥`. -/
noncomputable def obvIndExperiment [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (A : ObvIndAdversary Fn σ) (b : Bool) : Experiment := do
  let (pair, st) ← A.choose ()
  if obvIndValid G Φ pair then
    let view ← G.obvView k (pair.select b)
    A.guess st (some view)
  else
    A.guess st none

/-- The `obv.ind` advantage of an adversary: the distinguishing advantage between the two
experiments of `ObvInd`. -/
noncomputable def obvIndAdvantage [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (A : ObvIndAdversary Fn σ) : ℝ≥0 :=
  Experiment.advantage (obvIndExperiment G Φ k A false) (obvIndExperiment G Φ k A true)

/-! ## Obliviousness: simulation -/

/-- An `obv.sim` adversary: it chooses a query and keeps a state, then guesses whether the view
`(F, X)` is real or simulated, or guesses from `⊥` when its query was invalid. -/
abbrev ObvSimAdversary (Fn σ : Type) := TwoStage Unit (Query Fn) (Option ObvView) Bool σ

/-- An `obv.sim` simulator `S(1^k, φ)` at a fixed security parameter: it produces a view `(F, X)`
from the side information `φ = Φ(f)` alone. -/
abbrev ObvSimulator (Λ : Type) := Λ → ProbComp ObvView

/-- Experiment `b` of the game `ObvSim`, [BellareHoangRogaway2012], Section 3.5: when `x` has
`f.n` bits, `b = true` hands the adversary the real view `(F, X)` of `(f, x)` and `b = false` the
output of the simulator on `Φ(f)`; otherwise it hands the adversary `⊥`. -/
noncomputable def obvSimExperiment (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ) (S : ObvSimulator Λ)
    (B : ObvSimAdversary Fn σ) (b : Bool) : Experiment := do
  let (q, st) ← B.choose ()
  if q.input.length = G.inLen q.fn then
    let view ← if b then G.obvView k q else S (Φ.phi q.fn)
    B.guess st (some view)
  else
    B.guess st none

/-- The `obv.sim` advantage of an adversary against a simulator: the distinguishing advantage
between the two experiments of `ObvSim`. -/
noncomputable def obvSimAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ) (S : ObvSimulator Λ)
    (B : ObvSimAdversary Fn σ) : ℝ≥0 :=
  Experiment.advantage (obvSimExperiment G Φ k S B false) (obvSimExperiment G Φ k S B true)

/-! ## Authenticity -/

/-- An `aut` adversary: it chooses a query and keeps a state, then forges a garbled output from
the view `(F, X)`. -/
abbrev AutAdversary (Fn σ : Type) := TwoStage Unit (Query Fn) ObvView (List Bool) σ

/-- The game `Aut`, [BellareHoangRogaway2012], Section 3.6: when `x` has `f.n` bits, the
adversary receives `(F, X)` and wins when its forgery differs from `Ev(F, X)` and decodes
successfully; otherwise the game outputs `false`. -/
noncomputable def autExperiment (G : Scheme Fn) (k : ℕ) (A : AutAdversary Fn σ) : Experiment := do
  let (q, st) ← A.choose ()
  if q.input.length = G.inLen q.fn then
    let g ← G.garble k q.fn
    let encoded := G.encode g.encInfo q.input
    let forged ← A.guess st ⟨g.fn, encoded⟩
    return (forged != G.evalGarbled g.fn encoded) && (G.decode g.decInfo forged).isSome
  else
    return false

/-- The `aut` advantage of an adversary: its probability of winning `Aut`. -/
noncomputable def autAdvantage (G : Scheme Fn) (k : ℕ) (A : AutAdversary Fn σ) : ℝ≥0 :=
  Experiment.succProbability (autExperiment G k A)

/-! ## Elementary bounds -/

section Bounds

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)

theorem prvIndAdvantage_le_one [DecidableEq Λ] (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A ≤ 1 :=
  Game.advantage_le_one _ _

theorem prvSimAdvantage_le_one (S : PrvSimulator Λ) (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k S B ≤ 1 :=
  Game.advantage_le_one _ _

theorem obvIndAdvantage_le_one [DecidableEq Λ] (A : ObvIndAdversary Fn σ) :
    obvIndAdvantage G Φ k A ≤ 1 :=
  Game.advantage_le_one _ _

theorem obvSimAdvantage_le_one (S : ObvSimulator Λ) (B : ObvSimAdversary Fn σ) :
    obvSimAdvantage G Φ k S B ≤ 1 :=
  Game.advantage_le_one _ _

theorem autAdvantage_le_one (A : AutAdversary Fn σ) : autAdvantage G k A ≤ 1 :=
  Game.succProbability_le_one _

/-- The `prv.ind` advantage is twice the bias of the bit-guessing experiment, the absolute value
of `2 Pr[PrvInd = 1] − 1` in [BellareHoangRogaway2012], Section 3.4. -/
theorem prvIndAdvantage_eq_two_mul_guessingAdvantage [DecidableEq Λ] (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A =
      2 * Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit (prvIndExperiment G Φ k A))) :=
  Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit _

/-- An adversary whose pair is never valid has `prv.ind` advantage `0`: both experiments hand it
`⊥`. -/
theorem prvIndAdvantage_eq_zero_of_invalid [DecidableEq Λ] (A : PrvIndAdversary Fn σ)
    (h : ∀ pair st, (pair, st) ∈ (ProbComp.eval (A.choose ())).support → ¬ prvIndValid G Φ pair) :
    prvIndAdvantage G Φ k A = 0 := by
  have hexp : ∀ b, ProbComp.eval (prvIndExperiment G Φ k A b) =
      (ProbComp.eval (A.choose ())).bind fun q => ProbComp.eval (A.guess q.2 none) := by
    intro b
    simp only [prvIndExperiment, ProbComp.eval_bind]
    refine Probability.PMF.bind_congr_on_support _ _ _ ?_
    rintro ⟨pair, st⟩ hq
    simp only [h pair st hq, ↓reduceIte]
  rw [prvIndAdvantage, Experiment.advantage, hexp false, hexp true, Game.advantage_self]

end Bounds

end Cslib.Crypto.Garbling
