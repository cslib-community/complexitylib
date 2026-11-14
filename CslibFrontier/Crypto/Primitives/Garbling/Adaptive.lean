/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Foundations

/-!
# Coarse-grained adaptive privacy for garbling schemes

In the selective privacy game `PrvSim` of [BellareHoangRogaway2012], Section 3.4, the adversary
submits the function description `f` and the input `x` together before seeing the garbled circuit.
Bellare, Hoang and Rogaway [BellareHoangRogaway2012b], Section 3.1, Figure 2, introduce the
coarse-grained adaptive privacy game `Prv1`, in which the adversary first queries `Garble(f)` to
obtain the garbled function and decoding information `(F, d)`, and only then adaptively chooses
the input `x` in a second query `Input(x)` to obtain the garbled input `X`.

In the simulated world (`b = false`), a two-stage stateful simulator `Prv1Simulator` first produces
`(F, d)` and a simulator state from `Φ(f)`, and then produces `X` from the saved state and the
output `y = ev(f, x)` once `x` is chosen. The adversary has three stages, choosing `f`, choosing `x`
and guessing, so unlike the selective games it is not a `TwoStage` adversary. As in the selective
games, the experiment `prv1Experiment` and the simulator are at a fixed security parameter `k`.
Every stateful `prv1` simulator `S` induces a selective `prv.sim` simulator `prv1SimulatorToPrv S`
that runs the two simulator stages back to back, and every selective `prv.sim` adversary `B` embeds
into an adaptive `prv1` adversary `prvSimToPrv1 B` that commits to `x` in its first-stage state.
This embedding preserves the experiment distribution on the nose in both worlds
(`eval_prv1Experiment_prvSimToPrv1`), so adaptive `prv1` simulation security implies selective
`prv.sim` security with exact advantage equality (`prvSimAdvantage_prv1SimulatorToPrv_eq`) and
selective `prv.ind` security with a factor of two (`prvIndAdvantage_eq_two_mul_prv1Advantage`).

## Main definitions

* `Cslib.Crypto.Garbling.GarbledFn`: the answer `(F, d)` to the `Garble` query.
* `Cslib.Crypto.Garbling.Prv1Adversary`: a three-stage adaptive privacy adversary.
* `Cslib.Crypto.Garbling.Prv1Simulator`: a two-stage stateful simulator for `Prv1`.
* `Cslib.Crypto.Garbling.prv1Experiment`, `Cslib.Crypto.Garbling.prv1Advantage`: the `Prv1` game
  and its advantage.
* `Cslib.Crypto.Garbling.prv1SimulatorToPrv`, `Cslib.Crypto.Garbling.prvSimToPrv1`: the
  reduction from selective `prv.sim` to adaptive `prv1`.

## Main results

* `Cslib.Crypto.Garbling.prv1Advantage_eq_two_mul_guessingAdvantage`: the `prv1` advantage is
  twice the bias of the bit-guessing experiment `Experiment.guessBit`.
* `Cslib.Crypto.Garbling.eval_prv1Experiment_prvSimToPrv1`,
  `Cslib.Crypto.Garbling.prvSimAdvantage_prv1SimulatorToPrv_eq`: adaptive `prv1` simulation
  security implies selective `prv.sim` security with exact advantage preservation.
* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_two_mul_prv1Advantage`: adaptive `prv1` simulation
  security implies selective `prv.ind` security with a factor of two.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Adaptively Secure Garbling with Applications to
  One-Time Programs and Secure Outsourcing*][BellareHoangRogaway2012b]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Probability
open scoped NNReal

variable {Fn Λ σ τ ρ : Type}

/-! ## The `Prv1` adaptive privacy game -/

/-- The answer `(F, d)` to the `Garble(f)` query of `Prv1`: a garbled function and decoding
information, without the garbled input. -/
structure GarbledFn where
  /-- The garbled function `F`. -/
  fn : List Bool
  /-- The decoding information `d`. -/
  decInfo : List Bool
  deriving DecidableEq

/-- A coarse-grained adaptive privacy (`prv1`) adversary ([BellareHoangRogaway2012b], Section 3.1,
Figure 2): in stage 1 (`Garble`) it chooses a function `f` and saves a state; given `(F, d)`,
in stage 2 (`Input`) it adaptively chooses an input `x` and saves a state; finally it
guesses whether the view is real or simulated from the garbled input `X` (or `none` when `x` has
the wrong length). It has three stages, so it is not a `TwoStage` adversary. -/
structure Prv1Adversary (Fn σ τ : Type) where
  /-- Stage 1 (`Garble`): choose the function `f` and save a stage-1 state. -/
  chooseFn : ProbComp (Fn × σ)
  /-- Stage 2 (`Input`): from `(F, d)`, adaptively choose the input `x` and save a stage-2
  state. -/
  chooseInput : σ → GarbledFn → ProbComp (List Bool × τ)
  /-- Guess whether the experiment is real or simulated from the garbled input `X` (or `⊥`). -/
  guess : τ → Option (List Bool) → ProbComp Bool

/-- A stateful `prv1` simulator at a fixed security parameter ([BellareHoangRogaway2012b],
Section 3.1, Figure 2): in the first stage `garble` produces a simulated `(F, d)` together with a
simulator state from `Φ(f)`; in the second stage `input` produces a simulated garbled input `X` from
the saved simulator state and the output `y = ev(f, x)`. -/
structure Prv1Simulator (Λ ρ : Type) where
  /-- Stage 1 (`S(1^k, φ, 0)`): simulate `(F, d)` from `Φ(f)` and save a state. -/
  garble : Λ → ProbComp (GarbledFn × ρ)
  /-- Stage 2 (`S(y, 1)`): simulate `X` from the saved state and `y = ev(f, x)`. -/
  input : ρ → List Bool → ProbComp (List Bool)

/-- Experiment `b` of the coarse-grained adaptive privacy game `Prv1`
([BellareHoangRogaway2012b], Section 3.1, Figure 2): for `b = true` the adversary interacts with
the real garbling `G.garble k f` and encoding `G.encode g.encInfo x`; for `b = false` it interacts
with the two-stage stateful simulator `S` on `Φ(f)` and `G.ev f x`. An input `x` of length
different from `G.inLen f` is answered with `none` (`⊥`). -/
noncomputable def prv1Experiment (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (A : Prv1Adversary Fn σ τ) (b : Bool) : Experiment := do
  let (f, st) ← A.chooseFn
  if b then
    let g ← G.garble k f
    let (x, st') ← A.chooseInput st ⟨g.fn, g.decInfo⟩
    if x.length = G.inLen f then
      A.guess st' (some (G.encode g.encInfo x))
    else
      A.guess st' none
  else
    let (garbled, stSim) ← S.garble (Φ.phi f)
    let (x, st') ← A.chooseInput st garbled
    if x.length = G.inLen f then
      let X ← S.input stSim (G.ev f x)
      A.guess st' (some X)
    else
      A.guess st' none

/-- The `prv1` advantage of an adaptive adversary `A` against a stateful simulator `S`: the
distinguishing advantage between the simulated (`b = false`) and real (`b = true`) experiments of
`Prv1`. -/
noncomputable def prv1Advantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (A : Prv1Adversary Fn σ τ) : ℝ≥0 :=
  Experiment.advantage (prv1Experiment G Φ k S A false) (prv1Experiment G Φ k S A true)

theorem prv1Advantage_le_one (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ) (S : Prv1Simulator Λ ρ)
    (A : Prv1Adversary Fn σ τ) :
    prv1Advantage G Φ k S A ≤ 1 :=
  Game.advantage_le_one _ _

/-- The `prv1` advantage is twice the bias of the bit-guessing experiment, matching
`2 Pr[Prv1 = 1] - 1` in [BellareHoangRogaway2012b], Section 3.1. -/
theorem prv1Advantage_eq_two_mul_guessingAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (A : Prv1Adversary Fn σ τ) :
    prv1Advantage G Φ k S A =
      2 * Game.guessingAdvantage (ProbComp.eval (Experiment.guessBit (prv1Experiment G Φ k S A))) :=
  Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit _

/-! ## Reduction from selective `prv.sim` and `prv.ind` to adaptive `prv1` -/

/-- The selective `prv.sim` simulator induced by a stateful `prv1` simulator `S`: it runs stage 1
of `S` on `φ` to obtain `(F, d)` and a state, runs stage 2 of `S` on the state and `y` to obtain
`X`, and returns `(F, X, d)`. -/
noncomputable def prv1SimulatorToPrv (S : Prv1Simulator Λ ρ) : PrvSimulator Λ :=
  fun y φ => do
    let (garbled, stSim) ← S.garble φ
    let X ← S.input stSim y
    pure ⟨garbled.fn, X, garbled.decInfo⟩

/-- The stage-2 state saved by `prvSimToPrv1`: the selective adversary's state together with the
answer `(F, d)` received in stage 1. -/
structure PrvSimToPrv1State (σ : Type) where
  /-- The state of the selective `prv.sim` adversary. -/
  state : σ
  /-- The garbled function `F` and decoding information `d` received from `Garble(f)`. -/
  garbled : GarbledFn

/-- Embed a selective `prv.sim` adversary `B` into an adaptive `prv1` adversary: stage 1 runs
`B.choose` to obtain a query `(f, x)` and a state `st` and saves `(x, st)`; stage 2 outputs the
pre-selected input `x` and saves `st` with `(F, d)`; stage 3 hands `(F, X, d)` to `B.guess`. -/
def prvSimToPrv1 (B : PrvSimAdversary Fn σ) :
    Prv1Adversary Fn (List Bool × σ) (PrvSimToPrv1State σ) where
  chooseFn := do
    let (q, st) ← B.choose ()
    pure (q.fn, (q.input, st))
  chooseInput := fun (x, st) garbled => pure (x, ⟨st, garbled⟩)
  guess s X := B.guess s.state (X.map fun X => ⟨s.garbled.fn, X, s.garbled.decInfo⟩)

/-- Running `prv1Experiment` on `prvSimToPrv1 B` against `S` has the exact same output
distribution as running `prvSimExperiment` on `B` against `prv1SimulatorToPrv S`, in both the real
(`b = true`) and simulated (`b = false`) worlds. -/
theorem eval_prv1Experiment_prvSimToPrv1 (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (B : PrvSimAdversary Fn σ) (b : Bool) :
    ProbComp.eval (prv1Experiment G Φ k S (prvSimToPrv1 B) b) =
      ProbComp.eval (prvSimExperiment G Φ k (prv1SimulatorToPrv S) B b) := by
  simp only [prv1Experiment, prvSimExperiment, prvSimToPrv1, prv1SimulatorToPrv,
    Scheme.prvView, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨q, st⟩ : 1
  by_cases hx : q.input.length = G.inLen q.fn
  · cases b <;> simp [hx, ProbComp.eval_bind]
  · cases b <;> simp [hx, PMF.bind_const]

/-- Adaptive `prv1` simulation security implies selective `prv.sim` security with exact advantage
preservation: the `prv.sim` advantage of `B` against `prv1SimulatorToPrv S` equals the `prv1`
advantage of `prvSimToPrv1 B` against `S`. -/
theorem prvSimAdvantage_prv1SimulatorToPrv_eq (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k (prv1SimulatorToPrv S) B = prv1Advantage G Φ k S (prvSimToPrv1 B) := by
  simp only [prvSimAdvantage, prv1Advantage, Experiment.advantage,
    eval_prv1Experiment_prvSimToPrv1]

theorem prvSimAdvantage_prv1SimulatorToPrv_le (G : Scheme Fn) (Φ : SideInfo Fn Λ) (k : ℕ)
    (S : Prv1Simulator Λ ρ) (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k (prv1SimulatorToPrv S) B ≤ prv1Advantage G Φ k S (prvSimToPrv1 B) :=
  (prvSimAdvantage_prv1SimulatorToPrv_eq G Φ k S B).le

/-- Adaptive `prv1` simulation security implies selective `prv.ind` indistinguishability security
with a factor of two against every stateful `prv1` simulator. -/
theorem prvIndAdvantage_eq_two_mul_prv1Advantage [DecidableEq Λ] (G : Scheme Fn)
    (Φ : SideInfo Fn Λ) (hCompat : Φ.Compatible G) (k : ℕ) (S : Prv1Simulator Λ ρ)
    (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A = 2 * prv1Advantage G Φ k S (prvSimToPrv1 (prvIndToSim G Φ A)) := by
  rw [prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G Φ hCompat k (prv1SimulatorToPrv S),
    prvSimAdvantage_prv1SimulatorToPrv_eq]

theorem prvIndAdvantage_le_two_mul_prv1Advantage [DecidableEq Λ] (G : Scheme Fn)
    (Φ : SideInfo Fn Λ) (hCompat : Φ.Compatible G) (k : ℕ) (S : Prv1Simulator Λ ρ)
    (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A ≤ 2 * prv1Advantage G Φ k S (prvSimToPrv1 (prvIndToSim G Φ A)) :=
  (prvIndAdvantage_eq_two_mul_prv1Advantage G Φ hCompat k S A).le

end Cslib.Crypto.Garbling
