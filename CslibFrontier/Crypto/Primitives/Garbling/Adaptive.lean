/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Foundations
import CslibFrontier.Probability.PMF.Bind

/-!
# Coarse-grained adaptive privacy for garbling schemes

In the selective privacy game `PrvSim` of [BellareHoangRogaway2012], Section 3.4, the adversary
submits the function description `f` and the input `x` together before seeing the garbled circuit.
Bellare, Hoang and Rogaway [BellareHoangRogaway2012b], Section 3.1, Figure 2, introduce the
coarse-grained adaptive privacy game `Prv1`, in which the adversary first queries `Garble(f)` to
obtain the garbled function and decoding information `(F, d)`, and only then adaptively chooses
the input `x` in a second query `Input(x)` to obtain the garbled input `X`.

In the simulated world (`b = false`), a two-stage stateful simulator `Prv1Simulator` first
produces `(F, d)` and a simulator state from `(1^k, Φ(f))`, and then produces `X` from the saved
state and the output `y = ev(f, x)` once `x` is chosen. Every stateful `prv1` simulator `S`
induces a selective `prv.sim` simulator `prv1SimulatorToPrv S` that runs the two simulator stages
back to back, and every selective `prv.sim` adversary `B` embeds into an adaptive `prv1`
adversary `prvSimToPrv1 B` that commits to `x` in its first-stage state. This embedding preserves
the experiment distribution on the nose in both worlds (`eval_prv1Exp_prvSimToPrv1`), so adaptive
`prv1` simulation security implies selective `prv.sim` security with exact advantage equality
(`prvSimAdvantage_prv1SimulatorToPrv_eq`) and selective `prv.ind` security with a factor of two
(`prvIndAdvantage_eq_two_mul_prv1Advantage`).

## Main definitions

* `Cslib.Crypto.Garbling.Prv1Adversary`: a two-stage adaptive privacy adversary.
* `Cslib.Crypto.Garbling.Prv1Simulator`: a two-stage stateful simulator for `Prv1`.
* `Cslib.Crypto.Garbling.prv1Exp`, `Cslib.Crypto.Garbling.prv1Advantage`,
  `Cslib.Crypto.Garbling.prv1BitGame`: the `Prv1` game and its advantage.
* `Cslib.Crypto.Garbling.prv1SimulatorToPrv`, `Cslib.Crypto.Garbling.prvSimToPrv1`: the
  reduction from selective `prv.sim` to adaptive `prv1`.

## Main results

* `Cslib.Crypto.Garbling.prv1Advantage_eq_two_mul_guessingAdvantage`: the `prv1` advantage is
  twice the bias of the hidden-bit game `prv1BitGame`.
* `Cslib.Crypto.Garbling.eval_prv1Exp_prvSimToPrv1`,
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

/-- A coarse-grained adaptive privacy (`prv1`) adversary ([BellareHoangRogaway2012b], Section 3.1,
Figure 2): in stage 1 (`Garble`) it chooses a function `f` and saves a state `st`; given `(F, d)`,
in stage 2 (`Input`) it adaptively chooses an input `x` and saves a state `st'`; finally it
guesses whether the view is real or simulated from the garbled input `X` (or `none` when `x` has
the wrong length). -/
structure Prv1Adversary (Fn σ τ : Type) where
  /-- Stage 1 (`Garble`): choose the function `f` and save a stage-1 state. -/
  chooseFn : ℕ → ProbComp (Fn × σ)
  /-- Stage 2 (`Input`): from `(F, d)`, adaptively choose the input `x` and save a stage-2
  state. -/
  chooseInput : ℕ → σ → List Bool × List Bool → ProbComp (List Bool × τ)
  /-- Guess whether the experiment is real or simulated from the garbled input `X` (or `⊥`). -/
  guess : ℕ → τ → Option (List Bool) → ProbComp Bool

/-- A stateful `prv1` simulator ([BellareHoangRogaway2012b], Section 3.1, Figure 2): in the first
stage `garble` produces a simulated pair `(F, d)` together with a simulator state from
`(1^k, Φ(f))`; in the second stage `input` produces a simulated garbled input `X` from the saved
simulator state and the output `y = ev(f, x)`. -/
structure Prv1Simulator (Λ ρ : Type) where
  /-- Stage 1 (`S(1^k, φ, 0)`): simulate `(F, d)` from `(1^k, Φ(f))` and save a state. -/
  garble : ℕ → Λ → ProbComp ((List Bool × List Bool) × ρ)
  /-- Stage 2 (`S(y, 1)`): simulate `X` from the saved state and `y = ev(f, x)`. -/
  input : ρ → List Bool → ProbComp (List Bool)

/-- Experiment `b` of the coarse-grained adaptive privacy game `Prv1`
([BellareHoangRogaway2012b], Section 3.1, Figure 2): for `b = true` the adversary interacts with
the real garbling `G.garble k f` and encoding `G.encode g.encInfo x`; for `b = false` it interacts
with the two-stage stateful simulator `S` on `Φ(f)` and `G.ev f x`. An input `x` of length
different from `G.inLen f` is answered with `none` (`⊥`). -/
noncomputable def prv1Exp (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : Prv1Simulator Λ ρ) (b : Bool)
    (A : Prv1Adversary Fn σ τ) (k : ℕ) : ProbComp Bool := do
  let (f, st) ← A.chooseFn k
  if b then
    let g ← G.garble k f
    let (x, st') ← A.chooseInput k st (g.fn, g.decInfo)
    if x.length = G.inLen f then
      A.guess k st' (some (G.encode g.encInfo x))
    else
      A.guess k st' none
  else
    let (fd, stSim) ← S.garble k (Φ.phi f)
    let (x, st') ← A.chooseInput k st fd
    if x.length = G.inLen f then
      let X ← S.input stSim (G.ev f x)
      A.guess k st' (some X)
    else
      A.guess k st' none

/-- The `prv1` advantage of an adaptive adversary `A` against a stateful simulator `S`: the
distinguishing advantage between the simulated (`b = false`) and real (`b = true`) experiments of
`Prv1`. -/
noncomputable def prv1Advantage (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : Prv1Simulator Λ ρ)
    (A : Prv1Adversary Fn σ τ) (k : ℕ) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (prv1Exp G Φ S false A k))
    (ProbComp.eval (prv1Exp G Φ S true A k))

/-- The game `Prv1` with a hidden uniform bit: it outputs whether the adversary guessed the
bit. -/
noncomputable def prv1BitGame (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : Prv1Simulator Λ ρ)
    (A : Prv1Adversary Fn σ τ) (k : ℕ) : ProbComp Bool := do
  let b ← ProbComp.uniform Bool
  let b' ← prv1Exp G Φ S b A k
  return b' == b

theorem prv1Advantage_le_one (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : Prv1Simulator Λ ρ)
    (A : Prv1Adversary Fn σ τ) (k : ℕ) :
    prv1Advantage G Φ S A k ≤ 1 :=
  Game.advantage_le_one _ _

/-- The `prv1` advantage is twice the bias of the hidden-bit game `prv1BitGame`, matching
`2 Pr[Prv1 = 1] - 1` in [BellareHoangRogaway2012b], Section 3.1. -/
theorem prv1Advantage_eq_two_mul_guessingAdvantage (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (S : Prv1Simulator Λ ρ) (A : Prv1Adversary Fn σ τ) (k : ℕ) :
    prv1Advantage G Φ S A k =
      2 * Game.guessingAdvantage (ProbComp.eval (prv1BitGame G Φ S A k)) := by
  have hbit : ProbComp.eval (prv1BitGame G Φ S A k) =
      (PMF.uniformOfFintype Bool).bind fun bit =>
        (ProbComp.eval (prv1Exp G Φ S bit A k)).map (fun guess => guess == bit) := by
    simp only [prv1BitGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
    rfl
  have key : ∀ a b : ℝ, |a - b| = 2 * |(1 - a + b) / 2 - 1 / 2| := fun a b => by
    rw [show (1 - a + b) / 2 - 1 / 2 = (b - a) / 2 by ring, abs_div, Nat.abs_ofNat, abs_sub_comm]
    ring
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_guessingAdvantage, hbit,
    Game.succProbability_uniform_bool_beq, prv1Advantage, Game.coe_advantage]
  exact key _ _

/-! ## Reduction from selective `prv.sim` and `prv.ind` to adaptive `prv1` -/

/-- The selective `prv.sim` simulator induced by a stateful `prv1` simulator `S`: it runs stage 1
of `S` on `(1^k, φ)` to obtain `((F, d), stSim)`, runs stage 2 of `S` on `(stSim, y)` to obtain
`X`, and returns `(F, X, d)`. -/
noncomputable def prv1SimulatorToPrv (S : Prv1Simulator Λ ρ) : PrvSimulator Λ :=
  fun k y φ => do
    let ((F, d), stSim) ← S.garble k φ
    let X ← S.input stSim y
    pure (F, X, d)

/-- The stage-2 state saved by `prvSimToPrv1`: the selective adversary's state together with the
garbled function `F` and decoding information `d` received in stage 1. -/
structure PrvSimToPrv1State (σ : Type) where
  /-- The state of the selective `prv.sim` adversary. -/
  state : σ
  /-- The garbled function `F` received from `Garble(f)`. -/
  fn : List Bool
  /-- The decoding information `d` received from `Garble(f)`. -/
  decInfo : List Bool

/-- Embed a selective `prv.sim` adversary `B` into an adaptive `prv1` adversary: stage 1 runs
`B.choose` to obtain `((f, x), st)` and saves `(x, st)`; stage 2 outputs the pre-selected input
`x` and saves `(st, F, d)`; stage 3 reassembles `(F, X, d)` for `B.guess`. -/
def prvSimToPrv1 (B : PrvSimAdversary Fn σ) :
    Prv1Adversary Fn (List Bool × σ) (PrvSimToPrv1State σ) where
  chooseFn k := do
    let ((f, x), st) ← B.choose k
    pure (f, (x, st))
  chooseInput _ st fd := pure (st.1, ⟨st.2, fd.1, fd.2⟩)
  guess k s ans :=
    match ans with
    | some X => B.guess k s.state (some (s.fn, X, s.decInfo))
    | none => B.guess k s.state none

/-- Running `prv1Exp` on `prvSimToPrv1 B` against `S` has the exact same output distribution as
running `prvSimExp` on `B` against `prv1SimulatorToPrv S`, in both the real (`b = true`) and
simulated (`b = false`) worlds. -/
theorem eval_prv1Exp_prvSimToPrv1 (G : Scheme Fn) (Φ : SideInfo Fn Λ) (S : Prv1Simulator Λ ρ)
    (b : Bool) (B : PrvSimAdversary Fn σ) (k : ℕ) :
    ProbComp.eval (prv1Exp G Φ S b (prvSimToPrv1 B) k) =
      ProbComp.eval (prvSimExp G Φ (prv1SimulatorToPrv S) b B k) := by
  simp only [prv1Exp, prvSimExp, prvSimToPrv1, prv1SimulatorToPrv, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext ⟨⟨f, x⟩, st⟩
  by_cases hx : x.length = G.inLen f
  · cases b <;> simp [hx, ProbComp.eval_bind]
  · cases b <;> simp [hx, PMF.bind_const]

/-- Adaptive `prv1` simulation security implies selective `prv.sim` security with exact advantage
preservation: the `prv.sim` advantage of `B` against `prv1SimulatorToPrv S` equals the `prv1`
advantage of `prvSimToPrv1 B` against `S`. -/
theorem prvSimAdvantage_prv1SimulatorToPrv_eq (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (S : Prv1Simulator Λ ρ) (B : PrvSimAdversary Fn σ) (k : ℕ) :
    prvSimAdvantage G Φ (prv1SimulatorToPrv S) B k =
      prv1Advantage G Φ S (prvSimToPrv1 B) k := by
  rw [prvSimAdvantage, prv1Advantage, ← eval_prv1Exp_prvSimToPrv1, ← eval_prv1Exp_prvSimToPrv1]

theorem prvSimAdvantage_prv1SimulatorToPrv_le (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (S : Prv1Simulator Λ ρ) (B : PrvSimAdversary Fn σ) (k : ℕ) :
    prvSimAdvantage G Φ (prv1SimulatorToPrv S) B k ≤
      prv1Advantage G Φ S (prvSimToPrv1 B) k :=
  (prvSimAdvantage_prv1SimulatorToPrv_eq G Φ S B k).le

/-- Adaptive `prv1` simulation security implies selective `prv.ind` indistinguishability security
with a factor of two against every stateful `prv1` simulator. -/
theorem prvIndAdvantage_eq_two_mul_prv1Advantage [DecidableEq Λ] (G : Scheme Fn)
    (Φ : SideInfo Fn Λ) (hCompat : Φ.Compatible G) (A : PrvIndAdversary Fn σ)
    (S : Prv1Simulator Λ ρ) (k : ℕ) :
    prvIndAdvantage G Φ A k =
      2 * prv1Advantage G Φ S (prvSimToPrv1 (prvIndToSim G Φ A)) k := by
  rw [prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G Φ hCompat A (prv1SimulatorToPrv S) k,
    prvSimAdvantage_prv1SimulatorToPrv_eq]

theorem prvIndAdvantage_le_two_mul_prv1Advantage [DecidableEq Λ] (G : Scheme Fn)
    (Φ : SideInfo Fn Λ) (hCompat : Φ.Compatible G) (A : PrvIndAdversary Fn σ)
    (S : Prv1Simulator Λ ρ) (k : ℕ) :
    prvIndAdvantage G Φ A k ≤
      2 * prv1Advantage G Φ S (prvSimToPrv1 (prvIndToSim G Φ A)) k :=
  (prvIndAdvantage_eq_two_mul_prv1Advantage G Φ hCompat A S k).le

end Cslib.Crypto.Garbling
