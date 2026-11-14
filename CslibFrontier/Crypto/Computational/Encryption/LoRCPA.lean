/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Languages.Probabilistic.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# Adaptive multi-challenge left-or-right chosen-plaintext security

In the `Q`-query left-or-right chosen-plaintext experiment ([Boneh and Shoup, Section 11.2,
Attack Game 11.1, multi-message variant, p. 437][BonehShoup2023]), an adversary first initializes
its saved state word from the security parameter and public key (`start`), then Adaptive-CPA
interacts with a left-or-right encryption oracle for `Q n` queries (`query`), and finally outputs a
distinguishing bit (`guess`). At each query step, `query` receives the unary security parameter,
the current saved state word, and the reverse transcript of challenge ciphertexts seen so far, and
returns a fresh challenge pair `(msg₀, msg₁)` together with an updated state word (`ChoiceOut Msg`).
Because `query` updates the state word at every step, coins flipped or challenge messages chosen in
earlier queries remain available to subsequent queries and to `guess`.

This module also provides the generic `Q`-query public-key replacement distinguishers
`lorDistinguisher` (for a fixed challenge bit) and `lorKeyDistinguisher` (sampling a hidden fair
challenge bit and outputting `guess ^^ bit`), together with their uniform strict PPT composition
certificates (`isPPTOn_lorDistinguisher`, `isPPT_lorDistinguisher`, `isPPT_lorKeyDistinguisher`)
and the loss-two public-key replacement bound `advantage_lorDistinguisher_le`.

## Main definitions

* `Cslib.Crypto.Encryption.LoRAdversaryOf`, `Cslib.Crypto.Encryption.LoRAdversary`,
  `Cslib.Crypto.Encryption.WordLoRAdversary`: stateful adaptive left-or-right adversaries for
  typed, bit, and bit-word messages.
* `Cslib.Crypto.Encryption.encLoRStageInput`, `Cslib.Crypto.Encryption.encLoRLoopState`: encodings
  of the adaptive query/guess stage inputs and the `(state, transcript)` loop state.
* `Cslib.Crypto.Encryption.LoRAdversaryOf.IsPPT`, `Cslib.Crypto.Encryption.LoRAdversary.IsPPT`,
  `Cslib.Crypto.Encryption.WordLoRAdversary.IsPPT`: uniform strict PPT admissibility of all three
  stages with polynomially bounded per-step state growth.
* `Cslib.Crypto.Encryption.lorStep`, `Cslib.Crypto.Encryption.lorRun`: one adaptive query step and
  the `q`-step adaptive query loop.
* `Cslib.Crypto.Encryption.lorDistinguisher`, `Cslib.Crypto.Encryption.lorKeyDistinguisher`:
  fixed-bit and hidden-bit `Q`-query public-key distinguishers.
* `Cslib.Crypto.Encryption.lorGame`, `Cslib.Crypto.Encryption.LoRINDCPAOf`,
  `Cslib.Crypto.Encryption.LoRINDCPA`, `Cslib.Crypto.Encryption.WordLoRINDCPA`: the `Q`-query
  left-or-right chosen-plaintext experiment and asymptotic security definitions.

## Main results

* `Cslib.Crypto.Encryption.eval_lorGame_eq_distinguishingGame`: `lorGame` depends only on the
  public-key marginal via `lorDistinguisher`.
* `Cslib.Crypto.Encryption.distinguishingGame_lorKeyDistinguisher`,
  `Cslib.Crypto.Encryption.probability_lorKeyDistinguisher`,
  `Cslib.Crypto.Encryption.advantage_lorDistinguisher_le`: hidden-bit identity and loss-two
  public-key replacement bound for `Q`-query left-or-right experiments.
* `Cslib.Crypto.Encryption.isPPTOn_lorDistinguisher`,
  `Cslib.Crypto.Encryption.isPPT_lorDistinguisher`,
  `Cslib.Crypto.Encryption.isPPT_lorKeyDistinguisher`: uniform strict PPT certificates via
  `IsPPTOn.iterateWith_of_bounded_growth`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 (Attack Game 11.1, pp. 436–437).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open scoped NNReal

variable {Msg : Type}

/-- A stateful adaptive multi-challenge left-or-right adversary over message space `Msg`.
* `start` receives the security parameter and public-key word and returns an initial state word.
* `query` receives the security parameter, current state word, and reverse transcript of challenge
  ciphertext words received so far, and outputs the next challenge pair `(msg₀, msg₁)` together
  with the updated state word (`ChoiceOut Msg = (Msg × Msg) × List Bool`).
* `guess` receives the security parameter, final state word, and complete reverse transcript of
  challenge ciphertext words, and outputs a distinguishing bit. -/
structure LoRAdversaryOf (Msg : Type) where
  /-- Initialize the adversary state word from the security parameter and public key. -/
  start : ℕ → List Bool → ProbComp (List Bool)
  /-- Choose the next challenge pair `(msg₀, msg₁)` and update the saved state word. -/
  query : ℕ → List Bool → List (List Bool) → ProbComp (ChoiceOut Msg)
  /-- Output the final distinguishing bit from the saved state word and ciphertext transcript. -/
  guess : ℕ → List Bool → List (List Bool) → ProbComp Bool

/-- Adaptive query-and-guessing stage input `(1ⁿ, state, transcript)`: the security parameter `n`
in unary, then the adversary's saved state word and the reverse list of challenge ciphertext words.
Both the parameter and the state word are framed. -/
abbrev encLoRStageInput : ℕ × List Bool × List (List Bool) ↪ List Bool :=
  encPair encUnary (encPair encBits (encList encBits))

/-- Adaptive loop state `(state, transcript)`: the adversary's saved state word paired with the
reverse list of challenge ciphertext words received so far. -/
abbrev encLoRLoopState : List Bool × List (List Bool) ↪ List Bool :=
  encPair encBits (encList encBits)

/-- Uniform strict PPT certificate for a stateful `LoRAdversaryOf Msg` over message encoding
`encMsg`: all three stages (`start`, `query`, `guess`) are uniform strict PPT on their complete
inputs, and each adaptive `query` increases the bit length of the saved state word by at most a
polynomially bounded function of the security parameter. -/
structure LoRAdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : LoRAdversaryOf Msg) : Prop where
  /-- The initialization stage is uniform strict PPT on the parameter and public key. -/
  start : Probability.IsPPT encBits adversary.start
  /-- The adaptive query stage is uniform strict PPT on the parameter, state word, and ciphertext
  transcript. -/
  query : IsPPTOn encLoRStageInput (encChoiceOut encMsg)
    (fun ⟨n, state, transcript⟩ => adversary.query n state transcript)
  /-- The final guessing stage is uniform strict PPT on the parameter, state word, and ciphertext
  transcript. -/
  guess : IsPPTOn encLoRStageInput encBool
    (fun ⟨n, state, transcript⟩ => adversary.guess n state transcript)
  /-- Per-step additive growth of the saved state word is polynomially bounded in the security
  parameter. -/
  state_growth : ∃ bound : ℕ → ℕ, Cslib.PolynomiallyBounded bound ∧
    ∀ n state transcript choice,
      choice ∈ (ProbComp.eval (adversary.query n state transcript)).support →
      (ChoiceOut.state choice).length ≤ state.length + bound n

/-- A stateful adaptive left-or-right adversary for single-bit messages (`Bool`). -/
abbrev LoRAdversary : Type := LoRAdversaryOf Bool

/-- Native uniform strict PPT admissibility for a bit adaptive left-or-right adversary. -/
abbrev LoRAdversary.IsPPT (adversary : LoRAdversary) : Prop :=
  LoRAdversaryOf.IsPPT encBool adversary

/-- A stateful adaptive left-or-right adversary for bit-word messages (`List Bool`). -/
abbrev WordLoRAdversary : Type := LoRAdversaryOf (List Bool)

/-- Native uniform strict PPT admissibility for a bit-word adaptive left-or-right adversary. -/
abbrev WordLoRAdversary.IsPPT (adversary : WordLoRAdversary) : Prop :=
  LoRAdversaryOf.IsPPT encBits adversary

/-- One adaptive left-or-right query step: ask `adversary.query` on the current state word and
reverse ciphertext transcript, encrypt the challenge message selected by `bit` under `pk`, and
return the updated state word paired with the extended ciphertext transcript. -/
noncomputable def lorStep (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : LoRAdversaryOf Msg) (security : ℕ) (pk : List Bool) (bit : Bool)
    (loopState : List Bool × List (List Bool)) : ProbComp (List Bool × List (List Bool)) := do
  let choice ← adversary.query security loopState.1 loopState.2
  let c ← encrypt security pk (if bit then ChoiceOut.msg₁ choice else ChoiceOut.msg₀ choice)
  return (ChoiceOut.state choice, c :: loopState.2)

/-- Run `q` adaptive left-or-right query steps starting from `loopState = (state, transcript)`. -/
noncomputable def lorRun (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : LoRAdversaryOf Msg) (security : ℕ) (pk : List Bool) (bit : Bool) (q : ℕ)
    (loopState : List Bool × List (List Bool)) : ProbComp (List Bool × List (List Bool)) :=
  OracleComp.iterate q (lorStep encrypt adversary security pk bit) loopState

/-- The `Q`-query left-or-right public-key distinguisher for a fixed challenge bit `bit`:
initialize the adversary state on `pk`, answer `Q security` adaptive queries under `pk` and `bit`,
and return the adversary's final guess. -/
noncomputable def lorDistinguisher (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (Q : ℕ → ℕ) (adversary : LoRAdversaryOf Msg) (bit : Bool) : Distinguisher :=
  fun security pk => do
    let st₀ ← adversary.start security pk
    let final ← lorRun encrypt adversary security pk bit (Q security) (st₀, [])
    adversary.guess security final.1 final.2

/-- The single uniform hidden-bit public-key distinguisher for `Q`-query left-or-right security:
sample a fair challenge bit `bit`, run `lorDistinguisher` with `bit`, and return `guess ^^ bit`. -/
noncomputable def lorKeyDistinguisher (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (Q : ℕ → ℕ) (adversary : LoRAdversaryOf Msg) : Distinguisher :=
  fun security pk => do
    let bit ← ProbComp.uniform Bool
    let guess ← lorDistinguisher encrypt Q adversary bit security pk
    return guess ^^ bit

/-- The `Q`-query left-or-right chosen-plaintext experiment with generated keys. -/
noncomputable def lorGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (bit : Bool) (security : ℕ) : ProbComp Bool := do
  let keys ← keyGen security
  lorDistinguisher encrypt Q adversary bit security keys.1

/-- Adaptive `Q`-query left-or-right IND-CPA security over message encoding `encMsg` against every
uniform strict PPT `LoRAdversaryOf Msg`. -/
def LoRINDCPAOf (encMsg : Msg ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (lorGame keyGen encrypt Q adversary false n))
    (fun adversary n => ProbComp.eval (lorGame keyGen encrypt Q adversary true n))
    (LoRAdversaryOf.IsPPT encMsg)

/-- Adaptive `Q`-query left-or-right IND-CPA security for single-bit encryption (`Bool`). -/
abbrev LoRINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)) (Q : ℕ → ℕ) : Prop :=
  LoRINDCPAOf encBool keyGen encrypt Q

/-- Adaptive `Q`-query left-or-right IND-CPA security for bit-word encryption (`List Bool`). -/
abbrev WordLoRINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) (Q : ℕ → ℕ) : Prop :=
  LoRINDCPAOf encBits keyGen encrypt Q

/-- An honest key generator contributes precisely its public-key marginal to `lorGame`. -/
theorem eval_lorGame_eq_distinguishingGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (bit : Bool) (security : ℕ) :
    ProbComp.eval (lorGame keyGen encrypt Q adversary bit security) =
      distinguishingGame ((ProbComp.eval (keyGen security)).map Prod.fst)
        (lorDistinguisher encrypt Q adversary bit security) := by
  simp [lorGame, distinguishingGame, Game.withSetup, PMF.bind_map, Function.comp_def]

/-- The hidden-bit distinguisher `lorKeyDistinguisher` averages the two `lorDistinguisher` games,
complementing the `true` experiment. -/
theorem distinguishingGame_lorKeyDistinguisher (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (security : ℕ) :
    distinguishingGame keys (lorKeyDistinguisher encrypt Q adversary security) = (do
      let bit ← PMF.uniformOfFintype Bool
      (distinguishingGame keys (lorDistinguisher encrypt Q adversary bit security)).map
        (fun guess => guess ^^ bit)) := by
  unfold distinguishingGame Game.withSetup lorKeyDistinguisher
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.map_bind]
  rw [PMF.bind_comm]
  rfl

/-- Acceptance of `lorKeyDistinguisher` is one half plus half the signed `Q`-query gap. -/
theorem probability_lorKeyDistinguisher (keys : PMF (List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (security : ℕ) :
    (Game.succProbability
      (distinguishingGame keys (lorKeyDistinguisher encrypt Q adversary security)) : ℝ) =
      (1 + (Game.succProbability
          (distinguishingGame keys (lorDistinguisher encrypt Q adversary false security)) : ℝ) -
        Game.succProbability
          (distinguishingGame keys (lorDistinguisher encrypt Q adversary true security))) / 2 := by
  rw [distinguishingGame_lorKeyDistinguisher]
  exact Game.succProbability_uniform_bool_xor _

/-- Replacing the public-key law `real` with `ideal` in the `Q`-query left-or-right experiment
costs at most twice the distinguishing advantage of `lorKeyDistinguisher`, plus the `Q`-query
advantage under `ideal`. -/
theorem advantage_lorDistinguisher_le (real ideal : PMF (List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (Q : ℕ → ℕ)
    (adversary : LoRAdversaryOf Msg) (security : ℕ) :
    Game.advantage
      (distinguishingGame real (lorDistinguisher encrypt Q adversary false security))
      (distinguishingGame real (lorDistinguisher encrypt Q adversary true security)) ≤
        2 * Game.advantage
          (distinguishingGame real (lorKeyDistinguisher encrypt Q adversary security))
          (distinguishingGame ideal (lorKeyDistinguisher encrypt Q adversary security)) +
            Game.advantage
              (distinguishingGame ideal (lorDistinguisher encrypt Q adversary false security))
              (distinguishingGame ideal (lorDistinguisher encrypt Q adversary true security)) := by
  rw [distinguishingGame_lorKeyDistinguisher, distinguishingGame_lorKeyDistinguisher]
  exact Game.advantage_le_two_mul_uniform_bool_xor
    (fun bit => distinguishingGame real (lorDistinguisher encrypt Q adversary bit security))
    (fun bit => distinguishingGame ideal (lorDistinguisher encrypt Q adversary bit security))

/-- Parameterized uniform strict PPT certificate for `lorDistinguisher` when encryption is strict
PPT with polynomially bounded ciphertext length, `Q` is computable in polynomial time, and the
adversary satisfies `LoRAdversaryOf.IsPPT`. -/
theorem isPPTOn_lorDistinguisher {α : Type} {input : α ↪ List Bool}
    {encMsg : Msg ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg}
    {security : α → ℕ} {pk : α → List Bool} {bit : α → Bool}
    {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c,
      c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg)
    (hsecurity : ComputableInPolyTime security input encUnary)
    (hpk : ComputableInPolyTime pk input encBits)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool
      (fun a => lorDistinguisher encrypt Q adversary (bit a) (security a) (pk a)) := by
  let captEnc := encPair input encBits
  have hstart : IsPPTOn input encBits (fun a => adversary.start (security a) (pk a)) :=
    hadversary.start.on.preprocess (hsecurity.prod hpk)
  have hqArg : ComputableInPolyTime
      (fun p : (α × List Bool) × (List Bool × List (List Bool)) => (security p.1.1, p.2))
      (encPair captEnc encLoRLoopState) encLoRStageInput := by
    dsimp only [captEnc, encLoRLoopState, encLoRStageInput]; fun_prop
  have hstep : IsPPTOn (encPair captEnc encLoRLoopState) encLoRLoopState
      (fun p => lorStep encrypt adversary (security p.1.1) (pk p.1.1) (bit p.1.1) p.2) := by
    have hquery : IsPPTOn (encPair captEnc encLoRLoopState) (encChoiceOut encMsg)
        (fun p => adversary.query (security p.1.1) p.2.1 p.2.2) :=
      hadversary.query.preprocess hqArg
    let stepMidEnc := encPair (encPair captEnc encLoRLoopState) (encChoiceOut encMsg)
    have ha : ComputableInPolyTime
        (fun q : ((α × List Bool) × (List Bool × List (List Bool))) × ChoiceOut Msg => q.1.1.1)
        stepMidEnc input :=
      (fst input encBits).comp
        ((fst captEnc encLoRLoopState).comp
          (fst (encPair captEnc encLoRLoopState) (encChoiceOut encMsg)))
    have hchoice := snd (encPair captEnc encLoRLoopState) (encChoiceOut encMsg)
    have hmsgs := (fst (encPair encMsg encMsg) encBits).comp hchoice
    have hsel : ComputableInPolyTime
        (fun q : ((α × List Bool) × (List Bool × List (List Bool))) × ChoiceOut Msg =>
          if bit q.1.1.1 then ChoiceOut.msg₁ q.2 else ChoiceOut.msg₀ q.2)
        stepMidEnc encMsg :=
      ComputableInPolyTime.ite (hbit.comp ha)
        ((snd encMsg encMsg).comp hmsgs) ((fst encMsg encMsg).comp hmsgs)
    have henc : IsPPTOn stepMidEnc encBits
        (fun q => encrypt (security q.1.1.1) (pk q.1.1.1)
          (if bit q.1.1.1 then ChoiceOut.msg₁ q.2 else ChoiceOut.msg₀ q.2)) :=
      hencrypt.preprocess ((hsecurity.comp ha).prod ((hpk.comp ha).prod hsel))
    have hstateOut : ComputableInPolyTime
        (fun r : (((α × List Bool) × (List Bool × List (List Bool))) × ChoiceOut Msg) × List Bool =>
          ChoiceOut.state r.1.2)
        (encPair stepMidEnc encBits) encBits :=
      ((snd (encPair encMsg encMsg) encBits).comp hchoice).comp (fst stepMidEnc encBits)
    have htrOut : ComputableInPolyTime
        (fun r : (((α × List Bool) × (List Bool × List (List Bool))) × ChoiceOut Msg) × List Bool =>
          r.2 :: r.1.1.2.2)
        (encPair stepMidEnc encBits) (encList encBits) := by
      dsimp only [stepMidEnc, captEnc, encLoRLoopState, encChoiceOut]; fun_prop
    have hcons := henc.map_with (f := fun q c => (ChoiceOut.state q.2, c :: q.1.2.2))
      (hstateOut.prod htrOut)
    simpa only [lorStep, bind_pure_comp] using hquery.bind_with hcons
  have hcount : ComputableInPolyTime (fun p : α × List Bool => Q (security p.1))
      captEnc encUnary := by
    dsimp only [captEnc]; fun_prop
  have hinitial : ComputableInPolyTime
      (fun p : α × List Bool => (p.2, ([] : List (List Bool))))
      captEnc encLoRLoopState :=
    (snd input encBits).prod (const [])
  obtain ⟨stBound, hstBound, hstLen⟩ := hadversary.state_growth
  have hsecPoly : PolyBounded (fun p : α × List Bool => (captEnc p).length)
      (fun p => security p.1) :=
    (hsecurity.comp (fst input encBits)).tidy.polyBounded
  have hstPoly : PolyBounded (fun p : α × List Bool => (captEnc p).length)
      (fun p => stBound (security p.1)) :=
    (PolyBounded.of_polynomiallyBounded (fun p : α × List Bool => security p.1) hstBound).comp
      hsecPoly
  have hctPoly : PolyBounded (fun p : α × List Bool => (captEnc p).length)
      (fun p => ctBound (security p.1)) :=
    (PolyBounded.of_polynomiallyBounded (fun p : α × List Bool => security p.1) hctBound).comp
      hsecPoly
  have hgrowthPoly : PolyBounded (fun p : α × List Bool => (captEnc p).length)
      (fun p => 2 * stBound (security p.1) + 2 * ctBound (security p.1) + 1) :=
    (((PolyBounded.const 2).mul hstPoly).add ((PolyBounded.const 2).mul hctPoly)).add
      (PolyBounded.const 1)
  have hrun : IsPPTOn captEnc encLoRLoopState
      (fun p => lorRun encrypt adversary (security p.1) (pk p.1) (bit p.1)
        (Q (security p.1)) (p.2, [])) := by
    refine IsPPTOn.iterateWith_of_bounded_growth hcount.tidy hinitial.tidy hstep hgrowthPoly ?_
    intro p loopState next hnext
    simp only [lorStep, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hnext
    obtain ⟨choice, hchoice_supp, c, hc_supp, rfl⟩ := hnext
    have hst := hstLen (security p.1) loopState.1 loopState.2 choice hchoice_supp
    have hct := hctLen (security p.1) (pk p.1) _ c hc_supp
    simp only [encLoRLoopState, encPair_apply, encBits_apply, encList_cons,
      List.length_append, length_frame]
    omega
  have hguess : IsPPTOn (encPair captEnc encLoRLoopState) encBool
      (fun p => adversary.guess (security p.1.1) p.2.1 p.2.2) :=
    hadversary.guess.preprocess hqArg
  simpa only [lorDistinguisher] using hstart.bind_with (hrun.bind_with hguess)

/-- `lorDistinguisher` is one uniform strict PPT distinguisher when encryption is strict PPT with
polynomially bounded ciphertext length, `Q` is computable in polynomial time, and the adversary
satisfies `LoRAdversaryOf.IsPPT`. -/
theorem isPPT_lorDistinguisher {encMsg : Msg ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg} {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c,
      c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPT encBool (lorDistinguisher encrypt Q adversary bit) :=
  isPPTOn_lorDistinguisher hencrypt hctBound hctLen hQ hadversary
    (fst encUnary encBits) (snd encUnary encBits) (const bit)

/-- The hidden-bit reduction `lorKeyDistinguisher` is one uniform strict PPT distinguisher when
encryption is strict PPT with polynomially bounded ciphertext length, `Q` is computable in
polynomial time, and the adversary satisfies `LoRAdversaryOf.IsPPT`. -/
theorem isPPT_lorKeyDistinguisher {encMsg : Msg ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {Q : ℕ → ℕ} {adversary : LoRAdversaryOf Msg} {ctBound : ℕ → ℕ}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, k, msg⟩ => encrypt n k msg))
    (hctBound : Cslib.PolynomiallyBounded ctBound)
    (hctLen : ∀ n k msg c,
      c ∈ (ProbComp.eval (encrypt n k msg)).support → c.length ≤ ctBound n)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hadversary : adversary.IsPPT encMsg) :
    IsPPT encBool (lorKeyDistinguisher encrypt Q adversary) := by
  let baseEnc := encPair encUnary encBits
  let coinEnc := encPair baseEnc encBool
  have hcoin := isPPTOn_uniform_bool baseEnc
  have hdist : IsPPTOn coinEnc encBool
      (fun p => lorDistinguisher encrypt Q adversary p.2 p.1.1 p.1.2) :=
    isPPTOn_lorDistinguisher hencrypt hctBound hctLen hQ hadversary
      (by dsimp only [coinEnc, baseEnc]; fun_prop)
      (by dsimp only [coinEnc, baseEnc]; fun_prop)
      (snd baseEnc encBool)
  have hxor : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × Bool) × Bool => p.2 ^^ p.1.2)
      (encPair coinEnc encBool) encBool := by
    have hx := of_finite (encIn := encPair encBool encBool) (encOut := encBool)
      fun p : Bool × Bool => p.1 ^^ p.2
    have harg : ComputableInPolyTime
        (fun p : ((ℕ × List Bool) × Bool) × Bool => (p.2, p.1.2))
        (encPair coinEnc encBool) (encPair encBool encBool) := by
      dsimp only [coinEnc, baseEnc]; fun_prop
    simpa only [Function.comp_def] using hx.comp harg
  simpa only [IsPPT, lorKeyDistinguisher, bind_pure_comp] using
    hcoin.bind_with (hdist.map_with (f := fun p guess => guess ^^ p.2) hxor)

end Cslib.Crypto.Encryption
