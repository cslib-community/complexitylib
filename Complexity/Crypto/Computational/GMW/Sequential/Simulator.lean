/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GMW.Sequential
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import Complexity.Computability.Probabilistic.Adaptive
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Probability.PMF.Bind

/-!
# Multi-session zero-knowledge simulator and PRG reduction for sequentially amplified GMW

This module constructs the multi-session zero-knowledge simulator `gmwSeqSimulator` and the
single-challenge PRG reduction `gmwSeqViewReduction` for the `k n`-fold sequentially composed GMW
protocol (`Complexity.Crypto.Computational.GMW.Sequential`).

Given any uniform strict oracle PPT malicious verifier `Vstar` (`IsOraclePPTOn`), we extract its
clocked multi-tape probabilistic oracle Turing machine and run `k n` sequential sessions on its
configuration state `(rem, cfg)` via `sessionStep`, followed by `finishSessionRun` to complete any
remaining machine steps after the `k n` sessions are exhausted.

Because all `k n * ((n + 1) * totalLen (f a))` unopened commitment pads across the `k n` sessions
and `n + 1` challenge-guessing attempts per session are drawn independently of the adaptive machine
state, we flatten all unopened pads into a single list pre-sampled via `OracleComp.replicate` and
consume `totalLen (f a)` pads per attempt via `List.take` and `List.drop` (`attemptWithPadsStep`,
`sessionWithPadsStep`, `runAllSessionsWithPads`). Applying `sequenceTest` once to this flat pad
sequence yields the single-challenge reduction `gmwSeqViewReduction` with exact dyadic hybrid loss
`dyadicSize (k n * ((n + 1) * totalLen (f a)))` and multi-session rejection-sampling error at most
`(k n : ℝ≥0) * (7 / 8) ^ (n + 1)`.

## Main definitions

* `Cslib.Crypto.GMW.realPRGPadsSessionStep`: single-session hybrid repeating `gmwRealPRGPadsOpt`
  `att` times with fallback `st`.
* `Cslib.Crypto.GMW.attemptWithPadsStep`, `Cslib.Crypto.GMW.sessionWithPadsStep`,
  `Cslib.Crypto.GMW.runAllSessionsWithPads`: pre-sampled pad consumption across attempts and
  sessions.
* `Cslib.Crypto.GMW.gmwSeqSimulator`: witness-free multi-session simulator for any uniform strict
  oracle PPT malicious verifier `Vstar`.
* `Cslib.Crypto.GMW.gmwSeqViewReduction`: single-challenge PRG distinguisher for the `k n`-session
  view hybrid.

## Main results

* `Cslib.Crypto.GMW.gmwSeqView_advantage_le`: unconditional finite multi-session view-advantage
  bound.
* `Cslib.Crypto.GMW.isPPTOn_gmwSeqSimulator`: strict full-input PPT certificate for
  `gmwSeqSimulator`.
* `Cslib.Crypto.GMW.isPPTOn_gmwSeqViewReduction`: strict full-input PPT certificate for
  `gmwSeqViewReduction`.
* `Cslib.Crypto.GMW.AdvicePRG.gmwSeqView_negligible`: auxiliary-input zero-knowledge view
  indistinguishability under `AdvicePRG`.
* `Cslib.Crypto.GMW.gmwSeqView_indistinguishable_gmwSeqSimulator`: uniform-family view
  indistinguishability under `PseudorandomGenerator`.
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM
open _root_.Turing.MultiTapeMachine _root_.Turing.MultiTapePTM
open scoped NNReal ENNReal

/-! ### Step 1: Multi-session rejection-sampling hybrid -/

/-- One session of the intermediate hybrid on `(rem, cfg)`, repeating `gmwRealPRGPadsOpt` `att`
times and falling back to `st` on failure. -/
noncomputable def realPRGPadsSessionStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit) :
    ProbComp (ℕ × FiniteConfig tapes Bool Control Unit) :=
  firstSuccess st <$>
    OracleComp.replicate att
      (gmwRealPRGPadsOpt generator s m φ w (sessionStep machine limit st.1 2 st.2))

theorem eval_realPRGPadsSessionStep {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit) :
    ProbComp.eval (realPRGPadsSessionStep machine generator s m limit att φ w st) =
      repeatAttempt st
        (ProbComp.eval (realSessionStep machine generator s m limit φ w st)) att := by
  dsimp only [realPRGPadsSessionStep]
  rw [ProbComp.eval_map,
    ProbComp.eval_replicate_congr (eval_game0PadsOpt_eq_eval_game0Opt
      (encPair encUnary encFiniteConfig) generator s m φ w _),
    ← ProbComp.eval_map]
  exact eval_firstSuccess_replicate_eq_repeatAttempt st
    (eval_game0Opt_eq_bind_bernoulliAttemptOpt (encPair encUnary encFiniteConfig)
      generator s m φ w _) att

/-- Across `K` sequential sessions, replacing `realSessionStep` with `realPRGPadsSessionStep`
changes the acceptance probability of any post-processing game `post` by at most
`(K : ℝ≥0) * (7 / 8) ^ att`. -/
theorem advantage_iterate_realSessionStep_realPRGPadsSessionStep_le
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (K : ℕ) (st : ℕ × FiniteConfig tapes Bool Control Unit)
    (post : ℕ × FiniteConfig tapes Bool Control Unit → PMF Bool) :
    Game.advantage
      ((ProbComp.eval (OracleComp.iterate K
        (realSessionStep machine generator s m limit φ w) st)).bind post)
      ((ProbComp.eval (OracleComp.iterate K
        (realPRGPadsSessionStep machine generator s m limit att φ w) st)).bind post) ≤
      (K : ℝ≥0) * (7 / 8 : ℝ≥0) ^ att := by
  induction K generalizing st with
  | zero => simp [OracleComp.iterate_zero]
  | succ K ih =>
    simp only [OracleComp.iterate_succ_bind, ProbComp.eval_bind, PMF.bind_bind]
    have h1 : Game.advantage
        ((ProbComp.eval (realSessionStep machine generator s m limit φ w st)).bind
          (fun st' => (ProbComp.eval (OracleComp.iterate K
            (realSessionStep machine generator s m limit φ w) st')).bind post))
        ((ProbComp.eval (realPRGPadsSessionStep machine generator s m limit att φ w st)).bind
          (fun st' => (ProbComp.eval (OracleComp.iterate K
            (realSessionStep machine generator s m limit φ w) st')).bind post)) ≤
        (7 / 8 : ℝ≥0) ^ att := by
      rw [Game.advantage_comm, eval_realPRGPadsSessionStep]
      exact advantage_bind_repeatAttempt_le st _ _ att
    have h2 : Game.advantage
        ((ProbComp.eval (realPRGPadsSessionStep machine generator s m limit att φ w st)).bind
          (fun st' => (ProbComp.eval (OracleComp.iterate K
            (realSessionStep machine generator s m limit φ w) st')).bind post))
        ((ProbComp.eval (realPRGPadsSessionStep machine generator s m limit att φ w st)).bind
          (fun st' => (ProbComp.eval (OracleComp.iterate K
            (realPRGPadsSessionStep machine generator s m limit att φ w) st')).bind post)) ≤
        (K : ℝ≥0) * (7 / 8 : ℝ≥0) ^ att :=
      Game.advantage_bind_le_nnreal _ _ _ ih
    calc Game.advantage _ _
        ≤ (7 / 8 : ℝ≥0) ^ att + (K : ℝ≥0) * (7 / 8 : ℝ≥0) ^ att :=
          (Game.advantage_triangle _ _ _).trans (add_le_add h1 h2)
      _ = ((K + 1 : ℕ) : ℝ≥0) * (7 / 8 : ℝ≥0) ^ att := by push_cast; ring

/-! ### Step 2: Flattening unopened pads across attempts and sessions -/

theorem eval_replicate_add_take_drop {α β : Type} (A B : ℕ) (d : ProbComp α)
    (f : List α → List α → ProbComp β) :
    ProbComp.eval (do
      let zs ← OracleComp.replicate (A + B) d
      f (zs.take A) (zs.drop A)) =
    ProbComp.eval (do
      let xs ← OracleComp.replicate A d
      let ys ← OracleComp.replicate B d
      f xs ys) := by
  induction A generalizing f with
  | zero => simp [OracleComp.replicate_zero]
  | succ A ih =>
    rw [Nat.succ_add, OracleComp.replicate_succ, OracleComp.replicate_succ]
    simp only [bind_assoc, bind_map_left, List.take_succ_cons, List.drop_succ_cons,
      ProbComp.eval_bind]
    refine congrArg (PMF.bind _) (funext fun x => ?_)
    simpa only [ProbComp.eval_bind] using ih (fun xs ys => f (x :: xs) ys)

private theorem foldl_or_some {β : Type} (xs : List (Option β)) (v : β) :
    xs.foldl Option.or (some v) = some v := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem getD_foldl_or_none {β : Type} (xs : List (Option β)) (d : β) :
    (xs.foldl Option.or none).getD d = firstSuccess d xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => exact ih
    | some v => simp [List.foldl_cons, Option.or, firstSuccess, foldl_or_some]

/-- One attempt of a session consuming `totalLen φ` pre-sampled pads from `state.2` and updating
the first-success accumulator `state.1`. -/
noncomputable def attemptWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit)
    (state : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) :
    ProbComp (Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) := do
  let res ← gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit st.1 2 st.2)
    (state.2.take (totalLen φ))
  return (state.1.or res, state.2.drop (totalLen φ))

/-- One session of `att` attempts consuming `att * totalLen φ` pre-sampled pads from `state.2` and
updating the machine configuration `state.1`. -/
noncomputable def sessionWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (state : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) :
    ProbComp ((ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) := do
  let p ← OracleComp.iterate att
    (attemptWithPadsStep machine generator s m limit φ w state.1) (none, state.2)
  return (p.1.getD state.1, p.2)

/-- Run all `K` sessions on a pre-sampled flat list of `pads`, starting from the initial machine
configuration `(limit, FiniteConfig.init machine.initial word)`, and finish with
`finishSessionRun`. -/
noncomputable def runAllSessionsWithPads {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att K : ℕ) (φ : CNF ℕ) (w word : List Bool)
    (pads : List (List Bool)) : ProbComp (List Bool) := do
  let p ← OracleComp.iterate K
    (sessionWithPadsStep machine generator s m limit att φ w)
    ((limit, FiniteConfig.init machine.initial word), pads)
  finishSessionRun machine limit p.1

theorem eval_replicate_iterate_attemptWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit)
    (d_pad : ProbComp (List Bool)) (att B : ℕ)
    (acc : Option (ℕ × FiniteConfig tapes Bool Control Unit)) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate (att * totalLen φ + B) d_pad
      OracleComp.iterate att (attemptWithPadsStep machine generator s m limit φ w st)
        (acc, pads)) =
    ProbComp.eval (do
      let attempts ← OracleComp.replicate att (do
        let p ← OracleComp.replicate (totalLen φ) d_pad
        gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit st.1 2 st.2) p)
      let rest ← OracleComp.replicate B d_pad
      return (attempts.foldl Option.or acc, rest)) := by
  induction att generalizing acc with
  | zero => simp [OracleComp.iterate_zero, OracleComp.replicate_zero]
  | succ att ih =>
    have hadd : (att + 1) * totalLen φ + B = totalLen φ + (att * totalLen φ + B) := by ring
    rw [hadd]
    simp only [OracleComp.iterate_succ_bind, attemptWithPadsStep, bind_assoc, pure_bind]
    rw [eval_replicate_add_take_drop (totalLen φ) (att * totalLen φ + B) d_pad
      (fun p pads' => do
        let res ← gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit st.1 2 st.2) p
        OracleComp.iterate att (attemptWithPadsStep machine generator s m limit φ w st)
          (acc.or res, pads'))]
    simp only [OracleComp.replicate_succ, bind_assoc, bind_map_left, List.foldl_cons,
      ProbComp.eval_bind]
    refine congrArg (PMF.bind _) (funext fun p => ?_)
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind _) (funext fun res => ?_)
    simpa only [ProbComp.eval_bind] using ih (acc.or res)

theorem eval_replicate_sessionWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit)
    (d_pad : ProbComp (List Bool)) (B : ℕ) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate (att * totalLen φ + B) d_pad
      sessionWithPadsStep machine generator s m limit att φ w (st, pads)) =
    ProbComp.eval (do
      let st' ← firstSuccess st <$> OracleComp.replicate att (do
        let p ← OracleComp.replicate (totalLen φ) d_pad
        gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit st.1 2 st.2) p)
      let rest ← OracleComp.replicate B d_pad
      return (st', rest)) := by
  have hmap := congrArg
    (PMF.map (fun p : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool) =>
      (p.1.getD st, p.2)))
    (eval_replicate_iterate_attemptWithPadsStep machine generator s m limit φ w st d_pad att B none)
  simpa only [sessionWithPadsStep, bind_pure_comp, bind_map_left, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    PMF.pure_map, Function.comp_def, getD_foldl_or_none] using hmap

theorem eval_replicate_iterate_sessionWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ) (w : List Bool)
    (d_pad : ProbComp (List Bool)) (K : ℕ)
    (st : ℕ × FiniteConfig tapes Bool Control Unit) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate (K * (att * totalLen φ)) d_pad
      Prod.fst <$> OracleComp.iterate K
        (sessionWithPadsStep machine generator s m limit att φ w) (st, pads)) =
    ProbComp.eval (OracleComp.iterate K (fun cur =>
      firstSuccess cur <$> OracleComp.replicate att (do
        let p ← OracleComp.replicate (totalLen φ) d_pad
        gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit cur.1 2 cur.2) p)) st) := by
  induction K generalizing st with
  | zero => simp [OracleComp.iterate_zero, OracleComp.replicate_zero]
  | succ K ih =>
    have hmul : (K + 1) * (att * totalLen φ) = att * totalLen φ + K * (att * totalLen φ) := by ring
    rw [hmul]
    simp only [OracleComp.iterate_succ_bind, map_bind]
    have hstep := congrArg
      (fun d => d.bind (fun p : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool) =>
        ProbComp.eval (Prod.fst <$> OracleComp.iterate K
          (sessionWithPadsStep machine generator s m limit att φ w) p)))
      (eval_replicate_sessionWithPadsStep machine generator s m limit att φ w st d_pad
        (K * (att * totalLen φ)))
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind] at hstep ⊢
    rw [hstep]
    refine congrArg (PMF.bind _) (funext fun st' => ?_)
    simpa only [ProbComp.eval_bind] using ih st'

private theorem eval_iterate_congr {α : Type} {f g : α → ProbComp α}
    (h : ∀ x, ProbComp.eval (f x) = ProbComp.eval (g x)) (K : ℕ) (x : α) :
    ProbComp.eval (OracleComp.iterate K f x) = ProbComp.eval (OracleComp.iterate K g x) := by
  induction K generalizing x with
  | zero => rfl
  | succ K ih =>
    simp only [OracleComp.iterate_succ_bind, ProbComp.eval_bind, h x]
    exact congrArg (PMF.bind _) (funext ih)

theorem eval_replicate_runAllSessionsWithPads_prg {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att K : ℕ) (φ : CNF ℕ) (w word : List Bool) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate (K * (att * totalLen φ))
        (generator <$> BitString.sampleList s)
      runAllSessionsWithPads machine generator s m limit att K φ w word pads) =
    ProbComp.eval (do
      let st' ← OracleComp.iterate K
        (realPRGPadsSessionStep machine generator s m limit att φ w)
        (limit, FiniteConfig.init machine.initial word)
      finishSessionRun machine limit st') := by
  have hiter := eval_replicate_iterate_sessionWithPadsStep machine generator s m limit att φ w
    (generator <$> BitString.sampleList s) K (limit, FiniteConfig.init machine.initial word)
  have hbind := congrArg
    (fun d => d.bind (fun st' => ProbComp.eval (finishSessionRun machine limit st'))) hiter
  simp only [runAllSessionsWithPads, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def] at hbind ⊢
  exact hbind

theorem eval_replicate_runAllSessionsWithPads_uniform {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att K : ℕ) (φ : CNF ℕ) (w word : List Bool)
    (hw : ThreeSAT.verifier (φ, w) = true) :
    ProbComp.eval (do
      let pads ← OracleComp.replicate (K * (att * totalLen φ)) (BitString.sampleList m)
      runAllSessionsWithPads machine generator s m limit att K φ w word pads) =
    ProbComp.eval (do
      let st' ← OracleComp.iterate K
        (simSessionStep machine generator s m limit att φ)
        (limit, FiniteConfig.init machine.initial word)
      finishSessionRun machine limit st') := by
  have hiter := eval_replicate_iterate_sessionWithPadsStep machine generator s m limit att φ w
    (BitString.sampleList m) K (limit, FiniteConfig.init machine.initial word)
  have hcongr : ∀ cur : ℕ × FiniteConfig tapes Bool Control Unit,
      ProbComp.eval (firstSuccess cur <$> OracleComp.replicate att (do
        let p ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
        gmwRealWithPadsOpt generator s m φ w (sessionStep machine limit cur.1 2 cur.2) p)) =
      ProbComp.eval (simSessionStep machine generator s m limit att φ cur) := by
    intro cur
    change ProbComp.eval (firstSuccess cur <$> OracleComp.replicate att
        (gmwRealUniformPadsOpt generator s m φ w (sessionStep machine limit cur.1 2 cur.2))) =
      ProbComp.eval (simSessionStep machine generator s m limit att φ cur)
    simp only [simSessionStep, ProbComp.eval_map]
    rw [ProbComp.eval_replicate_congr
      (eval_game1Opt_eq_eval_gmwSimAttemptOpt (encPair encUnary encFiniteConfig)
        generator hw (sessionStep machine limit cur.1 2 cur.2))]
  rw [eval_iterate_congr hcongr] at hiter
  have hbind := congrArg
    (fun d => d.bind (fun st' => ProbComp.eval (finishSessionRun machine limit st'))) hiter
  simp only [runAllSessionsWithPads, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def] at hbind ⊢
  exact hbind

/-! ### Step 3: Strict polynomial-time certificates for session and multi-session loops -/

private theorem computableInPolyTime_optionOr {α β : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {left right : α → Option β}
    (hleft : ComputableInPolyTime left encA (encOption encB))
    (hright : ComputableInPolyTime right encA (encOption encB)) :
    ComputableInPolyTime (fun a => (left a).or (right a)) encA (encOption encB) :=
  (congrArg (ComputableInPolyTime · encA (encOption encB))
    (by funext a; cases left a <;> rfl)).mp
    ((hleft.tidy.optionIsSome.computableInPolyTime).ite' hleft hright)

private abbrev SessionCtx (α : Type) (tapes : ℕ) (Control : Type) :=
  α × (ℕ × (ℕ × FiniteConfig tapes Bool Control Unit))

private noncomputable def VstarSession {α : Type} {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (_ : ℕ) (x : SessionCtx α tapes Control) (_ : List Bool) :
    WordOracleComp Unit (ℕ × FiniteConfig tapes Bool Control Unit) :=
  sessionStep machine x.2.1 x.2.2.1 2 x.2.2.2

private theorem isOraclePPTOn_VstarSession {α : Type} {enc : α ↪ List Bool}
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit) :
    IsOraclePPTOn
      (encPair encUnary (encPair
        (encPair enc (encPair encUnary (encPair encUnary encFiniteConfig))) encBits))
      (encPair encUnary encFiniteConfig)
      (fun p => VstarSession (α := α) machine p.1 p.2.1 p.2.2) := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  let encCtx := encPair enc (encPair encUnary encSt)
  have hctx := (ComputableInPolyTime.snd encUnary (encPair encCtx encBits)).fst'.snd'
  have h := (isOraclePPTOn_sessionStep machine).preprocess'
    (hctx.fst'.prod (hctx.snd'.fst'.prod ((ComputableInPolyTime.const 2).prod hctx.snd'.snd')))
  exact (congrArg (IsOraclePPTOn _ _) (by funext p; rfl)).mp h

theorem isPPTOn_simSessionStep {α Param : Type} {enc : α ↪ List Bool}
    {input : Param ↪ List Bool} {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {n limit att : Param → ℕ} {a : Param → α}
    {st : Param → ℕ × FiniteConfig tapes Bool Control Unit}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hn : ComputableInPolyTime n input encUnary)
    (hlimit : ComputableInPolyTime limit input encUnary)
    (hatt : ComputableInPolyTime att input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hst : ComputableInPolyTime st input (encPair encUnary encFiniteConfig)) :
    IsPPTOn input (encPair encUnary encFiniteConfig) (fun p =>
      simSessionStep machine generator (n p + 7) (length (n p + 7))
        (limit p) (att p) (f (a p)) (st p)) := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  let encCtx := encPair enc (encPair encUnary encSt)
  have hfCtx := hf.comp' (ComputableInPolyTime.fst enc (encPair encUnary encSt))
  have hattOpt := isPPTOn_gmwSimAttemptOpt hg hlen hfCtx
    (isOraclePPTOn_VstarSession (α := α) (enc := enc) machine)
  have hsingle := hattOpt.preprocess
    (hn.prod ((ha.prod (hlimit.prod hst)).prod (.const ([] : List Bool))))
  have hfirst := computableInPolyTime_firstSuccess (enc := encSt)
    (hst.comp' (.fst input (encList (encOption encSt))))
    (.snd input (encList (encOption encSt)))
  have hres := (hsingle.replicate hatt).map_with (f := fun p xs => firstSuccess (st p) xs) hfirst
  exact (congrArg (IsPPTOn _ _) (by funext p; rfl)).mp hres

theorem mem_support_simSessionStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ)
    {st st' : ℕ × FiniteConfig tapes Bool Control Unit}
    (hst' : st' ∈ (ProbComp.eval (simSessionStep machine generator s m limit att φ st)).support) :
    st' = st ∨ st' ∈ OracleComp.support (sessionStep machine limit st.1 2 st.2) := by
  simp only [simSessionStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hst'
  obtain ⟨xs, hxs, rfl⟩ := hst'
  rcases firstSuccess_mem_or_eq st xs with h | h
  · exact Or.inl h
  · exact Or.inr (mem_support_gmwSimAttemptOpt generator s m φ _
      (mem_support_of_mem_replicate hxs h))

theorem isPPTOn_iterate_simSessionStep_finishSessionRun {α Param : Type}
    {enc : α ↪ List Bool} {input : Param ↪ List Bool}
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {n T att K : Param → ℕ} {a : Param → α} {word : Param → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hn : ComputableInPolyTime n input encUnary)
    (hT : ComputableInPolyTime T input encUnary)
    (hatt : ComputableInPolyTime att input encUnary)
    (hK : ComputableInPolyTime K input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hword : ComputableInPolyTime word input encBits) :
    IsPPTOn input encBits (fun p => do
      let st' ← OracleComp.iterate (K p)
        (simSessionStep machine generator (n p + 7) (length (n p + 7)) (T p) (att p) (f (a p)))
        (T p, FiniteConfig.init machine.initial (word p))
      finishSessionRun machine (T p) st') := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := tapes) (State := Control) (Oracle := Unit)
  let inv (p : Param) (_ : ℕ) (st : ℕ × FiniteConfig tapes Bool Control Unit) : Prop :=
    st.1 ≤ T p ∧ FiniteConfig.SpaceBound (word p).length (T p - st.1) (T p) st.2
  have hbase (p : Param) : inv p 0 (T p, FiniteConfig.init machine.initial (word p)) :=
    ⟨le_rfl, by simpa only [Nat.sub_self] using
      FiniteConfig.spaceBound_init machine.initial (word p) (T p)⟩
  have hpres (p : Param) (i : ℕ) (st : ℕ × FiniteConfig tapes Bool Control Unit)
      (_ : i < K p) (hst : inv p i st)
      (next : ℕ × FiniteConfig tapes Bool Control Unit)
      (hnext : next ∈ (ProbComp.eval (simSessionStep machine generator
        (n p + 7) (length (n p + 7)) (T p) (att p) (f (a p)) st)).support) :
      inv p (i + 1) next := by
    rcases mem_support_simSessionStep machine generator (n p + 7) (length (n p + 7))
        (T p) (att p) (f (a p)) hnext with rfl | hmem
    · exact hst
    · exact mem_support_sessionStep machine (T p) 2 hst.1 hst.2 hmem
  have hp1 := ComputableInPolyTime.fst input encSt
  have hp2 := ComputableInPolyTime.snd input encSt
  have hstep := isPPTOn_simSessionStep machine hg hlen hf
    (hn.comp' hp1) (hT.comp' hp1) (hatt.comp' hp1) (ha.comp' hp1) hp2
  have hTPoly : PolyBounded (fun p => (input p).length) T := by
    simpa only [encUnary_apply, List.length_replicate] using hT.polyBounded_length
  have hwordPoly : PolyBounded (fun p => (input p).length) (fun p => (word p).length) := by
    simpa only [encBits_apply] using hword.polyBounded_length
  have hsizePoly : PolyBounded (fun p => (input p).length)
      (fun p => (2 * cf + 3) * ((word p).length + T p + 1)) :=
    (PolyBounded.const (2 * cf + 3)).mul ((hwordPoly.add hTPoly).add (.const 1))
  have hinit := hT.tidy.prod
    (ComputableTidilyInPolyTime.finiteConfig_init (k := tapes) (Oracle := Unit)
      hword.tidy machine.initial)
  have hiter := (IsPPTOn.iterateWith_spec (input := input) (stateEncoding := encSt)
    (count := K) (initial := fun p => (T p, FiniteConfig.init machine.initial (word p)))
    (step := fun p => simSessionStep machine generator (n p + 7) (length (n p + 7))
      (T p) (att p) (f (a p)))
    hK.tidy hinit hstep inv hbase hpres hsizePoly
    (by
      intro p i st _ ⟨h1, h2⟩
      have hcfg : (encFiniteConfig st.2).length ≤ cf * (2 * ((word p).length + T p + 1)) :=
        (hcf (word p).length (T p - st.1) (T p) st.2 h2).trans (Nat.mul_le_mul_left cf (by omega))
      have hstlen : (encSt st).length = 2 * st.1 + 1 + (encCfg st.2).length := by
        simp only [encSt, length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [encCfg] at hstlen
      rw [Nat.add_mul, Nat.mul_assoc, show 2 * (cf * ((word p).length + T p + 1)) =
        cf * (2 * ((word p).length + T p + 1)) by ring]
      omega)).1
  have hfinish := (isPPTOn_finishSessionRun machine).preprocess ((hT.comp' hp1).prod hp2)
  have hres := hiter.bind_with (second := fun p st' => finishSessionRun machine (T p) st') hfinish
  exact (congrArg (IsPPTOn _ _) (by funext p; rfl)).mp hres

theorem length_enc_of_mem_support_sessionStep {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit) :
    ∃ C : ℕ, ∀ (limit q : ℕ) (st res : ℕ × FiniteConfig tapes Bool Control Unit),
      res ∈ OracleComp.support (sessionStep machine limit st.1 q st.2) →
      (encOption (encPair encUnary encFiniteConfig) (some res)).length ≤
        C * (limit + (encPair encUnary encFiniteConfig st).length + 1) := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := tapes) (State := Control) (Oracle := Unit)
  refine ⟨4 * cf + 6, fun limit q st res hres => ?_⟩
  let L₀ := (encCfg st.2).length
  let T₀ := L₀ + st.1
  have hbase : FiniteConfig.SpaceBound L₀ (T₀ - st.1) limit st.2 := by
    rw [show T₀ - st.1 = L₀ from Nat.add_sub_cancel _ _]
    exact (spaceBound_of_encFiniteConfig st.2).mono le_rfl le_rfl (Nat.zero_le _)
  obtain ⟨hrem, hsb⟩ := mem_support_sessionStep machine limit q
    (T := T₀) (by dsimp [T₀]; omega) hbase hres
  have hst_len : (encSt st).length = 2 * st.1 + 1 + L₀ := by
    simp only [encSt, L₀, length_encPair, encUnary_apply, List.length_replicate]
  have hres_len : (encOption encSt (some res)).length =
      2 * res.1 + 1 + (encCfg res.2).length + 1 := by
    simp [encOption, encSt]
  have hT : T₀ - res.1 ≤ L₀ + st.1 := by dsimp [T₀]; omega
  have hrem' : res.1 ≤ L₀ + st.1 := hrem
  have hcfg : (encFiniteConfig res.2).length ≤ cf * (2 * (limit + (encSt st).length + 1)) :=
    (hcf L₀ (T₀ - res.1) limit res.2 hsb).trans (Nat.mul_le_mul_left cf (by omega))
  dsimp only [encCfg, encSt] at hres_len hst_len hcfg ⊢
  rw [Nat.add_mul, show 4 * cf = 2 * (cf * 2) by omega, Nat.mul_assoc, Nat.mul_assoc]
  omega

theorem isPPTOn_attemptWithPadsStep {α Param : Type}
    {enc : α ↪ List Bool} {input : Param ↪ List Bool}
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    {generator : List Bool → List Bool} {f : α → CNF ℕ}
    {n s m limit : Param → ℕ} {a : Param → α} {w : Param → List Bool}
    {st : Param → ℕ × FiniteConfig tapes Bool Control Unit}
    {state : Param → Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hf : ComputableInPolyTime f enc encCNF)
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hlimit : ComputableInPolyTime limit input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hw : ComputableInPolyTime w input encBits)
    (hst : ComputableInPolyTime st input (encPair encUnary encFiniteConfig))
    (hstate : ComputableInPolyTime state input
      (encPair (encOption (encPair encUnary encFiniteConfig)) (encList encBits))) :
    IsPPTOn input (encPair (encOption (encPair encUnary encFiniteConfig)) (encList encBits))
      (fun p => attemptWithPadsStep machine generator (s p) (m p) (limit p)
        (f (a p)) (w p) (st p) (state p)) := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  have htotal := (computableInPolyTime_totalLen hf).comp' ha
  have htake := (ComputableTidilyInPolyTime.takeUnary encBits).computableInPolyTime.comp'
    (hstate.snd'.prod htotal)
  have hreal := isPPTOn_gmwRealWithPadsOpt hg
    (isOraclePPTOn_VstarSession (α := α) (enc := enc) machine)
    hn hs hm (ha.prod (hlimit.prod hst)) (.const ([] : List Bool)) hw (hf.comp' ha) htake
  have hp1 := ComputableInPolyTime.fst input (encOption encSt)
  have hp2 := ComputableInPolyTime.snd input (encOption encSt)
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := encBits)
    (encL := encList encBits)).computableInPolyTime.comp'
    ((hstate.comp' hp1).snd'.prod (htotal.comp' hp1))
  have hpost := (computableInPolyTime_optionOr (hstate.comp' hp1).fst' hp2).prod hdrop
  have hres := hreal.map_with
    (f := fun p res => ((state p).1.or res, (state p).2.drop (totalLen (f (a p))))) hpost
  exact (congrArg (IsPPTOn _ _) (by funext p; simp only [attemptWithPadsStep, VstarSession,
    bind_pure_comp])).mp hres

theorem mem_support_attemptWithPadsStep {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig tapes Bool Control Unit)
    {state next : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)}
    (hnext : next ∈
      (ProbComp.eval (attemptWithPadsStep machine generator s m limit φ w st state)).support) :
    (∀ v, next.1 = some v →
      state.1 = some v ∨ v ∈ OracleComp.support (sessionStep machine limit st.1 2 st.2)) ∧
    (encList encBits next.2).length ≤ (encList encBits state.2).length := by
  simp only [attemptWithPadsStep, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hnext
  obtain ⟨res, hres, rfl⟩ := hnext
  refine ⟨fun v hv => ?_, length_encList_sublist encBits (List.drop_sublist _ _)⟩
  dsimp only at hv
  cases h1 : state.1 with
  | some u => rw [h1] at hv; exact Or.inl hv
  | none =>
    rw [h1] at hv; simp only [Option.or] at hv; subst hv
    exact Or.inr (mem_support_gmwRealWithPadsOpt generator s m φ w _ _ hres)

theorem isPPTOn_sessionWithPadsStep_and_support {α Param : Type}
    {enc : α ↪ List Bool} {input : Param ↪ List Bool}
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    {generator : List Bool → List Bool} {f : α → CNF ℕ}
    {n s m limit att : Param → ℕ} {a : Param → α} {w : Param → List Bool}
    {state : Param → (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hf : ComputableInPolyTime f enc encCNF)
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hlimit : ComputableInPolyTime limit input encUnary)
    (hatt : ComputableInPolyTime att input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hw : ComputableInPolyTime w input encBits)
    (hstate : ComputableInPolyTime state input
      (encPair (encPair encUnary encFiniteConfig) (encList encBits))) :
    IsPPTOn input (encPair (encPair encUnary encFiniteConfig) (encList encBits))
      (fun p => sessionWithPadsStep machine generator (s p) (m p) (limit p) (att p)
        (f (a p)) (w p) (state p)) ∧
    ∀ p next, next ∈ (ProbComp.eval (sessionWithPadsStep machine generator
        (s p) (m p) (limit p) (att p) (f (a p)) (w p) (state p))).support →
      (next.1 = (state p).1 ∨
        next.1 ∈ OracleComp.support
          (sessionStep machine (limit p) (state p).1.1 2 (state p).1.2)) ∧
      (encList encBits next.2).length ≤ (encList encBits (state p).2).length := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  let encLoop := encPair (encOption encSt) (encList encBits)
  obtain ⟨C, hC⟩ := length_enc_of_mem_support_sessionStep machine
  let inv (p : Param) (_ : ℕ)
      (cur : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) : Prop :=
    (∀ v, cur.1 = some v →
      v ∈ OracleComp.support (sessionStep machine (limit p) (state p).1.1 2 (state p).1.2)) ∧
    (encList encBits cur.2).length ≤ (encList encBits (state p).2).length
  have hbase (p : Param) : inv p 0 (none, (state p).2) := ⟨by rintro _ ⟨⟩, le_rfl⟩
  have hpres (p : Param) (i : ℕ)
      (cur : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool))
      (_ : i < att p) (hcur : inv p i cur)
      (next : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool))
      (hnext : next ∈ (ProbComp.eval (attemptWithPadsStep machine generator
        (s p) (m p) (limit p) (f (a p)) (w p) (state p).1 cur)).support) :
      inv p (i + 1) next := by
    obtain ⟨h1, h2⟩ := mem_support_attemptWithPadsStep machine generator
      (s p) (m p) (limit p) (f (a p)) (w p) (state p).1 hnext
    refine ⟨fun v hv => ?_, h2.trans hcur.2⟩
    rcases h1 v hv with hprev | hmem
    · exact hcur.1 v hprev
    · exact hmem
  have hp1 := ComputableInPolyTime.fst input encLoop
  have hp2 := ComputableInPolyTime.snd input encLoop
  have hstep := isPPTOn_attemptWithPadsStep machine hg hf
    (hn.comp' hp1) (hs.comp' hp1) (hm.comp' hp1) (hlimit.comp' hp1)
    (ha.comp' hp1) (hw.comp' hp1) (hstate.comp' hp1).fst' hp2
  have hlimPoly : PolyBounded (fun p => (input p).length) limit := by
    simpa only [encUnary_apply, List.length_replicate] using hlimit.polyBounded_length
  have hstPoly : PolyBounded (fun p => (input p).length)
      (fun p => (encSt (state p).1).length) := (hstate.fst').polyBounded_length
  have hpadsPoly : PolyBounded (fun p => (input p).length)
      (fun p => (encList encBits (state p).2).length) := (hstate.snd').polyBounded_length
  have hsizePoly : PolyBounded (fun p => (input p).length)
      (fun p => 2 * (C * (limit p + (encSt (state p).1).length + 1) + 1) +
        (encList encBits (state p).2).length) :=
    ((PolyBounded.const 2).mul
      (((PolyBounded.const C).mul ((hlimPoly.add hstPoly).add (.const 1))).add (.const 1))).add
      hpadsPoly
  have hinit := ((ComputableInPolyTime.const (encOut := encOption encSt)
    (none : Option (ℕ × FiniteConfig tapes Bool Control Unit))).prod hstate.snd').tidy
  have hiter := IsPPTOn.iterateWith_spec (input := input) (stateEncoding := encLoop)
    (count := att) (initial := fun p => (none, (state p).2))
    (step := fun p => attemptWithPadsStep machine generator (s p) (m p) (limit p)
      (f (a p)) (w p) (state p).1)
    hatt.tidy hinit hstep inv hbase hpres hsizePoly
    (by
      intro p i cur _ ⟨h1, h2⟩
      have hcur_len : (encLoop cur).length =
          2 * (encOption encSt cur.1).length + 1 + (encList encBits cur.2).length := by
        simp only [encLoop, length_encPair]
      have hopt : (encOption encSt cur.1).length ≤
          C * (limit p + (encSt (state p).1).length + 1) := by
        cases hopt_eq : cur.1 with
        | none => simp [encOption]
        | some v => exact hC (limit p) 2 (state p).1 v (h1 v hopt_eq)
      omega)
  refine ⟨?_, fun p next hnext => ?_⟩
  · have hgetD := (hp2.fst'.tidy.optionGetDWithInput
      (hstate.comp' hp1).fst'.tidy).computableInPolyTime
    have hpost := hgetD.prod hp2.snd'
    have hres := hiter.1.map_with
      (f := fun (p : Param)
        (cur : Option (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) =>
        (cur.1.getD (state p).1, cur.2)) hpost
    exact (congrArg (IsPPTOn _ _) (by funext p; simp only [sessionWithPadsStep,
      bind_pure_comp])).mp hres
  · simp only [sessionWithPadsStep, bind_pure_comp, ProbComp.eval_map,
      PMF.mem_support_map_iff] at hnext
    obtain ⟨cur, hcur, rfl⟩ := hnext
    obtain ⟨h1, h2⟩ := hiter.2 p cur hcur
    refine ⟨?_, h2⟩
    cases hopt : cur.1 with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (h1 v hopt)

theorem isPPTOn_runAllSessionsWithPads {α Param : Type}
    {enc : α ↪ List Bool} {input : Param ↪ List Bool}
    {tapes : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit)
    {generator : List Bool → List Bool} {f : α → CNF ℕ}
    {n s m T att K : Param → ℕ} {a : Param → α} {w word : Param → List Bool}
    {pads : Param → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hf : ComputableInPolyTime f enc encCNF)
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hT : ComputableInPolyTime T input encUnary)
    (hatt : ComputableInPolyTime att input encUnary)
    (hK : ComputableInPolyTime K input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hw : ComputableInPolyTime w input encBits)
    (hword : ComputableInPolyTime word input encBits)
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    IsPPTOn input encBits (fun p =>
      runAllSessionsWithPads machine generator (s p) (m p) (T p) (att p) (K p)
        (f (a p)) (w p) (word p) (pads p)) := by
  let encCfg := encFiniteConfig (k := tapes) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary encCfg
  let encOuter := encPair encSt (encList encBits)
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := tapes) (State := Control) (Oracle := Unit)
  have hp1 := ComputableInPolyTime.fst input encOuter
  have hp2 := ComputableInPolyTime.snd input encOuter
  have hstep_and_supp := isPPTOn_sessionWithPadsStep_and_support machine hg hf
    (hn.comp' hp1) (hs.comp' hp1) (hm.comp' hp1) (hT.comp' hp1) (hatt.comp' hp1)
    (ha.comp' hp1) (hw.comp' hp1) hp2
  let inv (p : Param) (_ : ℕ)
      (cur : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) : Prop :=
    cur.1.1 ≤ T p ∧
    FiniteConfig.SpaceBound (word p).length (T p - cur.1.1) (T p) cur.1.2 ∧
    (encList encBits cur.2).length ≤ (encList encBits (pads p)).length
  have hbase (p : Param) :
      inv p 0 ((T p, FiniteConfig.init machine.initial (word p)), pads p) :=
    ⟨le_rfl, by simpa only [Nat.sub_self] using
      FiniteConfig.spaceBound_init machine.initial (word p) (T p), le_rfl⟩
  have hpres (p : Param) (i : ℕ)
      (cur : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool))
      (_ : i < K p) (hcur : inv p i cur)
      (next : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool))
      (hnext : next ∈ (ProbComp.eval (sessionWithPadsStep machine generator
        (s p) (m p) (T p) (att p) (f (a p)) (w p) cur)).support) :
      inv p (i + 1) next := by
    obtain ⟨h1, h2⟩ := hstep_and_supp.2 (p, cur) next hnext
    dsimp only at h1 h2
    rcases h1 with hst_eq | hmem
    · exact ⟨hst_eq ▸ hcur.1, hst_eq ▸ hcur.2.1, h2.trans hcur.2.2⟩
    · obtain ⟨hrem, hsb⟩ := mem_support_sessionStep machine (T p) 2 hcur.1 hcur.2.1 hmem
      exact ⟨hrem, hsb, h2.trans hcur.2.2⟩
  have hTPoly : PolyBounded (fun p => (input p).length) T := by
    simpa only [encUnary_apply, List.length_replicate] using hT.polyBounded_length
  have hwordPoly : PolyBounded (fun p => (input p).length) (fun p => (word p).length) := by
    simpa only [encBits_apply] using hword.polyBounded_length
  have hpadsPoly : PolyBounded (fun p => (input p).length)
      (fun p => (encList encBits (pads p)).length) := hpads.polyBounded_length
  have hsizePoly : PolyBounded (fun p => (input p).length)
      (fun p => 2 * ((2 * cf + 3) * ((word p).length + T p + 1)) + 1 +
        (encList encBits (pads p)).length) :=
    (((PolyBounded.const 2).mul
      ((PolyBounded.const (2 * cf + 3)).mul ((hwordPoly.add hTPoly).add (.const 1)))).add
      (.const 1)).add hpadsPoly
  have hinit := (hT.tidy.prod
    (ComputableTidilyInPolyTime.finiteConfig_init (k := tapes) (Oracle := Unit)
      hword.tidy machine.initial)).prod
    hpads.tidy
  have hiter := (IsPPTOn.iterateWith_spec (input := input) (stateEncoding := encOuter)
    (count := K)
    (initial := fun p => ((T p, FiniteConfig.init machine.initial (word p)), pads p))
    (step := fun p => sessionWithPadsStep machine generator (s p) (m p) (T p) (att p)
      (f (a p)) (w p))
    hK.tidy hinit hstep_and_supp.1 inv hbase hpres hsizePoly
    (by
      intro p i cur _ ⟨h1, h2, h3⟩
      have hcfg : (encFiniteConfig cur.1.2).length ≤ cf * (2 * ((word p).length + T p + 1)) :=
        (hcf (word p).length (T p - cur.1.1) (T p) cur.1.2 h2).trans
          (Nat.mul_le_mul_left cf (by omega))
      have houtlen : (encOuter cur).length =
          2 * (2 * cur.1.1 + 1 + (encCfg cur.1.2).length) + 1 +
            (encList encBits cur.2).length := by
        simp only [encOuter, encSt, length_encPair, encUnary_apply, List.length_replicate]
      dsimp only [encCfg] at houtlen
      rw [Nat.add_mul, Nat.mul_assoc, show 2 * (cf * ((word p).length + T p + 1)) =
        cf * (2 * ((word p).length + T p + 1)) by ring]
      omega)).1
  have hfinish := (isPPTOn_finishSessionRun machine).preprocess ((hT.comp' hp1).prod hp2.fst')
  have hres := hiter.bind_with
    (second := fun (p : Param)
      (cur : (ℕ × FiniteConfig tapes Bool Control Unit) × List (List Bool)) =>
      finishSessionRun machine (T p) cur.1) hfinish
  exact (congrArg (IsPPTOn _ _) (by funext p; rfl)).mp hres

/-! ### Step 4: Multi-session simulator `gmwSeqSimulator` and reduction `gmwSeqViewReduction` -/

/-- Witness-free multi-session simulator for the `k n`-fold sequentially composed GMW protocol.
For any uniform strict oracle PPT malicious verifier `Vstar` (`IsOraclePPTOn`), it extracts a
realizing multi-tape probabilistic oracle Turing machine and polynomial clock, executes `k n`
sequential simulated sessions (`simSessionStep` with `n + 1` attempts per session) on the machine
configuration, and finishes any remaining machine steps with `finishSessionRun`. -/
noncomputable def gmwSeqSimulator {α : Type} (enc : α ↪ List Bool)
    (generator : List Bool → List Bool) (length : ℕ → ℕ) (f : α → CNF ℕ) (k : ℕ → ℕ)
    (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) := by
  classical
  let encIn := encPair encUnary (encPair enc encBits)
  by_cases hV : IsOraclePPTOn encIn encBits (fun (n, a, z) => Vstar n a z)
  · let tapes := hV.2.choose
    let Control := hV.2.choose_spec.choose
    letI : Finite Control := hV.2.choose_spec.choose_spec.choose
    let machine := hV.2.choose_spec.choose_spec.choose_spec.choose
    let c := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose
    let d := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    let word := encIn (n, a, z)
    let T := c * (word.length + 1) ^ d
    exact do
      let st' ← OracleComp.iterate (k n)
        (simSessionStep machine generator (n + 7) (length (n + 7)) T (n + 1) (f a))
        (T, FiniteConfig.init machine.initial word)
      finishSessionRun machine T st'
  · exact pure []

/-- `gmwSeqSimulator` is a uniform strict PPT program whenever `generator`, `f`, and `k` are
polynomial-time computable and `Vstar` is uniform strict oracle PPT. -/
theorem isPPTOn_gmwSeqSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => gmwSeqSimulator enc generator length f k Vstar n a z) := by
  let encIn := encPair encUnary (encPair enc encBits)
  let tapes := hV.2.choose
  let Control := hV.2.choose_spec.choose
  have : Finite Control := hV.2.choose_spec.choose_spec.choose
  let machine := hV.2.choose_spec.choose_spec.choose_spec.choose
  let c := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let d := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hword : ComputableInPolyTime encIn encIn encBits :=
    ComputableInPolyTime.of_eq fun _ => rfl
  have hclockBits := (ComputableInPolyTime.const c).unary_mul'
    ((ComputableInPolyTime.unary_pow d).comp'
      (ComputableInPolyTime.length_bits.unary_add' (.const 1)))
  have hT := hclockBits.comp' hword
  have hn := ComputableInPolyTime.fst encUnary (encPair enc encBits)
  have ha := (ComputableInPolyTime.snd encUnary (encPair enc encBits)).fst'
  have hmain := isPPTOn_iterate_simSessionStep_finishSessionRun machine
    hg hlen hf hn hT (hn.unary_add' (.const 1)) (hk.comp' hn) ha hword
  exact (congrArg (IsPPTOn _ _) (by
    funext ⟨n, a, z⟩
    simp only [gmwSeqSimulator, encIn, hV, ↓reduceDIte, machine, c, d])).mp hmain

/-- Single-challenge PRG distinguisher for the `k n`-session GMW view hybrid.
It uses `sequenceTest` to splice `challenge` into the flat sequence of
`k n * ((n + 1) * totalLen (f a))` unopened pads, runs `runAllSessionsWithPads` on the verifier's
realizing machine, and passes the resulting view to `adversary n a z`. -/
noncomputable def gmwSeqViewReduction {α : Type} (enc : α ↪ List Bool)
    (generator : List Bool → List Bool) (length : ℕ → ℕ) (f : α → CNF ℕ) (k : ℕ → ℕ)
    (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (adversary : ℕ → α → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) (a : α) (w z : List Bool) (challenge : List Bool) : ProbComp Bool := by
  classical
  let encIn := encPair encUnary (encPair enc encBits)
  by_cases hV : IsOraclePPTOn encIn encBits (fun (n, a, z) => Vstar n a z)
  · let tapes := hV.2.choose
    let Control := hV.2.choose_spec.choose
    letI : Finite Control := hV.2.choose_spec.choose_spec.choose
    let machine := hV.2.choose_spec.choose_spec.choose_spec.choose
    let c := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose
    let d := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    let word := encIn (n, a, z)
    let T := c * (word.length + 1) ^ d
    exact sequenceTest
      (BitString.sampleList (length (n + 7)))
      (generator <$> BitString.sampleList (n + 7))
      (k n * ((n + 1) * totalLen (f a)))
      (fun pads => do
        let view ← runAllSessionsWithPads machine generator
          (n + 7) (length (n + 7)) T (n + 1) (k n) (f a) w word pads
        adversary n a z view)
      challenge
  · exact pure false

private theorem eval_gmwSeqInteract_eq_machine_of_isOraclePPTOn {α : Type} {enc : α ↪ List Bool}
    (generator : List Bool → List Bool) (s m K : ℕ) (φ : CNF ℕ) (w : List Bool)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {tapes : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM tapes Bool Control Unit) (c d : ℕ)
    (hspec : ∀ (p : ℕ × α × List Bool) (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) st,
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (encBits <$> Vstar p.1 p.2.1 p.2.2)).run st =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (machine.runOracle
            (c * ((encPair encUnary (encPair enc encBits) p).length + 1) ^ d)
            (encPair encUnary (encPair enc encBits) p))).run st)
    (n : ℕ) (a : α) (z : List Bool) :
    ProbComp.eval (gmwSeqInteract generator s m φ w K (Vstar n a z)) =
      ProbComp.eval (gmwSeqInteract generator s m φ w K
        (machine.runOracle
          (c * ((encPair encUnary (encPair enc encBits) (n, a, z)).length + 1) ^ d)
          (encPair encUnary (encPair enc encBits) (n, a, z)))) := by
  simp only [gmwSeqInteract, ProbComp.eval_bind, eval_runSeq]
  refine congrArg (PMF.bind _) (funext fun coinsList => congrArg (PMF.map Prod.fst) ?_)
  have h := hspec (n, a, z) (Bool × List (List Bool × List (List Bool)))
    (fun q state => PMF.pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 state))
    (false, coinsList)
  simpa only [encBits, Function.Embedding.coe_refl, id_map, ProbOracleComp.runWith,
    OracleComp.runWith] using h

/-- **Pointwise finite multi-session GMW view reduction** for every valid instance, witness, and
auxiliary word. Across `k n` sequential executions, the distinguishing advantage between the real
view of any uniform strict oracle PPT malicious verifier `Vstar` and `gmwSeqSimulator` is bounded
by `(k n : ℝ≥0) * (7 / 8) ^ (n + 1)` plus `dyadicSize (k n * ((n + 1) * totalLen (f a)))` times
the PRG advantage of `gmwSeqViewReduction` at seed length `n + 7`. -/
theorem gmwSeqView_advantage_le {α : Type} {enc : α ↪ List Bool}
    (generator : List Bool → List Bool) (length : ℕ → ℕ) (f : α → CNF ℕ) (k : ℕ → ℕ)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (adversary : ℕ → α → List Bool → List Bool → ProbComp Bool)
    (n : ℕ) (a : α) (w z : List Bool) (hw : ThreeSAT.verifier (f a, w) = true) :
    Game.advantage
        (distinguishingGame
          (((gmwSeqProver generator (n + 7) (length (n + 7)) (f a) w (k n)).run (Vstar n a z)
            (gmwSeqProver generator (n + 7) (length (n + 7)) (f a) w (k n)).init).map Prod.fst)
          (adversary n a z))
        (distinguishingGame
          (ProbComp.eval (gmwSeqSimulator enc generator length f k Vstar n a z))
          (adversary n a z)) ≤
      (k n : ℝ≥0) * (7 / 8 : ℝ≥0) ^ (n + 1) +
        (dyadicSize (k n * ((n + 1) * totalLen (f a))) : ℝ≥0) *
          Game.advantage
            (ProbComp.eval ((generator <$> BitString.sampleList (n + 7)) >>=
              gmwSeqViewReduction enc generator length f k Vstar adversary n a w z))
            (ProbComp.eval (BitString.sampleList (length (n + 7)) >>=
              gmwSeqViewReduction enc generator length f k Vstar adversary n a w z)) := by
  let encIn := encPair encUnary (encPair enc encBits)
  let tapes := hV.2.choose
  let Control := hV.2.choose_spec.choose
  have : Finite Control := hV.2.choose_spec.choose_spec.choose
  let machine := hV.2.choose_spec.choose_spec.choose_spec.choose
  let c := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let d := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hspec := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  let word := encIn (n, a, z)
  let T := c * (word.length + 1) ^ d
  let s := n + 7
  let m := length (n + 7)
  let att := n + 1
  let K := k n
  let φ := f a
  let st₀ : ℕ × FiniteConfig tapes Bool Control Unit :=
    (T, FiniteConfig.init machine.initial word)
  let post : ℕ × FiniteConfig tapes Bool Control Unit → PMF Bool :=
    fun st' => (ProbComp.eval (finishSessionRun machine T st')).bind
      (fun view => ProbComp.eval (adversary n a z view))
  have hreal_eq : distinguishingGame
      (((gmwSeqProver generator s m φ w K).run (Vstar n a z)
        (gmwSeqProver generator s m φ w K).init).map Prod.fst)
      (adversary n a z) =
    (ProbComp.eval (OracleComp.iterate K
      (realSessionStep machine generator s m T φ w) st₀)).bind post := by
    rw [← eval_gmwSeqInteract,
      eval_gmwSeqInteract_eq_machine_of_isOraclePPTOn generator s m K φ w machine c d hspec n a z,
      eval_gmwSeqInteract_runOracle_eq_iterate_realSessionStep]
    simp only [distinguishingGame, post, st₀, T, word, encIn, ProbComp.eval_bind,
      PMF.monad_bind_eq_bind, PMF.bind_bind]
    rfl
  let guessGame : Game :=
    (ProbComp.eval (OracleComp.iterate K
      (realPRGPadsSessionStep machine generator s m T att φ w) st₀)).bind post
  have hsim_eq : distinguishingGame
      (ProbComp.eval (gmwSeqSimulator enc generator length f k Vstar n a z))
      (adversary n a z) =
    (ProbComp.eval (OracleComp.iterate K
      (simSessionStep machine generator s m T att φ) st₀)).bind post := by
    simp only [gmwSeqSimulator, encIn, hV, ↓reduceDIte, machine, c, d,
      distinguishingGame, post, st₀, T, word, s, m, att, K, φ,
      ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
    rfl
  have h1 : Game.advantage
      ((ProbComp.eval (OracleComp.iterate K
        (realSessionStep machine generator s m T φ w) st₀)).bind post)
      guessGame ≤ (K : ℝ≥0) * (7 / 8 : ℝ≥0) ^ att :=
    advantage_iterate_realSessionStep_realPRGPadsSessionStep_le
      machine generator s m T att φ w K st₀ post
  let testPads : List (List Bool) → ProbComp Bool := fun pads => do
    let view ← runAllSessionsWithPads machine generator s m T att K φ w word pads
    adversary n a z view
  have hprg_eq : ProbComp.eval
      (OracleComp.replicate (K * (att * totalLen φ))
        (generator <$> BitString.sampleList s) >>= testPads) = guessGame := by
    have h := congrArg
      (fun d => d.bind (fun view => ProbComp.eval (adversary n a z view)))
      (eval_replicate_runAllSessionsWithPads_prg machine generator s m T att K φ w word)
    simpa only [testPads, guessGame, post, st₀, ProbComp.eval_bind, PMF.bind_bind] using h
  have hunif_eq : ProbComp.eval
      (OracleComp.replicate (K * (att * totalLen φ))
        (BitString.sampleList m) >>= testPads) =
      (ProbComp.eval (OracleComp.iterate K
        (simSessionStep machine generator s m T att φ) st₀)).bind post := by
    have h := congrArg
      (fun d => d.bind (fun view => ProbComp.eval (adversary n a z view)))
      (eval_replicate_runAllSessionsWithPads_uniform machine generator s m T att K φ w word hw)
    simpa only [testPads, post, st₀, ProbComp.eval_bind, PMF.bind_bind] using h
  have hseq := sequenceTest_advantage
    (BitString.sampleList m) (generator <$> BitString.sampleList s)
    (K * (att * totalLen φ)) testPads
  rw [hprg_eq, hunif_eq] at hseq
  have hred_eq : sequenceTest (BitString.sampleList m) (generator <$> BitString.sampleList s)
      (K * (att * totalLen φ)) testPads =
      gmwSeqViewReduction enc generator length f k Vstar adversary n a w z := by
    funext challenge
    simp only [gmwSeqViewReduction, encIn, hV, ↓reduceDIte, machine, c, d,
      testPads, word, T, s, m, att, K, φ]
  rw [hred_eq] at hseq
  rw [hreal_eq, hsim_eq, ← hseq]
  exact (Game.advantage_triangle _ guessGame _).trans (add_le_add_left h1 _)

private theorem isPPTOn_gmwSeqViewReduction_aux {α Aux : Type}
    {enc : α ↪ List Bool} {encAux : Aux ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    {zV zA : Aux → List Bool}
    (hzV : ComputableInPolyTime zV encAux encBits)
    (hzA : ComputableInPolyTime zA encAux encBits)
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view)) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits encAux))) encBits) encBool
      (fun ((n, a, w, aux), challenge) =>
        gmwSeqViewReduction enc generator length f k Vstar
          (fun n a _ view => adversary n a (zA aux) view) n a w (zV aux) challenge) := by
  let encIn := encPair encUnary (encPair enc encBits)
  let input := encPair encUnary (encPair enc (encPair encBits encAux))
  let tapes := hV.2.choose
  let Control := hV.2.choose_spec.choose
  have : Finite Control := hV.2.choose_spec.choose_spec.choose
  let machine := hV.2.choose_spec.choose_spec.choose_spec.choose
  let c := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let d := hV.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have htotal := computableInPolyTime_totalLen hf
  have hlength := PRG.polyTime_length hg hlen
  have hn_in := ComputableInPolyTime.fst encUnary (encPair enc (encPair encBits encAux))
  have hrest_in := ComputableInPolyTime.snd encUnary (encPair enc (encPair encBits encAux))
  have ha_in := hrest_in.fst'
  have hw_in := hrest_in.snd'.fst'
  have haux_in := hrest_in.snd'.snd'
  let wordFn (p : ℕ × (α × (List Bool × Aux))) : List Bool :=
    encIn (p.1, p.2.1, zV p.2.2.2)
  have hwordFn : ComputableInPolyTime wordFn input encBits :=
    (ComputableInPolyTime.of_eq (encIn := encIn) (encOut := encBits) fun _ => rfl).comp'
      (hn_in.prod (ha_in.prod (hzV.comp' haux_in)))
  have hclockBits := (ComputableInPolyTime.const c).unary_mul'
    ((ComputableInPolyTime.unary_pow d).comp'
      (ComputableInPolyTime.length_bits.unary_add' (.const 1)))
  have hTFn := hclockBits.comp' hwordFn
  let encTestIn := encPair (encPair input encBits) (encList encBits)
  have hqp := (ComputableInPolyTime.fst (encPair input encBits) (encList encBits)).fst'
  have hqn := hn_in.comp' hqp
  have hqs := hqn.unary_add' (.const 7)
  have hrun := isPPTOn_runAllSessionsWithPads machine hg hf
    hqn hqs (hlength.comp' hqs) (hTFn.comp' hqp) (hqn.unary_add' (.const 1)) (hk.comp' hqn)
    (ha_in.comp' hqp) (hw_in.comp' hqp) (hwordFn.comp' hqp)
    (.snd (encPair input encBits) (encList encBits))
  have hrp := (ComputableInPolyTime.fst encTestIn encBits).fst'.fst'
  have hadvPrep := hadv.preprocess
    (((hn_in.comp' hrp).prod ((ha_in.comp' hrp).prod (hzA.comp' (haux_in.comp' hrp)))).prod
      (.snd encTestIn encBits))
  have htest := hrun.bind_with
    (second := fun (q : ((ℕ × (α × (List Bool × Aux))) × List Bool) × List (List Bool))
      (view : List Bool) => adversary q.1.1.1 q.1.1.2.1 (zA q.1.1.2.2.2) view) hadvPrep
  have hp1 := ComputableInPolyTime.fst input encBits
  have hn1 := hn_in.comp' hp1
  have hs1 := hn1.unary_add' (.const 7)
  have hm1 := hlength.comp' hs1
  have ha1 := ha_in.comp' hp1
  have hcount1 := (hk.comp' hn1).unary_mul'
    ((hn1.unary_add' (.const 1)).unary_mul' (htotal.comp' ha1))
  have hseq := isPPTOn_sequenceTest (input := encPair input encBits) (sample := encBits)
    (replacement := fun p => BitString.sampleList (length (p.1.1 + 7)))
    (original := fun p => generator <$> BitString.sampleList (p.1.1 + 7))
    (count := fun p => k p.1.1 * ((p.1.1 + 1) * totalLen (f p.1.2.1)))
    (test := fun p xs => do
      let view ← runAllSessionsWithPads machine generator
        (p.1.1 + 7) (length (p.1.1 + 7))
        (c * ((wordFn p.1).length + 1) ^ d)
        (p.1.1 + 1) (k p.1.1)
        (f p.1.2.1) p.1.2.2.1 (wordFn p.1) xs
      adversary p.1.1 p.1.2.1 (zA p.1.2.2.2) view)
    (challenge := fun p => p.2)
    (isPPTOn_sampleList.preprocess hm1)
    ((isPPTOn_sampleList.preprocess hs1).map hg)
    hcount1 htest (ComputableInPolyTime.snd input encBits)
  exact (congrArg (IsPPTOn _ _) (by
    funext ⟨⟨n, a, w, aux⟩, challenge⟩
    simp only [gmwSeqViewReduction, encIn, hV, ↓reduceDIte, machine, c, d, wordFn])).mp hseq

/-- `gmwSeqViewReduction` has a strict uniform clock polynomial in its complete encoded input
`((1^n, (a, (w, z))), challenge)`. -/
theorem isPPTOn_gmwSeqViewReduction {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z), view) => adversary n a z view)) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits encBits))) encBits) encBool
      (fun ((n, a, w, z), challenge) =>
        gmwSeqViewReduction enc generator length f k Vstar adversary n a w z challenge) := by
  have h := isPPTOn_gmwSeqViewReduction_aux
    (.id' (encIn := encBits)) (.id' (encIn := encBits)) hg hlen hf hk hV hadv
  exact (congrArg (IsPPTOn _ _) (by
    funext ⟨⟨n, a, w, z⟩, challenge⟩
    simp only [gmwSeqViewReduction])).mp h

private theorem isPPTOn_gmwSeqViewReduction_pair {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view)) :
    IsPPTOn
      (encPair (encPair encUnary (encPair enc (encPair encBits (encPair encBits encBits)))) encBits)
      encBool
      (fun ((n, a, w, (z, z')), challenge) =>
        gmwSeqViewReduction enc generator length f k Vstar
          (fun n a _ view => adversary n a z' view) n a w z challenge) :=
  isPPTOn_gmwSeqViewReduction_aux
    (.fst encBits encBits) (.snd encBits encBits) hg hlen hf hk hV hadv

/-- Under `AdvicePRG enc generator length`, the `k n`-session real GMW interaction view and
`gmwSeqSimulator` have negligible distinguishing advantage against every full-input uniform strict
PPT distinguisher across all polynomially bounded valid instance, witness, verifier-auxiliary, and
distinguisher-auxiliary families. -/
theorem AdvicePRG.gmwSeqView_negligible {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {adversary : ℕ → α → List Bool → List Bool → ProbComp Bool}
    (hAdv : AdvicePRG enc generator length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    (hadv : IsPPTOn (encPair (encPair encUnary (encPair enc encBits)) encBits) encBool
      (fun ((n, a, z'), view) => adversary n a z' view))
    {a : ℕ → α} {w z z' : ℕ → List Bool}
    (ha : PolynomiallyBounded (fun n => (enc (a n)).length))
    (hw : PolynomiallyBounded (fun n => (w n).length))
    (hz : PolynomiallyBounded (fun n => (z n).length))
    (hz' : PolynomiallyBounded (fun n => (z' n).length))
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    Negligible (fun n => Game.advantage
      (distinguishingGame
        (((gmwSeqProver generator (n + 7) (length (n + 7)) (f (a n)) (w n) (k n)).run
          (Vstar n (a n) (z n))
          (gmwSeqProver generator (n + 7) (length (n + 7)) (f (a n)) (w n) (k n)).init).map
            Prod.fst)
        (adversary n (a n) (z' n)))
      (distinguishingGame
        (ProbComp.eval (gmwSeqSimulator enc generator length f k Vstar n (a n) (z n)))
        (adversary n (a n) (z' n)))) := by
  have hclock := isPPTOn_gmwSeqViewReduction_pair hAdv.1 hAdv.2.1 hf hk hV hadv
  have haux : PolynomiallyBounded (fun n => (encPair encBits encBits (z n, z' n)).length) := by
    simp only [length_encPair, encBits_apply]
    exact (((PolynomiallyBounded.const 2).mul hz).add (.const 1)).add hz'
  have hneg := hAdv.negligible_encoded hclock ha hw haux
  have hcount : ComputableTidilyInPolyTime (fun a => totalLen (f a)) enc encUnary :=
    (computableInPolyTime_totalLen hf).tidy
  have hsize : PolyBounded id (fun n => (enc (a n)).length) := ⟨_, ha, fun _ => le_rfl⟩
  have hcount_poly := (hcount.polyBounded.comp hsize).polynomiallyBounded
  have hk_poly : PolynomiallyBounded k := hk.tidy.polynomiallyBounded
  have hloss : PolynomiallyBounded
      (fun n => dyadicSize (k n * ((n + 1) * totalLen (f (a n))))) :=
    PolynomiallyBounded.comp ComputableInPolyTime.unary_dyadicSize.tidy.polynomiallyBounded
      (hk_poly.mul ((PolynomiallyBounded.id.add (.const 1)).mul hcount_poly))
  have hgeom := (negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1
  have herr := hgeom.polynomiallyBounded_mul hk_poly
  apply negligible_of_le (herr.add_fun (hneg.polynomiallyBounded_mul hloss))
  intro n
  simpa only [ProbComp.eval_bind] using
    gmwSeqView_advantage_le generator length f k hV
      (fun m a _ view => adversary m a (z' n) view)
      n (a n) (w n) (z n) (hw_sat n)

/-- **Zero-knowledge simulation of the sequentially amplified GMW protocol.** For any uniform strict
oracle PPT malicious verifier `Vstar` and any deterministic polynomial-time families of instances
`a`, valid `ThreeSAT` witnesses `w`, and auxiliary inputs `z`, the `k n`-session real interaction
view of `Vstar` with `gmwSeqProver` is computationally indistinguishable from
`gmwSeqSimulator`. -/
theorem gmwSeqView_indistinguishable_gmwSeqSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    {f : α → CNF ℕ} (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hV : IsOraclePPTOn (encPair encUnary (encPair enc encBits)) encBits
      (fun (n, a, z) => Vstar n a z))
    {a : ℕ → α} {w z : ℕ → List Bool}
    (ha : ComputableInPolyTime a encUnary enc)
    (hw_comp : ComputableInPolyTime w encUnary encBits)
    (hz : ComputableInPolyTime z encUnary encBits)
    (hw_sat : ∀ n, ThreeSAT.verifier (f (a n), w n) = true) :
    ComputationallyIndistinguishable
      (fun n => ((gmwSeqProver generator (n + 7) (length (n + 7)) (f (a n)) (w n) (k n)).run
        (Vstar n (a n) (z n))
        (gmwSeqProver generator (n + 7) (length (n + 7)) (f (a n)) (w n) (k n)).init).map Prod.fst)
      (fun n => ProbComp.eval (gmwSeqSimulator enc generator length f k Vstar n (a n) (z n))) := by
  intro adversary hadversary
  let encIn := encPair encUnary (encPair enc encBits)
  have htest : IsPPTOn (encPair encIn encBits) encBool
      (fun p => adversary p.1.1 p.2) :=
    hadversary.on.preprocess
      (((ComputableInPolyTime.fst encIn encBits).fst').prod (.snd encIn encBits))
  have hclock := isPPTOn_gmwSeqViewReduction
    (adversary := fun n _ _ view => adversary n view)
    hG.polyTime hG.length_eq hf hk hV htest
  let red : Distinguisher := fun n challenge =>
    gmwSeqViewReduction enc generator length f k Vstar (fun n _ _ view => adversary n view)
      n (a n) (w n) (z n) challenge
  have hn1 := ComputableInPolyTime.fst encUnary encBits
  have hred : IsPPT encBool red :=
    hclock.preprocess (input := encPair encUnary encBits)
      (prepare := fun p => ((p.1, a p.1, w p.1, z p.1), p.2))
      ((hn1.prod ((ha.comp hn1).prod ((hw_comp.comp hn1).prod (hz.comp hn1)))).prod
        (.snd encUnary encBits))
  have hneg := (hG.indistinguishable.shift 7) red hred
  have hcount_poly : PolynomiallyBounded (fun n => totalLen (f (a n))) :=
    ((computableInPolyTime_totalLen hf).comp ha).tidy.polynomiallyBounded
  have hk_poly : PolynomiallyBounded k := hk.tidy.polynomiallyBounded
  have hloss : PolynomiallyBounded
      (fun n => dyadicSize (k n * ((n + 1) * totalLen (f (a n))))) :=
    PolynomiallyBounded.comp ComputableInPolyTime.unary_dyadicSize.tidy.polynomiallyBounded
      (hk_poly.mul ((PolynomiallyBounded.id.add (.const 1)).mul hcount_poly))
  have hgeom := (negligible_geometric (by norm_num : (7 / 8 : ℝ≥0) < 1)).shift 1
  have herr := hgeom.polynomiallyBounded_mul hk_poly
  apply negligible_of_le (herr.add_fun (hneg.polynomiallyBounded_mul hloss))
  intro n
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_map,
    BitString.eval_sampleList, generatorEnsemble, red] using
    gmwSeqView_advantage_le generator length f k hV (fun n _ _ view => adversary n view)
      n (a n) (w n) (z n) (hw_sat n)

end Cslib.Crypto.GMW
