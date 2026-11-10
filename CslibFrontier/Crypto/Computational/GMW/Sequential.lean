/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
public import CslibFrontier.Computability.Probabilistic.Realization.OpenOracleSimulation
public import CslibFrontier.Crypto.Computational.GMW.Simulator
public import CslibFrontier.Crypto.Computational.GMW.Soundness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map

/-!
# Sequential soundness amplification for the 3-copy GMW zero-knowledge protocol

This module sequentially composes `k n` independent executions of the 3-copy masked-3SAT GMW
protocol (`CslibFrontier.Crypto.Computational.GMW.Protocol`), where `generator` maps seeds of
length `m` to words of length `length m`. Perfect completeness (`acceptProb = 1`) is preserved for
every `k`. If `3 * m + 1 ≤ length m` for all `m`, the soundness error drops from `1 / 3` to
`(1 / 3) ^ (k n)` against arbitrary unbounded stateful provers, again for every `k`.

Computational zero-knowledge is proved in
`CslibFrontier.Crypto.Computational.GMW.Sequential.Simulator`, which builds `gmwSeqSimulator` from
the single-session attempt and machine-slicing primitives of Sections 2 and 3 below. It holds
against arbitrary uniform strict oracle PPT malicious verifiers when the map `f` from instances to
formulas is computable in polynomial time and `k` is computable in polynomial time in unary
(`ComputableInPolyTime k encUnary encUnary`), and it is conditional: under `PseudorandomGenerator`
it covers instance, witness and auxiliary-input families computable in polynomial time from the
unary parameter, and under `AdvicePRG` it covers arbitrary such families of polynomially bounded
length. In both cases the witnesses are valid `ThreeSAT` witnesses.

## Main definitions

* `Cslib.Crypto.GMW.seqStep`, `Cslib.Crypto.GMW.runSeq`: multi-session deterministic state handler
  for `k` sequential two-round GMW sessions.
* `Cslib.Crypto.GMW.gmwSeqProver`, `Cslib.Crypto.GMW.gmwSeqInteract`: honest sequential prover and
  its `ProbComp` interaction realization.
* `Cslib.Crypto.GMW.gmwSeqVerifier`: sequentially amplified GMW verifier running `gmwVerifier`
  `k n` times and accepting iff all `k n` executions accept.
* `Cslib.Crypto.GMW.encBudgetedConfig`: the encoding of a machine configuration with its remaining
  step and query budgets, the state of `oneSessionStep`.

## Main results

* `Cslib.Crypto.GMW.isOraclePPTOn_gmwSeqVerifier`: `gmwSeqVerifier` is `IsOraclePPTOn`.
* `Cslib.Crypto.GMW.isPPTOn_gmwSeqInteract`: `gmwSeqInteract` is `IsPPTOn`.
* `Cslib.Crypto.GMW.acceptProb_gmwSeqVerifier_gmwSeqProver`: perfect completeness
  (`acceptProb = 1`).
* `Cslib.Crypto.GMW.acceptProb_replicate_all_le`, `Cslib.Crypto.GMW.acceptProb_gmwSeqVerifier_le`:
  sequential soundness amplification (`acceptProb ≤ (1 / 3) ^ (k n)`).
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM Turing.MultiTapeMachine
open scoped NNReal ENNReal

/-! ### Section 1: Sequential multi-session prover, verifier, completeness, and soundness -/

/-- Multi-session deterministic transition for sequential two-round GMW executions.
The state `(inRound2, coinsList)` tracks whether the current session is waiting for its first
query (`false`) or second query (`true`), together with the remaining list of per-session prover
coin pairs `(bits, seeds)`. Once `coinsList` is exhausted, subsequent queries return `[]`. -/
def seqStep (reply1 reply2 : (List Bool × List (List Bool)) → List Bool → List Bool)
    (q : List Bool) (s : Bool × List (List Bool × List (List Bool))) :
    List Bool × (Bool × List (List Bool × List (List Bool))) :=
  match s.2 with
  | [] => ([], (false, []))
  | coins :: rest =>
    if s.1 then
      (reply2 coins (BitString.listRow 3 0 q), (false, rest))
    else
      (reply1 coins q, (true, coins :: rest))

/-- Run a `WordOracleComp Unit` program against `seqStep` with honest GMW reply functions inside
`ProbComp`. -/
def runSeq {α : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit α)
    (st : Bool × List (List Bool × List (List Bool))) :
    ProbComp (α × (Bool × List (List Bool × List (List Bool)))) :=
  (OracleComp.interpret (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
    (fun q state => pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 state)))
    prog).run st

@[simp] theorem runSeq_pure {α : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (a : α) (st : Bool × List (List Bool × List (List Bool))) :
    runSeq generator s m φ (pure a) st = pure (a, st) := rfl

theorem runSeq_bind {α β : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit α) (next : α → WordOracleComp Unit β)
    (st : Bool × List (List Bool × List (List Bool))) :
    runSeq generator s m φ (prog >>= next) st =
      (runSeq generator s m φ prog st >>= fun x => runSeq generator s m φ (next x.1) x.2) := by
  simp only [runSeq, OracleComp.interpret_bind, StateT.run_bind]

theorem runSeq_map {α β : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (f : α → β) (prog : WordOracleComp Unit α)
    (st : Bool × List (List Bool × List (List Bool))) :
    runSeq generator s m φ (f <$> prog) st =
      Prod.map f id <$> runSeq generator s m φ prog st := by
  simp only [runSeq, OracleComp.interpret_map, StateT.run_map]; rfl

@[simp] theorem runSeq_sample {α : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : ProbComp α) (st : Bool × List (List Bool × List (List Bool))) :
    runSeq generator s m φ (ProbOracleComp.sample prog) st = (·, st) <$> prog := by
  simp only [runSeq, ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
    ProbComp.unifFin, OracleComp.interpret_query_eq_self]

@[simp] theorem runSeq_query (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (q : Unit × List Bool) (st : Bool × List (List Bool × List (List Bool))) :
    runSeq generator s m φ (ProbOracleComp.query q) st =
      pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 st) := by
  simp only [runSeq, ProbOracleComp.interpret_query]; rfl

theorem eval_runSeq {α : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit α) (st : Bool × List (List Bool × List (List Bool))) :
    ProbComp.eval (runSeq generator s m φ prog st) =
      ProbOracleComp.runWith
        (fun q state =>
          PMF.pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 state))
        prog st := by
  simpa [runSeq] using
    ProbOracleComp.eval_run_interpret_eq_runWith
      (fun q state => pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 state))
      prog st

/-- The honest sequential GMW prover for `k` executions on a 3SAT formula `φ` and witness `w`.
On the first query it samples `k` independent coin pairs from `sampleHonestCoins s φ w` and
answers up to `k` two-round sessions via `seqStep`. -/
noncomputable def gmwSeqProver (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (k : ℕ) : Prover Unit where
  State := Option (Bool × List (List Bool × List (List Bool)))
  init := none
  respond q state := match state with
    | none =>
      (ProbComp.eval (OracleComp.replicate k (sampleHonestCoins s φ w))).map fun coinsList =>
        let step := seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 (false, coinsList)
        (step.1, some step.2)
    | some st =>
      let step := seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 st
      PMF.pure (step.1, some step.2)

theorem run_gmwSeqProver_fst {α : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (k : ℕ) (prog : WordOracleComp Unit α) :
    ((gmwSeqProver generator s m φ w k).run prog
        (gmwSeqProver generator s m φ w k).init).map Prod.fst =
      ProbComp.eval (do
        let coinsList ← OracleComp.replicate k (sampleHonestCoins s φ w)
        Prod.fst <$> runSeq generator s m φ prog (false, coinsList)) := by
  let P := gmwSeqProver generator s m φ w k
  let State' := Bool × List (List Bool × List (List Bool))
  let relate : P.State → PMF State' := fun state => match state with
    | none => (ProbComp.eval (OracleComp.replicate k (sampleHonestCoins s φ w))).map (false, ·)
    | some st => PMF.pure st
  let oracle' : Unit × List Bool → StateT State' PMF (List Bool) := fun q state =>
    PMF.pure (seqStep (honestReply1 generator m φ) (honestReply2 s φ) q.2 state)
  have hsim := ProbOracleComp.runWith_simulation P.respond oracle' relate
    (fun q state => by
      cases state <;>
        simp [P, gmwSeqProver, relate, oracle', PMF.bind_map, Function.comp_def]) prog P.init
  have hmap := congrArg (PMF.map Prod.fst) hsim
  have hlhs : ((ProbOracleComp.runWith P.respond prog P.init).bind
        (fun (a, s') => (relate s').map (a, ·))).map Prod.fst =
      (P.run prog P.init).map Prod.fst := by
    simp only [pmf_norm, Prover.run]
    have hconst : ∀ x : α × P.State, PMF.map (fun _ : State' => x.1) (relate x.2) = PMF.pure x.1 :=
      fun _ => PMF.map_const _ _
    simp only [hconst]; rfl
  rw [hlhs] at hmap; rw [hmap]
  simp only [pmf_norm, P, gmwSeqProver, relate]
  exact congrArg (PMF.bind _) (funext fun coinsList => by rw [eval_runSeq])

/-- The PPT program realizing `gmwSeqProver`'s interaction with a verifier `prog`. -/
noncomputable def gmwSeqInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (k : ℕ) (prog : WordOracleComp Unit (List Bool)) : ProbComp (List Bool) := do
  let coinsList ← OracleComp.replicate k (sampleHonestCoins s φ w)
  let p ← runSeq generator s m φ prog (false, coinsList)
  return p.1

theorem eval_gmwSeqInteract (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (k : ℕ) (prog : WordOracleComp Unit (List Bool)) :
    ProbComp.eval (gmwSeqInteract generator s m φ w k prog) =
      ((gmwSeqProver generator s m φ w k).run prog
        (gmwSeqProver generator s m φ w k).init).map Prod.fst := by
  simpa only [gmwSeqInteract, bind_pure_comp] using
    (run_gmwSeqProver_fst generator s m φ w k prog).symm

/-- Encode the multi-session prover state `(inRound2, coinsList)`. -/
abbrev encSeqState : (Bool × List (List Bool × List (List Bool))) ↪ List Bool :=
  encPair encBool (encList encCoinPair)

private theorem computableInPolyTime_seqStep {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {q : α → List Bool} {st : α → Bool × List (List Bool × List (List Bool))}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF)
    (hq : ComputableInPolyTime q input encBits)
    (hst : ComputableInPolyTime st input encSeqState) :
    ComputableInPolyTime
      (fun a => seqStep (honestReply1 generator (m a) (φ a)) (honestReply2 (s a) (φ a))
        (q a) (st a))
      input (encPair encBits encSeqState) := by
  have heq : (fun a => seqStep (honestReply1 generator (m a) (φ a)) (honestReply2 (s a) (φ a))
        (q a) (st a)) =
      (fun a =>
        if (st a).2.isEmpty then
          ([], (false, []))
        else
          let coins := (st a).2.headD ([], [])
          let rest := (st a).2.tail
          if (st a).1 then
            (honestReply2 (s a) (φ a) coins (BitString.listRow 3 0 (q a)), (false, rest))
          else
            (honestReply1 generator (m a) (φ a) coins (q a), (true, (st a).2))) := by
    funext a
    rcases h : (st a).2 with _ | ⟨coins, rest⟩ <;> simp [seqStep, h]
  rw [heq]
  have hlist := hst.snd'
  have hcoins := (ComputableInPolyTime.headD (encA := encCoinPair) ([], [])).comp' hlist
  have hempty :=
    (ComputableTidilyInPolyTime.listIsEmpty' encCoinPair).computableInPolyTime.comp' hlist
  have htail := (ComputableTidilyInPolyTime.listTail encCoinPair).computableInPolyTime.comp' hlist
  exact hempty.ite' (.const ([], (false, [])))
    (hst.fst'.ite'
      ((computableInPolyTime_honestReply2 hs hφ hcoins
        (ComputableInPolyTime.bitsRowWithInput (.const 3) (.const 0) hq)).prod
        ((ComputableInPolyTime.const false).prod htail))
      ((computableInPolyTime_honestReply1 hg hm hφ hcoins hq).prod
        ((ComputableInPolyTime.const true).prod hlist)))

theorem isPPTOn_runSeq_honest {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool}
    {n s m : Caller → ℕ} {a : Caller → α} {z : Caller → List Bool}
    {φ : Caller → CNF ℕ} {coinsList : Caller → List (List Bool × List (List Bool))}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z))
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits)
    (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coinsList input (encList encCoinPair)) :
    IsPPTOn input (encPair encBits encSeqState)
      (fun c => runSeq generator (s c) (m c) (φ c)
        (Vstar (n c) (a c) (z c)) (false, coinsList c)) := by
  let encStepMid := encPair (encPair (encFinEnum Unit) encBits) encSeqState
  have hc := ComputableInPolyTime.fst input encStepMid
  have hrest := ComputableInPolyTime.snd input encStepMid
  have hstep := computableInPolyTime_seqStep hg (hs.comp' hc) (hm.comp' hc) (hφ.comp' hc)
    hrest.fst'.snd' hrest.snd'
  have hc1 := ComputableInPolyTime.fst input encBits
  have hlen := (ComputableInPolyTime.encoding_length (encList encCoinPair)).comp' (hcoins.comp' hc1)
  have hbound := (hlen.unary_mul' (hm.comp' hc1)).unary_add'
    (hlen.unary_mul' ((hs.comp' hc1).unary_add' (.const 1)))
  refine hV.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (stateEncoding := encSeqState)
    (handler := fun c q state =>
      pure (seqStep (honestReply1 generator (m c) (φ c)) (honestReply2 (s c) (φ c)) q.2 state))
    (prepare := fun c => (n c, a c, z c)) (initial := fun c => (false, coinsList c))
    (resources := fun c _ => (encList encCoinPair (coinsList c)).length * m c +
      (encList encCoinPair (coinsList c)).length * (s c + 1))
    (hn.prod (ha.prod hz)).tidy hstep.isPPTOn ((ComputableInPolyTime.const false).prod hcoins).tidy
    (fun c st => List.Sublist st.2 (coinsList c)) (fun _ => List.Sublist.refl _) hbound.tidy
    (fun c request state hstate result hresult => ?_)
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
  subst hresult
  have hbool_len (b : Bool) : (encBool b).length = 1 := by cases b <;> rfl
  rcases hlist : state.2 with _ | ⟨coins, rest⟩
  · simp [seqStep, hlist, encSeqState]
  · have hmem : coins ∈ coinsList c := hstate.subset (by simp [hlist])
    have hcoins_le : coins.1.length ≤ (encList encCoinPair (coinsList c)).length :=
      (by simp [encCoinPair]; omega : coins.1.length ≤ (encCoinPair coins).length).trans
        (SizedListEncoding.length_elem_le (coinsList c) coins hmem)
    have hsub_rest : List.Sublist rest (coinsList c) :=
      (List.sublist_cons_self coins rest).trans (hlist ▸ hstate)
    cases hround : state.1
    · simp only [seqStep, hlist, hround, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hlist ▸ hstate, ?_, by simp [encSeqState, hlist, hround]⟩
      dsimp only [honestReply1]
      exact (List.length_take_le _ _).trans
        ((Nat.mul_le_mul_right (m c) hcoins_le).trans (by omega))
    · simp only [seqStep, hlist, hround, ↓reduceIte]
      have hsub_len := length_encList_sublist encCoinPair (List.sublist_cons_self coins rest)
      refine ⟨hsub_rest, ?_, ?_⟩
      · dsimp only [honestReply2]; rw [length_proverReply2_any]
        exact (Nat.mul_le_mul_right (s c + 1) hcoins_le).trans (by omega)
      · simp only [encSeqState, length_encPair, hlist, hround, hbool_len]; omega

/-- `gmwSeqInteract` is uniform strict PPT whenever `k` is computable in polynomial time. -/
theorem isPPTOn_gmwSeqInteract {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceWitnessAuxInput enc) encBits
      (fun (n, a, w, z) =>
        gmwSeqInteract generator (n + 7) (length (n + 7)) (f a) w (k n)
          (Vstar n a z)) := by
  let input := encPair encUnary (encPair enc (encPair encBits encBits))
  have hlength := PRG.polyTime_length hg hlen
  have hn := ComputableInPolyTime.fst encUnary (encPair enc (encPair encBits encBits))
  have hs := hn.unary_add' (.const 7)
  have hrest := ComputableInPolyTime.snd encUnary (encPair enc (encPair encBits encBits))
  have hp1 := ComputableInPolyTime.fst input (encList encCoinPair)
  have hs1 := hp1.fst'.unary_add' (.const 7)
  change IsPPTOn input encBits
    (fun p : ℕ × α × List Bool × List Bool =>
      gmwSeqInteract generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1) p.2.2.1 (k p.1)
        (Vstar p.1 p.2.1 p.2.2.2))
  dsimp only [gmwSeqInteract]
  simp only [bind_pure_comp]
  exact ((isPPTOn_sampleHonestCoins hs (hf.comp' hrest.fst') hrest.snd'.fst').replicate
    (hk.comp' hn)).bind_with
    ((isPPTOn_runSeq_honest hV hg hp1.fst' hs1 (hlength.comp' hs1)
      hp1.snd'.fst' hp1.snd'.snd'.snd' (hf.comp' hp1.snd'.fst')
      (.snd input (encList encCoinPair))).map (.fst encBits encSeqState))

private theorem replicate_eq_iterate {Query : Type} {spec : OracleSpec.{0, 0} Query} {α : Type}
    (count : ℕ) (program : OracleComp spec α) :
    OracleComp.replicate count program =
      OracleComp.iterate count (fun xs => (fun x => xs ++ [x]) <$> program) [] := by
  induction count with
  | zero => rfl
  | succ count ih => rw [OracleComp.replicate_snoc, OracleComp.iterate_succ, ih]

theorem isOraclePPTOn_replicate_bool {Operation α : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {program : α → WordOracleComp Operation Bool} {count : α → ℕ}
    (hprog : IsOraclePPTOn input encBool program)
    (hcount : ComputableInPolyTime count input encUnary) :
    IsOraclePPTOn input encBits (fun a => OracleComp.replicate (count a) (program a)) := by
  simp only [replicate_eq_iterate]
  refine IsOraclePPTOn.iterateWith_of_bounded_growth' hcount (.const []) ?_
    (.const 1) (fun a state next hnext => ?_)
  · exact (hprog.preprocess' (prepare := Prod.fst)
      (ComputableInPolyTime.fst input encBits)).map_with'
      (f := fun p x => p.2 ++ [x])
      (ComputableInPolyTime.bitsAppend
        ((ComputableInPolyTime.fst (encPair input encBits) encBool).snd')
        ((ComputableInPolyTime.of_finite (fun b : Bool => [b])).comp'
          (ComputableInPolyTime.snd (encPair input encBits) encBool)))
  · obtain ⟨b, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    simp

/-- The sequentially amplified GMW verifier: execute `gmwVerifier` `k n` times and accept iff all
`k n` executions accept. -/
noncomputable def gmwSeqVerifier {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (k : ℕ → ℕ) (n : ℕ) (a : α) : WordOracleComp Unit Bool :=
  (fun bs => bs.all id) <$> OracleComp.replicate (k n) (gmwVerifier generator length f n a)

@[fun_prop]
theorem isOraclePPTOn_gmwSeqVerifier {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length k : ℕ → ℕ} {f : α → CNF ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hk : ComputableInPolyTime k encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary enc) encBool
      (fun p : ℕ × α => gmwSeqVerifier generator length f k p.1 p.2) := by
  have hV := isOraclePPTOn_gmwVerifier (enc := enc) hg hlen hf
  have hk' := hk.comp' (.fst encUnary enc)
  dsimp only [gmwSeqVerifier]
  exact IsOraclePPTOn.map' (f := fun bs : List Bool => bs.all id)
    (isOraclePPTOn_replicate_bool hV hk')
    (ComputableInPolyTime.bitsAllWithInput (.id' (encIn := encBits)) (.snd encBits encBool))

private theorem runSeq_gmwVerifier {α : Type} (generator : List Bool → List Bool)
    (length : ℕ → ℕ) (f : α → CNF ℕ) (n : ℕ) (a : α)
    (coins : List Bool × List (List Bool)) (rest : List (List Bool × List (List Bool))) :
    runSeq generator (n + 7) (length (n + 7)) (f a)
        (gmwVerifier generator length f n a) (false, coins :: rest) =
      (fun p => (p.1, (false, rest))) <$>
        runTwoRound (honestReply1 generator (length (n + 7)) (f a) coins)
          (honestReply2 (n + 7) (f a) coins)
          (gmwVerifier generator length f n a) (0, [false, false, false]) := by
  simp only [gmwVerifier, runSeq_bind, runSeq_sample, runSeq_query, runSeq_pure,
    runTwoRound_bind, runTwoRound_sample, runTwoRound_query, runTwoRound_pure,
    seqStep, twoRoundStep, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Nat.reduceBEq,
    bind_map_left, map_bind, pure_bind, map_pure]

private theorem eval_bind_replicate_runSeq_gmwVerifier {α : Type}
    (generator : List Bool → List Bool) (length : ℕ → ℕ) (f : α → CNF ℕ)
    (n : ℕ) (a : α) (w : List Bool) (K : ℕ) :
    ProbComp.eval (do
      let coinsList ← OracleComp.replicate K (sampleHonestCoins (n + 7) (f a) w)
      Prod.fst <$> runSeq generator (n + 7) (length (n + 7)) (f a)
        (OracleComp.replicate K (gmwVerifier generator length f n a))
        (false, coinsList)) =
    ProbComp.eval (OracleComp.replicate K (do
      let coins ← sampleHonestCoins (n + 7) (f a) w
      Prod.fst <$> runTwoRound (honestReply1 generator (length (n + 7)) (f a) coins)
        (honestReply2 (n + 7) (f a) coins)
        (gmwVerifier generator length f n a) (0, [false, false, false]))) := by
  induction K with
  | zero => simp [OracleComp.replicate]
  | succ K ih =>
    simp only [pmf_norm, OracleComp.replicate_succ, map_bind, runSeq_bind, runSeq_map,
      Functor.map_map, Prod.map_fst]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    simp only [pmf_norm, runSeq_gmwVerifier]
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind _) (funext fun p => ?_)
    have hih := congrArg (PMF.map (List.cons p.1)) ih
    simpa only [pmf_norm] using hih

/-- **Completeness of the sequentially amplified GMW protocol.** When
`ThreeSAT.verifier (f a, w) = true`, `gmwSeqProver` makes `gmwSeqVerifier` accept with
probability `1`. -/
theorem acceptProb_gmwSeqVerifier_gmwSeqProver {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (f : α → CNF ℕ) (k : ℕ → ℕ) (n : ℕ) (a : α) {w : List Bool}
    (hw : ThreeSAT.verifier (f a, w) = true) :
    acceptProb (gmwSeqVerifier generator length f k n a)
      (gmwSeqProver generator (n + 7) (length (n + 7)) (f a) w (k n)) = 1 := by
  have h1 := acceptProb_gmwVerifier_gmwProver hlen f n a hw
  rw [acceptProb, run_gmwProver_fst] at h1
  let single : ProbComp Bool := do
    let coins ← sampleHonestCoins (n + 7) (f a) w
    Prod.fst <$> runTwoRound (honestReply1 generator (length (n + 7)) (f a) coins)
      (honestReply2 (n + 7) (f a) coins)
      (gmwVerifier generator length f n a) (0, [false, false, false])
  change ProbComp.eval single true = 1 at h1
  have hsingle_pure : ProbComp.eval single = PMF.pure true := by
    have hfalse : ProbComp.eval single false = 0 := by
      have hsum := PMF.tsum_coe (ProbComp.eval single)
      rw [tsum_bool, h1] at hsum
      exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp (hsum.trans (zero_add 1).symm)
    ext b; cases b <;> simp [hfalse, h1]
  rw [acceptProb, run_gmwSeqProver_fst]
  have hmap : (do
      let coinsList ← OracleComp.replicate (k n) (sampleHonestCoins (n + 7) (f a) w)
      Prod.fst <$> runSeq generator (n + 7) (length (n + 7)) (f a)
        (gmwSeqVerifier generator length f k n a) (false, coinsList)) =
      (fun bs : List Bool => bs.all id) <$> (do
        let coinsList ← OracleComp.replicate (k n) (sampleHonestCoins (n + 7) (f a) w)
        Prod.fst <$> runSeq generator (n + 7) (length (n + 7)) (f a)
          (OracleComp.replicate (k n) (gmwVerifier generator length f n a))
          (false, coinsList)) := by
    simp only [gmwSeqVerifier, runSeq_map, map_bind, Functor.map_map, Prod.map_fst]
  rw [hmap, ProbComp.eval_map, eval_bind_replicate_runSeq_gmwVerifier,
    ProbComp.eval_replicate_congr (hsingle_pure.trans (ProbComp.eval_pure true).symm)]
  have hrep : ∀ K, (OracleComp.replicate K (pure true : ProbComp Bool)) =
      pure (List.replicate K true) := by
    intro K; induction K with
    | zero => rfl
    | succ K ih =>
      simp only [OracleComp.replicate_succ, ih, List.replicate_succ, map_pure, pure_bind]
  rw [hrep (k n)]; simp

/-- **Sequential soundness amplification for interactive proofs.** If no stateful prover makes
`verifier` accept with probability greater than `c`, then running `verifier` `k` times sequentially
and accepting iff all `k` executions accept has soundness error at most `c ^ k` against every
unbounded stateful prover `P`. -/
theorem acceptProb_replicate_all_le {Operation : Type}
    {verifier : WordOracleComp Operation Bool} {c : ℝ≥0∞}
    (hV : ∀ P : Prover Operation, acceptProb verifier P ≤ c)
    (k : ℕ) (P : Prover Operation) :
    acceptProb ((fun bs => bs.all id) <$> OracleComp.replicate k verifier) P ≤ c ^ k := by
  induction k generalizing P with
  | zero =>
    rw [acceptProb_eq_acceptProbWith]
    simpa [OracleComp.replicate] using
      ProbOracleComp.acceptProbWith_le_one P.respond (pure true) P.init
  | succ k ih =>
    have hbind : ((fun bs => bs.all id) <$> OracleComp.replicate (k + 1) verifier) =
        (verifier >>= fun b =>
          (fun bs => b && bs.all id) <$> OracleComp.replicate k verifier) := by
      simp [OracleComp.replicate_succ, map_bind, Functor.map_map]
    rw [hbind, acceptProb_eq_acceptProbWith, ProbOracleComp.acceptProbWith_bind,
      tsum_prod', tsum_bool]
    have hfalse (s' : P.State) :
        ProbOracleComp.acceptProbWith P.respond
          ((fun bs => false && bs.all id) <$> OracleComp.replicate k verifier) s' = 0 := by
      let P' : Prover Operation := ⟨P.State, s', P.respond⟩
      change acceptProb ((fun _ => false) <$> OracleComp.replicate k verifier) P' = 0
      refine acceptProb_eq_zero P' fun x hx => ?_
      rw [Prover.run_map, PMF.mem_support_map_iff] at hx
      obtain ⟨y, _, rfl⟩ := hx; rfl
    have htrue (s' : P.State) :
        ProbOracleComp.acceptProbWith P.respond
          ((fun bs => true && bs.all id) <$> OracleComp.replicate k verifier) s' ≤ c ^ k := by
      simpa [Bool.true_and, acceptProb_eq_acceptProbWith] using ih ⟨P.State, s', P.respond⟩
    simp only [hfalse, mul_zero, tsum_zero, zero_add]
    calc
      ∑' a : P.State, ProbOracleComp.runWith P.respond verifier P.init (true, a) *
          ProbOracleComp.acceptProbWith P.respond
            ((fun bs => true && bs.all id) <$> OracleComp.replicate k verifier) a
        ≤ ∑' a : P.State, ProbOracleComp.runWith P.respond verifier P.init (true, a) * c ^ k :=
          tsum_le_tsum fun a => mul_le_mul_right (htrue a) _
      _ = (∑' a : P.State, ProbOracleComp.runWith P.respond verifier P.init (true, a)) * c ^ k :=
          ENNReal.tsum_mul_right
      _ = acceptProb verifier P * c ^ k := by rw [acceptProb_eq_tsum, Prover.run_eq_runWith]
      _ ≤ c * c ^ k := mul_le_mul_left (hV P) _
      _ = c ^ (k + 1) := (pow_succ' c k).symm

/-- **Soundness of the sequentially amplified GMW protocol.** When `f a ∉ ThreeSAT` and
`3 * m + 1 ≤ length m` for all `m`, no unbounded stateful prover `P` makes `gmwSeqVerifier`
accept with probability greater than `(1 / 3) ^ (k n)`. -/
theorem acceptProb_gmwSeqVerifier_le {α : Type} {generator : List Bool → List Bool}
    {length : ℕ → ℕ} (hlen : ∀ seed, (generator seed).length = length seed.length)
    (hstretch : ∀ m, 3 * m + 1 ≤ length m)
    (f : α → CNF ℕ) (k : ℕ → ℕ) (n : ℕ) (a : α) (hnot : f a ∉ ThreeSAT) (P : Prover Unit) :
    acceptProb (gmwSeqVerifier generator length f k n a) P ≤ (1 / 3 : ℝ≥0∞) ^ (k n) :=
  acceptProb_replicate_all_le (acceptProb_gmwVerifier_le hlen hstretch f n a hnot) (k n) P

/-! ### Section 2: Typed `Option β` single-session GMW attempt primitives -/

/-- Extract the first `some x` from a list of optional attempt results, or return `d` if all
attempts are `none`. -/
def firstSuccess {β : Type} (d : β) (attempts : List (Option β)) : β :=
  ((attempts.filter Option.isSome).headD none).getD d

@[simp] theorem firstSuccess_nil {β : Type} (d : β) :
    firstSuccess d ([] : List (Option β)) = d := rfl

@[simp] theorem firstSuccess_cons {β : Type} (d : β) (o : Option β) (xs : List (Option β)) :
    firstSuccess d (o :: xs) = match o with
      | some x => x
      | none => firstSuccess d xs := by
  cases o <;> rfl

@[fun_prop]
theorem computableInPolyTime_firstSuccess {α β : Type} {input : α ↪ List Bool}
    {enc : β ↪ List Bool} {d : α → β} {attempts : α → List (Option β)}
    (hd : ComputableInPolyTime d input enc)
    (ha : ComputableInPolyTime attempts input (encList (encOption enc))) :
    ComputableInPolyTime (fun a => firstSuccess (d a) (attempts a)) input enc :=
  let hfilt := (ComputableInPolyTime.headD (encA := encOption enc) none).comp'
    (ha.filterWithInput
      (ComputableTidilyInPolyTime.snd input (encOption enc)).optionIsSome.computableInPolyTime)
  (hfilt.tidy.optionGetDWithInput hd.tidy).computableInPolyTime

/-- Run one simulated GMW attempt on a typed single-session verifier `prog : WordOracleComp Unit β`
with pre-sampled unopened pads `pads`. -/
noncomputable def gmwSimWithPadsOpt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    ProbComp (Option β) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← gmwSampleSimCoins s φ ch_guess
  let (view, _, challenge) ← runTwoRound
    (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess coins.1) coins.1 coins.2 pads)
    (fun _ => proverReply2 s φ ch_guess coins.1 coins.2)
    prog (0, [false, false, false])
  return if challenge == ch_guess then some view else none

/-- One typed attempt of the GMW simulator on `prog : WordOracleComp Unit β`. -/
noncomputable def gmwSimAttemptOpt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwSimWithPadsOpt generator s m φ prog pads

/-- Run one real GMW attempt on `prog : WordOracleComp Unit β` with pre-sampled unopened pads
`pads` and active flags `allOpenFlags φ ch_guess bits`. -/
noncomputable def gmwRealWithPadsOpt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    ProbComp (Option β) := do
  let ch_guess ← BitString.sampleList 3
  let m₀ ← BitString.sampleList φ.vars.length
  let m₁ ← BitString.sampleList φ.vars.length
  let m₂ ← BitString.sampleList φ.vars.length
  let bits := realBits φ w m₀ m₁ m₂
  let openFlags := allOpenFlags φ ch_guess bits
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  let (view, _, challenge) ← runTwoRound
    (fun r => proverReply1 generator m r openFlags bits seeds pads)
    (fun _ => proverReply2 s φ ch_guess bits seeds)
    prog (0, [false, false, false])
  return if challenge == ch_guess then some view else none

/-- One real GMW attempt on `prog : WordOracleComp Unit β` with PRG-generated unopened pads. -/
noncomputable def gmwRealPRGPadsOpt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let pads ← OracleComp.replicate (totalLen φ) (generator <$> BitString.sampleList s)
  gmwRealWithPadsOpt generator s m φ w prog pads

/-- One real GMW attempt on `prog : WordOracleComp Unit β` with uniform unopened pads. -/
noncomputable def gmwRealUniformPadsOpt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwRealWithPadsOpt generator s m φ w prog pads

/-- One honest GMW attempt on `prog : WordOracleComp Unit β` with a pre-sampled challenge guess
`ch_guess`. -/
noncomputable def game0Opt {β : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (w : List Bool) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← sampleHonestCoins s φ w
  let p ← runTwoRound
    (honestReply1 generator m φ coins)
    (fun _ => honestReply2 s φ coins ch_guess)
    prog (0, [false, false, false])
  return if p.2.2 == ch_guess then some p.1 else none

/-- Tag `out : β` with `some out` when a uniform 3-bit challenge equals `[false, false, false]`,
and return `none` otherwise. -/
noncomputable def bernoulliAttemptOpt {β : Type} (out : β) : PMF (Option β) :=
  (BitString.uniformList 3).map
    (fun ch_guess => if [false, false, false] == ch_guess then some out else none)

theorem map_encOption_gmwSimWithPadsOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    encOption enc <$> gmwSimWithPadsOpt generator s m φ prog pads =
      gmwSimWithPads generator s m φ (enc <$> prog) pads := by
  simp only [gmwSimWithPadsOpt, gmwSimWithPads, map_bind, runTwoRound_map, bind_map_left, map_pure]
  refine congrArg (Bind.bind _) (funext fun ch_guess =>
    congrArg (Bind.bind _) (funext fun coins =>
      congrArg (Bind.bind _) (funext fun ⟨view, round, challenge⟩ => ?_)))
  dsimp only [Prod.map, id_eq]; split_ifs <;> rfl

theorem map_encOption_gmwSimAttemptOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit β) :
    encOption enc <$> gmwSimAttemptOpt generator s m φ prog =
      gmwSimAttempt generator s m φ (enc <$> prog) := by
  simp only [gmwSimAttemptOpt, gmwSimAttempt, map_bind, map_encOption_gmwSimWithPadsOpt]

theorem map_encOption_gmwRealWithPadsOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    encOption enc <$> gmwRealWithPadsOpt generator s m φ w prog pads =
      gmwRealWithPads generator s m φ w (enc <$> prog) pads := by
  simp only [gmwRealWithPadsOpt, gmwRealWithPads, map_bind, runTwoRound_map, bind_map_left,
    map_pure]
  refine congrArg (Bind.bind _) (funext fun ch_guess =>
    congrArg (Bind.bind _) (funext fun m₀ =>
      congrArg (Bind.bind _) (funext fun m₁ =>
        congrArg (Bind.bind _) (funext fun m₂ =>
          congrArg (Bind.bind _) (funext fun seeds =>
            congrArg (Bind.bind _) (funext fun ⟨view, round, challenge⟩ => ?_))))))
  dsimp only [Prod.map, id_eq]; split_ifs <;> rfl

theorem map_encOption_gmwRealPRGPadsOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) :
    encOption enc <$> gmwRealPRGPadsOpt generator s m φ w prog =
      gmwRealPRGPads generator s m φ w (enc <$> prog) := by
  simp only [gmwRealPRGPadsOpt, gmwRealPRGPads, map_bind, map_encOption_gmwRealWithPadsOpt]

theorem map_encOption_gmwRealUniformPadsOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) :
    encOption enc <$> gmwRealUniformPadsOpt generator s m φ w prog =
      gmwRealUniformPads generator s m φ w (enc <$> prog) := by
  simp only [gmwRealUniformPadsOpt, gmwRealUniformPads, map_bind, map_encOption_gmwRealWithPadsOpt]

theorem map_encOption_game0Opt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) :
    encOption enc <$> game0Opt generator s m φ w prog =
      game0 generator s m φ w (enc <$> prog) := by
  simp only [game0Opt, game0, map_bind, runTwoRound_map, bind_map_left, map_pure]
  refine congrArg (Bind.bind _) (funext fun ch_guess =>
    congrArg (Bind.bind _) (funext fun coins =>
      congrArg (Bind.bind _) (funext fun ⟨view, round, challenge⟩ => ?_)))
  dsimp only [Prod.map, id_eq]; split_ifs <;> rfl

theorem map_encOption_bernoulliAttemptOpt {β : Type} (enc : β ↪ List Bool) (out : β) :
    (bernoulliAttemptOpt out).map (encOption enc) = bernoulliAttempt (enc out) := by
  simp only [bernoulliAttemptOpt, bernoulliAttempt, PMF.map_comp, Function.comp_def]
  congr 1 with ch_guess : 1
  cases [false, false, false] == ch_guess <;> rfl

theorem eval_game0Opt_eq_bind_bernoulliAttemptOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) :
    ProbComp.eval (game0Opt generator s m φ w prog) =
      (ProbComp.eval (do
        let coins ← sampleHonestCoins s φ w
        Prod.fst <$> runTwoRound (honestReply1 generator m φ coins) (honestReply2 s φ coins)
          prog (0, [false, false, false]))).bind bernoulliAttemptOpt := by
  apply Probability.PMF.map_injective (encOption enc).injective
  rw [← ProbComp.eval_map, map_encOption_game0Opt,
    eval_game0_eq_bind_bernoulliAttempt, run_gmwProver_fst]
  simp only [pmf_norm, runTwoRound_map, Functor.map_map, Prod.map_fst,
    map_encOption_bernoulliAttemptOpt]

private theorem bind_bernoulliAttemptOpt_ite {β : Type} (μ ν : PMF β) :
    (μ.bind bernoulliAttemptOpt).bind
      (fun o => match o with | some x => PMF.pure x | none => ν) = mixThree μ ν := by
  simp only [pmf_norm, bernoulliAttemptOpt, mixThree]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun ch_guess => ?_)
  cases [false, false, false] == ch_guess
  · exact PMF.bind_const _ _
  · exact PMF.bind_pure μ

theorem eval_firstSuccess_replicate_eq_repeatAttempt {β : Type} (d : β)
    {g : ProbComp (Option β)} {μ : PMF β}
    (hg : ProbComp.eval g = μ.bind bernoulliAttemptOpt) (k : ℕ) :
    ProbComp.eval (firstSuccess d <$> OracleComp.replicate k g) = repeatAttempt d μ k := by
  induction k with
  | zero => simp [repeatAttempt]
  | succ k ih =>
    simp only [pmf_norm, OracleComp.replicate_succ, map_bind, firstSuccess_cons, repeatAttempt]
    have hstep (o : Option β) :
        (ProbComp.eval (OracleComp.replicate k g)).map
          (fun xs => match o with | some x => x | none => firstSuccess d xs) =
        match o with | some x => PMF.pure x | none => repeatAttempt d μ k := by
      cases o with
      | none => simpa only [ProbComp.eval_map] using ih
      | some x => exact PMF.map_const _ _
    simp only [hstep, hg]
    exact bind_bernoulliAttemptOpt_ite μ (repeatAttempt d μ k)

theorem eval_game0PadsOpt_eq_eval_game0Opt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ) (w : List Bool)
    (prog : WordOracleComp Unit β) :
    ProbComp.eval (gmwRealPRGPadsOpt generator s m φ w prog) =
      ProbComp.eval (game0Opt generator s m φ w prog) := by
  apply Probability.PMF.map_injective (encOption enc).injective
  rw [← ProbComp.eval_map, ← ProbComp.eval_map,
    map_encOption_gmwRealPRGPadsOpt, map_encOption_game0Opt,
    eval_game0Pads_eq_eval_game0]

theorem eval_game1Opt_eq_eval_gmwSimAttemptOpt {β : Type} (enc : β ↪ List Bool)
    (generator : List Bool → List Bool) {s m : ℕ} {φ : CNF ℕ} {w : List Bool}
    (hw : ThreeSAT.verifier (φ, w) = true) (prog : WordOracleComp Unit β) :
    ProbComp.eval (gmwRealUniformPadsOpt generator s m φ w prog) =
      ProbComp.eval (gmwSimAttemptOpt generator s m φ prog) := by
  apply Probability.PMF.map_injective (encOption enc).injective
  rw [← ProbComp.eval_map, ← ProbComp.eval_map,
    map_encOption_gmwRealUniformPadsOpt, map_encOption_gmwSimAttemptOpt,
    eval_game1_eq_eval_gmwSimAttempt generator hw (enc <$> prog)]

theorem isPPTOn_gmwSimWithPadsOpt {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair (encInstanceAuxInput enc) (encList encBits)) (encOption encB)
      (fun p : (ℕ × α × List Bool) × List (List Bool) =>
        gmwSimWithPadsOpt generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) (Vstar p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have hV' := hV.map' (ComputableInPolyTime.of_eq (encOut := encBits) (f := encB) fun _ => rfl)
  rw [isPPTOn_iff_encoded]
  simp only [map_encOption_gmwSimWithPadsOpt]
  exact isPPTOn_gmwSimWithPads (Vstar := fun n a z => encB <$> Vstar n a z) hg hlen hf hV'

theorem isPPTOn_gmwSimAttemptOpt {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun p => Vstar p.1 p.2.1 p.2.2)) :
    IsPPTOn (encInstanceAuxInput enc) (encOption encB)
      (fun p : ℕ × α × List Bool =>
        gmwSimAttemptOpt generator (p.1 + 7) (length (p.1 + 7))
          (f p.2.1) (Vstar p.1 p.2.1 p.2.2)) := by
  have hV' := hV.map' (ComputableInPolyTime.of_eq (encOut := encBits) (f := encB) fun _ => rfl)
  rw [isPPTOn_iff_encoded]
  simp only [map_encOption_gmwSimAttemptOpt]
  exact isPPTOn_gmwSimAttempt (Vstar := fun n a z => encB <$> Vstar n a z) hg hlen hf hV'

theorem isPPTOn_gmwRealWithPadsOpt {α β Param : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} {input : Param ↪ List Bool}
    {generator : List Bool → List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    {n s m : Param → ℕ} {a : Param → α} {z w : Param → List Bool}
    {φ : Param → CNF ℕ} {pads : Param → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun p => Vstar p.1 p.2.1 p.2.2))
    (hn : ComputableInPolyTime n input encUnary)
    (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits)
    (hw : ComputableInPolyTime w input encBits)
    (hφ : ComputableInPolyTime φ input encCNF)
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    IsPPTOn input (encOption encB) (fun p =>
      gmwRealWithPadsOpt generator (s p) (m p) (φ p) (w p)
        (Vstar (n p) (a p) (z p)) (pads p)) := by
  have hV' := hV.map' (ComputableInPolyTime.of_eq (encOut := encBits) (f := encB) fun _ => rfl)
  rw [isPPTOn_iff_encoded]
  simp only [map_encOption_gmwRealWithPadsOpt]
  exact isPPTOn_gmwRealWithPads (Vstar := fun n a z => encB <$> Vstar n a z)
    hg hV' hn hs hm ha hz hw hφ hpads

/-! ### Section 3: Query-budgeted machine slicing (`sessionStep`) -/

/-- Query handler for `oneSessionStep`: truncates the oracle reply to `limit` bits and
decrements the remaining query budget `q` by `1`. -/
noncomputable def sessionQueryHandler (limit : ℕ) (req : Unit × List Bool) (q : ℕ) :
    WordOracleComp Unit (List Bool × ℕ) :=
  (fun ans => (ans, q - 1)) <$> (List.take limit <$> ProbOracleComp.query req)

/-- One step of the query-budgeted machine simulation: if both the remaining step budget `rem`
and query budget `q` are positive, executes one machine step via `OpenOracleSimulation.step`
with `sessionQueryHandler limit` and decrements `rem`; otherwise returns `(rem, q, cfg)`
unchanged. -/
noncomputable def oneSessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit : ℕ)
    (st : ℕ × ℕ × FiniteConfig k Bool Control Unit) :
    WordOracleComp Unit (ℕ × ℕ × FiniteConfig k Bool Control Unit) :=
  if st.1 = 0 || st.2.1 = 0 then
    pure st
  else
    (fun p => (st.1 - 1, p.2, p.1)) <$>
      OpenOracleSimulation.step machine sessionQueryHandler limit (st.2.2, st.2.1)

/-- Run `machine` for up to `rem` steps or until `q` oracle queries have been made,
truncating each oracle reply to `limit` bits, and returning the remaining step count and
finite configuration. -/
noncomputable def sessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit rem q : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    WordOracleComp Unit (ℕ × FiniteConfig k Bool Control Unit) :=
  (fun st => (st.1, st.2.2)) <$>
    OracleComp.iterate rem (oneSessionStep machine limit) (rem, q, cfg)

@[simp] theorem sessionStep_zero_rem {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit q : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    sessionStep machine limit 0 q cfg = pure (0, cfg) := rfl

private theorem iterate_oneSessionStep_zero_q {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit n rem : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    OracleComp.iterate n (oneSessionStep machine limit) (rem, 0, cfg) = pure (rem, 0, cfg) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [OracleComp.iterate_succ_bind]
    simp [oneSessionStep, ih]

@[simp] theorem sessionStep_zero_q {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit rem : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    sessionStep machine limit rem 0 cfg = pure (rem, cfg) := by
  simp [sessionStep, iterate_oneSessionStep_zero_q]

theorem sessionStep_succ {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit rem q : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) :
    sessionStep machine limit (rem + 1) (q + 1) cfg =
      (OpenOracleSimulation.step machine sessionQueryHandler limit (cfg, q + 1) >>= fun p =>
        sessionStep machine limit rem p.2 p.1) := by
  simp only [sessionStep, OracleComp.iterate_succ_bind, oneSessionStep,
    Nat.add_one_ne_zero, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Nat.add_sub_cancel, map_bind, bind_map_left]

/-- When `rem ≤ q`, the query budget `q` is never exhausted before `rem` steps, so
`sessionStep` produces the exact same output program as `machine.finiteRunFrom` with
`limit`-truncated replies. -/
theorem sessionStep_eq_finiteRunFrom {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit rem q : ℕ)
    (cfg : FiniteConfig k Bool Control Unit) (h : rem ≤ q) :
    (fun p => p.2.tapes.output) <$> sessionStep machine limit rem q cfg =
      machine.finiteRunFrom
        (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => List.take limit <$> ProbOracleComp.query (op, word)) rem cfg := by
  induction rem generalizing q cfg with
  | zero => simp [finiteRunFrom]
  | succ rem ih =>
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hq' : rem ≤ q' := by omega
    rw [sessionStep_succ, finiteRunFrom, OracleComp.iterate_succ_bind,
      map_bind, map_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [OpenOracleSimulation.step, finiteStep, hs, pure_bind]
      exact ih (q' + 1) cfg (by omega)
    | some control =>
      simp only [OpenOracleSimulation.step, finiteStep, hs,
        bind_pure_comp, bind_map_left, bind_assoc]
      refine congrArg (Bind.bind _) (funext fun coin => ?_)
      cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        simp only [pure_bind]
        exact ih (q' + 1) (cfg.step action symbol move) (by omega)
      | query channel next =>
        simp only [sessionQueryHandler, Functor.map_map, bind_map_left,
          Nat.add_sub_cancel]
        exact congrArg (Bind.bind _) (funext fun ans =>
          ih q' (cfg.receive channel next (List.take limit ans)) hq')

/-- Starting from `FiniteConfig.init machine.initial word` with `T ≤ q`, `sessionStep`
produces the exact same `ProbOracleComp` program as `machine.runOracle T word`. -/
theorem sessionStep_init_eq_runOracle {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (T q : ℕ)
    (word : List Bool) (h : T ≤ q) :
    (fun p => p.2.tapes.output) <$>
        sessionStep machine T T q (FiniteConfig.init machine.initial word) =
      machine.runOracle T word := by
  rw [sessionStep_eq_finiteRunFrom machine T T q _ h,
    _root_.Turing.MultiTapePTM.finiteRunFrom_take_runOracle]

/-- Every finite configuration `cfg` satisfies `FiniteConfig.SpaceBound L L 0 cfg` where
`L := (encFiniteConfig cfg).length`. -/
theorem spaceBound_of_encFiniteConfig {k : ℕ} {Control : Type} [Finite Control]
    (cfg : FiniteConfig k Bool Control Unit) :
    FiniteConfig.SpaceBound (encFiniteConfig cfg).length (encFiniteConfig cfg).length 0 cfg := by
  have htape (tape : Cslib.Turing.BiTape Bool) :
      tape.spaceUsed ≤ (encBiTape encBool tape).length + 1 := by
    have hstack (t : Cslib.Turing.StackTape Bool) : t.length ≤ (encStackTape encBool t).length := by
      rw [encStackTape_apply]
      exact SizedListEncoding.length_le (encA := encOption encBool)
        (encL := encList (encOption encBool)) t.toList
    have hL := hstack tape.left
    have hR := hstack tape.right
    simp only [Cslib.Turing.BiTape.spaceUsed, encBiTape_apply, length_encPair]; omega
  have hpi {Index Value : Type} [Fintype Index] (enc : Value ↪ List Bool)
      (values : Index → Value) (i : Index) :
      (enc (values i)).length ≤ (encPi enc values).length := by
    rw [encPi_apply]
    apply SizedListEncoding.length_elem_le (encA := enc) (encL := encList enc)
    rw [List.mem_ofFn]; exact ⟨Fintype.equivFin Index i, by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [encFiniteConfig_apply, encFiniteCfg_apply, length_encPair, encBits_apply]; omega
  · intro tape
    have h1 := htape (cfg.tapes.workTapes tape)
    have h2 := hpi (encBiTape encBool) cfg.tapes.workTapes tape
    simp only [encFiniteConfig_apply, encFiniteCfg_apply, length_encPair]; omega
  · simp only [encFiniteConfig_apply, encFiniteCfg_apply, length_encPair, encBits_apply]; omega
  · intro channel
    have h1 := hpi (encPair encBits (encBiTape encBool)) cfg.channels channel
    simp only [encFiniteConfig_apply, length_encPair, encBits_apply] at h1 ⊢; omega
  · intro channel
    have h1 := htape (cfg.channels channel).2
    have h2 := hpi (encPair encBits (encBiTape encBool)) cfg.channels channel
    simp only [encFiniteConfig_apply, length_encPair] at h2 ⊢; omega

/-- One step of `oneSessionStep` preserves the countdown and `FiniteConfig.SpaceBound`. -/
theorem mem_support_oneSessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit : ℕ)
    {W T : ℕ} {st next : ℕ × ℕ × FiniteConfig k Bool Control Unit}
    (hrem : st.1 ≤ T) (hcfg : FiniteConfig.SpaceBound W (T - st.1) limit st.2.2)
    (hnext : next ∈ OracleComp.support (oneSessionStep machine limit st)) :
    next.1 ≤ st.1 ∧ next.2.1 ≤ st.2.1 ∧
      FiniteConfig.SpaceBound W (T - next.1) limit next.2.2 := by
  unfold oneSessionStep at hnext
  split_ifs at hnext with hzero
  · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hnext
    exact ⟨le_rfl, le_rfl, hcfg⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hzero
    obtain ⟨p, hp, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have hstep : T - (st.1 - 1) = (T - st.1) + 1 := by omega
    cases hs : st.2.2.tapes.state with
    | none =>
      simp only [OpenOracleSimulation.step, hs] at hp
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hp
      exact ⟨by omega, le_rfl, hcfg.mono le_rfl (by omega) le_rfl⟩
    | some control =>
      simp only [OpenOracleSimulation.step, hs] at hp
      obtain ⟨coin, -, hp⟩ := OracleComp.mem_supportWith_bind_iff.mp hp
      cases htr : machine.tr control st.2.2.tapes.inputSymbol st.2.2.tapes.workTapeSymbols
          st.2.2.answerSymbols coin with
      | step action symbol move =>
        simp only [htr] at hp
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hp
        exact ⟨by omega, le_rfl, hstep ▸ hcfg.step action symbol move⟩
      | query channel nextState =>
        simp only [htr, sessionQueryHandler, Functor.map_map] at hp
        obtain ⟨⟨ans, q'⟩, hans, hp⟩ := OracleComp.mem_supportWith_bind_iff.mp hp
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hp
        obtain ⟨raw, -, hraw⟩ := OracleComp.mem_supportWith_map_iff.mp hans
        rcases Prod.mk.inj hraw with ⟨rfl, rfl⟩; dsimp only
        exact ⟨by omega, by omega,
          hstep ▸ hcfg.receive channel nextState _ (List.length_take_le _ _)⟩

/-- State `(rem, q, cfg)` of `oneSessionStep`, with both budgets in unary: the remaining step
budget `rem`, the remaining query budget `q`, then the machine's finite configuration encoded by
`encFiniteConfig`. Both budgets are framed. -/
noncomputable abbrev encBudgetedConfig {k : ℕ} {Control : Type} [Finite Control] :
    ℕ × ℕ × FiniteConfig k Bool Control Unit ↪ List Bool :=
  encPair encUnary (encPair encUnary encFiniteConfig)

/-- `oneSessionStep` is uniform strict oracle PPT. -/
theorem isOraclePPTOn_oneSessionStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) :
    IsOraclePPTOn
      (encPair encUnary encBudgetedConfig)
      encBudgetedConfig
      (fun p => oneSessionStep machine p.1 p.2) := by
  let encHMid := encPair (encPair (encFinEnum Unit) encBits) encUnary
  let encHIn := encPair encUnary encHMid
  have hhandler : IsOraclePPTOn encHIn (encPair encBits encUnary)
      (fun ⟨limit, req, q⟩ => sessionQueryHandler limit req q) := by
    have hq := (IsOraclePPTOn.query_take' () (input := encHIn)
      (request := fun p => p.2.1.2) (limit := fun p => p.1)
      ((ComputableInPolyTime.snd encUnary encHMid).fst'.snd')
      (.fst encUnary encHMid)).map_with' (output := encPair encBits encUnary)
      (f := fun p ans => (ans, p.2.2 - 1))
      ((ComputableInPolyTime.snd encHIn encBits).prod
        (((ComputableInPolyTime.fst encHIn encBits).snd'.snd').unary_sub' (.const 1)))
    exact (congrArg (IsOraclePPTOn _ _) (by
      funext ⟨limit, ⟨⟨⟩, word⟩, q⟩
      simp only [sessionQueryHandler, Functor.map_map])).mp hq
  have hstep := OpenOracleSimulation.isOraclePPTOn_step machine hhandler
  let encCfg := encFiniteConfig (k := k) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary (encPair encUnary encCfg)
  let encIn := encPair encUnary encSt
  have h1 := ComputableInPolyTime.fst encUnary encSt
  have h2 := ComputableInPolyTime.snd encUnary encSt
  have hcond := (ComputableInPolyTime.bool_or.comp'
    ((h2.fst'.beq (.const 0)).prod (h2.snd'.fst'.beq (.const 0)))).of_enc_eq (encD := encBool)
    (g := fun p : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit =>
      decide ((decide (p.2.1 = 0) || decide (p.2.2.1 = 0)) = true)) (fun _ => rfl)
  unfold oneSessionStep
  apply IsOraclePPTOn.ite' hcond h2.isOraclePPTOn
  have hp1 := ComputableInPolyTime.fst encIn (encPair encCfg encUnary)
  have hp2 := ComputableInPolyTime.snd encIn (encPair encCfg encUnary)
  have hno := (hstep.preprocess'
    (h1.prod (h2.snd'.snd'.prod h2.snd'.fst'))).map_with'
    (f := fun (p : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit)
      (r : FiniteConfig k Bool Control Unit × ℕ) => (p.2.1 - 1, r.2, r.1))
    ((hp1.snd'.fst'.unary_sub' (.const 1)).prod (hp2.snd'.prod hp2.fst'))
  exact (congrArg (IsOraclePPTOn _ _) (by funext p; rfl)).mp hno

/-- `sessionStep` is uniform strict oracle PPT. -/
theorem isOraclePPTOn_sessionStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) :
    IsOraclePPTOn
      (encPair encUnary encBudgetedConfig)
      (encPair encUnary encFiniteConfig)
      (fun p => sessionStep machine p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let encCfg := encFiniteConfig (k := k) (State := Control) (Oracle := Unit)
  let encSt := encPair encUnary (encPair encUnary encCfg)
  let encIn := encPair encUnary encSt
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Unit)
  let L₀ (a : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit) : ℕ := (encCfg a.2.2.2).length
  let T₀ (a : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit) : ℕ := L₀ a + a.2.1
  let inv (a : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit) (_ : ℕ)
      (st : ℕ × ℕ × FiniteConfig k Bool Control Unit) : Prop :=
    st.1 ≤ a.2.1 ∧ st.2.1 ≤ a.2.2.1 ∧ FiniteConfig.SpaceBound (L₀ a) (T₀ a - st.1) a.1 st.2.2
  have hbase (a : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit) : inv a 0 a.2 := by
    refine ⟨le_rfl, le_rfl, ?_⟩
    rw [show T₀ a - a.2.1 = L₀ a from Nat.add_sub_cancel _ _]
    exact (spaceBound_of_encFiniteConfig a.2.2.2).mono le_rfl le_rfl (Nat.zero_le _)
  have hpres (a : ℕ × ℕ × ℕ × FiniteConfig k Bool Control Unit) (i : ℕ)
      (st : ℕ × ℕ × FiniteConfig k Bool Control Unit) (_ : i < a.2.1) (hst : inv a i st)
      (next : ℕ × ℕ × FiniteConfig k Bool Control Unit)
      (hnext : next ∈ OracleComp.support (oneSessionStep machine a.1 st)) :
      inv a (i + 1) next := by
    obtain ⟨h1, h2, h3⟩ := mem_support_oneSessionStep machine a.1
      (T := T₀ a) (by dsimp [T₀]; have := hst.1; omega) hst.2.2 hnext
    exact ⟨h1.trans hst.1, h2.trans hst.2.1, h3⟩
  have hstep := (isOraclePPTOn_oneSessionStep machine).preprocess'
    (((ComputableInPolyTime.fst encIn encSt).fst').prod (.snd encIn encSt))
  have hiter := (IsOraclePPTOn.iterateWith_spec' (input := encIn) (stateEncoding := encSt)
    (count := fun a => a.2.1) (initial := fun a => a.2)
    (step := fun a st => oneSessionStep machine a.1 st)
    ((ComputableInPolyTime.snd encUnary encSt).fst') (.snd encUnary encSt) hstep inv hbase hpres
    (size := fun a => (4 * cf + 6) * ((encIn a).length + 1))
    (PolyBounded.of_forall_le (4 * cf + 6) 1 (fun _ => by simp))
    (by
      intro a i st _ ⟨h1, h2, h3⟩
      have hlen : (encIn a).length =
          2 * a.1 + 1 + (2 * a.2.1 + 1 + (2 * a.2.2.1 + 1 + L₀ a)) := by
        simp only [encIn, encSt, length_encPair, encUnary_apply, List.length_replicate]; rfl
      have hstlen : (encSt st).length =
          2 * st.1 + 1 + (2 * st.2.1 + 1 + (encCfg st.2.2).length) := by
        simp only [encSt, length_encPair, encUnary_apply, List.length_replicate]
      have hT : T₀ a - st.1 ≤ L₀ a + a.2.1 := by dsimp [T₀]; omega
      have hcf' : (encFiniteConfig st.2.2).length ≤ cf * (2 * ((encIn a).length + 1)) :=
        (hcf (L₀ a) (T₀ a - st.1) a.1 st.2.2 h3).trans (Nat.mul_le_mul_left cf (by omega))
      dsimp only [encCfg] at hstlen
      rw [Nat.add_mul, show 4 * cf = 2 * (cf * 2) by omega, Nat.mul_assoc, Nat.mul_assoc]
      omega)).1
  exact hiter.map' (output := encPair encUnary encCfg)
    ((ComputableInPolyTime.fst encUnary (encPair encUnary encCfg)).prod
      ((ComputableInPolyTime.snd encUnary (encPair encUnary encCfg)).snd'))

/-- Every state reachable by `sessionStep` preserves the countdown and `FiniteConfig.SpaceBound`. -/
theorem mem_support_sessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit q : ℕ)
    {W T : ℕ} {st st' : ℕ × FiniteConfig k Bool Control Unit}
    (hrem : st.1 ≤ T)
    (hcfg : FiniteConfig.SpaceBound W (T - st.1) limit st.2)
    (hst' : st' ∈ OracleComp.support (sessionStep machine limit st.1 q st.2)) :
    st'.1 ≤ T ∧ FiniteConfig.SpaceBound W (T - st'.1) limit st'.2 := by
  simp only [sessionStep] at hst'
  obtain ⟨full, hfull, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hst'
  have hinv := OracleComp.iterate_invariant
    (fun (_ : ℕ) (s : ℕ × ℕ × FiniteConfig k Bool Control Unit) =>
      s.1 ≤ T ∧ FiniteConfig.SpaceBound W (T - s.1) limit s.2.2)
    ⟨hrem, hcfg⟩
    (fun _ s _ ⟨hs1, hs2⟩ next hnext => by
      obtain ⟨h1, -, h3⟩ := mem_support_oneSessionStep machine limit hs1 hs2 hnext
      exact ⟨h1.trans hs1, h3⟩)
    full hfull
  exact hinv

/-- Run a `WordOracleComp Unit` program answering every oracle query with `[]`. -/
def runEmptyOracle {α : Type} (prog : WordOracleComp Unit α) : ProbComp α :=
  Prod.fst <$>
    (OracleComp.interpret (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n))
      (fun _ (_ : Unit) => pure ([], ()))) prog).run ()

/-- Running `runSeq` from the exhausted prover state `(false, [])` answers every query with `[]`,
independently of `generator`, `s`, `m`, and `φ`. -/
theorem runSeq_nil_fst {α : Type} (generator : List Bool → List Bool) (s m : ℕ) (φ : CNF ℕ)
    (prog : WordOracleComp Unit α) :
    Prod.fst <$> runSeq generator s m φ prog (false, []) = runEmptyOracle prog := by
  unfold runSeq runEmptyOracle
  induction prog with
  | pure a => rfl
  | liftBind q cont ih =>
    cases q with
    | inl d =>
      change Prod.fst <$> ((StateT.lift (ProbComp.unifFin d)).run (false, []) >>= _) =
        Prod.fst <$> ((StateT.lift (ProbComp.unifFin d)).run () >>= _)
      simp only [StateT.run_lift, bind_assoc, pure_bind, map_bind]
      exact congrArg (Bind.bind _) (funext ih)
    | inr q => exact ih []

/-- Any `IsOraclePPTOn` program remains `IsPPTOn` when interpreted under `runEmptyOracle`. -/
theorem isPPTOn_runEmptyOracle {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {prog : α → WordOracleComp Unit β} (h : IsOraclePPTOn input output prog) :
    IsPPTOn input output (fun a => runEmptyOracle (prog a)) := by
  have hsub := h.run_interpret_preprocess (Caller := α) (State := Unit)
    (operationEncoding := encFinEnum Unit) (stateEncoding := encFinEnum Unit)
    (handler := fun _ _ _ => pure ([], ())) (prepare := id) (initial := fun _ => ())
    (resources := fun _ _ => 0) ComputableTidilyInPolyTime.id'
    (ComputableInPolyTime.const ([], ())).isPPTOn (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) (ComputableTidilyInPolyTime.const 0)
    (fun _ _ _ _ result hres => by
      simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hres
      subst hres; exact ⟨trivial, by simp, by simp⟩)
  exact IsPPTOn.map hsub (ComputableInPolyTime.fst output (encFinEnum Unit))

/-- Complete any remaining steps of a sliced machine run against the exhausted prover state
`(false, [])` and return the final output tape. -/
noncomputable def finishSessionRun {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) (limit : ℕ)
    (st : ℕ × FiniteConfig k Bool Control Unit) : ProbComp (List Bool) :=
  runEmptyOracle ((fun p => p.2.tapes.output) <$> sessionStep machine limit st.1 limit st.2)

/-- `finishSessionRun` is uniform strict PPT. -/
theorem isPPTOn_finishSessionRun {k : ℕ} {Control : Type} [Finite Control]
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit) :
    IsPPTOn (encPair encUnary (encPair encUnary encFiniteConfig)) encBits
      (fun p => finishSessionRun machine p.1 p.2) := by
  let encCfg := encFiniteConfig (k := k) (State := Control) (Oracle := Unit)
  have h1 := ComputableInPolyTime.fst encUnary (encPair encUnary encCfg)
  have h2 := ComputableInPolyTime.snd encUnary (encPair encUnary encCfg)
  have hout := ComputableInPolyTime.finiteCfg_output.comp'
    (ComputableTidilyInPolyTime.finiteConfig_tapes.computableInPolyTime.comp'
      (.snd encUnary encCfg))
  have hrun := isPPTOn_runEmptyOracle
    (((isOraclePPTOn_sessionStep machine).preprocess'
      (h1.prod (h2.fst'.prod (h1.prod h2.snd')))).map' (output := encBits) hout)
  exact (congrArg (IsPPTOn _ _) (by funext p; rfl)).mp hrun

private theorem runSeq_sessionStep_one_add {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ)
    (rem Q : ℕ) (cfg : FiniteConfig k Bool Control Unit)
    (coins : List Bool × List (List Bool)) (rest : List (List Bool × List (List Bool)))
    (msg1 : List Bool) :
    Prod.fst <$> runSeq generator s m φ
        (sessionStep machine limit rem (Q + 1) cfg) (true, coins :: rest) =
      (runTwoRound (honestReply1 generator m φ coins) (honestReply2 s φ coins)
        (sessionStep machine limit rem 1 cfg) (1, msg1) >>= fun p =>
        Prod.fst <$> runSeq generator s m φ
          (sessionStep machine limit p.1.1 Q p.1.2) (false, rest)) := by
  induction rem generalizing cfg with
  | zero => simp [runSeq, runTwoRound]
  | succ rem ih =>
    rw [sessionStep_succ, sessionStep_succ (q := 0)]
    cases hs : cfg.tapes.state with
    | none => simp only [OpenOracleSimulation.step, hs, pure_bind]; exact ih cfg
    | some control =>
      simp only [OpenOracleSimulation.step, hs, bind_pure_comp, bind_map_left,
        runSeq_bind, runTwoRound_bind, runSeq_sample, runTwoRound_sample, map_bind, bind_assoc]
      refine congrArg (Bind.bind _) (funext fun coin => ?_)
      cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        simp only [pure_bind, runSeq_pure, runTwoRound_pure]
        exact ih (cfg.step action symbol move)
      | query channel next =>
        simp only [sessionQueryHandler, Functor.map_map,
          runSeq_map, runTwoRound_map, runSeq_query, runTwoRound_query,
          seqStep, ↓reduceIte, twoRoundStep, Nat.add_sub_cancel,
          Prod.map, id_eq, Nat.reduceBEq, Bool.false_eq_true,
          sessionStep_zero_q, runTwoRound_pure, map_pure, pure_bind]

/-- Splitting a `(Q + 2)`-query `sessionStep` run under `runSeq` into a single two-query session
under `runTwoRound` followed by the remaining `Q`-query `sessionStep` run under `runSeq`. -/
theorem runSeq_sessionStep_two_add {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ)
    (rem Q : ℕ) (cfg : FiniteConfig k Bool Control Unit)
    (coins : List Bool × List (List Bool)) (rest : List (List Bool × List (List Bool))) :
    Prod.fst <$> runSeq generator s m φ
        (sessionStep machine limit rem (Q + 2) cfg) (false, coins :: rest) =
      (runTwoRound (honestReply1 generator m φ coins) (honestReply2 s φ coins)
        (sessionStep machine limit rem 2 cfg) (0, [false, false, false]) >>= fun p =>
        Prod.fst <$> runSeq generator s m φ
          (sessionStep machine limit p.1.1 Q p.1.2) (false, rest)) := by
  induction rem generalizing cfg with
  | zero => simp [runSeq, runTwoRound]
  | succ rem ih =>
    have hQ : Q + 2 = (Q + 1) + 1 := rfl
    rw [hQ, sessionStep_succ, sessionStep_succ (q := 1)]
    cases hs : cfg.tapes.state with
    | none => simp only [OpenOracleSimulation.step, hs, pure_bind]; exact ih cfg
    | some control =>
      simp only [OpenOracleSimulation.step, hs, bind_pure_comp, bind_map_left,
        runSeq_bind, runTwoRound_bind, runSeq_sample, runTwoRound_sample, map_bind, bind_assoc]
      refine congrArg (Bind.bind _) (funext fun coin => ?_)
      cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        simp only [pure_bind, runSeq_pure, runTwoRound_pure]
        exact ih (cfg.step action symbol move)
      | query channel next =>
        simp only [sessionQueryHandler, Functor.map_map,
          runSeq_map, runTwoRound_map, runSeq_query, runTwoRound_query,
          seqStep, Bool.false_eq_true, ↓reduceIte, twoRoundStep, Nat.add_sub_cancel,
          Prod.map, id_eq, beq_self_eq_true, map_pure, pure_bind]
        exact runSeq_sessionStep_one_add machine generator s m limit φ rem Q
          (cfg.receive channel next (List.take limit
            (honestReply1 generator m φ coins (cfg.channels channel).1)))
          coins rest [false, false, false]

/-- Any result in the support of `runTwoRound` lies in `OracleComp.support prog`. -/
theorem mem_support_runTwoRound {β : Type} (f1 f2 : List Bool → List Bool)
    (prog : WordOracleComp Unit β) (s s' : ℕ × List Bool) {result : β}
    (h : (result, s') ∈ (ProbComp.eval (runTwoRound f1 f2 prog s)).support) :
    result ∈ OracleComp.support prog := by
  rw [eval_runTwoRound] at h
  exact ProbOracleComp.mem_support_of_mem _ h

theorem mem_support_gmwSimWithPadsOpt {β : Type} (generator : List Bool → List Bool)
    (s m : ℕ) (φ : CNF ℕ) (prog : WordOracleComp Unit β) (pads : List (List Bool)) {result : β}
    (h : some result ∈ (ProbComp.eval (gmwSimWithPadsOpt generator s m φ prog pads)).support) :
    result ∈ OracleComp.support prog := by
  simp only [gmwSimWithPadsOpt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨ch_guess, -, coins, -, ⟨view, round, challenge⟩, hp, hret⟩ := h
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hret
  split_ifs at hret; cases hret
  exact mem_support_runTwoRound _ _ prog _ _ hp

theorem mem_support_gmwSimAttemptOpt {β : Type} (generator : List Bool → List Bool)
    (s m : ℕ) (φ : CNF ℕ) (prog : WordOracleComp Unit β) {result : β}
    (h : some result ∈ (ProbComp.eval (gmwSimAttemptOpt generator s m φ prog)).support) :
    result ∈ OracleComp.support prog := by
  simp only [gmwSimAttemptOpt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨pads, -, h⟩ := h
  exact mem_support_gmwSimWithPadsOpt generator s m φ prog pads h

theorem mem_support_gmwRealWithPadsOpt {β : Type} (generator : List Bool → List Bool)
    (s m : ℕ) (φ : CNF ℕ) (w : List Bool) (prog : WordOracleComp Unit β)
    (pads : List (List Bool)) {result : β}
    (h : some result ∈ (ProbComp.eval (gmwRealWithPadsOpt generator s m φ w prog pads)).support) :
    result ∈ OracleComp.support prog := by
  simp only [gmwRealWithPadsOpt, ProbComp.eval_bind, PMF.mem_support_bind_iff] at h
  obtain ⟨ch_guess, -, m₀, -, m₁, -, m₂, -, seeds, -, ⟨view, round, challenge⟩, hp, hret⟩ := h
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hret
  split_ifs at hret; cases hret
  exact mem_support_runTwoRound _ _ prog _ _ hp

theorem firstSuccess_mem_or_eq {β : Type} (d : β) (xs : List (Option β)) :
    firstSuccess d xs = d ∨ some (firstSuccess d xs) ∈ xs := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    cases x with
    | none => exact ih.imp id (List.mem_cons_of_mem _)
    | some val => exact Or.inr List.mem_cons_self

theorem mem_support_of_mem_replicate {α : Type} {n : ℕ} {g : ProbComp α} {xs : List α}
    (hxs : xs ∈ (ProbComp.eval (OracleComp.replicate n g)).support) {x : α} (hx : x ∈ xs) :
    x ∈ (ProbComp.eval g).support := by
  induction n generalizing xs with
  | zero =>
    simp only [OracleComp.replicate_zero, ProbComp.eval_pure, PMF.support_pure,
      Set.mem_singleton_iff] at hxs
    subst hxs; cases hx
  | succ n ih =>
    simp only [OracleComp.replicate_succ, ProbComp.eval_bind, ProbComp.eval_map,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hxs
    obtain ⟨y, hy, ⟨ys, hys, rfl⟩⟩ := hxs
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hy
    · exact ih hys hmem

/-- One session of the honest sequential execution on `(rem, cfg)` with fresh prover coins. -/
noncomputable def realSessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ) (w : List Bool)
    (st : ℕ × FiniteConfig k Bool Control Unit) :
    ProbComp (ℕ × FiniteConfig k Bool Control Unit) := do
  let coins ← sampleHonestCoins s φ w
  Prod.fst <$> runTwoRound (honestReply1 generator m φ coins) (honestReply2 s φ coins)
    (sessionStep machine limit st.1 2 st.2) (0, [false, false, false])

/-- One session of the simulated sequential execution on `(rem, cfg)`, repeating
`gmwSimAttemptOpt` `att` times and falling back to `st` on failure. -/
noncomputable def simSessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit att : ℕ) (φ : CNF ℕ)
    (st : ℕ × FiniteConfig k Bool Control Unit) :
    ProbComp (ℕ × FiniteConfig k Bool Control Unit) :=
  firstSuccess st <$>
    OracleComp.replicate att
      (gmwSimAttemptOpt generator s m φ (sessionStep machine limit st.1 2 st.2))

/-- Peeling `K` sessions of `runSeq` on `sessionStep` into `OracleComp.iterate K realSessionStep`
followed by `runEmptyOracle`. -/
theorem eval_replicate_runSeq_sessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m limit : ℕ) (φ : CNF ℕ) (w : List Bool)
    (K : ℕ) (st : ℕ × FiniteConfig k Bool Control Unit) :
    ProbComp.eval (do
      let coinsList ← OracleComp.replicate K (sampleHonestCoins s φ w)
      Prod.fst <$> runSeq generator s m φ
        (sessionStep machine limit st.1 (limit + 2 * K) st.2) (false, coinsList)) =
    ProbComp.eval (do
      let st' ← OracleComp.iterate K (realSessionStep machine generator s m limit φ w) st
      runEmptyOracle (sessionStep machine limit st'.1 limit st'.2)) := by
  induction K generalizing st with
  | zero => simp [runSeq_nil_fst]
  | succ K ih =>
    have hadd : limit + 2 * (K + 1) = (limit + 2 * K) + 2 := by omega
    rw [hadd, OracleComp.replicate_succ, OracleComp.iterate_succ_bind]
    simp only [realSessionStep, bind_assoc, bind_map_left, runSeq_sessionStep_two_add,
      ProbComp.eval_bind, ProbComp.eval_map]
    refine congrArg (PMF.bind _) (funext fun coins => ?_)
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind _) (funext fun p => ?_)
    simpa only [ProbComp.eval_bind, ProbComp.eval_map] using ih p.1

/-- `gmwSeqInteract` on a clocked machine run `machine.runOracle T word` has the exact same output
distribution as `K` iterations of `realSessionStep` followed by `finishSessionRun`. -/
theorem eval_gmwSeqInteract_runOracle_eq_iterate_realSessionStep {k : ℕ} {Control : Type}
    (machine : _root_.Turing.MultiTapePTM k Bool Control Unit)
    (generator : List Bool → List Bool) (s m T K : ℕ) (φ : CNF ℕ) (w word : List Bool) :
    ProbComp.eval (gmwSeqInteract generator s m φ w K (machine.runOracle T word)) =
      ProbComp.eval (do
        let st' ← OracleComp.iterate K
          (realSessionStep machine generator s m T φ w)
          (T, FiniteConfig.init machine.initial word)
        finishSessionRun machine T st') := by
  have hrun := sessionStep_init_eq_runOracle machine T (T + 2 * K) word (by omega)
  have hmap := congrArg (PMF.map (fun p : ℕ × FiniteConfig k Bool Control Unit => p.2.tapes.output))
    (eval_replicate_runSeq_sessionStep machine generator s m T φ w K
      (T, FiniteConfig.init machine.initial word))
  have hlhs : PMF.map (fun p : ℕ × FiniteConfig k Bool Control Unit => p.2.tapes.output)
      (ProbComp.eval (do
        let coinsList ← OracleComp.replicate K (sampleHonestCoins s φ w)
        Prod.fst <$> runSeq generator s m φ
          (sessionStep machine T T (T + 2 * K) (FiniteConfig.init machine.initial word))
          (false, coinsList))) =
      ProbComp.eval (gmwSeqInteract generator s m φ w K (machine.runOracle T word)) := by
    rw [← hrun]
    simp only [pmf_norm, gmwSeqInteract, runSeq_map, Functor.map_map, Prod.map_fst, bind_pure_comp]
  have hrhs : PMF.map (fun p : ℕ × FiniteConfig k Bool Control Unit => p.2.tapes.output)
      (ProbComp.eval (do
        let st' ← OracleComp.iterate K (realSessionStep machine generator s m T φ w)
          (T, FiniteConfig.init machine.initial word)
        runEmptyOracle (sessionStep machine T st'.1 T st'.2))) =
      ProbComp.eval (do
        let st' ← OracleComp.iterate K (realSessionStep machine generator s m T φ w)
          (T, FiniteConfig.init machine.initial word)
        finishSessionRun machine T st') := by
    simp only [pmf_norm, finishSessionRun, runEmptyOracle, OracleComp.interpret_map, StateT.run_map,
      Functor.map_map]
  rw [← hlhs, ← hrhs, hmap]

end Cslib.Crypto.GMW
