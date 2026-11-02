/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import Complexity.Languages.Probabilistic.Oracle.QueryCount

/-!
# External query bounds from the machine clock

Each instruction makes at most one external request and writes at most one symbol per query
buffer. Starting from empty channels, a run of `fuel` instructions therefore makes at most
`fuel` external calls, each with a request length at most `fuel`. Private coins are sampled
independently and do not count as external requests. The bound permits arbitrarily long replies
and arbitrary state shared by the external handlers.

Moreover, because each channel's answer head starts at position `0` on query reception and moves by
at most one cell per instruction, a `fuel`-step run from `initialConfig` never inspects reply
indices at or beyond `fuel`. Replacing every reply by `reply.take fuel` in `finiteRunFrom`
therefore yields the exact same `OracleComp` program as `machine.run`.

## Main results

* `Turing.MultiTapePTM.query_bounds_runFrom`: bounds from a partial run and its initial buffers.
* `Turing.MultiTapePTM.query_bounds_runOracle`: the clock bounds calls and request lengths.
* `Turing.MultiTapePTM.finiteRunFrom_take_init`: truncating replies to the clock preserves the
  exact typed program.

## References

Adapted from Computability/Machines/Turing/MultiTape/Oracle/QueryBounds.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol Control Operation Query State : Type} [DecidableEq Operation]
  {input : List Symbol}

/-- A partial run adds at most one external call per instruction. Requests fit within the
initial buffer bound plus elapsed time, regardless of the oracle's reply sizes. -/
theorem query_bounds_runFrom (machine : MultiTapePTM k Symbol Control Operation)
    (request : Operation → List Symbol → Query) (size : Query → ℕ)
    (hrequest : ∀ op word, size (request op word) ≤ word.length)
    (oracle : Query → StateT State PMF (List Symbol)) (fuel : ℕ)
    (cfg : Config k Symbol Control Operation input) (bound : ℕ)
    (hbuffers : ∀ op, (cfg.channels op).queryBuffer.length ≤ bound)
    (s s' : State) (transcript transcript' : OracleComp.Transcript
      (fun _ : Query => List Symbol)) (output : List Symbol)
    (htranscript : ∀ entry ∈ transcript, size entry.1 ≤ bound)
    (h : (output, s', transcript') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (OracleComp.withTranscript oracle))
      (machine.runFrom (ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => ProbOracleComp.query (request op word)) fuel cfg)).run
          (s, transcript)).support) :
    transcript'.length ≤ transcript.length + fuel ∧
      ∀ entry ∈ transcript', size entry.1 ≤ bound + fuel := by
  induction fuel generalizing cfg bound s transcript with
  | zero =>
    simp only [runFrom_zero, OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    rw [h.2.2]
    exact ⟨by simp, by simpa using htranscript⟩
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp only [runFrom_succ, hs, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      rw [h.2.2]
      exact ⟨by simp, fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)⟩
    | some control =>
      simp only [runFrom_succ, hs, OracleComp.interpret_bind, StateT.run_bind,
        ProbOracleComp.run_interpret_sample, ProbComp.eval_uniform,
        Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
        PMF.mem_support_bind_iff] at h
      obtain ⟨coin, _, h⟩ := h
      cases ha : machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
          cfg.answerSymbols coin with
      | step action symbol move =>
        rw [ha] at h
        have hnext : ∀ op, ((cfg.step action symbol move).channels op).queryBuffer.length ≤
            bound + 1 := by
          intro op
          simp only [Config.step, List.length_append]
          exact Nat.add_le_add (hbuffers op) (symbol op).length_toList_le
        obtain ⟨hcount, hsize⟩ := ih _ (bound + 1) hnext _ _
          (fun entry hentry => (htranscript entry hentry).trans (Nat.le_add_right ..)) h
        exact ⟨by lia, fun entry hentry => by have := hsize entry hentry; lia⟩
      | query op next =>
        simp only [ha, OracleComp.interpret_bind, StateT.run_bind,
          Probability.PMF.monad_bind_eq_bind, ProbOracleComp.interpret_query] at h
        simp only [StateT.run, OracleComp.withTranscript, PMF.bind_map, Function.comp_def,
          PMF.mem_support_bind_iff] at h
        obtain ⟨⟨answer, nextState⟩, _, h⟩ := h
        have hnext : ∀ operation,
            ((cfg.receive op next answer).channels operation).queryBuffer.length ≤ bound := by
          intro operation
          by_cases heq : operation = op
          · subst operation
            simp [Config.receive]
          · simpa [Config.receive, heq] using hbuffers operation
        obtain ⟨hcount, hsize⟩ := ih _ bound hnext _ _ (by
          intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | hentry
          · exact (hrequest op _).trans (hbuffers op)
          · exact htranscript entry hentry) h
        exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount,
          fun entry hentry => (hsize entry hentry).trans (by lia)⟩

/-- From blank channels, the same clock bounds external calls and every request length. -/
theorem query_bounds_runOracle (machine : MultiTapePTM k Symbol Control Operation)
    (fuel : ℕ) (input : List Symbol) :
    (machine.runOracle fuel input).IsQueryBounded fuel ∧
      (machine.runOracle fuel input).QueriesSatisfy fun request => request.2.length ≤ fuel := by
  have hrun (State : Type) (oracle : Operation × List Symbol → StateT State PMF (List Symbol))
      (s s' : State) (output : List Symbol)
      (transcript : OracleComp.Transcript (fun _ : Operation × List Symbol => List Symbol))
      (h : (output, s', transcript) ∈ ((OracleComp.interpret
        (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
          (OracleComp.withTranscript oracle)) (machine.runOracle fuel input)).run
            (s, [])).support) :
      transcript.length ≤ fuel ∧ ∀ entry ∈ transcript, entry.1.2.length ≤ fuel := by
    simpa using query_bounds_runFrom machine (fun op word => (op, word))
      (fun request => request.2.length) (by intros; exact le_rfl) oracle fuel
      (machine.initialConfig input) 0 (by simp [initialConfig])
      s s' [] transcript output (by simp) h
  exact ⟨ProbOracleComp.isQueryBounded_of_length_transcript_le fun State oracle s s' output
      transcript h => (hrun State oracle s s' output transcript h).1,
    ProbOracleComp.queriesSatisfy_of_forall_mem_transcript fun State oracle s s' output
      transcript h => (hrun State oracle s s' output transcript h).2⟩

/-- Agreement with a native configuration up to truncating each channel's reply to `limit`
symbols. -/
structure _root_.Turing.MultiTapeMachine.FiniteConfig.RepresentsTake (limit : ℕ)
    (finite : FiniteConfig k Symbol Control Operation)
    (cfg : Config k Symbol Control Operation finite.tapes.input) : Prop where
  /-- Ordinary configurations correspond. -/
  tapes : finite.tapes.Represents cfg.tapes
  /-- Pending requests agree. -/
  queries : ∀ op, (finite.channels op).1 = (cfg.channels op).queryBuffer
  /-- Answer tapes agree with the `limit`-prefix of each channel's reply. -/
  answers : ∀ op, (finite.channels op).2.Represents
    (fun position =>
      if 0 ≤ position then ((cfg.channels op).answer.take limit)[position.toNat]? else none)
    (cfg.channels op).answerPos

omit [DecidableEq Operation] in
/-- Initial finite storage represents the native initial configuration at any reply truncation
limit. -/
theorem _root_.Turing.MultiTapeMachine.FiniteConfig.representsTake_init (limit : ℕ)
    (state : Control) (input : List Symbol) :
    (FiniteConfig.init (k := k) (Oracle := Operation) state input).RepresentsTake limit
      { tapes := Cfg.init state input } := by
  refine ⟨FiniteCfg.represents_init _ _, fun _ => rfl, ?_⟩
  intro op position
  simp [FiniteConfig.init, Cslib.Turing.BiTape.read_nil]

omit [DecidableEq Operation] in
/-- When every answer head lies strictly before `limit`, the truncated finite configuration sees
the exact same answer symbols as the native configuration. -/
theorem _root_.Turing.MultiTapeMachine.FiniteConfig.RepresentsTake.answerSymbols {limit : ℕ}
    {finite : FiniteConfig k Symbol Control Operation}
    {cfg : Config k Symbol Control Operation finite.tapes.input}
    (h : finite.RepresentsTake limit cfg)
    (hpos : ∀ op, (cfg.channels op).answerPos < (limit : ℤ)) :
    finite.answerSymbols = cfg.answerSymbols := by
  funext op
  rw [FiniteConfig.answerSymbols, Config.answerSymbols, Channel.answerSymbol,
    (h.answers op).head]
  split_ifs with hnonneg
  · have hlt : (cfg.channels op).answerPos.toNat < limit := by
      have := hpos op
      lia
    exact List.getElem?_take_of_lt hlt
  · rfl

omit [DecidableEq Operation] in
/-- An ordinary transition preserves truncated representation. -/
theorem _root_.Turing.MultiTapeMachine.FiniteConfig.RepresentsTake.step {limit : ℕ}
    {finite : FiniteConfig k Symbol Control Operation}
    {cfg : Config k Symbol Control Operation finite.tapes.input}
    (h : finite.RepresentsTake limit cfg)
    (action : Turing.Action k Symbol Control) (symbol : Operation → Option Symbol)
    (move : Operation → SignType) :
    (finite.step action symbol move).RepresentsTake limit (cfg.step action symbol move) := by
  refine ⟨h.tapes.step action, ?_, ?_⟩
  · intro op
    simp only [FiniteConfig.step, Config.step, h.queries]
  · intro op
    simpa only [FiniteConfig.step, Config.step, Option.elim_none] using
      (h.answers op).step (none, move op)

/-- Installing a truncated reply in finite storage represents installing the full reply in native
storage. -/
theorem _root_.Turing.MultiTapeMachine.FiniteConfig.RepresentsTake.receive {limit : ℕ}
    {finite : FiniteConfig k Symbol Control Operation}
    {cfg : Config k Symbol Control Operation finite.tapes.input}
    (h : finite.RepresentsTake limit cfg)
    (op : Operation) (next : Control) (answer : List Symbol) :
    (finite.receive op next (answer.take limit)).RepresentsTake limit
      (cfg.receive op next answer) := by
  refine ⟨⟨rfl, h.tapes.inputPos, h.tapes.workTapes, h.tapes.output⟩, ?_, ?_⟩
  · intro other
    by_cases heq : other = op
    · subst other
      simp [FiniteConfig.receive, Config.receive]
    · simpa [FiniteConfig.receive, Config.receive, heq] using h.queries other
  · intro other
    by_cases heq : other = op
    · subst other
      intro position
      simp [FiniteConfig.receive, Config.receive, Cslib.Turing.BiTape.read_mk₁]
    · simpa [FiniteConfig.receive, Config.receive, heq] using h.answers other

/-- Truncating every reply to `limit` symbols in `finiteRunFrom` produces the exact same typed
program as `runFrom` whenever the remaining fuel keeps every answer head below `limit`. -/
theorem finiteRunFrom_take_eq {spec : OracleSpec.{0, 0} Query}
    (machine : MultiTapePTM k Symbol Control Operation)
    (coin : OracleComp spec Bool)
    (query : Operation → List Symbol → OracleComp spec (List Symbol)) (fuel limit : ℕ)
    (finite : FiniteConfig k Symbol Control Operation)
    (cfg : Config k Symbol Control Operation finite.tapes.input)
    (h : finite.RepresentsTake limit cfg) (hfuel : fuel ≤ limit)
    (hpos : ∀ op, (cfg.channels op).answerPos + (fuel : ℤ) ≤ (limit : ℤ)) :
    machine.finiteRunFrom (fun choices => choices <$> coin)
        (fun op word => List.take limit <$> query op word) fuel finite =
      machine.runFrom coin query fuel cfg := by
  induction fuel generalizing finite with
  | zero => simp [finiteRunFrom, h.tapes.output]
  | succ fuel ih =>
    rw [finiteRunFrom, OracleComp.iterate_succ_bind, map_bind]
    cases hs : cfg.tapes.state with
    | none =>
      simp only [finiteStep, h.tapes.state, hs, pure_bind]
      change machine.finiteRunFrom _ _ fuel finite = _
      rw [ih finite cfg h (by lia) (fun op => by have := hpos op; lia)]
      simp [runFrom, runConfigFrom, MultiTapeMachine.runConfigFrom, hs]
    | some state =>
      have hans : finite.answerSymbols = cfg.answerSymbols :=
        h.answerSymbols (fun op => by have := hpos op; lia)
      simp only [finiteStep, h.tapes.state, h.tapes.inputSymbol,
        h.tapes.workTapeSymbols, hans, bind_assoc, runFrom, runConfigFrom,
        MultiTapeMachine.runConfigFrom, hs, map_bind]
      congr 1
      funext action
      cases action with
      | step action symbol move =>
        simp only [pure_bind]
        refine ih _ _ (h.step action symbol move) (by lia) (fun op => ?_)
        have hmove : ((move op : SignType) : ℤ) ≤ 1 := by cases move op <;> decide
        have := hpos op
        simp only [Config.step]
        lia
      | query op next =>
        simp only [h.queries, bind_map_left, bind_assoc, pure_bind, map_bind]
        congr 1
        funext answer
        refine ih _ _ (h.receive op next answer) (by lia) (fun other => ?_)
        by_cases heq : other = op
        · subst other
          simp only [Config.receive, Function.update_self, zero_add]
          lia
        · have := hpos other
          simp only [Config.receive, Function.update_of_ne heq]
          lia

/-- Over `fuel` steps from blank initial storage, truncating every oracle reply to `fuel` symbols
preserves the exact typed `OracleComp` program. -/
theorem finiteRunFrom_take_init {spec : OracleSpec.{0, 0} Query}
    (machine : MultiTapePTM k Symbol Control Operation)
    (coin : OracleComp spec Bool)
    (query : Operation → List Symbol → OracleComp spec (List Symbol)) (fuel : ℕ)
    (input : List Symbol) :
    machine.finiteRunFrom (fun choices => choices <$> coin)
        (fun op word => List.take fuel <$> query op word) fuel
        (FiniteConfig.init machine.initial input) =
      machine.run coin query fuel input :=
  finiteRunFrom_take_eq machine coin query fuel fuel _ _
    (FiniteConfig.representsTake_init _ _ _) le_rfl (fun _ => by simp [initialConfig])

/-- Specializing `finiteRunFrom_take_init` to `runOracle`: truncating every external reply to
`fuel` symbols preserves the exact `ProbOracleComp` program. -/
theorem finiteRunFrom_take_runOracle (machine : MultiTapePTM k Symbol Control Operation)
    (fuel : ℕ) (input : List Symbol) :
    machine.finiteRunFrom
        (fun choices => choices <$> ProbOracleComp.sample (ProbComp.uniform Bool))
        (fun op word => List.take fuel <$> ProbOracleComp.query (op, word)) fuel
        (FiniteConfig.init machine.initial input) =
      machine.runOracle fuel input :=
  finiteRunFrom_take_init machine _ _ fuel input

end Turing.MultiTapePTM
