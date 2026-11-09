/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Correctness
public import CslibFrontier.Computability.Probabilistic.NativeBatch
public import CslibFrontier.Languages.Probabilistic.Iteration
import Mathlib.Tactic

/-!
# Adaptive raw-interface retention program

An actual `ProbOracleComp` program composes selection, a preformed concurrent query,
full raw response decoding, rational local retention, completion stopping and output.
Selection is a supplied closed randomized *program*, never a success/existence
certificate. It sees the entire visible response history, including unbounded invoice
metadata and earlier requests, and retains its own unbounded private word storage.
It cannot inspect hidden oracle state or issue extra external calls.
The program itself performs every query. Initial `Input.proposals` are ignored.

The exact joint execution law threads one shared oracle memory. Source feasibility,
provenance, resource meters and the final local certificate follow from the program
and the original guarded handler, including rejected/reused requests and cancellations.
There is no finite response alphabet or independence assumption.

This is the executable program layer of [Wang2027], Theorem 5(1), PDF p. 12,
Appendix A.5 p. 16, with the source interface of PDF pp. 4--6. It is **not** a
native realization theorem: copying a full unbounded reply and the runtime parser/
tape handoff are not certified by the existing bounded-prefix oracle-PPT compiler.
Nor does this module establish the quantitative productivity/cost envelopes or an
optimum comparison. Those remain necessary for the source upper endpoint.

## Main definitions

* `program`: the complete bounded adaptive program, returning a mask only on completion.
* `transition`: its derived joint step on visible and arbitrary hidden state.

## Main results

* `run_joint`: exact full joint law of the actual program, without a representation premise.
* `run_invariant`: actual source feasibility and exact resource/provenance ledgers.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention.Selector
open ConcurrentBatch NativeOpenExecution

/-- Visible replies, newest first, and an absorbing explicit halt flag. -/
structure State where
  /-- Complete raw replies, including metadata and rejection packets. -/
  history : List Word
  /-- True once the scheduler halts or the computed completion test succeeds. -/
  stopped : Bool
  /-- Complete submitted requests, newest first, including rejected transactions. -/
  requests : List Word := []
  /-- Unbounded private scheduler storage, retaining previous private random choices. -/
  privateState : Word := []
  deriving DecidableEq

/-- No proposals or oracle information are available before the first call. -/
@[expose] def initial : State := ⟨[], false, [], []⟩

/-- Parse the actual raw replies in chronological order. Caller-supplied proposal
lists play no role in the selection-only program. -/
@[expose] def data (n : ℕ) (x : Input) (s : State) : Input :=
  { x with proposals :=
      (s.history.reverse.flatMap (parseProposals n x.rows.length)).map sourceIndices }

/-- A selection result contains a nonempty preformed batch (or halt) and updated
private scheduler storage. It contains no desired response or output certificate. -/
structure Decision (n : ℕ) where
  /-- A selected nonempty preformed batch, or an explicit policy halt. -/
  batch : Option (Batch n)
  /-- Private scheduler state to retain for subsequent adaptive decisions. -/
  privateState : Word

/-- Stateful closed randomized selection code. Its stored words may be arbitrarily
long; earlier random choices and requests are available at later decisions. -/
abbrev Scheduler (n : ℕ) := Input → State → ProbComp (Decision n)

/-- The actual loop body: decide whether to stop, select before the response,
submit one whole batch, and save its actual full raw reply for local retention. -/
@[expose] def turn {n : ℕ} (choose : Scheduler n) (x : Input) (s : State) :
    ProbOracleComp (fun _ : Unit × Word => Word) State := do
  if s.stopped || complete (data n x s) then
    pure { s with stopped := true }
  else
    let decision ← ProbOracleComp.sample (choose (data n x s) s)
    match decision.batch with
    | none => pure { s with stopped := true, privateState := decision.privateState }
    | some batch =>
      let word ← ProbOracleComp.query ((), encodeBatch batch)
      pure ⟨word :: s.history, false, encodeBatch batch :: s.requests, decision.privateState⟩

/-- Execute at most the supplied number of selection attempts. The original source
handler separately enforces the issued-turn deadline and exactly-once limits. -/
@[expose] def run {n : ℕ} (choose : Scheduler n) (x : Input) (budget : ℕ) :
    ProbOracleComp (fun _ : Unit × Word => Word) State :=
  OracleComp.iterate budget (turn choose x) initial

/-- Report failure unless the executable rational retention scan finds a full cover. -/
@[expose] def result (n : ℕ) (x : Input) (s : State) : Option Word :=
  if complete (data n x s) then some (output (data n x s)) else none

/-- Complete selection-only program on the original raw request/response interface.
No cover or success flag is supplied to the program. -/
@[expose] def program {n : ℕ} (choose : Scheduler n) (x : Input) (budget : ℕ) :
    ProbOracleComp (fun _ : Unit × Word => Word) (Option Word) := result n x <$> run choose x budget

/-- A computed completed cover prevents both scheduling and another oracle call. -/
theorem turn_complete {n : ℕ} (choose : Scheduler n) (x : Input) (s : State)
    (hc : complete (data n x s) = true) :
    turn choose x s = pure { s with stopped := true } := by
  simp [turn, hc]

/-- Once explicitly stopped, the loop never calls the scheduler or oracle again. -/
theorem turn_stopped {n : ℕ} (choose : Scheduler n) (x : Input) (s : State)
    (hs : s.stopped = true) : turn choose x s = pure s := by
  simp only [turn, hs, Bool.true_or, ↓reduceIte]
  congr 1
  cases s
  simp_all

/-- Updating proposals leaves all WSC and feasible-dual promises unchanged. -/
theorem data_valid (n : ℕ) (x : Input) (hx : Valid x) (s : State) : Valid (data n x s) :=
  ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩

/-- Decoding the actual result is derived from the executable completion test. -/
theorem result_decode (n : ℕ) (x : Input) (s : State) (word : Word)
    (hr : result n x s = some word) :
    complete (data n x s) = true ∧
      decodeFamily x.rows.length word = some (outputFamily (data n x s)) := by
  unfold result at hr
  split_ifs at hr with hc
  · cases hr
    exact ⟨hc, decode_output _⟩

/-- A successful result is a cover of the original rows with its derived local
certificate. No successful-output or certification contract is passed to the loop. -/
theorem result_cover (n : ℕ) (x : Input) (hx : Valid x) (s : State) (word : Word)
    (hr : result n x s = some word) :
    (instanceOf x hx).covered ((outputFamily (data n x s)).image Fin.val) =
        (instanceOf x hx).ground ∧
      (instanceOf x hx).cost ((outputFamily (data n x s)).image Fin.val) ≤
        (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e :=
  completed_output _ (data_valid n x hx s) (result_decode n x s word hr).1

private theorem normalize_source (n : ℕ) (x : Input) (s : State)
    (C : Finset (Fin x.rows.length)) :
    (normalize (data n x s) (sourceIndices C)).toFinset = C.image Fin.val := by
  ext j
  simp only [normalize, List.mem_toFinset, List.mem_filter, population, data,
    List.mem_range, sourceIndices_mem, decide_eq_true_eq, Finset.mem_image]
  constructor
  · exact fun h => h.2
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, i, hi, rfl⟩

/-- All candidate families actually visible in the replies, irrespective of whether
local retention accepts them. History is newest first as in the source ledger. -/
@[expose] def available (n m : ℕ) : List Word → Finset (Fin m)
  | [] => ∅
  | word :: history => (parseProposals n m word).foldr (· ∪ ·) ∅ ∪ available n m history

private theorem parsed_union (n m : ℕ) (history : List Word) :
    (history.reverse.flatMap (parseProposals n m)).foldr (· ∪ ·) ∅ =
      available n m history := by
  induction history with
  | nil => rfl
  | cons word history ih =>
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.foldr_append, available]
    rw [← Finset.empty_union ((parseProposals n m word).foldr (· ∪ ·) ∅),
      List.foldr_assoc, ih, Finset.empty_union]
    exact Finset.union_comm _ _

/-- The adaptive program can only output candidates in actual queried responses;
initial proposal data cannot fabricate a successful family. -/
theorem provenance (n : ℕ) (x : Input) (hx : Valid x) (s : State) :
    outputFamily (data n x s) ⊆ available n x.rows.length s.history := by
  have hp := retained_provenance (data n x s) (data_valid n x hx s)
  rw [← outputFamily_image] at hp
  have he : ((data n x s).proposals.map
      (fun P => (normalize (data n x s) P).toFinset)).foldr (· ∪ ·) ∅ =
      (available n x.rows.length s.history).image Fin.val := by
    change (((s.history.reverse.flatMap (parseProposals n x.rows.length)).map sourceIndices).map
      (fun P => (normalize (data n x s) P).toFinset)).foldr (· ∪ ·) ∅ = _
    rw [List.map_map]
    simp only [Function.comp_def, normalize_source, List.foldr_map]
    rw [← Finset.image_empty Fin.val]
    rw [List.foldr_hom (Finset.image Fin.val) (fun C D => (Finset.image_union C D).symm)]
    rw [parsed_union]
  rw [he] at hp
  intro i hi
  have hm := hp (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
  have heq : j = i := Fin.ext he
  exact heq ▸ hj

noncomputable section
variable {n : ℕ} {Private : Type}

/-- Derived execution kernel. Private coins select a batch before one response is
sampled; that same response updates the raw history and the full hidden ledger. -/
@[expose] def transition (env : Environment Unit Private) (choose : Scheduler n) (x : Input) :
    State × Memory Unit Private → PMF (State × Memory Unit Private) := fun (s, memory) =>
  if s.stopped || complete (data n x s) then PMF.pure ({ s with stopped := true }, memory)
  else (ProbComp.eval (choose (data n x s) s)).bind fun decision => match decision.batch with
    | none => PMF.pure ({ s with stopped := true, privateState := decision.privateState }, memory)
    | some batch => (env ((), encodeBatch batch) memory).map fun (reply, privateState) =>
        (⟨reply.word :: s.history, false, encodeBatch batch :: s.requests, decision.privateState⟩,
          memory.record ((), encodeBatch batch) reply privateState)

/-- The program's actual stateful semantics, retaining its entire oracle memory. -/
@[expose] def execute {α : Type} (env : Environment Unit Private)
    (p : ProbOracleComp (fun _ : Unit × Word => Word) α) (memory : Memory Unit Private) :
    PMF (α × Memory Unit Private) :=
  (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
      (handler env)) p).run memory

/-- One actual program turn has the explicit selected-before-response joint law. -/
theorem turn_joint (env : Environment Unit Private) (choose : Scheduler n) (x : Input)
    (s : State) (memory : Memory Unit Private) :
    execute env (turn choose x s) memory = transition env choose x (s, memory) := by
  unfold turn
  simp only [transition]
  split_ifs
  · simp [execute, OracleComp.interpret_pure, StateT.run_pure]
  · simp only [execute, OracleComp.interpret_bind, ProbOracleComp.run_interpret_sample,
      StateT.run_bind, PMF.monad_bind_eq_bind, PMF.bind_map]
    congr 1
    funext decision
    obtain ⟨batch, privateData⟩ := decision
    cases batch with
    | none => simp [OracleComp.interpret_pure, StateT.run_pure]
    | some batch =>
      simp only [Function.comp_apply, OracleComp.interpret_bind,
        ProbOracleComp.interpret_query, OracleComp.interpret_pure, StateT.run_bind,
        StateT.run_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      change ((env ((), encodeBatch batch) memory).map (fun (reply, privateState) =>
        (reply.word, memory.record ((), encodeBatch batch) reply privateState))).map
          (fun (word, next) =>
            ((⟨word :: s.history, false, encodeBatch batch :: s.requests, privateData⟩ : State),
              next)) = _
      rw [PMF.map_comp]
      rfl

/-- The complete joint path law is derived from the code. In particular the oracle
private state, all query/response correlations, bills and durations are not resampled. -/
theorem run_joint (env : Environment Unit Private) (choose : Scheduler n) (x : Input)
    (budget : ℕ) (memory : Memory Unit Private) :
    execute env (run choose x budget) memory =
      ObservedProcess.stateLaw (transition env choose x) budget (initial, memory) := by
  induction budget with
  | zero => simp [run, execute, OracleComp.iterate_zero, ObservedProcess.stateLaw,
      OracleComp.interpret_pure, StateT.run_pure]
  | succ budget ih =>
    simp only [run, OracleComp.iterate_succ, execute, OracleComp.interpret_bind,
      StateT.run_bind, PMF.monad_bind_eq_bind] at *
    rw [ih, ObservedProcess.stateLaw]
    congr 1
    funext pair
    exact turn_joint env choose x pair.1 pair.2

/-- The program's visible history consists exactly of the replies actually queried. -/
@[expose] def Consistent (s : State) (memory : Memory Unit Private) : Prop :=
  s.history = memory.events.map (fun event => event.reply.word) ∧
    s.requests = memory.events.map Event.request

/-- Exact source meters and provenance together with the actual visible input history. -/
@[expose] def Invariant (limits : Limits n) (s : State)
    (memory : Memory Unit (ServerState n Private)) : Prop :=
  NativeBatch.Invariant limits memory ∧ Consistent s memory

/-- Every supported turn preserves the actual source/raw history and resource
ledgers, whether its request is accepted, reused, rejected, or deadline-truncated. -/
theorem transition_invariant (limits : Limits n) (sample : Sampler n Private)
    (choose : Scheduler n) (x : Input) (s next : State)
    (memory memory' : Memory Unit (ServerState n Private))
    (hi : Invariant limits s memory)
    (hs : (next, memory') ∈
      (transition (environment limits sample) choose x (s, memory)).support) :
    Invariant limits next memory' := by
  simp only [transition] at hs
  split_ifs at hs
  · rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact hi
  · obtain ⟨batch, _, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    obtain ⟨batch, privateData⟩ := batch
    cases batch with
    | none =>
      rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact hi
    | some batch =>
      obtain ⟨⟨reply, privateState⟩, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
      cases he
      refine ⟨NativeBatch.serve_invariant limits sample memory hi.1 _ reply privateState hr, ?_⟩
      obtain ⟨hwords, hrequests⟩ := hi.2
      exact ⟨congrArg (List.cons reply.word) hwords,
        congrArg (List.cons (encodeBatch batch)) hrequests⟩

/-- Full actual execution from an empty source memory has the same guarded source
history, token bill and external duration. No target success or admission premise. -/
theorem run_invariant (limits : Limits n) (sample : Sampler n Private)
    (choose : Scheduler n) (x : Input) (budget : ℕ) (seed : Private)
    (s : State) (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (execute (environment limits sample) (run choose x budget)
      ⟨ConcurrentBatch.initial seed, []⟩).support) : Invariant limits s memory := by
  rw [run_joint] at hs
  induction budget generalizing s memory with
  | zero =>
    rw [ObservedProcess.stateLaw, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨NativeBatch.initial_invariant limits seed, rfl, rfl⟩
  | succ budget ih =>
    obtain ⟨⟨mid, prior⟩, hm, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    exact transition_invariant limits sample choose x mid s prior memory (ih mid prior hm) hs

/-- The program's proposal ledger is the original raw-channel ledger, with no
extra proposals reconstructed from hidden oracle information. -/
theorem available_consistent (s : State) (memory : Memory Unit Private)
    (hc : Consistent s memory) (m : ℕ) :
    available n m s.history = NativeBatch.nativeAvailable (n := n) m memory.events := by
  rw [hc.1]
  induction memory.events with
  | nil => rfl
  | cons event events ih => simp only [List.map_cons, available, NativeBatch.nativeAvailable, ih]

/-- End-to-end original-source admission is derived for every scheduler program.
A successful returned mask uses only proposals in actual accepted source batches,
including when other issued calls in those batches were canceled. -/
theorem run_source_provenance (limits : Limits n) (sample : Sampler n Private)
    (choose : Scheduler n) (x : Input) (hx : Valid x) (budget : ℕ) (seed : Private)
    (s : State) (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (execute (environment limits sample) (run choose x budget)
      ⟨ConcurrentBatch.initial seed, []⟩).support) :
    outputFamily (data n x s) ⊆
      NativeBatch.sourceAvailable x.rows.length memory.privateState.history := by
  have hi := run_invariant limits sample choose x budget seed s memory hs
  obtain ⟨_, _, _, hledger⟩ := hi.1
  have hp := provenance n x hx s
  rw [available_consistent s memory hi.2, hledger x.rows.length] at hp
  exact hp

/-- Exact common-oracle joint law of the emitted mask and all accumulated resources.
This equality includes every oracle-private state and the full transcript; it does
not assume a success probability, integrability or a bounded total invoice. -/
theorem program_joint (env : Environment Unit Private) (choose : Scheduler n) (x : Input)
    (budget : ℕ) (memory : Memory Unit Private) :
    execute env (program choose x budget) memory =
      (ObservedProcess.stateLaw (transition env choose x) budget (initial, memory)).map
        (fun (s, memory) => (result n x s, memory)) := by
  simp only [program, execute, OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map]
  change (execute env (run choose x budget) memory).map _ = _
  rw [run_joint]

/-- Every supported completed execution has the actual source bill and maximum
concurrent-duration sum, original deadline/nonreuse guarantees, and derived output
provenance. This assertion covers failed executions as well as successful ones. -/
theorem run_resources (limits : Limits n) (sample : Sampler n Private)
    (choose : Scheduler n) (x : Input) (hx : Valid x) (budget : ℕ) (seed : Private)
    (s : State) (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (execute (environment limits sample) (run choose x budget)
      ⟨ConcurrentBatch.initial seed, []⟩).support) :
    WellFormed limits memory.privateState ∧
      tokenBill memory.events = (memory.privateState.history.map Exchange.tokens).sum ∧
      elapsed memory.events = memory.privateState.elapsed ∧
      outputFamily (data n x s) ⊆
        NativeBatch.sourceAvailable x.rows.length memory.privateState.history := by
  obtain ⟨hw, ht, hd, _⟩ :=
    (run_invariant limits sample choose x budget seed s memory hs).1
  exact ⟨hw, ht, hd,
    run_source_provenance limits sample choose x hx budget seed s memory hs⟩

/-- Original-source correctness of every actually successful program output:
decoding, provenance, full original-instance coverage, the derived feasible-dual
certificate and deadline feasibility are simultaneous facts about the same run. -/
theorem program_correct (limits : Limits n) (sample : Sampler n Private)
    (choose : Scheduler n) (x : Input) (hx : Valid x) (budget : ℕ) (seed : Private)
    (word : Word) (memory : Memory Unit (ServerState n Private))
    (hs : (some word, memory) ∈
      (execute (environment limits sample) (program choose x budget)
        ⟨ConcurrentBatch.initial seed, []⟩).support) :
    ∃ C : Finset (Fin x.rows.length), decodeFamily x.rows.length word = some C ∧
      C ⊆ NativeBatch.sourceAvailable x.rows.length memory.privateState.history ∧
      (instanceOf x hx).covered (C.image Fin.val) = (instanceOf x hx).ground ∧
      (instanceOf x hx).cost (C.image Fin.val) ≤
        (x.rho : ℝ) * ∑ e ∈ (instanceOf x hx).ground, (instanceOf x hx).dual e ∧
      memory.privateState.elapsed ≤ limits.deadline := by
  rw [program_joint, PMF.mem_support_map_iff] at hs
  obtain ⟨⟨s, prior⟩, hr, he⟩ := hs
  obtain ⟨hout, rfl⟩ := Prod.mk.inj he
  have hr' : (s, prior) ∈ (execute (environment limits sample) (run choose x budget)
      ⟨ConcurrentBatch.initial seed, []⟩).support := by rwa [run_joint]
  obtain ⟨hcover, hcost⟩ := result_cover n x hx s word hout
  obtain ⟨⟨⟨_, _, hdeadline, _, _⟩, _, _, _⟩, _⟩ :=
    run_invariant limits sample choose x budget seed s prior hr'
  exact ⟨outputFamily (data n x s), (result_decode n x s word hout).2,
    run_source_provenance limits sample choose x hx budget seed s prior hr', hcover,
    hcost, hdeadline⟩

end

end Cslib.Probability.StochasticOracle.NativeRetention.Selector
