# Programs, probability laws, and native realization

## Typed free programs

[OracleSpec](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Basic.lean#L54) assigns a reply type to each request. [OracleComp](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Basic.lean#L57) is `PFunctor.FreeM` over that signature. A node issues one request and chooses its continuation from the reply; a leaf returns a value. This is well-founded adaptive interaction. It is not an unbounded looping language. A general signature may have infinitely many replies, so well-foundedness should not be paraphrased as a single uniform finite depth for every generic program [cslib-frontier][complexitylib].

[interpret](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Basic.lean#L72) uses the free-monad universal interpreter. The handler can target any suitable monad: a PMF gives a law, a state transformer stores private evolving oracle state, and another `OracleComp` implements an oracle reduction. `interpret_interpret` is the algebraic substitution law. For reductions with private coins, [ProbOracleComp.simulate](../../CslibFrontier/Languages/Probabilistic/Oracle/Substitution.lean) substitutes only external calls and preserves sampling for the outer interpreter; the [worked client](../workflows/probabilistic-workflows.md#substitute-an-oracle-while-preserving-private-samples) shows the program and its composition proof. The file credits Devon Tuma and the VCVio work of Tuma, Quang Dao and collaborators; reuse of `PFunctor.FreeM` comes from cslib.

[ProbComp](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Basic.lean#L141) specializes the signature to requests `n : Nat` returning `Fin (n+1)`. Its [eval](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Basic.lean#L159) answers with the exact uniform PMF. Finite branching gives ordinary finite sampling trees. The type is not restricted to fair coins and does not attach a cost to Lean computations inside continuations. A long pure function and a short pure function can have the same query count.

## One semantics with several views

[CslibFrontier/Languages/Probabilistic/Semantics.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Semantics.lean) provides `evalWith` for independent handlers, `supportWith` for allowed response sets, and `runWith` for the joint law of result and final hidden state. Support correspondence lemmas connect probabilistic execution to relational reachability. [runWith](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Oracle/Interaction.lean#L61) specializes this to private samples plus typed external calls; [Oracle/Simulation.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Simulation.lean) states its invariant, simulation and state-representation rules (`runWith_invariant`, `runWith_map_state`, `runWith_run_interpret`, …), so proofs need not unfold it to the interpretation of the sum handler. Inductive proofs over a client use `ProbOracleComp.induction`, whose cases are a returned value, a private draw `sample (ProbComp.unifFin n) >>= cont` (stepped by `runWith_sample_bind`; `runWith_sample_bind_congr` exchanges draws with the same law and `runWith_sample_bind_comm` moves a draw past any program) and an external call `query q >>= cont`; a client interpreted through a handler of programs runs against the handler programs' runs (`runWith_interpret`, `runWith_interpret_sumHandler`). Interactive provers, cryptographic oracles and data-structure methods reuse this stateful semantics.

To run an oracle program as a closed sampler, import [Oracle/Run.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Run.lean) and write `A.run O`: private draws stay uniform and each external query `q` runs the probabilistic oracle `O q`. A deterministic oracle `f` is `fun q => pure (f q)`. The simp lemmas `run_pure`, `run_bind`, `run_map`, `run_query` and `run_sample` step a concrete program, `run_simulate` runs a reduction built with `ProbOracleComp.simulate` by running each handler program against `O`, and `eval_run` gives its law as the interpretation at the `PMF` level. Fixed-instance security experiments state the challenger's oracle this way instead of spelling out the sum handler; the real experiment of [Primitives/PRF/Finite.lean](../../CslibFrontier/Crypto/Primitives/PRF/Finite.lean) samples a key and returns `A.run fun x => pure (F key x)`. The word-level games `prfRealGame`/`prfIdealGame`, the `BlockCipher` PRP games of [Computational/PseudorandomPermutation.lean](../../CslibFrontier/Crypto/Computational/PseudorandomPermutation.lean), `weakPrfRealGame`/`weakPrfIdealGame`, the multi-key, coin and Even–Mansour word games and `evalBooleanOracle` have the same shape, `(adversary n []).run fun request => …`; a proof that unfolds one of them to the `PMF` level rewrites with `eval_run`, or unfolds `ProbOracleComp.run` before applying `ProbOracleComp.eval_interpret`.

When the oracle keeps state, import [Oracle/RunState.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/RunState.lean) and write `A.runState O`, where each `O q` is a `StateT σ ProbComp` program; `runState_lift` reduces a memoryless oracle to `run`, and `eval_runState` gives the law as `runWith`. `A.runLog O` returns the result with the log of queries and replies, oldest first. `A.runLogWith O` lets the oracle read the log so far and refuse a query (`O log q = none`), which is answered with `default` and not logged; one-time and no-repeat signing or MAC oracles take this form. A query-bounded program leaves a log no longer than its bound (`IsQueryBounded.length_runLog_le`, `IsQueryBounded.length_runLogWith_le`), from `measure_runState_le`, the stateful form of `OracleComp.IsCostBounded.measure_le`. Every logged pair is a reply that the oracle's program can produce (`forall_mem_runLogWith`); [Game/Forgery.lean](../../CslibFrontier/Crypto/Game/Forgery.lean) uses it to show that every answered signature verifies, so strong and existential forgery coincide for unique signatures. See [OracleRunState.lean](../../CslibFrontierTests/OracleRunState.lean) for checked examples.

For non-terminal normalization of oracle experiments and reductions, import `CslibFrontier.Languages.Probabilistic.Oracle.Norm` ([Oracle/Norm.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Norm.lean)) and run `simp only [runWith_norm, pmf_norm]`. The set is priority-ordered and is not claimed to be confluent: where several rules match the same term, the higher-priority ones win. These fold closed `ProbComp.eval ((OracleComp.interpret …).run s)` and nested stateful handler runs (`runWith_run_interpret`, `runWith_interpret_sumHandler_eta`) into `ProbOracleComp.runWith`, and `runWith_lift` rewrites a run against a lifted memoryless oracle to `(OracleComp.evalWith …).map (·, s)`. The default-priority rules step concrete `ProbOracleComp.runWith`, `OracleComp.runWith`, `OracleComp.evalWith`, and `ProbOracleComp.sample` `do`-blocks to `PMF.bind`, `PMF.pure`, and `PMF.map` in one pass while leaving black-box `adversary` calls intact inside `ProbOracleComp.runWith`. `OracleComp.interpret_bind` and `StateT.run_bind` are intentionally excluded: bottom-up `simp` would otherwise split concrete reduction `do`-blocks inside `StateT.run` before `ProbOracleComp.eval_run_interpret_eq_runWith` or `ProbOracleComp.runWith_run_interpret` matches the enclosing run. See [RunWithNorm.lean](../../CslibFrontierTests/RunWithNorm.lean) for checked examples covering black-box adversaries, nested reduction handlers, concrete `do` programs, and stateless `evalWith`.

The final state matters: an adversary can observe consequences of an earlier call through later calls. Equality of output marginals alone is too weak for general oracle substitution. Native open-program realization therefore quantifies equality of the joint result/state law against every stateful PMF handler, not just against a fixed memoryless oracle.

The adjacent modules supply different semantic tools, not alternative machines:

| Tool | Source | Role |
|---|---|---|
| Pathwise query/cost bounds | [CslibFrontier/Languages/Probabilistic/QueryCount.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/QueryCount.lean) | Bound every branch by an explicit request charge |
| Lifted oracles in sum handlers | [Sum/Lift.lean](../../CslibFrontier/Languages/Probabilistic/Sum/Lift.lean) | Pull an unchanged state out of `sumHandler`: `sumHandler_lift`, and `run_interpret_sumHandler_readOnly` for lifted private coins beside an external handler that only reads the state, reduce the run to an interpretation at the initial state |
| Transcripts | [CslibFrontier/Languages/Probabilistic/Transcript.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Transcript.lean) | Retain dependent request/reply pairs |
| Memoization and random oracles | [CslibFrontier/Languages/Probabilistic/RandomOracle.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/RandomOracle.lean) | Repeated calls receive the same cached random answer |
| Bidirectional random permutations | [CslibFrontier/Languages/Probabilistic/RandomPermutation.lean](../../CslibFrontier/Languages/Probabilistic/RandomPermutation.lean) | Forward/inverse consistency, `bidirDedup` query deduplication, and sampling without replacement; [RandomPermutation/ExtPermsCard.lean](../../CslibFrontier/Languages/Probabilistic/RandomPermutation/ExtPermsCard.lean) bounds the permutations taking `k` prescribed values at `k` distinct points (`card_extPerms_ofFn_mul_descFactorial_le`) |
| Ideal cipher model | [CslibFrontier/Languages/Probabilistic/IdealCipher.lean](../../CslibFrontier/Languages/Probabilistic/IdealCipher.lean) | Key-indexed forward/inverse permutations (`uniform_interpret_eq_lazy`) and coupled `untilBad` reduction to forgetful sampling (`abs_sub_uniformPerm_forgetful_le`) |
| Coupled simulation and until-bad | [CslibFrontier/Languages/Probabilistic/UntilBad.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/UntilBad.lean) | Transfer probability bounds until a designated bad event |
| Replay/forking | [CslibFrontier/Languages/Probabilistic/Forking.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/Forking.lean) | Explicit tapes and reply lists permit repeatable adversary runs |
| Exact rational laws and Bernoulli coins | [CslibFrontier/Languages/Probabilistic/Rational.lean](../../CslibFrontier/Languages/Probabilistic/Rational.lean) | Exact rational output probabilities (`ProbComp.evalRat`, `ProbComp.eval_eq_iff_evalRat_eq`) and loop-free clamped rational coins (`ProbComp.bernoulliRat`) |

An ideal full random function table and its lazy cache can have the same transcript distribution while radically different representation costs. Their semantic equivalence does not, by itself, prove efficient materialization of the full table. At the open `OracleComp` level, forward-only query deduplication wraps a program with `memoize OracleComp.query` ([Memoize.lean](../../CslibFrontier/Foundations/Control/Monad/Memoize.lean)), while bidirectional permutation reductions wrap `PermOracleSpec α` programs with `RandomPermutation.bidirDedupStep` / `RandomPermutation.bidirDedup` ([RandomPermutation.lean](../../CslibFrontier/Languages/Probabilistic/RandomPermutation.lean), checked in [RandomPermutationSwitching.lean](../../CslibFrontierTests/RandomPermutationSwitching.lean)) so both forward hits in `dom(cache)` and inverse hits in `ran(cache)` reuse cached answers without repeating underlying oracle calls, preserving `evalPerm π` output laws, pathwise query bounds, and pairwise-distinct domain/range cache invariants.

## Closed strict polynomial time

[IsPPTOn](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/PPT.lean#L71) asserts that the encoded output distribution of `program a` equals the encoded run of one finite-control fair-coin multitape machine for `c * (|input a|+1)^d` steps, with one choice of machine, `c` and `d` for all `a`. The run is clocked. [CslibFrontier/Computability/Probabilistic/PPT/Clock.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/PPT/Clock.lean) turns the clocked witness into an intrinsically halting machine while charging the clock construction and maintenance. This is strict polynomial time, not expected polynomial time.

Encodings are embeddings into bit lists. This gives faithful representations but does not by itself supply an efficient decoder. The `length_le` theorem derives a polynomial bound on every supported output's encoded length. Congruence transfers the property through equality of laws. Deterministic `ComputableInPolyTime.isPPTOn` embeds ordinary native computation.

For a common coin and output budget, import [CoinTape.Bounds](../../CslibFrontier/Computability/Probabilistic/CoinTape/Bounds.lean). `IsPPTOn.exists_total_seeded_evaluator_with_length` gives one polynomial envelope in the complete encoded input length. Every uniform tape at least that long replays the program exactly, and every supported encoded output fits the same envelope. The native evaluator returns a supported result even on shorter tapes; that support guarantee does not claim the correct distribution for a short tape. [Checked examples](../../CslibFrontierTests/SeededEvaluatorBounds.lean) use a random word sampler to exercise empty input, short tapes, longer uniform tapes and genuinely different supported outputs.

[IsPPT](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Parameter.lean#L48) passes security parameter `n` in unary together with an auxiliary bit string. The clock is polynomial in the combined encoded input, not only in `n`. This is why a security claim over arbitrarily long samples is not automatically the same as a conventional polynomial-length ensemble statement.

For explicit concrete step schedules rather than existentially quantified polynomial clocks, import [Computability/Probabilistic/Time.lean](../../CslibFrontier/Computability/Probabilistic/Time.lean). `ComputesInTimeOn input output t program` (and parameterized `ComputesInTime output t program` on `encPair encUnary encBits`, charging `t n aux.length`) requires one finite-control fair-coin machine whose `t a`-step closed run matches `(ProbComp.eval (program a)).map output` and has actually halted (`final.tapes.state = none`) on every supported execution at step `t a`. Requiring actual halting rather than clock-cutoff fuel makes `ComputesInTimeOn.mono` hold unconditionally for arbitrary upper bounds `t₁ a ≤ t₂ a` without requiring `t₂` to be computable, lifts plain deterministic `ComputableInTimeAndSpace` certificates with exact step bound `t` (`ComputableInTimeAndSpace.computesInTimeOn`), and composes sequential phases in `2 * t₁ a + t₂' a + 4` steps (`ComputesInTimeOn.bind`, `.preprocess`, `.map`), independent of the component machines' state or work-tape counts. `isPPTOn_iff_exists_polyBounded_computesInTimeOn` and `isPPT_iff_exists_polyBounded_computesInTime` prove equivalence with `IsPPTOn` and `IsPPT`; [checked examples](../../CslibFrontierTests/Crypto/ConcreteSecurity.lean) verify concrete step counts, unconditional padding, and the `IsPPTOn` round-trip.

At the snapshot, the inspectable formal abstract (since retired) used a finite random tape and a deterministic polynomial-time evaluator: [StrictPPT](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/Randomized.lean#L36). [strictPPT_iff](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CryptographyBridge.lean#L59) related that presentation to the library's native predicate. It was an equivalent presentation with an explicit bridge, not a second unconnected efficiency convention.

For a list traversal with known component seed laws, import
[Languages.Probabilistic.Traverse.CoinTape](../../CslibFrontier/Languages/Probabilistic/Traverse/CoinTape.lean).
`ProbComp.eval_mapM_of_uniformList` realizes the original `list.mapM program` by splitting
`list.length * width` uniform bits into rows and applying `List.zipWith evaluate` to inputs
and rows. The component law is required only for values in the supplied list. Repeated input
values still receive independent blocks; empty lists and width zero are allowed. This semantic
law supplies an explicit seed allocation, while native efficiency remains a separate obligation.
The existing `IsPPTOn.mapM` certificate uses this same law. The
[checked examples](../../CslibFrontierTests/TraversalCoinTape.lean) show distinct seeds at repeated
inputs and a component law that deliberately fails outside the input list.

## Open oracle polynomial time

[WordOracleComp](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Oracle.lean#L56) combines private samples with a finite operation name and an arbitrary bit-string payload/reply. [IsOraclePPTOn](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Oracle.lean#L63) chooses one native oracle machine and one polynomial clock before all inputs, state types, stateful handlers and starting states. The equality includes the final external state.

For the word-oracle interface, interpretation, query accounting and native realization are distinct proof tasks:

```mermaid
flowchart TB
program["Word-oracle program family<br/>free requests and continuations"]
handler["Stateful PMF handler<br/>external oracle state"]
law["Joint probability law<br/>result and final state"]
queries["Pathwise request bound<br/>chosen request charges"]
certificate["IsOraclePPTOn certificate<br/>explicit input and output encodings"]
machine["One native oracle machine<br/>one polynomial clock"]
program -->|"interpret"| law
handler -->|"answer and update state"| law
program -->|"bound every branch"| queries
program -.->|"prove realization"| certificate
law -.->|"match the full law"| certificate
certificate -->|"supply a uniform witness"| machine
```

The dotted arrows are obligations of [IsOraclePPTOn](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Oracle.lean#L63): one machine and clock must match the joint law for every input, stateful handler and starting state. The [request bound](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Languages/Probabilistic/QueryCount.lean) has no implication arrow to that certificate; it does not charge arbitrary pure continuation work. For a closed program, [IsPPTOn](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/PPT.lean#L71) instead matches the encoded output law without an external handler.

Request construction, tape-head movement and reply inspection are charged machine operations. The external handler's own computation is outside the oracle machine's cost. A reply may be arbitrarily long; the machine cannot return an arbitrarily long output for free, as the native `length_le` theorem records. Typed oracle interfaces need explicit word encodings and realization certificates before this native predicate applies.

Finite first-order fair-coin oracle-machine syntax is available by importing
[`Probabilistic/Universal/Description.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Universal/Description.lean).
Its `eDesc` word is a right-associated tuple encoding in field order: unary work-tape count, unary
user-state count, unary operation count, unary initial-state tag, then the transition-table
`encList`. The first four fields are framed in turn; the final `encList` tail has one frame per entry.
Each entry frames its key before the branch-pair tail. Keys put ordinary state/input/work-head
fields before answer heads, and branches are ordered `false`, then `true`. Consequently `descLen`
is a rigorous unary model-code length, not an implementation byte size. Invalid initial, successor
or operation tags halt locally, and an
invalid operation tag makes no external call. `Desc.toMachine` leaves operation dispatch inside a
finite machine (`Fin operations`), while `Desc.runWith_toMachine` identifies the full output and
shared-state law for every stateful handler. The supplied fuel remains an external clock and the
handler's own computation remains outside it. This layer provides syntax and denotation only: it
does not yet provide a fixed universal interpreter, its controller/copying/marshalling resource
map, or a PPT/QROM certificate. The complete
[`OracleDescription.lean` client](../../CslibFrontierTests/OracleDescription.lean) separately runs
one fixed logging handler and checks adaptive queries, zero clock and malformed-tag boundaries.

For explicit concrete step and query schedules on word-oracle programs, import [Computability/Probabilistic/Oracle/Time.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/Time.lean). `ComputesOracleInTimeOn input output t program` (and parameterized `ComputesOracleInTime`) requires one finite-control oracle machine that matches the joint output and external-state law under `ProbOracleComp.runWith` across all shared stateful handlers within `t a` steps and has actually halted (`final.1.tapes.state = none`) on every supported execution at step `t a`. Actual halting gives unconditional step monotonicity (`ComputesOracleInTimeOn.mono`); `ComputesOracleInTimeOn.query_bounds` shows that every `t a`-step execution makes at most `t a` external queries of payload length at most `t a`, while `ComputesOracleInTimeAndQueriesOn` and `ComputesOracleInTimeAndQueries` track a separate query budget `q` alongside `t` when `q` is much smaller than the step count. Plain deterministic computations (`ComputableInTimeAndSpace.computesOracleInTimeOn`) and closed halting programs (`ComputesInTimeOn.computesOracleInTimeOn`, `ComputesOracleInTimeOn.computesInTimeOn`) lift without step overhead, `query_take_pair` and `query_take` give explicit linear step bounds for bounded-prefix oracle calls, and buffered closed/open compositions (`bind_sample_left`, `bind_sample_right`, `preprocess`, `map`) charge `2 * t₁ a + t₂' a + 4` steps while preserving external query budgets. `isOraclePPTOn_iff_exists_polyBounded_computesOracleInTimeOn` and `isOraclePPT_iff_exists_polyBounded_computesOracleInTime` connect these explicit-time predicates back to `IsOraclePPTOn` and `IsOraclePPT`, with stateful execution and round-trip checks in [CslibFrontierTests/Crypto/ConcreteSecurity.lean](../../CslibFrontierTests/Crypto/ConcreteSecurity.lean).

[CslibFrontier/Computability/Probabilistic/Oracle/Substitution.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Oracle/Substitution.lean) closes an efficient open program under efficient stateful oracle replacement. The principal endpoint `IsOraclePPTOn.run_interpret_preprocess_open` includes an invariant and controlled growth of replies and encoded handler state. Merely saying that each call is polynomial time would permit iterated state doubling and does not imply a polynomial total run. The underlying [CslibFrontier/Computability/Probabilistic/Realization/OpenOracleSimulation.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/Realization/OpenOracleSimulation.lean) supplies a machine-configuration simulation; the public theorem is supported by that realization.

Saved-coin execution reuses `MultiTapePTM.runConfigFromCoins` from
[`CoinTape.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/CoinTape.lean).
The native [`Replay/WithOracle.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Replay/WithOracle.lean)
controller reads a supplied bit before executing the source instruction, so a query retains that
bit's branch and the original request/reply channels. `ReplayWithOracle.run_coins` equates the
complete programs in `2 * coins.length + 1` transitions, including the final stop. The controller's
own private samples may be discarded only under a stateless coin law. Its auxiliary-tape operations
are shared with the native clock in
[`Machine/AuxiliaryTape.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Machine/AuxiliaryTape.lean).
That controller bound assumes prepared tapes. The native `exists_oracleReplay` theorem in
[`Replay/WithOracleInput.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Replay/WithOracleInput.lean)
adds pair decoding and virtual-input marking, proving a linear clock in the entire encoded
`(coins, input)` pair and actual halting. The shared pair preparer also serves closed replay.

[`Oracle/Replay.lean`](../../CslibFrontier/Computability/Probabilistic/Oracle/Replay.lean) exposes
`MultiTapePTM.isOraclePPTOn_runCoins` and `IsOraclePPTOn.exists_savedCoins`. The latter starts with
an actual certified oracle-PPT program, fixes one bit per native instruction, and gives an efficient
replay whose polynomial-length uniform coin tape reproduces the joint encoded-output and external
state law for every stateful handler. Replies remain on their original channels; replay does not
copy an unbounded reply into a configuration encoding. This completes the replay prerequisite
[#2579](https://github.com/cslib-community/cslib-frontier/issues/2579). The full Schnorr ROM forking
reduction built on it is in
[`SchnorrSignature/Security.lean`](../../CslibFrontier/Crypto/Computational/SchnorrSignature/Security.lean).

[`Oracle/ReplayParameter.lean`](../../CslibFrontier/Computability/Probabilistic/Oracle/ReplayParameter.lean)
starts from a public-key length bound `keyC * (n + 1)^keyD`.
`IsOraclePPT.exists_savedCoins_of_length_le` uses one uniform tape of length
`c * (2*n + 2 + keyC*(n + 1)^keyD)^d`, independent of the key. Replay takes only the prefix
specified by the original full-input machine clock. Equality holds for every key within the
bound and retains the complete external state; the handler's own randomness stays external.
`IsOraclePPT.exists_savedCoins_of_keyGen` derives the bound from actual strict-PPT key generation.
[`CoinTape/QueryBounds.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/CoinTape/QueryBounds.lean)
bounds calls on every fixed tape, including tapes outside the intended sampling support.

[`RandomOracle/Simulation.lean`](../../CslibFrontier/Crypto/Protocols/Signature/RandomOracle/Simulation.lean)
transports such joint-state mixtures through the existing shared-world signature game. Its
`eval_worldRealize_eq_bind` includes the cache and signing log before final verification, and works
with any acceptance rule. In particular, final-message freshness permits repeated signing queries.
These shared laws complete [#2652](https://github.com/cslib-community/cslib-frontier/issues/2652);
the full efficient Schnorr reduction is in `SchnorrSignature/Security.lean`.

[`Signature/WordRandomOracle.lean`](../../CslibFrontier/Crypto/Computational/Signature/WordRandomOracle.lean)
routes Boolean channel `false` to signing and `true` to hashing. All word hash payloads remain
distinct, and digest replies use an injective encoding. `wordEufCmaGame` is the resulting EUF-CMA
game of a native word forger in the shared world, and `ROMSignature.EUFCMA` asks that every
uniform oracle-PPT word forger win it with negligible probability. `exists_eufCmaGame_savedCoinForger`
starts from key generation with a polynomial bound on supported public keys (which strict-PPT key
generation supplies through `IsPPTOn.length_le`) and an actual `IsOraclePPT` word forger, and proves
equality of `wordEufCmaGame` and the explicit-coin EUF-CMA game. One native machine
and clock work uniformly for all digest types and encodings, including parameter-dependent ones.
Its native replay
certificate charges the whole `(n, pk, coins)` input, the key-length guard, tape truncation, and
the existing total pair decoder. Oversized keys return the empty pair without calls; every tape
obeys the parameter-only call bounds, including tapes outside the sampling support. Plain
`ComputableInPolyTime.encoding_comp` supplies the encoded machine input.

This completes the generic word-forger adapter
[#2636](https://github.com/cslib-community/cslib-frontier/issues/2636). The scheme's signer, hash
handler and final verifier still run in the existing typed shared world. Native realizations of
those components and Schnorr's concrete query encoding are separate obligations; the full efficient
Schnorr forking reduction is in `SchnorrSignature/Security.lean`. Repeated signing/hash and
fresh/replayed-message examples are checked in
[`Crypto/WordRandomOracle.lean`](../../CslibFrontierTests/Crypto/WordRandomOracle.lean).

## Exact versus approximate randomness

`ProbComp.uniform` permits exact finite uniform laws. A fair-coin machine with a fixed finite time bound has dyadic probabilities, so exact uniform sampling on three elements cannot follow simply from writing that program. This is a mathematical consequence of the definitions, not a reported failure. The sampling libraries distinguish power-of-two/dyadic laws, bounded samplers and approximate modular sampling. Group protocols can retain exact ideal PMFs and separately prove closeness and native efficiency of a word-level sampler.

For a concrete field with exact fair-bit sampling, import [Sampling/F4](../../CslibFrontier/Computability/Probabilistic/Sampling/F4.lean). `F4.sample` draws the two Boolean coordinates of Mathlib's `QuadraticAlgebra (ZMod 2) 1 1`, where the generator satisfies `θ² = θ + 1`. `F4.eval_sample` proves exact uniformity over its four elements, and `F4.isPPTOn_sample` supplies the strict-PPT certificate under `F4.encoding`, the standard pair encoding of those coordinates. Addition, subtraction and multiplication have `F4.computableInPolyTime_add`, `F4.computableInPolyTime_sub` and `F4.computableInPolyTime_mul` certificates for the same encoding. These are fixed-field lookup certificates; they do not supply uniform arithmetic for a growing extension degree. Probability-only clients can import [the sampler semantics](../../CslibFrontier/Languages/Probabilistic/Sampling/F4.lean) without the machine calculus. [Checked clients](../../CslibFrontierTests/F4Sampling.lean) compose the sampler into runtime-varying lists with the full independent uniform vector law.

When an optional sampler feeds a randomized continuation, [PMF/Option/Bind.lean](../../CslibFrontier/Probability/PMF/Option/Bind.lean) provides `PMF.bind_option_apply_of_some`. A successful-part law `μ (some a) = mass * ν a` gives the scaled successful continuation plus `μ none * k none b`. This retains the actual failure branch without conditioning it away. The bounded-sampler Boolean-test proof uses the same law; [checked examples](../../CslibFrontierTests/PMFOptionBind.lean) distinguish accepting and rejecting failure branches while success flips a fresh fair bit.

Randomized Word-RAM takes another convention: one instruction may sample uniformly from any fitted finite interval. Its query count and `unifBitCost` are explicit currencies; neither equals the strict fair-coin runtime without a further implementation theorem. See [the RAM discussion](../algorithms-and-memory/wordram-and-bridges.md).

### Binary-counter exponential iteration and multitape Schöning k-SAT

Iterating a strict-PPT round `R a` times via [`Computability/Probabilistic/Adaptive.lean`](../../CslibFrontier/Computability/Probabilistic/Adaptive.lean) or [`Computability/Probabilistic/Repeat.lean`](../../CslibFrontier/Computability/Probabilistic/Repeat.lean) encodes the round count in unary (`encUnary`), which is polynomial only when `R a` is polynomially bounded. For exact-exponential randomized algorithms where `R a` is exponential in input parameters while workspace must stay polynomial, [`Probabilistic/Loop/Space.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Loop/Space.lean) proves `runsInSpace_toNTM_seq_repeatUntilBlank`: given closed `RunsWords` specifications for preparation within `t₁` steps, every normal and terminal body round within `t` steps, and the final phase within `t₂` steps, preparation establishes the state invariant, normal rounds preserve it and leave the loop tape nonblank, the terminal round leaves that tape blank, and the final-phase specification covers every supported final state. Each phase begins and ends in a `wordsCfg` with all work-tape heads reset to zero, so these time bounds imply that every replay prefix keeps every work-tape head inside `window B = [-B, B]`, where `B = max t₁ (max t t₂)`. Consequently, `seq prep (seq (repeatUntilBlank body) lastM)` stays within workspace `k * (2 * max t₁ (max t t₂) + 1)` across arbitrarily many rounds, independent of the round count. Building on that space invariant, [`Computability/Probabilistic/ExponentialIterate.lean`](../../CslibFrontier/Computability/Probabilistic/ExponentialIterate.lean) provides `IsPPTOn.exists_multiTapePTM_iterate_binary`, `IsPPTOn.exists_multiTapePTM_iterateWith_binary`, and `IsPPTOn.exists_multiTapePTM_repeatAnyBool_binary`: given a polynomial-time computable binary count `R : α → ℕ` (into `encNat`, so `|encNat (R a)|` is polynomial whenever `R a ≤ 2 ^ poly(|input a|)`) and a strict-PPT step, one finite-control fair-coin `MultiTapePTM` realizes `OracleComp.iterate (R a)` (or short-circuiting Boolean OR amplification) in deterministic worst-case halting time `(R a + 1) * C * (|input a| + 1) ^ D` and polynomial `machine.toNTM.RunsInSpace` independent of `R a`.

[`Complexity/FineGrained/SchoeningMachine.lean`](../../CslibFrontier/Computability/Complexity/FineGrained/SchoeningMachine.lean) applies binary-counter amplification and approximate modular sampling (`ProbComp.sampleModNat`) to realize Schöning's randomized local-search `k`-SAT algorithm [schoening99][schoening99] on fair-coin multitape Turing machines over `encCNF` (`CNF ℕ`), complementing the unit-cost `rand` Word-RAM realization in [`Algorithms/WordRAM/Schoening/Amplify.lean`](../../CslibFrontier/Algorithms/WordRAM/Schoening/Amplify.lean) and the pure Markov-chain bound in [`Complexity/FineGrained/Schoening.lean`](../../CslibFrontier/Computability/Complexity/FineGrained/Schoening.lean). Because clause lengths `m ≤ k` need not be powers of two, each walk step draws `w = 2 n + k + 3` fair bits (`n = φ.numVars`) via `sampleModNat w m`: `le_fairWalk_toReal` and `half_mul_succeedProb_trial_le_fairTrial` show that across `3 n` steps the cumulative dyadic bias satisfies `(1 - k / 2 ^ w) ^ (3 n) ≥ 1 / 2`, preserving at least half of the ideal single-trial success probability. Running `2 * schoeningTrials k φ.numVars c` binary-counted trials (`computableInPolyTime_two_mul_schoeningTrials`) yields `exists_multiTapePTM_KSAT`: for every fixed `k ≥ 3` and amplification parameter `c : ℕ`, one fair-coin `MultiTapePTM` halts on every branch within `C * (((2 (k - 1)) / k) ^ φ.numVars * (|encCNF φ| + 1) ^ E)` steps and `C * (|encCNF φ| + 1) ^ E` work-tape cells (`machine.toNTM.RunsInSpace`), outputs `PMF.pure [false]` whenever `φ ∉ KSAT k` (including formulas that violate width `k`), and accepts every `φ ∈ KSAT k` with probability at least `1 - Real.exp (-c)`. Setting `c = 2` gives `exists_decidesWithBoundedErrorInTime_KSAT` (`DecidesWithBoundedErrorInTime encCNF (KSAT k) T`) and the `(4 / 3) ^ n` `3`-SAT specialization `exists_decidesWithBoundedErrorInTime_ThreeSAT`, exercised on concrete formulas in [`CslibFrontierTests/BranchingAndSchoening.lean`](../../CslibFrontierTests/BranchingAndSchoening.lean).

## Known Limitations

No expected-PPT machine predicate was identified in the surveyed probabilistic computability modules. The existing [ZPP definition](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/ZPP.lean#L79) uses native polynomial-time `Option Bool` trials: every returned Boolean is correct and at least half of the polynomial-length seeds return an answer. It is [proved equal to `RP ∩ coRP`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/ZPP.lean#L266); an expected-polynomial-time characterization is not modeled here. See its [machine-model account](../machines-and-classes/verifiers-counting-interaction.md). This survey did not inspect every low-level composition proof or run the `ppt` tactic. Query-bounded ideal algorithms and native realizable algorithms remain distinct interfaces in the model map.

[complexitylib]: ../sources.md#complexitylib
[schoening99]: ../sources.md#schoening99
