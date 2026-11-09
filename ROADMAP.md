# Roadmap

The directions Complexitylib aims to cover, grouped by area. This file lists directions only:
status, progress and completion notes live on the linked issues and pull requests, module
docstrings describe what is proved, and the [README](README.md) and the curated formal abstracts
present completed results. A PR edits this file when it opens or closes a direction.

A direction is complete only when its machine, resource and quantitative conclusions are proved
for the actual algorithms, with explicit models, encodings and assumptions. An abstract algorithm,
a class definition or an assumed reconstruction theorem does not complete it. Search Mathlib,
CSLib and this library before starting, and check upstream work.

The [pre-rewrite roadmap][archive] is the archive of past detail and design records, including
the FHE industrial context, the first-order design decisions and the repository's history.

## Programs

| Program | Issues |
| --- | --- |
| Frontier program: ambitious theorems toward the research frontier | [#897]; its tracks are linked below |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798], audit [#884] |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862], from [#456] |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949], [#939] |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#1104] |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640], [#643] |
| Crypto frontier track: Kilian's succinct arguments | [#999] |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002] |
| STOC manuscript headline results: faithful models, quantitative bounds and algorithmic guarantees | [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527) |

| A Verso guide with a chapter per area | [#585] |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124] |
| Proof automation: predictable polynomial-time certificate search | [#1155] |

STOC submission 191 remains incomplete: Theorem 4 still needs native binary algorithm/resource
certificates,
general response/resource execution, asymptotic approximation consequences and the stated
Set Cover approximation-hardness transfer; the executable rational-cost greedy batch and its
harmonic/logarithmic comparison with every risk-feasible competitor are proved.
Exact rational-power threshold evaluation agrees with the real-log convention, but its
native binary resources remain unproved. The emitted rational batch now has pathwise
total token-bill and parallel deadline bounds derived from individual call caps; this
now composes with the actual response law through a finite conditional resource table,
with one event for certified success, bill cap and parallel deadline. This is not a native
machine or an unrestricted response/resource execution certificate.
Theorem 5 now has a finite-transcript conditional-history expected-cost accounting lemma
with a correlated client. Actual proposed/retained-set finite executions now derive
both productive-count bridges and conditional-history binomial coverage bounds;
the comparison recurrence is identified with Mathlib's binomial law. The retained
family carries the local dual certificate. The universal revealed-cover observable
is not yet composed with a universal selection-only machine/output model or the
lower-cost accounting theorem in the original component; the finite behavioral
policy assembly below now supplies that connection. Actual retained-completion reach bounds and the finite stopped conditional-mean
bill sum are proved. Response-dependent accrued bills are connected by the finite tower identity.
The binomial survival series now has derived sum `r/p` for `p>0`; every finite actual
response-bill expectation is bounded by `c*r/p`. Noncompletion probabilities and
nonnegative marginal expected bills are summable. An infinite full-history response law and its conditional next-response kernels are
constructed in `AdaptivePath` using Ionescu–Tulcea. Its finite cylinder expectations
are now identified with the finite accounting recursion by `integral_responseHistory`,
including a correlated actual-bill client. Almost-sure eventual retained completion is proved via cylinder expectations and
Borel–Cantelli under the stronger all-history productivity envelope. The actual nonnegative total bill is now defined as the supremum of accrued bills;
monotone convergence proves almost-sure finiteness, real integrability and expectation
at most `c*r/p` from explicit nonnegativity and conditional cost bounds.
Response-dependent correlated billing and empty-ground/certain-productivity clients
exercise the bridge.
`AdaptiveReachable` now derives finite completion/binomial and stopped-bill bounds,
a.s. completion and total-bill integrability from positive-probability issued-history
envelopes. Its actual selected-batch joint law has proved factorization, positive-batch
conditioning and tower/envelope composition; null histories and batches impose no
productivity/cost envelope. An unreachable poisoned-history correlated client checks
that the old all-history envelopes really fail. Finite alphabets remain required.
`AdaptiveStopping` now reuses Mathlib hitting times for measurable first/capped
completion indices, proves the actual survival-series mean and `r/p` bound, and
connects capped physical execution with stopped accounting. Supported per-response
latency contracts give a measurable joint deadline/completion/dual-certificate event
with the binomial probability lower bound; actual capped token cost has the finite
survival bound. Correlated, null-history, early-stop, zero-budget/empty-ground and
`p=1` clients check these interfaces. `SelectionPolicy` now separates a fixed oracle
from arbitrary randomized choice/halt/output kernels, with selection-only provenance
from all buffered proposals rather than local retention. `SelectionLowerBound` and
`SelectionDeadline` derive universal token and necessary deadline-binomial bounds
from supported selected-batch envelopes. `SelectionOptimum` constructs an admissible
retaining witness, bounds the infimum over all admissible policies, and proves the
matching-envelope `1/eta` ratio. Correlated, randomized halt/output and uncertified
buffering clients check that this is a broader policy class. These are fixed finite-
alphabet behavioral semantics; encoded PTM realization, general measurable-alphabet
coverage and native machine resources remain open. For Theorem 6, `ResidualCover` now
constructs arbitrary disjoint promised X3C blocks with the source triple/fallback weights,
derives dual/integral optima one, recovers the block partition from incidence and the
missing block from the actual residual, and verifies both local certificates.
`ResidualPolicy` derives exact attained one/two-turn costs and their adaptivity ratio
over all finite behavioral policies, including mixed first batches and randomized
conditional selection/extraction. An overlapping-triple, five-block client checks the
strict ratio 5/3 and universal competitor bounds. These are the source's general finite
construction and behavioral numerical endpoints. `NativeOneTurn` now constructs
behavioral tables from two actual clocked native fair-coin machines surrounding one
external batch, conditioning retained private state on the observed action. Joint
laws, raw output encoding, all finite observables and supported-halting clock padding
are preserved. `NativeResidualOneTurn` derives the one-turn cost lower bound for this
concrete admitted protocol class, normalizing unproposed failed outputs without
strengthening successful-output-only provenance. A native two-bit client checks a
nontrivial 1/3 posterior, encoding, halting/padding and source-instance cost/admission.
`NativeOpenExecution` now derives actual multi-query open-native transition/path
laws, retaining full work tapes, communication channels, oracle private state and
raw query/reply/resource history. General discrete PMF disintegration and
`ObservedProcess` construct complete-public-history behavioral kernels without
finite private-state/observation alphabets. `NativeOpenSelection` preserves the
joint path/success/bill/duration law under successful-output-only provenance,
including failed fabricated outputs and accepted empty covers. A real native
work-tape/answer-dependent two-query client derives correlated execution, early
stopping, bill 5 and duration 19/4; an infinite-hidden-type client checks full
observed-history conditioning. `NativeUnboundedExecution` now removes a common
instruction clock by constructing increasing actual halted-state masses, with
missing mass recorded as divergence. Complete native stopped states and derived
behavioral stopped observations have identical joint laws, including successful
output provenance, query history, accumulated bill and external duration. A real
native geometric waiting loop proves almost-sure termination, positive live mass
at every finite clock, expected bill 4 and duration 7/2; a sure-divergence client
checks that nontermination is not a halted failure. `NativeInterface` now connects
actual native transition tables, fair saved-coin replay and selected-before-response
interfaces to this unbounded stopped law. Preparing a request never samples its
response; dispatch retains the full native/oracle state and records the same raw
reply and charges. Derived selected-signal posteriors preserve the full joint law,
and two interface ticks equal one original instruction. Cofinal clocks identify
complete stopped interface/native/behavioral laws, including divergence and
successful-output provenance. A complete client reuses the actual correlated
work-tape and unbounded waiting machines and checks a positive-probability query
posterior before its response. `NativeEpoch` now actually executes silent
computation to the first selected query or committed halt, retaining silent
divergence. Its pre-response seek law is independent of the response handler,
preserves oracle memory and receipts, and has a proved pause/resume identity with
the original native terminal law. Actual epoch prefixes append at most one query
record per decision; halt decisions add none. Full observed-history kernels
factor through the actual selected epoch before sampling its response. A concrete
unbounded native singleton-opportunity client instantiates the finite quantitative
policy API with matching joint record/output/cost/duration laws, certified success
1/2 and expected bill 4. The existing universal lower theorem proves cost at least
4 for every admissible one-turn behavioral competitor meeting that success target.
The client's nonempty preformed singleton batch, exactly-once opportunity use,
maximum latency and concrete cutoff are checked; correlated two-query and sure
silent-divergence clients also pass. The general finite-opportunity concurrent
protocol now checks actual binary whole-batch packets before response sampling:
nonempty preformed requests, exactly-once opportunity use, turn/deadline guards,
per-call cutoff/deadline cancellation, accrued token invoices and concurrent maxima.
Arbitrary native executions and actual source stopping boundaries preserve source
feasibility, candidate-mask provenance and exact joint resource meters. Rejected
native transactions are silent source computation. Actual selected-batch full-history
kernels and finite-prefix resumption retain hidden correlation and divergence.
A correlated three-opportunity/two-batch client checks early success, cutoff and
deadline cancellation, reuse and zero-budget rejection; an actual native packet-writing
PTM derives the two-call memory/resource law. A constructed finite joint trajectory
table instantiates the quantitative oracle at one reached physical snapshot. This
batch-local transfer is not a compiler from arbitrary native policies into finite
tables. Whole-policy native traces now avoid that finite abstraction: actual silent
source epochs retain accrued receipts on divergence, preserve native/source meters
and SelectionOnly provenance, and terminate or diverge after at most the finite
turn budget plus one epoch. Their complete readback equals the original unbounded
native terminal law. General discrete selected-history kernels derive resource
accounting and lower/upper conditional-cost comparisons for arbitrary native metadata;
a finite conditional upper envelope gives finite expected bill bounded by that envelope
times the actual source turn budget.
The universal cost theorem fixes one oracle and seed before quantifying over every
finite-control admitted native competitor. A real two-batch packet-writing PTM has
issued count two, expected bill 13 and latency 8. A geometric-metadata client proves
unbounded positive-mass invoices, excludes a lossless finite invoice alphabet, and
discharges a nonzero universal per-issued cost envelope for every native competitor.
General discrete native history rewards now transfer revealed progress and retained
productivity without a finite response alphabet. Reached selected-response coverage
caps and original SelectionOnly output provenance derive the actual native success
lower bound `η*r_b*c/p`, without an integrability or lower-optimum premise. The extra
silent completion epoch provably issues no batch; native covering-output probability
is bounded by the binomial tail at the actual source turn budget. Actual locally
retained receipts satisfy the reverse binomial coverage bound and stopped invoice
survival-sum bound, hence `c*r_a/p`, under the conditional productivity and stop-at-cover
contracts. A correlated concurrent native batch has nonempty certified retained
coverage probability 1/2 and a computed conditional invoice envelope. A concrete
packet-writing/output machine proves original native SelectionOnly admission and
success probability one, instantiates positive lower and upper cost bounds, and
checks that silent halting adds no binomial trial.
Actual native lower-latency envelopes now derive the exact physical deadline
allowance `min(u, floor(D/ℓ))`: an issued receipt resumes live native code, live
epoch indices force prior issued turns, and actual accrued durations bound those
turns. Later receipt observables are provably no-call padding, including retained
bills on silent divergence. The assembled original-native accepted-by-deadline
event satisfies both the success-level cost lower bound and the refined binomial
tail. Zero external deadline forbids accepted nonempty covers without extra
envelopes. Correlated/canceled two-batch and successful-output clients instantiate
the actual latency and joint bounds. This uses external interface duration, not
compiled physical timers.
The upper selector's rational local phase now has one uniform finite-control binary
native machine over runtime incidence rows, binary rational weights/dual prices and
proposal lists. It computes normalization, coverage differences, exact local tests,
retention, a completion decision and the original source output mask. Native loop
state-size/resource certificates and real-valued retention/certificate/provenance
correspondence are derived. The actual open native local phase terminates and
preserves all previously received oracle memory, token bills and external duration.
A correlated source-report client constructs its local input from actual proposals;
the original local machine starts from prepared decoded data. A complete `OracleComp` selector program now composes
preformed batch selection, full raw responses, exact rational retention, completion
stopping and source-mask output. Its derived joint law and actual guarded-source
admission preserve hidden-state correlation, provenance, cancellation invoices and
concurrent duration. Initial proposal data is ignored. A two-turn proper-partial
cover client checks actual history-dependent queries and the full joint result.
An actual finite-control full-reply reader now writes and issues the raw request,
scans the complete response and preserves its joint private state/invoice/duration.
The native output compiler buffers that response on a real work tape from a blank
initial buffer. General actual native `seq` composition now preserves unbounded
terminal laws, including divergent phases, without common phase clocks; a reader
can hand its real buffer to arbitrary native continuation code. These laws follow
from native instructions and stopped limits, not a supplied representation.
One uniform native raw-history processor now parses every concurrent opportunity,
skips canceled calls and arbitrary invoice metadata, checks original mask lengths
and performs exact rational retention/completion/output. Its polynomial local
clock is derived in all encoded runtime bytes, even malformed huge length headers.
For every actual guarded raw-program run, native parsing agrees with the source
decoder without a supplied source-validity premise. Actual native local stopping
and the joint word/memory law preserve hidden correlation, provenance and both
resource ledgers; a correlated two-query client derives the successful native local
output from actual source execution. The processor starts with an encoded raw
history on its input tape. A combined actual native response program now copies
the full report to a real buffer, reserves/writes the boundary marker, rewinds the
buffer and executes a native continuation through virtual-input redirection. Its
whole-configuration unbounded law preserves channels, oracle memory and divergent
continuation mass; no prepared-buffer or common-clock premise is supplied. The
retention specialization derives a native continuation from the parser/rational
computability proof and emits a source mask on computed completion. Correlated
cancellation and unbounded geometric-invoice sources check the same complete native
program, including nonempty covers and whole-policy trace compatibility.
Context is fixed when this specialization's code is constructed: this is a
query/retention program, not the uniform adaptive selector. A separate runtime-context
transport milestone now preserves arbitrary ordinary tape functions and nonzero
heads through that response compiler. One actual finite-control two-query program
appends the first full reply's frame to a runtime word, issues the resulting word
as its second request and restores the context head/inner flag using native
rewind/erase instructions. Its derived full-world and readback laws preserve the
same private oracle state, correlated replies, invoices and external durations.
Its original entry context is already on a native work tape. A constructed pure
initializer now loads that tape from original rational-instance/startup input on
blank native work tapes, clears scratch storage and restores the input cursor
before the same two-query carrier. The derived whole-law/readback connection
preserves arbitrary native consumer divergence and shared resource observations.
The concrete initializer computes empty-history completion, ignores fabricated
initial proposals, and records zero turn/opportunity allowances in the stop bit.
One machine works for all encoded startup data and a fixed correlated geometric
source, including a nonempty feasible-dual cover instance, unbounded first replies,
zero allowances and empty ground. A native initial guard now reads a computed
dispatch bit, emits the framed initial output and halts without an oracle call on
initial completion or zero allowances. Its exact stopped law composes with the
blank-tape initializer and preserves prior oracle memory/resources; a correlated
unbounded-reply client checks the live branch of the same machine. The older
unconditional carrier remains available. The guarded live branch still makes two
raw calls without a post-response check (and can exceed a one-turn allowance);
semantic post-response/control enforcement and source-admitted query selection
are not yet realized. This is a concrete binary
startup ABI, not a conventional external source/PTM encoding bridge.
A separate runtime-control ABI now has uniform native semantic post-response
processing: actual histories/private words and turn/planning/allotment counts are
updated, rational retention/completion is recomputed, and a guard packet is written
to tape zero with local scratch/input/flag cleanup. A constructed blank-tape
input-loader/query/full-reader/postprocessor has a derived joint context/output/
oracle-memory law; no context is compiled into its continuation. Nonempty cover,
cancellation, unbounded correlated reports and exhausted-counter clients exercise
that same code. This is one native phase. Requests are raw framed runtime states,
not source-admitted concurrent batches; the planning opportunity count is not yet
an actual source used-set and allotments are not observed real elapsed time.
Reading the new guard, handing its payload to a source-valid next planner, clearing
the outer reply buffer/marker and constructing repeated feedback remain open.
The phase frontend always queries; initial/post-response guards are not part of it.
Its separate State ABI still needs conversion from the guarded Startup entry and
an invariant authenticating old stored history against actual oracle events.
It supplies neither native upper quantitative guarantees nor an optimum comparison.
An injective header format carries original encoded data, old raw histories,
private storage and budget/availability/stop/output fields. Those header fields
are transported, not semantically updated by the append transducer. The second
request depends on both original context and reply, checked on a fixed geometric
source with unbounded reply lengths and empty/zero-cost edges. This concrete raw
append scheduler is not a source concurrent-batch selector. The outer reply buffer
and marker remain retained, and full buffer reuse/repeated restart are unproved.
Native semantic context/private-state updates, dynamically generated next batches, buffer/workspace
cleanup and reuse, post-response stopping, and the repeated adaptive
query/stop/output loop still need concrete composition. The raw-program/native-local joint-law composition is not a theorem
that one native online machine implements that composition.
The strict oracle-PPT compiler's input-only clock and bounded-prefix query do not
supply that realization. This obstruction is now proved on one fixed actual
geometric-invoice source: for every instruction budget there is a positively
supported full report longer than that budget. No native competitor has the exact
joint query word/memory law as its ordinary output at that clock, and no
`ComputesTidily` full-query
specification exists at any finite clock. Thus the existing clocked tidy
composition/`iterateWhile` obligations cannot be discharged by the full reader;
assuming a common bound would strengthen the source model. This does not rule out
an unbounded native loop. It requires response-dependent stopped-law composition
with actual prepared-buffer, cursor, private-state and workspace invariants.
The arbitrary pointwise `Selector.Scheduler` function is also not itself a uniform
native scheduler code witness. Native productive continuation, quantitative upper bounds
and a successful output from that same compiled selector remain to be assembled.
Native optimum/envelope comparison through a uniformly
realized successful upper selector, source
subinstance/role/residual/external-machine encodings and exact source stopping
conventions remain open. In particular, the upper productivity contract excludes
premature silent divergence; it is not yet established for a uniform native selector.
The retained divergent-prefix ledger is not yet a cofinal infinite-instruction
path-cost or real-integrability theorem; general measurable/nonatomic laws and
compiled physical-clock semantics remain open. Unrestricted Theorems 5/6 and ALL-main
remain incomplete.
Theorem 4's native resource/asymptotic/hardness claims also remain open. Neither the
policy LP nor the binary-input two-batch savings FPTAS supplies those missing claims.

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897].

1. [Completeness of oblivious transfer](#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886])
3. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889])
4. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity)
5. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891])
6. [MIP = NEXP](#interactive-proofs) ([#892])
7. [Regev's worst-case to average-case reduction](#cryptographic-landmarks)

## Cryptography

### Cryptographic landmarks

- **Completeness of oblivious transfer.** In the ideal OT-hybrid model, every polynomial-time
  multiparty functionality admits a protocol secure against static malicious corruptions, with
  real/ideal simulation and abort, under the standard communication assumptions.
- **Regev's worst-case to average-case reduction.** For suitable `q` and Gaussian noise rate
  `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time
  algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`. The noise distribution, modulus
  restrictions and quantum reduction are part of the theorem.
- **Kilian's succinct arguments** ([#999]). If collision-resistant hash families exist, every
  language in NP has an interactive argument with polylogarithmic communication, by committing
  to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle
  versions.

### Modern fully homomorphic encryption

Gentry's bootstrapping is instantiated with GSW ([#486]; formal abstract `gsw-fhe`), including
uniform compactness for the leveled wrapper decryption circuits and level-indexed multi-hop
evaluation. Its remaining follow-up ([#1104]) is Gentry's exact concrete-security loss together
with the `poly(ℓ, d)` running-time clause of his Theorem 4. Then develop these in reviewable
milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions
where their hypotheses match. The [pre-rewrite FHE section][archive-fhe] maps the schemes to
current libraries and workloads.

1. **Ring arithmetic and RLWE.** Polynomial-ring operations over `(Z/qZ)[X]/(X^d + 1)`, RNS/CRT
   conversions, rounding and modulus-switching error bounds, and negacyclic NTTs implementing
   ring multiplication, with native certificates. Define the RLWE secret and error laws and
   experiment separately; an ordinary-LWE reduction does not give them.
2. **FHEW/TFHE programmable bootstrapping**
   ([Ducas–Micciancio](https://eprint.iacr.org/2014/816);
   [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870)). Ring-GSW external
   products, blind rotation, sample extraction and key switching; prove the bootstrap decrypts
   to `f(m)` with its noise, failure, width and runtime bounds, including negacyclic lookup
   restrictions and torus representations; floating-point FFT implementations need their own
   rounding-error proof. Then the [smaller-key methods of Lee et al.](https://eprint.iacr.org/2022/198)
   and batched variants, preserving their exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV** ([Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277);
   [Fan–Vercauteren](https://eprint.iacr.org/2012/144)). Slot encoding,
   multiplication, relinearization, rotations and level management, with leveled evaluation
   before a separately proved refresh. Equality modulo the plaintext modulus differs from
   ordinary integer equality, which needs a range bound.
4. **Approximate packed CKKS and its bootstrap**
   ([Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421)), with an explicit
   approximate-correctness interface and a norm bound on decoded error covering rescaling,
   rounding, key switching and rotations.
5. **Scheme switching and threshold variants**, with explicit range/precision contracts,
   evaluation-key assumptions, corruption thresholds, interaction, robustness and
   decryption-query access, distinguishing honest-but-curious from malicious security.

For each scheme, prove chosen-plaintext security for the actual algorithms and public evaluation
keys; keep LWE/RLWE, circular/KDM assumptions and attack-cost estimates distinct; introduce a
decryption-failure game when correctness is not perfect; and require nonvacuous parameter
families and full-input native runtime.

### Public-key, lattice and symmetric constructions ([#640])

- **Sigma protocols and Fiat–Shamir** ([#581]): computational Schnorr signatures under discrete
  log against strict PPT forgers; eavesdropping security in the strict-PPT model, with the
  statistical-distance term from sampling `ZMod q`.
- **Chosen-ciphertext security** ([#1885]): multi-challenge CCA from the single-challenge
  Cramer–Shoup theorem.
- **Lattices**: Fiat–Shamir with aborts and signatures from SIS (Lyubashevsky 2009,
  2012); strict-PPT samplers for integer boxes; identification security under SIS; efficiency
  certificates for the simulator and extractor; full interactive-view simulation; SIS for
  general moduli; module SIS and module LWE toward Dilithium-style schemes, as theory.
- **General:** reusable adaptive reductions, public-key encryption, universal-instance zero
  knowledge, hard-core predicates and hardness amplification, and connections to learning and
  average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643])

In order:
- the `PublicCoin → IP` bridge, with a uniform word verifier and adversarial decoding;
- parallel and AND/OR composition, and round-by-round knowledge soundness;
- oracle statements, so a later phase can query an earlier phase's oracle message (virtual
  output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds;
- efficiency-certified simulators and extractors, and auxiliary-input zero knowledge on the core;
- polynomial commitment and evaluation-query reductions, and the Ligero IOP;
- the BCS transform to non-interactive arguments in the random-oracle model;
- VOLE as an ideal functionality, and VOLE-in-the-head;
- libzk's compositional structure as a composition of these components, without ciphersuites.

### Concurrent and quantum security

- **Concurrent composition:** extend the protocol semantics with environments, scheduling,
  session identifiers and concurrent executions; prove a composition theorem with efficient
  simulators and explicit setup, corruption and communication assumptions. Then develop
  selected adaptive-corruption and non-malleability applications, alongside the static-malicious
  OT target.
- **Quantum-secure cryptography:** uniform quantum-efficient distinguishers, computational
  indistinguishability with quantum side information, and security reductions for concrete
  constructions. Connect the quantum-computation and lattice tracks through these adversary
  models; justify each reduction in that model. Later targets include quantum oracle access,
  the quantum random-oracle model, and extraction or rewinding under their precise hypotheses.

## Complexity classes and reductions

### Coverage catalogue

Build an auditable coverage index spanning the [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo)
and the canonical problems and theorems that ECCC papers need, verified against primary sources.
Each entry records its source and aliases, precise model and conventions, Lean declarations,
missing prerequisites and level (definition, partial development, verified theorem). Track
containments, separations, closure properties, complete problems and reductions separately, and
cover decision, function, search, counting, promise, distributional and parameterized problems,
with uniformity, advice, oracle access, error gaps, resources and reduction types explicit. The
index links to canonical definitions rather than keeping a second set.

### Structure, time and space

- Time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes;
  completeness, padding, self-reducibility, relativization and oracle separations, preserving
  each reduction's resource bound.
- **Time hierarchies** ([#1572]): native polynomial padding separates every pair of integer
  degrees `1 ≤ a < b`, in deterministic and in nondeterministic time, and the `O(t log t)`
  universal simulation ([#800]) gives `DTIME f ⊂ DTIME g` for time-constructible `f ≥ n` once
  `(f + 1) * polylog f ≤ g`, with an absolute exponent (`Hierarchy/TimePolylog`). Composing it
  with the word-RAM simulations gives `RAMTIME T ⊂ RAMTIME T⁵` over `Basis.additive` for
  polynomial `T` (`Hierarchy/WordRAM`). For nondeterministic time, padding amplifies the coarse
  lazy-diagonal hierarchy, which separates degree `d` from degree `6 * d + 14`; lazy
  diagonalization also separates `NTIME (2 ^ (k * n))` from `NTIME (2 ^ ((8 * k + 16) * n))`, so
  `NE ⊄ NTIME (2 ^ (k * n))`. Remaining targets
  include the textbook `f log f = o(g)` hierarchy, which needs the diagonal to clock the universal
  machine's own steps, noninteger polynomial degrees, a word-RAM hierarchy by direct
  diagonalization with a smaller gap, and sharp nondeterministic and alternating time
  hierarchies with certified simulators.
- **Probabilistic time hierarchies** ([#2084]): the hierarchy for promise problems
  (`PromiseBPTIME`), by delayed diagonalization following He (ECCC TR25-004), and the
  one-bit-advice hierarchy for languages of van Melkebeek and Pervyshev. `PromiseBPTIME` and its
  explicit-time sample-and-verify characterization are in place (`Classes/Promise/Time` and
  `Classes/Promise/Time/Verifier`). The advice-free hierarchy for `BPTIME` itself is open and is
  not a target.
- The space hierarchy for `log n ≤ g n`, which needs a universal simulation that does not hold
  its input.
- **Space:** Savitch bounds for general space-constructible functions.
- **Randomized logspace** ([#459], [#474]): RL and BPL, `USTCON ∈ RL`, Nisan's generator,
  `BPL ⊆ L²` and Saks–Zhou. The preprint route to native `RL = L` remains open in
  [#1444](https://github.com/cslib-community/complexitylib/issues/1444). Its estimator work in
  [#1721](https://github.com/cslib-community/complexitylib/issues/1721) has an integer-grid slack
  schedule with endpointwise telescoping and summable available-scale precision payments.
  Actual correction iterates now supply product entry/row-mass bounds and their scheduled
  omitted-product norm sum. Product-seed correction/reward samples have proved true means,
  reaching the next actual hierarchy reward. The local pilot and actual-correction
  preparation/normalization families now share an expanded dependency order, including
  normalized children and an actual copy/reward projection client. Ranks are computed from
  finite iteration bounds; role/rate/suffix requests preserve the inherited source or reset it
  to the midpoint. Pilot steps use the current maximum; actual corrections and copy weights
  use the final pilot maximum. A bounded cross-stage hierarchy/reward client now connects
  the previous-reward and base-matrix leaves to actual earlier-stage constructors, with a
  computed decreasing global rank and nonconstant two-stage regression. Routed direct/residual
  bins now have a finite partition/true-mean client into the actual next matrix, primitive
  affine sampling instances, native copy-symbol suffix laws and whole-function role/rate/usage
  requests with computed rank payments. Signed residual evaluation now separates the negative
  endpoint correction from the midpoint product correction, with actual tuple-dependent sample
  means. Bounded top-bin routing and dense preparation/normalization accept arbitrary child
  functions, retain raw ranks, and agree with actual hierarchy bounds in a two-stage client.
  The residual-bin phase order is local; full global stochastic preparation/access enumeration,
  finite-accuracy ports, estimated copy/routing-fraction comparisons, and the complete scheduled
  mean-prefix bound remain open; range/true means do not establish root
  regularity or the error recurrence. Paired raw differences, full-coordinate conditional walks, summed noise, compression, strong recursive
  induction and native logarithmic workspace/class equality remain required.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a
  logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888]): implicit Tree Evaluation with the
  fan-in-`d` space bound and the native block-tree evaluator are developed in the stacked
  work tracked by the issue. The full `DTIME_subset_DSPACE_sqrt` inclusion is proved in
  `Complexity/Computability/Complexity/Classes/TimeSpace/Williams.lean` for arbitrary
  injective input encodings and every `t(n) ≥ n`, without time constructibility. Its fixed
  driver scans the original input, searches schedules and increases balanced time guesses.
  The stacked development still needs final CI and integration; the broad issue remains
  open until it lands. For Cook–Mertz itself: malformed-input handling
  and the refined `O(ℓ + H log(ℓ + 2))` parameter bound.
- Alternating time and space classes and bounded-alternation characterizations of PH; sharp
  bounds for sublinear space, distinct from polynomial-space simulation.
- **Deeper consequences of a Boolean-hierarchy collapse:** Kadin's sparse `S` with
  `coNP ⊆ NP^S`, and the collapse of `PH` into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, which follows from
  results of Wagner and of Chang and Kadin, not from Kadin's 1988 argument (see his erratum).
  `BooleanHierarchy/Kadin.lean` proves only `PH = Σ₃ᴾ ∩ Π₃ᴾ`.

- **Explicit universal SAT solver:** construct one fixed native algorithm, independent of an
  assumed fast SAT algorithm, and prove its worst-case running time is polynomial if and only if
  `P = NP`. Specify a total SAT decision procedure, including unsatisfiable inputs, separately
  from verified witness search; account for dovetailing, certificate checking and universal
  simulation overhead rather than relying only on the existing `SAT ∈ P ↔ P = NP` equivalence.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351]): logspace Turing reductions, in an oracle model whose query tape is
  not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of
  Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets:** `P/poly ⊆ P^SPARSE` (Meyer), the converse of
  `PWithOracle_subset_PPolyOn` in `Classes/Sparse/Turing.lean`. After Kadin's
  `PH ⊆ P^{NP[O(log n)]}` (`Classes/Sparse/Kadin.lean`, [#2062]): `P^{NP[O(log n)]} ⊆ Σ₂ᴾ ∩ Π₂ᴾ`,
  hence `PH = Θ₂ᴾ` under his hypothesis; his stronger form with a sparse `S ∈ NP` and
  `coNP ⊆ NP^S`; and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** p-isomorphism and paddability; paddable NP-complete sets are p-isomorphic,
  so the standard NP-complete problems are all p-isomorphic to SAT; the isomorphism conjecture as a
  hypothesis; every many-one complete set for EXP is complete under one-one, length-increasing
  reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal,
  Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so
  every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang);
  separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and
  Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468]): the full expanded 2013 paper of
  Glaßer, Nguyen, Reitwießner, Selman and Witek: native transfer from local self-reducibility
  (Lemma 3.3), including virtual-input/answer regeneration and adaptive-to-tt conversion.
  Uniform runtime initialization, virtual-word reads and a two-pass Boolean-state native
  evaluator are certified; arbitrary logspace query-generator/evaluator consumption, supplied
  header preparation, answer regeneration and the resource-certified suffix loop remain open;
  bounded and many-one self-reducibility specializations; concrete complete self-reducible
  problems (Theorem 3.5); Section 4
  bounded/logarithmic-query results and
  separations, and Section 5 mitoticity/diagonalization. The additional parity-logspace
  application needs a native path-counting class and complement closure.
- **Uniform diagonalization** (Schöning), which generalizes Ladner's theorem.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE.
  P-selective sets (Selman): a P-selective NP-complete set gives `P = NP`, P-selective sets lie in
  `P/poly` (Ko), and self-reducible P-selective sets lie in P.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and
  so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity:** immune and bi-immune sets, P-bi-immune sets in EXP (Balcázar and Schöning), and
  almost-everywhere hardness.

### Average-case complexity

- Distribution ensembles with computability and samplability certificates; distributional
  reductions with explicit domination and resource bounds; DistNP, errorless average-case
  classes and heuristic classes, keeping runtime tails and permitted error distinct. Reuse the
  specialized Liu–Pass hardness notions through proved bridges.
- **Levin completeness:** a distributional bounded-halting problem complete for the chosen
  polynomial-time computable-distribution class, followed by a separately scoped extension to
  samplable distributions. Connect the framework to one-way functions, learning and the
  metacomplexity track ([#798]), preserving the distribution and reduction conventions.

### Counting and modular classes

- The Another Solution Problem (ASP) framework: certify polynomial-time forward and inverse
  witness maps. The parsimonious reductions to positive exact-one SAT and its planar
  three-occurrence variants already preserve counts over occurring variables; the new local
  replacements have constant-factor growth and preserve the earlier linear grid sides and
  quadratic planar costs. See the [reduction catalogue](guide/ComplexityGuide/NPCompleteness.lean)
  for the completed NP-completeness and NP-hardness endpoints. Exact count preservation alone
  does not supply the ASP runtime certificates.
- Counting reductions and further oracle results preserving exact multiplicities; permanent
  #P-completeness; modular and counting hierarchies; the oracle-algorithm form of Stockmeyer's
  approximate counting.
- For composite moduli: the prime-power collapse `Mod_{p^e}P = Mod_pP` and union closure.
  Complement closure for moduli that are not prime powers is open, and relativizing proofs
  cannot give it (Barrington–Beigel–Rudich), so it is not a library direction.
- Target-relativized `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and
  UP-oracle containment.
- Native oracle counting machines: efficient encoded oracle checking, response-access costs and
  oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **MIP = NEXP** ([#892]): `NEXP ⊆ MIP₂` through the BFL multilinearity test and arithmetization
  of exponential-time tableaux; an efficient GKR verifier under log-space uniformity.
- Private-to-public-coin transformations, `AM[k] = AM`, interactive-machine characterizations
  of Arthur–Merlin classes, and statistical and perfect zero knowledge.

### Descriptive complexity and first-order reductions

Ordered first-order complexity follows Immerman: structures on `{0, …, n-1}` with `n ≥ 2`, FO
means FO(≤, BIT), and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings; the order-free
`FO.Reduces` and `FO.QFReduces` stay as a general layer. Numeric predicates are computed from the
universe size, not supplied as unverified input tables. In dependency order:

- **Ordered completeness.** SAT, 3SAT, 3COL, independent set, clique and vertex cover
  NP-complete under first-order or quantifier-free projections; REACH NL-complete under
  first-order reductions.
- **Projections:** projection reducibility on finite structure classes and the standard ordered
  machine-encoding bridge. The classical qfp convention excludes BIT (Immerman–Landau,
  Definition 3.6), and arbitrary quantifier-free combinations of input relations are not
  projections.
- **Circuit Value P-complete under first-order reductions**, via `REACHa → MCVP → CVP` (Immerman,
  Theorem 3.26 and Exercise 3.28), with the alternating-logspace simulation of polynomial-time
  machines and the translation to `encCircuitValue`.
- Numeric certificates for further restricted-domain families; canonical BIT on a restricted
  domain need not be first-order definable.
- Order-free: SAT-to-3SAT, graph-property hardness, and bridges to the separately encoded
  problems.
- Extend the synthesis rules to nested operator bodies and give regular-language quantifiers
  their ordered characteristic-word semantics.
- Further logical characterizations on ordered structures: FO(TC) = NL and FO(DTC) = L,
  SO-Horn = P (Grädel), and DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing);
  then order-invariant and fixed-point queries and uniform translations between syntax,
  structures and algorithms.
- A witness-carrying reduction structure once a client needs one, for example size bounds for
  Cook–Levin.
- **Logical lower-bound methods:** Ehrenfeucht–Fraïssé and pebble games with their logical
  equivalence theorems, locality and concrete nondefinability results; then counting and
  fixed-point expressiveness, including Cai–Fürer–Immerman-style separations. Reuse upstream
  model-theoretic foundations and connect the methods to the ordered capture theorems.
- **Dynamic descriptive complexity:** dynamic programs and update semantics with explicit
  initialization, auxiliary relations and domain conventions; invariant-preservation rules and
  reachability in DynFO as a target. Relate logical update restrictions to the stateful-algorithm
  interfaces through explicit translations.

### Uniform circuit families

Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and input
encodings; certify circuit generation, evaluation and the machine-to-circuit simulations,
preserving size, depth and construction resources; and prove FO with order and BIT equals
DLOGTIME-uniform AC⁰ under explicit conventions.

### Search, parameterized and fine-grained complexity

- **TFNP:** CLS, further local search, fixed-point and equilibrium problems.
- **Parameterized:** strongly uniform variants (computable `f`), further explicit polynomial
  kernels, the W and A hierarchies, and parameterized lower bounds; connect these to
  [structural graph algorithms](#structural-graph-algorithms) and their decomposition costs.
- **Exponential-time SAT** ([#894]): Schöning, PPZ and PPSZ run on the randomized word RAM with
  exact laws, amplification and time bounds (PPSZ's round count takes an input bound
  `a / b ≥ 1 - qbar k h`). Remaining: curated abstracts, and the uniform `o(n)` forms of the PPSZ
  bounds with `w` growing in `n`.
  Further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886]): for `0 < ε < 1/8`, NP-hardness of
  distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most
  `7/8 + ε` of the clauses. This needs Raz–Holenstein parallel repetition for small-soundness
  Label Cover and Håstad's separate perfect-completeness construction for MAX-E3SAT.
- The FGLSS clique-hardness reduction and its amplification, retaining the exact gap and
  reduction runtime.
- Gap and approximation-preserving reductions, APX/PTAS/FPTAS, inapproximability consequences of
  PCP, CSP classifications and relaxation gaps, with assumptions such as the Unique Games
  Conjecture stated explicitly. The 2-to-2 games theorem waits for [#886].
- **A practical PCP construction:** a reasonably runnable construction and its cost on complete
  reductions; rotation certificates polynomial in the bit length of a vertex name; machine-level
  error reduction and extractors from expander walks, with certified seed and evaluation costs.

### Proof complexity

- Proof-space lower bounds, Frege, cutting planes, polynomial calculus and sum-of-squares, and
  certified DPLL solver runtimes.
- **Feasible interpolation** ([#1817]): the transfer of communication lower bounds to proof-size
  lower bounds ([#2019]).
- **Proof search:** automatizability and weak automatizability with explicit encodings and
  runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow
  and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.

## Circuits and algebraic complexity

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889]): no polynomial-size,
  constant-depth circuits over AND, OR, NOT and fixed-modulus counting gates for some language in
  NEXP.
- **Circuit lower bounds from refuting ETH** ([#1539]): `E^NP ⊄ SIZE(O(n))`, and a language in
  `E^NP` whose fan-in-two circuits need more than `c n √log n` gates infinitely often, by
  Williams's witness-circuit argument with the library's #CircuitSAT counters. `E^NP` is defined,
  and the witness bits of formulas prepared in time `2^O(n)` are in `E^NP`.
  `FineGrained.CircuitLowerBoundBudget` proves the counter's quantitative budget for three
  circuits of size `n √⌊log₂(n+2)⌋ / (12(A+1))` plus linear overhead; the integer arithmetic,
  polynomial-time computation of this size cap, and rescaling to coefficient
  `1 / (24(A+1)d)` at framed lengths `d n` are checked. The exponential nondeterministic time
  hierarchy has landed. Still open are connecting its separating language to the framed witness
  preparation, uniformly constructing the linear-size decoder and checker, and completing the
  nondeterministic simulation for the full separation theorem.
- Uniform and nonuniform NC, AC and TC, circuit-to-machine bridges, algorithm-to-lower-bound
  arguments, and barriers such as natural proofs and algebrization. NC simulation of unrestricted
  `TCⁱ` needs Muroga's threshold weight-bounding theorem.
- Formula lower bounds beyond Andreev's, following Jukna; Raz–Wigderson's monotone depth bound for
  matching on general graphs.
- **Monotone circuits versus P:** Razborov's `n ^ Ω(log n)` monotone bound for bipartite perfect
  matching is proved ([#2063]); the separation also needs bipartite perfect matching in
  `Complexity.P`.
- **An explicit frontier extractor:** port v1's sumset-extractor construction with an explicit
  family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses. It would
  exceed the library's unconditional `3.5 N - o(N)` bound in P, so it needs an independent
  correctness review of the frontier core.
- **Weighted threshold representations:** v1's explicit source-reduction family, universal scalar
  circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting.
- **Depth-two threshold circuits for Andreev's function** ([#2347]): the exact quadratic
  `4 * 4 ^ b + b * m * 2 ^ b + 1` depth-two weighted threshold upper bound
  (`WeightedThreshold/Andreev.lean`), the windowed average-case `(1 - δ)`-agreement and
  `(1 / 2 + ε)`-correlation depth-two upper bounds (`WeightedThreshold/AndreevWindowed.lean` and
  `WeightedThreshold/AndreevAverage.lean`), Erdős–Littlewood–Offord anti-concentration
  (`Combinatorics/LittlewoodOfford.lean`) together with the repaired Kane–Williams gate and wire
  random restriction lemmas (`WeightedThreshold/RandomRestriction.lean`, Lemma 1.1 and Lemma 3.1 of
  arXiv:1511.07860v1), the `b`-variable LTF and depth-two threshold function counting bounds
  (`WeightedThreshold/ThresholdCounting.lean`, Theorem 2.3 and Section 4 of arXiv:1511.07860v1), and
  the fixed-weight quadratic-in-`ε` average-case `Ω(ε² n ^ (3 / 2) / log² n)` gate and
  `Ω(ε² n ^ (5 / 2) / log ^ (5 / 2) n)` active-wire lower bounds for
  `3 * (b + 2) / √(2 ^ b) ≤ ε ≤ 1 / 2` in the balanced regime
  (`WeightedThreshold/AndreevLowerBound.lean`, improving the
  `ε³` dependence in Theorem 1.1 and Section 5 of arXiv:1511.07860v1) are proved; closing the
  worst-case depth-two threshold gate gap between `Ω̃(n ^ (3 / 2))` and `O(n ^ 2)` remains open.
- **Construction runtimes**, certified separately from gate counts: the mass-production
  constructors, with constructive choices of information sets and line menus; the
  iterated-function preprocessing; and the bit complexity of formula evaluation on the rational
  hitting-list matrices.
- **Algebraic complexity** ([#891]): the rest of Limaye–Srinivasan–Tavenas. Proved: simple
  circuits (product gates reading distinct wires) of constant product-depth computing iterated
  matrix multiplication need superpolynomial size over any field, at `d = ⌊log₂ ⌊log₂ n⌋⌋`, from an
  explicit bound with exponent `d ^ (1 / (4 ^ Δ - 1))`. Remaining: their semantic set-multilinear
  model; growing `Δ` with exponent `d ^ exp(-O(Δ))`; the `√d` bound at `Δ = 1` (LST Lemma 13 and
  Corollary 4); the full range of `d`; and the `0/1`-substitution remark. Also the
  Kabanets–Impagliazzo theorem (a deterministic PIT algorithm implies NEXP ⊄ P/poly or the permanent
  has no polynomial-size arithmetic circuits); Valiant's VNP-completeness of the permanent over
  fields of characteristic other than two (membership now has an explicit Ryser witness over
  every commutative ring; VNP-hardness remains open); formula and branching-program models,
  identity testing, hitting sets, and tensor and rank methods, including partial-derivative
  measures (Nisan–Wigderson depth-3 bounds and shifted partials) and the depth-reduction chasms at
  depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform
  construction costs certified
  separately from gate counts.
- **Real-algebraic decision procedures:** port the Sturm–Tarski query evaluator, recursive
  evaluator, implicit arithmetic, native space certificates and the ETR upper bound from
  [lean-canny](https://github.com/SamuelSchlesinger/lean-canny).

### Jukna coverage

Formalize the established results, constructions and worthwhile exercises of
[Jukna's *Boolean Function Complexity* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html),
with the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html), auditing
each statement against the numbered result. Organize modules by subject, not chapter.

| Chapters | Next coverage work |
| --- | --- |
| 1–2: foundations and Boolean analysis | Counting, graph complexity, degree and approximation results; the partial-function circuit upper bounds that use Lemma 1.17. |
| 3–5: communication | Matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | Remaining formula and monotone bounds; span programs and negation complexity. |
| 11–13: depth restrictions and general gates | Depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | Bounded-read and bounded-time lower bounds and the remaining tree results. |
| 18–19: proof complexity | Proof-space and cutting-plane lower bounds. |
| 20: barriers and further methods | The book's generator, natural-proof, fusion and indirect lower-bound results. |

## Pseudorandomness, coding and Boolean analysis

- **Derandomization from hardness:** the infinitely-often variant, and the EXP ⊄ P/poly endpoint
  of Babai, Fortnow, Nisan and Wigderson.
- **Extractors** ([#895]) beyond Chor–Goldreich: two-source extractors for lower min-entropy,
  where the `t`-wise independent parts of Chattopadhyay–Zuckerman's Theorem 4.1 are formalized with
  exponent `O(d²)` in place of their `3 d + 6` (the almost `t`-wise independent parts are not), with
  Tribes as a small instance (coalitions of fewer than `w` bits only), and their resilient functions
  (Theorems 3 and 4) and extractor (Theorem 1) are not yet formalized;
  condensers, limited independence, explicit expanders and space-bounded generators, with finite
  guarantees separate from uniform construction and decoding costs.
- **Codes:** Guruswami–Sudan list decoding and local decoding, keeping interpolation,
  list-size/agreement guarantees and decoding runtime as separate obligations; concrete
  list-decodable codes for Nisan–Wigderson.
- **Boolean analysis:** hypercontractivity beyond `p ≤ 2 ≤ q` and its applications.
- **Resource-bounded measure and dimension:** martingales and gales with explicit computation
  budgets, their success sets, and measure and dimension within complexity classes; connect
  quantitative randomness to the Kolmogorov-complexity development. State the resource bounds
  and uniformity of the betting strategies separately from ordinary measure-theoretic facts.

## Communication, queries, learning and other models

- **Lifting** ([#890]): applications of deterministic lifting, such as partition-number
  separations, and randomized lifting.
- Multiparty protocols, discrepancy and information complexity, direct-sum and direct-product
  results, and reductions to streaming, sketching and cell-probe lower bounds.
- **Streaming and sketching:** native time and space bounds for Count-Min, including hash-seed
  storage and evaluation; AMS frequency moments, CountSketch, turnstile updates, and heavy-hitter
  recovery; communication-to-streaming transfers with explicit state encodings and pass counts.
- **Learning:** machine-certified running times for the LMN and Kushilevitz–Mansour learners;
  distributional problems and reductions, samplability, average-to-worst-case connections,
  PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Give the
  computational–statistical gap program concrete clients: an SQ oracle with tolerance and query
  costs, statistical-dimension lower bounds for a specified planted problem, and corresponding
  sample and runtime upper bounds. Develop low-degree likelihood-ratio and sum-of-squares
  comparisons where justified, distinguishing restricted-model bounds from unrestricted
  computational hardness. Use the [distributional framework](#average-case-complexity).
- **Property and distribution testing:** independent repetition of Boolean local tests and BLR
  linearity testing have explicit decision-tree query bounds. Remaining: further access models,
  tolerant and distribution testing, query and sample bounds, canonical testers and lower bounds.
- **Kolmogorov complexity and metacomplexity** ([#798], [#884]): the near-linear threshold regime
  of Liu–Pass Theorem 3.1 (c), hardness for every polynomial `t(n) ≥ (1 + ε)n` rather than above a
  polynomial threshold, which needs a rate-1 efficient conditional EP-PRG running in `n + O(n^c)`
  multi-tape steps for a constant `c < 1`; prefix-free complexity,
  resource-bounded MCSP variants and connections to learning, cryptography and lower bounds; the
  circuitized anti-checker with an efficient generator; the asymptotic parameter instantiation of
  Theorem 5 as a concrete rounded-threshold, ternary-device statement; and hardness results for
  `MINKT` and `MINcKT` (whose
  definitions, conditional `K^t` measure, and `NP` memberships are in `Kolmogorov/MINKT.lean`,
  `Kolmogorov/Conditional.lean`, and `Kolmogorov/MINcKT.lean`), as independently scoped
  developments; the reverse
  multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding.
- **Quantum computation** ([#896]): channel semantics and approximation costs alongside the
  circuit and measurement semantics, reusing suitable quantum foundations rather than
  incompatible models, and a bridge between the query and circuit models; complete problems for
  BQP; QMA and related query, communication and interactive classes, with amplification,
  containments and complete problems. Supply the
  [quantum adversary models](#concurrent-and-quantum-security) needed by cryptographic
  reductions.

- **Shor's algorithm:** bounded-error polynomial-time integer factoring and discrete logarithms
  in the native uniform quantum-circuit model, with explicit input/output encodings, success
  probabilities and gate-approximation costs. Develop quantum period/order finding and phase
  estimation, the quantum Fourier transform, reversible modular exponentiation, continued-fraction
  recovery and the classical reductions; certify uniform circuit generation and polynomial gate
  bounds alongside correctness.

### Differential privacy and adaptive data analysis

- Dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with
  postprocessing and adaptive composition. Start with a finite or discrete mechanism proving
  both privacy and utility, including sampling cost and finite-precision error.
- The exponential mechanism, private query answering and private learning; privacy–accuracy
  and sample-complexity lower bounds; then adaptive data-analysis and generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources
  explicit, reusing the probability, oracle-computation and learning APIs.

## Algorithms and optimization

### Optimization and duality

- **Linear programming:** rational input and output encodings, primal and dual certificates,
  weak and strong duality, and infeasible or unbounded outcomes. Reuse Mathlib's convexity and
  linear-algebra foundations; certify certificate checking and a polynomial-time LP algorithm
  with bit complexity and intermediate precision accounted for.
- **Separation and optimization:** a precise oracle interface and a separation–optimization
  equivalence with its representation, accuracy and well-boundedness hypotheses. Extend to
  convex optimization through explicit oracle and numerical-error contracts.
- **Primal–dual approximation and multiplicative weights:** reusable analyses with vertex cover
  and set cover as first primal–dual clients; multiplicative-weights regret and approximation
  bounds with finite-precision implementations, then applications to games, learning and
  optimization.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations),
reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** integral max-flow/min-cut and a native augmenting-path algorithm with
  charged runtime; then minimum-cost flow and weighted bipartite matching through common
  residual-network and duality machinery.
- **Matroids:** matroid intersection with explicit oracle and implementation costs, beyond the
  weighted greedy algorithm and its independence-oracle interface.
- **Submodular optimization:** further constraints and approximation bounds beyond the
  cardinality-constrained `1 - 1/e` greedy, charging value-oracle calls separately from their
  concrete realizations.

### Online algorithms and competitive analysis

- Request sequences, online strategies, offline optima and competitive ratios with additive
  constants; distinguish deterministic and randomized strategies and oblivious and adaptive
  adversaries. Compare algorithms in the same action and cost model, including initialization.
- **Adaptive search trees:** working-set and dynamic-finger bounds for splay trees, and a BST
  access-and-rotation model with Wilber-style lower bounds. State dynamic optimality as a
  conjectural research target with explicit strategy and sequence quantifiers.

### Structural graph algorithms

- Tree decompositions, width and normalization into a suitable decomposition form; a reusable
  dynamic-programming evaluator over a supplied decomposition, with state-space, transition,
  join and runtime bounds. Start with native independent-set, coloring and SAT/CSP decision and
  counting clients, specifying the graph whose width is measured.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style
  theorem with computable parameter dependence on width and formula size. Keep the supplied
  decomposition and its encoding explicit; certify decomposition finding separately. Connect
  the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Markov-chain sampling:** finite kernels, stationarity, reversibility and total-variation
  mixing; coupling, path coupling, conductance and canonical-path arguments. Implement
  Metropolis sampling for encoded rational target weights, charging initialization, arithmetic
  and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling:** interfaces separating relative error, failure
  probability, output-distribution error and runtime, including zero-count instances. Start
  with a complete DNF-counting FPRAS; prove sampling/counting reductions for suitably
  self-reducible relations, with the sampling and counting oracle costs included.
- Extend to randomized approximate counting for matchings and permanents of nonnegative
  rational matrices through explicit mixing and reduction theorems. Reuse the coupling and
  expander APIs and connect to the separate Stockmeyer oracle-counting track where their
  hypotheses agree.

### Constructive probabilistic methods

- **Moser–Tardos resampling:** an actual resampling program, its correctness and expected
  resampling bound, and native sampling and event-detection costs, building on the variable
  form of the Local Lemma.
- **Conditional expectations and pessimistic estimators:** certified choice and update rules,
  algorithmic alteration, and concrete coloring, satisfiability or combinatorial-construction
  clients. Preserve the quantitative guarantee when converting an existence argument into a
  deterministic or randomized algorithm.

## Machines, RAM and data structures

- **Efficient universal simulation** ([#800]): the clocked universal function runs in time
  `O(N + poly(D, M) · (t + 1) log(t + 2))`, for encoded input length `N`, description length `D`
  and largest input symbol `M`, by a divide-and-conquer windowed simulation
  (`computableInO_universal_nlogn`). Remaining: a source-space-sensitive storage bound (the
  space is currently bounded only by the time), and an unclocked form that runs until the
  simulated machine halts.
- **Plain computability** ([#862]): complete the plain calculus ([#608]), delete the tidy
  calculus, keeping only a machine-level kernel inside the Machines layer, and switch the
  abstract bridges to the shared predicate.
- **Certificate APIs and automation** ([#1155]): predictable search, with fixed heartbeat budgets
  on regression goals, failures that name the subterm lacking a certificate, and cheap
  syntax-directed composition for glue code. Infer encodings for ordinary functional expressions
  through constructor, projection, lookup and composition rules; generalize list, bounded-table,
  cache and nested-loop invariants where clients need them; keep separate time, workspace and
  output-size bounds through composition; apply cumulative streaming contracts to captured
  iteration and nested loops; certify PRG stretching with seed length, rounds and generator cost
  kept separate; and develop general open-program composition. Use Cook–Levin and GGM as
  regression clients. Improve configuration views, tape partitions and handoff identities only
  where several clients benefit, keeping machine transitions out of global simp.
- **Mathlib TM2:** sublinear work-space comparisons and a linear-space forward simulation.
- **Generic RAM:** uniform arbitrary-program dispatch and general width-selection and input-fit
  theorems; simulating operations by programs over smaller bases; structured programs and time
  classes over arbitrary value domains with weighted or bit costs; simulations between instances;
  the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Word RAM:** an AC⁰ basis; wider-fragment and Turing-machine simulations;
  transfer of Anthropic's modular machine and 3SUM/APSP algorithms; size-based width selection
  with an input-fit guarantee and explicit overhead;
  expected-time rules for unbounded almost-surely terminating structured loops; random-tape
  equivalence and BPP/RP/ZPP simulation bridges for the randomized word RAM ([#1124]); transfer
  of cell-probe lower bounds; and the Horn-SAT, 2SAT, matching and domino-tiling clients.
- **Sharper native Exact Triangle exponent** ([#2423]): the automatic box-backed Exact Triangle
  host runs in `Oκ(n^(3−33/20000))` (exponent 2.99835) after integer retuning; reaching the
  source's stated 2.9983 under the same native conventions remains open.
- **Memory-oracle realization** ([#2205], [#2213]): the foundational graded kernel certifies
  all four memory queries, register-word glue, native branches and binds with one fixed
  continuation emitter for all runtime replies. Its functional representation retains the
  complete memory and frontier, and its instruction currency adds local work to memory charges.
  Bounded runtime loops also charge local computation and every iteration, including query-free
  iterations. Fixed flat programs include the actual input-installation prefix and final halt,
  with explicit input layout, fits and safe-domain hypotheses. A separate operation-level
  memory implementation exposes body-only costs under delivered arguments. Existing framed
  Word-RAM certificates can be derived from semantic modules after discharging their local
  initialization, footprint and ABI conditions; a one-cell ADT checks that boundary. Multiword
  glue preserves full-word Option payloads, and the actual memory-stack size/push/pop methods
  have uniform native certificates over runtime layouts, with local work 0/10/19. The stack is
  migrated: `Stack.Native` and `Stack.Controller` replace its hand-stepped dispatcher, which
  remains only as the stepped component of Chan–He traversal (`Traversal.WordStack`). Backends of
  framed refinements export their frame (`modifies`, `frame`), run products over one memory,
  and allocate from arbitrary memory through `Memory.Allocator` (`Backend.Allocation`); the stack
  and a pair of stacks check all three. Queue operation calls now use one fixed native
  dispatcher over physical-array memory programs, with resident count words and paid commits.
  Its dynamic certificate preserves the original two-array space, dirty six-instruction
  initialization and adaptive-call bounds. The binary heap now realizes its original memory methods
  and allocator, retains compact local-zero initialization and a genuine linear dirty clear, and
  supplies the original log-linear Dijkstra endpoint through an actual initialized native program.
  The graph encoding and word envelope stay unchanged; one factor precedes all graphs and widths,
  and the clock includes the prefix, control and halt. The old hand-stepped binary execution is
  retired, while its pure model/order lemmas and source credit remain. Remaining are the full
  framed queue/faithful-allocation client, generic stateful and whole-client composition, Fibonacci
  execution migration and the full C2/M1b objective; arbitrary host continuations do not acquire
  runtime bounds.
  The Fibonacci method family ([#2290]) realizes all five original memory methods with one fixed
  native factor, exact typed-source/history transport and the existing nonzero amortized
  potential. The Fibonacci Dijkstra consumer now reserves the original zero tail without clearing,
  derives its reached callee domains from the shared framed history, and pays the nonzero heap
  potential through the existing amortized telescope. One actual initialized native program
  retains the original word envelope and sharper reachable-vertex bound, including its prefix,
  control and halt and the entire final memory/frontier. The old Dijkstra executor and its
  implementation-specific coefficient 640 are superseded; the original existential endpoints
  are unchanged. MinPQ migration and the execution core it still uses remain open, as do generic
  whole-client transfer and the abstract-space decision.
  The Karger–Stein specification bridge ([#2289]) gives the existing recursive native code the
  exact answer law of its contraction-oracle client, preserving pathwise instruction/random-call
  bounds, word fits and memory frames. Probability and amplification are proved at the
  specification layer. This does not complete its memory-oracle native realization: the
  randomized realization adapters, contraction implementation and recursive frame-stack
  migration remain part of [#2205].
- **Stateful algorithms and data structures:** Word-RAM controllers for larger adaptive and
  iterative clients, including the two-stack queue and timeline-editing controllers; reusable
  allocation and deallocation, shrinking, and live and peak space accounting; ownership and
  recursive procedures; model realizations for cell probes, caches and randomness; present and
  historical queries for the retroactive interface; balancing and heap or RAM representations of
  search trees; uniform preprocessing and dynamic updates for fusion trees; deletion and
  predecessor for van Emde Boas sets; and deallocation,
  shrinking and compiled client controllers for the doubling array.
- **A typed-call evaluator** for fixed-program Word-RAM clients, returning the typed observation,
  final state and halt-inclusive instruction cost, so the prefix-sum clients no longer
  assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#949]): lift operation-count helpers
  (`numQueries`, `numInserts`, `numDecreaseKeys`, `numExtractMins`) to `IndexedMinPQ`, parameterize
  flat-program operation-sequence execution (`RunsOps`) over `PQCode` in
  `DataStructure/PriorityQueue/WordRAM/Basic.lean`
  so `BinaryHeap` and `FibonacciHeap` share a generic `run_ops_exact` theorem, and factor a common
  `ShortestPathSpec p bound` predicate in `Dijkstra/HeapStatement.lean` across `LogLinearSpec`,
  `FibonacciSpec`, and `FibonacciLinearSpec`.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** work–span semantics and a processor-scheduling or simulation theorem,
  followed by prefix scan, sorting and graph primitives with both work and span bounds. State
  processor access, synchronization and scheduling overhead explicitly.
- **Memory hierarchies:** external-memory and ideal-cache models with explicit capacity and
  block-size parameters; scanning, B-tree operations, blocked matrix multiplication and
  cache-oblivious sorting as clients. Connect arithmetic-step, memory-access and cache-miss
  bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity:** LOCAL and CONGEST models with explicit identifiers, round,
  message-size and randomness conventions; locality lower bounds and communication-to-round
  reductions with corresponding algorithmic examples.

## Coverage and reuse

The long-term bar is to support formalizing every paper in the
[Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/),
with the additional work per paper increasingly its new mathematics: standard models,
representation changes, reductions, resource certificates and proof techniques come from the
library. Use a growing, source-pinned sample of papers, including some chosen after an API was
designed, as demanding clients, and promote recurring obligations into shared APIs only after
reuse is demonstrated.

- **One sensitivity API.** Define the sensitivity measures over any `Fintype` in CSLib and drop
  the separate measures of the sensitivity-separation development.
- **CNF evaluation certificates:** `fun_prop` certificates for evaluating literals, clauses and
  formulas under a polynomial-time assignment, so clients stop passing `CNF.eval`,
  `Clause.eval` and `Literal.eval` to `fun_prop` as unfolding hints.
- Factor indicator-expectation identities from PCP's second-moment calculation, and recurring
  cardinality and logarithm conversions, once a second client benefits.

### OpenAI math results ([#1002])

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI
math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the
openai/math release, and extract the results in scope: the headline theorems and also the minor
lemmas useful in their own right. Prove each against Complexitylib's own definitions, from the
cited manuscript's exact statement with its version pinned; a source formalization is a
reference, not evidence. Label unrefereed results as such. The openai/math formalizations are
Apache 2.0, as is Complexitylib, so adaptation with attribution is permitted. The practice is
still to read them for the mathematics and write proofs against Complexitylib's definitions; any
adapted code keeps its Apache 2.0 attribution. The rewrites state no license and are only read
and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/complexitylib/issues/1538)):
  `ContractionCounting.exists_modelCounter_fixedDensity` proves the fixed-density bound
  `2^{O_{k,D}(n / √log n)}` by tensor contraction (Theorem D.1 with `ℓ = 1`), and
  `DensityBranchCounting.exists_modelCounter` combines it with the interpolation-scale counter in
  one machine. `CountingSimulation.truncEntryContractionAlgorithm` now supplies polynomial
  truncation order and precision `O(s log s)`, with a linear vertex bound. The arbitrary-density
  bound `2^{O_k(n log log n / √log n)}` still needs the Lemma D.2 construction and its native
  application to this interface; #1538 remains open.
- **Exact optimization and large weights:** `MaxSAT.exists_histogram_algorithm` and
  `MaxSAT.exists_optimum_algorithm` compute the complete score distribution and optimum value in
  contraction time measured by literal occurrences plus clauses. Their sparse fixed-width
  specializations give `2^{O_{k,c}(n / √log n)}` time and polynomial space.
  `BinaryWeights.certificate` contracts natural tensor tables exactly when their bit lengths are
  polynomial in the structural size; `BinaryWeightedCounting.exists_partitionFunctionCounter`
  supplies the native weighted-CSP application. Remaining extensions are native optimizing
  assignment extraction and signed or rational weight interfaces. A variable-count rate for
  dense exact MAX-SAT is not established by these results or by ordinary SAT sparsification.

## Documentation and repository

- **The guide** ([#585]): a chapter per area, including Foundations (bit strings, Fourier
  analysis, PMF and `ProbComp`, codes), proof complexity, descriptive complexity, and Word RAM
  and algorithms, reusing checked examples.
- **Curated formal abstracts:** improve readability, and compare each changed abstract with its
  final source statements.
- **Archive `complexitylib-v1`** once its remaining work is dispositioned.

## Deferred scopes

These remain coverage targets but are deferred from the active queue; their issues were closed as
not planned, not as proved.

- The full VNP-completeness reduction for the permanent ([#321]). Arithmetic formulas now
  project to the permanent with dimension `Formula.size + 1` over every commutative semiring;
  a selector occurring in one permanent entry can be eliminated with one extra dimension when
  `2` is invertible. The conversion from VP witnesses to formulas, the two-entry gadget and
  general Boolean-sum elimination needed for VNP-hardness remain open.
- General auxiliary-input zero knowledge ([#324]); see the GMW theorem above.
- Williams's square-root-space simulation ([#361]) and implicit Tree Evaluation ([#367]), now the
  frontier track [#888].
- Vollmer's generalized-quantifier survey ([#399]): ordered leaf words, explicit uniformity and
  input-access models, finite-monoid classification and generalized logical quantifiers.

[archive]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md
[archive-fhe]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities
[#321]: https://github.com/cslib-community/complexitylib/issues/321
[#324]: https://github.com/cslib-community/complexitylib/issues/324
[#361]: https://github.com/cslib-community/complexitylib/issues/361
[#367]: https://github.com/cslib-community/complexitylib/issues/367
[#399]: https://github.com/cslib-community/complexitylib/issues/399
[#456]: https://github.com/cslib-community/complexitylib/issues/456
[#459]: https://github.com/cslib-community/complexitylib/issues/459
[#474]: https://github.com/cslib-community/complexitylib/issues/474
[#486]: https://github.com/cslib-community/complexitylib/issues/486
[#581]: https://github.com/cslib-community/complexitylib/issues/581
[#585]: https://github.com/cslib-community/complexitylib/issues/585
[#608]: https://github.com/cslib-community/complexitylib/issues/608
[#640]: https://github.com/cslib-community/complexitylib/issues/640
[#643]: https://github.com/cslib-community/complexitylib/issues/643
[#798]: https://github.com/cslib-community/complexitylib/issues/798
[#800]: https://github.com/cslib-community/complexitylib/issues/800
[#862]: https://github.com/cslib-community/complexitylib/issues/862
[#884]: https://github.com/cslib-community/complexitylib/issues/884
[#886]: https://github.com/cslib-community/complexitylib/issues/886
[#888]: https://github.com/cslib-community/complexitylib/issues/888
[#889]: https://github.com/cslib-community/complexitylib/issues/889
[#890]: https://github.com/cslib-community/complexitylib/issues/890
[#891]: https://github.com/cslib-community/complexitylib/issues/891
[#892]: https://github.com/cslib-community/complexitylib/issues/892
[#894]: https://github.com/cslib-community/complexitylib/issues/894
[#895]: https://github.com/cslib-community/complexitylib/issues/895
[#896]: https://github.com/cslib-community/complexitylib/issues/896
[#897]: https://github.com/cslib-community/complexitylib/issues/897
[#939]: https://github.com/cslib-community/complexitylib/issues/939
[#949]: https://github.com/cslib-community/complexitylib/issues/949
[#999]: https://github.com/cslib-community/complexitylib/issues/999
[#1002]: https://github.com/cslib-community/complexitylib/issues/1002
[#1104]: https://github.com/cslib-community/complexitylib/issues/1104
[#1124]: https://github.com/cslib-community/complexitylib/issues/1124
[#1155]: https://github.com/cslib-community/complexitylib/issues/1155
[#1351]: https://github.com/cslib-community/complexitylib/issues/1351
[#1539]: https://github.com/cslib-community/complexitylib/issues/1539
[#1572]: https://github.com/cslib-community/complexitylib/issues/1572
[#2468]: https://github.com/cslib-community/complexitylib/issues/2468
[#1817]: https://github.com/cslib-community/complexitylib/issues/1817
[#1885]: https://github.com/cslib-community/complexitylib/pull/1885
[#2019]: https://github.com/cslib-community/complexitylib/issues/2019
[#2062]: https://github.com/cslib-community/complexitylib/issues/2062
[#2063]: https://github.com/cslib-community/complexitylib/issues/2063
[#2205]: https://github.com/cslib-community/complexitylib/issues/2205
[#2213]: https://github.com/cslib-community/complexitylib/issues/2213
[#2289]: https://github.com/cslib-community/complexitylib/issues/2289
[#2145]: https://github.com/cslib-community/complexitylib/issues/2145
[#2084]: https://github.com/cslib-community/complexitylib/issues/2084
[#2290]: https://github.com/cslib-community/complexitylib/issues/2290
[#2423]: https://github.com/cslib-community/complexitylib/issues/2423
