# Work with randomized and oracle programs

Start with three separate questions: what program is being described, what distribution it denotes, and what machine implements it. `ProbComp α` describes finite-uniform sampling with ordinary `do` notation; `ProbComp.eval` interprets that syntax as a `PMF α`. `ProbOracleComp spec α` adds external requests whose reply types are given by `spec`. The underlying `OracleComp` is a free program over a typed request interface. A PMF supplies mathematical probability semantics; merely writing a PMF does not supply a sampler or a runtime certificate. The [programs and realization reference](../programs-crypto-and-probability/programs-and-realization.md) explains these layers and their sources. [complexitylib][complexitylib]

## Certify a closed randomized routine

Use `IsPPTOn input output program` when the required conclusion is a uniform, strict polynomial-time implementation on encoded types. The encodings are embeddings into bit lists. One finite-control fair-coin machine and one polynomial clock must work for every input, with exact equality of encoded output laws. Output writing is charged. This is the contract to request before proving a probabilistic routine efficient.

<!-- worked-example -->

**Worked example: Compose a fair coin with a certified callback**

**Goal:** certify a coin-sampling routine, then a scan whose deterministic callback has a supplied polynomial-time certificate.

Open [ComplexityTests/PPTTactic.lean](../../ComplexityTests/PPTTactic.lean). Its entry import is `Complexity.Tactic.PPT`; the file also imports `Complexity.Crypto.Computational.GGM.Evaluation` for later clients. The following contextual excerpt uses its `open Cslib Cslib.Probability Turing.MultiTapeTM`. It is copied from the checked file, not independently checked as a standalone snippet.

<!-- excerpt: ppt-coin-reverse -->
```lean
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt
```

The working sequence is: choose the input/output encodings, write the program, supply certificates for named callbacks, and invoke `ppt`. It combines probabilistic composition rules with deterministic `polytime` automation. For a callback, the missing obligation is often a deterministic certificate with the exact captured-argument encoding. This second contextual excerpt, from the same client, makes that obligation visible:

<!-- excerpt: ppt-callback-scan -->
```lean
example (test : List Bool × Bool × ℕ → Bool)
    (htest : ComputableInPolyTime test
      (encPair encBits (encPair encBool encUnary)) encBool) :
    IsPPTOn encBits encBool (fun word => do
      let bit ← ProbComp.uniform Bool
      pure ((List.range word.length).any fun i => test (word, bit, i))) := by
  fail_if_success (clear htest; ppt)
  ppt
```

**Result:** native efficiency of the whole sampling-and-scan routine. This does not establish the application-specific meaning of `test`.

**When it fails:** compare tuple association and encodings before unfolding the machine. Here the scan index is unary; a binary certificate is a different contract. For folds, inspect the client's explicit `PolyBounded` growth premise. For a named routine, the same file demonstrates registering its proved theorem with `@[program_certificate]`.

<!-- /worked-example -->

Also check the sampler itself. `ProbComp.uniform (Fin 3)` has exact uniform semantics, but a strictly bounded fair-coin machine cannot give each outcome probability one third. The client deliberately tests that `ppt` does not certify it for free. Use an applicable dyadic sampler or the library's approximate-sampling results, carrying the approximation error into the later probability proof.

## Certify an adaptive oracle client

For native oracle efficiency, start with `WordOracleComp Operation α`: finite operation names and word payloads/replies.

<!-- worked-example -->

**Worked example: Bound the reply prefix of an adaptive oracle call**

**Goal:** certify the oracle client's native runtime while allowing its next query to depend on the previous reply.

Open [ComplexityTests/OracleComposition.lean](../../ComplexityTests/OracleComposition.lean), whose main import is `Complexity.Computability.Probabilistic.Oracle.Composition`. Its query-bound examples additionally import `Complexity.Computability.Probabilistic.QueryBounds`. This contextual excerpt uses the file's `open Cslib Cslib.Probability Turing Turing.MultiTapeTM`:

<!-- excerpt: oracle-adaptive-prefix -->
```lean
private noncomputable def adaptive (word : List Bool) : WordOracleComp Bool (List Bool) := do
  let first ← List.take 1 <$> ProbOracleComp.query (false, word)
  if first = [true] then List.take word.length <$> ProbOracleComp.query (true, first)
  else pure []

-- The certificate is found compositionally from the bounded-prefix query and the conditional.
private theorem adaptive_isOraclePPTOn : IsOraclePPTOn encBits encBits adaptive := by
  unfold adaptive
  fun_prop
```

First specify the operation set and request representation. Then bound the amount of each reply inspected or retained, prove deterministic preprocessing efficient, and compose the query/conditional rules.

**Result:** one machine and clock work for every input, state type, stateful handler and initial state, preserving the joint law of output and final oracle state. The certificate charges request construction and reply access; the external handler's computation remains external.

Next inspect behavior under a concrete handler. The same client defines `counting`, which increments a counter on every call. Its semantic examples establish final count one on the unselected branch and two on the selected branch. This catches interaction differences that equality of output marginals could hide. For the simpler `runWith` interface, open [ComplexityTests/OracleSemantics.lean](../../ComplexityTests/OracleSemantics.lean).

Use `adaptive_isOraclePPTOn.query_bounds` to obtain polynomial bounds on external call count and request length. A separately proved `IsCostBounded` charges chosen requests along every path; `ProbOracleComp.IsQueryBounded` counts external calls rather than private samples. Neither bound by itself pays for arbitrary Lean callbacks.

**When it fails:** if `fun_prop` fails on returning an entire oracle reply, check whether the requested conclusion permits unbounded output. The linked client contains explicit failure examples and the bounded-prefix repair.

<!-- /worked-example -->

When replacing the external handler with an implementation, open [Oracle/Substitution.lean](../../Complexity/Computability/Probabilistic/Oracle/Substitution.lean). The plain-certificate variant `IsOraclePPTOn.run_interpret_preprocess_open'` requires efficient preparation, initialization and handling, plus an invariant and bounds on reply length and added encoded state. Its `hresources` premise also certifies a uniform unary computation of the resource allowance from the original caller and request; an abstract polynomial bound alone does not supply this certificate. Repeated state doubling explains why “each call is polynomial time” is insufficient.

## Connect a randomized RAM loop to its answer law

Use this route when a randomized Word-RAM loop already exists and you want to derive its answer
distribution from an oracle specification. First choose the observed value, a supported-state
postcondition and explicit instruction and random-call budgets. Import
[Randomized/LoopSegmentLaw.lean](../../Complexity/Computability/WordRAM/Randomized/LoopSegmentLaw.lean).
`LoopSegmentLaw` retains the existing `LoopSegment` execution witness and bounds every supported
path. Its exact equality describes the chosen observation's PMF; its instruction budget is an
upper bound, not an assertion that every run takes the same time.
Random-call budgets use the existing [randomized RAM convention](../algorithms-and-memory/wordram-and-bridges.md),
which gives finite-interval sampling its own instruction and resource semantics.

From the repository root, open the complete
[WordRAMLoopSegmentLaw client](../../ComplexityTests/WordRAMLoopSegmentLaw.lean), including its
import, namespace and concrete starting state. Follow three steps:

1. Prove the body's `ExecRandLaw`, including its supported-state postcondition and budgets.
   `LoopSegmentLaw.single` requires the active guard and adds two instructions for loop control.
2. For several segments, use `LoopSegmentLaw.trans`. Supply the next law for **every** state
   satisfying the preceding postcondition; instruction and random-call budgets add.
3. Use `LoopSegmentLaw.finish` after proving the guard false on the entire final postcondition.
   It adds two instructions for the exit check and yields the existing `ExecRandLaw`.

The linked one-bit fixture sets a register to one and exits. Its budget is five instructions:
one body instruction, two control instructions and two exit instructions, with zero random calls.
From a configured checkout, check that client and the specification-law examples with:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.WordRAMLoopSegmentLaw ComplexityTests.KargerFastCutLaw
```

A successful build checks the paid loop and the triangle, recursive seven-vertex and zero-cut
graph cases. If composition fails, compare the continuation law's observation and postcondition
with the preceding segment. If finishing fails, prove the exit condition for all supported
states. A query-count bound alone does not supply either instruction bound.

For the larger application, follow
[KargerFastCutLaw](../../ComplexityTests/KargerFastCutLaw.lean) into
[Lean/Karger/FastCut](../../Complexity/Algorithms/Lean/Karger/FastCut.lean), then
[KargerStein](../../Complexity/Algorithms/WordRAM/KargerStein.lean). The specification restarts
both recursive branches from the same parent graph and interprets their replies independently.
Its success statements concern a minimum-cut **value**, with the stated positive-minimum-cut
hypothesis; cut support also covers the zero-cut fixture. The native laws retain their word-fit,
frame and supported-path resource premises. To pass from a code observation to a halted cut
answer, [Karger/OutputLaw](../../Complexity/Algorithms/WordRAM/Karger/OutputLaw.lean)'s
`program_of_law` additionally requires fitting input words, cut support and allowance for the
final halt. This specification bridge leaves the memory-oracle contraction realization and
recursive frame-stack migration open.

## Use the bounded H4 hierarchy clients

For selected correction/pilot cutoffs, import
[HierarchyCutoffs](../../Complexity/Foundations/Probability/HierarchyCutoffs.lean).
Supply a `FourthRootHierarchyParams 16 1 16 32 8` witness and both ordered retention laws;
`correctionSampling` and `pilotSampling` derive the incoming count from the existing detector.
Their public projection equations let ordinary imports inspect recipe parameters without
unfolding opaque constructors. `correction_col_support` and `pilot_col_support` apply to
arbitrary raw, preparation and maximum children. The support margins use the actual Q/ρ gates.

For finite prime frame environments, start with
[HierarchyRankCutoffs](../../Complexity/Foundations/Probability/HierarchyRankCutoffs.lean)
and its [complete regression client](../../ComplexityTests/HierarchyCutoffs.lean).
The constructor examples use H=4, P=5 and horizon zero on a positive singleton matrix.
These constructors have two independent full-environment seeds. For the genuine mean of
one actual environment, import
[HierarchyCorrectionMean](../../Complexity/Foundations/Probability/HierarchyCorrectionMean.lean)
and follow its [complete regression client](../../ComplexityTests/HierarchyCorrectionMean.lean).
`terminalSplit` retains every spectator coordinate. Use `genuine_request_mean_usage` for
an independent usage grid rate, including narrower usage; the same-rate specialization is
`genuine_request_mean_density`. Both transport the source-conditioned average through the
split and derive source nonemptiness and the actual usage density. Supply a nonzero padding
multiplier, injective identifiers, an admissible request, a finite prime rank horizon, equal
true source/terminal stage rates, and a nonnegative substochastic matrix C bounded entrywise
by that rate. The usage exponent need not belong to the rank horizon: its box has positive
side at every finite exponent. The children are the existing raw input, its genuine joint
source/usage preparation and the final pilot maximum. The target remains the existing
correction iterate on the true split channels. `CorrectionSampling.withUsage` reuses all gates
and source/incoming laws, replacing only the measured usage marginal and terminal pair bound.

The P=5 client has different nonempty source and terminal copy suffixes and a genuine final
pilot proved zero from its detector rank. Its narrower-usage example fixes source/rank exponent
1 and uses usage exponent 2, with actual densities 81/625 and 16/625 and a strictly positive
complete request mean. Thus the usage change is observable in the actual environment.

For a sampling source narrower than the true stage, import
[HierarchySourceSampling](../../Complexity/Foundations/Probability/HierarchySourceSampling.lean)
and use `source_request_mean`; follow its
[complete regression client](../../ComplexityTests/HierarchySourceSampling.lean).
Supply source exponent `s`, stage exponent `k`, `k ≤ s`, and a horizon containing `s`.
The true `stageSource` retains the source role and suffix at the terminal stage rate.
`stageRaw` and `stageMaximum` use these genuine stage channels. `sourcePreparation`
uses the actual sampling source for its incoming gate. `source_normalizer` identifies its
joint actual source/usage mean on the same environment, and `stage_atomCutoff_eq`
preserves the true cutoff. `CorrectionSampling.withSource` changes only the sampling-source
pair law, preserving the true input, final pilot, gates and incoming budget. The common
`correctionRequest_eq_split` avoids rebuilding the split transport for each choice of children.

The P=5 regression has source/stage/usage exponents 2/1/3, actual densities
16/625, 81/625 and 1/625, different nonempty copy suffixes, and a free spectator role.
It proves a positive complete actual request mean with the genuine final pilot. Usage
exponent 3 is outside the required source/stage horizon 2.

To discharge the raw input fourth moment for a positive-iteration residual, import
[HierarchyRawMoment](../../Complexity/Foundations/Probability/HierarchyRawMoment.lean)
and apply `rawIncomingNormalized_noise_le_lower`. Supply positive N, u, row rank K and
incoming rank Kc. The selected cutoff laws derive the actual left correction child's
range `CA = 2 * Q(atomCap)`, row support K and incoming support Kc, for arbitrary raw,
preparatory and pilot children. Its source-released product costs
`K^3 * CA^4 * Kc * (rate(km) / u)` times the weighted right-child fourth moment.
`incomingMomentBudget` adds the actual weighted direct and negative child moments, with
a conservative factor 64 for the signed sum. The right child includes the exact usage
ratio and midpoint marginal divisor from `rawSample`; it never takes the old source as
an extra argument. All children may share every rank coordinate.

The [checked examples](../../ComplexityTests/HierarchyRawMoment.lean) include a complete
P=5 residual with input moment one and positive correction product, different nonempty
copy suffixes and a spectator. A correlated two-factor example has exact moment 257/2.
An identity family with one nonzero per row and column has moment n at N=u=1, so support
and range caps alone do not imply a width-independent unnormalized moment. The new client
requires lower-child moments to be paid by a later induction; it assumes no final raw or
noise certificate. Zero correction remains literal; the moment/noise bridge here treats
positive iterations. Pilot/copy paths, quantitative lower-child budgets, summation and
recursive/native correctness remain open.

For the first compression signal, import
[FirstSignal](../../Complexity/Foundations/Probability/NormalizedAtomRows/FirstSignal.lean)
and apply `actualFirstSignal_noise_le_lower`. Its child-budget-indexed inputs are genuine
`rawIncomingNormalized` samples. `firstSignalIncrement` takes successive conditional-walk
differences from zero; `actualPrefix_firstSignalIncrement` identifies prefix i with walk
i+1 divided by `rate k`. Stationarity on the full terminal slice, including empty slices,
then identifies `actualNoiseEntry` with centered walk noise divided by
`rate k * (1 + G / rate k)`.

The endpoint row moment is bounded directly by `rate k` to the inverse fourth power,
times `32 * lambda^(2*steps(i+1))`, times the explicit lower-child
`incomingMomentBudget` at budget i+1. No maximum-entry conversion, hidden width constant,
or independence assumption is used. The
[regressions](../../ComplexityTests/ActualFirstSignal.lean) check nonzero nonconstant
telescoping prefixes, zero inputs, empty slices and a nonconstant random mean/moment.
Choosing numerical walk lengths still requires a numerical payment for those child
moments; arbitrary children have no uniform payment here. The preparatory second signal
needs its own moment bridge, and recursive induction and native RL=L remain open.

For a coarser source, `source_incoming_cost_le` quantifies the generic incoming cost as
`32 * R * (sourceRate / stageRate)`; the fixed incoming rank is not proved to pay that
inflated budget. Arbitrary coarser sampling sources, a fully assembled recursive hierarchy,
lower-child budget induction, native realization and RL=L remain in
[issue #1721](https://github.com/cslib-community/complexitylib/issues/1721).

## Carry the certificate into a security proof

Keep efficiency and security as separate goals. In [Crypto/Computational/Basic.lean](../../Complexity/Crypto/Computational/Basic.lean), computational indistinguishability quantifies over certified strict-PPT distinguishers. It does not require the compared PMF ensembles to be efficiently sampleable or polynomially bounded in length. Check those properties separately when the intended construction needs them.

Specify the experiment, admissible adversaries, success event and assumption; prove the reduction's efficiency using the routines above; then prove the probability or advantage inequality. Semantic rewrites and native certificates discharge different obligations. If a proposed reduction only has a query bound, return to the realization step before calling it a computational security reduction. Use the [security-game reference](../programs-crypto-and-probability/security-games-and-primitives.md) to choose the correct primitive and adversary model.

[complexitylib]: ../sources.md#complexitylib
