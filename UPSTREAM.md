# Upstream integration

Coordination and integration decisions not already recorded in source.

The authoritative records are:

* [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json) and
  [lean-toolchain](lean-toolchain) for pinned versions;
* each module's `-- upstream:` markers for candidate, submitted, vendored or local-only status,
  including PR numbers and copied revisions; markers can also identify blocks within a module;
* [Complexity.lean](Complexity.lean) for the module inventory.

Use `python3 scripts/upstream_sync.py --offline` to list copied dependencies, and
`python3 scripts/upstream_sync.py` to compare recorded revisions and the base pin with upstream.
It checks head revisions, not source equality or unrecorded overlaps. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for synchronization and removal, and
[CONTRIBUTING.md](CONTRIBUTING.md#upstreaming) for preparing an upstream worktree.
Do not add a ledger row for an ordinary candidate or repeat its source marker here.

## Coordination before submission

* **Machine calculus.** Build on Christian Reitwiessner's `crei/tidy-universal` branch and its
  component PRs, including #1111, #1112 and #1138. Local `-- vendored:` comments identify required
  adaptations. The branch's `IterateWhile` supersedes the version from #1112. Coordinate the
  shared encodings and calculus through CSLib issue #611, including the `TapeEncodable`
  interface proposed in #590. Check #767 and its split #768 before adding space-to-time
  inclusions or overlapping class definitions; reconcile the local encoded, plain-machine
  definitions of `P`/`NP` with its `DTIME`-based language classes. The local `DSPACE`, `L`,
  `DTIME` and `EXP` (`Classes/Space/Basic`, `Classes/LogSpace`, `Classes/Time`, `Classes/EXP`)
  use #767's shapes over encoded instances; once #767 lands, derive them from its
  language-indexed classes rather than keeping parallel definitions. The local `PSPACE`
  retains its instance-dependent polynomial space bound;
  `mem_PSPACE_iff_exists_mem_DSPACE` in `Classes/Space` proves its equivalence to the local
  union of `DSPACE (n ^ k)`. A bridge to #767's language-indexed classes is still separate.
  Time and space constructibility are in `Classes/Constructible`, independent of hierarchy
  theorems. Selected-tape specifications
  formerly in `Combinators/StreamFold` and `Encodings/MultiPass` now live beside the plumbing
  operations; preserve their exact space bounds when resynchronizing the copied files.
  The step-machine layer (`StepMachine/*`, `Encodings/StepMachine*`, `Combinators/StepMachine`
  and their helpers) and the blocks marked `@9cce4cc7` in older copies come from a later local
  rewrite of the branch that is not yet published; `scripts/upstream_sync.py` reports them
  against the published head until it is. The rest of the branch is still copied at `@7f7c0696`.
* **Polynomial bounds.** The tidy calculus's size-parameterized `PolyBounded` adapts CSLib's
  `PolynomiallyBounded` and shares its closure API. Coordinate this adaptation with the tidy
  branch; preserve it when resynchronizing the vendored files.
  `Foundations/Data/Nat/PolynomialBound/Closure.lean` is the proposed next submission following
  #1067.
* **Mathlib TM2.** `Computability/Machines/Turing/TM2/*` certifies Mathlib's stack-machine
  statements directly through the tidy calculus; it does not depend on the TM0 simulator in
  [Complexitylib PR #72](https://github.com/SamuelSchlesinger/complexitylib/pull/72).
  Its dependent finite-table helpers (`Encodings/DPi` and `Complexity/PolyTime/DPi` under
  `Machines/Turing/MultiTape`) extend the existing table API. Coordinate these helpers with
  the machine-calculus work above before upstreaming. The forward bridges preserve polynomial
  time and transfer terminating polynomial-stack-space computations, using configuration counting
  and binary-clock iteration for space. The reverse compiler in `TM2/Reverse` constructs a
  finite-alphabet `FinTM2`, including canonical `haltList` cleanup, with linear time overhead and
  total stack length at most input length plus native work space plus output length.
  `Reverse/Transfer` proves polynomial-time and PSPACE equivalence under the original binary
  encodings; `PolyTime/List` supplies the word conversions and `TM2/Recoding` transfers TM2
  computations across them without decoding the typed embeddings.
  These comparisons do not preserve sublinear work-space conventions.
* **Probabilistic programs.** Coordinate the shared `PFunctor.FreeM` API with #1086–#1089 and
  typed oracles with #1129. The copied PMF blocks have their own markers and removal instructions
  in [Probability/PMF.lean](Complexity/Probability/PMF.lean); remove only the merged blocks.
* **Security games.** The #1068 negligible-bound base is now supplied by the cslib pin.
  `Crypto/Negligible.lean` imports it and retains the #1069 `fun_prop` registrations, with
  pointwise addition/multiplication wrappers needed by lambda-shaped automation clients;
  remove the submitted registrations when #1069 lands. The candidate public helpers
  `Negligible.add_fun` and `Negligible.mul_fun` remain until upstream declarations preserve
  those full names. `Crypto/Game.lean` retains the unmerged #1069 security-game API. Its two local pointwise/common-mixture advantage bounds (#802) must also be retained when
  syncing or removing that copy.
  The probability/game stack copies the October 23 upstream refresh (#1062, #1069, #1070,
  #1072 and #1129). `Crypto.negligible_iff` and the negligible closure lemmas now come from
  the base pin; local PMF additions and negligible automation remain alongside the copied portions.
  Exact revisions are recorded in their source markers.
  The following hybrid layer is tracked by its own marker in `Crypto/Game/Hybrid.lean`.
  `Crypto/Game/Statistical.lean` copies only the Boolean equality from #1072; its remaining
  declarations require the arbitrary-type metric replacement in #1065. Until that is in the
  base pin, extraction bounds quantify over every randomized test of the full encoded output,
  using the existing finite-PMF metric and `Game.Indistinguishable` with all tests admissible.
  Coordinate the finite PRG API and its distribution-based refactor in #1071 before adapting
  `Crypto/Primitives/PRG/Game`.
* **Query complexity.** Numerical measures and certificates use the merged
  `Computability/QueryComplexity` API directly, on `Fin n`/`Bool`. Generic decision trees,
  restrictions and Fourier analysis retain arbitrary coordinate/output types; sensitivity
  lower bounds there use explicit coordinate sets. The restriction representations agree
  definitionally, with `QueryComplexity/Restriction` connecting filling to `Forces`.
  Align the remaining tree representation in `Computability/DecisionTree` with #925 and
  coordinate its certificate follow-up `D ≤ C₀ C₁`; no second numerical measure API is retained.
* **Word RAM.** `Computability/WordRAM/*` adapt the bounded-word RAM of the Lean formalization
  accompanying the tromino undecidability paper,
  [`edemaine/lean-trominoes`](https://github.com/edemaine/lean-trominoes) @6d5b36c1 (Apache-2.0),
  which is not a CSLib branch. The adapted files retain the source's copyright notice
  (lean-trominoes contributors) and credit Erik Demaine alongside the adaptation author in their
  `Authors:` lines; coordinate follow-up submissions and attribution with him,
  alongside the CSLib algorithm-model work: Shreyas Srinivas's query-combinator
  programs (#685, and the register word-RAM models in his Algolean repository) and the merged
  query framework (#401), which
  count only lifted queries. A deeply embedded machine beneath such front ends answers, for the
  RAM, the objection that pure Lean computation is uncharged. The module docstrings record the
  deviations from the source. The operations form a basis (`WordRAM/Basis`) over
  `Cslib.Circuits.Signature`, and translation between bases (`WordRAM/MapOp`) uses the local
  `Circuit/SignatureHom` maps of signatures, so these files depend on that candidate. The
  unbounded-register `Computability/RAM`, inspired by
  Cook–Reckhow and supporting both unit and logarithmic costs, remains a separate candidate.
* **Generic RAM values.** `Computability/GenericRAM/*` supplies a shared finite-register RAM
  interpreter with configurable value, address, configuration and literal types, operation/test
  signatures, and fault policies. `WordRAM/Generic` embeds every existing word-operation basis
  with exact step, fault, output and instruction-count preservation, including arbitrary initial
  states; no existing public WordRAM definition changes. The signed instance follows the
  lean-trominoes signed range and its address, move, halt and program-counter checks, retaining
  its source credit. The algebraic instances use tagged natural words and exact field values:
  only natural words can address memory. Real comparison is mathematical, noncomputable
  semantics; prime-field interpretation is executable. The real variant follows the separation
  of words and reals in Erickson–van der Hoog–Miltzow, but uses finite named registers, a tagged
  memory and checked word arithmetic. These are explicit model choices, not a proved equivalence
  with their two-array model. Coordinate this common core with the algorithm-model work above;
  the existing Cook–Reckhow-inspired RAM and its logarithmic cost remain separate.
  `GenericRAM/Native` separately packages existing native TM `ComputableTidilyInO` witnesses for
  encoded scalar primitives, with caller-selected configuration encoding and unrestricted
  input-dependent bounds. Its forgetful bridge reuses `IsComputable`; polynomiality is a separate
  bound property. `GenericRAM/Native/Nat` supplies a checked bounded-natural addition model;
  `WordRAM/Native` supplies complete polynomial-time `NativePrimitives` bundles for
  `Basis.standard`, `Basis.additive`, `Basis.arithmetic`, and `Basis.exact` (plus restricted
  sub-bases and homomorphic preimages) with unary width and binary operands (#489).
  Both reuse Christian Reitwiessner's native arithmetic/encoding calculus.
  `GenericRAM/Simulation/{Finite,Turing,Run}` combine these per-symbol certificates with sparse
  memory and finite control to simulate single steps and clocked multi-step runs of any fixed
  generic-RAM program on native multitape Turing machines
  (`Cslib.GenericRAM.FiniteState.transport_inO`, `Cslib.GenericRAM.FiniteState.transport_polyTime`
  and `Cslib.GenericRAM.FiniteState.transport_polyTime_of_le_const`). `transport_inO` is
  parameterized by explicit time and space bounds; `transport_polyTime` needs a polynomial step
  bound (`hStepsBound`) and a polynomial bound on the encoded intermediate run results
  (`hOutLen`); `transport_polyTime_of_le_const` derives both from a constant step bound. Uniform
  arbitrary-program dispatch and charged configuration selection remain separate.
* **Signed programs on unsigned words.** `WordRAM/Signed/*` reuse `GenericRAM.Signed`'s
  range, arithmetic and interpreter. The sign-and-magnitude encoding needs one extra unsigned
  bit; the arithmetic blocks use two. `State`, `Operations`, `Compile` and `Input` extend them
  to complete programs over the full five-operation signed model (constants, copies,
  addition, subtraction, multiplication, Euclidean division/remainder with Lean's total
  zero-divisor conventions, memory, signed tests, jumps and halt). Successful source runs of `t`
  instructions transfer to one fixed unsigned program at width `w + 2` within `32*t + 5`
  instructions, including the five-instruction length header conversion and the final halt. Each
  source integer uses one target word, source memory addresses are unchanged, nine scratch
  registers precede the source register bank, and each source instruction occupies sixty-four
  target code slots. Code labels need not fit a data word in the target model. Run-prefix
  theorems preserve the complete source memory and register bank. This is forward correctness,
  not reflection of source faults; transfer from Anthropic's modular signed machine and its
  3SUM/APSP algorithms remains separate.
* **Direct 3SUM adaptation.** `Algorithms/ThreeSum/Convolution.lean` adapts the explicit
  Convolution-3SUM to Exact Triangle correctness reduction from Anthropic's
  [`formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp),
  `Sec3/Theorem21a/Convolution.lean`. Its reduction uses the arbitrary-matrix predicate in
  `Algorithms/ExactTriangle/Defs.lean`, shared with future Exact Triangle solvers.
  The three weight matrices use the original formulas; an explicit nonnegative magnitude bound
  also handles empty input. The native builder in `Algorithms/WordRAM/ThreeSum/{Cell,Fill,Memory}.lean`
  extends the one-weight kernel with index/address calculations and the complete matrix loop.
  Given its arguments in registers, it writes one instance in at most `131*t² + 5` instructions
  at width `w + 2`, excluding the halt; its theorem identifies the three encoded matrices and
  preserves the input. Layout, signed index/filler bounds and target address bounds are explicit.
  The existing signed and unsigned APIs were reused; no source machine or separate run semantics
  were copied. The full reduction host, native Chan–He preprocessing, fast Exact Triangle and full
  input/time/width/asymptotic composition remain in
  [#1394](https://github.com/cslib-community/complexitylib/issues/1394), including the improved
  Section 4 route needed for the published exponent 1.9992. Anthropic's copyright and attribution
  are retained; the native proofs and representation choices are local.

  `Algorithms/ThreeSum/ThreeSets.lean` and `ArrayPacking.lean` provide the generic distinct-position
  frontend and three-array packing. `Algorithms/ThreeSum/ChanHe/` now adapts the core mathematical
  reduction: minimum-prime searches, collision/heavy-element bounds, light-element arrays, bounded
  ternary recursion and composition with the frontend. At polynomial magnitudes it gives explicit
  length, count and magnitude bounds; `scanPairs` counts candidate-prime/element pairs and is not
  a charged running time. Generic finite-average and prime-counting lemmas live in Foundations.
  See milestone [#1435](https://github.com/cslib-community/complexitylib/issues/1435).
  `Algorithms/ExactTriangle/Lopsided.lean` adapts the finite unweighted lopsided query/counting
  interface from the same pin's `Sec3/MatrixLanguage.lean`: arbitrary-injection zero padding,
  common-neighbor counts as product entries, detection, the zero/one converse, and signed products
  from `4 * β²` count instances with the original queried edges. Its digit identities live in
  `Foundations/Data/Matrix/IntegerBits.lean`, reuse Mathlib's pointwise positive/negative parts,
  and give an explicit `Nat.log 2 U + 1` magnitude-bit bound including zero. Query answers use
  `Set.EqOn`; no additional weighted-triangle predicate or source machine is introduced.
  This is the mathematical interface milestone
  [#1438](https://github.com/cslib-community/complexitylib/issues/1438), with no sparsity assumption,
  preprocessing/time claim or solver. `Algorithms/ExactTriangle/{Weights,Hashing}.lean` now adapts
  the modular counting/coefficient identities, minimum-count prime and uniform false-positive
  bound from `Sec3/Theorem17/Hashing.lean`, using supplied matrices and the existing decision
  predicate. Its integer-square window characterisation supports later native enumeration.
  The quotient/coefficient API lives in `Foundations/RingTheory/CyclicIntRing.lean`; the uniform
  all-window prime-count bound lives in `Foundations/NumberTheory/PrimeWindow.lean`, retaining
  the source credit to Mathlib, Patrick Stevens and Bolton Bailey. These are mathematical
  statements, not native instructions or an assumed solver. See
  [#1442](https://github.com/cslib-community/complexitylib/issues/1442).
  `Algorithms/ExactTriangle/{Splitting,Witnesses}.lean` adapts the complete finite splitting and
  witness recovery component ([#1447](https://github.com/cslib-community/complexitylib/issues/1447)),
  using the existing matrices, lopsided graph and `Set.EqOn` answer API. Computable integer parameters
  retain the source's exact real floor/ceiling specifications through checked bridges.
  `Algorithms/MatrixMultiplication/Schonhage/` adapts the tensor-recursion core from the same pin's
  `Sec2/{Lemma6,Recursion,Lemma7_8,Lemma10}.lean`: the ten-term polynomial identity with explicit
  error, full evaluation, shared encodings, pruned values, visited leaves and passed-set totals.
  Its pure finite recursion traces are not native machine semantics or charged instruction costs.
  The zero-depth empty-query root exception is explicit, with an unconditional root-or-leaf API.
  See [#1459](https://github.com/cslib-community/complexitylib/issues/1459); tiling/sparse leaf bounds
  remain in #1394.
  The existing
  signed and unsigned APIs were reused; no source machine or separate run semantics were copied.
  Tensor/sparse query programs, the full reduction host, native Chan–He preprocessing, fast Exact
  Triangle and full input/time/width/asymptotic composition remain in
  [#1394](https://github.com/cslib-community/complexitylib/issues/1394), including the improved
  Section 4 route needed for the published exponent 1.9992. Anthropic's copyright and attribution
  are retained; the native proofs and representation choices are local.
