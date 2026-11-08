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
* **Universal simulation.** The local universal interpreter preserves Christian Reitwiessner’s
  description format and execution semantics. Its resource certificates now separate
  transition-description size and binary input-head length from the copied configuration;
  `Universal/Input` uses the existing native streaming fold to emit a selected input symbol
  without repeatedly copying list tails. Retain these local improvements when synchronizing
  `Universal/Complexity`, `Bound` and their resource consumers with `crei/tidy-universal`.
  `Bound`'s `q₀_le`, `tapes_le` and `table_le` are public locally, for the time–space speedup
  in `Classes/TimeSpace/Speedup` and for `Universal/WindowedBound`; keep them public when
  synchronizing.
  This is an extension of the existing interpreter, not a buffered Hennie–Stearns backend.
  `Universal/Windowed*` adds a divide-and-conquer windowed simulation on top of the vendored
  description format and `stepWith`; with the native `Combinators/StackLoop` and
  `Combinators/DivConq` combinators it proves the `O(t log t)` bound
  `computableInO_universal_nlogn`. It is a new local construction layered beside the vendored
  files, not a revision of them; keep it out of the copied modules when synchronizing.
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
  signatures, and fault policies. `WordRAM/Defs` embeds every existing word-operation basis
  with exact step, fault, output and instruction-count preservation, including arbitrary initial
  states, and derives the word RAM's interpreter metatheory from the generic one; the WordRAM
  definitions keep their own syntax and step function. The signed instance follows the
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
* **Native shared tensor encoder.** `Algorithms/WordRAM/MatrixMultiplication/Schonhage/` implements the complete shared left/right
  encoding milestone ([#1493](https://github.com/cslib-community/complexitylib/issues/1493)).
  Fixed standard-WordRAM code with 32 registers transforms one coordinate at a time between
  two disjoint `10^L` buffers. It starts from `State.init` with a depth header and `7^L`
  sign-and-magnitude words, computes all public `encodingL`/`encodingR` values, and preserves
  the input and every cell outside the two buffers. Mathlib's `finFunctionFinEquiv` supplies
  least-significant-first string numbering. All stages, powers, indices, address arithmetic,
  signed add/subtract blocks and the final output copy cost at most `240*(L+1)*10^L`
  instructions; halt adds one. Signed operands have magnitude bounded from the original
  input by `7^L*A < 2^(w-1)`; the explicit natural bound `L+64+64*10^L` must fit target width
  `w+2`. The two extra bits and actual arithmetic-block costs come from the existing native
  signed kernels, without a copied source machine or a whole-program simulation hypothesis.
  The existing array-copy interface is retained, with a narrow generalization for disjoint
  blocks in either address order or identical blocks. `Encoding.setup` and `Encoding.powerBody`
  retain their simultaneous `7^L`/`10^L` loop sharing the `stage` counter (`5*L+18` setup
  instructions) rather than running two sequential `WordRAM.Power.program` loops.
  This encoder is reused by the shared-band, routed-product and complete native composition
  described below; its standalone contract does not assert the complete 3SUM exponent.
* **Native shared-band preparation.** The native shared-band preparation component
  ([#1523](https://github.com/cslib-community/complexitylib/issues/1523)) computes a deterministic
  `Layout` and both subset tables by native mask/popcount scans, computes the square-root block
  count and its square by renaming `NatSqrt.program` (`BandPreparation.rootRegisters`) followed by
  one multiplication (`5*sqrt(k)+8` steps), and decodes each band-array index into the original
  row/column and thin-dimension coordinates. Real matrix bounds are checked before row-major
  multiplication.
  Each shared row/column band calls the unchanged encoder once; tiles refer to its catalogue
  block in the existing leaf order. The fixed 96-register standard code starts from actual
  `State.init` scalar/matrix input, charges snapshot and restoration of the complete original
  prefix, and preserves arbitrary outside memory. All counter/address fits follow from an
  explicit original-parameter word budget; signed fits follow from the original entry bound.
  Its complete instruction bound, including halt, is
  `81920*(L+1)*N²/(4^m)^(1/18)` when `L=19m` and `N≥(4^m)^18`. Native power, ordered-filter,
  finite-digit and row-major list lemmas live in small topic modules; the existing mathematical
  layout, matrix and encoding interfaces are reused. No source machine or call/time oracle
  is introduced.
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
  were copied. `Algorithms/WordRAM/ThreeSum/Host/` adds the complete charged native host: ordinary
  header initialization, polynomial magnitude computation, square root, consecutive matrix layout,
  all `2t` instances and a finite solver program in a disjoint register bank. Its initialized run
  theorem connects the actual pre-halt state to the Convolution-3SUM answer and preserves the input.
  The host's source-width threshold is `(20κ+125)clog₂(N+2)`; signed kernels use target width `w+2`.
  This host module remains parametric in a concrete solver's execution/correctness/frame theorem;
  the actual canonical solver and complete 1.9992 ordinary-host composition are described below.
  [#1394](https://github.com/cslib-community/complexitylib/issues/1394) tracks maintainer integration.
  Anthropic's copyright and attribution are retained; native proofs and representation choices
  are local.
  Native numeric parameter computation, signed-residue/histogram counting, trial-division prime
  tables, collision-tested least-prime scans and complete two-prime modulus selection also use
  the existing `WordRAM.Code`/`ExecWithin` APIs. Their explicit local fit, frame and charged-cost
  contracts are composed by a fixed 128-register bounded traversal with an explicit seven-word
  stack frame and exact preorder packed output. The traversal consumes a root descriptor and
  runtime fuel; its polynomial local envelope derives kernel fits and charges every stack,
  descriptor and address operation. It does not invoke a Convolution-3SUM solver. Composition
  from initialized input through every frontend root is proved in
  `Algorithms/WordRAM/ThreeSum/ChanHe/Preprocessing.lean`. One finite 128-register program per
  fixed magnitude exponent returns the existing exact finite instance list. All fits derive from
  `(1300κ+7865) clog₂(n+2)` physical width; every run prefix uses polynomial words/addresses even
  at wider admitted widths. Its charged cost is at most
  `Kκ (n+2)(sqrt(n+2)+1)(log₂(n+2)+1)^13`, including the final halt. The complete native
  preprocessing milestone is #1446. The ordinary host first used that complete catalogue
  (#1559). `Algorithms/WordRAM/ThreeSum/Decision.lean` now consumes each actual packed node
  during the native traversal: its current packed pointer, common length and allocation endpoint
  supply the Convolution host's arguments. No pointer-table store or subsequent table read is
  executed. The caller-owned matrices start at the current node endpoint; the callee preserves
  every pending heavy buffer and frontend source below it. The exact preorder and all calls
  remain, including after a positive verdict. One actual post-consumer copy releases the
  packed/residue/histogram tail for later construction. Persistent heavy-buffer allocation is
  monotone and the conservative table gap remains reserved. `Decision/VisitorRelease` proves
  the retained child endpoints and exact released frontier. `Visitor.live_transition` gives
  the actual body's final heap as its initial heap plus three count cells and the sum of current
  input-column lengths; skipped bodies leave the heap unchanged. The discarded tail has that
  length sum plus `4*N+M` words. These storage equalities do not improve the proved total-space
  or arbitrary-callee touched-high-water bound.
  One finite program per fixed exponent and certified finite
  Exact Triangle block returns the existing distinct-position verdict, with derived positive
  logarithmic physical width, polynomial words/space at every admitted-width prefix, and a fully
  charged compositional bound at the actual packed size. `Host.Callee` requires actual finite-code
  execution, matrix correctness, logarithmic width and a protected-prefix frame on arbitrary old
  scratch memory; `Host.Slow.callee` is a proved exhaustive native instance.
  The canonical `ExactTriangle/ParameterSelecting.callee` computes actual integer parameters,
  selects a genuine minimum-count prime and runs the box-backed controller or exhaustive small
  branch. Its actual time field is uniformly `Oκ(n^(3−33/20000))` for polynomial original
  magnitudes, with no selected-prime or runtime-law hypothesis. `ThreeSum/Decision/One9992`
  proves the complete ordinary integer endpoint: one fixed computable 848-register standard
  program per magnitude exponent, all-length distinct-position verdict, initialized same-state
  prefix/halt, logarithmic admission, polynomial every-wide words/support and charged
  `Oκ(n^1.9992)` steps. Equal values at different positions are permitted. Unit Word-RAM time,
  canonical signed encoding and polynomially bounded integers are explicit; this is not
  arbitrary-real or bit/Turing time, or the source machine's `SolvedInTime` predicate.
  No selected abstract is changed. Native tuning and representation choices are original;
  the finite reductions, builder, tensor identities and box mathematics retain their source
  credit. `ChanHe/ConvolutionSizes` transfers original magnitudes to the actual packed side;
  finite and native count bounds share `shifted_count_bound_le`.
  `ThreeSum/Decision/Runtime` factors the charged analysis independently of any concrete callee:
  every uniform ET saving `0 < δ ≤ 1` gives every ordinary exponent `a > 2-δ/2`. `Transfer`
  derives the same initialized verdict and every-wide word/support contract. The weaker
  `Subquadratic` endpoint now specializes this same canonical tuned pipeline at `2-1/5184`;
  there is no second conservative implementation or duplicate fixed-exponent proof.
  `Foundations/Data/Nat/LogRpow` remains general mathematics intended for Mathlib, transporting
  real log little-o to shifted natural logs for side/count/preprocessing estimates without
  expanding a widely imported hub.
  The follow-up #2380 extracts `Computability/WordRAM/Call` with migrated ordinary-host and
  traversal clients. Fixed-bank record transfers (`Traversal.WordStack.pushRecord`/`popRecord`)
  stay in `ChanHe/TraversalStack`, beside the word dispatcher that #2272 made traversal-local.
  `Traversal.OutputLayout` continues to export the standalone producer's live table/payload
  endpoints. The ordinary visitor instead supplies its actual current node endpoint,
  independently of the polynomial value envelope. Callee framing preserves this live prefix.
  `Decision.program` takes finite solver code directly; the old catalogue controller and its
  `Controls`, `Call`, `Body`, `Loop` and `Initialize` proof modules are removed. Shared quantitative
  definitions live in `Decision.Cost`; their values, the initialized endpoint's admission and
  the 1.9992 bound are unchanged. The internal arbitrary-state `exec_large` helper now requires
  full initial boundedness, derived by the initialized-input caller. The catalogue and visitor
  root proofs share the actual 68-instruction initialization certificate in
  `ChanHe/TraversalInitialize`; register renaming retains its stack frame and readback.
  `Visitor.construct_consume` exposes the original construction state and actual callee frames,
  so only live child/stack views cross the call; no complete post-call packed view is rebuilt.
  `VisitorCost` charges the
  consumer plus packed-tail release at `Host.callerTime+8` and proves the unchanged budget
  transfer with fixed slack 18 and four per emitted node; `exec_consume` alone retains its
  `Host.callerTime+7` contract. `GhostLoop.loop_potential_state` charges variable actual body costs
  and both loop-control instructions through an explicit mathematical potential.
  `One9992` adds admissibility/input fitting and standard uniform decision/time corollaries
  while retaining the complete initialized-run theorem. The Operator Manual companion documents
  these APIs and the quantitative account; no selected abstract or agent workflow changes.

  The preprocessing stage proofs are private implementation details: `PreprocessingSetup`
  contains snapshot, prime-table and reservation setup; `PreprocessingLoop` contains the forest
  invariant and loop proof. `PreprocessingExecute` uses `import all` for these two companions;
  visitor initialization reuses the actual setup contracts through `import all` too.
  Initialized-input, readback, width and resource endpoints remain available through
  `Preprocessing`.

  Bounded API follow-ups from the traversal/preprocessing reviews: move
  `modulus_bounds_of_candidates` from `SelectorBounds` beside `Collisions`' `modulus_bounds` and
  derive or cross-reference the stronger bound, migrating `TraversalCall` and selector tests.
  Derive `Structured`'s `ExecWithin.loop_invariant` as the `Data`-state case of
  `GhostLoop`'s `ExecWithin.loop_invariant_state`, preserving the existing copy/residue/padding/
  search/reservation clients. Resolve the current import direction by keeping both rules in one
  loop topic module before changing those clients.

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
  with descriptive lemmas in `Cslib.Matrix`. The scalar magnitude-bit bound, including zero,
  lives in `Foundations/Data/Int/LogBounds.lean`. Count answers use `Set.EqOn`; detection
  consumes a direct iff on queried edges. No additional weighted-triangle predicate or source
  machine is introduced.
  This is the mathematical interface milestone
  [#1438](https://github.com/cslib-community/complexitylib/issues/1438), with no sparsity assumption,
  preprocessing/time claim or solver. `Algorithms/ExactTriangle/{Weights,Hashing}.lean` now adapts
  the modular counting/coefficient identities, minimum-count prime and uniform false-positive
  bound from `Sec3/Theorem17/Hashing.lean`, using supplied matrices and the existing decision
  predicate. The application-independent `Nat.sqrtPrimeWindow` API lives in
  `Foundations/NumberTheory/SqrtPrimeWindow.lean`; its integer-square characterization supports
  native enumeration, and splitting and witness recovery reuse it.
  The quotient/coefficient API lives in `Foundations/RingTheory/CyclicIntRing.lean`; the uniform
  all-window prime-count bound lives in `Foundations/NumberTheory/PrimeWindow.lean`, retaining
  the source credit to Mathlib, Patrick Stevens and Bolton Bailey. These are mathematical
  statements, not native instructions or an assumed solver. See
  [#1442](https://github.com/cslib-community/complexitylib/issues/1442).
  The native cyclic-convolution prerequisite under
  [#1701](https://github.com/cslib-community/complexitylib/issues/1701) reuses that quotient in
  `Foundations/RingTheory/CyclicIntRing/Coefficients.lean` and supplies actual standard signed
  array multiplication in `Algorithms/WordRAM/MatrixMultiplication/CyclicConvolution/`.
  Source indexing/quotient mathematics adapt pinned Anthropic `RingOps.lean`/`Cyclic.lean`;
  the native execution, frame and `42p² + 9p + 4` pre-halt instruction bound are proved directly.
  The concrete counter continues in `Algorithms/WordRAM/ExactTriangle/CountPrime/` and the
  native explicit-stack `Algorithms/WordRAM/MatrixMultiplication/Strassen/` component, using
  original native pointwise signed array operations under `Computability/WordRAM/Signed/`.
  It selectively adapts the pinned `CountPrime`, `Strassen`, `ZOrder` and `Count` algorithms;
  actual standard WordRAM setup/residues/matrices/seven-product recursion/extraction are proved
  from original signed arrays. The 128-register ABI uses raw arguments 64..69 and result 70;
  initialized input is raw `(n,p)` plus three canonical signed row-major arrays. The existing
  `ExactTriangle.countZeroMod`, cyclic quotient and Morton APIs retain their meanings.
  Native cost, including halt, is at most `3704*(p+1)²*(n+1)^2.81`; all p-dependent coefficient
  arithmetic is charged, rather than importing Light's ring-operation constants. If the
  original modulus and weight bound satisfy `p,A≤(n+2)^κ`, physical width
  `(κ+24)*clog₂(n+2)` suffices and every wider prefix has words/support below
  `(n+2)^(κ+25)`. The generic caller allows dirty scratch and original-array aliasing below
  its workspace. `Int.toNat_neg_emod` is kept in the existing integer-residue topic module.
  This completes the counter's mathematical/native component, with validation/review tracked
  in #1701. Native minimum-count prime selection (#2098) is implemented in
  `Algorithms/WordRAM/ExactTriangle/PrimeSelection/`: square tests and charged trial division
  enumerate the exact existing prime window, invoking the real counter on original signed
  matrices and dirty scratch. Original-input halting correctness and the existing selected-prime
  predicate are proved, with charge at most `3704*(sqrt(D)+1)^3*(n+1)^2.81 + 42*(D+1)` including
  header/halt. For `D≤n`, `κ≥1` and weights bounded by `(n+2)^κ`, physical width
  `(κ+30)*clog₂(n+2)` suffices, and all wider prefixes have words/support below
  `(n+2)^(2κ+60)`. The general initialized theorem permits `D>n` and empty matrices with
  `D≥16`; the logarithmic source-regime simplification is separate. The source prime-list
  producer and Light execution are not imported. The canonical integer parameter family in
  `Algorithms/ExactTriangle/ParameterChoice.lean` uses `b=floor(log₂(n)/2394)`, `m=63b`,
  `D=4^m`, `g=4^(2b)` and `L=21m`. It reserves `D^19≤n` on positive inputs and has raw saving
  `2/1197`. `Algorithms/WordRAM/ExactTriangle/DyadicParameters/` computes these values with the
  actual logarithm and two power routines, complete charge, same-state prefix/halt and an exact
  fast/small flag. The first fast size is `2^2394`; this replaces the former 1296-bit/36b/19m
  finite regime, so old finite parameter and branch bounds are not retained by renaming alone.
  `Power/Rename.lean` exposes actual power execution on an arbitrary injective bank, reused by
  both calls. These integer parameters and their native realization are original adaptations,
  not Anthropic's fractional-root computation.
  `ParameterChoice/CostGeometry.lean` and native `ExactTriangle/DyadicCost.lean` simplify the
  actual preparation, box products, root/query/controller and genuine selector charges to a
  common `n³/g` scale. The degree-three tensor-depth coefficient and one global selected-prime
  failed-scan reserve are retained. `DyadicCost/Asymptotics.lean` absorbs the complete logarithmic
  factor, and `CallableFixedPrime/DyadicCost.lean` includes the real parameter, selector, copy,
  translated-controller and header/halt budgets in an original-scalar natural allowance.
  One coefficient and threshold per fixed original magnitude exponent give actual
  `Oκ(n^(3−33/20000))` time uniformly over matrices, selected primes, reference memories and
  physical widths. The allowance ceiling is proof metadata, not a runtime instruction or oracle.
  `Algorithms/WordRAM/ExactTriangle/ParameterSelecting/` supplies one640-register actual
  fast/small program. The host0–6 ABI restores0–5 and returns Boolean6; input is raw n,F and
  three canonical-signed arrays with computed pointers. `ThreeSum.Host.Slow.exec_at` reuses
  the exhaustive code under individual span bounds. `CallableFixedPrime.exec_at` separates
  semantic execution from final-data boundedness; `exec` retains its initial boundedness premise
  for that stronger conclusion. Unused old words do not restrict semantic correctness; their
  raw P remains explicit in caller prefix-resource theorems. Initialized logarithmic admission
  and polynomial every-wide words/support are derived from original inputs.
  The canonical `StreamingFixedPrime` and `CallableFixedPrime` are the actual box-backed implementations;
  retired `Box`-prefixed families and their conservative alternatives are removed. The complete
  ordinary 1.9992 composition is described above. The native ET2.99835 bound does not claim the
  sharper source ET2.9983 exponent or its separate Light/signed-modular machine predicate.
  `Algorithms/ExactTriangle/{Splitting,Witnesses}.lean` adapts the complete finite splitting and
  witness recovery component ([#1447](https://github.com/cslib-community/complexitylib/issues/1447)),
  using the existing matrices, lopsided graph and `Set.EqOn` answer API. Computable integer parameters
  retain the source's exact real floor/ceiling specifications through checked bridges.
  `Algorithms/WordRAM/ExactTriangle/` implements the complete initialized preparation component
  ([#1532](https://github.com/cslib-community/complexitylib/issues/1532)). Fixed sixty-four-register
  code of at most 641 flat instructions consumes raw `(D,g,n,p)` headers and signed-encoded
  A–B, B–C and A–C weights. It computes the residue classes, query chunks and records and writes
  both padded instance matrices. These matrices contain raw unsigned zero/one words; a signed
  product consumer must charge their conversion. The supplied positive modulus is not selected
  by this program. In the source regime `16 ≤ D ≤ n`, `1 ≤ g` and `p` in the square-root prime
  window, actual initialized execution including halt costs at most `690n²Dg`. Every sufficiently
  wide physical machine has the same output. Under `D,g,p ≤ n` and input magnitudes bounded by
  `(n+2)^κ`, sufficient width is at most `(κ+18)clog₂(n+2)`, and every prefix's words and address
  support are bounded by `(n+2)^(κ+19)`. The generic width and signed-fit topic modules are reused
  unchanged from #1537 and #1552. These are actual execution and fit proofs, without supplied
  layout, execution or solver contracts. This preparation contract is consumed by the product
  and complete native endpoint described below; it does not itself select the prime or solve ET.
  `Algorithms/MatrixMultiplication/Schonhage/` adapts the tensor-recursion core from the same pin's
  `Sec2/{Lemma6,Recursion,Lemma7_8,Lemma10}.lean`: the ten-term polynomial identity with explicit
  error, full evaluation, shared encodings, pruned values, visited leaves and passed-set totals.
  Its pure finite recursion traces are not native machine semantics or charged instruction costs.
  The zero-depth empty-query root exception is explicit, with an unconditional root-or-leaf API.
  See [#1459](https://github.com/cslib-community/complexitylib/issues/1459). The complete finite
  thin-product component ([#1463](https://github.com/cslib-community/complexitylib/issues/1463))
  adapts `Sec2/{Levels,Lemma9,Tiling,Orders,Lemma11,Theorem5}` and needed finite magnitude bounds.
  Layouts contain only indexing choices, whose existence is proved; sparse bounds are derived
  from exact contributing-leaf counts. Generic function-position counts, ordered gluing, binomial
  and finite-sum bounds live in small Foundations modules. Mathlib `Finset.orderEmbOfFin` indexes
  both a level set and its complement, and `Finset.piecewise` restricts answers. No source machine,
  problem-statement universe or solver/time hypothesis is imported.
  The existing signed and unsigned APIs were reused; no source machine or separate run semantics were copied.
  The ordinary host retains its parametric `Host.Callee` interface and exhaustive reference
  instance. The canonical automatic ET callee and complete native 1.9992 composition are proved
  as described above, with integration tracked in
  [#1394](https://github.com/cslib-community/complexitylib/issues/1394). Anthropic's copyright and
  attribution are retained; native proofs and representation choices are local.
* **Finite Section 4 boxes.** The cube/box prerequisite ([#2160](https://github.com/cslib-community/complexitylib/issues/2160))
  adapts `Sec4/{Boxes,Lemma27_28,BoxesFromLeaves,Lemma29}` at the same formal-math pin,
  preserving Anthropic's credit and reusing the existing terms, encodings, signed leaf order
  and alpha/beta counts. Cubes fix terms or admit every term at a star; boxes additionally
  constrain the star/P0 count and ordering. Output boxes partition exactly the high-order
  contributing leaves; low-order products remain explicit in the signed sum identity.
  The finite value recurrence recomputes children and is not a memoized native data structure.
  Its count bound needs only `m ≤ L` and `t ≤ m`, weakening the source's `10*m ≤ L` premise.
  The reusable initial-subset argument is generalized to arbitrary linear orders in the small
  Mathlib-intended `Foundations/Data/Finset/Lowest` topic module, used by the canonical boxes.
  The native compact-table, query and complete 1.9992 pipeline below consume these finite facts;
  this prerequisite alone is not a runtime theorem. No curated abstract changes are needed.
* **Native shared box tables.** The original native representation in
  [#2176](https://github.com/cslib-community/complexitylib/issues/2176) reuses the finite boxes
  and value recurrence above. A one-time directory over `(m-t+1)*10^L` slots computes compact
  ranks and three-word descriptors. Per-tile code writes one signed value per box, reading
  only earlier child ranks; lookup reads those stored words. This replaces the primary
  source's per-tile relative-pointer trie, not its mathematical box notion. Native level zero
  remains least significant, matching the existing encoders; the source's Horner numbering
  must not be substituted silently. Shared setup is at most `64*(L+1)^2*10^L` for `m ≤ L`,
  each tile costs at most `328*B+8`, and valid lookup at most `18*L+32`, with the actual box
  count `B`. The routed native composition below charges setup, resident geometry and retained
  tile storage explicitly; this table component alone does not establish the complete endpoint.
  `Foundations/Data/{Finset/LowestMax,Nat/RadixUpdate}` hold the small general ordered-subset
  and radix-update facts used by these concrete clients. No curated abstract or rendering
  changes are needed for this native data-structure prerequisite.
* **Native sparse box query.** [#2203](https://github.com/cslib-community/complexitylib/issues/2203)
  reuses the finite `starBelow` partition and actual compact table above. A five-word native
  task stack enumerates only prefixes of contributing leaves with order at most `t`.
  Full leaves below the threshold multiply the original signed words; threshold leaves
  compute the canonical box key and load its stored signed value. Finite frontier mass
  and potential proofs charge actual expansion, stack traffic, dispatch and signed sums:
  the reusable query costs at most `258*(L+1)*Σ(d≤t) alpha(m,d)+28` instructions.
  This prefix traversal is an original alternative to `Sec4/Theorem30`'s bounded-nine-string
  successor and per-tile trie at the same pinned formal-math source. It preserves the
  existing bilinear expression, not the source trace or time contract. Level zero remains
  least significant and the inner `P0` digit is nine. Actual initialized preparation,
  same-witness prefix/halt and outside frame are proved; a logarithm of original magnitudes
  and addresses admits all wider machines, with an independent-width polynomial envelope
  for every prefix. Shared table setup and retained storage remain explicit. The following
  routed-product component supplies all-tile reuse and actual routing; the complete ordinary
  composition is described above. This query milestone changes no curated abstract or rendering.
* **Routed native box product.** [#2314](https://github.com/cslib-community/complexitylib/issues/2314)
  reuses the existing actual raw-coordinate router, shared band producer and original-order
  reconstruction. One native geometry construction serves all tiles; each actual retained-value
  table and sparse query batch is charged, including temporary-result copies and every repeated
  request occurrence. An appended ordinary threshold is read before low-memory reuse and restored
  with all original input words. No computed layout, routing, encoding, table, run or time oracle
  is supplied. The original native controller preserves the existing source terms and numbering.
  The finite `BoxTradeoff` modules adapt the Section 4 geometric-tail and weighted-binomial
  estimates at the same formal-math pin, with an original algebraic block specialization
  `L=189k`, `m=9k`, `t=k`. Under `D^18≤N` and `Q*2^m≤N²`, the complete actual ledger has
  finite `D^(-8/125)` saving with polynomial depth factors explicit. Here `Q` counts occurrences,
  strengthening distinct-set sparsity when inputs repeat. Exact integer comparisons replace
  analytic numerical approximations. Canonical `StreamingFixedPrime`, `CallableFixedPrime` and
  `ParameterSelecting` compose the actual ET and ordinary 1.9992 endpoint described above.
  No curated abstract or rendering changes.
* **Callable box products and actual ET records.**
  [#2335](https://github.com/cslib-community/complexitylib/issues/2335) translates the full routed
  box product with the existing native memory-window compiler. Original dimensions derive a
  polynomial virtual window and logarithmic physical admission; no bounded-scratch or source-fit
  oracle is supplied. Two real instructions extend final normalization to the appended threshold.
  Actual setup, translations, input/answer normalization and halt retain the finite `D^(-8/125)`
  bound with explicit depth factors. The new record consumer reuses actual decoding/copies,
  executes sixteen changed level/length/threshold instructions, and calls that compiled product.
  Its initialized client runs the genuine original-weight producer and selects an occupied record;
  readbacks and occurrence sparsity are conclusions of that execution. General correctness uses
  `L=21*m` and `t=m/9`; the quantitative specialization requires `m=9k`. The complete per-record
  finite saving charges adapter and halt, with producer work separate. Canonical `StreamingFixedPrime`
  performs the complete record traversal, and `ParameterSelecting` supplies actual parameters
  and prime selection for the 1.9992 ordinary composition. Curated abstracts are unchanged.
* **Native pruned-query evaluator.** The explicit-stack pruned-query evaluator ([#1526](https://github.com/cslib-community/complexitylib/issues/1526))
  is original native code, reusing the finite `Pruned.result`, `childSet` and trace/leaf
  quantities from `Sec2/Lemma10.lean`. `PrunedQuery.queryIndex` directly applies the existing
  encoder `leafIndex` to `privateLeaf`; its executable output dictionary retains digit nine
  for the inner wildcard. Fixed 96-register code computes child lists by actual digit tests,
  division and timestamp deduplication, scans requested cells only, and charges the full stack,
  signed kernels and reporting. Its complete initialized runs and callable pointer/epoch kernel
  have explicit source-magnitude, address and outside-frame contracts. The actual bound including
  halt is `8192*(L+Q+1+(L+1)*|leaves(requested queries)|)`. The source Light implementation's
  semantics and instruction constants are not reused.
  Native wanted-query routing ([#1561](https://github.com/cslib-community/complexitylib/issues/1561))
  uses actual count, prefix and stable-scatter passes after computing the subset table and each
  query's tile/code. It reuses `MaskTable.layout`, `outStrOfPos`, `wantedStrings` and the existing
  `PrunedQuery.queryIndex`/encoder leaf order; no parallel layout or output-string universe is
  added. Primitive counts use Mathlib's `Nat.count` and its prefix/monotonicity APIs directly.
  The generic `CountingSort` topic module adds stable positions, their permutation and
  bucket-span meaning, without redundant count/offset definitions. The narrow `WordRAM.Sequence`
  proof module reassociates existing
  structured execution derivations without changing code or charges. Original scalar headers
  and raw coordinate pairs are the entire initialized input. Fixed 96-register standard code
  computes all tables and grouped arrays, preserves the original input/outside frame, and
  charges at most `128*(L+1)*(Q+numBands²+2^L+1)` instructions including halt. Its positive
  ceiling-logarithmic admission threshold depends only on the original numerical budget.
  Within-tile order is stable input order; no sorted or duplicate-free query premise is needed
  by the pruned kernel.
  The band catalogue retains the same leaf ordering and canonical signed words.
  Native queried-product composition ([#1581](https://github.com/cslib-community/complexitylib/issues/1581))
  now connects those actual programs. It computes all protected buffers and tile arguments,
  calls the shared encoders and pruned pointer/epoch kernel, and reconstructs every requested
  `Matrix.mul` value in original order, retaining duplicates. Original signed matrices and raw
  coordinate pairs are the entire initialized input. Raw nonnegative mode actually doubles
  every matrix word before signed encoding, covering the raw 0/1 producer ABI. Copies,
  header adaptation, one directory initialization, dispatch, epochs, reporting and restoration
  are all charged. Existing `MaskTable.layout`, `wantedStrings`, `encodingL/R`, leaf numbering,
  `Pruned.result` and stable-position meanings are reused; the existing `Wanted.tileKey_eq_iff`
  lemma is exposed for the concrete tile-correctness proof without changing its statement.
  The fixed 160-register program has at most 32768 flat instructions including halt and reads
  no physical-width instruction. At `L=19m`, `D=4^m`, `D^18≤N`, `Q*2^m≤N²`, the complete charge
  including halt is `4325376*(19m+1)*N²/D^(1/18)`. Distinct-set sparsity retains an additive
  occurrence charge instead. The sufficient physical width is `128*clog₂(N+Q+A+2)`; its
  magnitude/address budget and allocation have explicit polynomial envelopes in the original
  dimensions, request count and entry bound. These are original native execution/resource
  proofs, not a transfer of source Light semantics or instruction constants. This reusable
  pruned product does not itself compose the full ET/3SUM algorithm; the canonical improved
  box-backed 1.9992 pipeline is described above.
  Caller-safe queried products ([#1618](https://github.com/cslib-community/complexitylib/issues/1618))
  rebase actual memory accesses above a runtime caller base. The generic `WordRAM.MemoryWindow`
  compiler charges an addition/load/remainder for each load and an addition/store for each
  store, reusing ordinary native `Exec` and `Code`. Its clipped-memory view permits dirty
  workspace without bulk initialization; it is a value relation, not independent run semantics.
  The original product program is unchanged. Existing `NatClog` (the exact module already
  landed in #1469) and `WordRAM.Power` compute the source modulus from original counts; fixed
  register normalization and two `WordRAM.ArrayNormalize` span loops are actual charged code.
  The callable raw-zero/one thin-regime client uses 163 registers and at most 131072 flat
  instructions. It restores local input, returns exact product words at an absolute pointer,
  preserves the caller outside its window, and retains the original charged raw-to-signed
  doubling. At `D=4^m`, `L=19m`, `D^18≤N`, its standalone charge including halt is at most
  three times the original product charge plus `2048*(N*D+Q+1)`. Distinct-set sparsity retains
  the additive occurrence charge; `Q*2^m≤N²` gives `17301504*(19m+1)*N²/D^(1/18)`.
  The window is at most `(2*(N+Q+3))^128`; this deliberately large polynomial address-space
  reservation is not a claim about a tightly packed physical allocation. Every width at least
  `256*clog₂(base+N+Q+P+5)` suffices for initialized callers with prefix words bounded by `P`.
  The arbitrary dirty-caller interface uses `P` to bound every initial register and memory
  word, including words loaded before the actual remainder; native prefix bounds then follow
  from that derived physical admission. Initialized scratch is zero, so its `P` only needs
  to bound the protected caller prefix. The generic compiler theorem remains separate from
  the concrete thin-geometry admission and saving.
  The real ET-record/matrix/query adapter is tracked in
  [#1626](https://github.com/cslib-community/complexitylib/issues/1626). Its fixed 320-register
  native code computes the selected record address, reads all six fields, recovers the exact
  `4^m` exponent with existing `NatLog`, stores local original headers and copies the two raw
  matrices and interleaved occurrence coordinates above the actual producer heap. Raw zero/one
  words are copied unchanged; the callee's existing loop performs charged signed doubling.
  The complete 163-register callable bank is renamed together, preserving the producer's low
  64 registers. Memory relocation uses the real callable compiler, never register renaming alone.
  `PreparationInput.exec_input` exposes the existing structured initialized derivation so real
  caller code can compose it. Its private fit proof stays private; existing `runs_input` reuses
  the new rule with unchanged statement, assumptions, exact readback and halt-inclusive budget.
  The first-record initialized client supplies no layout/run/time/fit/solver certificate;
  actual producer readback derives all source pointer ranges and coordinate meanings, and
  actual chunk counts derive occurrence sparsity. The general caller supports every occupied
  record ordinal. The per-record charge including halt is at most three times the original
  product plus `4096*(nD+Q+1)`, or `34603008*(19m+1)*n²/D^(1/18)` under the admitted geometry.
  The original producer word bound supplies caller `P` and heap placement; the complete wider
  initialized prefixes have a positive logarithmic width threshold and polynomial words/support
  independent of physical width. The canonical fixed-prime controller, automatic selection
  and ordinary composition above supply the complete native endpoint beyond this record API.
  The original-weight consumer in
  [#1639](https://github.com/cslib-community/complexitylib/issues/1639) composes actual producer,
  product and verification code in 400 registers. It reads original interleaved pairs, computes
  the piece interval with the native square-root kernel, and invokes the entire renamed
  32-register signed verifier only while searching and on nonzero actual answers. The native
  scan counter is at most existing finite false positives plus the returned 0/1 flag. Thus a
  failed record has no additive successful-scan charge. Caller memory outside the original
  product window and the complete producer bank are framed; widths and all-prefix words/support
  are derived from original headers/weights at every sufficiently wide physical word size.
  Source Light semantics and costs are not imported or simulated by assumption. The native
  verifier returns its last zero, while finite `scanPiece` returns its first; failure and
  original-weight soundness agree. The existing decoded queries now expose chunk membership,
  nonrepetition and rank order, with an actual initialized client. The general raw writer bound
  is placed at `WriteMatrices.entry_le_one`, and shared finite piece coordinates are in the
  narrow `ExactTriangle.PieceBounds` module, reused by preparation and recovery. The canonical
  ET controller and parameter selector supply the complete native endpoint described above;
  this verification component changes no curated abstract.
  The bounded fixed-prime continuation developed in
  [#1662](https://github.com/cslib-community/complexitylib/issues/1662) is now the canonical
  box-backed `StreamingFixedPrime` controller ([#2341](https://github.com/cslib-community/complexitylib/issues/2341),
  [#2498](https://github.com/cslib-community/complexitylib/pull/2498)). It computes the catalogue
  once and constructs/consumes each logical record in one reused physical slot in a fixed
  416-register program. The materialized fixed-prime execution API is retired; the independent
  `Instances` producer and record product/witness APIs remain. A derived standalone output
  indexes mathematical accounting, without claiming producer execution for the stream. Distinct
  record/query occurrences inject into global `failedScans`; actual total scans satisfy
  `S≤F(p)+returnedFlag`, with only one successful-return flag. At `m=9k`, aggregate box work is
  at most `125829120*(189k+1)^2*(9k+1)*D^(-8/125)*n³*g`. One-time `690n²Dg` preparation,
  root/query/controller work, one global failed-scan reserve and halt remain explicit.
  `CallableFixedPrime` adds actual original-array copy/sum, computed-width setup, memory-window
  translation and return copies while preserving the selector bank and caller frame
  ([#2355](https://github.com/cslib-community/complexitylib/issues/2355)). Original-input
  logarithmic admission and polynomial every-wide prefix words/support cover this actual code.
  The source Light host uses piece-major rounds and per-round matrix construction; the native
  producer prepares a chunk-major catalogue once and later products stop after success.
  No source-trace equivalence or Light simulation is assumed. Canonical parameter/prime
  selection and the ordinary 1.9992 composition are proved as described above; integration
  remains tracked under #1394. No selected abstract is changed.
  Stage `exec_*` lemmas are internal implementation APIs exported across proof modules;
  callers use the flat initialized runs, width theorem or pointer/epoch kernel. The narrow
  `WordRAM.ArrayAppend` and `WordRAM.InputArray` topic modules keep append/input dependencies
  and interface changes away from the widely imported `Allocation` core.
  Post-integration [#1553](https://github.com/cslib-community/complexitylib/issues/1553) replaces
  pruned `powers` with five retained constant initializations (`powerSetup`) followed by
  `Power.program.rename powerRegisters`, preserving the `4L+10` step bound and `PowersLocal`
  frame, and replaces `BandPreparation.rootCode` with `NatSqrt.program.rename rootRegisters`
  followed by `square ← root * root` (`5*sqrt(k)+8` steps). `ChanHe.Parameters.power` retains
  its compile-time fixed-exponent unrolling (`κ+1` straight-line instructions over `magnitude`
  and `base` without a runtime exponent/counter register or `Fits w (κ+1)` premise at `n=0`),
  and `Encoding.setup`/`powerBody` retains its simultaneous `7^L`/`10^L` loop sharing `stage`.
* **Typed RAM upstream core.** [CSLib #1158](https://github.com/leanprover/cslib/pull/1158) at
  `beea60a15eddc91d93e92fa5af9fb965c351d0d5` proposes
  `Cslib/Computability/Machines/RAM/Basic.lean`, in namespace `Cslib.RAM.Typed`.
  This redesigns the local WordRAM/GenericRAM core with a register and word-addressed memory bank
  per sort, `Fin (2 ^ w)` words, and absorbing halt/fault states. A halt retains the data without
  choosing an output register; `RelSeries` run paths permit terminal padding. Before migrating
  local clients, bridge their operation bases, input/output conventions and exact halting costs.
  Algorithms, interpretation transfer, native simulations and time-class APIs remain separate
  follow-ups. The existing local modules remain candidates, not copies of this submission.
* **Encoded sparse memory.** `Computability/GenericRAM/SparseMemory/*` reuses Mathlib's `AList`
  with constant value type and the existing native `ComputableTidilyInO` equality, find and filter
  routines. Its certificates expose actual native TM witnesses, parameterized time/space bounds,
  and polynomial-time corollaries, and feed the fixed-program step and whole-run simulators in
  `GenericRAM/Simulation/{Turing,Run}` (#298, #292).
* **Stateful algorithms prototype.** `DataStructure/StateTransition.lean` and
  `DataStructure/StateTransition/*` reuse Quang Dao's merged
  `PFunctor.FreeM` for adaptive clients and substitution, adding persistent representation
  simulation, interface composition, semantic Hoare rules and separate native-resource
  certificates. Its queue and reset-and-replay constructions deliberately count backend calls;
  arbitrary pure continuations do not have machine-time certificates. `CostHoare` adds client
  operation-cost contracts and separate method-budget composition. The `stateful` Aesop rules
  support these contracts. `WordRAM/Controller` adds fixed-code client refinements with charged
  preparation, control flow and final halt. `WordRAM/Function` gives separate nonuniform and
  uniform RAM function-time predicates, with named-certificate reuse by `polytime`. Arbitrary continuation
  synthesis, iterative clients and a Turing-machine simulation remain open.
  The bounded `WordRAM/Realization` foundation (#2213, under #2205) reuses the memory
  oracle and the same native `Code`/`ExecWithin` semantics. Its explicit faithful register
  encodings support all four memory queries, certified word glue, branches and uniform
  reply-dependent bind, charging local work as well as memory operations. Bounded native loops
  charge iterations even without a query. The initialized flat-program projection installs
  live inputs in `2*k+5` instructions and includes the final halt; Unit observation additionally
  writes a real zero word. Input layout, bounded words and safe domains remain explicit.
  The operation-level memory backend uses four fixed constructor bodies and the generic
  implementation interface; its delivered-argument preparation is explicit and uncharged, so
  its body bounds are not whole-client clocks. The upper local-ADT adapter reuses the existing
  initialization/locality bundle and semantic module; its argument map instantiates one global
  emitter rather than selecting code after runtime layouts. Combined cost takes the program and
  an explicit work grading, with a separately proved envelope before dropping local work.
  Certified coordinate-wise glue stages multiword results with every copy charged; Option
  values use a tag and unshifted payload, including maximal fitting words. The actual
  `Stack.Memory` size/push/pop clients reuse those rules over faithfully encoded runtime layouts,
  with visible layout/representation/spare-capacity conditions and local work 0/10/19.
  `Stack.Native` runs those three certificates through `Realization.Backend` as a native stack
  with one constant per-operation bound, and `Stack.Controller` compiles an adaptive stack client
  to one flat program through `realize`; the hand-stepped stack dispatcher survives only inside
  Chan–He traversal (`Traversal.WordStack`), which steps it with exact counts.
  The full framed queue/faithful allocation client remains separate. No abstract headline is added.
  `PriorityQueue/BinaryHeap/Native` realizes the original memory heap methods, with exact source
  state/history transport and a single code family before runtime layouts, dimensions and widths.
  Its raw interface retains the compact `3n+1` fit/local-zero domain and uses the shared linear
  clear for dirty storage; the original two-query `3n+2` allocator stays unchanged for allocated
  clients. The pure model and order lemmas retain Renfei Zhou's source credit outside `WordRAM`.
  The native Dijkstra client preserves the original adjacency-list encoding, word envelope and
  log-linear endpoint, including the actual input prefix and final halt, with one existential
  uniform factor. The old hand-stepped binary-heap execution and its fixed clock/register
  constants are retired; no reduction in source size, space or instruction count is asserted.
  The bounded two-stack queue migration landed in #2303; the generic framed/allocation/whole-client
  objectives remain open. The native Fibonacci Dijkstra consumer uses the same framed source
  interface and generic history/key/domain lemmas, retains the original nonzero heap potential,
  and reserves the original `9n+5` layout in the input's zero tail without a clearing pass. Its
  flat program retains the original word hypothesis and sharper reachable-vertex clock, pays
  actual prefix/body/halt and preserves the complete source memory/frontier. It supersedes only
  the old Dijkstra executor and fixed-640 implementation helpers, not the MinPQ-used Fibonacci
  execution core or the unresolved abstract-space contract.
  Karger–Stein's specification-law bridge (#2289) reuses the existing contraction client and
  native execution model. `LoopSegmentLaw` packages the existing finite loop segments with an
  exact observation law and strict pathwise instruction/query bounds; the two-branch recurrence
  lives at the PMF layer, and compiled cut-output transport is shared with basic Karger.
  The exact-basis abstract bridge keeps its existing compatibility statements and source.
  This refactor does not supply the later memory-oracle contraction/frame-stack realization
  under #2205 or introduce a new curated headline.
  `DataStructure/OrderedSet` and `DataStructure/OrderedSet/*` provide neutral
  optional-minimum contracts, a typed finite-set interface including deletion, and adaptive
  minimum extraction, with no tree or cost dependency. Bounded-key implementations may specialize
  insertion admissibility.
  `DataStructure/SearchTree/*` reuses Mathlib's `BinaryTree`, height and node count for an
  unbalanced ordered-set realization. Finite-set behavior, strict invariants and height-bounded
  node visits are proved, including deletion through the shared interface and adaptive clients;
  allocation, comparison implementation and client computation are excluded from that cost model.
  It is not
  a balanced tree or machine-time certificate.
  `WordRAM/Dynamic` separately connects
  fixed bounded-word operation programs and faithful memory transcripts to those contracts.
  The direct shared-heap queue realizes physical-array memory programs through one fixed
  finite Backend family and the existing dynamic certificate. Count words remain in registers;
  one native dispatcher, charged metadata copies and a scaled rear potential give uniform
  amortized instruction bounds, including halt. Initialization uses six register instructions
  from arbitrary bounded dirty data, preserving every memory cell. The original `2 * capacity`
  reservation and end-fit domain are retained. The shared register count and exchange factor are
  fixed before widths, layouts, values and clients; the removed hand-code's literal instruction
  constants are not asserted. External client computation and tag/payload delivery remain outside
  the operation-history bound; no generic stateful memory-only Backend instance is claimed.
  Coordinate placement and overlap with Srinivas's #685 and the merged #401 (`Algorithms/Lean/Query`)
  before upstream submission; #685 is not copied here. This is a prototype of composition and
  refinement, not a replacement for their query models or a general cell-probe lower-bound semantics.
* **Earlier review requests.** The withdrawn #1099–#1101 requested abstract word encodings and
  textbook sources for FP/poly, P/poly and their machine simulation. The withdrawn #869 and
  #871–#875 requested composition above configuration level; use `TransformsTapes`-style specs.
* **Realizable PAC learning.** `MachineLearning/PACLearning/Realizable` copies Shaopeng Zhu's
  #858 unchanged; drop the copy once #858 lands. The local `RealizableSample`, `ERM`,
  `FiniteClass`, `GrowthFunction`, `EpsilonNet` and `VCUpperBound` modules build on it and on the
  pinned `PACLearning.{Defs, VersionSpace, VCDimension}`. Samuel Schlesinger's lower-bound stack
  (#950, #961 merged; headline on `SamuelSchlesinger/cslib:feat/pac-learning-ehkv-headline`)
  proves the EHKV `Ω(d/ε)` bound, so it is not duplicated here; that branch's
  `error_realizable_self_eq_zero` and `optimalError_realizable_eq_zero` overlap
  `isRealizableBy_map_graph` and `IsRealizableBy.optimalError_eq_zero`, so reconcile names
  before submission. #966 would make `sampleComplexity` and `vcDim` `ℕ∞`-valued;
  `sampleComplexity_realizableDistributions_le_of_finite`,
  `sampleComplexity_realizableDistributions_le_of_hasFiniteVCDim`,
  `sampleComplexity_univ_le_of_finite` (agnostic, `AgnosticFiniteClass`) and
  `growthFunction_le_sum_choose_vcDim` will need restating if it lands.

These are coordination references, not a second record of live PR status. Check the relevant
upstream discussion before starting or submitting overlapping work.

## Placement decisions not already recorded in source

Paths below omit `Complexity/` and `.lean`. The default CSLib destination mirrors the source
path. A destination recorded in a source marker takes precedence; the alternatives below need
agreement during upstream review.

| Local module or declarations | Integration note |
| --- | --- |
| `Computability/Machines/Turing/MultiTape/Encodings/StreamFold` | The candidate `streamFold_sum` generalizes the vendored proof; `streamFold` is its compatibility corollary. When resynchronizing or removing the copy, preserve the summed contract and shared proof until upstream includes them. |
| `Computability/Machines/Turing/MultiTape/Encodings/Length` | Add to the tidy branch's `Encodings/List`. |
| `Computability/Machines/Turing/MultiTape/TapeLemmas` | `exists_visitedByTapeHead_eq_Icc` and `workTapes_runFrom_eq_of_notMem_visitedByTapeHead` were relocated from `Plumbing/Shadow` (#316); upstream with `TapeLemmas`. |
| `Computability/Machines/Turing/MultiTape/Configuration` | `Turing.Action.instFinite` was relocated from `Machine/ChoiceTable` (#354); place beside `Action` in upstream `Configuration`. |
| `Computability/Machines/Turing/MultiTape/Plumbing/ExtendTapesView` | Derive the old `tapeEmb`/`noTapes` lemmas from `viewCfg`; `oneTapeCfg i = viewCfg (tapeEmb i)` by `rfl`. |
| `Computability/Machines/Turing/MultiTape/Probabilistic/IterateWhile` | Its private tape helpers parallel the vendored deterministic `Combinators/IterateWhile`; share them once the tidy branch exposes them. |
| `Computability/Machines/Turing/MultiTape/Plumbing/TransformsTapes` | `runFrom_nop_withState` was relocated from `Combinators/TidyNormalForm` (#354); place beside `runFrom_nop_one` in upstream `Plumbing/TransformsTapes`. |
| `Computability/Machines/Turing/MultiTape/Encodings/Decoder` | Total decoders with tidy certificates; add to the tidy branch's `Encodings` beside `Option`/`Pair`/`List`. |
| `Computability/Machines/Turing/MultiTape/Encodings/NatPower` | Addition to the tidy branch's `Encodings/Nat`: `encNat (2 ^ n)` and its linear clock certificate. |
| `Computability/Circuit/{Unfolding,MapOp}`, `Computability/Circuit/Encoding/MapOp` | Consider integrating into `Circuit/Formula`, `Circuit/Program`, and `Circuit/Encoding`, respectively. |
| `Computability/Circuit/Boolean/FirstOrder` | Consider a descriptive-complexity directory. |
| `Foundations/Data/BitString/{Agree,Block}` | Add to CSLib's `Foundations/Data/BitString`. |
| `Foundations/Data/List/{Fold,Lookup,Counting,Append}` | Fold invariants, lookup and register-file bounds, predicate counts, and append identities including unary headers; `Basic` reexports these topics. Consider Mathlib's `Data/List/GetD` and `Data/List/Basic`. |
| `Foundations/Relation/RelatesWithinSteps` | Bounded reachability helpers; consider Mathlib's `Logic/Relation`. |
| `Foundations/MeasureTheory/Measure/TotalVariation/Map` | Mathlib candidate beside `Measure/TotalVariation/Defs`: measurable-map contraction for the existing full-L1 distance of finite measures, including unequal masses. Derived from vector-measure variation; no new distance definition. |
| `Foundations/MeasureTheory/Measure/TotalVariation/Mixture` | Mathlib candidate beside `Measure/TotalVariation/Defs`: finite-sum bounds and exact nonnegative scaling for canonical full-L1 distance, combined into a component-and-weight mixture bound for arbitrary finite measures. Uses signed-measure variation without new distance or mixture definitions. |
| `Foundations/Probability/Gaussian/Standard` | Mathlib candidate beside `Probability/Distributions/Gaussian/Multivariate`: identifies the existing normalized Gaussian density with a scaled `stdGaussian`, then computes its actual scalar projection using characteristic-function uniqueness and the Gaussian Fourier transform. No parallel Gaussian measure definition; positive width, arbitrary projection vector and dimension zero are covered. |
| `Foundations/BooleanAnalysis/Fourier` | Consider Mathlib beside `Analysis/Fourier/FiniteAbelian`. |
| `Foundations/Algebra/Module/ZLattice/CoefficientFiber`, `Foundations/Probability/Gaussian/CoefficientFiber` | General mathematics intended for Mathlib: basis-coordinate reduction and its exact scalar-lattice fibers, followed by discrete-Gaussian mass and conditioning identities. Reuses the existing pointwise submodule action, basis equivalence, `PMF.filter` and normalization; positive composite moduli and lower-rank lattices are supported. |
| `Foundations/MeasureTheory/Group/ConvolutionDensity` | Mathlib candidate beside `Measure/WithDensity`: a convolution density formula with arbitrary s-finite first measure, including singular inputs, derived measurability and multiplicative/additive versions. Reuses existing convolution, product and density constructions; no finite-mass or integrability premise. |
| `Foundations/Analysis/Lattice/Fourier` | General mathematics intended for Mathlib beside `Analysis/Fourier/PoissonSummation`: dual-frequency character invariance and the unnormalized coefficient identity, reusing fundamental-domain unfolding. No new lattice or periodization definition. |
| `Foundations/Analysis/Lattice/{Covolume,Dual,Poisson}`, `Foundations/Probability/Gaussian/{Fourier,Poisson}` | General mathematics intended for Mathlib: basis-coordinate integrals and dual discreteness extend the existing Z-lattice APIs; arbitrary full-rank lattice Poisson reconstruction extends `Analysis/Fourier/PoissonSummation`, with Schwartz and positive-width Gaussian clients. Reuses the existing covolume, dual submodule, automorphize and torus Fourier series. |
| `Foundations/MeasureTheory/Group/QuotientDensity` | Mathlib candidate beside `MeasureTheory/Measure/Haar/Quotient`: measurable nonnegative automorphization and exact quotient-density folding, using the canonical quotient measurable space and existing fundamental-domain unfolding. No topology, integrability or finite-mass assumption. |
| `Foundations/Probability/Gaussian/{MassBounds,CenteredTail}` | Centered lattice Gaussian mass scaling and strict-radius concentration; intended for Mathlib beside the lattice Gaussian Poisson API. Reuses the existing weights, normalizers and PMF, with positive-width, full-rank and center-zero hypotheses explicit. |
| `Foundations/Probability/Gaussian/{ShiftBounds,Smoothing}` | Uniform shifted Gaussian mass control and a satisfiable quantitative dual-tail width criterion; intended for Mathlib beside lattice Gaussian Poisson and concentration. Reuses the actual dual submodule, nonzero Gaussian sum and existing normalizer. Does not define a minimum smoothing parameter. |
| `Foundations/Analysis/Lattice/QuotientMeasure`, `Foundations/Probability/Gaussian/{Measure,Quotient}` | Mathlib candidates: actual Gaussian probability normalization, covolume-normalized fundamental quotient probability and invariance, and the Gaussian quotient density/full-L1 bound. Reuses canonical `Measure.withDensity`, `Measure.map`, `automorphize`, dual mass and `tvDist`; no parallel measure definitions or minimum smoothing parameter. |
| `Foundations/Probability/Gaussian/Convolution` | Actual coset discrete-Gaussian convolution density and full-L1 bounds; intended for Mathlib beside lattice Gaussian smoothing. Reuses existing `Measure.conv`, mapped PMFs, `withDensity` and `tvDist`, with the arbitrary singular-measure convolution-density prerequisite from #2714. No minimum smoothing parameter or sampler definition. |
| `Foundations/Probability/Gaussian/Projection` | Actual scalar and canonical mod-one coset Gaussian experiment bounds from Corollary 3.10; intended for Mathlib beside lattice Gaussian convolution. Reuses the proved normalized-density projection and full-L1 map contraction, with an actual dual-mass bound or a sufficient numerical dual-gap criterion. No parallel Gaussian, circle law or smoothing-parameter definition. |
| `Foundations/BooleanAnalysis/{Bernoulli,CoordinateSampling,Fibers,HarmonicTransform,LightPatterns,MirrorSets}`, `Foundations/Analysis/HarmonicMean` | Consider Mathlib probability APIs; generic finite-type `harmonicMean` is split into `Foundations/Analysis/HarmonicMean` (#317). |
| `Foundations/BooleanAnalysis/HadamardTester` | Consider the PCP hierarchy. |
| `Foundations/Combinatorics/CentralBinomial` | Consider Mathlib's `Data/Nat/Choose/Central` (`Nat.centralBinom_sq_mul_le`) and `Combinatorics/Choose`. |
| `Foundations/Combinatorics/InclusionMatrix` | Mathlib candidate: Gottlieb's full-rank theorem for subset inclusion matrices over fields where `1, …, #U` are nonzero, with its double-counting lemmas; consider `Combinatorics/SetFamily`. |
| `Foundations/Combinatorics/{FiniteCover,Hoeffding,Hypergeometric,PowersetTail,Sunflower}` | Consider Mathlib combinatorics; probabilistic-method lemmas belong near `Combinatorics/Probabilistic`. |
| `Foundations/Data/Finset/Expect` | Product-type expectation helpers extracted from `Foundations/Combinatorics/Expander/Products` (#317); Mathlib candidates. |
| `Foundations/Data/Finset/Markov` | Mathlib candidate: `Algebra/Order/BigOperators/Group/Finset` (`Finset.card_filter_mul_le_sum`, `Finset.mul_card_filter_le_sum`). |
| `Foundations/Data/Finset/OrderGlue` | #1545 resolves the generic naming follow-up from #1496 after native bands stabilized in #1536: order-embedding/subset/complement terminology, Mathlib's `orderEmbOfFin_mem`/`range_orderEmbOfFin` and ordinary substitution in place of five redundant wrappers, and migration of finite tensor clients with checked native band clients. Retain this focused topic module. |
| `Foundations/Data/Matrix/Permanent` | Mathlib candidate: Laplace expansion of the permanent along row and column 0, beside `LinearAlgebra/Matrix/Permanent` (mirroring `Matrix.det_succ_row_zero`). |
| `Foundations/LinearAlgebra/{Rank,Matrix/CutRank,Matrix/Lindsey}` | Mathlib candidates: `LinearAlgebra/Dimension/LinearMap` and `LinearAlgebra/Matrix/Rank`; placement of Lindsey's lemma needs agreement. |
| `Foundations/LinearAlgebra/Matrix/{FourierMotzkin,Farkas,LinearProgramming,BasicSolution}` | Mathlib candidates: polyhedral Farkas' lemma and LP duality over any linearly ordered field, proved by Fourier–Motzkin elimination, and basic solutions with Cramer-rule size bounds for integer systems (`BasicSolution`). Mathlib's `ProperCone.hyperplane_separation` is topological (closed cones in real locally convex spaces, so not `ℚ`), and at the current pin `PointedCone.dual`/`DualFG` have no Farkas or Minkowski–Weyl theorem. Upstream review should decide whether to restate these as `PointedCone.DualFG`/`FG` duality. The 2023–24 LP pull requests `leanprover-community/mathlib4` 7386, 9693, 10026 and 10159 (all closed) and Dvořák–Kolmogorov's `duality` repository (`DvorakKolmogorov2024`, cited in the modules) take different approaches; nothing was vendored. |
| `Probability/PairwiseIndependentHash/Shift` | Consider integration into `PairwiseIndependentHash`. |
| `Probability/PairwiseIndependentHash/Toeplitz` | Move `Matrix.toeplitz` to Mathlib beside `LinearAlgebra/Matrix/Circulant`. |
| `Probability/ApproximateCounting/Relative` | Extract the natural-number root lemmas to Mathlib. |
| `Foundations/Data/Nat/Bits` | `Nat.foldr_bit_bits` is a candidate for Mathlib's `Data/Nat/Bits`; its local relocation is complete, but upstream integration is still pending. |

## Deprecation policy and breaking changes

From `2110aa5a` (2026-10-19), renaming, moving or removing a public declaration already on `main`
left a deprecated alias or theorem at the old full name; the sweep integrated at `7738dcea` added
aliases for the names that changed before the rule existed and restored old binder orders where
they had changed. The library supports no downstream users yet, so #587 deleted every deprecated
declaration, and such changes now update all clients in this repository instead (`AGENTS.md`,
Proof hygiene). This list records earlier changes that had no mechanical successor.

* **Signature changes under the old name.** `GeneralizedGeography.decide_mem_eq_any` became the
  more general `List.decide_mem_eq_any`; `RotationMap.le_edgeExpansion_of_spectralExpansion_le`
  takes `V` implicitly; `PolyTimeComplete` takes `{β}` before `C`; `PMF.iid_map` has the opposite
  orientation; `eval_toUnbounded_atomsOf` changed its signature.
* **Removed or made private, without a successor of the same shape.**
  - Raz–Wigderson helpers: `bobAnswer_aliceMatching`, `aliceGraph_swap_swap`, `bobGraph_swap_swap`,
    `exists_run_oneRun`, `run_oneRun_of_disjointness`, `run_oneRun_of_mem`.
  - Graph non-isomorphism: `PublicCoin.entry`, `entry_fin`, `value`, `value_fin` (use `matrixBit`)
    and `mem_orbit_self`.
  - Communication: `PublicCoin.majority` and `le_card_filter_ne_of_majority_ne` (use
    `BitString.strictMajorityOn` and `card_filter_eq_le_half_of_strictMajorityOn_ne`);
    `ecomplexity_le_succ`, `IsFoolingSet.le_ecomplexity`,
    `PublicCoin.Solves.sq_mul_two_pow_le_four_pow`.
  - Hamiltonian cycle: `SAT.rowLength`, `rowLength_sub_one`, `diamondArcs`, `literalArcs`,
    `diamondGraphArcs`, `diamondGraphVertices`, `mem_diamondGraphArcs`, `mem_diamondGraphVertices`
    (use `Diamond.graph`); `Diamond.Follows` and its lemmas are private.
  - `SAT.SparseIndependentSet.mem_clauseEdges` and `mem_variableEdges`; the eight
    `CookLevin.determined_of_mem_*` lemmas (private); `SharpSAT.getD_idxOf`,
    `getD_mem_of_isFirst`, `isFirst_idxOf`; `Crypto.le_length_encPreimagePrefix` and
    `UniformLearning.toOuterMeasure_uniformOfFintype_ne` (private);
    `UniformLearning.signVal_mul_chi_mem_Icc`.
  - Landings of 2026-10-19 before the rule: about 25 `AffineDisperser` names; the natural-proofs
    predicates `IsNatural`, `IsLarge`, `IsUseful`, `IsCircuitTest`, `truthTableGenerator` and their
    lemmas, moved into the `NaturalProof` namespace; 12 Ladner helpers (among them `boolDecoder`,
    `natDecoder`, `ofBits`, `dropFalsesT`); `BakerGillSolovay.unaryLanguage` and three lemmas.
* **Meaning strengthened under the old name.** On 2026-10-20 `Turing.MultiTapeNTM.DecidesInSpace`
  started to require that every branch halt (Sipser, Definition 8.1), so `NL` and `NPSPACE`
  follow the textbook convention. The former meaning is `Turing.MultiTapeNTM.RecognizesInSpace`
  (`DecidesInSpace.recognizesInSpace`); membership proofs now also need a per-instance halting
  bound, the second component of `DecidesInSpace` (read back with
  `DecidesInSpace.exists_runsInTime`).
* **Word-RAM operation bases.** On 2026-10-21 the word RAM became parametric in a basis of
  operations. `Cslib.WordRAM.Op`, `Instr`, `Program` and `Code` take a basis `B` before the register
  count, and `DecidableInTime`, `DecidableInTimeAt`, `LinearTime` and `PolynomialTime` take it as
  their first explicit argument; the previous instruction set is `Cslib.WordRAM.Basis.standard`.
  The constructors `Op.bin` and `Op.width` became definitions of the same names over the standard
  basis, so construction is unchanged but pattern matching, `Op.bin.injEq` and `Op.width.injEq`
  are gone (match on `Op.alu`). `Op`, `Instr` and `Code` no longer derive `Repr`. The binder `B` of
  `Exec.loop`, `ExecWithin.loop` and `ExecWithin.loop_invariant` is now `T`, and the `B : Set β`
  binder of the `recode` lemmas in `WordRAM/Time` is now `A'`; named-argument callers must follow.
  On the same date `Cslib.Circuits.Signature.Hom` and `Signature.Hom.Preserves` moved, with their
  names unchanged, from `Circuit/MapOp` to `Circuit/SignatureHom`, which `Circuit/MapOp` imports.
* **Word-RAM bases with undefined values.** On 2026-10-23 `Cslib.WordRAM.Basis.interp` became
  `Option`-valued, and an operation whose value is `none` faults. The field
  `Basis.interp_mono_of_not_readsWidth` replaces `Basis.interp_eq_of_not_readsWidth`; it only keeps
  values that fit a word.
  `Basis.Hom.preserves` is now a field of its own, an equation per word size, operation and
  arguments, rather than `Signature.Hom.Preserves`. `StandardOp.eval`, `Basis.standard_interp_bin`
  and `Basis.standard_interp_width` wrap their old values in `some`. `Op.eval_alu` now reads
  `(B.interp w f (x.regs ∘ args)).bind (x.put w d)`: an undefined value propagates, and the word
  check follows for a defined one. `Exec.alu` and `ExecWithin.alu` take the value `v` and the
  hypothesis `B.interp w f (x.regs ∘ args) = some v`. `Basis.standard` keeps its semantics; the new
  `Basis.exact` faults on `x - y` for `y > x` and on `x / 0` and `x % 0`.
* **Renamed modules.** On 2026-10-20 `Circuit/Boolean/MassProduction/{Sharp,SharpParameters,
  SharpStatement}` became `…/{Fine,FineParameters,FineStatement}`, with their `Sharp` declarations
  renamed to `Fine`. Imports of the old module paths must be updated: a module stub would have no
  upstream counterpart, so none is kept.
* **Withdrawn results of 2026-10-22 (#372).** On 2026-10-22 the maintainer withdrew results merged
  that morning without adequate correctness review, deleting them without aliases. An alias would
  keep exactly the names being withdrawn, and none of them had been submitted to cslib or used
  downstream.
  - Regev's reduction (`Crypto/Lattice/LWE.lean`, whole module) and OT completeness
    (`Crypto/Multiparty/ObliviousTransfer.lean`, whole module).
  - `ACC0.lean`: `SymPlusCompilation`, `symPlusCompilation_zero`,
    `exists_fastSymPlusEval_of_symPlusCompilation`, `exists_mem_NEXP_notMem_ACC0`,
    `not_NEXP_subset_ACC0`. The duplicate `Cslib.Circuits.Boolean.SigmaP_subset_EXP` and
    `SigmaP_subset_NEXP` were also deleted; use `Cslib.Complexity.SigmaP_subset_EXP` and
    `SigmaP_subset_NEXP`, now in `Classes/Inclusions`.
  - `IdentityTesting.lean`: `kabanets_impagliazzo`, `kabanets_impagliazzo_of_EXP_subset_P`,
    `PermPITCertified`, `exists_certified_perm_family_of_PITInt_mem_P_of_mem_VP`,
    `NEXP_eq_EXP_of_NEXP_subset_SigmaP`.
  - `Hastad.lean`: `hastadSATProb` and its three lemmas, `hastadGraphSATProb`, and
    `hastadGraphSATProb_eq_add_hastadGraphLinearCorr`. The SAT conjuncts were dropped from
    `hastadGraphProb_longCode_of_satisfies` (now `graphLinearProb_longCode_of_satisfies`) and
    `hastad_gapLabelCover_dichotomy` (now `gapLabelCover_dichotomy`).
  - The conditional sumset-extractor frontier layer (#391), whose extractor-family hypothesis was
    never discharged: `Circuit/Frontier/Extractor.lean` and `Complexity/FrontierExtractor.lean`
    (whole modules), and the decimal restatements
    `eventually_456249_div_100000_sub_mul_lt_innerSize`,
    `circuitLowerBound_456249_div_100000`, `averageCaseBound_456249_div_100000`,
    `eventually_456249_div_100000_sub_mul_lt_innerSize_of_nondeterministicDecides` and
    `eventually_456249_div_100000_sub_mul_lt_card_of_aggregates`. Combine the exact-`L` theorems
    with `Gaussian.circuitCoefficient_ge_456249` instead.
  - #392 withdrew Gentry's bootstrapping (`Crypto/Computational/Bootstrapping.lean` and
    `Bootstrapping/{HomomorphicEval,KeyChain,KeyEncryption}.lean`, whole modules), whose
    `Bootstrappable` interface assumed the content of the theorem. From the Håstad modules it
    deleted `GapExactThreeDistinctSAT`, `no_GapExactThreeDistinctSAT_eq_empty`, `xorThreeCNF` and
    its five lemmas, `hastadLinearProb_le_of_hastadLinearCorr_le` and the same-day alias
    `Cslib.PCP.Hastad.fourierCoeff_sq_signVal_le_one`. The kept long-code, folding and projection
    lemmas moved to `Cslib.BitString` in `Foundations/BooleanAnalysis/LongCode` (`IsFolded`
    became `IsOdd`), and `Hastad/ExactThreeDistinct` merged into
    `PCP/Approximation/MaxExactThreeSAT`, keeping its declaration names; imports of the deleted
    module path must be updated. `hastad_gapLabelCover_dichotomy` (now `gapLabelCover_dichotomy`)
    now chooses `η` before the label sets.
  - Follow-up #390 (same date and policy): the rest of the `ACC0.lean` Williams scaffolding,
    `SymPlusCircuit` and its API, `evalMask` and its lemmas, `zetaTransform`, `fastZeta`,
    `fastZeta_eq_zetaTransform`, `parity_mem_EXP`, `parity_mem_NEXP`,
    `exists_mem_NEXP_notMem_{AC0,AC0Mod,SIZEMod}`, `exists_mem_SIZEMod_of_mem_AC0Mod`,
    `NEXP_subset_PPoly_of_NEXP_subset_ACC0`, `PH_eq_SigmaP_two_of_NEXP_subset_ACC0` and
    `Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`; the remaining `ACC0` development is
    split into `ACC0/Basic` and `ACC0/Simulation`, and `NC_subset_PPoly`, `AC_subset_PPoly` and
    `size_majorityDeMorganCircuit_le_sq` moved to `DepthClasses`, `FanInTwo` and `ThresholdNC1`,
    all with names unchanged. The module
    `Circuit/Arithmetic/IdentityTesting` is deleted. Its Schwartz–Zippel restatements
    (`MvPolynomial.card_mul_card_roots_le`, `card_roots_le`,
    `exists_eval_ne_zero_of_totalDegree_lt_card`; use Mathlib's
    `MvPolynomial.schwartz_zippel_totalDegree`), `encArith*`, `PITInt` and its lemmas, the
    arithmetic circuit combinators, the permanent chain (`minorVar` through
    `isLaplacePermChain_laplacePermCircuit`), `intPermFamily` and `exists_mem_NEXP_notMem_SIZE`
    are deleted. `Matrix.permanent_succ_{column,row}_zero` moved to
    `Foundations/Data/Matrix/Permanent`, `Cslib.Circuits.Circuit.eval_polynomial` to
    `Arithmetic/VP`, and `permFamily`, `isPFamily_permFamily` and
    `totalDegree_permanent_genericMatrix_le` to `Arithmetic/Determinant`, with names unchanged.
* **Two multigraph namespaces.** Since 2026-10-20 the frontier multigraph
  (`Cslib.Circuits.Frontier.Multigraph`) defines its simple graph as that of the multigraph given by
  its ends (`Cslib.Multigraph`), and its module publicly imports the latter. Their shared base names
  `toSimpleGraph`, `toSimpleGraph_adj`, `edgeCut` and `mem_edgeCut` are ambiguous when both
  namespaces are visible, for example inside `namespace Cslib.Circuits.Frontier` or with both
  opened; use dot notation (`G.toSimpleGraph_adj`) or full names. Upstreaming the frontier
  multigraph therefore follows `Foundations/Combinatorics/Multigraph.lean`.

The [historical ledger](https://github.com/cslib-community/complexitylib/blob/d0e6373970029a91018528463ca7a5ccd0fc9fd1/UPSTREAM.md)
preserves earlier integration notes and per-module follow-up ideas.

* **Word-RAM word-size contracts (2026-10-22).** Time and encoding arguments now depend on
  word size, and an ordinary predicate `allowed : α → ℕ → Prop` admits input/width pairs.
  `WordSizeDependentProgram` selects code only by width; the primary decision and function classes
  require a fixed register count and uniformly bounded instruction-list length.
  `Uniform` variants retain one fixed program,
  which may read the width. Existing fixed-code clients prove the uniform variants and can
  forget uniformity. The `LogWord` wrappers express the transdichotomous assumption, require a
  positive constant, and remain conditional on input fitting. Asymptotic time keeps correctness
  at every admitted fitting input
  and makes only the runtime estimate eventual, with constants shared by all widths. Width
  schedules connect to Mathlib's real-valued big-O after casting. No effective selection of code,
  width or encoding, or Turing-machine complexity identification, follows. These breaking local
  API changes intentionally retain no deprecated aliases, as authorized by Erik for this redesign.
