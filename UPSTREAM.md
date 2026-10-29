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
  retain the source's exact real floor/ceiling specifications through checked bridges. The existing
  signed and unsigned APIs were reused; no source machine or separate run semantics were copied.
  Tensor/sparse query programs, the full reduction host, native Chan–He preprocessing, fast Exact
  Triangle and full input/time/width/asymptotic composition remain in
  [#1394](https://github.com/cslib-community/complexitylib/issues/1394), including the improved
  Section 4 route needed for the published exponent 1.9992. Anthropic's copyright and attribution
  are retained; the native proofs and representation choices are local.
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
* **Stateful algorithms prototype.** `Foundations/Semantics/Stateful/*` reuses Quang Dao's merged
  `PFunctor.FreeM` for adaptive clients and substitution, adding persistent representation
  simulation, interface composition, semantic Hoare rules and separate native-resource
  certificates. Its queue and reset-and-replay constructions deliberately count backend calls;
  arbitrary pure continuations do not have machine-time certificates. `CostHoare` adds client
  operation-cost contracts and separate method-budget composition. The `stateful` Aesop rules
  support these contracts. `WordRAM/Controller` adds fixed-code client refinements with charged
  preparation, control flow and final halt; the adaptive stack example constructs its empty
  representation from the standard input. `WordRAM/Function` gives separate nonuniform and
  uniform RAM function-time predicates, with named-certificate reuse by `polytime`. Arbitrary continuation
  synthesis, iterative clients and a Turing-machine simulation remain open.
  `Foundations/Data/OrderedSet` and `Foundations/Semantics/Stateful/OrderedSet` provide neutral
  optional-minimum contracts, a typed finite-set interface and adaptive clients, with no tree or
  cost dependency. Bounded-key implementations may specialize insertion admissibility.
  `Algorithms/Lean/SearchTree/*` reuses Mathlib's `BinaryTree`, height and node count for an
  unbalanced ordered-set realization. Finite-set behavior, strict invariants and height-bounded
  node visits are proved, including for the pure deletion operation `erase`; allocation,
  comparison implementation and client computation are excluded from that cost model. It is not
  a balanced tree or machine-time certificate.
  `WordRAM/Dynamic` separately connects
  fixed bounded-word operation programs and faithful memory transcripts to those contracts.
  The direct shared-heap queue uses the existing FIFO operation signature and native operation
  traces, with a hidden two-stack representation, a concrete-register potential, framed storage,
  and separately charged initialization. Its `2 * capacity` reservation is explicit; external
  client computation and argument delivery are not charged by the operation-history bound.
  Coordinate placement and overlap with Srinivas's #685 and the merged #401 (`Algorithms/Lean/Query`)
  before upstream submission; #685 is not copied here. This is a prototype of composition and
  refinement, not a replacement for their query models or a general cell-probe lower-bound semantics.
* **Earlier review requests.** The withdrawn #1099–#1101 requested abstract word encodings and
  textbook sources for FP/poly, P/poly and their machine simulation. The withdrawn #869 and
  #871–#875 requested composition above configuration level; use `TransformsTapes`-style specs.

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
| `Foundations/BooleanAnalysis/Fourier` | Consider Mathlib beside `Analysis/Fourier/FiniteAbelian`. |
| `Foundations/BooleanAnalysis/{Bernoulli,CoordinateSampling,Fibers,HarmonicTransform,LightPatterns,MirrorSets}`, `Foundations/Analysis/HarmonicMean` | Consider Mathlib probability APIs; generic finite-type `harmonicMean` is split into `Foundations/Analysis/HarmonicMean` (#317). |
| `Foundations/BooleanAnalysis/HadamardTester` | Consider the PCP hierarchy. |
| `Foundations/Combinatorics/CentralBinomial` | Consider Mathlib's `Data/Nat/Choose/Central` (`Nat.centralBinom_sq_mul_le`) and `Combinatorics/Choose`. |
| `Foundations/Combinatorics/{FiniteCover,Hoeffding,Hypergeometric,PowersetTail,Sunflower}` | Consider Mathlib combinatorics; probabilistic-method lemmas belong near `Combinatorics/Probabilistic`. |
| `Foundations/Data/Finset/Expect` | Product-type expectation helpers extracted from `Foundations/Combinatorics/Expander/Products` (#317); Mathlib candidates. |
| `Foundations/Data/Finset/Markov` | Mathlib candidate: `Algebra/Order/BigOperators/Group/Finset` (`Finset.card_filter_mul_le_sum`, `Finset.mul_card_filter_le_sum`). |
| `Foundations/Data/Matrix/Permanent` | Mathlib candidate: Laplace expansion of the permanent along row and column 0, beside `LinearAlgebra/Matrix/Permanent` (mirroring `Matrix.det_succ_row_zero`). |
| `Foundations/LinearAlgebra/{Rank,Matrix/CutRank,Matrix/Lindsey}` | Mathlib candidates: `LinearAlgebra/Dimension/LinearMap` and `LinearAlgebra/Matrix/Rank`; placement of Lindsey's lemma needs agreement. |
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
