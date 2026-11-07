# Model map

This maintained map contains **265 curated entries** from the November 2 survey across four areas. Entries include models, behavior-changing variants, resource predicates and semantic interfaces; they are not asserted to be mathematically independent models. Follow each entry to the chapter explaining its semantics, resources, declarations, results and limitations. The optional [index script](data/coverage.py) exports these table rows; it does not discover models or reconstruct semantic judgments.

The [module census script](data/census.py) can enumerate every tracked Lean source file at the fixed snapshot. Its broad ownership assignment is an indexing aid, not a claim that every line was reviewed. Model-family completeness remains a semantic judgment; generated inventories are optional and untracked.

## Machines and classes

[Section overview](machines-and-classes/index.md).

| ID | Model or interface | Family |
|---|---|---|
| `native-parametric` | [Parametric multitape choice/oracle machine](machines-and-classes/native-and-resources.md) | native |
| `native-deterministic` | [Deterministic multitape TM](machines-and-classes/native-and-resources.md) | native |
| `native-nondeterministic` | [Set-branching multitape NTM](machines-and-classes/native-and-resources.md) | native |
| `native-probabilistic` | [Fair-coin multitape PTM](machines-and-classes/native-and-resources.md) | native |
| `native-counting` | [List-branching counting TM](machines-and-classes/native-and-resources.md) | native |
| `native-alternating` | [Binary alternating multitape ATM](machines-and-classes/native-and-resources.md) | native |
| `oracle-ppt` | [Native stateful oracle-PPT realization](machines-and-classes/native-and-resources.md) | native-oracle |
| `raw-resource-transducer` | [Independent time/workspace transducer](machines-and-classes/native-and-resources.md) | resource |
| `charged-resource-transducer` | [Output-charged compositional space](machines-and-classes/native-and-resources.md) | resource |
| `function-time` | [FTIME encoded function class](machines-and-classes/native-and-resources.md) | resource |
| `logspace-transducer` | [Output-uncharged logarithmic-space transducer](machines-and-classes/native-and-resources.md) | resource |
| `rl` | [RL randomized logspace](machines-and-classes/native-and-resources.md) | resource |
| `bpl` | [BPL randomized logspace](machines-and-classes/native-and-resources.md) | resource |
| `step-machine` | [StepMachine](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `read-machine` | [ReadMachine](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `query-machine` | [QueryMachine](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `nondeterministic-query-machine` | [NondeterministicQueryMachine](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `counter-program` | [Finite natural-register CounterProgram](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `nondeterministic-counter` | [Nondeterministic counter interpretation](machines-and-classes/intermediate-and-legacy.md) | intermediate |
| `single-tape` | [cslib SingleTapeTM](machines-and-classes/intermediate-and-legacy.md) | legacy |
| `tm0` | [Mathlib Post-style TM0](machines-and-classes/intermediate-and-legacy.md) | legacy |
| `tm1` | [Mathlib structured tape TM1](machines-and-classes/intermediate-and-legacy.md) | legacy |
| `tm2` | [Mathlib finite-stack TM2](machines-and-classes/intermediate-and-legacy.md) | legacy |
| `partrec` | [Mathlib partial-recursive codes](machines-and-classes/computability-and-description.md) | computability |
| `native-universal` | [Encoded native universal interpreter](machines-and-classes/computability-and-description.md) | computability |
| `native-total` | [Native total computability and decidability](machines-and-classes/computability-and-description.md) | computability |
| `description-method` | [Abstract DescriptionMethod](machines-and-classes/computability-and-description.md) | description |
| `partrec-description` | [Partrec universal description method](machines-and-classes/computability-and-description.md) | description |
| `tm-description` | [Described-machine-clock Kolmogorov model](machines-and-classes/computability-and-description.md) | description |
| `conditional-description` | [Conditional description and composition](machines-and-classes/computability-and-description.md) | description |
| `blum-measure` | [Blum complexity measures over Mathlib partial-recursive codes](machines-and-classes/computability-and-description.md) | computability |
| `np-verifier` | [Exact-length NP witness verifier](machines-and-classes/verifiers-counting-interaction.md) | verifier |
| `alternating-verifier` | [PH witness blocks and alternating games](machines-and-classes/verifiers-counting-interaction.md) | verifier |
| `bpp-verifier` | [BPP uniform-seed verifier](machines-and-classes/verifiers-counting-interaction.md) | verifier |
| `rp-verifier` | [RP one-sided seed verifier](machines-and-classes/verifiers-counting-interaction.md) | verifier |
| `zpp-verifier` | [ZPP Option Bool trials](machines-and-classes/verifiers-counting-interaction.md) | verifier |
| `sharp-p` | [#P witness count](machines-and-classes/verifiers-counting-interaction.md) | counting |
| `gap-p` | [GapP signed count](machines-and-classes/verifiers-counting-interaction.md) | counting |
| `pp` | [PP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `parity-p` | [ParityP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `mod-p` | [ModP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `ceq-p` | [CeqP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `up` | [UP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `few-p` | [FewP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `us` | [US](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `spp` | [SPP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `wpp` | [WPP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `lwpp` | [LWPP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `awpp` | [AWPP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `sbp` | [SBP](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `bpppath` | [BPPpath](machines-and-classes/verifiers-counting-interaction.md) | counting-acceptance |
| `deterministic-oracle` | [Efficient deterministic oracle program](machines-and-classes/verifiers-counting-interaction.md) | oracle-verifier |
| `counting-oracle` | [#P function-bit oracle](machines-and-classes/verifiers-counting-interaction.md) | oracle-verifier |
| `ma` | [Merlin-Arthur verifier](machines-and-classes/verifiers-counting-interaction.md) | interactive |
| `am` | [Arthur-Merlin verifier](machines-and-classes/verifiers-counting-interaction.md) | interactive |
| `ip` | [Stateful classical interactive proof](machines-and-classes/verifiers-counting-interaction.md) | interactive |
| `mip` | [Classical noncommunicating multiprover proof](machines-and-classes/verifiers-counting-interaction.md) | interactive |
| `pcp` | [Nonadaptive PCP verifier](machines-and-classes/verifiers-counting-interaction.md) | proof-verifier |
| `local-test` | [Typed local proof test](machines-and-classes/verifiers-counting-interaction.md) | proof-verifier |
| `constraint-graph` | [Typed constraint multigraph](machines-and-classes/verifiers-counting-interaction.md) | proof-intermediate |
| `regular-constraint-graph` | [Rotation-map regular constraint graph](machines-and-classes/verifiers-counting-interaction.md) | proof-intermediate |
| `encoded-constraint-graph` | [List-encoded finite constraint graph](machines-and-classes/verifiers-counting-interaction.md) | proof-intermediate |
| `two-prover-game` | [Classical two-prover one-round game](machines-and-classes/verifiers-counting-interaction.md) | proof-game |
| `search-relation` | [Polynomially balanced FNP relation](machines-and-classes/search-and-promises.md) | search |
| `fp-search` | [Polynomial-time FPSearch solver](machines-and-classes/search-and-promises.md) | search |
| `tfnp` | [Total FNP relation](machines-and-classes/search-and-promises.md) | search |
| `pls` | [PLS](machines-and-classes/search-and-promises.md) | total-search-principle |
| `ppp` | [PPP](machines-and-classes/search-and-promises.md) | total-search-principle |
| `ppad` | [PPAD](machines-and-classes/search-and-promises.md) | total-search-principle |
| `ppa` | [PPA](machines-and-classes/search-and-promises.md) | total-search-principle |
| `promise-completion` | [Disjoint promise and completion lift](machines-and-classes/search-and-promises.md) | promise |
| `promise-randomized` | [Direct randomized promise verifier](machines-and-classes/search-and-promises.md) | promise |
| `primrec` | [Mathlib primitive-recursive typed functions](machines-and-classes/computability-and-description.md) | computability |
| `mathlib-computable` | [Mathlib total computable typed functions](machines-and-classes/computability-and-description.md) | computability |
| `single-tape-description` | [Single-tape clocked description method](machines-and-classes/computability-and-description.md) | description |
| `tm0-description` | [Finitely supported TM0 description method](machines-and-classes/computability-and-description.md) | description |
| `tm1-description` | [Finitely supported TM1 description method](machines-and-classes/computability-and-description.md) | description |
| `fine-grained-time` | [Parameterized exponential and subexponential native time](machines-and-classes/native-counting.md) | resource |
| `fpt` | [FPT with arbitrary parameter bound](machines-and-classes/parameterized-complexity.md) | parameterized-resource |
| `xp` | [XP with arbitrary parameter bounds](machines-and-classes/parameterized-complexity.md) | parameterized-resource |
| `fpt-function` | [Native FPT function computation](machines-and-classes/parameterized-complexity.md) | parameterized-resource |
| `fpt-reduction` | [Parameter-respecting FPT many-one reduction](machines-and-classes/parameterized-complexity.md) | parameterized-reduction |
| `kernelization` | [Native polynomial-time same-problem kernelization](machines-and-classes/parameterized-complexity.md) | parameterized-preprocessing |
| `polynomial-kernel` | [Polynomially bounded kernelization](machines-and-classes/parameterized-complexity.md) | parameterized-preprocessing |
| `many-one-kernel` | [Many-one reducibility by admissible maps](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-many-one` | [Native polynomial-time many-one reduction](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-one-one` | [Polynomial-time one-one reduction](machines-and-classes/reductions.md) | reduction-interface |
| `logspace-one-one` | [Logspace one-one reduction](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-invertible-one-one` | [Polynomial-time invertible one-one reduction](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-length-increasing` | [Strictly length-increasing polynomial-time reduction](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-invertible-length-increasing` | [Invertible strictly length-increasing polynomial-time reduction](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-isomorphism` | [Polynomial-time language isomorphism](machines-and-classes/reductions.md) | reduction-interface |
| `polytime-tt` | [Unrestricted truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-tt` | [Unrestricted truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-ktt` | [Fixed-query truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-ktt` | [Fixed-query truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-btt` | [Constant-bounded truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-btt` | [Constant-bounded truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-dtt` | [Disjunctive truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-dtt` | [Disjunctive truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-ctt` | [Conjunctive truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-ctt` | [Conjunctive truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-ptt` | [Positive truth-table in polynomial time](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `logspace-ptt` | [Positive truth-table in logarithmic space](machines-and-classes/reductions.md) | nonadaptive-reduction |
| `polytime-turing` | [Adaptive polynomial-time Turing reduction](machines-and-classes/reductions.md) | adaptive-reduction |
| `polytime-many-one-autoreduction` | [PolyTimeManyOneAutoreducible](machines-and-classes/reductions.md) | autoreduction |
| `logspace-many-one-autoreduction` | [LogSpaceManyOneAutoreducible](machines-and-classes/reductions.md) | autoreduction |
| `polytime-tt-autoreduction` | [Unrestricted truth-table autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `polytime-ktt-autoreduction` | [Fixed-query truth-table autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `polytime-btt-autoreduction` | [Constant-bounded truth-table autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `polytime-dtt-autoreduction` | [Disjunctive truth-table autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `polytime-ctt-autoreduction` | [Conjunctive truth-table autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `polytime-turing-autoreduction` | [Adaptive polynomial-time Turing autoreduction](machines-and-classes/reductions.md) | autoreduction |
| `mitotic-splitting` | [Resource-bounded mitotic splitting interfaces](machines-and-classes/reductions.md) | reduction-splitting |
| `linear-measure-reduction` | [Polynomial-time reduction with linear parameter growth](machines-and-classes/reductions.md) | fine-grained-reduction-rule |
| `exponential-measure-reduction` | [Exponential-cost reduction into m-log-m measure](machines-and-classes/reductions.md) | fine-grained-reduction-rule |

## Circuits, logic and information access

[Section overview](circuits-logic-and-other-models/index.md).

| ID | Model or interface | Family |
|---|---|---|
| `acyclic-circuit` | [Typed acyclic circuit and straight-line program](circuits-logic-and-other-models/index.md) | circuits |
| `source-synthesis` | [Semantic synthesis and source-relative complexity](circuits-logic-and-other-models/index.md) | circuits |
| `generic-formula` | [Tree formulas over arbitrary signatures](circuits-logic-and-other-models/index.md) | circuits |
| `demorgan` | [Binary De Morgan circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `monotone` | [Monotone Boolean circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `unbounded` | [Unbounded fan-in Boolean circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `modular` | [Unbounded modular gates and AC0[q]/ACC0](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `threshold` | [Unweighted threshold circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `weighted-threshold` | [Real weighted threshold circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `activation` | [Weighted affine gates with arbitrary Boolean activation](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `multiplicity` | [Symmetric gates with explicit input multiplicities](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `oracle-circuit` | [Boolean circuits with oracle gates](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `quantified-circuit` | [Existential and universal auxiliary-input circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `conondeterministic-and` | [Conondeterministic AND complexity](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `bounded-error-circuit` | [Circuits supplied uniform random auxiliary bits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `nonuniform-classes` | [Nonuniform size/depth circuit classes](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `layered-code` | [Serialized layered Boolean circuits](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `alternating-formula` | [Fixed-depth alternating AND/OR formulas](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `read-once-formula` | [Positive and literal read-once formula syntax](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `semicircuit` | [Boolean semicircuits with affine equations](circuits-logic-and-other-models/index.md) | boolean-circuits |
| `cyclic` | [Monotone cyclic circuits](circuits-logic-and-other-models/index.md) | circuits |
| `full-basis` | [Full bounded-arity semantic basis](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `arithmetic` | [Arithmetic circuits and formulas](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `affine` | [Arbitrary-arity affine gates](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `sigmapi-formula` | [Sigma-Pi arithmetic formulas](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `sigmapi-circuit` | [Sigma-Pi DAG circuits with simple products](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `vp` | [Valiant VP and polynomial families](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `vnp` | [Valiant VNP and p-projection completeness](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `waring` | [Waring sums of powers](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `matrix-multiplication-exponent` | [Matrix multiplication exponent, tensor rank and degeneration](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `sum-of-terms` | [Dictionary sum-of-terms circuits](circuits-logic-and-other-models/index.md) | circuits |
| `rational-formula` | [Noncommutative rational formulas with partial evaluation](circuits-logic-and-other-models/index.md) | algebraic-circuits |
| `decomposable-dag` | [Smooth decomposable set-of-assignments DAGs](circuits-logic-and-other-models/index.md) | networks |
| `constraint-network` | [Local-constraint networks on multigraphs](circuits-logic-and-other-models/index.md) | networks |
| `readonce-nbp` | [Frontier read-once nondeterministic branching programs](circuits-logic-and-other-models/index.md) | branching-programs |
| `tensor-network` | [Semiring-valued tensor networks](circuits-logic-and-other-models/index.md) | networks |
| `described-tensor` | [Descriptor-based Boolean tensor networks](circuits-logic-and-other-models/index.md) | networks |
| `explicit-tensor` | [Explicit truth-table tensor networks](circuits-logic-and-other-models/index.md) | networks |
| `quantum-circuit` | [Finite-dimensional unitary circuits](circuits-logic-and-other-models/index.md) | quantum |
| `quantum-code` | [Hadamard and reversible Boolean quantum codes](circuits-logic-and-other-models/index.md) | quantum |
| `uniform-quantum` | [Native polynomial-time uniform quantum families](circuits-logic-and-other-models/index.md) | quantum |
| `bqp` | [Bounded-error polynomial-time uniform quantum languages](circuits-logic-and-other-models/index.md) | quantum |
| `bqtime` | [Bounded-error quantum gate time](circuits-logic-and-other-models/index.md) | quantum |
| `nqtime` | [Positive-acceptance quantum gate time](circuits-logic-and-other-models/index.md) | quantum |
| `eqtime` | [Exact quantum gate time](circuits-logic-and-other-models/index.md) | quantum |
| `postbqtime` | [Postselected bounded-error quantum gate time](circuits-logic-and-other-models/index.md) | quantum |
| `monoid-program` | [Monoid and permutation branching programs](circuits-logic-and-other-models/index.md) | branching-programs |
| `inplace-finite` | [In-place finite-state multihead dynamics](circuits-logic-and-other-models/index.md) | finite-dynamics |
| `universal-gate-map` | [Universal gate-by-gate iteration map](circuits-logic-and-other-models/index.md) | finite-dynamics |
| `decision-tree` | [Deterministic Boolean query trees](circuits-logic-and-other-models/index.md) | information-access |
| `comparison-tree` | [Monotone/separable comparison queries](circuits-logic-and-other-models/index.md) | information-access |
| `randomized-query` | [Finite-support randomized decision trees](circuits-logic-and-other-models/index.md) | information-access |
| `distributional-query` | [Distributional decision-tree complexity](circuits-logic-and-other-models/index.md) | information-access |
| `quantum-query` | [Phase-oracle quantum query algorithms](circuits-logic-and-other-models/index.md) | quantum |
| `deterministic-communication` | [Two-party bit communication trees](circuits-logic-and-other-models/index.md) | communication |
| `local-oriented-cycle` | [Deterministic LOCAL algorithms on oriented cycles](circuits-logic-and-other-models/query-and-communication.md) | distributed |
| `dag-communication` | [Acyclic networks of communication protocols](circuits-logic-and-other-models/index.md) | communication |
| `round-communication` | [Bounded-round message protocols](circuits-logic-and-other-models/index.md) | communication |
| `publiccoin` | [Public-coin communication](circuits-logic-and-other-models/index.md) | communication |
| `privatecoin` | [Private-coin communication](circuits-logic-and-other-models/index.md) | communication |
| `nondet-communication` | [Nondeterministic rectangle-cover communication](circuits-logic-and-other-models/index.md) | communication |
| `fo` | [Mathlib first-order syntax and finite relational structures](circuits-logic-and-other-models/index.md) | finite-logic |
| `fo-interpretation` | [Tuple-domain first-order interpretations](circuits-logic-and-other-models/index.md) | finite-logic |
| `tagged-interpretation` | [Tagged interpretations with varying tuple dimensions](circuits-logic-and-other-models/index.md) | finite-logic |
| `fo-projection` | [Literal-leaf numeric-case first-order projections](circuits-logic-and-other-models/index.md) | finite-logic |
| `raw-operator` | [General scoped logical operators and raw LFP syntax](circuits-logic-and-other-models/index.md) | finite-logic |
| `lfp` | [Positive checked first-order least fixed point](circuits-logic-and-other-models/index.md) | finite-logic |
| `tc` | [First-order reflexive transitive closure](circuits-logic-and-other-models/index.md) | finite-logic |
| `eso` | [Existential second-order relational sentences](circuits-logic-and-other-models/index.md) | finite-logic |
| `relational-encoding` | [Unordered finite relational table encoding](circuits-logic-and-other-models/index.md) | finite-logic |
| `ordered-structure` | [Canonical ordered finite structures with BIT](circuits-logic-and-other-models/index.md) | finite-logic |
| `ordered-domain` | [Ordered restricted-domain interpretations with numeric certificates](circuits-logic-and-other-models/index.md) | finite-logic |
| `fulltuple` | [Positive-dimensional full-tuple ordered interpretations](circuits-logic-and-other-models/index.md) | finite-logic |
| `cnf` | [Literal lists, CNF and assignment counting](circuits-logic-and-other-models/index.md) | propositional-models |
| `clause-set` | [Finite-set CNF for sparsification](circuits-logic-and-other-models/index.md) | propositional-models |
| `csp` | [Relation-alphabet constraint satisfaction problems](circuits-logic-and-other-models/index.md) | propositional-models |
| `qbf` | [Named-variable quantified Boolean formulas](circuits-logic-and-other-models/index.md) | propositional-models |
| `resolution-relation` | [Inductive resolution derivability](circuits-logic-and-other-models/index.md) | proof-systems |
| `resolution-lines` | [Resolution proofs as ordered line lists](circuits-logic-and-other-models/index.md) | proof-systems |
| `resolution-tree` | [Tree-like resolution derivations](circuits-logic-and-other-models/index.md) | proof-systems |
| `pac` | [General deterministic PAC framework](circuits-logic-and-other-models/index.md) | learning |
| `randomized-pac` | [Randomized agnostic PAC framework](circuits-logic-and-other-models/index.md) | learning |
| `uniform-learning` | [Uniform-distribution Boolean sample learning](circuits-logic-and-other-models/index.md) | learning |
| `membership-learning` | [Randomized membership-query learners](circuits-logic-and-other-models/index.md) | learning |
| `linearity-test` | [Decision-tree property testers for Boolean linearity](circuits-logic-and-other-models/index.md) | learning |
| `mcsp` | [Total truth-table minimum circuit size](circuits-logic-and-other-models/index.md) | metacomplexity |
| `partial-mcsp` | [Partial truth-table circuit minimization](circuits-logic-and-other-models/index.md) | metacomplexity |
| `succinct-mcsp` | [Sample-set succinct MCSP](circuits-logic-and-other-models/index.md) | metacomplexity |
| `gap-mcsp` | [GapMCSP promise problems](circuits-logic-and-other-models/index.md) | metacomplexity |
| `average-case-circuit-hardness` | [Average-case hardness against nonuniform De Morgan circuits](circuits-logic-and-other-models/index.md) | lower-bound-methods |
| `fusion` | [Finite invariant-failure gate covers](circuits-logic-and-other-models/index.md) | lower-bound-methods |
| `semifilter` | [Semifilter witnesses and two-dimensional pair covers](circuits-logic-and-other-models/index.md) | lower-bound-methods |
| `approximation` | [Local circuit approximation schemes](circuits-logic-and-other-models/index.md) | lower-bound-methods |
| `natural-property` | [Large constructive useful Boolean-function properties](circuits-logic-and-other-models/index.md) | metacomplexity |

## Programs, probability and cryptography

[Section overview](programs-crypto-and-probability/index.md).

| ID | Model or interface | Family |
|---|---|---|
| `prob-free-oracle` | [Typed free oracle computation](programs-crypto-and-probability/programs-and-realization.md) | free-programs |
| `prob-finite-sampling` | [Finite exact sampling programs](programs-crypto-and-probability/programs-and-realization.md) | free-programs |
| `prob-stateful-semantics` | [Stateful probability and ideal oracle semantics](programs-crypto-and-probability/programs-and-realization.md) | probability-semantics |
| `native-strict-ppt` | [Uniform strict probabilistic polynomial time](programs-crypto-and-probability/programs-and-realization.md) | native-probabilistic |
| `native-oracle-ppt` | [Uniform stateful oracle polynomial time](programs-crypto-and-probability/programs-and-realization.md) | native-probabilistic |
| `crypto-game-schema` | [Admissible-adversary Boolean games](programs-crypto-and-probability/security-games-and-primitives.md) | security-games |
| `crypto-uniform-primitives` | [Uniform hardness and pseudorandomness families](programs-crypto-and-probability/security-games-and-primitives.md) | security-games |
| `crypto-staged-encryption` | [Chosen-message and chosen-ciphertext encryption](programs-crypto-and-probability/security-games-and-primitives.md) | security-games |
| `crypto-signing-auth` | [Signing, authentication, nonce and index games](programs-crypto-and-probability/security-games-and-primitives.md) | security-games |
| `crypto-commitment` | [Public-parameter commitment distributions](programs-crypto-and-probability/security-games-and-primitives.md) | security-games |
| `crypto-homomorphic` | [Compact bit encryption and circuit evaluation](programs-crypto-and-probability/homomorphic-encryption.md) | security-games |
| `crypto-sigma` | [Sigma transcripts, extraction and aborts](programs-crypto-and-probability/protocols-and-privacy.md) | protocols |
| `crypto-ideal-oracle` | [Random-oracle signatures and ideal-permutation ciphers](programs-crypto-and-probability/protocols-and-privacy.md) | ideal-oracles |
| `crypto-zero-knowledge` | [Generable and auxiliary-input zero knowledge](programs-crypto-and-probability/protocols-and-privacy.md) | interactive-proofs |
| `crypto-mpc` | [Synchronous typed oracle-aided MPC](programs-crypto-and-probability/protocols-and-privacy.md) | protocols |
| `crypto-uc` | [Call-bounded UC execution and emulation](programs-crypto-and-probability/protocols-and-privacy.md) | protocols |
| `crypto-perfect-secrecy` | [Perfect-secrecy encryption](programs-crypto-and-probability/protocols-and-privacy.md) | information-theoretic-crypto |
| `crypto-secret-sharing` | [Authorized-coalition secret sharing](programs-crypto-and-probability/protocols-and-privacy.md) | information-theoretic-crypto |
| `privacy-differential` | [Differential privacy of output laws for an explicit adjacency relation](programs-crypto-and-probability/protocols-and-privacy.md) | privacy |
| `average-exact-ppt` | [MildlyHardOnAverage](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-symmetric-ppt` | [MildlyHardOnAverageToApprox](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-one-sided-ppt` | [MildlyHardOnAverageToOneSidedApprox](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-exact-deterministic` | [MildlyHardOnAverageDet](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-symmetric-deterministic` | [MildlyHardOnAverageToApproxDet](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-one-sided-deterministic` | [MildlyHardOnAverageToOneSidedApproxDet](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-exact-io` | [MildlyHardOnAverageIO](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-symmetric-io` | [MildlyHardOnAverageToApproxIO](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-one-sided-io` | [MildlyHardOnAverageToOneSidedApproxIO](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-exact-enat-ppt` | [MildlyHardOnAverageENat](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `average-exact-enat-io` | [MildlyHardOnAverageIOENat](programs-crypto-and-probability/average-case-hardness.md) | average-case-hardness |
| `interactive-public-coin-reduction` | [Public-coin interactive oracle reduction](programs-crypto-and-probability/interactive-reductions.md) | interactive-reductions |
| `interactive-efficient-extraction` | [Uniform efficient straight-line extraction](programs-crypto-and-probability/interactive-reductions.md) | interactive-reductions |
| `interactive-efficient-simulation` | [Uniform approximate native HVZK simulation](programs-crypto-and-probability/interactive-reductions.md) | interactive-reductions |
| `interactive-sumcheck` | [Sumcheck with final direct evaluation](programs-crypto-and-probability/interactive-reductions.md) | interactive-reductions |
| `interactive-gkr` | [Layered arithmetic circuit GKR protocol](programs-crypto-and-probability/interactive-reductions.md) | interactive-reductions |

## Algorithms and memory

[Section overview](algorithms-and-memory/index.md).

| ID | Model or interface | Family |
|---|---|---|
| `natural-ram-unit` | [Unbounded natural RAM, unit cost](algorithms-and-memory/ram-variants.md) | natural-ram |
| `natural-ram-log` | [Unbounded natural RAM, logarithmic cost](algorithms-and-memory/ram-variants.md) | natural-ram |
| `generic-ram` | [Generic partial-operation RAM](algorithms-and-memory/ram-variants.md) | generic-ram |
| `algebraic-real-ram` | [Tagged exact real RAM](algorithms-and-memory/ram-variants.md) | generic-ram |
| `algebraic-prime-field-ram` | [Tagged prime-field RAM](algorithms-and-memory/ram-variants.md) | generic-ram |
| `wordram-fixed` | [Fixed-program bounded Word-RAM](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `wordram-width-family` | [Width-selected Word-RAM programs](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `wordram-list-output` | [Memory-array list outputs](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `wordram-randomized` | [Exact finite-uniform randomized Word-RAM](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `wordram-expected` | [Expected Word-RAM execution and Las Vegas loops](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `wordram-structured` | [Structured programs with exact native counts](algorithms-and-memory/wordram-and-bridges.md) | word-ram |
| `state-transition` | [Relational adaptive data-structure clients](algorithms-and-memory/memory-specifications.md) | state-transition |
| `randomized-state-transition` | [Randomized state transitions and refinement](algorithms-and-memory/memory-specifications.md) | state-transition |
| `oblivious-sequence` | [Oblivious operation/transcript contracts](algorithms-and-memory/memory-specifications.md) | state-transition |
| `memory-oracle` | [Allocated word-memory oracle](algorithms-and-memory/memory-specifications.md) | memory |
| `native-callable` | [Dynamic programs, controllers and graded realization](algorithms-and-memory/memory-specifications.md) | memory |
| `ram-footprints-traces` | [RAM footprints, traces and memory windows](algorithms-and-memory/memory-specifications.md) | memory |
| `online-deterministic` | [Deterministic online competitive problems](algorithms-and-memory/online-and-streaming.md) | online |
| `count-min-stream` | [Weighted insertion Count-Min sketch](algorithms-and-memory/online-and-streaming.md) | streaming |
| `native-stream-fold` | [Native input-stream folds](algorithms-and-memory/online-and-streaming.md) | streaming |
| `cost-game` | [Finite strategic games in cost form, potentials and coarse correlated equilibria](algorithms-and-memory/strategic-games.md) | game-theory |
| `atomic-congestion-game` | [Atomic congestion games with Rosenthal's potential](algorithms-and-memory/strategic-games.md) | game-theory |
| `nonatomic-routing` | [Nonatomic selfish routing and Wardrop flows](algorithms-and-memory/strategic-games.md) | game-theory |
| `retroactive-rebuild` | [Timeline editing by reset and replay](algorithms-and-memory/memory-specifications.md) | state-transition |
| `catalytic-restoring-operations` | [Borrowed-register and key-table restoration](algorithms-and-memory/catalytic-and-tree-evaluation.md) | catalytic-operations |
| `tree-evaluation-binary` | [Explicit binary Tree Evaluation](algorithms-and-memory/catalytic-and-tree-evaluation.md) | tree-evaluation |
| `tree-evaluation-ary` | [Fan-in-d Tree Evaluation and shared registers](algorithms-and-memory/catalytic-and-tree-evaluation.md) | tree-evaluation |
| `tree-evaluation-packed-controller` | [Packed tree registers and uniform raw controller](algorithms-and-memory/catalytic-and-tree-evaluation.md) | tree-evaluation |
| `mechanism-single-parameter` | [Single-parameter sealed-bid mechanisms and Myerson's Lemma](algorithms-and-memory/mechanism-design.md) | mechanism-design |
| `mechanism-general-vcg` | [General-valuation mechanisms and VCG](algorithms-and-memory/mechanism-design.md) | mechanism-design |
