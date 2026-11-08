# Circuits, logic, and information-access models

Complexitylib uses several kinds of computational model for different purposes. A circuit gives a finite composition of semantic operations; a decision tree or communication protocol charges access to information; a logical formula defines a query on a finite structure; a proof object measures a derivation; a learner or tester measures examples or oracle queries. These models often share functions and theorems, but their resource units are not interchangeable. This section surveys their definitions and the principal bridges at source snapshot `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. [complexitylib][complexitylib]

The curated [Model map](../model-map.md) contains **92 entries**, separating changes in semantics or resource accounting while grouping internal proof records under the model they support. The original survey checked 189 principal declaration anchors in 125 distinct cited files. These dated counts describe the editorial selection; they are neither a declaration census of the whole library nor an assertion that there are exactly 92 mathematically distinct models.

## Reading map

| Document | Main question |
|---|---|
| [Circuits and formulas](circuits-and-formulas.md) | What is a gate, what is free, and how do the Boolean bases and nonuniform classes differ? |
| [Algebraic and quantum models](algebraic-and-quantum.md) | Which algebraic equalities, partial operations, encodings, the matrix multiplication exponent and quantum resources are formalized? |
| [Networks and finite dynamics](networks-and-iteration.md) | How do graph separators, tensor contractions, nondeterministic paths and function iteration connect? |
| [Query and communication complexity](query-and-communication.md) | Which information-access costs are charged, including LOCAL rounds, and what lower-bound and simulation theorems use them? |
| [Finite-model logic](finite-model-logic.md) | How do formulas, interpretations, encodings and native complexity classes meet? |
| [Propositional proof systems](proof-systems.md) | Which proof objects and measures support resolution lower bounds, interpolation, cutting planes and Frege proofs? |
| [Learning and property testing](learning-and-testing.md) | Are the proved bounds on samples, queries, or machine time? |
| [Metacomplexity and lower-bound methods](metacomplexity-and-methods.md) | What are the MCSP variants and conditional barriers, and how are general lower-bound arguments packaged? |

## Architecture and concrete use

The central reusable layer is upstream CSLib's `Signature`, `Interpretation`, topologically indexed `Program`, and `Circuit`. Complexitylib extends that layer with formulas, weighted costs, semantic synthesis, alternative bases and theorem-specific interfaces. The same circuit program can be interpreted over booleans, formal polynomials or another carrier; meaning-preserving interpretation maps transport evaluation. This reuse supports mathematical variation without duplicating the acyclic graph machinery. [cslib][cslib] See [Circuit](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Circuit/Basic.lean#L46) and [source-relative complexity](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/SourceComplexity.lean).

A representative chain is a fixed first-order sentence over finite relational structures. Its input encoding gives the universe size and relation truth tables. The sentence can be compiled into an unbounded fan-in Boolean formula with constant depth and polynomial size; a separate compilation gives a native logspace decider. Adding positive least fixed points changes the logical model and yields polynomial-time model checking. In the reverse direction, a native polynomial-time machine is represented by a fixed-point tableau, giving the ordered Immerman–Vardi equivalence. The circuit, logic and native-time claims are different links in that chain, not three names for the same implementation. See [finite-model logic](finite-model-logic.md).

A second chain begins with an unsatisfiable CNF. A resolution refutation is a proof object whose size counts lines. Interpolation extracts a separating circuit, while tree-like resolution also gives a decision tree that searches for a falsified clause. The resulting gate or query lower bound constrains proof size through an explicit bridge. Neither representation alone charges the running time of a proof-search algorithm. See [proof systems](proof-systems.md).

A third chain starts with a local-constraint network. A layout exposes a frontier of edge assignments; sweeping the layout gives a read-once nondeterministic branching program. Tensor networks use a related graph representation but sum products of local weights instead of existentially testing constraints. Their explicit descriptors and native contraction algorithms require additional encoding and arithmetic arguments. See [networks](networks-and-iteration.md).

## Resource conventions

| Quantity | Convention in the relevant model |
|---|---|
| Circuit size | Operation gates; input nodes and designated output wires are free. |
| Circuit depth | Maximum designated-output depth; a theorem may instead name a weighted depth. |
| Formula size | Either input-leaf occurrences or operation nodes; the choice is explicit. |
| Arithmetic depth | Ordinary depth or product-only depth; coefficient cost is generally not bit cost. |
| Query complexity | Usually structural worst-case depth, including all trees in randomized support. |
| Communication | Transmitted bits, messages, or maximum local DAG-node cost, depending on the model. |
| Distributed rounds | Synchronous LOCAL rounds with unbounded messages and local computation; identifiers and the cycle length are explicit inputs. |
| Learning | Sample, membership-query or mistake count; native runtime is a separate theorem. |
| Logic | Usually data complexity of one fixed formula, not combined complexity of formula and structure. |
| Proof complexity | Lines, tree nodes, or distinct-literal width; not proof-search time. |

These distinctions are visible in the source definitions and model map. In particular, nonuniform families choose a circuit separately at each input length; finite real weights need not have finite bit encodings; a raw total decoder may assign fallback values while the language rejects malformed codes. [complexitylib][complexitylib]

## Source evidence and scope

The author inspected representative definitions throughout these families and traced selected abstract-to-library endpoints, including Fagin, Barrington, constant-depth Boolean lower bounds, Braverman, formula bounds, partial MCSP and magnification. Definition inspection and endpoint tracing were recorded separately in the survey. **This worker did not run a Lean build**; compilation evidence belongs to the assurance section. Likewise, named mathematical sources are credited from the pinned implementation documentation, with no assertion that every original paper was independently compared theorem by theorem.

The November 2 dependency-pin audit found that the live CSLib and Mathlib package HEADs differed from the manifest pins. All five directly cited CSLib files, three pinned guidance files and the two imported Mathlib first-order foundation files were byte-identical to independently retrieved pinned contents, so no mathematical statement or declaration anchor changed. That audit read immutable Git objects or independently retrieved GitHub blobs verified against their Git blob IDs, with lazy fetching disabled. This checks the selected dependency evidence, not the entire transitive dependency graph.

Coverage is organized by model family and behavior-changing variant. The 564 files under the circuit root alone include many arithmetic, encoding and proof-internal records that are not independent computational models. The map is intentionally curated rather than derived by treating each `structure` declaration as a model. Its principal remaining coverage risk is an omitted subordinate semantic variant in the large circuit/frontier/rational development; the source-location validator cannot establish semantic completeness.

The [native verifier account](../machines-and-classes/verifiers-counting-interaction.md) owns IP and PCP class semantics. The distinct public-coin oracle-reduction model, sumcheck and GKR are covered in [interactive reductions](../programs-crypto-and-probability/interactive-reductions.md), including full versus coordinate access and the separate efficiency interfaces. This section owns their circuit and query-testing models. BQP and its four gate-time/acceptance variants are owned here through uniform-circuit semantics; [machines and classes](../machines-and-classes/index.md) cross-links native class containments involving them. Cryptographic games and pseudorandomness are owned by [programs and cryptography](../programs-crypto-and-probability/index.md); their natural-proofs client is discussed here. Development dates and automation claims belong to [development history](../development-history/index.md), not to current source annotations.

## Maintaining the reference

The [model map](../model-map.md) links to the maintained explanations of semantics, resources,
results, bridges and limitations. Update those pages when an API or model changes. Generated
ledgers, copied dependency blobs and one-off validation reports are not inputs to this manual.
The [reproduction notes](../BUILD.md#regenerating-research-outputs) distinguish optional mechanical
exports from the semantic judgments that require review.

[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
