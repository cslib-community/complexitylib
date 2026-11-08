# Algorithms, memory, and data structures

This part of Complexitylib contains several machine models and a separate family of specification and resource interfaces. Unbounded natural RAM, generic partial-operation RAM, exact algebraic RAM, bounded Word-RAM and randomized Word-RAM do not have interchangeable costs. State-transition clients, memory oracles, online strategies and streaming sketches add useful models of interaction but are not automatically machine implementations [complexitylib][complexitylib].

The survey baseline is `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. Definitions and representative theorem statements were inspected read-only. No Lean build was performed by this author. The [model map](../model-map.md) links the explanatory pages, which record inspected sources, principal declarations, assumptions, bridges and ownership.

## Reading map

- [RAM variants](ram-variants.md): unbounded natural registers, unit/logarithmic cost, generic partial operations, exact real/prime-field arithmetic and native representation obligations.
- [Word-RAM and proved bridges](wordram-and-bridges.md): instruction semantics, uniformity, output conventions, randomized execution, expected time, and actual Turing simulations.
- [Memory and state-transition specifications](memory-specifications.md): relational adaptive clients, refinement, amortization, memory charges, native callable contracts, framing and traces.
- [Online and streaming models](online-and-streaming.md): demand paging, competitive analysis, Count-Min and native streaming folds.
- [Strategic games, congestion and the price of anarchy](strategic-games.md): cost games, potential games, Rosenthal's theorem, smoothness and coarse correlated equilibria, and the `5/2` and `4/3` price-of-anarchy bounds.
- [Borrowed registers and native Tree Evaluation](catalytic-and-tree-evaluation.md): exact restoration, explicit gate-table inputs, Cook–Mertz workspace, and fan-in/packed variants.
- [Representative algorithm endpoints](algorithm-endpoints.md): what the formal abstracts prove about sorting/selection, shortest paths, heaps, hashing and minimum cut, the classical approximation bounds for set cover, vertex cover and metric TSP, Freivalds' costed randomized matrix-product verifier, Euler circuits in multigraphs, Farkas' lemma and LP duality over ordered fields, Yannakakis's factorization theorem for extension complexity, and LLL-reduced lattice bases.
- [Mechanism design](mechanism-design.md): single-parameter mechanisms, Myerson's Lemma, Vickrey and knapsack auctions, VCG, Myerson's optimal auction, Bayes–Nash equilibrium, revenue equivalence and the first-price auction; incentive properties only, with no running time charged. The same page covers social welfare functions and Arrow's impossibility theorem.

## Taxonomy

| Layer | Model or interface | Cost convention |
|---|---|---|
| Machine | Natural RAM extending URM registers | Unit cost or separately specified bit-length/logarithmic cost |
| Machine schema | `GenericRAM.Model` | One step per instruction; partial operation, address, control and admissibility checks |
| Machine instances | Tagged exact real / prime-field RAM | Unit-cost exact field operations plus bounded natural-word addresses |
| Machine | Fixed-code bounded Word-RAM | Executed instruction count; checked fitted words; explicit halt |
| Program-family variant | Width-dependent Word-RAM | Code selected by width, with uniform list-length bound; selector uncharged |
| Machine extension | Randomized Word-RAM | Unit-cost exact finite-interval sampling; call/bit currencies and expected instruction count |
| Proof language | Structured RAM `Code` | Exact compiler correspondence including branches, jumps and final halt |
| Specification | Relational and randomized state transitions | Explicit operation charge, adaptive clients, demonic validity; pure controller work uncharged |
| Memory interface | Allocated word-memory oracle | Reads/writes and allocation charged by declared currency; native realization separate |
| Native interface | Dynamic programs, controllers and realizations | Fixed emitted machine code, charged glue/control and preserved memory invariants |
| Resource logic | Footprints, traces, separation/frame assertions | Actual RAM accesses and instructions; not a free-computation cell-probe model |
| Interaction model | Deterministic online strategy | Compare explicit cost against all legal offline schedules |
| Streaming interfaces | Weighted insertion sketch / native scan fold | Numerical/probabilistic accuracy versus separately certified native time/workspace |
| Restoring operations | Arbitrary borrowed vector registers or key tables | Exact restoration; native realization not bundled |
| Tree-evaluation problem family | Binary/fan-in-d gate trees and packed controllers | Explicit input encoding; native Cook–Mertz workspace distinct from algebraic correctness |
| History transformation | Timeline editing by reset and replay | Explicit edit/reset/replay calls; no automatic rollback or constant-time list copying |
| Incentive model | Single-parameter and general sealed-bid mechanisms | None: allocation and payment rules are arbitrary real functions; DSIC/IR over nonnegative bids; Bayes–Nash equilibrium over independent priors (revenue results assume densities) |

## Major bridge statements

The current snapshot includes real bridges between Word-RAM and native Turing computation. [Complexity/Computability/WordRAM/OfTuring.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/OfTuring.lean) compiles finite-control binary multitape machines to one fixed additive Word-RAM program. [Complexity/Computability/WordRAM/Turing/Overhead.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/WordRAM/Turing/Overhead.lean) gives a quantitative reverse simulation using sparse memory and efficient scalar operations. [mem_P_iff_uniformPolynomialTime](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/P/WordRAM.lean#L153) identifies the fixed-program polynomial-time decision classes under the stated encoding and basis conditions. Older descriptions of the Word-RAM layer as lacking this bridge are stale.

The generic exact-real instance has no corresponding binary Turing simulation: exact real values are part of its mathematical semantics. Generic finite encodings and efficient scalar certificates support simulations for appropriate encodable instances; they cannot remove the representation premise.

## Design observations

Source statements separate fixed programs from width-selected families, scalar outputs from memory-array outputs, and memory-query charges from total instruction counts. **Inference:** this reduces the risk that a representation convention or free controller is mistaken for a polynomial-time algorithm. Native realization includes a separate work allowance for pure/control operations, addressing the fact that zero memory queries can still require nonconstant computation.

Several representative algorithms use the RAM's preinstalled, zero-filled input memory. Their bounds begin at that initial state. Dynamic callable results instead state whether initialization may assume a fresh zeroed block or must clear an arbitrary existing block. These conventions materially affect initialization costs.

The source headers credit Erik Demaine and the lean-trominoes contributors for the Word-RAM foundation, Renfei Zhou for randomized RAM and several algorithm/data-structure endpoints, Samuel Schlesinger for extensions and interfaces, and Christian Reitwiessner for the native streaming backend. This is source attribution, not a measurement of who or what authored every proof.

## Source-review scope

The November 1–2 source review consulted Erickson's Section 6.1/Table 1, Sleator–Tarjan's
Section 4/Theorems 5–6, Cormode's point-query theorem, the Cook–Mertz primary report,
Williams' Appendix A, and the pinned catalytic-comparison Lean source. It checked selected
statements and model conventions, not their entire proof chains. Cook–Reckhow and Thorup
checks were limited to metadata or source attribution; Goldreich's tree-evaluation check
covered report metadata and abstract. The detailed pages retain the relevant qualifications.

This section had no direct dependency-file citations affected by the shared-checkout drift.
The chapters link the fixed source revision; copied dependencies and generated audit reports
are not maintained inputs.

## Known Limitations

Completeness is by computational/specification model family. The many Word-RAM algorithm modules are clients, not hundreds of additional models; their complete proof bodies were not audited. The formal abstracts were inspected selectively for exact quantifiers and limits. No claim is made here about performance of Lean's evaluator, compiled Lean code, real hardware, or a deployment implementation.

[complexitylib]: ../sources.md#complexitylib
