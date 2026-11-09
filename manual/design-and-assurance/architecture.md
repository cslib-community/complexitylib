# Architecture and design decisions

## Programs, semantics and implementation witnesses

The machine layer extends CSLib's configurations and actions rather than introducing unrelated deterministic and nondeterministic machines. The parametric choice interface recovers `MultiTapeTM` and `MultiTapeNTM` step-exactly. Additional interpretations preserve the distinctions between fair probabilistic choice, counted branch multiplicity and alternating acceptance. The [machine survey](../machines-and-classes/index.md) explains these definitions and their bridges.

Above this layer, free programs describe interactions independently of a particular interpreter. `PFunctor.FreeM` supports pure return, oracle operations and continuation; interpretation supplies probability, state or concrete machine execution. A clocked machine run is itself represented as a program. This permits semantic equality and simulation theorems to be reused instead of rebuilding a transition table for every algorithm. The [current design commitments](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/AGENTS.md#design-commitments-do-not-re-litigate-casually) explicitly require the universal machine to be an interpreter program certified by the calculus.

The distinction between a Lean function and a resource-certified algorithm is load-bearing. A function may be total and mathematically well-defined yet have no efficient implementation. Similarly a PMF can specify a distribution that cannot be sampled exactly by a finite bounded fair-coin computation. [CONTRIBUTING.md, Algorithms are programs](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/CONTRIBUTING.md#algorithms-are-programs) directs algorithms to `ProbComp`/`OracleComp`, keeping PMFs for denotational laws and ideal distributions. A realizability theorem then supplies the native machine and resource bound. This design makes the implementation obligation visible; it does not make it disappear.

## Resource currencies are explicit

The public direction is plain computability with independent time and space bounds. Tidy machines additionally restore tape/head conditions useful for composing implementations; these are construction invariants, not properties that every user-facing function should expose. Existing tidy statements are being migrated, with a per-module ratchet preventing growth. This is an ongoing migration, not a completed removal. [Current contribution rules](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/CONTRIBUTING.md#public-surface-under-the-module-system)

Input length is the length of the chosen encoding. Binary naturals, unary controls, framed lists, finite structures and machine descriptions have different size laws; changing an encoding can change the resource claim. The library therefore uses explicit input/output embeddings in computability statements and proves encoding-size bounds. For low-space functions the additional question is whether returned data counts toward the workspace contract. `ComputableInO` charges output size while `ComputableInBigO` does not; logarithmic-space transductions have a separate convention. See the [resource table](../machines-and-classes/native-and-resources.md).

The same discipline applies outside native machines:

| Interface | What it charges | Further obligation |
|---|---|---|
| Oracle program | Selected calls or operation costs | Controller time, handler implementation and growth |
| Circuit construction | Gates, sometimes weighted gates or depth | Uniform generation and bit-level cost where required |
| State-transition specification | Costs of allowed operations | A realization and efficient controller |
| Word-RAM | Instructions over a stated word width and basis | Width adequacy, encoding and machine simulation |
| Communication/query protocol | Communication or oracle queries | Local computation, if the theorem requires it |

These interfaces share compositional proof patterns without identifying their cost units. A theorem whose result is information-theoretic should remain useful without manufacturing a runtime claim. Conversely, an efficient-implementation theorem must fix the machine/program and constants in the required order before universally quantifying inputs.

## Semantic refinement instead of positional bookkeeping

The library repeatedly separates a high-level operation from its representation. Circuit synthesis tracks available values and charges a shared intermediate once. Stateful data structures give an abstract transition specification, then a concrete representation invariant and refinement. Word-RAM controllers implement memory interactions with fixed code, while named memory records make client proofs refer to cells by name. These are related design choices: semantic contracts isolate representation details so downstream proofs can describe the algorithm. They do not imply all representations or controllers are equally efficient.

The circuit refactor is documented by [PR #520](https://github.com/cslib-community/cslib-frontier/pull/520). The later named-cell pivot is documented by [issue #2205](https://github.com/cslib-community/cslib-frontier/issues/2205) and [PR #2228](https://github.com/cslib-community/cslib-frontier/pull/2228). The latter completes insertion-related Fibonacci-heap operations, not the full priority-queue refinement: decrease-key and extract-min remain outside that milestone. Their reported proof-size comparisons are historical measurements by the contributors, not benchmarks reproduced in the historical study.

## Module interfaces and build consequences

Lean's module system makes the distinction between public API dependencies and proof-only imports explicit. Source files use `module`, `public import` for dependencies needed by clients, and ordinary imports for proof support. `@[expose]` makes a definition body part of the downstream interface and is used selectively. A proof-only helper can remain private, while the small reusable theorem should live in the lowest suitable topic module. [Module guidance](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/CONTRIBUTING.md#public-surface-under-the-module-system)

This organization affects compilation as well as readability. Adding an exported declaration to a widely imported hub may invalidate clients that never mention it. [Issue #569](https://github.com/cslib-community/cslib-frontier/issues/569) records a historical fan-out investigation and motivated advice to prefer narrowly imported topic modules. Interface stability is not simply textual proof stability: axiom dependencies and `import all` can also affect consumers. The snapshot's source census records imports but does not measure recompilation time.

Before the first supported release the project deliberately avoids accumulating deprecated wrappers: a public rename or relocation updates library clients, tests, abstracts and guides together. This is an explicit tradeoff between present internal coherence and external compatibility. It should not be described as a permanent compatibility promise. [Current file/proof rules](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/AGENTS.md#proof-hygiene)

## Reading design historically

Several decisions evolved during rapid development: strengthening nondeterministic space termination, moving from tidy public contracts to plain ones, separating quantifier-free interpretations from first-order projections, revising word-RAM fault/basis conventions, and replacing a prose theorem list with checked abstracts. The pinned source links identify the surveyed snapshot. A history of why these choices changed must use dated issues or transcripts; current documentation alone cannot establish the original motivation. The [case studies](../development-history/case-studies.md) provide that evidence where available.

This architectural account is a synthesis of the inspected interfaces and policies. It is not a claim that every module already follows the preferred design without exceptions. [complexitylib][complexitylib]

[complexitylib]: ../sources.md#complexitylib
