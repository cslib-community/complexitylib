# Design and assurance

cslib-frontier combines several mathematical models through explicit interpretation and resource theorems. Its characteristic engineering choice is to make ordinary functional or oracle programs the client interface, then discharge their cost through reusable certificates for concrete machines. No single notion of computation subsumes every circuit, probabilistic, logical or memory model in the library. The model sections document those distinctions; this section explains how the interfaces are organized and checked.

- [Architecture and design decisions](architecture.md): semantic layers, encoding, resource accounting, module boundaries, and migration.
- [Proof automation and client interfaces](automation.md): an index of the tactics by goal, certificate search, loop rules, word-RAM execution, circuit construction and logical synthesis.
- [Assurance and trust](assurance.md): builds, axiom audits, the results registry, semantic review and the retired formal abstracts and comparator contracts.
- [Upstream reuse and source credit](upstream-and-credit.md): dependency identity, copied code, general mathematics, original contributions and attribution.

## Architectural reading order

Read the native [machine/resource conventions](../machines-and-classes/native-and-resources.md) before interpreting claims of polynomial time or logarithmic space. Read [program semantics and realizability](../programs-crypto-and-probability/programs-and-realization.md) before cryptographic reductions. For algorithms, the important distinction is between a costed specification, its controller, and its RAM implementation; the [algorithm section](../algorithms-and-memory/index.md) gives the model-specific details. Circuit cost and uniformity have their own [interfaces](../circuits-logic-and-other-models/index.md).

The architecture consists of explicit proved connections. In particular, an oracle-call bound is not a native runtime theorem; a denotational PMF is not automatically a realizable sampler; an existential circuit family is not automatically uniformly generated; and an axiom audit is not an audit of the meaning of a theorem. These distinctions recur across otherwise different subjects and are central to explaining the library coherently.

## Relation to CSLib

CSLib's founding paper proposes a common Lean infrastructure for computer science, while its semantic-spine paper describes reusable reduction and labelled-transition interfaces, automation and CI support. cslib-frontier is a substantial client of that project, spanning algorithms, complexity, cryptography, logic and other models of computation, and also a staging area for proposed upstream extensions. The library does not independently originate Lean, Mathlib, CSLib's base models, or all of the program calculus it adapts. [barrett26][barrett26] [henson26][henson26]

The upstreamability rule is a design target with documented exceptions, not a statement that every file has already passed upstream review. At the [survey snapshot](../history/survey.md) the library depended on CSLib `254e30e6d4299c51323aaeaf5f51a4763b375d4a` and Lean `v4.36.0-rc2`; the complete manifest remains in the pinned repository and the source census can be regenerated ([source census script](../data/census.py)). The current pins are in [lake-manifest.json](../../lake-manifest.json) and [lean-toolchain](../../lean-toolchain).

## Scope of this assessment

This section began as an inspection of definitions, interfaces, selected proof dependencies and repository policy at the [survey's fixed revision](../history/survey.md). Hosted CI supplies build evidence for that revision; no new Lean compilation was performed during the initial source review. The current checkout’s policy documents govern contributions. The [development history](../history/development.md) separately investigates what the available record shows actually happened.

[barrett26]: ../sources.md#barrett26
[henson26]: ../sources.md#henson26
