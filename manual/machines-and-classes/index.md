# Machines and complexity classes

Complexitylib's machine layer connects a concrete multitape operational model to higher-level verification, counting, interaction, search, and description-complexity models. The strongest common feature is that semantic definitions and efficiency claims are separate: a Lean function or free program acquires a native complexity bound only through a machine-realization theorem. This chapter describes those contracts at the pinned snapshot, including variants whose acceptance semantics or resource accounting differ. [complexitylib][complexitylib]

The underlying cslib machine contributes read-only input, two-way work tapes, append-only output, and independent time and visited-work-cell bounds. Complexitylib extends that core to fair randomness, branch multiplicity, alternation, and oracle channels; it also connects cslib's single-tape model and Mathlib's TM0, TM1, TM2, and partial-recursive machinery. These bridges have different preservation strengths: some are step-exact, some polynomial, and some concern only eventual computation. [cslib][cslib]

## Reading path

- [Native machines and resource contracts](native-and-resources.md) explains configurations, uniformity, choice semantics, output charging, and randomized logspace.
- [Intermediate interfaces and other Turing formalisms](intermediate-and-legacy.md) covers StepMachine, ReadMachine, QueryMachine, counter programs, single-tape machines, TM0/TM1 and TM2.
- [Verifiers, counting, and interaction](verifiers-counting-interaction.md) covers NP/PH, randomized and counting predicates, oracle programs, MA/AM, IP/MIP, and PCP.
- [Search relations and promises](search-and-promises.md) covers FNP/TFNP, PLS/PPP/PPAD/PPA and promises, with their distinct totality contracts.
- [Major endpoints and quantitative boundaries](endpoints-and-hierarchies.md) records completeness, containment, hierarchy, and oracle results with their actual scope.
- [Native exact counting and SAT endpoints](native-counting.md) records the unconditional fixed-width counter, encodings, independent resource bounds, manuscript mapping and ETH/SETH consequences.
- [Computability and description methods](computability-and-description.md) covers universal descriptions, halting, Rice, partial recursion, Post's correspondence problem, Kolmogorov models, and their different clocks.
- [Parameterized complexity and kernelization](parameterized-complexity.md) covers FPT/XP quantifiers, parameter-respecting reductions, kernel contracts and the native vertex-cover kernel.
- [Reductions and information access](reductions.md) covers many-one refinements, polynomial-time and logspace truth tables, adaptive oracle reductions, autoreducibility and fine-grained transfer.
- The [model map](../model-map.md) links each model or acceptance/resource variant to its explanatory chapter.

The intended unit is a model family. Counting-class variants receive individual records because their acceptance predicates differ, although they share a verifier machine. Polynomial/exponential bounds and complementary classes are described as derived families, not invented as new operational machines. We do not enumerate every problem reduction or every auxiliary finite-state simulator.

## Cross-chapter boundaries

Free program syntax and stateful probabilistic interpretation are owned by [programs and cryptography](../programs-crypto-and-probability/index.md); this chapter owns the native efficiency and classical interactive-proof contracts. RAM and memory-access models belong to [algorithms and memory](../algorithms-and-memory/index.md). Circuits, algebraic and quantum circuits, branching programs, query complexity and finite-model logic belong to [circuits and logic](../circuits-logic-and-other-models/index.md). In particular, `BQP` is defined by `Quantum.UniformCircuitFamily` in [Classes/BQP.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/BQP.lean#L13), so this snapshot does not introduce a quantum Turing machine through that definition.

The Kolmogorov/average-case-hardness interface crosses into cryptography; the clock and description semantics are recorded here, while cryptographic equivalences and heuristic quantifiers belong to the programs/cryptography chapter. The architecture and migration of the compositional proof calculus belong to [design and assurance](../design-and-assurance/index.md).

## Evidence and attribution

This is a source inspection, not a new Lean build. Definitions, selected endpoint statements, relevant proof connections and representative tests were read. The inventory records tests as inspected source; none is labeled newly compiled in this chapter. The original survey checked source identities, declaration locations and captured digests. Those historical checks do not prove inventory completeness or mathematical correctness.

The shared dependency checkouts did not match the manifest pins. Referenced upstream files were retrieved independently at the pinned commits, captured with Git blob hashes, and used to regenerate source locations and digests. The chapters link the pinned upstream sources directly; copied dependency files are not retained in the manual. No compilation claim uses the mismatched working dependencies.

Source ownership is recorded per file. The native core is inherited from pinned cslib; Christian Reitwiessner's vendored tidy/universal and step-machine work is retained with its authorship. The PCP and Sipser–Lautemann ports credit Bolton Bailey and Samuel Schlesinger. Mathlib model bridges retain their own declared contributors. These are source-header observations; they do not establish the amount of individual or automated labor.

No independent quantum TM, Cobham algebra, or Bellantoni–Cook safe-recursion model was found in the assigned source routes. Unused models merely available in transitive dependencies are not counted as locally developed models. Broad source-to-literature equivalence is not implied by a familiar class name: the detailed pages record differences such as output-charged space, reduction-defined SL, the restricted hierarchy gaps, and the described-machine clock for Kolmogorov complexity.

## Maintaining the reference

Update the explanatory pages and [model map](../model-map.md) together when a model changes.
The former machine-readable ledger and its one-off audit reports are not maintained inputs.
The [manual checks](../../scripts/check_operator_manual.py) check links and registered Lean
excerpts; semantic and source-to-statement review remains necessary.

[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
