# Reference index

[Operator's Manual](README.md) · [Task routes](workflows/index.md) · [Build the documentation](BUILD.md)

The reference chapters describe the library's models, major theorems and bridges, resource
conventions and design. Read them once a [workflow](workflows/index.md) has shown you how to
state and prove a claim, or when you need the exact model behind a theorem. They are maintained
with the code: update the affected descriptions when an interface or theorem contract changes.
The chapters grew from the [2 November 2026 source survey](history/survey.md), and some still
cite source at that pinned revision; a changed claim needs a current source link.

Use the [model map](model-map.md) to locate a model or interface, and the
[API documentation](https://www.cslib.io/cslib-frontier/) for every declaration. The
[results inventory](../results/README.md) lists named results.

## Chapters

| Chapter | Main library areas | Covers |
|---|---|---|
| [Design and assurance](design-and-assurance/index.md) | `Tactic/`, cross-cutting | Architecture, compositional proof APIs, automation, reuse and upstream strategy, testing, trusted boundaries, the results registry and the retired formal abstracts and comparator contracts |
| [Machines and complexity classes](machines-and-classes/index.md) | `Computability/` | Native deterministic, nondeterministic, probabilistic, counting, alternating and oracle machines; alternative machine interfaces; resource definitions and classical completeness and containment theorems |
| [Circuits, logic, and information-access models](circuits-logic-and-other-models/index.md) | `Computability/`, `Logics/`, `Languages/SQL/`, `MachineLearning/` | Circuits and formulas, algebraic and quantum variants, branching programs, decision, query and communication models, finite-model theory, SQL query semantics, learning and proof systems |
| [Probabilistic programs and cryptography](programs-crypto-and-probability/index.md) | `Languages/Probabilistic/`, `Probability/`, `Crypto/`, `Privacy/` | Free programs, oracle and state semantics, native efficiency, security games, reductions, construction theorems and privacy models |
| [Algorithms, memory, and data structures](algorithms-and-memory/index.md) | `Algorithms/`, `DataStructure/`, `GameTheory/` | RAM variants, costed specifications, refinement, memory and oracle implementations, streaming and online models, algorithm endpoints, strategic games and mechanism design |
| [Primary sources](sources.md) | all | Canonical bibliography and evidence provenance |

`Foundations/` holds general mathematics used throughout; its modules are cited from the
chapters that use them.

One section owns each model. BQP is defined through uniform quantum circuits and belongs to
circuits; free program syntax belongs to programs, RAM realization to algorithms. Bridge
discussions link back to both models. Partrec/Primrec and Kolmogorov models belong to machines;
proof automation belongs to design.

The [History](history/index.md) part keeps the dated record from the complexitylib period: the
source survey, the automated-development study and the earlier paper plan.
