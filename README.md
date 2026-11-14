# cslib-frontier

cslib-frontier is the frontier formalization library for
[CSLib](https://github.com/leanprover/cslib), written in Lean 4 on top of CSLib and Mathlib. Its
scope is computer science generally: algorithms and data structures, computational complexity,
cryptography, logic, models of computation, and more. It develops reusable arguments about
algorithms, resource bounds, reductions, lower bounds, and cryptographic security, held to CSLib's
standards so that they can move upstream.

A central goal is to let you write recognizable functional programs and prove their efficiency
compositionally, with Turing-machine implementations justified underneath. Nonconstructive
mathematics and model-specific lower bounds also belong. Developments should establish useful
results or make those results easier to state, prove, and reuse.

Development is AI-assisted. Contributors are responsible for the mathematical statements,
source attribution, and maintainability of their changes. Lean checks proofs against their stated
definitions; independent review checks that those definitions and statements express the intended
mathematics. See [Contributing](CONTRIBUTING.md) to propose, implement, or review a development.

## Start here

| I want to… | Start with… |
| --- | --- |
| Learn to use the library, by hand or with an agent | [Operator's Manual](manual/README.md): setup, worked examples, tactics, models and troubleshooting |
| Direct agents working in the library | [Agent Operator's Manual](manual/AGENT_OPERATORS.md): roles, review and handoffs |
| Read checked Lean tutorials | [Guide](https://www.cslib.io/cslib-frontier/guide/) |
| See what an area covers | [Library map](#library-map) below |
| Find a named result, such as Cook–Levin or the PCP theorem | [Results inventory](results/README.md), then the declarations it links in the [API documentation](https://www.cslib.io/cslib-frontier/) |
| Find a model, definition or mathematical tool | [Search the API documentation](https://www.cslib.io/cslib-frontier/search.html), rebuilt nightly from `main`; [CslibFrontier.lean](CslibFrontier.lean) lists every module |
| Use cslib-frontier in another Lean project | [Add a pinned dependency](#use-from-another-lean-project) |
| Build or edit this repository | [Build a checkout](#build-a-checkout) |
| Propose a substantial new direction | [Open an issue](https://github.com/cslib-community/cslib-frontier/issues/new/choose), as [Contributing](CONTRIBUTING.md#proposing-and-contributing-work) describes; [ROADMAP.md](ROADMAP.md) lists the accepted directions |
| Contribute a result or improve an API | [Contributing](CONTRIBUTING.md) |

### Library map

Each top-level directory of [CslibFrontier/](CslibFrontier) is a library area. The reference
chapters of the Operator's Manual describe its models and main theorems; the checked examples
in [CslibFrontierTests/](CslibFrontierTests) show the APIs in use.

| Area | Covers | Start with |
| --- | --- | --- |
| `Computability/` | Turing machines and other machine models, time and space classes, reductions and completeness, circuits, PCP, query and communication complexity | [Machines and complexity classes](manual/machines-and-classes/index.md) and [circuits and other models](manual/circuits-logic-and-other-models/index.md); examples for [polynomial time](CslibFrontierTests/PolyTimeTactic.lean), [time classes](CslibFrontierTests/TimeClasses.lean), [NP-completeness](CslibFrontierTests/NPCompleteness.lean) and [uniform circuits](CslibFrontierTests/UniformCircuits.lean) |
| `Algorithms/` | Graph, string, flow, optimization, approximation and sorting algorithms, as Lean functions and Word-RAM programs with proved correctness and cost | [Algorithms, memory, and data structures](manual/algorithms-and-memory/index.md); example: [Dijkstra](CslibFrontierTests/Dijkstra.lean) |
| `DataStructure/` | Dictionaries, hashing, priority queues, search trees, sketches and memory specifications | [Dictionaries, hashing and randomized algorithms](manual/algorithms-and-memory/dictionaries-hashing-and-randomized.md); [Count-Min examples](CslibFrontierTests/CountMin.lean) and their [accuracy bound](CslibFrontier/DataStructure/CountMin/Probability.lean) |
| `Crypto/` | Security games, primitives, computational assumptions, reductions and protocols | [Probabilistic programs and cryptography](manual/programs-crypto-and-probability/index.md); examples for [PPT programs](CslibFrontierTests/PPTTactic.lean) and [oracle reductions](CslibFrontierTests/OraclePPT.lean) |
| `Languages/`, `Probability/` | Probabilistic and oracle programs with their semantics, the probability tools they use, and SQL query semantics | [Programs, probability laws, and native realization](manual/programs-crypto-and-probability/programs-and-realization.md); [SQL query semantics](manual/circuits-logic-and-other-models/sql-semantics.md) with [join-size examples](CslibFrontierTests/Languages/SQL/JoinSize.lean) |
| `Privacy/` | Differential privacy | [Protocol models, ideal oracles, and privacy](manual/programs-crypto-and-probability/protocols-and-privacy.md) |
| `Logics/` | Propositional proof systems, constraint satisfaction, and first- and second-order logic over finite structures | [Proof complexity](manual/circuits-logic-and-other-models/proof-systems.md) and [finite-model logic](manual/circuits-logic-and-other-models/finite-model-logic.md); [FO(LFP) and FO(TC) examples](CslibFrontierTests/FOOperators.lean), [Immerman–Vardi](CslibFrontier/Computability/Complexity/ImmermanVardi.lean) |
| `MachineLearning/` | PAC, online and statistical-query learning | [Learning and property testing](manual/circuits-logic-and-other-models/learning-and-testing.md) |
| `GameTheory/` | Strategic games, congestion games, mechanism design and social choice | [Strategic games](manual/algorithms-and-memory/strategic-games.md) and [mechanism design](manual/algorithms-and-memory/mechanism-design.md) |
| `Tactic/` | Automation: `polytime`, `ppt`, `negligible`, `game_trans`, first-order synthesis and others | [Proof automation](manual/design-and-assurance/automation.md) |
| `Foundations/` | General mathematics: data, combinatorics, Boolean analysis, linear algebra and number theory | Cited from the chapters that use it; some modules are destined for Mathlib |

The checked examples use `fun_prop`, `polytime` and `ppt` with explicit encodings and
client-supplied invariants; the deterministic backend builds on Christian Reitwiessner's tidy
machine calculus. For an NP-completeness proof, the
[Clique example](CslibFrontier/Computability/Complexity/Problems/Clique.lean) uses graph
complementation and the [reduction index](CslibFrontier/Computability/Complexity/Reduction.lean)
points to the other proved problems. The [results inventory](results/README.md) collects named
results with checked theorem identifiers and cited sources; its coverage and source audits
remain incomplete.

## Build and use

The package is named `cslib-frontier`; imports begin with `CslibFrontier.`. Most declaration
namespaces begin with `Cslib`, and Turing-machine declarations use `Turing`.

### Build a checkout

Install [Lean and its tools](https://lean-lang.org/install/) (including `elan` and `lake`), Git,
and Python 3.11+. The commands below assume Bash. Elan selects the Lean and Lake version from
[lean-toolchain](lean-toolchain); [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json) record the dependency versions.

```bash
git clone https://github.com/cslib-community/cslib-frontier.git
cd cslib-frontier
scripts/build.sh --wfail --iofail
```

The wrapper restores Mathlib and cslib-frontier caches before invoking `lake build`, then
compiles changed or missing modules. It forwards Lake arguments and its exit status.
`scripts/check.sh` also restores caches before validation. Before using Lean through MCP or
another editor, run `scripts/cache/ensure.sh`; bare `lake` and MCP commands do not call it.
Repeated bootstrap calls for the same checkout state reuse a ten-minute attempt stamp.
Use `scripts/cache/ensure.sh --refresh` to retry immediately. See
[scripts/cache/README.md](scripts/cache/README.md) for how the caches work and what they trust.

Import the specific modules you need. `import CslibFrontier` imports the whole library. To contribute,
follow [CONTRIBUTING.md](CONTRIBUTING.md) and the
[validation sequence](AGENTS.md#validation-sequence).

### Use from another Lean project

APIs are still evolving, so pin a full commit SHA. Choose a revision from the
[commit history](https://github.com/cslib-community/cslib-frontier/commits/main/), and copy the
contents of its `lean-toolchain` into your project's `lean-toolchain`. Use the toolchain from
that same revision when adding or updating the dependency.

For a project using `lakefile.toml`, add the following entry, replacing `<commit SHA>` with the
chosen full SHA:

```toml
[[require]]
name = "cslib-frontier"
git = "https://github.com/cslib-community/cslib-frontier"
rev = "<commit SHA>"
```

CSLib and Mathlib are transitive dependencies. If your project already requires either one,
first align those requirements with the versions in cslib-frontier's `lake-manifest.json` at
the chosen revision.

Then run the commands below from your project directory. When changing existing direct
dependency pins, include those package names in the update command: for example,
`lake update cslib-frontier cslib mathlib` when changing both. Updating only `cslib-frontier`
leaves the other direct dependencies locked.

```bash
lake update cslib-frontier
lake build
```

Commit the resulting `lake-manifest.json` along with the Lake configuration and `lean-toolchain`.
Use the `CslibFrontier.` imports shown in the [checked examples](#library-map).

### Build the documentation

[manual/BUILD.md](manual/BUILD.md) explains how to build the two manuals, the API reference
(doc-gen4), the checked guide (Verso) and the source history dashboard. The **API documentation**
workflow publishes the API reference, guide and dashboard from `main` nightly at
[cslib.io/cslib-frontier](https://www.cslib.io/cslib-frontier/).

## Project information

This repository was the CSLib-based Complexitylib until 2026-11-08, when it was renamed
cslib-frontier and its scope widened from computational complexity theory to computer science
generally ([#3675](https://github.com/cslib-community/cslib-frontier/issues/3675)). Declaration
names did not change. The pre-CSLib
[complexitylib-v1](https://github.com/SamuelSchlesinger/complexitylib-v1) has a different API;
some of its developments remain to be ported. The [manual's history](manual/history/index.md)
keeps the dated record of the complexitylib period.

Modules follow CSLib's APIs, paths, namespaces, and contribution standards so they can move
upstream with the import prefix changed from `CslibFrontier.` to `Cslib.`. Acceptance requires
CSLib review. [ROADMAP.md](ROADMAP.md) lists the accepted directions;
[CONTRIBUTING.md](CONTRIBUTING.md#upstreaming) describes upstreaming and lists live coordination
threads; each module's `-- upstream:` marker records its status.

Source headers retain authorship, module docstrings credit mathematical and formalization
sources, and [references.bib](references.bib) contains the bibliography.
Licensed under [Apache 2.0](LICENSE).
