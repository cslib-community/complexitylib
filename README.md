# Complexitylib

Complexitylib is a Lean 4 library of computational complexity theory, built on
[CSLib](https://github.com/leanprover/cslib) and Mathlib. It develops reusable arguments about
algorithms, resource bounds, reductions, lower bounds, and cryptographic security.

A central goal is to let you write recognizable functional programs and prove their efficiency
compositionally, with Turing-machine implementations justified underneath. Nonconstructive
mathematics and model-specific lower bounds also belong. Developments should establish useful
results or make those results easier to state, prove, and reuse.

Development is AI-assisted. Contributors are responsible for the mathematical statements,
source attribution, and maintainability of their changes. Lean checks proofs against their stated
definitions; independent review checks that those definitions and statements express the intended
mathematics. See [Contributing](CONTRIBUTING.md) to propose, implement, or review a development.

## Start here

The [Operator's Manual](manual/README.md) covers using the codebase by hand or with an agent:
setup, worked examples, tactics, models, design patterns and troubleshooting. The short
[Agent Operator's Manual](manual/AGENT_OPERATORS.md) explains how humans direct agents, choose
roles and manage review and handoffs. The [guide](https://www.cslib.io/complexitylib/guide/)
provides checked Lean tutorials. For a particular task, start below.

| I want to… | Start with… |
| --- | --- |
| Learn to use the library from the beginning | [Operator's Manual](manual/README.md) |
| Direct agents working in the library | [Agent Operator's Manual](manual/AGENT_OPERATORS.md) |
| Use Complexitylib in another Lean project | [Add a pinned dependency](#use-from-another-lean-project) |
| Build or edit this repository | [Build a checkout](#build-a-checkout) |
| Certify functional programs and loops | [PolyTime examples](ComplexityTests/PolyTimeTactic.lean) |
| State P/NP membership or prove a problem NP-complete | [Checked plain examples](ComplexityTests/NPCompleteness.lean), then [Clique](Complexity/Computability/Complexity/Problems/Clique.lean) |
| Construct circuits for polynomial-time function families | [Uniform circuit examples](ComplexityTests/UniformCircuits.lean) |
| Define queries using least fixed points or tuple closure | [FO(LFP), FO(TC), and synthesis examples](ComplexityTests/FOOperators.lean) |
| Move between ordered FO(LFP) queries and native polynomial time | [Immerman–Vardi characterization](Complexity/Computability/Complexity/ImmermanVardi.lean) |
| State deterministic function-time or exact path-counting bounds | [FTIME and SharpTIME examples](ComplexityTests/TimeClasses.lean) |
| Write probabilistic programs or oracle reductions | [PPT examples](ComplexityTests/PPTTactic.lean), [oracle examples](ComplexityTests/OraclePPT.lean) |
| Estimate frequencies in a stream | [Count-Min examples](ComplexityTests/CountMin.lean), then [fixed-query accuracy](Complexity/DataStructure/CountMin/Probability.lean) |
| Find a named result, such as Cook–Levin or the PCP theorem | [Results inventory](results/README.md), then the declarations it links in the [API documentation](https://www.cslib.io/complexitylib/) |
| Find a computational model or mathematical tool | [Search the API documentation](https://www.cslib.io/complexitylib/search.html), rebuilt nightly from `main`; [Complexity.lean](Complexity.lean) lists every module, and each documents its definitions, results, and references |
| Contribute a result or improve an API | [Contributing](CONTRIBUTING.md) |

The checked examples show `fun_prop`, `polytime`, and `ppt` with explicit encodings and
client-supplied invariants. The deterministic backend builds on Christian Reitwiessner's tidy
machine calculus.

For an NP-completeness proof, fix the instance encoding, give a verifier with a polynomial
certificate-length bound, and reduce a known NP-hard problem to yours. Prove the verifier and
reduction map polynomial-time with `fun_prop` or `polytime`, then prove their membership
equivalences. The [Clique example](Complexity/Computability/Complexity/Problems/Clique.lean)
uses graph complementation; the [reduction index](Complexity/Computability/Complexity/Reduction.lean)
points to the other proved problems and their reduction maps. The checked examples state these
claims with plain `ComputableInPolyTime`.

The [results and reference inventory](results/README.md) uses readable Lean commands to collect
named results, with checked theorem identifiers and cited sources; its generated index links each
theorem to the [API documentation](https://www.cslib.io/complexitylib/). Coverage and source
audits remain incomplete.

## Build and use

The package is named `complexitylib`; imports begin with `Complexity.`. Most declaration
namespaces begin with `Cslib`, and Turing-machine declarations use `Turing`.

### Build a checkout

Install [Lean and its tools](https://lean-lang.org/install/) (including `elan` and `lake`), Git,
and Python 3.11+. The commands below assume Bash. Elan selects the Lean and Lake version from
[lean-toolchain](lean-toolchain); [lakefile.toml](lakefile.toml) and
[lake-manifest.json](lake-manifest.json) record the dependency versions.

```bash
git clone https://github.com/cslib-community/complexitylib.git
cd complexitylib
scripts/build.sh --wfail --iofail
```

The wrapper restores Mathlib and Complexitylib caches before invoking `lake build`, then
compiles changed or missing modules. It forwards Lake arguments and its exit status.
`scripts/check.sh` also restores caches before validation. Before using Lean through MCP or
another editor, run `scripts/cache/ensure.sh`; bare `lake` and MCP commands do not call it.
Repeated bootstrap calls for the same checkout state reuse a ten-minute attempt stamp.
Use `scripts/cache/ensure.sh --refresh` to retry immediately. See
[scripts/cache/README.md](scripts/cache/README.md) for how the caches work and what they trust.

Import the specific modules you need. `import Complexity` imports the whole library. To contribute,
follow [CONTRIBUTING.md](CONTRIBUTING.md) and the
[validation sequence](AGENTS.md#validation-sequence).

### Use from another Lean project

APIs are still evolving, so pin a full commit SHA. Choose a revision from the
[commit history](https://github.com/cslib-community/complexitylib/commits/main/), and copy the
contents of its `lean-toolchain` into your project's `lean-toolchain`. Use the toolchain from
that same revision when adding or updating the dependency.

For a project using `lakefile.toml`, add the following entry, replacing `<commit SHA>` with the
chosen full SHA:

```toml
[[require]]
name = "complexitylib"
git = "https://github.com/cslib-community/complexitylib"
rev = "<commit SHA>"
```

CSLib and Mathlib are transitive dependencies. If your project already requires either one,
first align those requirements with the versions in Complexitylib's `lake-manifest.json` at
the chosen revision.

Then run the commands below from your project directory. When changing existing direct
dependency pins, include those package names in the update command: for example,
`lake update complexitylib cslib mathlib` when changing both. Updating only `complexitylib`
leaves the other direct dependencies locked.

```bash
lake update complexitylib
lake build
```

Commit the resulting `lake-manifest.json` along with the Lake configuration and `lean-toolchain`.
Use the `Complexity.` imports shown in the [checked examples](#start-here).

### Build the documentation

Run the following commands from the repository root. For a cold checkout, first restore the
available caches with `scripts/cache/ensure.sh`.

#### API reference

To build searchable API documentation from the module docstrings:

```bash
python3 scripts/check_docs.py --config-only
lake -d docbuild build Complexity:docs
python3 scripts/check_docs.py
python3 -m http.server --bind 127.0.0.1 --directory docbuild/.lake/build/doc
```

Open `http://localhost:8000` to browse and search. The **API documentation** workflow publishes
`main` to the [API documentation site](https://www.cslib.io/complexitylib/) nightly.
A manual run on another branch produces an `api-docs` artifact instead; serve it by replacing
the directory argument above with the extracted artifact directory.

If removing a source module leaves `check_docs.py` reporting obsolete modules, rebuild the
generated documentation after any documentation build has stopped:

```bash
lake -d docbuild clean docbuild
lake -d docbuild build Complexity:docs
python3 scripts/check_docs.py
```

The named clean removes only `docbuild/.lake/build`, including HTML, per-module data and the
SQLite database; deleting HTML alone leaves stale data behind. Library and dependency build
outputs, package checkouts and Lake's artifact cache are retained. Documentation for all imported
modules is regenerated, which can take substantial time even with warm library build outputs.

#### Checked guide

The [guide](guide/ComplexityGuide.lean) introduces the library area by area, with Lean examples
that are checked against the library whenever the guide is built. It is written with
[Verso](https://github.com/leanprover/verso) in a separate `guide` project. To build and preview it:

```bash
scripts/guide.sh
python3 -m http.server --bind 127.0.0.1 --directory guide/.lake/build/site/html-multi
```

The first build compiles Verso and links the guide's generator, which takes a few minutes. The
**API documentation** workflow publishes the guide from `main` with the API documentation, at
[/guide/](https://www.cslib.io/complexitylib/guide/). The **Guide** workflow builds
pull requests that change the guide and uploads the pages as a `guide` artifact.

## Project information

This is the canonical CSLib-based Complexitylib. The renamed historical
[pre-CSLib implementation](https://github.com/SamuelSchlesinger/complexitylib-v1) remains available
with archival pending; it has a different API, and some developments remain to be ported. The temporary
repository and package name `complexitylib2` was retired when this repository moved to CSLib
Community. Downstream projects using that package name should change it to `complexitylib`; Lean
imports remain unchanged.

Modules follow CSLib's APIs, paths, namespaces, and contribution standards so they can move
upstream with the import prefix changed from `Complexity.` to `Cslib.`. Acceptance requires
CSLib review. [ROADMAP.md](ROADMAP.md) records outstanding work;
[UPSTREAM.md](UPSTREAM.md) records upstream coordination and exceptional integration decisions.

Source headers retain authorship, module docstrings credit mathematical and formalization
sources, and [references.bib](references.bib) contains the bibliography.
Licensed under [Apache 2.0](LICENSE).
