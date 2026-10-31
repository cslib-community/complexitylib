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

The [guide](https://www.cslib.io/complexitylib/guide/) introduces the library through checked Lean
examples. For setup or a particular task, start below.

| I want to… | Start with… |
| --- | --- |
| Use Complexitylib in another Lean project | [Add a pinned dependency](#use-from-another-lean-project) |
| Build or edit this repository | [Build a checkout](#build-a-checkout) |
| Compare selected proofs with independently stated contracts | [Comparator suites](comparator/README.md) |
| Certify functional programs and loops | [PolyTime examples](ComplexityTests/PolyTimeTactic.lean) |
| State P/NP membership or prove a problem NP-complete | [Checked plain examples](ComplexityTests/NPCompleteness.lean), then [Clique](Complexity/Computability/Complexity/Problems/Clique.lean) |
| Construct circuits for polynomial-time function families | [Uniform circuit examples](ComplexityTests/UniformCircuits.lean) |
| Define queries using least fixed points or tuple closure | [FO(LFP), FO(TC), and synthesis examples](ComplexityTests/FOOperators.lean) |
| State deterministic function-time or exact path-counting bounds | [FTIME and SharpTIME examples](ComplexityTests/TimeClasses.lean) |
| Write probabilistic programs or oracle reductions | [PPT examples](ComplexityTests/PPTTactic.lean), [oracle examples](ComplexityTests/OraclePPT.lean) |
| Estimate frequencies in a stream | [Count-Min examples](ComplexityTests/CountMin.lean), then [fixed-query accuracy](Complexity/Algorithms/Streaming/CountMin/Probability.lean) |
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

The [results and reference inventory](results/README.md) collects named results, exact Lean
declarations and cited sources, including results without formal abstracts. It is an initial,
incomplete collection with CI-checked declaration references.

The [selected formal abstracts](abstracts/README.md) present a small set of major results with
inspectable definitions and checked Lean statements. The [combined PDF](https://www.cslib.io/complexitylib/abstracts/catalogue.pdf)
and individual PDFs are generated from those sources. Each states its model and limitations;
the selection is not an exhaustive API reference.

## Selected results

* [Cook–Levin: SAT is NP-complete](abstracts/ComplexityAbstracts/CookLevinAbstract.lean): Every efficiently checkable bit-string problem reduces in polynomial time to satisfiability.
* [The PCP theorem](abstracts/ComplexityAbstracts/PCPAbstract.lean): NP proofs can be checked with logarithmic randomness and constantly many nonadaptive queries.
* [Fagin: logic captures NP](abstracts/ComplexityAbstracts/FaginAbstract.lean): Existential second-order logic captures precisely the isomorphism-invariant NP properties of finite relational structures.
* [Savitch: NPSPACE equals PSPACE](abstracts/ComplexityAbstracts/SavitchAbstract.lean): Nondeterminism does not enlarge polynomial space.
* [Reingold: undirected reachability is in L](abstracts/ComplexityAbstracts/USTCONAbstract.lean): Undirected graph connectivity can be decided with logarithmic work space.
* [Immerman–Szelepcsényi: nondeterministic space is closed under complement](abstracts/ComplexityAbstracts/ImmermanSzelepcsenyiAbstract.lean): Nondeterministic space at least logarithmic is closed under complement; in particular NL equals coNL.
* [Shamir: IP equals PSPACE](abstracts/ComplexityAbstracts/ShamirAbstract.lean): Interaction and randomness give a polynomial-time verifier the power of polynomial space.
* [Toda: a counting oracle decides the polynomial hierarchy](abstracts/ComplexityAbstracts/TodaAbstract.lean): Every problem in the polynomial hierarchy is decidable in polynomial time with an exact counting oracle.
* [Barrington: five states capture NC¹](abstracts/ComplexityAbstracts/BarringtonAbstract.lean): Polynomial-length permutation programs on five states capture logarithmic-depth polynomial-size Boolean circuits.
* [Håstad and Razborov–Smolensky: parity resists shallow circuits](abstracts/ComplexityAbstracts/ConstantDepthAbstract.lean): At fixed depth, parity requires more than polynomially many gates, including over an odd-prime modular basis.
* [Braverman: polylogarithmic independence fools AC⁰](abstracts/ComplexityAbstracts/BravermanAbstract.lean): k-wise independence with k = (log(m/ε))^O(d²) fools every depth-d circuit of NOT and unbounded fan-in AND/OR gates with size and fan-in at most m, to within error ε.
* [Formula lower bounds: parity and Andreev](abstracts/ComplexityAbstracts/FormulaBoundsAbstract.lean): Tree-shaped computation pays for repeated work: parity requires quadratic leaf size, and Andreev gives a stronger explicit bound.
* [Limaye–Srinivasan–Tavenas over any field (after Forbes): constant-depth algebraic circuits for IMM need superpolynomial size](abstracts/ComplexityAbstracts/ConstantDepthArithmeticAbstract.lean): Over every field, constant product-depth simple algebraic circuits computing iterated matrix multiplication of ⌊log₂ ⌊log₂ n⌋⌋ generic n × n matrices need more than n^c gates for every c and all large n.
* [One-way functions yield pseudorandom generators and adaptive functions](abstracts/ComplexityAbstracts/CryptographyAbstract.lean): One-wayness yields pseudorandomness, from an extra output bit to functions secure against adaptive oracle queries.
* [Gentry and GSW: fully homomorphic encryption from LWE](abstracts/ComplexityAbstracts/GSWFHEAbstract.lean): Bootstrapping the GSW scheme gives leveled fully homomorphic encryption from decision LWE, and fully homomorphic encryption under an additional circular-security assumption.
* [Haken: pigeonhole formulas require long resolution proofs](abstracts/ComplexityAbstracts/ResolutionAbstract.lean): The pigeonhole principle has short CNF statements but requires exponentially many resolution lines.
* [Communication: disjointness and inner product resist randomness](abstracts/ComplexityAbstracts/CommunicationAbstract.lean): Both problems require linearly many communicated bits even with shared randomness and bounded error.
* [Sipser–Gács–Lautemann: BPP lies in the second polynomial level](abstracts/ComplexityAbstracts/SipserLautemannAbstract.lean): Bounded-error polynomial time admits both existential–universal and universal–existential polynomial descriptions.
* [Chor–Goldreich: the inner product extracts from two weak sources](abstracts/ComplexityAbstracts/ChorGoldreichAbstract.lean): Two independent weak random sources whose min-entropies add up to more than the string length give a nearly fair bit through the inner product modulo two.
* [OpenAI: the Exponential Time Hypothesis is false](abstracts/ComplexityAbstracts/SubexponentialSATAbstract.lean): For each fixed clause width, one deterministic machine exactly counts satisfying assignments in subexponential time and polynomial space; every fixed-width SAT exponent is zero, and ETH and SETH are false.
* [Ilango: Partial MCSP is hard under the Exponential Time Hypothesis](abstracts/ComplexityAbstracts/PartialMCSPAbstract.lean): Under ETH, deciding circuit size for partial Boolean functions cannot be done in time 2^o(m log m) = N^o(log log N). *Note (October 2026):* the native formalization now [proves ETH false](abstracts/ComplexityAbstracts/SubexponentialSATAbstract.lean). This conditional entry is retained and its theorem remains valid, but its premise is false.
* [McKay–Murray–Williams: barely superlinear circuit lower bounds for MCSP separate P from NP](abstracts/ComplexityAbstracts/MagnificationAbstract.lean): If NP has polynomial-size circuits, then MCSP on 2^n-bit truth tables has circuits of size 2^n poly(n + s(n)); hence barely superlinear MCSP lower bounds separate NP from P/poly and P from NP.

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

### Compare theorem statements and proofs

The optional [comparator suites](comparator/README.md) compare selected library proofs with
independently stated contracts using `lake comparator --paranoid`. They cover reduction and
circuit facts, two `polytime` proofs, and the fixed-width SAT counting and ETH endpoints.
The guide explains the Linux sandbox requirement, the trusted definitions, and how to run a
negative control that submits a valid proof of the wrong statement.

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
