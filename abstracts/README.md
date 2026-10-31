# Selected formal abstracts

The catalogue promotes a small set of major result groups, listed in the table below. Each has a
checked Lean abstract with the definitions needed to understand its statement, a bridge to the
library proof, and an audited dependency boundary. Some abstracts also allowlist a few library modules for foundational models
(for example circuit signatures or oracle runs); each such abstract names them in its docstring, and
a reader must inspect them as well. The generated PDFs present the mathematical definitions and
selected statements first, followed by exact representation details and any shared foundations in
appendices. Proof bodies are omitted. Lean checks the proofs; independent review must still check
their intended meaning.

The [combined PDF](https://www.cslib.io/complexitylib/abstracts/catalogue.pdf)
and individual PDFs are built by the **Formal abstract PDFs** workflow and published from main on
the documentation site under `https://www.cslib.io/complexitylib/abstracts/`. PR builds
provide review artifacts with checked-out and PR-head revisions. Publication requires integration;
a newly proposed entry may not yet appear on the published site.

Lean sources live in `abstracts/ComplexityAbstracts/`, built as the dedicated `ComplexityAbstracts`
library (`lake build ComplexityAbstracts`). The library root imports every abstract and bridge;
`lake test` also runs their audits and the regression tests in `ComplexityTests/Abstracts/`.
Existing declaration namespaces are preserved; the catalogue records them separately from
module names when needed. Generated products remain in the ignored `abstracts/build/` folder.

## Selection

A headline must establish a substantial full endpoint with conventional, inspectable semantics,
hypotheses that are satisfiable or are standard open assumptions stated as such (such as the
existence of a one-way function), explicit models and encodings, and honest quantitative bounds. The
catalogue does not promote a partial construction, assumed core reduction, bounded experiment or
helper API as a standard theorem. Many useful library results remain outside this selection. The
former paper/TeX index is retired; Git history retains its sources.

| Result | Model and scope |
| --- | --- |
| [Cook–Levin: SAT is NP-complete](ComplexityAbstracts/CookLevinAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/cook-levin.pdf) | Explicit CNF encoding, total native-machine reductions, and UNSAT coNP-completeness. |
| [The PCP theorem](ComplexityAbstracts/PCPAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/pcp.pdf) | Perfect completeness, soundness at most one half, and explicit native efficiency; construction constants are large. |
| [Fagin: logic captures NP](ComplexityAbstracts/FaginAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/fagin.pdf) | Finite relational signatures, explicit encodings, empty universes and nullary relations. |
| [Savitch: NPSPACE equals PSPACE](ComplexityAbstracts/SavitchAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/savitch.pdf) | Native machines and polynomial space; this abstract states class equality rather than a parameterized quadratic-space bound. |
| [Reingold: undirected reachability is in L](ComplexityAbstracts/USTCONAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/reingold.pdf) | Explicit unary-size header and adjacency-matrix encoding; native logspace, without a reduction-defined SL corollary. |
| [Immerman–Szelepcsényi: nondeterministic space is closed under complement](ComplexityAbstracts/ImmermanSzelepcsenyiAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/immerman-szelepcsenyi.pdf) | One finite-state native machine per problem, every-prefix work space c₁ s(n) + c₂ for any s with log₂ n ≤ s(n), no constructibility assumed, every branch terminating, arbitrary injective encodings; directed non-reachability on unary-header adjacency matrices as a corollary. |
| [Shamir: IP equals PSPACE](ComplexityAbstracts/ShamirAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/shamir.pdf) | All prover strategies are quantified explicitly, with a uniform native clock and specified completeness and soundness. |
| [Toda: a counting oracle decides the polynomial hierarchy](ComplexityAbstracts/TodaAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/toda.pdf) | Witness counts and oracle bit answers are explicit; correctness holds for every extension of valid oracle answers. |
| [Barrington: five states capture NC¹](ComplexityAbstracts/BarringtonAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/barrington.pdf) | Nonuniform circuits and permutation programs; no uniform generator or compiler runtime is asserted. |
| [Håstad and Razborov–Smolensky: parity resists shallow circuits](ComplexityAbstracts/ConstantDepthAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/constant-depth.pdf) | Explicit finite bounds, gate semantics and depth conventions; nonuniform lower bounds. |
| [Braverman: polylogarithmic independence fools AC⁰](ComplexityAbstracts/BravermanAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/braverman.pdf) | Arbitrary distributions with uniform marginals on every set of at most k positions; explicit bound with our own constants and exponent, weaker than Braverman's; size and depth count NOT gates and constants; one parameter q bounds the size, the fan-in and log₂ of the inverse error; nonuniform and information-theoretic. |
| [Formula lower bounds: parity and Andreev](ComplexityAbstracts/FormulaBoundsAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/formula-bounds.pdf) | De Morgan formulas, literal leaves, explicit block indexing and finite quantitative bounds; no general-circuit lower bound. |
| [Limaye–Srinivasan–Tavenas over any field (after Forbes): constant-depth algebraic circuits for IMM need superpolynomial size](ComplexityAbstracts/ConstantDepthArithmeticAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/constant-depth-arithmetic.pdf) | Any field, formal polynomials, unbounded fan-in sum and product gates, product gates reading distinct wires, size counting all gates; explicit non-asymptotic bound with exponent d^(1/(4^Δ-1)); constant product-depth Δ and the single value d = ⌊log₂ ⌊log₂ n⌋⌋; nonuniform. |
| [One-way functions yield pseudorandom generators and adaptive functions](ComplexityAbstracts/CryptographyAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/cryptography.pdf) | Uniform probabilistic polynomial time with explicit native evaluators, negligible advantage and full stateful oracle semantics; asymptotic security, not a concrete implementation audit. |
| [Gentry and GSW: fully homomorphic encryption from LWE](ComplexityAbstracts/GSWFHEAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/gsw-fhe.pdf) | Explicit GSW algorithms at an LWE family with quasi-polynomial modulus, the GSW key law for the leveled scheme's fresh ciphertexts and Gentry's self-loop key; an existential evaluator, remaining key chain and decryption circuits with correctness, fixed widths, uniformly generated polynomial-size decryption circuits, native algorithms and IND-CPA; circular security as a separate hypothesis. |
| [Haken: pigeonhole formulas require long resolution proofs](ComplexityAbstracts/ResolutionAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/resolution.pdf) | The non-onto pigeonhole formula and a line-based resolution rule, with bound 2^(floor(n/24)); proof size is not solver runtime. |
| [Communication: disjointness and inner product resist randomness](ComplexityAbstracts/CommunicationAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/communication.pdf) | Shared randomness, per-input error at most one third and explicit linear bounds; exact deterministic equality records the final-answer convention. |
| [Sipser–Gács–Lautemann: BPP lies in the second polynomial level](ComplexityAbstracts/SipserLautemannAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/sipser-lautemann.pdf) | Fair random bits, explicit quantifier blocks and total native polynomial-time tests. |
| [Chor–Goldreich: the inner product extracts from two weak sources](ComplexityAbstracts/ChorGoldreichAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/chor-goldreich.pdf) | Arbitrary sources with real min-entropy bounds, the exact bias bound and its strong form, sharpness at k1 + k2 = n; information-theoretic. |
| [OpenAI: the Exponential Time Hypothesis is false](ComplexityAbstracts/SubexponentialSATAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/subexponential-sat.pdf) | One fixed native machine per width, exact model counts, and interpolation-scale time with polynomial overhead and polynomial space in the encoded formula length; all SAT exponents zero and ETH/SETH false. §§3–6 and Proposition 6.4, not the sharper Theorem 1.1 / Appendix D bound. |
| [Ilango: Partial MCSP is hard under the Exponential Time Hypothesis](ComplexityAbstracts/PartialMCSPAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/partial-mcsp.pdf) | Explicit 3SAT and PartialMCSP encodings (unary and binary thresholds), De Morgan all-gates and binary-gate costs, and deterministic multi-tape lower bounds 2^o(m log m) = N^o(log log N) plus NP membership. *Note (October 2026):* the native formalization now [proves ETH false](ComplexityAbstracts/SubexponentialSATAbstract.lean). This conditional entry is retained and its theorem remains valid, but its premise is false. |
| [McKay–Murray–Williams: barely superlinear circuit lower bounds for MCSP separate P from NP](ComplexityAbstracts/MagnificationAbstract.lean) · [PDF](https://www.cslib.io/complexitylib/abstracts/magnification.pdf) | Plain De Morgan circuits counting all operation gates, decision MCSP[n^k] on N = 2^n-bit truth tables in standard binary order, and native multi-tape P and NP; conditional magnification from a size lower bound at some arity per exponent. |

## Generate and review PDFs

With Python 3.11+, `latexmk`, Poppler utilities and a TeX distribution containing Libertine,
newtxmath, Inconsolata (`zi4`), microtype, tcolorbox and the usual LaTeX extras:

```bash
python3 -B scripts/build_abstracts.py --check
python3 -B scripts/build_abstracts.py
```

On Debian/Ubuntu, the workflow installs `latexmk`, `lmodern`, `poppler-utils`, `texlive-latex-extra`,
`texlive-fonts-extra` and `texlive-plain-generic` without recommended packages, and caches the
downloaded archives. Outputs go to `abstracts/build/`:
individual PDFs, `catalogue.pdf`, generated TeX, and `provenance.json`. They are untracked. Use `--require-clean`
for publication builds; a local build with edits records dirty-source digests and labels links as
pointing to the base revision.

Run the Lean validation sequence in [CONTRIBUTING.md](../CONTRIBUTING.md), including `lake test`,
before accepting changed abstracts. Independently compare the abstract and bridge against the
final implementation: quantifiers, machine model, encodings, resource bounds, satisfiability of
premises and mathematical source credit. Inspect every rendered page for legibility and clipping,
verify exact declaration links, and record the reviewed source revision and artifact/run. The
provenance identifies source files, bridge files, their digests, PDFs and selected declarations;
it supplements these reviews rather than replacing them.

Site publication additionally requires successful **Lean Action CI** and **Formal abstract PDFs**
runs for the exact artifact source SHA, from a `push` to `main` in this repository. Before staging
the documentation site, `scripts/check_abstract_ci.py` waits up to 20 minutes for both runs, selects
each workflow's latest run and current attempt, and rejects missing, failed, cancelled, mismatched
or still-pending validation. It then downloads the exact `formal-abstracts-<sha>-<attempt>` artifact
and verifies `provenance.json` and every PDF's SHA-256 digest before staging `abstracts/*.pdf` and
`abstracts/provenance.json` into the deployed Pages tree. PR PDF review artifacts remain available
without publication, and no second Lean or TeX build is started during documentation deployment.

This gate preserves the exact-source CI and provenance guarantees recorded in
[#432](https://github.com/cslib-community/complexitylib/issues/432) and
[#673](https://github.com/cslib-community/complexitylib/issues/673). Its workflow identity,
event/SHA filtering, pagination and attempt handling follow the
[GitHub workflow-run REST API](https://docs.github.com/en/rest/actions/workflow-runs).

## Layout and sources

The source section `/-! ## Representation details ... -/` marks definitions and explanations
to display in an appendix. The group ends at the next `##` section heading. Its definitions are
retained in full; selected theorem statements must remain in the main presentation. These are
presentation conventions in comments, not new Lean syntax.

An entry using shared definitions lists their modules in its `foundations` array, for example
`["ComplexityAbstracts.Encoding", "ComplexityAbstracts.Computation"]`. The list must exactly match
the abstract's direct foundation imports and their transitive foundation imports. The audit helper
and proof bridges are excluded from that display check; Lean's `#check_abstract` still checks the
actual elaborated dependency boundary, including dependencies of allowed definitions. A listed
foundation cannot be another abstract or bridge, and missing, duplicate, unused or cyclic
foundation modules fail validation.

Individual PDFs include the needed foundations with their definitions, theorem signatures,
namespaces and source links. The combined catalogue displays each foundation once, after the
selected abstracts. `provenance.json` records each foundation's source digest and declaration
links, and a source change during rendering invalidates the build. Single-file Markdown and TeX
previews also include imported foundations and identify their local source digests. Moving a
definition to an appendix does not establish an encoding-invariance or model-equivalence theorem;
any such change still needs a checked correspondence in Lean.

The typography, syntax colors and pale code boxes adapt Erik Demaine and Stefan Langerman’s
[translation-tiling paper style](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/paper.texlish)
and [Lean snippet extraction workflow](https://github.com/edemaine/translation-tiling-paper/blob/5309313e662377d2efb353acba454859469606bd/figures/extract_lean_snippets.py).
No logo is copied. Mathematical sources and earlier formalizations are credited in each Lean
abstract and its implementation. The local [lean-abstract skill](../.agents/skills/lean-abstract/SKILL.md)
describes the statement/bridge discipline and the limits of `#check_abstract`.
