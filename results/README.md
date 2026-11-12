# Results and reference inventory

The canonical collection is [Entries.lean](../CslibFrontierResults/Entries.lean): readable Lean
commands with real theorem identifiers. This is the initial collection for
[#2012](https://github.com/cslib-community/cslib-frontier/issues/2012), not a complete inventory
or a claim that every cited paper is fully formalized.
Initial collection: Christian Reitwiessner, with Codex assistance.

The collection includes the headline results that the curated formal abstracts selected until
they were retired on 2026-11-08, registered against the library theorems that the abstracts'
bridges applied, except the depth-two threshold bounds for Andreev's function: they are original
results, which wait for a representation (see "Remaining collection work"). Their bibliography
keys come from the library modules' citations; their source theorem numbers and locators are left
`unverified`. The bibliography remains [references.bib](../references.bib); it is not copied
into another authored manifest.

The [Arora–Barak 2007 draft audit](arora-barak-2007.md) records a source-pinned chapter-level
coverage comparison, including missing endpoints, partial matches and source/model problems.
Its chapters 8–10 record distinguishes constant-round protocols, counting-oracle interfaces
and quantitative crypto bounds. Its Chapter 14 record includes a checked degree obstruction to the draft's literal
circuit-to-determinant statement; it is not a claim of book-wide coverage.

The [Goldreich draft audit](goldreich-2007.md) records a source-pinned chapter-level coverage comparison
for *Computational Complexity: A Conceptual Perspective*; it is not a claim of book-wide coverage.

## Authoring

For example, an entry records the source paper's theorem name or number separately from its
section/page locator:

```lean
register_result "first-order-logspace" where
  title := "Fixed first-order queries are decidable in logarithmic space"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 3.1", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.Vocabulary.queryLanguage_mem_L,
    Cslib.Logic.FO.Definable.queryLanguage_mem_L
  ]
  scope := "Fixed relational first-order sentences; inspect the full entry's model restrictions."
```

This is an excerpt illustrating the syntax; the full entry preserves the precise scope.
Source identifiers come from recorded repository documentation, not a new primary-source audit.
Use `unverified` explicitly when a source theorem name/number or locator has not been collected.
Do not guess an identifier or use a section number as if it were a theorem number.

Ordinary Lean name resolution provides editor navigation and fails compilation for missing
imports or renamed declarations. The command also rejects private names, non-propositions,
repeated IDs/references and theorem lists spanning different defining modules. It derives fully
qualified names and module ownership; these are not maintained as duplicate strings.

`CslibFrontierResults` is a separate local documentation library, included in the default
`lake build` targets. Mathematical modules do not import the registry. Compiled environment
entries survive imports and are exported by [ExportResults.lean](../scripts/ExportResults.lean).
JSON is generated output; there is no hand-maintained `registry.json`.

## Reading and checking

Run from the repository root:

```bash
lake build CslibFrontierResults
python3 scripts/results_registry.py                  # collection and bibliography checks
python3 scripts/results_registry.py --markdown         # results grouped by topic
python3 scripts/results_registry.py --papers           # grouped by cited bibliography key
python3 scripts/results_registry.py --json             # generated combined inventory
python3 scripts/results_registry.py --compiled         # original public-theorem metadata
```

The generated Markdown contains declaration links into the API documentation, scope notes,
recorded source theorem names or numbers, additional locators and bibliography links. Links
follow `main`, so proposed entries appear there after integration.

The reader refuses stale registry outputs before exporting. CI additionally uses the existing
Lean output reader to check original declaration kind, public visibility and module ownership
for the combined inventory. This matters under Lean's module system: an imported theorem and
an unexposed proof-valued definition can both appear as axioms in the exported environment.
Elaboration checks name visibility and proposition types; the original-kind audit distinguishes
theorems from proof definitions and actual axioms. Bibliography keys are checked against the
current bibliography by the Python validator, rather than frozen when a Lean module is compiled.

## What the references mean

- **`recorded`**: the collector inspected the Lean statement and copied its citation and source
  identifier/locator from existing repository documentation. This is not a new independent
  check against the original paper. Generated `source_theorem` and `locator` fields are nullable;
  null corresponds to the explicit Lean `unverified` marker.

Reference integrity proves neither mathematical correspondence nor completeness. A result's
hypotheses and model limits remain authoritative. Probability bounds do not imply certified native
runtime, and conditional results are not unconditional endpoints.

## Remaining collection work

Collect precise paper-to-result correspondences and source theorem names/numbers, audit their
sources, and expand coverage across the library. Algorithms, cryptography, proof complexity,
circuit bounds, communication and descriptive complexity contain substantial additional results.
Original results without external sources need an explicit representation before adding
them. Publication and search are also tracked in #2012. Passing compilation and reference checks
does not complete these objectives.

The original [accepted-certificate measure example](../CslibFrontier/Computability/Circuit/Boolean/FormalComplexityMeasure/Certificate.lean)
is also awaiting representation for source-free results. A singleton has measure `n` while at
least half the truth tables have measure zero. This explains why the additive `-n` in
Razborov–Rudich Theorem 5.1(b) cannot simply be omitted as in the 2007 Arora–Barak draft's
Theorem 22.3. It is not registered as a proof of either source theorem; the corrected density
amplification endpoint remains open under [#4711](https://github.com/cslib-community/cslib-frontier/issues/4711).
