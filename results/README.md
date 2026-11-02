# Results and reference inventory

The canonical collection is [Entries.lean](../ComplexityResults/Entries.lean): readable Lean
commands with real theorem identifiers. This is the initial collection for
[#2012](https://github.com/cslib-community/complexitylib/issues/2012), not a complete inventory
or a claim that every cited paper is fully formalized.
Initial collection: Christian Reitwiessner, with Codex assistance.

The collector reuses the selected groups in [the abstract catalogue](../abstracts/catalogue.json)
and adds eight Lean-authored groups: oracle counting lowness, first-order model checking in L,
NL ⊆ P, PPZ and Schöning success bounds, the OV-to-SAT transfer, and native sparsification.
The catalogue continues to own abstract titles, scopes and theorem selections. The bibliography
remains [references.bib](../references.bib); neither is copied into another authored manifest.

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

`ComplexityResults` is a separate local documentation library, included in the default
`lake build` targets. Mathematical modules do not import the registry. Compiled environment
entries survive imports and are exported by [ExportResults.lean](../scripts/ExportResults.lean).
JSON is generated output; there is no hand-maintained `registry.json`.

## Reading and checking

Run from the repository root:

```bash
lake build ComplexityResults
python3 scripts/results_registry.py                  # collection and bibliography checks
python3 scripts/results_registry.py --markdown         # results grouped by topic
python3 scripts/results_registry.py --papers           # grouped by cited bibliography key
python3 scripts/results_registry.py --json             # generated combined inventory
python3 scripts/results_registry.py --compiled         # original public-theorem metadata
```

The generated Markdown contains declaration links, scope notes, recorded source theorem names
or numbers, additional locators, bibliography links and optional abstract PDFs. Library entries
link to API documentation; abstract entries link to their Lean sources, since their modules are
not part of the published API documentation. Source links follow `main`, so proposed entries
appear there after integration.

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
- **`module-citations`**: bibliography keys extracted from an abstract's documentation. They may
  describe background, definitions, alternative proofs or several results. These context
  references have no per-theorem source identifier; grouping by them is a discovery aid, not a
  claim that every theorem formalizes every cited work.

The abstracts retain their checked bridges and review requirements. Reference integrity proves
neither mathematical correspondence nor completeness. A result's hypotheses and model limits
remain authoritative. Probability bounds do not imply certified native runtime, and conditional
results are not unconditional endpoints.

## Remaining collection work

Collect precise paper-to-result correspondences and source theorem names/numbers, audit their
sources, and expand coverage across the library. Algorithms, cryptography, proof complexity,
circuit bounds, communication and descriptive complexity contain substantial additional results.
Catalogue entries currently share the topic “selected abstracts”; finer classification remains
open. Original results without external sources need an explicit representation before adding
them. Publication and search are also tracked in #2012. Passing compilation and reference checks
does not complete these objectives.
