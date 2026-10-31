# Results and reference inventory

This is the first collection for [#2012](https://github.com/cslib-community/complexitylib/issues/2012),
not a complete inventory of the library or a claim that every cited paper is fully formalized.
Initial collection: Christian Reitwiessner, with Codex assistance.

The collector reuses all 22 selected groups in [the abstract catalogue](../abstracts/catalogue.json)
and adds eight groups in [registry.json](registry.json): oracle counting lowness, first-order
model checking in L, NL ⊆ P, PPZ and Schöning success bounds, the OV-to-SAT transfer, and native
sparsification. The existing catalogue owns abstract titles, scopes and theorem selections; they
are not copied into a second manifest. The bibliography remains [references.bib](../references.bib).

Run from the repository root:

```bash
python3 scripts/results_registry.py                  # IDs, modules and bibliography references
python3 scripts/results_registry.py --markdown         # results grouped by topic
python3 scripts/results_registry.py --papers           # results grouped by cited bibliography key
python3 scripts/results_registry.py --compiled         # built public-theorem references
```

The generated Markdown contains declaration links, scope notes, recorded source locators,
bibliography links, and optional abstract PDFs. Library declarations link to the API docs;
abstract declarations link directly to their Lean sources because their modules are not part
of the published API documentation. Source links follow `main`, so a proposed entry becomes
available there after integration.

The compiled check requires the registered modules to have been built. CI runs it after the
library and tests, using the same Lean output reader as the existing declaration audits. It
rejects missing or renamed declarations, private declarations, definitions or axioms presented
as theorems, and declarations attributed to the wrong module. Static checks reject unknown
bibliography keys, missing modules, invalid IDs and duplicate theorem registrations.

## What the references mean

- **`recorded`**: the initial collector inspected the Lean statement and copied the citation and
  locator from existing repository documentation. This collection does not provide a new
  independent check against the original paper. A null locator means that a precise locator
  has not yet been collected; it must not be filled by guessing.
- **`module-citations`**: bibliography keys extracted from an abstract's documentation. They may
  describe background, definitions, alternative proofs or several distinct results. Grouping by
  these keys is a discovery aid, not a claim that each theorem formalizes every cited source.

The abstracts retain their existing checked bridges and review requirements. The registry
checker establishes reference integrity; it establishes neither mathematical correspondence
nor completeness. A result's explicit hypotheses and model restrictions remain authoritative.
In particular, probability bounds do not imply certified native runtime, and a conditional
result is not an unconditional endpoint.

## Remaining collection work

Collect precise paper-to-result correspondences and locators, record their source review, and
audit coverage across the library. Algorithms, cryptography, proof complexity, circuit bounds,
communication and descriptive complexity contain substantial additional results beyond this
seed. The topic index currently groups catalogue-derived entries under “selected abstracts”;
more detailed topic classification remains to be collected. Original results without an
external source need an explicit representation before adding them. Publication and search are
also tracked in #2012. None of these gaps is satisfied merely by a passing reference check.
