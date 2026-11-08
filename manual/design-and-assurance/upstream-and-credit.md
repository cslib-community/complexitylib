# Upstream reuse and source credit

Complexitylib's rule is that reusable modules should be upstreamable to CSLib with only `Complexity.` import-path rewriting, with documented exceptions for general mathematics intended for Mathlib and local scaffolding. Namespaces already follow the intended upstream home: `Turing` for the multi-tape machine development and generally `Cslib` elsewhere. This rule constrains API placement and reuse; it does not assert that upstream maintainers have accepted every candidate. [complexitylib][complexitylib]

## Ownership is recorded in the source

Each module has an upstream marker. At the snapshot, the first marker in each of the 3,896 library files classifies 3,813 as candidates, 60 as vendored, 19 as submitted, three as copied subsets and one as local-only. The three subset strings describe portions of `crei/tidy-universal`; the census preserves them literally rather than forcing them into a newer policy vocabulary. These are source declarations of status at the fixed revision, not live GitHub verification of every upstream PR. [Module census script](../data/census.py)

The pinned `lakefile.toml` and `lake-manifest.json` record the base pin; source markers record pending upstream work and copied revisions; `-- vendored:` comments and module docstrings record local adaptations; and [CONTRIBUTING.md](../../CONTRIBUTING.md#upstreaming) lists live coordination threads. A local copy of unmerged upstream work is permitted only for what the pinned dependency lacks, with original authors and declaration names retained. When the pin incorporates it, the copy should be deleted together with the pin update. Such copies are distinct from original Complexitylib definitions.

## Contributions and source credit

| Stream | Evidence and appropriate credit |
|---|---|
| Lean and Mathlib foundations | Dependency manifest and imports; credit the foundational libraries instead of describing reused mathematics as new formalization |
| CSLib base semantic/model APIs | Pinned CSLib source, including configurations/actions, circuits and semantic infrastructure |
| Christian Reitwiessner's machine/program work | Source authors, copied-branch markers and `-- vendored:` adaptation comments; preserve credit through local adaptations |
| Bolton Bailey's predecessor developments | File headers and explicit port rules for PCP internals, Sipser–Lautemann and containment material |
| Erik Demaine's RAM work and other contributor ports | Original source headers/revisions and documented Word-RAM adaptation; distinguish the model from later local realization/refinement work |
| Mathematical source results | `references.bib`, source locators and statement-to-source mappings; original theorem authors are not interchangeable with formalization authors |
| AI-assisted implementation/review | PR disclosures, session records and agent identities; a shared Git author is insufficient to identify the active agent or all human input |

This table is a provenance taxonomy, not a complete author list. The [module census script](../data/census.py) exports each file's authors field; Git author/coauthor metadata is exported separately. Neither determines an academic authorship order. The manuscript should ask contributors to confirm their specific contributions and should preserve mathematical source credit even when an implementation has been extensively refactored.

## Documented adaptations and open coordination

The current machine calculus uses local adaptations of upstream development, including tape-bound handling and efficient primitives. The universal simulation's later windowed divide-and-conquer construction is explicitly distinguished from a Hennie–Stearns buffered implementation. The Mathlib TM2 bridge and native Word-RAM bridge have their own quantitative scopes; no source-history statement should imply tight resource preservation beyond the proved bounds. [Upstream coordination notes](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/UPSTREAM.md#coordination-before-submission)

The probabilistic free-program interfaces also connect to in-flight CSLib work. Generic RAM and bounded Word-RAM coexist because their value domains, instructions and cost conventions differ. A typed-RAM redesign recorded upstream is not automatically a locally proved bridge. The [algorithm survey](../algorithms-and-memory/index.md) records the current local endpoints rather than inferring them from upstream plans.

## Citation discipline for the eventual manuscript

For each selected theorem, cite both the mathematical source and the exact formal declaration. State the source version and locator, then record material changes to models, quantifiers, encoding, uniformity or bounds. A theorem named after a classical result may intentionally give a class equality instead of its sharp parameterized bound. A newly proved endpoint derived from a recent manuscript needs that manuscript's exact version and a separate account of what has been checked. A conditional theorem remains conditional even when its hypothesis is a familiar conjecture.

The initial source review verified source locations and inspects representative definitions; it does not claim to have re-read every original mathematical paper. Some mathematical attributions are explicitly reported from the pinned implementation's bibliography. Verified external references and their access limitations are centralized in [sources.md](../sources.md). Retain that attribution boundary when using or describing the result.

[complexitylib]: ../sources.md#complexitylib
