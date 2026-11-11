# The 2 November 2026 source survey

[History](index.md) · [Reference index](../index.md) · [Build the documentation](../BUILD.md)

The reference chapters and the [model map](../model-map.md) began as a source survey of
complexitylib, as cslib-frontier was then named, at commit
`13e6a31951bf1c89a1a6258c44f9444aecbbefd8` on 2 November 2026. Its baseline includes a
complete source-file census, 265 curated model and interface entries, 39 primary-source
entries, development statistics and verified short transcript excerpts. The reference chapters
are now maintained with the code; the measurements and accounts of validation on this page remain
fixed to their stated revisions.

## Research questions and coverage

1. What are the library's distinct computational, logical, probabilistic, and specification models? For each, what are the syntax or states, semantics, encodings, resource measures, and relevant quantifiers?
2. Which major theorems are proved over each model, and which bridges between models are proved? What limitations and unresolved endpoints remain?
3. How do programming interfaces, compositional resource proofs, tactics, module boundaries, upstream reuse, and statement audits fit together?
4. What does the available development record show about automation, human direction, agent coordination, review, revisions, timing, build cost, and failures?
5. What evidence is reproducible and potentially publishable, and what remains a private, incomplete, or observational record?

The coverage unit is a model family or behavior-changing variant, not every mathematical declaration. The census records 3,896 library Lean files and 1,094,225 physical lines, plus 1,230 test files and 76 formal-abstract files (the abstracts were retired on 2026-11-08). The model map then contained 115 machine/class/resource entries, 92 circuit/logic/information-access entries, 33 program/crypto entries and 25 RAM/specification/algorithm entries. The original survey associated those entries with 389 distinct source paths. Entries include interfaces as well as models; the count is not a claim of mathematical independence. Existing scope limitations remain visible.

## Evidence rules

Each source claim identifies a declaration and its source evidence; the original survey uses pinned locations. A compiled theorem establishes its Lean statement under its dependencies; correspondence to intended mathematics is a separate assessment. Current policy is evidence of current design, not evidence that the same process governed earlier work. Commit timestamps, observed session spans, tool runtimes, CI durations, aggregate work, and elapsed calendar time are different measurements and will not be substituted for one another.

The chapters distinguish source ownership (upstream, local extension, copied/vendored, or scaffolding) and review evidence (definition inspected, endpoint traced, compiled, primary source checked).

Transcript analysis is restricted to this project and documented predecessor identities. Raw private transcripts stay outside the publishable corpus. Extracted records retain provenance, timestamps and redaction notes, and distinguish human instructions, assistant reports and independently observed tool results. Raw transcript access is separate from the public evidence retained here.

Local and `samuel@desktop` conversation stores are candidate evidence. Copied sessions must be deduplicated. Unmatched sessions, overlapping workers, rebases, squashes and missing transcript coverage remain visible in denominators; commit counts cannot establish a percentage of work performed autonomously.

## Supplementary code

The live manual commands are [check_operator_manual.py](../../scripts/check_operator_manual.py)
and [build_operator_manual.py](../../scripts/build_operator_manual.py). They check the current
checkout and build both books from maintained Markdown and source excerpts. Neither needs
generated research data, private logs or a checkout at the survey revision.

Optional scripts regenerate the [source census](../data/census.py),
[Git chronology](data/git_history.py), and a simple
[index of the maintained model map](../data/coverage.py). The
[public audit](../data/audit.py) reconciles census and Git counts and checks the manual.
See [reproduction instructions](../BUILD.md#regenerating-research-outputs) for inputs and commands.

[Codex](data/session_census.py) and
[Claude](data/claude_census.py) extraction, the
[excerpt verifier](data/transcript_excerpts.py),
[timing analysis](data/analyze.py), and
[history plotter](data/plot_history.py) require the original private
records or their separately retained exports. These scripts do not supply missing desktop records.

Generated inventories, copied dependencies, API responses, plots and validation dumps are not
versioned. The original detailed model ledgers and their one-off audit machinery are retired;
the curated model map and explanatory chapters are the maintained reference. Scripts cannot
reconstruct the semantic judgments behind those chapters. The two small workflow excerpt
registrations are authored checker inputs and remain versioned.

The [citation checker](../data/validate_corpus.py), [book assembler](../data/build_manual.py),
and [LaTeX converter](../data/build_latex.py) operate on the maintained source documents.

## Known Limitations

- The original survey received independent agent reviews of model semantics, source attribution and evidence reproduction. Their scope was the survey and its evidence; they do not certify every mathematical proof.
- Desktop transcripts remain inaccessible. Current-path local Codex records end October 24 UTC, and Claude records end October 30; the source cutoff is November 2 UTC. Other agents, tools, accounts and deleted sessions may also be absent.
- No controlled productivity comparison is implied by development chronology.
- The source checkout is much larger than a line-by-line review can certify; completeness concerns the model inventory, with confidence and coverage recorded explicitly.
- Primary-paper correspondence was checked selectively. Some attributions are reported from source annotations, and novel/surprising endpoints need further specialist mathematical review.
- The shared `.lake` dependencies did not match the manifest pins during validation. Cited dependency sources were independently retrieved at the pinned revisions and blob-checked; the mismatch was not resolved by changing the user's checkout. No new Lean build was performed.
