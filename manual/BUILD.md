# Build the two manuals

Read the Markdown without any publishing tools. The default build produces the substantial
Operator’s Manual; `--agent-manual` selects the short Agent Operator’s Manual for humans
driving agents. To check the maintained source, run these commands from the repository root
with Python 3.11+:

```bash
python3 scripts/check_operator_manual.py
python3 scripts/test_operator_manual.py
```

CI and both full and quick `scripts/check.sh` runs require these checks. They need no PDF
tools, Lean build or generated research data, and do not replace independent review of the
manuals' meaning and usability.

To produce the books, also install Pandoc, XeLaTeX and `pdfinfo` (Poppler).
The main book's model diagrams require
Graphviz (`dot`); the short agent manual does not invoke it. The TeX installation needs
`fontspec`, `fvextra`, `xurl`, `bookmark`, `microtype`, `fancyhdr`, `etoolbox`, `tcolorbox` and the usual
AMS/graphics/table packages, plus TeX Gyre Pagella, TeX Gyre Heros and DejaVu Sans Mono fonts.
The converter uses the font filenames shipped by TeX Live. Dependencies are local commands;
the build script does not download tools or invoke Lean.

From the repository root:

```bash
python3 scripts/build_operator_manual.py
python3 scripts/build_operator_manual.py --agent-manual
```

Outputs share the ignored `manual/_build/` directory and have distinct names:

| Book | TeX/PDF filename stem | Source manifest |
|---|---|---|
| Operator’s Manual | `cslib-frontier-operators-manual` | `manual-source-manifest.json` |
| Agent Operator’s Manual | `cslib-frontier-agent-operators-manual` | `agent-manual-source-manifest.json` |

Neither book needs research exports or historical plots. The short book contains only
[AGENT_OPERATORS.md](AGENT_OPERATORS.md) and its policy/source links; it carries no academic
bibliography or historical figure. Each manifest records the selected manual, source revision,
working-tree status and exact input hashes. It is build provenance, not validation of the
mathematical statements. The main build renders model diagrams from the Markdown into
`figures/` beside its TeX. Each generated TeX file is editable and compiles independently with
XeLaTeX; retain those figure PDFs with the main book's TeX file.

Before distributing an existing book, check that its chapter and bibliography inputs still
match the current manual:

```bash
python3 scripts/build_operator_manual.py --check-build manual/_build
python3 scripts/build_operator_manual.py --agent-manual --check-build manual/_build
```

Each check needs only Python and validates the selected manual. It fails for missing chapters,
changed input text or converters, stale bibliography contents, missing or altered diagrams,
or altered generated TeX/PDF. A build that produces only TeX does not certify
an older PDF left in the output directory. Rebuild after such changes and inspect the
affected pages. A passing live link/excerpt check alone does not validate an older PDF.
Bibliography bodies are read directly from canonical `sources.md`.

Without local publishing tools, use the **Operator's Manual PDFs** workflow. It runs on pull
requests that change `manual/` or the manual scripts, and can also be started by hand. It builds
and checks both books from the pull request's head commit, and its run summary links an artifact
containing both PDFs and their source manifests.

To generate TeX with its diagram assets, or select another output directory:

```bash
python3 scripts/build_operator_manual.py --tex-only
python3 scripts/build_operator_manual.py --output-dir /tmp/cslib-frontier-manual-book
```

The second path is an example destination that you choose. No files in that directory are
removed automatically. For repeated independent TeX compilation, run XeLaTeX three times
from the output directory so the contents and citations stabilize. Generated links to repository
files outside the selected book point to GitHub at the rendered commit; the PDF can be moved
without retaining the checkout. Push that commit before sharing the PDF. Links within the book
remain internal anchors, and source Markdown keeps its checkout-relative links. The builder
rejects links to uncommitted or locally modified repository targets: commit those targets first
so the linked content matches the source being reviewed. Uncommitted book prose can still be
rendered when its external source targets are committed. A successful builder exits
zero; the full build also prints the PDF metadata. Inspect the output for missing glyphs,
unresolved references, clipped lines and unreadable tables before distributing it.

Edit the Markdown and regenerate for maintained changes. Do not commit generated TeX, PDF,
logs, research exports or auxiliary files. The source files and converters are sufficient to reproduce the book.
The Operator’s Manual includes the workflows, full reference, historical study and bibliography;
it links to the separate short manual without duplicating that manual’s content. Both builds omit
link-only navigation paragraphs. The original academic paper plan remains in
[paper-plan.md](paper-plan.md) as historical editorial context.

Coordinator review must cover the impact on both manuals before integration. When either
manual changes, check its rendered pages and retain its matching manifest when distributing
the artifact. A shared converter change requires checking both editions. See
[the maintenance procedure](MAINTAINING.md) and the
[contribution policy](../CONTRIBUTING.md#maintaining-the-manuals).

## Maintain diagrams and worked examples

Model diagrams live in `mermaid` code fences in the reference pages. GitHub renders them
directly; the PDF builder reads the same source and uses Graphviz to produce vector figures.
Keep the fences unindented and at the top level, outside lists and blockquotes; nested
diagrams are rejected. Generated asset paths preserve the source directory hierarchy.
The supported flowchart subset is deliberately small: start with `flowchart TB` or
`flowchart LR`; define each rectangular node separately as `input["Input value"]`; use
`input -->|"encoded by"| output` for a labelled edge or `input --> output` without a label.
The dotted form is `input -.->|"needs a certificate"| output`. Identifiers use letters,
digits and underscores and start with a letter. Labels are quoted plain text with optional
`<br/>` line breaks. Define both endpoints; do not use subgraphs, styles, clicks or inline
node definitions on edges. The checker rejects unsupported syntax instead of omitting it.
The renderer supplies consistent typography, colours and arrow styles. Explain the meaning
and limits of arrows in the adjacent prose; an arrow must not imply an unstated realization
or resource theorem.

Wrap an existing worked example using these source markers and a plain bold title:

```text
<!-- worked-example -->
**Worked example: A descriptive task title**

Ordinary Markdown, including the existing contextual excerpt and its source link.
<!-- /worked-example -->
```

Keep headings outside the markers and do not nest panels. In Markdown the title and example
remain ordinary readable text. The PDF numbers examples within their chapter and gives them
a shaded panel, a contrasting title and a continuation label when they cross a page.
State the goal, required context, result and likely failure or recovery. Keep the Lean excerpt
unchanged unless its checked source client changes. The live checker verifies panel boundaries
and diagram syntax as well as excerpt identity; it does not establish diagram semantics.

Generated figure PDFs and the source manifest stay in the ignored build directory. The
freshness check includes figure hashes, so replacing or losing a figure requires a rebuild.

## Regenerating research outputs

The historical study reports a fixed observation at `13e6a319`, dated November 2, 2026.
Its scripts are optional tools for inspecting the evidence; running them is not a prerequisite
for reading or building either manual. Outputs default to the ignored `manual/_generated/`
directory. Keep generated JSON, API responses, dependency copies and plots out of commits.
The maintained chapters and [model map](model-map.md) hold the semantic account; the scripts
do not reconstruct the retired detailed model ledgers or repeat their mathematical review.

With Git history through the fixed revision available locally, run from the repository root:

```bash
python3 manual/data/audit.py .
```

This writes the source census under `_generated/data/`, the Git chronology under
`_generated/development-history/data/`, a navigation index derived from the maintained model
map, and `_generated/audit.json`. A successful audit reports `"status": "pass"`: the first-parent
net line count agrees with the source census, daily commit totals agree with the history, and
the current manual passes its link, excerpt and citation checks. It does not compile Lean or
audit mathematical completeness. It does not fetch missing Git objects; if history is missing,
supply a complete checkout as the positional argument instead of `.`. To export just the
navigation index, run `python3 manual/data/coverage.py`.

The timing analysis additionally requires the original private logs and GitHub observations.
These are not included in the repository. With authorized access to the original logs, choose
a private output directory outside the checkout and replace the example paths below:

```bash
python3 manual/development-history/data/session_census.py /path/to/codex/sessions --private-output /private/path/manual-provenance
python3 manual/development-history/data/claude_census.py /path/to/claude/projects --private-output /private/path/manual-provenance
python3 manual/development-history/data/transcript_excerpts.py /private/path/manual-provenance
```

The two censuses write aggregate and timing exports to the ignored history directory and
source-path provenance to the selected private directory. The excerpt verifier checks the
22 handwritten selections against those originals. Compressed Codex `.zst` logs require
Python 3.14's standard-library support or the optional `zstandard` package. Missing originals mean these private measurements cannot be
reproduced; the public Git audit remains usable.

An installed, authenticated GitHub CLI can collect the selected public records:

```bash
python3 manual/development-history/data/collect_github.py
```

The collector makes read-only requests and records retrieval timestamps. Use
`--select issue_569`, for example, to retrieve one record. These are new observations:
comments, PR states, reruns and retention may have changed, and expired CI records cannot be
recovered by this script. Refetching does not recreate the original response bytes or guarantee
the study's historical totals.

Once the required census, Git, private-session and GitHub exports are present, run:

```bash
python3 manual/development-history/data/analyze.py
python3 manual/development-history/data/plot_history.py --data-only
python3 manual/development-history/data/plot_history.py
```

Analysis reads `_generated/development-history/data/`; plotting also reads the source census
under `_generated/data/` and writes JSON, SVG and PNG under
`_generated/development-history/figures/`. The final command requires Matplotlib. Use
`--data-dir` for another history directory, and the plotter's `--census-dir` and `--output`
for other census and figure directories. A missing-input error means an earlier extraction
is absent; do not substitute empty data. Neither generated analysis nor plots are book inputs.
