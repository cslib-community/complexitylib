# Maintain and review both manuals

The Operator's Manual serves humans and agents working in the codebase. Its acceptance goal
is operational: a Lean-literate human can select the intended
model, find and apply its API, diagnose a failed proof, validate a change and prepare a
reviewable contribution using the checked-out source and ordinary development tools.
Readability and complete context are part of that goal. A list of declaration names alone
is not an operating procedure.

The [Agent Operator's Manual](AGENT_OPERATORS.md) serves the human directing agents. Its
acceptance goal is that the human can assign a clear task, obtain trustworthy review, recognize
when to intervene and preserve a useful handoff. It links to codebase procedures in the
Operator's Manual rather than repeating them.

## Assess the change

For every PR, assess both manuals and identify affected reader tasks and pages. Changes to public declarations,
models, encodings, hypotheses, resource bounds, automation, imports, dependency setup,
validation, review or upstream procedures can change what a reader must do or may claim.
Update affected manuals and canonical examples alongside the implementation. For each manual
whose readers are unaffected, record a specific no-impact reason, such as a proof-only refactor
with identical statements, imports and automation behavior. The [repository policy](../CONTRIBUTING.md)
defines the required assessment, mandatory coordinator review of both manuals and independent
review of affected content.

Keep one source of truth. Explain the task here; link to current [policy](../AGENTS.md),
[cache documentation](../scripts/cache/README.md), [guide](../guide/CslibFrontierGuide.lean),
module docstrings and complete tests for their details. Do not copy a new body of Lean code
into this manual without a checked source client. The workflow snippets are contextual
excerpts, each declared in `workflows/data/*-excerpts.json`. They retain source authorship
and require the linked client's imports, namespace and local assumptions.

A new page also needs a place in the book. Add a reference or history chapter to `ORDER` in
[build_latex.py](data/build_latex.py), or a workflow or appendix page to `WORKFLOWS` or
`APPENDICES` in [build_manual.py](data/build_manual.py), and link it from an existing page.
A new reference section goes before the final `history` entry of `ORDER`; a page
deliberately kept out of the book belongs in `NON_CHAPTER_DOCUMENTS` in `build_manual.py`.
Chapter order is an editorial choice, so the lists are maintained by hand; the checker
reports any page missing from them.

Model diagrams and worked-example panels are part of the maintained account. Review the
meaning of every changed arrow and resource label against the referenced definitions; keep
missing implementation or uniformity obligations visible. Panels should make the goal, context,
result and recovery easy to find while preserving the canonical excerpt. Follow the
[source conventions](BUILD.md#maintain-diagrams-and-worked-examples); generated graphics stay
with the untracked book products.

## Check the affected reader path

1. Read the changed instructions using only the repository and its declared tools. Check
   that the entry page leads to the task, prerequisites, command, expected result and next step.
2. Open the complete client. Verify that the model, encoding, hypotheses and resource claim
   agree with the explanation; inspect a meaningful edge or failure case.
3. Run `python3 scripts/check_operator_manual.py` and `python3 scripts/test_operator_manual.py`.
   The checker validates local paths and Markdown anchors, source line anchors (each starts a
   declaration and, when its link text names a declaration of the linked file, that one), visual
   markup, lists that would print as running text (a list item directly after a paragraph line),
   the book's chapter lists, excerpt registration and unique exact excerpt matches in
   current source; its controls exercise failure and recovery.
   Both are required in CI and run before Lean work in full and quick `scripts/check.sh` modes.
   They need only Python, without publishing tools or regenerated research data. Inserting unrelated
   lines above an excerpt is allowed. Changing, removing or duplicating its text needs attention.
   A relative source link such as `File.lean#L120` or `File.lean#L120-L180` must also start where
   the cited text starts: an unindented declaration (after modifiers such as `private` or
   `noncomputable`), an `@[…]` attribute or a `/--` docstring, outside any comment. A range may
   instead start at `/-!`, `section` or `namespace`, and `#L1` links a whole file. An edit that
   adds or removes lines above an anchored declaration, even inside a proof, moves it: run
   `python3 scripts/check_operator_manual.py --fix-anchors` to repoint `[Ns.name](File.lean#Ln)`
   links at the current header line of the declaration they name, and find any remaining prose,
   range or ambiguous links with `git grep -n 'File.lean#L' manual/` to update by hand.
   `STALE_SOURCE_ANCHORS` in the checker lists links that are stale, or that queued pull requests
   will make stale, and tolerates them until those pull requests land
   ([#3991](https://github.com/cslib-community/cslib-frontier/issues/3991)); repointing one of
   those links needs no edit to the list.
4. When Lean examples or their imports change, check the complete affected source clients under
   the [validation policy](../AGENTS.md#validation-sequence). The documentation checker is not
   a Lean build. Existing hosted validation can cover unchanged examples at the same revision.
5. When publishing either book or changing its converter/layout, follow [BUILD.md](BUILD.md),
   inspect the affected rendered pages and check the build log. A prose edit need not force a
   whole-library rebuild or a new full-book layout review.

The coordinator checks both manual-impact assessments and ensures independent review covers
the final change against the source and affected tasks, including the evidence for each
no-impact decision. Review the human agent-driving route when roles, task assignment, review,
handoffs, intervention or permissions change; review the codebase route when its APIs or
operating procedures change. A passing link check cannot approve
mathematical meaning, usability, completeness or whether a no-impact reason is sound.
Record any missing route or prerequisite as a concrete defect, not an instruction to ask an
agent to fill it in.

## Preserve the research record

The model reference began as a source survey at `13e6a319`. Keep its pinned evidence when it
still supports the claim; revise a changed claim with a current source link and scope note.
Source identity is evidence, not agreement with a textbook definition. Preserve source credit,
conditional hypotheses, bounded milestones and unresolved broader objectives.

The [history](history/index.md) measurements and quantitative census are historical. New
measurements belong to a separately dated observation with defined coverage, units and denominators. Keep
their scripts and methods in the repository; write generated exports, API responses, dependency
copies and plots to ignored directories, as described in [BUILD.md](BUILD.md#regenerating-research-outputs).
The small excerpt registrations are handwritten source inputs and stay versioned. Maintain
semantic judgments in the chapters and model map rather than in generated inventories.

The optional fixed-snapshot audit is described with the
[survey's supplementary code](history/survey.md#supplementary-code). It is not a merge check
against the moving repository and must not be run as a substitute for the live manual checker.
Public Git evidence can be regenerated from complete history; private logs and the original
mutable GitHub responses are separate reproduction requirements.
