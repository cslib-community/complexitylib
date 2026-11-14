<!-- Keep the description proportional to the change. See AGENTS.md#writing-in-issues-and-prs.
Start directly with prose or choose headings that help explain this particular change. -->

<!-- What changes, why, and which issue does it address?
Write for a contributor who has not followed the task: introduce the setting, central idea and
what the result enables before relying on specialized terms or Lean names. For a substantial
development, explain how the main steps connect and why consequential choices are needed.
Use an example, equation or before/after comparison when it helps the reader.
For mathematical changes, state the claim and important assumptions. Where relevant, explain
the source-to-Lean mapping or why existing definitions could not be reused.
For API/reuse refactors, identify a representative caller and what it no longer repeats;
follow AGENTS.md#check-the-api-through-its-callers.
New or changed statements follow AGENTS.md#encodings-in-statements; explain any exception.
For each headline (AGENTS.md#faithful-headlines), say whether it states the cited result or is
original; a conditional or restricted stand-in is named and documented as a step or helper, leaves
the cited objective open, and is never presented as the cited result in the title, description or
inventory (a "Limitations" list does not substitute for this). Name any stand-in this change
supersedes and removes.
Computational security theorems follow AGENTS.md#security-theorems: they assume only named
hardness assumptions, the adversary's class and properties of components the cited result takes as
given, never anything about a reduction, simulator or extractor that the proof constructs, and
each reduction has an efficiency witness (`isPPT_…`, `isOraclePPT_…` or a circuit-size bound). -->

Authors of new files: <!-- the issue's originator(s) (its "Originated by" field, else its
author) and the person whose agents did the work, as in AGENTS.md#file-rules. Delete if no file is
added. -->

## Manual impact

<!-- Required for every change: assess both the Operator's Manual and Agent Operator's Manual.
Link updated sections and checked examples, or give a concrete reason no edit is needed for
one or both manuals. Coordinators must ensure independent review of this assessment against
the final revision. See CONTRIBUTING.md#maintaining-the-manuals. -->

## Validation

<!-- Give checks and outcomes, or link existing CI/review evidence. State material limitations.
For library changes, link the duplication notices for the reviewed revision and record resolutions
of relevant candidates (or link the existing explanation), including skipped/incomplete coverage.
For manual changes, include relevant excerpt/link checks, Lean example checks and rendered-page
inspection. Record the manual review with the code review rather than duplicating it here.
Omit items that do not apply; do not claim review that has not happened. -->

## AI assistance

<!-- Name the tools and how they were used, or say none. -->
