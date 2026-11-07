# Commands and vocabulary

Run repository commands from its root. The [getting-started exercise](workflows/getting-started.md)
shows the complete first use; [contribution policy](../AGENTS.md#validation-sequence) governs
which evidence is required. A zero exit status means that command's stated scope passed.

| Situation | Command | Result and next step |
|---|---|---|
| Cold editor checkout | `scripts/cache/ensure.sh` | Attempts cache restoration; if imports are still missing, build the affected target or follow the cache guide |
| Check a complete named client | `scripts/build.sh ComplexityTests.NPCompleteness --wfail --iofail` | Builds that client and dependencies; inspect the first error before broadening the build |
| Check library changes and importing clients | `scripts/check.sh --quick` | Checks the manuals, then uses local Git comparison; unsupported layouts fall back to full checks; inspect the reported scope |
| Validate the final source locally | `scripts/check.sh` | Checks the manuals and runs all six Lean gates; any failure prevents treating the run as full validation |
| Add a library module | `lake exe mk_all` | Regenerates the library aggregate; inspect its diff and check the affected client |
| Check aggregate completeness | `lake exe mk_all --check` | Fails if an aggregate is stale; regenerate it and review the change |
| Check manual links and contextual excerpts | `python3 scripts/check_operator_manual.py` | Reports current-source matches and broken links; repair the affected prose or canonical example |
| Check the manual checker | `python3 scripts/test_operator_manual.py` | Runs isolated positive and negative controls; failure identifies a checker regression |
| Generate an editable book | `python3 scripts/build_operator_manual.py` | Writes LaTeX/PDF under ignored `manual/_build/`; inspect changed pages before distributing |
| See isolated worktrees | `scripts/worktree.sh list` | Lists registered work; inspect ownership before takeover or removal |
| Queue an approved PR | `python3 scripts/queue_pr.py <PR> <approved head>` | Queues exactly that head once its required check passes; a refusal names the precondition to fix |
| Check a restacked PR | `python3 scripts/check_restack.py <approved head> <new head>` | Exit 0: the new head is the approved change replayed onto newer `main`, and the approval carries; exit 1: review the printed diffs |

The full validation sequence is maintained in [AGENTS.md](../AGENTS.md#validation-sequence),
and cache behavior in [the cache guide](../scripts/cache/README.md). Commands above call
those same scripts; they do not define an independent validation policy.

## Search before adding an API

The following read-only searches use `rg` (ripgrep). If it is unavailable, use editor
workspace search. After dependencies are present, search all three libraries:

```bash
rg -n 'ComputableInPolyTime' Complexity ComplexityTests .lake/packages/cslib/Cslib
rg -n 'iterate_spec|iterateWith_spec' Complexity .lake/packages/cslib/Cslib
rg -n 'yourCandidateName' Complexity .lake/packages/cslib/Cslib .lake/packages/mathlib/Mathlib
```

A hit gives a source location to inspect, not an interchangeable theorem. Read its full
statement and imports. If there are no hits, check spelling and namespace, related notions,
the [model routes](workflows/finding-results.md) and [upstream coordination](../UPSTREAM.md)
before declaring the API absent.

## Vocabulary

| Term | Meaning in the manual |
|---|---|
| Model | A specified syntax or state space, semantics and resource convention |
| Encoding | The representation of an input or output as a finite word; its length affects bounds |
| Plain computability | The public machine-existence/resource contract; tidy machine machinery stays inside proofs |
| Certificate | A Lean proof of a stated property, such as computation cost; it does not supply unrelated functional correctness |
| Program | Free syntax that can be interpreted with semantics and resource bounds; a PMF alone describes a distribution |
| Native realization | A theorem connecting a program or abstract model to the selected machine interface |
| Uniformity | A single effective construction or machine across inputs/sizes; separate per-size existence is weaker |
| Bridge | A proved translation between specified models, preserving the advertised semantics and charging its overhead |
| Contextual excerpt | Exact code from a linked complete client; imports, namespaces and preceding assumptions remain necessary |
| Validation | The checks actually run on a stated revision, with their scope and outcome |
| Independent review | Inspection by a non-author who did not design or implement the reviewed change |
| Snapshot evidence | A dated source or development observation; it does not automatically describe later revisions |

For the model-specific meaning of time, workspace, error, query cost, circuit size, advice,
adversary access and other resources, use the [model selection table](workflows/choosing-models.md)
and its linked reference chapters. Do not infer one resource convention from another's name.
