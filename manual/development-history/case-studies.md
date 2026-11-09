# Development case studies

These cases were chosen to explain distinct mechanisms: semantic failure, editorial correction, API simplification, model selection and infrastructure maintenance. They are not a representative sample from which to estimate failure or productivity rates. Public issue/PR sources are linked directly; selected private utterances were checked by the excerpt extractor during the survey. Generated API responses are not versioned.

## Accepted proofs with the wrong advertised endpoint

[Issue #372](https://github.com/cslib-community/cslib-frontier/issues/372) documents a serious October 22 audit of recently merged work. It identifies results whose hypotheses assumed the advertised conclusion, computational constructions that relied on noncomputational choice/inversion, and protocol models that restricted an adversary so strongly that the advertised security claim no longer followed. The issue records a maintainer instruction to delete unsuitable results and correct claims. [Issue #372](https://github.com/cslib-community/cslib-frontier/issues/372)

The recorded examples include a Regev-related quantum step exposing existence of short vectors as an oracle, an OT model whose malicious adversary could not express relevant deviations, circuit-collapse assumptions that already contained the difficult conclusion, and a purported satisfiability probability lacking the claimed connection to a CNF construction. These are the historical audit's diagnoses. This dossier does not present them as defects still present in the final snapshot; later deletions and replacement developments must be assessed separately.

[Issue #392](https://github.com/cslib-community/cslib-frontier/issues/392) continues the removal/correction work, including a bootstrappability interface that assumed the content it purported to establish. This episode is valuable for the paper because ordinary proof acceptance is entirely compatible with proving a weak, vacuous or misdescribed statement. An automatic reviewer can reproduce the author's mistaken model rather than catch it. The countermeasure is source-to-statement review with quantifier order, adversary power, realizability and nonvacuity inspected explicitly.

The subsequent transcript contains the human direction to recover the ambitious goals and to encode the actual theorem rather than rush a restricted substitute (excerpts e11–e13). The current [cryptography survey](../programs-crypto-and-probability/index.md) assesses later GSW/FHE interfaces under their explicit assumptions and limits. Historical withdrawal is evidence of a process failure and correction; it neither invalidates all later work nor certifies its recovery.

## Curating formal abstracts

On October 22 at 21:30:38 UTC the user asked for inspection of claim accuracy and drift from human intent (e07). The conversation then requested comprehensible formal abstracts, a higher threshold for headlines, and a smaller selection replacing the prose/TeX list (e08–e10). This is direct evidence that editorial scope was human-directed.

The snapshot's implementation had a 25-group Lean catalogue with presentation/bridge files, dependency audits and generated PDFs. The [assurance section](../design-and-assurance/assurance.md#retired-formal-abstracts-and-comparator-contracts) describes what those checks established and why the abstracts were retired on 2026-11-08 in favor of the results inventory. It would be inaccurate to say that the transcript proves every headline was subsequently verified by a human. It establishes the decision and the requested standard; source and CI established the mechanism.

## Circuit synthesis: removing bookkeeping while retaining costs

The October 23 session began with a request for structural simplification. At 17:07:10.575 UTC the user selected automatic tracking of available wires (e01–e02), then asked whether the abstraction could introduce subtle circuit inefficiencies (e03). PR #520 introduced `Synthesis.Builder` and a tactic for applying an explicitly chosen construction while locating its inputs.

The public PR reports eleven refactored proofs across six modules, 154 fewer client lines, and 54 fewer library lines after counting the new infrastructure, with 57 regression lines added. These are contributor-reported scope measurements; the PR's overall additions/deletions include a different set of files and should not be confused with those subcounts. The mathematical contract preserves statements and gate bounds, charges shared constructions once, and adds no gates for wire lookup. [PR #520](https://github.com/cslib-community/cslib-frontier/pull/520), [PR #520](https://github.com/cslib-community/cslib-frontier/pull/520)

The user then asked whether the result was clear to a human reader (e05), and later withdrew interest in general budget-guided synthesis (e06). The assistant report distinguishes checking a requested budget from automatically selecting the cheapest construction (e04), consistent with the current tactic source. This case shows both automation of proof plumbing and human control over feature scope. The measured request-to-merge interval was 1h28m11.425s, but it depends on an existing circuit library and cannot measure the cost of creating that library.

## RAM models and named memory cells

The October 20 Claude conversation compared existing RAM approaches, then explicitly directed integration of both definitions and preservation of original contributor credit (e15–e17). The resulting library keeps unbounded-natural RAM, GenericRAM and bounded Word-RAM semantics distinct. Later simulation and uniformity theorems establish particular connections; those bridges should not be projected backward onto the state of the library at the time of this conversation.

By November 1, [issue #2205](https://github.com/cslib-community/cslib-frontier/issues/2205) records a maintainer-directed pivot to oracle programs and refinement to reduce Word-RAM proof plumbing. It includes source-specific proof-size measurements and repeated update/frame operations. These are recorded diagnostic measurements, not independent measurements repeated here. [Issue #1764](https://github.com/cslib-community/cslib-frontier/issues/1764) similarly motivates named fields over long positional projection chains.

PR #2228 is a concrete partial result of that approach: named-record proofs for Fibonacci-heap `isEmpty`, `getKey` and insertion. Its body reports 1,011 hand-stepped proof-body lines versus 255 plus 39 generic record lines for the compared operations. That comparison is task-specific and contributor-reported. The full indexed priority-queue refinement awaits decrease-key/extract-min and is not completed by this insertion milestone. [PR #2228](https://github.com/cslib-community/cslib-frontier/pull/2228)

## Build cost, cache evidence and abandoned metrics

The October 23 build-ergonomics conversation asked both for compilation improvements and preservation of potentially useful worktree changes before cleanup (e18–e20). The final architecture includes cache bootstrap, shared remote artifacts, isolated mutable outputs and merge-group reuse. These mechanisms can reduce redundant compilation, but their presence does not quantify net time saved.

[Issue #569](https://github.com/cslib-community/cslib-frontier/issues/569) records an import-fan-out study at an earlier 1,850-module snapshot and explains why adding small APIs to hubs can have a large build cost. [Issue #1197](https://github.com/cslib-community/cslib-frontier/issues/1197), still open in the retrieved record, calls for a kill switch, trace evidence and measured net benefit for cache handoff machinery. The pinned measurement guide explicitly separates dormant measurement infrastructure from an authorized experiment. No such experiment was activated for this review.

The quality programme in [issue #587](https://github.com/cslib-community/cslib-frontier/issues/587) was wound down at the user's direction, with one reporting milestone completed and targeted consolidation continuing. A closed issue therefore does not necessarily mean its original broad objective was achieved. This is a useful counterexample to using closed-issue counts as a progress metric.

Together these cases support a restrained process claim: automation can produce and refactor large developments, while semantic trust, interface quality, scope control and build economics remain active engineering and editorial work. The evidence does not isolate the causal benefit of any one model, tactic, review policy or cache design.
