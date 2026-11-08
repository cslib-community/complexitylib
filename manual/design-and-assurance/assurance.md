# Assurance and trust

## What each check establishes

The library's assurance mechanisms address different questions. A build checks elaboration and proof acceptance; a transitive axiom audit restricts logical dependencies; the results registry checks the identity of the theorems it lists; mathematical review assesses whether the statements express the intended result. These are complementary forms of evidence. Lean's official validation guide explicitly separates proof validity from theorem meaning. [lean-validation][lean-validation]

| Mechanism | Evidence supplied | Limit |
|---|---|---|
| Strict build and tests | Source elaborates and checked examples compile | Does not establish intended semantics or source correspondence |
| Module/import/style/lint checks | Selected API and repository conventions | Does not certify all design decisions |
| Global axiom audit | Imported Complexity declarations use only allowed transitive axioms | Trusts imported compiled artifacts and the checking environment |
| Results registry | Each listed theorem exists, is public and is a proposition; its source keys are in the bibliography | Establishes neither mathematical correspondence nor completeness |
| Independent agent review | A separate source inspection and recorded verdict | Is neither human approval nor a statistical guarantee of correctness |

## Build and axiom policy

The full validation sequence is strict `lake build`, aggregate-import checking, strict `lake test`, declaration lint, style lint and Init-import checking. [`scripts/check.sh`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/scripts/check.sh) bootstraps optional caches and runs those gates. Quick mode checks affected modules and transitive clients when its analysis is supported, but is expressly not full validation. Hosted coverage of the exact source revision can supply the full gate evidence without a redundant local run.

[`ComplexityTests/Axioms.lean`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Axioms.lean#L11) traverses the declaration tables of imported Complexity modules, including private/generated declarations and extensions in other namespaces. It rejects transitive axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Named guards additionally record selected results intended to use fewer axioms. This is broader than checking a small list of headline theorem names, but it is not an independent reimplementation of the kernel or a semantic audit of every definition.

The source rules prohibit `sorry`, custom axioms and `native_decide` on main. They also ask reviewers to watch for vacuous hypotheses and require at least one test instance of structures that bundle bounds. Such tests can expose an impossible contract; they do not establish every advertised interpretation.

At the snapshot, merge-group run [41384852164](https://github.com/cslib-community/complexitylib/actions/runs/41384852164) passed on the exact SHA. Its `ci-checks` job ran from 03:46:07 to 04:00:29 UTC on November 2: 14 minutes 22 seconds. Recorded build, test, lint, import-generation, style and Init checks succeeded. The survey also recorded success for the subsequent main CI and abstract-PDF workflows (the latter since retired); their response snapshots are not versioned here. This research pass inspected metadata and workflow source; it did not rerun Lean or independently examine every generated PDF.

A positive build cannot by itself establish the reception or external acceptance of a new mathematical result. The [native counting survey](../machines-and-classes/native-counting.md) states the claims and limits of the native subexponential SAT endpoint and of the retained ETH-conditional Partial MCSP theorem whose premise the snapshot itself negates.

## Retired formal abstracts and comparator contracts

At the survey revision the repository had two further mechanisms, both retired on 2026-11-08. The curated formal abstracts ([`abstracts/`](https://github.com/cslib-community/complexitylib/tree/f65cf6aabf60f13270367fea7d080141c7a910f5/abstracts); 25 result groups in the snapshot's [catalogue](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/catalogue.json)) restated selected headline results in a separate Lean library with their own model definitions, proved each restatement from the library in a bridge file, audited its elaborated dependencies with `#check_abstract` and rendered the statements as PDFs. The comparator suites ([`comparator/`](https://github.com/cslib-community/complexitylib/tree/f65cf6aabf60f13270367fea7d080141c7a910f5/comparator)) checked six selected solutions against independently written statements, including the fixed-width exact SAT counting endpoint and the ETH proposition, under a sandboxed `lake comparator --paranoid` run whose workflow was manual-only.

The abstracts were retired because the library's own definitions proved as readable as their restatements, while the restatements drifted: pull requests such as [#2847](https://github.com/cslib-community/complexitylib/pull/2847) and [#2851](https://github.com/cslib-community/complexitylib/pull/2851) corrected errors in the abstracts themselves. The comparator suites were barely maintained. Named results are now collected in the [results inventory](../../results/README.md), whose checked registry links each listed theorem into the API documentation; the library statement is the contract to review.

## Review and its observed failure mode

The current policy requires a nonauthor to inspect correctness and API quality on the relevant revision, and changed reasoning to receive fresh review. It allows one competent reviewer to cover both, distinguishes agent review from human/platform approval, and carries earlier approval only across a verified mechanical delta. These rules aim to make review substantive rather than a count of approving agents.

The historical [withdrawal case](../development-history/case-studies.md) demonstrates why that distinction matters: accepted proofs can have hypotheses that assume the advertised endpoint, or noncomputational operations that silently provide the hard part. The library's response included deletion, narrower claims, model recovery and stricter headline selection. This is evidence of a correction process and a documented failure, not evidence that all later semantics have been independently certified.

[lean-validation]: ../sources.md#lean-validation
