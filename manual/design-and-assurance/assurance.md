# Assurance, formal abstracts and trust

## What each check establishes

The library's assurance mechanisms address different questions. A build checks elaboration and proof acceptance; a transitive axiom audit restricts logical dependencies; independent statement comparison checks selected exported proofs against separately written contracts; mathematical review assesses whether the contracts express the intended result. These are complementary forms of evidence. Lean's official validation guide explicitly separates proof validity from theorem meaning. [lean-validation][lean-validation]

| Mechanism | Evidence supplied | Limit |
|---|---|---|
| Strict build and tests | Source elaborates and checked examples compile | Does not establish intended semantics or source correspondence |
| Module/import/style/lint checks | Selected API and repository conventions | Does not certify all design decisions |
| Global axiom audit | Imported Complexity declarations use only allowed transitive axioms | Trusts imported compiled artifacts and the checking environment |
| Formal-abstract bridge | Presentation theorem follows from library declarations | Readability and faithful informal interpretation require review |
| Comparator contracts | Selected solutions match independently written statements under configured checkers | Trusted harness, upstream definitions and statement meaning remain assumptions |
| Independent agent review | A separate source inspection and recorded verdict | Is neither human approval nor a statistical guarantee of correctness |

## Build and axiom policy

The full validation sequence is strict `lake build`, aggregate-import checking, strict `lake test`, declaration lint, style lint and Init-import checking. [`scripts/check.sh`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/scripts/check.sh) bootstraps optional caches and runs those gates. Quick mode checks affected modules and transitive clients when its analysis is supported, but is expressly not full validation. Hosted coverage of the exact source revision can supply the full gate evidence without a redundant local run.

[`ComplexityTests/Axioms.lean`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Axioms.lean#L11) traverses the declaration tables of imported Complexity modules, including private/generated declarations and extensions in other namespaces. It rejects transitive axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Named guards additionally record selected results intended to use fewer axioms. This is broader than checking a small list of headline theorem names, but it is not an independent reimplementation of the kernel or a semantic audit of every definition.

The source rules prohibit `sorry`, custom axioms and `native_decide` on main. They also ask reviewers to watch for vacuous hypotheses and require at least one test instance of structures that bundle bounds. Such tests can expose an impossible contract; they do not establish every advertised interpretation.

At the snapshot, merge-group run [41384852164](https://github.com/cslib-community/complexitylib/actions/runs/41384852164) passed on the exact SHA. Its `ci-checks` job ran from 03:46:07 to 04:00:29 UTC on November 2: 14 minutes 22 seconds. Recorded build, test, lint, import-generation, style and Init checks succeeded. The survey also recorded success for the subsequent main CI and abstract-PDF workflows; their response snapshots are not versioned here. This research pass inspected metadata and workflow source; it did not rerun Lean or independently examine every generated PDF.

## Curated formal abstracts

[`abstracts/catalogue.json`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/catalogue.json) selects 25 result groups at this revision. Each selected group has a presentation statement and a bridge to the library, with foundation modules used to make important models explicit. These files form a dedicated Lean library imported by the abstract tests. The generated PDFs omit proof bodies and carry source provenance; the Lean statements are the maintained source, rather than an independently edited TeX theorem list.

`#check_abstract` audits elaborated dependencies against the intended presentation boundary. Its allowlist can expose a narrowly identified foundational model but should not hide the theorem's complexity-class semantics. The policy demands satisfiable hypotheses or explicitly stated standard assumptions, honest quantitative bounds, and a substantial endpoint. It also explicitly distinguishes the audit from human interpretation. [Abstract policy](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/AGENTS.md#curated-formal-abstracts)

The catalogue is deliberately smaller than the library. It supplies readable entry points to selected results and does not enumerate every model. It also contains source-sensitive developments requiring careful treatment, including the native subexponential SAT endpoint and the retained ETH-conditional Partial MCSP theorem whose premise the snapshot itself negates. The [native counting survey](../machines-and-classes/native-counting.md) states those claims and limits. A positive build cannot by itself establish the reception or external acceptance of a new mathematical result.

## Independently stated comparator contracts

The [`comparator` directory](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/comparator/README.md) contains six contracts across three suites. The basic suite covers composition of admissible reductions and the one-gate lower bound for a nonprojection. Automation contracts cover two Goldreich–Levin functions. The SAT suite restates the fixed-width exact-counting endpoint and ETH proposition with its own CNF semantics, encodings and resource conditions.

Statement files import only pinned upstream CSLib/Mathlib definitions; solution files apply Complexitylib results. The runner invokes sandboxed `lake comparator --paranoid`, allows only the standard three axioms, and refuses to treat inability to run the sandbox as success. A negative control checks rejection of valid proofs of `True` submitted under the expected theorem names. These are concrete protections against confusing a proved proposition with the requested one.

Comparator remains a selected-contract mechanism. The harness, statements, dependency pins and sandbox are trusted inputs. Its workflow is manual-only at this snapshot, not a per-PR guarantee. The present review inspected the committed contracts/runner documentation but did not run the suites or claim comparator coverage of the whole library. Even external proof checkers cannot determine whether a reviewed formal ETH statement is the intended informal ETH without semantic assessment.

## Review and its observed failure mode

The current policy requires a nonauthor to inspect correctness and API quality on the relevant revision, and changed reasoning to receive fresh review. It allows one competent reviewer to cover both, distinguishes agent review from human/platform approval, and carries earlier approval only across a verified mechanical delta. These rules aim to make review substantive rather than a count of approving agents.

The historical [withdrawal case](../development-history/case-studies.md) demonstrates why that distinction matters: accepted proofs can have hypotheses that assume the advertised endpoint, or noncomputational operations that silently provide the hard part. The library's response included deletion, narrower claims, model recovery and stricter headline selection. This is evidence of a correction process and a documented failure, not evidence that all later semantics have been independently certified.

[lean-validation]: ../sources.md#lean-validation
