# Assurance and trust

## What each check establishes

The library's assurance mechanisms address different questions. A build checks elaboration and proof acceptance; a transitive axiom audit restricts logical dependencies; the results registry checks the identity of the theorems it lists; mathematical review assesses whether the statements express the intended result. These are complementary forms of evidence. Lean's official validation guide explicitly separates proof validity from theorem meaning. [lean-validation][lean-validation]

| Mechanism | Evidence supplied | Limit |
|---|---|---|
| Strict build and tests | Source elaborates and checked examples compile | Does not establish intended semantics or source correspondence |
| Module/import/style/lint checks | Selected API and repository conventions | Does not certify all design decisions |
| Global axiom audit | Imported CslibFrontier declarations use only allowed transitive axioms | Trusts imported compiled artifacts and the checking environment |
| Results registry | Each listed theorem exists, is public and is a proposition; its source keys are in the bibliography | Establishes neither mathematical correspondence nor completeness |
| Independent agent review | A separate source inspection and recorded verdict | Is neither human approval nor a statistical guarantee of correctness |

## Build and axiom policy

The full validation sequence is strict `lake build`, aggregate-import checking, strict `lake test`, declaration lint, style lint and Init-import checking. [`scripts/check.sh`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/scripts/check.sh) bootstraps optional caches and runs those gates. Quick mode checks affected modules and transitive clients when its analysis is supported, but is expressly not full validation. Hosted coverage of the exact source revision can supply the full gate evidence without a redundant local run.

[`CslibFrontierTests/Axioms.lean`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Axioms.lean#L11) traverses the declaration tables of imported CslibFrontier modules, including private/generated declarations and extensions in other namespaces. It rejects transitive axioms beyond `propext`, `Classical.choice` and `Quot.sound`. Named guards additionally record selected results intended to use fewer axioms. This is broader than checking a small list of headline theorem names, but it is not an independent reimplementation of the kernel or a semantic audit of every definition.

The source rules prohibit `sorry`, custom axioms and `native_decide` on main. They also ask reviewers to watch for vacuous hypotheses and require at least one test instance of structures that bundle bounds. Such tests can expose an impossible contract; they do not establish every advertised interpretation.

At the snapshot, merge-group run [41384852164](https://github.com/cslib-community/cslib-frontier/actions/runs/41384852164) passed on the exact SHA. Its `ci-checks` job ran from 03:46:07 to 04:00:29 UTC on November 2: 14 minutes 22 seconds. Recorded build, test, lint, import-generation, style and Init checks succeeded. The survey also recorded success for the subsequent main CI and abstract-PDF workflows (the latter since retired); their response snapshots are not versioned here. This research pass inspected metadata and workflow source; it did not rerun Lean or independently examine every generated PDF.

A positive build cannot by itself establish the reception or external acceptance of a new mathematical result. The [native counting survey](../machines-and-classes/native-counting.md) states the claims and limits of the native subexponential SAT endpoint and of the retained ETH-conditional Partial MCSP theorem whose premise the snapshot itself negates.

## Retired formal abstracts and comparator contracts

At the survey revision the repository had two further mechanisms, both retired on 2026-11-08. The curated formal abstracts ([`abstracts/`](https://github.com/cslib-community/cslib-frontier/tree/f65cf6aabf60f13270367fea7d080141c7a910f5/abstracts); 25 result groups in the snapshot's [catalogue](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/catalogue.json)) restated selected headline results in a separate Lean library with their own model definitions, proved each restatement from the library in a bridge file, audited its elaborated dependencies with `#check_abstract` and rendered the statements as PDFs. The comparator suites ([`comparator/`](https://github.com/cslib-community/cslib-frontier/tree/f65cf6aabf60f13270367fea7d080141c7a910f5/comparator)) checked six selected solutions against independently written statements, including the fixed-width exact SAT counting endpoint and the ETH proposition, under a sandboxed `lake comparator --paranoid` run whose workflow was manual-only.

The abstracts were retired because the library's own definitions proved as readable as their restatements, while the restatements drifted: pull requests such as [#2847](https://github.com/cslib-community/cslib-frontier/pull/2847) and [#2851](https://github.com/cslib-community/cslib-frontier/pull/2851) corrected errors in the abstracts themselves. The comparator suites were barely maintained. Named results are now collected in the [results inventory](../../results/README.md), whose checked registry links each listed theorem into the API documentation; the library statement is the contract to review.

## Review and its observed failure mode

The current policy requires a nonauthor to inspect correctness and API quality on the relevant revision, and changed reasoning to receive fresh review. It allows one competent reviewer to cover both, distinguishes agent review from human/platform approval, and carries earlier approval only across a verified mechanical delta. These rules aim to make review substantive rather than a count of approving agents.

The historical [withdrawal case](../history/case-studies.md) demonstrates why that distinction matters: accepted proofs can have hypotheses that assume the advertised endpoint, or noncomputational operations that silently provide the hard part. The library's response included deletion, narrower claims, model recovery and stricter headline selection. This is evidence of a correction process and a documented failure, not evidence that all later semantics have been independently certified.

## Finite EFX counterexample

Import `CslibFrontier.GameTheory.FairDivision.EFX`. `Cslib.FairDivision.EFX` uses complete
ownership functions and additive natural-valued item utilities. An EFX comparison removes
every possible single good from another agent's bundle. `ParetoDominates` requires all agents
to weakly improve and at least one to strictly improve.

`PositiveCounterexample.not_efx_and_paretoOptimal` applies to the explicit positive
four-agent, eight-good instance of Mahabadi, Ramakrishnan and Tarnawski, Theorem 1.
The finite proof covers every ownership function via `finFunctionFinEquiv`; each of the
$4^8$ allocations is checked by ordinary kernel reduction in blocks of 256 against a list of
24 possible strict improvements. Neither a search script nor native evaluation is trusted.
The [checked client](../../CslibFrontierTests/GameTheory/EFX.lean) shows an actual EFX allocation
and its strict improvement, and applies the general counterexample theorem. From the
repository root, run `scripts/build.sh CslibFrontierTests.GameTheory.EFX` to check it.
The result rules out EFX and Pareto efficiency together; EFX alone exists for this instance.
For the parameterized extension, import `CslibFrontier.GameTheory.FairDivision.EFXApproximation`.
`ApproximateEFX α v a` compares own utility with $α$ times the utility after removal,
using a real factor and the same additive natural-valued utilities and complete allocations.
At factor one it is equivalent to `EFX`; decreasing the factor preserves the condition.
The predicate accepts any real factor. On the paper's usual range $0<α\le1$ it is its
approximate-EFX condition; the exclusion proof also covers factors above one.

`ApproximateCounterexample.values K` is Theorem 2's exact four-agent, nine-good table,
with all item values positive for every integer $K\ge6$.
`not_approximateEFX_and_paretoOptimal` excludes simultaneous approximate EFX and Pareto
optimality for $α>2/3+1/K$. `exists_parameter` makes the Archimedean choice of $K$ for
any real $α>2/3$; `exists_counterexample` supplies the resulting positive valuation table.
These are the Theorem 2 family and the introduction's arbitrary-factor endpoint, not a
finite-parameter approximation. There is no bit encoding or algorithmic runtime assertion.

The proof checks every ownership function against symbolic certificates: in $z=K-6$, an
EFX violation follows from nonnegative coefficients of a quadratic utility comparison;
a Pareto improvement follows from nonnegative affine utility differences, with one strictly
positive constant difference. The witnesses are the paper's trades and their symmetries or
a swap of the two large goods. Kernel reduction verifies the finite certificates; algebra
then establishes their validity for every $K\ge6$. No upper bound on $K$ is checked or assumed.
The [approximation client](../../CslibFrontierTests/GameTheory/EFXApproximation.lean) checks a
complete EFX allocation throughout the family, an actual strict improvement at $K=6$,
failure of EFX when one agent receives everything, factors $3/4$ and $667/1000$ at $K=13$ and $K=3001$, and arbitrary real-factor use.
From the repository root, run
`scripts/build.sh CslibFrontierTests.GameTheory.EFXApproximation` to check it.

The EFX formalization covers the paper's two primary theorems. It does not yet cover
Appendix A's nondegenerate valuation variant or separately establish the eight-good
$6/7$ strengthening. These ancillary claims are distinct from the main-results coverage.

[lean-validation]: ../sources.md#lean-validation

## All-out-of-r sharing from odd sources

Import `CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR` and open
`Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR`.
For $r=n+1\ge2$ parties and $b\ge r$, `binary_separation n b` produces actual
coefficients in $\mathrm{GF}(2^b)$ and fixed message/share bijections to $b$- and
$(b+1)$-bit strings. It proves reconstruction for every ambient key, joint privacy
for every proper coalition, the exact key cardinality $(2^r-1)2^{(r-1)b}$, and the
min-entropy lower bound $(r-1)b+\log_2(2^{r-1}-1)$. The source is the actual
`OddSources.source`: odd nonempty active sets at indices in $T$, nonempty even
sets at the remaining indices. There is no additional dealer randomness.

The index is a vector in $V^{r-1}$. `pad` returns its first $r-1$ coordinates and
their negative sum, equal to their sum in characteristic two. `sum_pad` and
`padProjection_bijective` prove properties (P1) and (P2). `reconstruct_shares`
uses the visible activation tags and a nonzero sum of independent coefficients.
`view_law` gives equation (9) of STOC submission 886 as an equality of PMFs:
the entire view of $r-1$ parties is uniform on its message-independent support.
`coalition_privacy` projects that joint law to every smaller coalition. In
contrast, `full_view_not_private` proves that the full view distinguishes distinct
messages, so the privacy statement has a substantive threshold boundary.

`card_branch`, `card_oddBranches`, `card_evenBranches`, `card_keys`, and
`card_keys_bounds` expose the exact counts used in Theorem 5.1.
`no_string_extractor` proves error at least $1/(2(2^r-1))$ on some actual source
for every deterministic extractor with any positive output length.
`exists_tight_index_extractor` constructs a balanced bit of the actual pad index,
proves the matching upper bound on every source, and proves that some source
attains equality. `exists_tight_one_bit_index_extractor` transports the same
attained bound to literal one-bit strings, so it matches item 3 at output length one.
These instantiate the common odd-source parity and tightness
results using proved branch counts, nonempty classes and even index cardinality.
`binary_separation` bundles all four items of Theorem 5.1 without unproved
linking assumptions. `binary_construction` remains the sharing-only entry point.
The fixed bijections are noncomputable choices; no bit-level runtime is claimed.

From the repository root, run `scripts/build.sh CslibFrontierTests.Crypto.AllOutOfR`.
The [checked client](../../CslibFrontierTests/Crypto/AllOutOfR.lean) constructs the
$r=2,b=2$ and $r=3,b=3$ instances, checks both support endpoints, tests joint privacy
for two of three parties as well as singletons and the empty coalition, and shows
that a single party has no nonempty even branch. It also applies the full bundle,
checks arbitrary positive output lengths and the attained sharp constants $1/6$
for two parties and $1/14$ for three. The source locator is
[Aggarwal2026](../../references.bib), Section 5, equations (7)–(9), Theorem 5.1
and Lemmas 5.2–5.4, submission PDF pp. 10–11.
