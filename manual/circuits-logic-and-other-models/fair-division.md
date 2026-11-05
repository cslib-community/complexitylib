<!--
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-->

# Finite additive fair division

Import [MMSImpossibility.lean](../../Complexity/GameTheory/FairDivision/MMSImpossibility.lean)
for Ezra and Garbuz's STOC 2027 submission 115, Theorem 2 (PDF p. 13).
An `Allocation` assigns each of eleven indivisible goods to one of four agents;
`bundle a i` is its fiber. Thus every good is allocated exactly once, and empty
bundles are allowed. `itemValue` is the source's positive integer table, and
`value` is its additive extension to arbitrary bundles. Agents 0 and 1 use the
first row; agents 2 and 3 use the second (`agentType`).

`Guarantees t n` means some complete four-way partition gives every bundle
value at least $n$ according to valuation type $t$. This ranges over all
partitions, independently of which agents will receive them. `guarantees_iff`
proves this predicate equivalent to $n\le21$: the displayed source partitions
witness 21, while total value 84 bounds every partition by averaging. This
characterizes the actual maximin share as 21 for each agent.

`unavoidable_loss a` proves some agent gets value at most 20 in every complete
allocation. Consequently no such allocation exceeds $20/21$ of MMS for all
agents. Kernel-checked subset splits replace the source's Python enumeration:
the union of the first two agents' bundles must have first-row value at least
42 and second-row value at most 42; none of the remaining unions supports both
required splits. The theorem quantifies over arbitrary complete allocations,
not merely a preselected collection of partitions.

The [checked client](../../ComplexityTests/PaperEndpointsBatchB.lean) gives an
allocation with utility vector $(22,20,20,24)$, attaining minimum 20, and shows
that threshold 22 is impossible even for a single valuation's maximin partition.
After building the library, elaborate that complete client with
`lake env lean ComplexityTests/PaperEndpointsBatchB.lean`; expected success is
no diagnostics. If its imports are missing, follow the normal checkout/cache
bootstrap instructions before retrying. The source's asymptotic goods bounds,
chores results and general existence questions remain outside this endpoint.
