<!--
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-->

# Finite additive fair division

Import [MMSImpossibility.lean](../../Complexity/GameTheory/FairDivision/MMSImpossibility.lean)
for Ezra and Garbuz's STOC submission 115, Theorem 2 (PDF p. 13).
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
bootstrap instructions before retrying.

## Chores and the constant bound

Import [MMSChores.lean](../../Complexity/GameTheory/FairDivision/MMSChores.lean)
for Theorem 4 (PDF p. 14). The source's eleven-item positive cost table uses
exactly the same allocation utilities, agent types and witness partitions.
`Caps t c` means a complete partition with every bundle costing at most $c$;
the chores MMS minimizes this maximum, reversing the goods convention.
`caps_iff` characterizes the exact MMS as 90, and `total` gives total cost 360,
so MMS equals proportional share for both types. `unavoidable_loss` quantifies
over every complete allocation and proves some agent incurs cost at least 93.
`allocation_cap_iff` proves the optimum maximum cost is exactly 93: the first
source partition attains costs $(90,90,93,81)$, as checked in the client. Thus
the instance witnesses the factor $93/90=31/30$. The proof uses a kernel-checked
subset-splitting certificate, with no restrictions on allocations.

## Asymptotic construction in progress

Import [MMSAsymptotic.lean](../../Complexity/GameTheory/FairDivision/MMSAsymptotic.lean)
for the actual parameterized construction in Section 2.1 of STOC submission 115
(PDF p. 8). `Good k d` contains the $X,Y,G,Z,P,Q,D$ item families, with
$n=2k+2+d$ agents and exactly $n+5k$ items (`card_goods`). `weight`, `correction`,
`goodsValue` and `choreCost` implement the source tables. The source chooses $k$
divisible by 8; this makes the division in $U=7k^3-k^2/2$ exact. Item values and
costs are integers, proved strictly positive for every $k>0$ and every label set.
This positivity does not assert that arbitrary label sets satisfy the source's
balanced-code constraints.

`low_bundle_rigidity k hk B` is the complete equivalence in Lemma 7 (PDF p. 9):
a subset of low goods has weight $17k^2$ exactly when it is one $G$ good or a
matched $X_j,Y_j$ pair. It holds for arbitrary positive $k$, without enumeration
at a selected size. `goodsValue_add_choreCost` gives the exact bundle identity
$v_S(B)+c_S(B)=6w(B)$ used in the goods-to-chores argument. The checked client
contains a 128-agent item-count instance, matched/mismatched low pairs and
positivity applications. The Z weight is exactly $T-H=68k^3-17k^2$; it is not
$3T/4$ for general $k$. `weight_total` proves total weight $nT$, while
`correction_total`, `goodsValue_total` and `choreCost_total` give zero total
correction and total value/cost $n\cdot204k^3$ for each size-$k$ label set.

`labelSet` implements the labels $2h+a_h$. `card_labelSet`, `sum_labelSet` and
`labelSet_sdiff_card` prove the source cardinality, balanced-word sum and one-sided
distance identities. `witness` is the complete type-specific partition of Lemma 6;
`witness_weight` and `witness_correction` prove each bundle has weight $T$ and zero
correction. `balanced_guarantees_iff` and `balanced_caps_iff` therefore prove exact
goods and chores MMS $204k^3$ for every balanced even-length word, over all
complete partitions. The checked client includes a concrete balanced type with
$k=8$, $d=110$ and exact MMS $104448$, so these premises are satisfiable.

Import [MMSCodes.lean](../../Complexity/GameTheory/FairDivision/MMSCodes.lean)
for actual code existence. `exists_population_code n` constructs $n$ distinct
balanced words of length $64(\lfloor\log_2 n\rfloor+1)$ and pairwise Hamming
distance at least $2(\lfloor\log_2 n\rfloor+2)$. The proof uses the existing
Gilbert–Varshamov bound, followed by appending each word's complement.
This gives a weaker relative distance than Lemma 5's $1/4$, but a positive
constant distance and rate. It does not claim Lemma 5's exact constants.
`high_items_le_population` shows that $n\ge65536$ accommodates the high items;
`population_item_count` proves the actual instantiated item type has exactly
$n+5k$ items and at most $n+640\lfloor\log_2 n\rfloor$ items. The common
binomial estimates now live in
[HammingBallBounds.lean](../../Complexity/Foundations/Data/Code/HammingBallBounds.lean),
shared with Justesen codes, with their original declarations and source credit.

Theorems 1 and 3 remain unfinished: the contradiction for every allocation and
the quantified inverse-log-squared loss are still required. The weaker distance
constant in the constructed code also requires a correspondingly smaller
additive shortfall in the final hardness proof.
The existence side of the claimed MMS threshold also requires the cited external
existence theorem. The finite four-agent result and this structural lemma do not
complete those headline claims.
