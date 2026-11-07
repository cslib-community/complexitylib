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

## Uniform asymptotic goods and chores hardness

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

Import [MMSPopulation.lean](../../Complexity/GameTheory/FairDivision/MMSPopulation.lean)
for the quantified Theorems 1 and 3. `population_hardness n hn` applies to every
$n\ge65536$. It supplies the actual label sets, strictly positive item values
and costs, exact goods and chores MMS over all partitions, and a loss for every
complete allocation. `card_population` proves that the actual agent type has
exactly $n$ elements. Set $r=\lfloor\log_2 n\rfloor$; the code length is
$k=64(r+1)$ and the relative loss is explicitly
$1/(4{,}000{,}000{,}000r^2)$. These constants are weaker than the source's displayed
$1/(400{,}000(\log_2 n)^2)$, and establish the same asymptotic order. They account
for the constructed code's weaker distance; the source's original constants are
not asserted.

The proof in
[MMSAllocationLoss.lean](../../Complexity/GameTheory/FairDivision/MMSAllocationLoss.lean)
first forces one high item per bundle and auxiliary weight exactly $T$.
`allocation_label_distance` then proves that the types receiving $P$ and $Q$
have one-sided label distance at most $5\ell$ when every correction is at least
$-\ell$. `universal_goods_loss` and `universal_chores_loss` contradict the code
distance. Their explicit label invariants are discharged by the actual code in
`population_hardness`; allocation hardness is not a hypothesis. The chosen
integer additive loss is $\ell=\lfloor(r+1)/4\rfloor$. Chores use the reversed
corrections and the same exact-MMS partitions.

`inverse_polynomial_lt_gap` proves that for every real $\varepsilon>0$ and
$C\ge0$, $Cn^{-\varepsilon}$ is eventually smaller than the constructed gap.
`no_inverse_polynomial_guarantee` supplies an actual counterexample for every
sufficiently large $n$, ruling out simultaneous $1-Cn^{-\varepsilon}$ goods
and $1+Cn^{-\varepsilon}$ chores guarantees. The exponent is an arbitrary
positive real, not only an integer.

Import [MMSExistence.lean](../../Complexity/GameTheory/FairDivision/MMSExistence.lean)
for the exact-existence consequences. The reusable model definitions live in
[MaximinShare.lean](../../Complexity/GameTheory/FairDivision/MaximinShare.lean),
which can be imported independently of the construction. `bundleValue` is a complete allocation's
additive fiber value. `GoodsMMSAllocation` compares the received bundle with the
least bundle of every competing partition; `ChoresMMSAllocation` compares it
with the greatest bundle. This avoids a choice of extremum representation while
preserving the max-min/min-max semantics. `GoodsExistenceBudget n m` and
`ChoresExistenceBudget n m` quantify over all finite instances with exactly $n$
agents, at most $m$ items, and nonnegative real additive values or costs.
`not_goodsExistenceBudget` and `not_choresExistenceBudget` refute these universal
guarantees at $m=n+640\lfloor\log_2 n\rfloor$ for every $n\ge65536$.

`logarithmic_threshold_of_external_existence` combines this negative direction
with an **explicit external hypothesis**: the positive logarithmic-budget
existence result attributed to Feige by the source. The resulting quantified
bracket gives guaranteed existence below one logarithmic excess and failure at
another, for goods and chores. Feige's theorem is neither proved nor independently
source-audited here. Hummel's four-agent minimality result also remains external;
the four-agent constructions prove the advertised ratios without proving minimality.

The [uniform-hardness client](../../ComplexityTests/MMSPopulation.lean) checks the
first admissible population's code length and dummy count, applies both
existence-budget obstructions, and checks exact-MMS semantics on one-agent and
two-agent instances (including failed allocations). It also applies the
asymptotic comparison to the nonintegral exponent $1/3$. From a bootstrapped
checkout with the library built, run
`lake env lean ComplexityTests/MMSPopulation.lean`; success produces no diagnostics.
Use the normal cache bootstrap if imported artifacts are missing.
