# Sorting, selection and recurrences

Part of the [representative algorithm endpoints](algorithm-endpoints.md); the conventions and limitations stated there apply to this page.

## Sorting and selection

[abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/RandomizedWordRAMAbstract.lean) (retired; its bridge applied [Quicksort.lean](../../CslibFrontier/Algorithms/WordRAM/Quicksort.lean) and [Quickselect.lean](../../CslibFrontier/Algorithms/WordRAM/Quickselect.lean)) gives one fixed 16-register program for in-place randomized quicksort and one for quickselect, in the exact Word-RAM basis with unit-cost finite-interval `rand`.

| Algorithm | Fitting-width condition | Worst-case executed steps | Expected steps | Other guarantee |
|---|---|---|---|---|
| Quicksort | `w ≥ 3*(floorlog₂(n)+1)` and input fit | `20*n² + 8*n + 32` | `≤ 120*n*(floorlog₂(n)+1)+32` | At most `n-1` draws, sorted permutation, linear scratch frame |
| Quickselect, `k<n` | `w ≥ 2*(floorlog₂(n)+1)` and input fit | `10*n²+15` | `≤80*n+15` | At most `n-1` draws, kth sorted value and partition, no auxiliary memory |

Quickselect receives the index followed by the array; an invalid index has an explicit eight-step, no-write, no-randomness behavior returning zero. The expected costs are machine instruction counts. They do not price the `rand` instruction as an exact strict-PPT finite-coin sampler.

### Deterministic selection in the comparison model

Import `CslibFrontier.Algorithms.Lean.Query.Select.Correctness` and `CslibFrontier.Algorithms.Lean.Query.Select.Cost`. [Defs.lean](../../CslibFrontier/Algorithms/Lean/Query/Select/Defs.lean) defines `Cslib.Query.select k xs`, the groups-of-five median-of-medians algorithm in cslib's comparison-query model `FreeM (LEQuery α)`, the model of `Cslib.Query.mergeSort`. Every comparison `a ≤ b` is an oracle query and list manipulation is free. The program sorts lists of at most `selectCutoff = 730` elements with `mergeSort`. For a longer list it takes the lower median of each group of five, selects the median of these medians recursively as the pivot, partitions three ways (below, equivalent to and above the pivot) and recurses into the part holding rank `k` [BFPRT 1973][bfprt73], [CLRS 9.3][clrs09]. The three-way partition makes the algorithm correct for total preorders with ties. Before recursing into a side, the program checks without comparisons that the side has at most `selectSideBound n` elements, and returns `none` otherwise. Under an oracle implementing a total preorder the check always passes. It makes the recursion well founded and lets the comparison bound hold for every oracle.

| Declaration | Statement |
|---|---|
| `select_isOrderStatistic`, `eval_select_eq_none` | under an oracle implementing a total preorder `r`, `select k xs` returns an element of rank `k` when `k < xs.length`, and `none` otherwise. No antisymmetry is assumed |
| `eval_select_eq_getElem?_mergeSort` | in a linear order, `select k xs` returns `xs.mergeSort[k]?` |
| `length_filter_lt_le_selectSideBound`, `length_filter_gt_le_selectSideBound` | the median-of-medians counting bound: if the pivot has rank `⌊(g−1)/2⌋` among the `g = ⌈n/5⌉` group medians, at most `n − 3⌊(g−1)/2⌋ − 1` elements lie strictly on either side of it |
| `select_countQueries_le`, `select_upperBound` | `select k` makes at most `37 n` comparisons under every oracle, as `UpperBound (select k) List.length (37 * ·)` |

The cost proof solves `T(n) ≤ 8n/5 + T(⌈n/5⌉) + 2n + T(selectSideBound n)` by strong induction. Sorting the groups costs `8n/5` (`medians_countQueries_le`), the partition costs `2n` (`partition3_countQueries_le`), and the base case costs `n⌈log₂ n⌉ ≤ 10n`. The group cost uses [CountBound.lean](../../CslibFrontier/Algorithms/Lean/Query/Sort/Merge/CountBound.lean), which sharpens cslib's merge bound: a merge makes at most `|xs| + |ys| − 1` comparisons (`merge_countQueries_le_sub_one`), so `mergeSort` sorts five elements with at most `8` (`mergeSortCountBound_five`). Ranks are stated with `List.IsOrderStatistic` in [OrderStatistic.lean](../../CslibFrontier/Foundations/Data/List/OrderStatistic.lean): at most `k` elements lie strictly below `y` and more than `k` lie at or below it. `List.isOrderStatistic_iff_mergeSort` identifies the rank-`k` element of a linear order with `xs.mergeSort[k]`. The [tests](../../CslibFrontierTests/QuerySelect.lean) run lists longer than the cutoff, duplicates, out-of-range ranks, a preorder with ties and a dishonest oracle.

The constant `37` comes from this simple accounting. Blum, Floyd, Pratt, Rivest and Tarjan refine the algorithm (`PICK`) to at most `5.4305 n` comparisons [BFPRT 1973][bfprt73]; that constant is not formalized. Group sizes other than five, lower bounds for the median and for general ranks, the second-smallest bound `n + ⌈log₂ n⌉ − 2` and a word-RAM implementation also remain open; see `ROADMAP.md`.

### Comparison lower bounds for the minimum and the maximum

Import `CslibFrontier.Algorithms.Lean.Query.Select.MinMax.LowerBound`. In the same model, [Basic.lean](../../CslibFrontier/Algorithms/Lean/Query/Select/MinMax/Basic.lean) states what a correct algorithm is. `Cslib.Query.IsMinAlg alg` asks that, under every oracle implementing a linear order, `alg xs` returns a least element of every nonempty `xs`. `Cslib.Query.IsMinMaxAlg alg` asks the same for a pair consisting of a least and a greatest element. Requiring correctness only for linear orders makes the lower bounds stronger. The file also gives the matching algorithms, which are correct for every total preorder. `findMin` is the linear scan. `findMinMax` compares the elements in pairs and then compares the smaller of each pair with the current minimum and the larger with the current maximum [CLRS 9.1][clrs09].

| Declaration | Statement |
|---|---|
| `countQueries_findMin`, `findMin_upperBound`, `findMin_isMinAlg` | `findMin` makes exactly `n − 1` comparisons under every oracle and is correct |
| `countQueries_findMinMax`, `findMinMax_upperBound`, `findMinMax_isMinMaxAlg` | `findMinMax` makes exactly `(3n + 1)/2 − 2 = ⌈3n/2⌉ − 2` comparisons under every oracle and is correct |
| `IsMinAlg.length_sub_one_le_countQueries`, `IsMinAlg.lowerBound_infinite`, `IsMinAlg.countQueries_findMin_le` | a correct algorithm for the minimum makes at least `n − 1` comparisons on every list of `n` distinct elements, against every oracle implementing a linear order; hence `findMin` is optimal on every input |
| `IsMinMaxAlg.exists_le_countQueries`, `IsMinMaxAlg.lowerBound_infinite`, `IsMinMaxAlg.exists_countQueries_findMinMax_le` | for a correct algorithm for the minimum and maximum and a list of `n` distinct elements, some oracle implementing a linear order forces at least `⌈3n/2⌉ − 2` comparisons; hence `findMinMax` is optimal on every input |

The proofs use the fooling relations of [Fooling.lean](../../CslibFrontier/Algorithms/Lean/Query/Sort/LEQuery/Fooling.lean), along the comparisons recorded by `LEQuery.queriedPairs` ([QueriedPairs.lean](../../CslibFrontier/Algorithms/Lean/Query/Sort/LEQuery/QueriedPairs.lean)). An element is *found above* (`FoundAbove`) if some comparison with distinct sides put it on the strictly larger side. Moving an element that was never found above to the bottom of the order (`moveToBot`) keeps every answer, so a correct algorithm cannot tell the two orders apart (`eval_moveToBot_eq`). Hence every element except the reported minimum is found above, and each comparison finds at most one element above. For the minimum and maximum, the adversary keeps a linear order and before each comparison moves one of its two elements to the top or the bottom. An element that has only been found above moves to the top, one that has only been found below moves to the bottom, and earlier answers are preserved. The potential that weighs an element `1`, `2` or `4` according to how many of the two facts hold grows by at most `2` per comparison, from `n` to at least `4n − 4` (Pohl's argument; [Pohl 1972][pohl72], [Knuth 5.3.3][knuth98], [CLRS 9.1][clrs09]). The upper-bound counts are exact. The lower bound for the minimum holds against every linear oracle. The lower bound for the minimum and maximum holds against an oracle chosen by the adversary, given as a Boolean comparator that implements a linear order. The [tests](../../CslibFrontierTests/QueryMinMax.lean) run both algorithms on concrete lists, tabulate the bound, and show that algorithms which make no comparisons are rejected by the lower bounds.

## Divide-and-conquer recurrences

[MasterTheorem.lean](../../CslibFrontier/Foundations/Data/Nat/MasterTheorem.lean) solves divide-and-conquer cost recurrences over `ℕ` with explicit constants. `Nat.DivideConquerBound T a b n₀ T₀ f` has two parts:

- The base bound: `T n ≤ T₀` for `n ≤ n₀`.
- The recursive step: for `n > n₀`, every `S` that bounds `T` on `[0, ⌈n/b⌉]` gives `T n ≤ a S + f n`.

So a cost function with floor and ceiling splits, or several subproblems of size at most `⌈n/b⌉`, satisfies it directly. Monotonicity is not required and the recurrence need not be an equality. To prove `step` for a concrete recurrence:

1. Unfold one level with `rw`. If the definition's pattern match does not rewrite cleanly, state the one-level equation first.
2. Instantiate `hS` at each subproblem size, proving each `m ≤ (n + b - 1) / b` with `omega`.
3. Normalize `c * n ^ d` with `simp only`.
4. Close the goal with `omega`.

The clients below follow this recipe.

`DivideConquerBound` itself imposes no condition on `a`, `b` or `n₀`, and without further hypotheses the conclusions below can fail. For example, `T n = n` with `a = b = n₀ = T₀ = 1` and `c = d = 0` satisfies the contract, because `⌈n/1⌉ = n`, yet case 2 would give `T 2 ≤ 1`.

`DivideConquerBound.le_sum` unrolls the recursion for `a ≥ 1` and monotone `f`. For `f n = c n ^ d` the three cases follow. All three statements in the table assume `a ≥ 1`, `b ≥ 2` and `n₀ ≥ 1`:

| Case | Lean statement | Bound |
|---|---|---|
| `a > b ^ d` | `sub_mul_le_pow_clog` | `(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ ⌈log_b n⌉` |
| `a = b ^ d` | `le_mul_pow_mul_clog` | `T n ≤ (b n) ^ d (T₀ + c n₀ ^ d ⌈log_b n⌉)` for `n ≠ 0` |
| `a < b ^ d` | `pow_sub_mul_le_mul_pow` | `(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d` for `n ≠ 0` |

[MasterTheoremAsymptotics.lean](../../CslibFrontier/Foundations/Data/Nat/MasterTheoremAsymptotics.lean) turns these into `O(n ^ log_b a)`, `O(n ^ d log n)` and `O(n ^ d)` as Mathlib `IsBigO` statements (`isBigO_rpow`, `isBigO_pow_mul_log`, `isBigO_pow`). In case 1 it also gives an explicit real-power bound (`le_mul_rpow`). The conversions are the base-`b` lemmas `Nat.pow_clog_le_mul_rpow_logb` and `Nat.clog_le_two_mul_logb` in [LogTwoRpow.lean](../../CslibFrontier/Foundations/Data/Nat/LogTwoRpow.lean), whose base-`2` cases are used by Karatsuba. Mathlib's `Mathlib.Computability.AkraBazzi` proves the more general Akra–Bazzi `Θ` bound, but it needs an equality recurrence over `ℝ` with positive base values. The statements here give upper bounds only. Case 3 is proved for polynomial `f`, not under the general regularity condition. Applied to cslib's merge-sort count, case 2 gives `2 n ⌈log₂ n⌉`, which is weaker by the factor `b` than cslib's own `n ⌈log₂ n⌉`. The halving lemma `Nat.add_mul_two_pow_clog_le_of_halving` ([HalvingRecurrence.lean](../../CslibFrontier/Foundations/Data/Nat/HalvingRecurrence.lean)) remains the sharper tool for `b = 2`. It carries a subtracted lower-order term through the induction, which the Karatsuba addition count needs (`addCount_add_le_pow_clog`).

The checked client [MasterTheorem.lean](../../CslibFrontierTests/MasterTheorem.lean) applies the theorem to:

- cslib's `timeMergeSortRec`;
- Karatsuba's `mulCount`, recovering `mulCount_le_pow_clog`;
- a Strassen-shaped `7 T(⌈n/2⌉) + n²`, giving `O(n ^ log₂ 7)`;
- a binary-search recurrence;
- a base-`3` case-3 recurrence.

It also refutes the hypothesis for `n²`. Build with

```bash
lake build CslibFrontier.Foundations.Data.Nat.MasterTheoremAsymptotics CslibFrontierTests.MasterTheorem
```

## Branching-vector recurrences and SAT search trees

[BranchingVector.lean](../../CslibFrontier/Foundations/Data/BranchingVector.lean) solves exact-exponential search-tree recurrences governed by a positive integer decrease vector `steps = [a₁, …, a_b]` (`aᵢ > 0`) via the characteristic sum `Cslib.BranchingVector.charSum steps r = ∑_{d ∈ steps} r ^ (-d)` [Fomin–Kratsch][fominkratsch10]. Whenever `1 ≤ r` satisfies `charSum steps r ≤ 1`, any `BranchingRecurrence T steps C` (`T n ≤ max C (∑_{d ∈ steps, d ≤ n} S (n - d))` for strict-prefix upper bounds `S`) obeys `T n ≤ C * r ^ n` (`BranchingRecurrence.le_mul_pow`, and `T n ≤ r ^ n` at `C = 1` via `le_pow`).

For explicit multi-way search trees, `Cslib.BranchingVector.BranchingTree σ` equips states with `isLeaf`, `children`, `measure : σ → ℕ`, and `steps : List ℕ` such that every non-leaf expansion has child measure drops dominating some sublist of `steps`. When `1 ≤ r` and `charSum T.steps r ≤ 1`:

- `T.leafCount_le_pow` bounds the number of leaves from `s` by `r ^ T.measure s`;
- `T.nodeCount_le_mul_pow` bounds total internal and leaf nodes by `(T.measure s + 1) * r ^ T.measure s`;
- `T.workCost_le_mul_nodeCount` and `T.workCost_le_mul_pow` separate per-node overhead `nodeWork u ≤ W` multiplicatively as `workCost nodeWork s ≤ W * nodeCount s ≤ W * (T.measure s + 1) * r ^ T.measure s`, without folding polynomial node work into the exponential base `r`;
- `T.iff_exists_leaf`, `T.sum_leaves_eq`, and `T.le_sum_leaves` transport Boolean predicates and additive or subadditive invariants from `s` across `T.leaves s`.

Closed-form sub-`2` branching factors are provided for Fibonacci splits `[1, 2]` (`goldenBranchFactor = (1 + √5) / 2`, `charSum_fibonacci`) and `k`-clause prefix splits `prefixSteps k = [1, 2, …, k]` (`prefixBranchFactor k = 2 - (1 / 2) ^ k < 2` for `k ≥ 1`, `charSum_prefixSteps_le_one`).

[CNF/Branching.lean](../../CslibFrontier/Logics/Propositional/CNF/Branching.lean) connects `BranchingTree` to propositional CNF search while keeping covering and partitioning branch rules distinct in their types (`CNF.BranchMode.covering` versus `.partitioning` in `CNF.BranchRule`):

- `CNF.CoversModels φ branches` preserves `Satisfiable` (`CoversModels.satisfiable_iff`) and bounds `φ.modelCountOn declared` from above by the sum of branch counts (`modelCountOn_le_sum`), whereas `CNF.PartitionsModels φ branches` requires every satisfying assignment of `φ` to satisfy **exactly one** branch, giving exact model-count additivity (`PartitionsModels.modelCountOn_eq_sum`).
- Binary variable splitting (`varSplitRule v`) partitions models unconditionally. Naive clause literal branching (`clauseCoverRule c`, creating one branch `[l] :: φ` per `l ∈ c`) covers models when `c ∈ φ` (`coversModels_clauseCoverBranches`), but **does not partition models**: `not_partitionsModels_clauseCoverBranches_two` refutes `PartitionsModels` on a two-literal clause with distinct variables.
- Disjoint prefix branching (`clausePrefixBranches c φ`, asserting `[l₁]`, `[¬l₁, l₂]`, …, `[¬l₁, …, ¬l_{b-1}, l_b]`) partitions models whenever `φ` entails `c` (`partitionsModels_clausePrefixBranches`). Eliminating assigned variables along non-tautological clauses of width at most `k` yields `CNF.clausePrefixTree k`: on `n = declared.card` variables, `modelCountOn_eq_sum_clausePrefixTree_leaves` proves exact leaf model-count conservation (`∑_{l ∈ leaves} (if [] ∈ l.formula then 0 else 2 ^ l.unassigned.card)`), `satisfiable_iff_exists_clausePrefixTree_leaf` characterizes satisfiability, `leafCount_clausePrefixTree_le` bounds leaves by `(2 - (1 / 2) ^ k) ^ n` (`k ≥ 1`), and `leafCount_clausePrefixTree_two_le` specializes `k = 2` to `((1 + √5) / 2) ^ n`. Checked examples live in [BranchingAndSchoening.lean](../../CslibFrontierTests/BranchingAndSchoening.lean).

[bfprt73]: ../sources.md#bfprt73
[clrs09]: ../sources.md#clrs09
[fominkratsch10]: ../sources.md#fominkratsch10
[knuth98]: ../sources.md#knuth98
[pohl72]: ../sources.md#pohl72
