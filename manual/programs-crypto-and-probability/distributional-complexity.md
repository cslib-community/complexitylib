# Distributional problems, AvgP, HeurP and Levin reductions

This page covers the distributional average-case framework of Levin, in the form given by Bogdanov and Trevisan [bt06][bt06]. The framework lives under [Complexity/Computability/Complexity/Classes/AverageCase/](../../Complexity/Computability/Complexity/Classes/AverageCase/). It is separate from the [Liu–Pass hardness predicates](average-case-hardness.md). Those predicates fix the uniform distribution and quantify over heuristics for a function. The distributional framework pairs a language with an arbitrary ensemble and studies classes of such pairs under reductions. A [proved bridge](#bridge-to-mild-hardness) connects the two.

## Ensembles and their efficiency classes

[Ensemble](../../Complexity/Computability/Complexity/Classes/AverageCase/Ensemble.lean) is a family `dist : ℕ → PMF (List Bool)` with `dist n` supported on words of length exactly `n`. This is the setting of the source's uniform ensemble and of its compression argument (Claim 20). Algorithms read `n` as the length of their input. The source also allows ensembles over other polynomially related lengths; those are padded to this form rather than modelled directly.

| Declaration | Meaning | Source |
|---|---|---|
| `Ensemble.cdf` | `D_{|x|}({y : binaryValue y ≤ binaryValue x})`, the cumulative distribution in the numeric order of same-length words | Def. 2 |
| `Ensemble.PComp` | `cdf x = num x / den x` for naturals `num`, `den ≠ 0` computable in polynomial time from `encBits` to binary `encNat` | Def. 2 |
| `Ensemble.PSamp` | a native strict-PPT program (`IsPPTOn encUnary encBits`) whose output law on `n` is exactly `dist n` | Def. 1 |
| `Ensemble.uniform` | `BitString.uniformList n` at each length; `uniform_pComp`, `uniform_pSamp` | §2.1 |

The source does not fix how cdf values are represented. Here they are exact rationals. `Ensemble.binaryValue_le_iff_le` identifies the numeric order with the source's lexicographic order on words of equal length. Samplability is exact, with no statistical-distance slack.

## Distributional classes

[DistProblem](../../Complexity/Computability/Complexity/Classes/AverageCase/Distributional.lean) pairs `lang : Set (List Bool)` with `ens : Ensemble`. All four algorithm predicates require correctness only on the support of the ensemble. Each run is a total, deterministic polynomial-time computation on all inputs.

| Predicate / class | Algorithm type | Guarantee on each length `n` | Source |
|---|---|---|---|
| `IsErrorlessScheme`, `AvgP` | `List Bool × ℕ → Option Bool`, `k` unary | no wrong answer on the support; `Pr[none] ≤ 1/(k+1)` | Defs. 6, 8 |
| `IsHeuristicScheme`, `HeurP` | `List Bool × ℕ → Bool`, `k` unary | `Pr[wrong] ≤ 1/(k+1)` | Def. 11 |
| `IsErrorlessAlgorithm δ`, `AvgDeltaP δ` | `List Bool → Option Bool` | no wrong answer on the support; `Pr[none] ≤ δ n` | Def. 9 |
| `IsHeuristicAlgorithm δ`, `HeurDeltaP δ` | `List Bool → Bool` | `Pr[wrong] ≤ δ n` | Def. 10 |
| `DistNP`, `SampNP` | — | `lang ∈ NP encBits` with a `PComp`, respectively `PSamp`, ensemble | §2.1 |

The source allows a scheme time polynomial in `n/δ`. With `δ = 1/(k+1)` and `k` in unary, "polynomial in `n` and `k`" is the same bound up to polynomial change. Runtime tails and wrong answers stay distinct: an errorless scheme may say `none` but never errs on the support. Proved inclusions are `mem_AvgP_of_mem_P`, `AvgP_subset_HeurP`, `AvgP_subset_AvgDeltaP q` (failure `1/(q(n)+1)`), `HeurP_subset_HeurDeltaP q` and `AvgDeltaP_subset_HeurDeltaP`.

Levin's original definition bounds a moment `E[t(x)^ε]` of the running time. It is **not** formalized here. The source shows it equivalent to `AvgP` (Prop. 7), but only after discarding instances of probability zero, on which the scheme formulation imposes nothing. A literal equivalence with this library's total schemes would therefore need an off-support convention first.

## Reductions and completeness

[DistReduction L L'](../../Complexity/Computability/Complexity/Classes/AverageCase/Reduction.lean) bundles the following data:

- a map `f : List Bool → List Bool` with `ComputableInPolyTime f encBits encBits`;
- correctness `x ∈ L.lang ↔ f x ∈ L'.lang` on the support of `L.ens.dist n`;
- a length map `m : ℕ → ℕ` and a polynomial `p : Polynomial ℕ` with domination at **every** word `y`: `(L.ens.dist n).map f y ≤ p(n) · L'.ens.dist (m n) y`.

Source Definition 17 asks for domination only on the target support. Requiring it at every word is a deliberate strengthening. It implies that `f` maps supports into supports (`DistReduction.mem_support`), and the source's Lemma 18 proof uses exactly that when it applies the target algorithm's correctness to `f x`. The bounded-halting reduction of Theorem 19 meets the strengthened condition. It is injective on the support of `D_n`, and the source bounds `D_n(x) ≤ poly(n) · U^BH(f x)` for every `x` in that support. The image probability of any word is therefore `D_n(x)` for its unique support preimage, or `0`. The target ensemble `U^BH_N` does not have full support, so this argument, not support size, carries the condition. The source takes `m` to be a polynomial. Here `m` is unconstrained, and `DistReduction.exists_m_le` derives `m n ≤ c (n+1)^d` from the running time of `f`.

| Result | Statement |
|---|---|
| `DistReduction.mem_AvgP`, `mem_HeurP` | Lemma 18. The source scheme is `(x, k) ↦ A' (f x, p(|x|)·(k+1))` |
| `DistReduction.mem_AvgDeltaP`, `mem_HeurDeltaP` | Failure `δ` transfers to `n ↦ p(n) · δ(m n)` |
| `DistReduction.exists_comp`, `DistReducible.trans` | Composition, with domination factor `p(n) · p'(c (n+1)^d)` |
| `DistReducible.refl` | Identity reduction |
| `DistHard`, `DistComplete`, `DistComplete.mem_AvgP_iff`, `mem_HeurP_iff` | A complete problem is in `AvgP` (resp. `HeurP`) iff its whole class is |

**Not yet proved:** Levin's theorem that a distributional bounded-halting problem is `DistNP`-complete (Theorem 19 via Claim 20), and the Impagliazzo–Levin extension to `SampNP`. Both are tracked on the [roadmap](../../ROADMAP.md#average-case-complexity).

## Bridge to mild hardness

[not_mildlyHardOnAverageDet_of_mem_HeurP](../../Complexity/Computability/Complexity/Classes/AverageCase/MildHardness.lean) shows the following. If `({x | b x = true}, Ensemble.uniform) ∈ HeurP`, then `fun x => (b x).toNat` is not `MildlyHardOnAverageDet`. The proof runs the scheme with confidence `2 p(n)`, which errs with probability at most `1/(2p(n)+1) < 1/p(n)`. `not_mildlyHardOnAverage_of_mem_HeurP` gives the strict-PPT version through the existing PPT-to-deterministic specialization. Only Boolean targets under the uniform ensemble are bridged.

## Checked examples

[ComplexityTests/AverageCaseDistributional.lean](../../ComplexityTests/AverageCaseDistributional.lean) checks the following:

- uniform `PComp` and `PSamp`, and a concrete cdf value;
- bit complementation as a dominating reduction (`flipReduction`, factor `1`);
- no length map and polynomial make duplication `x ↦ x ++ x` dominated by the uniform ensemble (`not_dominates_dup`);
- `{0^n : n ∈ K}` lies in `AvgDeltaP (fun n => 2^{-n})` for **every** `K : Set ℕ`, including undecidable `K`. Classes with a fixed failure bound therefore contain undecidable problems, while `AvgP` requires failure below every `1/(k+1)`;
- membership of `(Set.univ, uniform)` in `AvgP`, `HeurP` and `DistNP`;
- a bridge instance.

[bt06]: ../sources.md#bt06
