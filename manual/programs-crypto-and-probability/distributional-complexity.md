# Distributional problems, AvgP, HeurP and Levin reductions

This page covers the distributional average-case framework of Levin, in the form given by Bogdanov and Trevisan [bt06][bt06]. The framework lives under [Complexity/Computability/Complexity/Classes/AverageCase/](../../Complexity/Computability/Complexity/Classes/AverageCase/). It is separate from the [Liu–Pass hardness predicates](average-case-hardness.md). Those predicates fix the uniform distribution and quantify over heuristics for a function. The distributional framework pairs a language with an arbitrary ensemble and studies classes of such pairs under reductions. A [proved bridge](#bridge-to-mild-hardness) connects the two.

## Ensembles and their efficiency classes

[Ensemble](../../Complexity/Computability/Complexity/Classes/AverageCase/Ensemble.lean) is a family `dist : ℕ → PMF (List Bool)` with `dist n` supported on words of length exactly `n`. This is the setting of the source's uniform ensemble and of its compression argument (Claim 20). Algorithms read `n` as the length of their input. The source also allows `D_n` to be supported on words of several lengths (§2.3). Such ensembles are not modelled, and no reindexing bridge is provided.

| Declaration | Meaning | Source |
|---|---|---|
| `Ensemble.cdf` | `D_{|x|}({y : binaryValue y ≤ binaryValue x})`, the cumulative distribution in the numeric order of same-length words | Def. 2 |
| `Ensemble.PComp` | `cdf x = num x / den x` for naturals `num`, `den ≠ 0` computable in polynomial time from `encBits` to binary `encNat` | Def. 2 |
| `Ensemble.PSamp` | a native strict-PPT program (`IsPPTOn encUnary encBits`) whose output law on `n` is exactly `dist n` | Def. 1 |
| `Ensemble.uniform` | `BitString.uniformList n` at each length; `uniform_pComp`, `uniform_pSamp` | §2.1 |

The source does not fix how cdf values are represented. Here they are exact rationals. `BitString.binaryValue_le_iff_le` identifies the numeric order with the source's lexicographic order on words of equal length. Samplability is exact, with no statistical-distance slack.

## Distributional classes

[DistProblem](../../Complexity/Computability/Complexity/Classes/AverageCase/Distributional.lean) pairs `lang : Set (List Bool)` with `ens : Ensemble`. All four algorithm predicates require correctness only on the support of the ensemble. Each run is a total, deterministic polynomial-time computation on all inputs.

| Predicate / class | Algorithm type | Guarantee on each length `n` | Source |
|---|---|---|---|
| `IsErrorlessScheme`, `AvgP` | `List Bool × ℕ → Option Bool`, `k` unary | no wrong answer on the support; `Pr[none] ≤ 1/(k+1)` | Defs. 6, 8 |
| `IsHeuristicScheme`, `HeurP` | `List Bool × ℕ → Bool`, `k` unary | `Pr[wrong] ≤ 1/(k+1)` | Def. 11 |
| `IsErrorlessAlgorithm δ`, `AvgDeltaP δ` | `List Bool → Option Bool` | no wrong answer on the support; `Pr[none] ≤ δ n` | Def. 9 |
| `IsHeuristicAlgorithm δ`, `HeurDeltaP δ` | `List Bool → Bool` | `Pr[wrong] ≤ δ n` | Defs. 10, 11 |
| `DistNP`, `SampNP` | — | `lang ∈ NP encBits` with a `PComp`, respectively `PSamp`, ensemble | §2.1 |

The source allows a scheme time polynomial in `n/δ`. With `δ = 1/(k+1)` and `k` in unary, "polynomial in `n` and `k`" is the same bound up to polynomial change. Runtime tails and wrong answers stay distinct: an errorless scheme may say `none` but never errs on the support. Proved inclusions are `mem_AvgP_of_mem_P`, `AvgP_subset_HeurP`, `AvgP_subset_AvgDeltaP q` (failure `1/(q(n)+1)`), `HeurP_subset_HeurDeltaP q` and `AvgDeltaP_subset_HeurDeltaP`.

Levin's original definition bounds a moment `E[t(x)^ε]` of the running time. It is **not** formalized here. The source shows it equivalent to `AvgP` (Prop. 7), but only after discarding instances of probability zero, on which the scheme formulation imposes nothing. A literal equivalence with this library's total schemes would therefore need an off-support convention first.

## Reductions and completeness

[DistReduction L L'](../../Complexity/Computability/Complexity/Classes/AverageCase/Reduction.lean) bundles the following data:

- a map `f : List Bool → List Bool` with `ComputableInPolyTime f encBits encBits`;
- correctness `x ∈ L.lang ↔ f x ∈ L'.lang` on the support of `L.ens.dist n`;
- a length map `m : ℕ → ℕ` and a polynomial `p : Polynomial ℕ` with domination at **every** word `y`: `(L.ens.dist n).map f y ≤ p(n) · L'.ens.dist (m n) y`.

Source Definition 17 asks for domination only on the target support. `Probability.PMF.forall_map_apply_le_mul_iff` shows that domination at every word is exactly that condition plus support preservation, `f (Supp D_n) ⊆ Supp D'_{m(n)}` (`DistReduction.mem_support`). The source's Lemma 18 proof uses support preservation when it applies the target algorithm's correctness to `f x`, and the lemma fails without it. Counterexample: take `D'_n` to be the point mass at `0^n`, `L' = {x ++ [true] | x ∈ L}` and `f x = x ++ [true]`. The map `f` is correct and satisfies the literal domination vacuously, and "always no" decides `(L', D')` on its support, so every `(L, D)` would land in `AvgP`. The every-word condition is therefore the repair that Lemma 18 needs, not an optional strengthening. The bounded-halting reduction of Theorem 19 meets the strengthened condition, as [`BoundedHalting.distHard_problem`](#levins-completeness-theorem) checks. That reduction is injective, so the image probability of any word is `D_n(x)` for its unique preimage `x`, or `0`. The target ensemble `U^BH_N` does not have full support, so injectivity, not support size, carries the condition. The source takes `m` to be a polynomial. Here `m` is unconstrained, and `DistReduction.exists_m_le` derives `m n ≤ c (n+1)^d` from the running time of `f`.

| Result | Statement |
|---|---|
| `DistReduction.mem_AvgP`, `mem_HeurP` | Lemma 18. The source scheme is `(x, k) ↦ A' (f x, p(|x|)·(k+1))` |
| `DistReduction.mem_AvgDeltaP`, `mem_HeurDeltaP` | Failure `δ` transfers to `n ↦ p(n) · δ(m n)` |
| `DistReduction.exists_comp`, `DistReducible.trans` | Composition, with domination factor `p(n) · p'(c (n+1)^d)` |
| `DistReducible.refl` | Identity reduction |
| `DistHard`, `DistComplete`, `DistComplete.mem_AvgP_iff`, `mem_HeurP_iff` | A complete problem is in `AvgP` (resp. `HeurP`) iff its whole class is |

## Levin's completeness theorem

[BoundedHalting.distComplete_problem](../../Complexity/Computability/Complexity/Classes/AverageCase/Completeness.lean) proves Theorem 19 of the source, which goes back to Levin [lev86][lev86]: the distributional bounded halting problem `(BH, U^BH)` is complete for `DistNP` under `DistReduction`. Consequently `problem_mem_AvgP_iff` and `problem_mem_HeurP_iff` state that `(BH, U^BH)` lies in `AvgP` (resp. `HeurP`) exactly when all of `DistNP` does. The proof has four parts.

| Part | Declarations | Source |
|---|---|---|
| Collapse of the uniform ensemble at a polynomial-time prefix code of headers: exact dyadic cdf, `PComp`, and probability `2^{-|h|}` for a padded header `h` | [HeaderParser](../../Complexity/Computability/Complexity/Classes/AverageCase/Collapse.lean), `collapse`, `ensemble`, `cdf_ensemble`, `pComp_ensemble`, `ensemble_dist_collapse` | definition of `U^BH_N`, §3.2 |
| The problem: `BH`, its header code, `U^BH`, `BH ∈ NP` and `(BH, U^BH) ∈ DistNP` | [BoundedHalting](../../Complexity/Computability/Complexity/Classes/AverageCase/BoundedHalting.lean): `BH`, `encode`, `parser`, `uniformBH`, `uniformBH_dist_encode`, `uniformBH_pComp`, `BH_mem_NP`, `problem_mem_DistNP` | (3.1) |
| Compression: `C` is computable in polynomial time and injective on each length, with `|C(x)| ≤ |x| + 1` and `2^{|C(x)|} D_n(x) ≤ 2` | [Compression](../../Complexity/Computability/Complexity/Classes/AverageCase/Compression.lean): `compress`, `compress_polyTime`, `compress_injective`, `length_compress_le`, `two_pow_length_compress_mul_le` | Claim 20 |
| The reduction `x ↦ (c, code x, 1^{t(x)})` onto length `N(n)`, with domination factor `2^{2|c|+4} (6n+5)^2 (2n+1)^2` | [distHard_problem](../../Complexity/Computability/Complexity/Classes/AverageCase/Completeness.lean), `code`, `codeVerifier`, `two_pow_length_header_code_mul_le` | Theorem 19 |

The formal statement differs from the source in these modelling choices:

- **Verifier-form machines.** The library's universal machine (`Kolmogorov.DescriptionMethod.universalTMRunFor`) is deterministic. `BoundedHalting.Accepts c z t` therefore asks for a witness `v` with `|v| ≤ t` such that program `c`, run for `t` steps on `(z, v)`, returns `[true]`. This is the guess-and-verify form of a `t`-step nondeterministic machine. No bridge to a separate nondeterministic machine model is provided.
- **Header code.** An instance is `frame c ++ frame (lenWord |z|) ++ z ++ 1^t`. The program costs `2|c| + 1` header bits rather than the source's `ℓ + 2 log ℓ`. Since `c` is fixed for each source problem, this changes only the constant in the domination factor. Words that are not padded headers are not in `BH`, as in the source.
- **Code across lengths.** The source's `C` is injective for each fixed `n`. The reduction uses `code x = frame (lenWord |x|) ++ compress x`, which is injective on all words, so the simulated verifier can decode `x` without knowing `n`.
- **Finite precision.** The source takes the longest common prefix of the binary expansions of two cdf values. `compress` instead takes the common prefix of `⌊a 2^n⌋` and `⌈b 2^n⌉ - 1`, where `a` and `b` are the cdf values below and at `x`. `Nat.lt_commonPrefix_mid_le` shows that the resulting dyadic point lies in `(a, b]`, which gives injectivity.
- **Domination at every word.** The reduction meets the strengthened condition of `DistReduction` because it is injective.

**Not yet proved:** the Impagliazzo–Levin extension to `SampNP`. It is tracked on the [roadmap](../../ROADMAP.md#average-case-complexity).

## Bridge to mild hardness

[not_mildlyHardOnAverageDet_of_mem_HeurP](../../Complexity/Computability/Complexity/Classes/AverageCase/MildHardness.lean) shows the following. If `({x | b x = true}, Ensemble.uniform) ∈ HeurP`, then `fun x => (b x).toNat` is not `MildlyHardOnAverageDet`. The proof runs the scheme with confidence `2 p(n)`, which errs with probability at most `1/(2p(n)+1) < 1/p(n)`. Because the bound holds at every length (`exists_heuristic_of_mem_HeurP`), `not_mildlyHardOnAverageIO_of_mem_HeurP` also rules out infinitely-often hardness. `not_mildlyHardOnAverage_of_mem_HeurP` gives the strict-PPT version through the existing PPT-to-deterministic specialization. Only Boolean targets under the uniform ensemble are bridged.

## Checked examples

[ComplexityTests/AverageCaseDistributional.lean](../../ComplexityTests/AverageCaseDistributional.lean) checks the following:

- uniform `PComp` and `PSamp`, and a concrete cdf value;
- bit complementation as a dominating reduction (`flipReduction`, factor `1`);
- no length map and polynomial make duplication `x ↦ x ++ x` dominated by the uniform ensemble (`not_dominates_dup`);
- `{0^n : n ∈ K}` lies in `AvgDeltaP (fun n => 2^{-n})` for **every** `K : Set ℕ`, including undecidable `K`. Classes with a fixed failure bound therefore contain undecidable problems, while `AvgP` requires failure below every `1/(k+1)`;
- membership of `(Set.univ, uniform)` in `AvgP`, `HeurP` and `DistNP`;
- a bridge instance.

[ComplexityTests/AverageCaseCompleteness.lean](../../ComplexityTests/AverageCaseCompleteness.lean) checks the following:

- the prefix and predecessor facts on concrete words, and a common-prefix split of `5 < 6`;
- Claim 20 for the uniform ensemble, under which no word is heavy;
- the header length and the exact probability `2^{-9}` of a concrete `BH` instance, and that the empty word is not in `BH`;
- `(BH, U^BH) ∈ DistNP`, completeness, and the `AvgP`/`HeurP` corollaries.

[bt06]: ../sources.md#bt06
[lev86]: ../sources.md#lev86
