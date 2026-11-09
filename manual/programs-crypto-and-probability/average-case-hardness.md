# Average-case heuristics and the Liu–Pass bridge

This family specifies how often an efficient algorithm can compute or approximate a numerical function on uniformly random bit strings. It uses the [native strict-PPT model](programs-and-realization.md), and connects the [clocked Kolmogorov model](../machines-and-classes/computability-and-description.md) to [uniform one-way functions](security-games-and-primitives.md). These are hardness predicates on functions, not a new machine instruction set [complexitylib][complexitylib].

Levin's distributional framework, which pairs languages with arbitrary ensembles and defines `AvgP`, `HeurP` and dominating reductions, is described in [Distributional problems, AvgP, HeurP and Levin reductions](distributional-complexity.md). Its bridge theorem shows that a Boolean target whose uniform distributional problem lies in `HeurP` is not mildly hard on average.

## Heuristics, success events, and quantifiers

[MildlyHardOnAverage](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L94) chooses one polynomial `p : Polynomial ℕ`, positive at every natural input, before quantifying over heuristics. For every `H : List Bool → ProbComp ℕ` with `IsPPTOn encBits encNat H`, there is a length threshold, allowed to depend on `H`, after which

`Pr[x ← uniform {0,1}^n; v ← H(x): v = f(x)] ≤ 1 − 1/p(n)`.

The probability averages both the input and the heuristic's coins. The heuristic gets the input string, with its length available from that input; the definition adds no length-dependent advice. Native efficiency is uniform over all inputs. The target `f` need not be computable. A deterministic heuristic instead has `ComputableInPolyTime H encBits encNat`, and the only randomness is the uniform input.

The actual variants are:

| Declaration | Heuristic | Correctness event | Required lengths |
|---|---|---|---|
| [MildlyHardOnAverage](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L94) | Uniform strict PPT | `v = f(x)` for Nat-valued `f` | Eventually all |
| [MildlyHardOnAverageToApprox](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L111) | Uniform strict PPT | `Nat.dist v (f x) ≤ g(n)` | Eventually all |
| [MildlyHardOnAverageToOneSidedApprox](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L129) | Uniform strict PPT | `f(x) − g(n) ≤ v ≤ f(x)`, with Nat subtraction | Eventually all |
| [MildlyHardOnAverageDet](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L140) | Deterministic polynomial time | Exact equality | Eventually all |
| [MildlyHardOnAverageToApproxDet](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L149) | Deterministic polynomial time | Symmetric `g` approximation | Eventually all |
| [MildlyHardOnAverageToOneSidedApproxDet](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L159) | Deterministic polynomial time | One-sided `g` approximation | Eventually all |
| [MildlyHardOnAverageIO](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L169) | Deterministic polynomial time | Exact equality | Infinitely often |
| [MildlyHardOnAverageToApproxIO](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L178) | Deterministic polynomial time | Symmetric `g` approximation | Infinitely often |
| [MildlyHardOnAverageToOneSidedApproxIO](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L188) | Deterministic polynomial time | One-sided `g` approximation | Infinitely often |
| [MildlyHardOnAverageENat](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L198) | Uniform strict PPT, Nat output | `(v : ℕ∞) = f(x)` | Eventually all |
| [MildlyHardOnAverageIOENat](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L208) | Deterministic polynomial time, Nat output | `(v : ℕ∞) = f(x)` | Infinitely often |

Every row chooses the positive gap polynomial before its heuristic. In the infinitely-often rows the qualifying lengths can depend on that heuristic. There is no claim here that deterministic infinitely-often hardness is equivalent to eventual PPT hardness. The source proves specialization in the expected direction: PPT hardness implies deterministic hardness, and deterministic eventual hardness implies its infinitely-often companion. An ENat target can take `∞`, which no finite output can equal; finiteness therefore matters when connecting those predicates to natural-valued Kolmogorov complexity.

## Approximation and finiteness bridges

[MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L316) converts one-sided `2g` hardness into symmetric `g` hardness when `x ↦ g(x.length)` is natively polynomial time. The proof shifts a purported symmetric approximator downward; the same inverse-polynomial failure gap is preserved. A deterministic companion is provided. These are proved bridges, not definitional identifications. Smaller success windows inherit hardness; approximation hardness also implies exact hardness.

[mildlyHardOnAverageENat_timeBounded_iff](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Kolmogorov/AverageCase.lean#L67) and its IO companion identify the ENat and Nat target versions when `n+1 ≤ t(n)` for every `n`. A literal-printing program supplies that sufficient clock, ensuring finite `K^t`; the Nat wrapper alone does not establish finiteness. The [description-method chapter](../machines-and-classes/computability-and-description.md) explains the underlying machine encoding and step clock.

## Main equivalences and their exact scope

Write `K^t` for the library's `timeBoundedNat t`, and `OWF` for existence of a function satisfying its uniform native `OneWay` predicate. The main theorem statements are:

| Endpoint | Right-hand side equivalent to `OWF` |
|---|---|
| [Exact Nat target](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay/LiuPass.lean#L880) | Some polynomial `p`, with `n+1 ≤ p(n)` at every length, makes `K^p` mildly hard against uniform strict PPT |
| [Exact ENat target](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay/LiuPass.lean#L892) | The same polynomial-clock statement for `timeBounded p` and the ENat hardness predicate |
| [Polynomial threshold](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay/LiuPass.lean#L905) | Some such polynomial `p` makes `K^t` mildly hard for every natural-valued clock `t ≥ p` pointwise |
| [Symmetric approximation](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay/LiuPass.lean#L922) | For every natural `d`, some such polynomial `p` makes every `K^t`, `t ≥ p`, hard to approximate within `d·(floor(log₂ n)+1)` |

The approximation equivalences also appear with ceiling and floor integer logarithms. The real `d log₂ n` success window follows from the upper-rounded window; it is exposed as an eventual probability bound rather than an extra primitive hardness definition. In the threshold statements `t` itself is not required to be polynomial or computable. The threshold may depend on the OWF and approximation constant, and is obtained from a native polynomial-time generator certificate. These theorems are conditional equivalences; they do not establish that an OWF or a hard `K^t` exists.

The local proof route goes through conditional entropy-preserving PRGs and the Kolmogorov generator/counting bounds, combined with the Section 4 converse in `OneWay/LiuPassConverse.lean`. The [constant-zero counterexample](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/AverageCase.lean#L586) is a useful negative witness that the generic exact hardness predicate is not automatic.

## Source correspondence and evidence

Liu–Pass Definitions 2.4–2.5 and Theorem 3.1 use strict success inequalities and, in part (c), every polynomial clock at least `(1+ε)n`. The library uses `≤` with an existential positive inverse-polynomial gap; elementary gap rescaling accounts for that inequality convention. Its clock conclusion is the **polynomial-threshold form**, not the paper's near-linear range. The source explicitly identifies the missing rate-1 generator argument and distinguishes `p(n) ≥ n+1` as a sufficient native finiteness condition from the paper's positive-clock wording. Retain those differences when applying the theorem [liupass20][liupass20].

The definitions and listed theorem statements were inspected at `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`; the primary paper's Definitions 2.4–2.5 and Theorem 3.1 were checked in arXiv v1. This is not a full audit of either proof. Existing `CslibFrontierTests/AverageCase.lean` and `CslibFrontierTests/LiuPass.lean` were located as regression evidence; no tests or Lean build were run in this revision.

[complexitylib]: ../sources.md#complexitylib
[liupass20]: ../sources.md#liupass20
