# Mechanism design

The modules under `Complexity/GameTheory/Mechanism/` formalize sealed-bid mechanisms with
quasilinear utilities, following Roughgarden's CS364A lecture notes (2013), Lectures 2–4 and 7.
They are mathematical models of incentives: allocation and payment rules are arbitrary real
functions, and no running time is charged. Hardness and approximation of the allocation
problems, such as knapsack, are separate questions.

## Single-parameter environments

Import `Complexity.GameTheory.Mechanism.Myerson` (or a module above it). In
`Cslib.GameTheory.SingleParameter`, a `Mechanism ι` pairs an allocation rule and a payment rule,
both of type `(ι → ℝ) → ι → ℝ`. Bidder `i` with valuation `v` facing bids `b` has utility
`M.utility i v b = v * M.allocation b i - M.payment b i`. The conventions that affect statements
are:

- Bids and valuations are real. Every incentive predicate quantifies only over *nonnegative*
  bid profiles `0 ≤ b` and valuations `0 ≤ v`, so values of a rule on profiles with a negative
  entry never matter (`Mechanism.IsDSIC.congr`, `Mechanism.IsIR.congr`).
- `IsDSIC` is truthfulness alone: replacing `b i` by `v` never lowers utility. Individual
  rationality `IsIR` is a separate predicate. Roughgarden's "DSIC" bundles both (Lecture 2,
  Theorem 5.1 (1)).
- `IsMonotone x` says each curve `z ↦ x (Function.update b i z) i` is monotone on `[0, ∞)`
  when `0 ≤ b`. `IsImplementable x` says some payment rule makes `⟨x, p⟩` DSIC.
- `IsNormalized M` is the normalization `p_i(0, b₋ᵢ) = 0` of Myerson's Lemma (b).
- `IsWelfareMaximizing X x` asks that on every nonnegative profile `x b ∈ X` maximizes the
  reported welfare `∑ i, b i * y i` over `y ∈ X`; tie-breaking is arbitrary.

Myerson's payment is `myersonPayment x b i = b i * x b i - ∫ z in 0..b i, x (update b i z) i`,
and `myerson x` is the mechanism with these payments. The main results hold for *every*
monotone rule, not only piecewise-constant ones:

- `isImplementable_iff_isMonotone` (Lecture 3, Theorem 4.3 (a)), with `myerson_isDSIC` for
  sufficiency and `Mechanism.IsDSIC.isMonotone` for necessity.
- `Mechanism.IsDSIC.payment_eq`: every DSIC payment rule equals the zero-bid payment plus
  Myerson's payment. `Mechanism.IsDSIC.payment_eq_myersonPayment` is uniqueness under
  normalization (Theorem 4.3 (b), (c)).
- `myerson_isIR`, `myersonPayment_nonneg` and `myersonPayment_le` give the payment range
  `0 ≤ p ≤ b x` of Lecture 3, (1).
- `IsWelfareMaximizing.isMonotone`: welfare maximization is monotone for any tie-breaking, so
  it is implementable in every single-parameter environment.

The uniqueness proof does not differentiate. It shows that `u(v) - ∫₀ᵛ x` is constant by
summing the swap inequalities over uniform partitions and letting the mesh go to zero. The
private lemmas stay one-dimensional, so the same argument applies to any monotone curve.

## 0-1 rules, Vickrey and knapsack auctions

`Complexity.GameTheory.Mechanism.CriticalBid` treats `IsBinary` rules (`x b i ∈ {0, 1}` on
nonnegative profiles). `criticalBid x b i` is the infimum of the winning nonnegative bids, and
`criticalBidMechanism x` charges it to winners. `criticalBid_mul_eq_myersonPayment` identifies
these payments with Myerson's. `criticalBid_eq_of_threshold` and `isMonotone_of_threshold`
compute them from a threshold description.

`Complexity.GameTheory.Mechanism.Vickrey` defines the second-price auction on a linearly
ordered finite bidder type. The winner is the highest bidder, with ties going to the smallest
index (`Wins`), and pays `highestOtherBid b i`, which is `0` with a single bidder. The theorems
`mechanism_isDSIC`, `mechanism_isIR`, `isWelfareMaximizing_allocation` (over
`singleItemFeasible`) and `mechanism_payment_eq_myersonPayment` are Lecture 2, Claims 4.1–4.2 and
Theorem 5.1 (1)–(2), and Lecture 3, §6.

`Complexity.GameTheory.Mechanism.Knapsack` defines `knapsackFeasible w W`, the 0-1 vectors with
`∑ wᵢ xᵢ ≤ W`. `exists_knapsack_isWelfareMaximizing` gives a welfare-maximizing rule whose
critical-bid mechanism is DSIC and IR with Myerson's payments (Lecture 4, §1.2–1.3). It is an
existence theorem: it does not choose or analyze an algorithm.

## General environments and VCG

Import `Complexity.GameTheory.Mechanism.VCG`. In `Cslib.GameTheory`, a `Mechanism ι Ω` chooses
an outcome in `Ω` from reported valuations `b : ι → Ω → ℝ` and charges payments. Valuations are
arbitrary real functions for DSIC; `IsIR` assumes `0 ≤ b i` for the truthful agent.
`groves_isDSIC` proves that a Groves mechanism with a welfare-maximizing outcome rule is DSIC,
for any outcome type, provided the pivot ignores the agent's own report. With finitely many
outcomes, `vcg f` uses the Clarke pivot `clarkePivot` (a `Finset.sup'`). `vcg_isDSIC`,
`vcg_payment_nonneg` and `vcg_isIR` are Lecture 7, Theorem 2.1 and the remarks after (2) and
(4). `exists_isDSIC_isWelfareMaximizing` packages them for `[Finite Ω] [Nonempty Ω]`.

## Worked examples

The [checked examples](../../ComplexityTests/MechanismDesign.lean) show the following:

- A Vickrey auction on bids `(3, 5, 4)`: bidder `1` wins and pays `4`. With a tie on `(5, 5)`,
  bidder `0` wins.
- A single-bidder rule that allocates only to low bids is not monotone and so not
  implementable.
- For the linear rule `xᵢ(b) = bᵢ`, Myerson's payment is `bᵢ²/2` and the mechanism is DSIC.
- In a two-agent public project, VCG charges the pivotal agent its externality `1`.
- Knapsack feasibility holds and fails on small inputs, and the existence theorems are
  nonvacuous.

To prove that a concrete rule is implementable, prove `IsMonotone` by `intro i b hb z hz z' hz'
hzz'` followed by `change` to the explicit curve inequality. Then apply `myerson_isDSIC`, or, for
0-1 rules, give a threshold and use `isMonotone_of_threshold`.

## Known Limitations

Only dominant-strategy, deterministic, sealed-bid mechanisms are covered. Not yet formalized:
the sponsored-search payment formula (Lecture 3, (8)–(9)), the greedy knapsack rule and its
½-approximation (Lecture 4, §2.2, Theorem 2.1), Bayesian revenue maximization with virtual
values (Lecture 5), the Green–Laffont/Holmström characterization of DSIC welfare maximizers, and
any computational cost of allocation rules. See `ROADMAP.md` and issue #2907.
