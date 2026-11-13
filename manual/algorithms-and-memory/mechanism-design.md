# Mechanism design

The modules under `CslibFrontier/GameTheory/Mechanism/` formalize sealed-bid mechanisms with
quasilinear utilities, following Roughgarden's CS364A lecture notes (2013), Lectures 2–5 and 7.
They are mathematical models of incentives: allocation and payment rules are arbitrary real
functions, and no running time is charged. Hardness and approximation of the allocation
problems, such as knapsack, are separate questions. Preference aggregation without money, starting
with Arrow's impossibility theorem and the Gibbard–Satterthwaite theorem, is in
`CslibFrontier/GameTheory/SocialChoice/` and is described
[below](#social-choice-arrows-impossibility-theorem).

## Single-parameter environments

Import `CslibFrontier.GameTheory.Mechanism.Myerson` (or a module above it). In
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
- `IsNormalized M` is the normalization `p_i(0, b_{-i}) = 0` of Myerson's Lemma (b).
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

The uniqueness proof does not differentiate. It shows that `u(v) - ∫ x` over `[0, v]` is constant by
summing the swap inequalities over uniform partitions and letting the mesh go to zero. The
private lemmas stay one-dimensional, so the same argument applies to any monotone curve.

## 0-1 rules, Vickrey and knapsack auctions

`CslibFrontier.GameTheory.Mechanism.CriticalBid` treats `IsBinary` rules (`x b i ∈ {0, 1}` on
nonnegative profiles). `criticalBid x b i` is the infimum of the winning nonnegative bids, and
`criticalBidMechanism x` charges it to winners. `criticalBid_mul_eq_myersonPayment` identifies
these payments with Myerson's. `criticalBid_eq_of_threshold` and `isMonotone_of_threshold`
compute them from a threshold description.

`CslibFrontier.GameTheory.Mechanism.Vickrey` defines the second-price auction on a linearly
ordered finite bidder type. The winner is the highest bidder, with ties going to the smallest
index (`Wins`), and pays `highestOtherBid b i`, which is `0` with a single bidder. The theorems
`mechanism_isDSIC`, `mechanism_isIR`, `isWelfareMaximizing_allocation` (over
`singleItemFeasible`) and `mechanism_payment_eq_myersonPayment` are Lecture 2, Claims 4.1–4.2 and
Theorem 5.1 (1)–(2), and Lecture 3, §6.

`CslibFrontier.GameTheory.Mechanism.Knapsack` defines `knapsackFeasible w W`, the 0-1 vectors with
`∑ wᵢ xᵢ ≤ W`. `exists_knapsack_isWelfareMaximizing` gives a welfare-maximizing rule whose
critical-bid mechanism is DSIC and IR with Myerson's payments (Lecture 4, §1.2–1.3). It is an
existence theorem: it does not choose or analyze an algorithm.

## General environments and VCG

Import `CslibFrontier.GameTheory.Mechanism.VCG`. In `Cslib.GameTheory`, a `Mechanism ι Ω` chooses
an outcome in `Ω` from reported valuations `b : ι → Ω → ℝ` and charges payments. Valuations are
arbitrary real functions for DSIC; `IsIR` assumes `0 ≤ b i` for the truthful agent.
`groves_isDSIC` proves that a Groves mechanism with a welfare-maximizing outcome rule is DSIC,
for any outcome type, provided the pivot ignores the agent's own report. With finitely many
outcomes, `vcg f` uses the Clarke pivot `clarkePivot` (a `Finset.sup'`). `vcg_isDSIC`,
`vcg_payment_nonneg` and `vcg_isIR` are Lecture 7, Theorem 2.1 and the remarks after (2) and
(4). `exists_isDSIC_isWelfareMaximizing` packages them for `[Finite Ω] [Nonempty Ω]`.

`IsDSICOn M V` restricts DSIC to valuation domains `V i`. A single-parameter environment is the
domain of linear valuations `linearValuation x i v = fun ω => v * x ω i` for an allocation map
`x : Ω → ι → ℝ` and `v ≥ 0` (`linearDomain x i`). Import
`CslibFrontier.GameTheory.Mechanism.LinearValuation` to move between the two models:

- `M.toSingleParameter x` runs a general mechanism on the reports `linearProfile x b` of scalar
  bids `b`. `isDSIC_toSingleParameter_iff` says that it is DSIC in the single-parameter sense
  exactly when `M.IsDSICOn (linearDomain x)`. `IsDSIC.toSingleParameter` and
  `IsIR.toSingleParameter` (for `0 ≤ x`) transfer the general properties.
- In the other direction, `SingleParameter.Mechanism.toMechanism` is a single-parameter mechanism
  on allocation vectors `Ω = ι → ℝ`, reading bidder `j`'s bid off its reported value of
  `Pi.single j 1`. `toSingleParameter_toMechanism` recovers the mechanism, and
  `isDSIC_iff_isDSICOn_toMechanism` restates single-parameter DSIC.

`CslibFrontier.GameTheory.Mechanism.VickreyVCG` specializes VCG to Vickrey. The single-item
outcomes are `Option ι`, with allocation `singleItem`. The Clarke pivot of the linear valuations of
`b` is `highestOtherBid b i` (`clarkePivot_linearProfile_singleItem`), so every welfare-maximizing
rule charges the second price to whoever gets the item (`vcg_payment_linearProfile_singleItem`).
`winner b` is the Vickrey winner as an outcome (`winner_eq_some`, `winner_eq_none`). Any
welfare-maximizing rule that picks `winner b` on the linear valuations of `b` makes VCG allocate
and charge at `b` exactly as `Vickrey.mechanism` (`vcg_toSingleParameter_eq_of_eq_winner`), and
`exists_vcg_toSingleParameter_eq` provides such a rule for all nonnegative bids.

## Revenue maximization: virtual values and Myerson's optimal auction

Import `CslibFrontier.GameTheory.Mechanism.OptimalAuction` (Lecture 5; Myerson 1981). Valuations are
independent, bidder `i`'s drawn from `μ i`. Expectations are Bochner integrals over the product
`Measure.pi μ` of the payments at truthful bids `v`. The revelation principle is not formalized: a
DSIC mechanism is compared with other DSIC mechanisms, both played truthfully.

- `HasValueDensity μ f h` says `μ = (volume.restrict (Icc 0 h)).withDensity f` with
  `f : ℝ → NNReal` measurable and positive on `(0, h)`. Positivity matters: `virtualValue μ f v =
  v - μ.real (Ioi v) / f v` uses Lean's `x / 0 = 0`. Atoms and unbounded supports are excluded.
- `IsRegular μ f h` is strict monotonicity of `virtualValue μ f` on `[0, h]` (Definition 3.1).
  `IsRegular.strictMonoOn_Ici` extends it to `[0, ∞)`, where `φ(v) = v` above `h`. Endpoint
  convention: the predicate includes `v = 0`, where `φ(0) = -1/f(0)` depends on the chosen value
  `f(0)`. So it needs `f(0) > 0` with `-1/f(0) < φ(v)` on `(0, h]`, and in particular `φ` bounded
  below near `0`. This is strictly stronger than Definition 3.1 when `(1 - F)/f → ∞` at `0`. For
  example, `f(v) = 2v` on `[0, 1]` is regular in the textbook sense but never `IsRegular`.
- `HasValueDensity.integral_payment_eq_integral_virtualValue_mul` is the one-bidder identity
  `E[v g(v) - ∫₀ᵛ g] = E[φ(v) g(v)]` for any measurable `g` bounded on `[0, h]`. The proof
  only reverses the order of integration and does not integrate by parts, so `g` need not be
  monotone.
- `integral_sum_myersonPayment_eq` (Revenue module, eq. (6)) states that expected revenue equals
  expected virtual welfare for a measurable rule bounded on nonnegative profiles.
  `Mechanism.IsDSIC.integral_sum_payment_eq` gives the same for normalized DSIC mechanisms, and
  `Mechanism.IsDSIC.integral_sum_payment_le` gives the inequality for DSIC and IR mechanisms.
- `IsVirtualWelfareMaximizing φ X x`: on every nonnegative profile `x b ∈ X` maximizes
  `∑ i, φ i (b i) * y i`. `integral_sum_payment_le_myerson` is the optimality theorem: if `X ⊆ [0,
  1]^ι` and `x` is a measurable virtual-welfare maximizer, then `myerson x` has the largest expected
  revenue among DSIC, IR mechanisms with measurable allocations in `X`. The inequality does not
  use regularity. Regularity makes `myerson x` DSIC through `IsVirtualWelfareMaximizing.isMonotone`
  and `myerson_isDSIC_of_isVirtualWelfareMaximizing`, for any tie-breaking.
- Single item, i.i.d. bidders: `Vickrey.reserveAllocation φ` sells to the Vickrey winner when its
  virtual value is nonnegative. `Vickrey.integral_sum_payment_le_reserve` is its optimality. The
  winner pays `max r (highestOtherBid b i)` (`Vickrey.myersonPayment_reserveAllocation`) for any
  `IsReserveThreshold φ r`. `IsRegular.isReserveThreshold` shows that `reservePrice φ =
  sInf {v | 0 ≤ v ∧ 0 ≤ φ v}` is one, even when `φ` is discontinuous, and `reservePrice_uniform`
  gives `1/2` for `U[0, 1]`. `Vickrey.integral_sum_payment_le_secondPriceReserve` states the
  optimality with these second-price-with-reserve payments written out.

Measurability of the virtual-welfare maximizer is a hypothesis of
`integral_sum_payment_le_myerson`, because no measurable argmax selection is formalized. For the
single-item rule it is proved (`Vickrey.measurable_reserveAllocation`), and so is the
measurability of the plain Vickrey rule (`Vickrey.measurable_allocation`).

To apply the theorem to a new distribution, prove `HasValueDensity` (following
`hasValueDensity_uniform`), then `IsRegular` by computing `virtualValue` on `[0, h]` (following
`virtualValue_uniform`). Supply a measurable virtual-welfare maximizer. If regularity fails, the
inequality still holds, but `myerson x` need not be DSIC; that case needs ironing, which is not
formalized.

If `IsRegular` gets stuck at `v = 0`, check the density's value there. Choose `f(0) > 0`, for
example by redefining `f` at the single point `0`. This does not change `μ`, since
`withDensity` ignores null sets. Then show that `-1/f(0)` lies below `φ` on `(0, h]`. If
`(1 - F(v))/f(v) → ∞` as `v → 0⁺`, as for `f(v) = 2v`, then no choice of `f(0)` works. In that
case the DSIC and single-item results (`IsVirtualWelfareMaximizing.isMonotone`,
`Vickrey.integral_sum_payment_le_reserve`) do not apply yet. `integral_sum_payment_le_myerson`
itself still holds, since it does not assume regularity. The checked examples prove that
`f(v) = 2v` fails `IsRegular` for every choice of `f(0)`.

## Bayes–Nash equilibrium, revenue equivalence and the first-price auction

Import `CslibFrontier.GameTheory.Mechanism.Bayesian` (Hartline, *Mechanism Design and Approximation*,
Chapter 2, version of 20 September 2021 [hartline21]). Bidder `i`'s valuation is drawn from `μ i`,
supported on `[0, h i]`, and bidder `i` bids `β i v` on valuation `v`. The interim rules
`M.interimAllocation μ β i z` and `M.interimPayment μ β i z` are the expected allocation and payment
of bid `z`, an integral over `Measure.pi μ` in which coordinate `i` is overwritten by `z`.
Hartline's interim rules indexed by values are their compositions with `β i`.

- `M.IsBayesNash μ h β` requires, for every bidder and *every* type `v ∈ [0, h i]` (not almost
  every), a legal bid `0 ≤ β i v` that no legal bid `z ≥ 0` beats in interim utility. Bids
  outside the range of `β i` count as deviations. The definition does not link `h` to `μ`: `h i`
  is meant to be the support bound and `μ i` a probability measure, which the revenue results
  assume; otherwise it can hold vacuously (`h i < 0`, or some `μ j = 0`).
- `IsTruthfulOn X P s` (in `SingleParameter`) is one-dimensional incentive compatibility of a
  curve pair; `IsTruthfulOn.monotoneOn` is the swap argument, and DSIC along one bidder's own bid
  is `IsTruthfulOn` on `[0, ∞)` (`Mechanism.IsDSIC.isTruthfulOn`), which Myerson's Lemma uses. On
  `[0, h]` it is equivalent to monotonicity of `X` plus `P v = P 0 + (v X v - ∫₀ᵛ X)`
  (`IsTruthfulOn.payment_eq`, `isTruthfulOn_of_payment_eq`). The proof reuses Myerson's DSIC
  lemmas through a private one-bidder mechanism on the bid projected to `[0, h]`
  (`Set.projIcc`), so nothing is re-derived.
- `IsBayesNash.monotoneOn` and `IsBayesNash.interimPayment_eq` are Theorem 2.5.1. The converse,
  `isBayesNash_iff`, replaces Hartline's assumption of onto strategies by the condition that every
  legal bid is weakly dominated by the bid of some type in the support. Onto strategies meet it
  with equality, and it is the check (v)(b) of Hartline's §2.8 that the first-price equilibrium
  needs.
- `IsBayesNash.integral_sum_payment_eq` is the Bayes–Nash revenue formula: the zero types' interim
  payments plus the expected virtual welfare of the equilibrium allocation. It needs probability
  measures with `HasValueDensity`, integrable payments and measurable, bounded allocations.
  `IsBayesNash.integral_payment_eq_integral_interimAllocation` is the per-bidder interim form
  `pᵢ(0) + E[φᵢ(vᵢ) xᵢ(vᵢ)]`, which needs no measurability of the ex post allocation.
- Revenue equivalence (Corollary 2.7.1, with equal rather than zero payments of the zero types):
  `IsBayesNash.integral_sum_payment_eq_of_interimAllocation_ae_eq` assumes interim allocation
  rules equal for almost every type, Hartline's "same BNE allocation";
  `IsBayesNash.integral_sum_payment_eq_of_allocation_ae_eq` assumes the stronger almost sure
  equality of ex post allocations; `IsBayesNash.interimPayment_eq_of_interimAllocation_eq` is the
  type-by-type form.

`CslibFrontier.GameTheory.Mechanism.FirstPrice` defines the first-price auction
(`FirstPrice.mechanism`, Vickrey's winner, who pays its bid) and the strategy
`uniformBid n v = (n - 1) v / n`. `isBayesNash_uniformBid` proves that for `n` bidders with values
uniform on `[0, 1]` this is a Bayes–Nash equilibrium. Its expected revenue is `(n - 1) / (n + 1)`
(`integral_sum_payment_uniformBid`), equal to the second-price auction's
(`integral_sum_payment_uniformBid_eq_vickrey`, Corollary 2.7.2 for the uniform distribution;
`integral_sum_payment_vickrey`). `not_isBayesNash_id` shows that truthful bidding is not an
equilibrium with two or more bidders. Hartline proves the two-bidder case (§2.3, Example 2.8.1); the
`n`-bidder formula is the standard generalization, derived here by the same method rather than
quoted.

To verify a candidate equilibrium of another auction, compute the interim allocation
`interimAllocation μ β i z` for every bid `z ≥ 0`, as `interimAllocation_uniformBid` does. Then
apply `isBayesNash_iff`: monotonicity and the payment identity are one-variable facts, and for
domination exhibit, for each bid outside the range, a type whose bid does at least as well.

## Social choice: Arrow's impossibility theorem

Import `CslibFrontier.GameTheory.SocialChoice.Arrow`. The namespace `Cslib.GameTheory.SocialChoice`
models preference aggregation: there are no payments or utilities, only rankings. Voters `V` rank
alternatives `A`. The preference model below is in `CslibFrontier.GameTheory.SocialChoice.Ranking`,
which the Arrow module imports publicly.

- `Ranking A` is a strict linear order, given by a relation `Prefers` that is irreflexive,
  transitive and total on distinct alternatives. `toTop b` and `toBottom b` move `b` to one end
  and keep the other alternatives in order. `IsTop` and `IsBottom` say that `b` is at an end.
  `Ranking.nonempty` gives a ranking of any type, by the Szpilrajn extension theorem.
- `WeakRanking A` is a complete preorder `AtLeast`, with strict part
  `Prefers a b := ¬ AtLeast b a`, so society may be indifferent. `Ranking.toWeakRanking` views a
  ranking as a weak ranking without ties.
- A `SocialWelfareFunction V A` maps every profile `V → Ranking A` to a `WeakRanking A`. Every
  profile of strict rankings is admissible (unrestricted domain); voters cannot be indifferent.
  This makes Arrow's theorem formally stronger, not weaker: Pareto and IIA are only assumed on
  strict profiles, so more rules are covered. The version in which voters may be indifferent
  follows by a short IIA reduction, which is not formalized.

Rankings are bundled structures, not `LinearOrder` instances, because a profile puts different
orders on the same type and the proof builds rankings pointwise. The bridge instances
`IsStrictTotalOrder A r.Prefers`, `IsPreorder A R.AtLeast` and `Std.Total R.AtLeast` give access to
Mathlib's unbundled order API. The axioms and the strict part of a weak ranking are `@[expose]`d,
so clients can unfold them.

The axioms are `IsPareto` (weak Pareto: if every voter strictly prefers `a` to `b`, so does
society), `IsIIA` (society's `AtLeast a b` depends only on each voter's `Prefers a b`;
`IsIIA.prefers_iff` gives the strict form), `IsDictator i` (whenever voter `i` strictly prefers `a`
to `b`, so does society) and `IsDictatorial`. `dictatorship i` adopts voter `i`'s ranking. The
main results:

- `isDictatorial_of_isPareto_of_isIIA`: with `[Finite V]` and three distinct alternatives
  (`∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c`), a weakly Pareto rule satisfying IIA is dictatorial.
  This is Arrow's theorem. `isDictatorial_of_three_le_card` takes `3 ≤ Fintype.card A` instead.
  The set of alternatives may be infinite.
- `existsUnique_isDictator_of_isPareto_of_isIIA`: the dictator is unique. By
  `isDictator_iff_eq_dictatorship`, a rule with dictator `i` is `dictatorship i`, so it has no
  ties. `isPareto_and_isIIA_iff` combines these: the weakly Pareto IIA rules are exactly the
  dictatorships.
- `isTop_or_isBottom_of_extremal`: the extremal lemma used in the proof.

The proof is the first of the three in Geanakoplos, *Three brief proofs of Arrow's impossibility
theorem* (Economic Theory, 2005). Suppose every voter
places `b` at one end of their ranking. Then society places `b` strictly at one end: otherwise
some `a ≥ b ≥ c` socially with `a ≠ c`, and moving `c` above `a` in every ranking, without moving
`b`, contradicts transitivity by IIA and Pareto. Next, move `b` from the bottom to the top one
voter at a time. An induction over `Finset`s finds an *extremely pivotal* voter `n`, whose move
takes `b` from the social bottom to the social top. Voter `n` dictates every pair `x, y ≠ b`:
consider a profile in which `n` ranks `x ≻ b ≻ y` and everyone else keeps `b` where it was. It
agrees with the pivotal profiles on `x` versus `b` and on `b` versus `y`. Finally, the pivotal
voters of different alternatives coincide, which covers the pairs containing `b`.

To apply the theorem to a concrete rule, prove `IsPareto` and `IsIIA` and obtain the dictator.
To show that a rule escapes it, find the hypothesis that fails. A rule with strict social rankings,
`F : Profile V A → Ranking A`, is covered through `fun P => (F P).toWeakRanking` and
`Ranking.toWeakRanking_prefers`, as in the checked example.

## Social choice: the Gibbard–Satterthwaite theorem

Import `CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaite`. It reuses `Ranking` and `Profile`
from `CslibFrontier.GameTheory.SocialChoice.Ranking`, and Arrow's theorem. A `SocialChoiceFunction V A`
maps every profile `V → Ranking A` to one alternative. The definitions, all in
`SocialChoiceFunction`, are `@[expose]`d:

- `IsStrategyProof`: for all profiles `P` and `Q` that differ only in voter `i`'s ranking, `i` does
  not strictly prefer `f Q` to `f P` by the true ranking `P i`. `isStrategyProof_iff` restates it
  with `Function.update`.
- `IsMaskinMonotone`: if no voter ranks an alternative above `f P` at `Q` that they ranked below it
  at `P`, then `f Q = f P`.
- `IsDictator i`: for every profile, voter `i` ranks the outcome above every other alternative in
  the *range* of `f`. For a rule onto `A`, `isDictator_iff_of_surjective` reduces this to `i`'s top
  alternative always being chosen. `IsDictatorial` asks for some dictator.
- `dictatorship i` chooses `(P i).top`, where `Ranking.top` is the top alternative of a ranking of a
  finite nonempty type.

The main results:

- `isStrategyProof_iff_isMaskinMonotone`: with `[Finite V]`, strategy-proofness and Maskin
  monotonicity are equivalent (Muller and Satterthwaite, 1977).
- `isDictatorial_of_isStrategyProof`: with `[Finite V]` and `3 ≤ (Set.range f).encard`, a
  strategy-proof rule is dictatorial. This is the Gibbard–Satterthwaite theorem in its range form.
  `isDictatorial_of_isMaskinMonotone` is the Muller–Satterthwaite theorem in the same form.
- `isDictatorial_of_isStrategyProof_of_surjective` is the onto form of
  [Nisan][nisan07], Theorem 9.8. It takes `Function.Surjective f` and three distinct alternatives.
- `isStrategyProof_and_surjective_iff`: with `[Finite V] [Finite A] [Nonempty A]` and three
  distinct alternatives, the strategy-proof onto rules are exactly the dictatorships.
  `IsDictator.isStrategyProof` gives one direction for every rule, onto or not.

The proof is the reduction to Arrow's theorem in [Nisan][nisan07], §9.2.4. Changing one voter's
report at a time shows that a strategy-proof rule is Maskin monotone. Let every voter move the
alternatives of a set `S` to the top of their ranking (`Ranking.toTopSet`). If `S` meets the range,
monotonicity and unanimity keep the outcome in `S`. Society then ranks `a` at least as high as `b`
when the outcome after every voter moves `a` and `b` to the top is `a`. This is a weak ranking,
weakly Pareto and IIA, so `SocialWelfareFunction.isDictatorial_of_isPareto_of_isIIA` gives a
dictator. Nisan's construction needs a rule onto `A`. For the range form, the induced social welfare
function ranks the range: each voter's ranking of the range is extended to `A` by placing the range
on top (`Ranking.extend`).

The ranking operations used by the proof are in the Ranking module: `Ranking.top`,
`Ranking.toTopSet`, `Ranking.restrict` and `Ranking.extend`, each with a definitional `_iff` lemma
or membership lemmas. The set of alternatives may be infinite, as for Arrow's theorem. The
electorate must be finite, since Arrow's theorem is used.

To apply the theorem to a concrete rule, prove `IsStrategyProof` (or `IsMaskinMonotone`) and
exhibit three distinct outcomes. To show that a rule escapes it, find the hypothesis that fails:
majority rule between two alternatives has only two outcomes, and a non-dictatorial rule with three
outcomes, such as the Borda count, must be manipulable.

## Worked examples

The [checked examples](../../CslibFrontierTests/GameTheory/MechanismDesign.lean) show the following:

- A Vickrey auction on bids `(3, 5, 4)`: bidder `1` wins and pays `4`. With a tie on `(5, 5)`,
  bidder `0` wins.
- A single-bidder rule that allocates only to low bids is not monotone and so not
  implementable.
- For the linear rule `xᵢ(b) = bᵢ`, Myerson's payment is `bᵢ²/2` and the mechanism is DSIC.
- In a two-agent public project, VCG charges the pivotal agent its externality `1`.
- VCG on single-item outcomes, run on linear valuations, is DSIC and individually rational as a
  single-parameter mechanism, and on bids `(3, 5, 4)` its Vickrey-tie-breaking instance charges
  bidder `1` the second price `4`.
- Knapsack feasibility holds and fails on small inputs, and the existence theorems are
  nonvacuous.

The [social choice examples](../../CslibFrontierTests/GameTheory/SocialChoice.lean) are a `module`
that uses only the public surface of the Arrow module. Dictatorship is weakly Pareto and IIA, so
the theorem is not vacuous. Three hypotheses are each tested against a rule that drops it:

- With three voters and two alternatives, pairwise majority rule is weakly Pareto, IIA and not
  dictatorial, so three alternatives are needed.
- With two voters and three alternatives, the Borda count is weakly Pareto and not dictatorial:
  when the two voters hold opposite rankings, every alternative has Borda score `2`. By Arrow's
  theorem the Borda count therefore violates IIA, so IIA is needed.
- Universal indifference is IIA but not weakly Pareto.

The examples also apply the theorem to three voters and three alternatives, and to a rule with
strict social rankings.

The [Gibbard–Satterthwaite examples](../../CslibFrontierTests/GameTheory/GibbardSatterthwaite.lean)
also use only the public surface. A dictatorship is strategy-proof and onto, so the theorem is not
vacuous; the theorem is applied to three voters and three alternatives and, in range form, to a rule
with values in `ℕ`. Majority rule between two alternatives `a` and `b`, ties going to `b`, is
strategy-proof. With at least two voters it is not dictatorial: a lone supporter of `a` cannot get
`a`. On `Bool` with three voters it is onto, so the theorem needs three alternatives. On `Fin 3` its
range is `{0, 1}`, so the hypothesis concerns the range, not the number of alternatives. On `Fin 4`,
the rule choosing voter `0`'s favourite among `{0, 1, 2}` is strategy-proof, has three outcomes and
is not onto. Voter `0` is its dictator, but the outcome is not always their top alternative, so for
rules that are not onto, a dictator gets their favourite outcome in the range. Finally, the Borda
count with two voters and three alternatives, ties going to the smaller alternative, is
manipulable. Voter `0` ranks `1 ≻ 0 ≻ 2` and voter `1` ranks `0 ≻ 1 ≻ 2`. The scores are
`(3, 3, 0)`, so the outcome is `0`. If voter `0` reports `1 ≻ 2 ≻ 0` instead, the scores are
`(2, 3, 1)` and the outcome is `1`. Both outcomes are checked by `decide`.

The [optimal-auction examples](../../CslibFrontierTests/GameTheory/OptimalAuction.lean) use
`U[0, 1]`, which has reserve price `1/2`. With two bidders, bids `(0.3, 0.4)` do not sell. On
`(0.6, 0.2)` bidder `0` pays `1/2`. On `(0.7, 0.9)` bidder `1` pays `0.7`. The plain Vickrey rule
is not a virtual-welfare maximizer, and Myerson's theorem compares Vickrey with and without the
reserve, so its hypotheses are satisfiable. The rising density `f(v) = 2v` on `[0, 1]` fails
`IsRegular` for every choice of `f(0)`, which illustrates the endpoint convention.

The [Bayes–Nash examples](../../CslibFrontierTests/GameTheory/BayesNash.lean) check that the
second-price interim rules `x(v) = v`, `p(v) = v²/2` are incentive compatible while a decreasing
curve is not. In the two-bidder first-price auction, bidding `v / 2` is an equilibrium, a bid of
`1/4` wins with probability `1/2`, truthful bidding is not an equilibrium, and both auctions earn
`1/3`. With three bidders the bid is `2v/3` and both earn `1/2`; a lone bidder bids `0`.

To prove that a concrete rule is implementable, prove `IsMonotone` by `intro i b hb z hz z' hz'
hzz'` followed by `change` to the explicit curve inequality. Then apply `myerson_isDSIC`, or, for
0-1 rules, give a threshold and use `isMonotone_of_threshold`. If monotonicity fails at some
nonnegative profile, the rule is not implementable at all (`isImplementable_iff_isMonotone`), as
in the `lowBidRule` example. A failure caused only by negative bids is irrelevant: change the
rule there, since `Mechanism.IsDSIC.congr` shows that DSIC ignores profiles with a negative
entry.

## Randomized Facility-Location Mechanisms

The randomized facility-location modules model mechanisms without money that map an `ι`-indexed
profile of reported locations on a pseudometric space `(G, [PseudoMetricSpace G]
[MeasurableSpace G])` (slightly generalizing the metric-space and graph-distance settings of
[Procaccia and Tennenholtz][procacciatennenholtz13], §3, p. 18:7, and
[Alon, Feldman, Procaccia, and Tennenholtz][alonfeldmanprocacciatennenholtz10], §2,
arXiv:0907.2049v1 p. 4) to a facility distribution `ProbabilityMeasure G`.

* [FacilityLocation.Basic](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Basic.lean):
  defines `socialCost x y := ∑ i, dist (x i) y`, `optSocialCost`, `IsOptimal`,
  `Mechanism ι G := (ι → G) → ProbabilityMeasure G`, the extended nonnegative Lebesgue expected
  distance `expectedECost μ loc := ∫⁻ y, edist loc y ∂μ` (`ℝ≥0∞`), and the real-valued Bochner
  integral `expectedCost μ loc := ∫ y, dist loc y ∂μ`. Defining `Mechanism.IsStrategyProof`,
  `Mechanism.IsWeakGroupStrategyProof`, `Mechanism.IsGroupStrategyProof`, and
  `Mechanism.HasApproxRatio` against `expectedECost` avoids Bochner integrability's `0`-default on
  infinite-moment distributions while recovering real-valued equivalences
  (`isStrategyProof_iff_expectedCost_le`, `hasApproxRatio_iff_expectedSocialCost_le`) whenever
  `HasFiniteCost` holds. Here `IsWeakGroupStrategyProof` (no nonempty coalition makes every
  member strictly better off) matches what PT §3 and AFPT §2 call "group strategyproofness", while
  `IsGroupStrategyProof` formalizes the stronger variant noted in passing in PT §3 (p. 18:7).
  `Mechanism.deterministic` and `Mechanism.ofPMF` embed deterministic rules and finite/countable
  `PMF` rules into `Mechanism`, using `PMF.toMeasure_eq_sum` and `PMF.lintegral_toMeasure` from
  [PMF.ToMeasure](../../CslibFrontier/Probability/PMF/ToMeasure.lean) for `expectedECost_ofPMF`.
  `HasApproxRatio.one_le` shows `1 ≤ α` whenever `G` is nontrivial and `2 ≤ Fintype.card ι`.
  For deterministic rules on a metric space, `unanimous_of_surjective_isStrategyProof` shows that
  surjective strategyproof rules are unanimous. `profile_update_induction`, which switches agents
  from one profile to another one at a time, is the shared induction behind that lemma, the
  interval and tree Pareto arguments and the cycle coalition argument.
* [FacilityLocation.Dictatorship](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Dictatorship.lean):
  proves on any pseudometric space (`[OpensMeasurableSpace G]`) that `dictatorship i₀` is strongly
  group strategyproof (`dictatorship_isGroupStrategyProof`) with the elementary worst-case
  approximation ratio `max 1 (Fintype.card ι - 1)` (`dictatorship_hasApproxRatio`), and that
  `randomDictatorship` (Mechanism 1 of [AFPT][alonfeldmanprocacciatennenholtz10], §3.2, arXiv
  p. 6: uniform `PMF.uniformOfFintype` over nonempty finite `ι`) is strategyproof
  (`randomDictatorship_isStrategyProof`) with approximation ratio `2 - 2 / Fintype.card ι`
  (`randomDictatorship_hasApproxRatio`, generalizing AFPT Theorem 3.1 and its first remark,
  arXiv pp. 6–7, from metric/graph spaces to pseudometrics). Both bounds share the per-agent
  shift lemma `socialCost_self_le`.
* [FacilityLocation.Median](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Median.lean):
  builds on [Fintype.OrderStatistic](../../CslibFrontier/Foundations/Data/Fintype/OrderStatistic.lean)
  (`Fintype.IsOrderStatistic`, `Fintype.orderStatistic`, `Fintype.lowerMedian`,
  `Fintype.upperMedian`, `Fintype.sum_abs_sub_lowerMedian_le`, and
  `Fintype.sum_abs_sub_upperMedian_le`, bridged to sorted multisets and `List.IsOrderStatistic`).
  Proves that every fixed `k`-th `orderStatisticMechanism` on `ℝ` (clamped at
  `Fintype.card ι - 1`) is strongly group strategyproof for all `k : ℕ`
  (`orderStatisticMechanism_isGroupStrategyProof`, strengthening the weak group strategyproofness
  noted in [Procaccia and Tennenholtz][procacciatennenholtz13], §3.1, pp. 18:7–18:8 and
  attributed there to [Moulin][moulin80], which was not directly inspected), shows
  `lowerMedian_isOptimal` and `upperMedian_isOptimal` for `socialCost` on `ℝ`, and concludes that
  `medianMechanism` (picking the lower median `x_((n - 1) / 2)` as the leftmost optimal point
  for even `n`, PT §3.1, p. 18:7) is both strongly group strategyproof
  (`medianMechanism_isGroupStrategyProof`) and `1`-approximate (`medianMechanism_hasApproxRatio_one`).
  Conversely, `not_isStrategyProof_meanMechanism` shows that `meanMechanism` (over `mean`,
  unfolded via `mean_def`) fails strategyproofness whenever `2 ≤ Fintype.card ι`.

The [facility-location checks](../../CslibFrontierTests/FacilityLocation.lean) verify concrete
`medianMechanism` and `Fintype.lowerMedian` evaluations on `![0, 1, 10]` (cost `10 =
optSocialCost < 12`) and even `n = 4` (`![0, 1, 2, 10]`, both `Fintype.lowerMedian = 1` and
`Fintype.upperMedian = 2` optimal with cost `11`), clamped `orderStatisticMechanism (ι := Fin 3) 5`,
non-strategyproof counterexamples for `meanMechanism` on `![0, 1, 1]` and the even-`n` midpoint
`midpointMedian4` on `![0, 1, 2, 3]`, tightness of ratio `2` for `dictatorship 0` on `Fin 3`,
strategyproofness and `(4/3)`-approximation of `randomDictatorship` on `Fin 3` over `ℝ` separated
from `IsGroupStrategyProof` (on `![0, 1, 2]` deviating to `![1, 1, 1]`) and
`IsWeakGroupStrategyProof` (on the 4-point star metric `Star4`, matching AFPT §3.2 third remark vs
line weak GSP in §3.2 fourth remark), a continuous uniform `[0, 1]` `ProbabilityMeasure ℝ`
evaluation (`expectedCost = 1/4` at `1/2`), and `constantZero2` failing every approximation ratio.

## Deterministic Strategyproof Location on Intervals, Trees, and Cyclic Graphs

Building on single-peaked metric preferences over `MetricGraph` tree and cycle geometry, three
modules characterize deterministic strategyproof onto mechanisms following
[Moulin][moulin80] (primary paper not read directly) and [Schummer and Vohra][schummervohra02] (author preprint, Theorems 1 and 2):

* [FacilityLocation.Interval](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Interval.lean):
  formalizes Moulin's generalized median rules via
  `MoulinScheme ι a b` (`MoulinScheme.eval`, `MoulinScheme.eval_surjective`,
  `MoulinScheme.eval_isGroupStrategyProof`). `isStrategyProof_and_surjective_iff_exists_moulinScheme`
  equates deterministic strategyproofness plus surjectivity on `Set.Icc a b` (`a < b`) with
  `MoulinScheme.eval`, `moulinScheme_of_isometry` transfers the characterization across any isometry
  from `Set.Icc a b`, and `moulinScheme_finTwo_eq` characterizes two-agent schemes.
* [FacilityLocation.Tree](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Tree.lean):
  formalizes extended median voter schemes `TreeEMVS W ι` for finite nonempty agents on a tree
  metric graph (`W.graph.IsTree`), proving unique equilibrium existence (`TreeEMVS.existsUnique_equilibrium`),
  defining `TreeEMVS.eval` (`TreeEMVS.eval_eq_iff`, `TreeEMVS.eval_const`,
  `TreeEMVS.eval_surjective`, `TreeEMVS.eval_isGroupStrategyProof`), and proving
  `isStrategyProof_and_surjective_iff_exists_treeEMVS` and automatic amplification from strategyproofness
  to strong group strategyproofness (`isGroupStrategyProof_of_isStrategyProof_of_surjective_tree`).
  `TreeEMVS` adapts the source's definition (consistent generalized median schemes on leaf-to-leaf
  paths, preprint Section 3, p. 12) to winning coalitions per direction at each point; its docstring
  describes the correspondence. The source's Theorem 1 (p. 15) states only strategyproofness; the
  strong group strategyproofness is an extension proved here.
* [FacilityLocation.Cycle](../../CslibFrontier/GameTheory/Mechanism/FacilityLocation/Cycle.lean):
  proves cycle dictatorship on graphs with cycles: for any shortest closed cycle (`IsShortestCycle W c`),
  `exists_cycleDictator_of_isShortestCycle` shows every deterministic strategyproof onto mechanism
  restricts to a dictatorship on profiles supported on `Set.range (circleMap ...)`,
  `exists_cycleDictator_of_not_isAcyclic` yields a shortest-cycle dictatorship whenever
  `¬ W.graph.IsAcyclic`, and `exists_dictatorship_of_cycleGraph` proves global dictatorship whenever
  `W.graph` is isomorphic to `SimpleGraph.cycleGraph (n + 3)`. The offset matters: Mathlib's
  `cycleGraph 2` is a single edge, whose realization is an interval with non-dictatorial median
  rules. The source's Theorem 2 (preprint p. 21) covers every cycle; only shortest cycles are
  formalized here.

The [Schummer–Vohra examples](../../CslibFrontierTests/SchummerVohra.lean) use strict `module`
visibility with `borel` measurable spaces on `MetricGraph` to instantiate a symmetric 3-agent
`MoulinScheme` alongside a constant non-onto counterexample, a 2-of-3 majority `TreeEMVS` on a
3-leaf star `star3` that evaluates `![vertex 1, vertex 2, vertex 3]` to `vertex 0` (non-dictatorial),
global dictatorship on `cycleGraph 3`, and a `Triangle + Tail` (`Fin 4`) group-strategyproof onto rule
that acts as player `0` on the shortest 3-cycle without being globally dictatorial.

## Known Limitations

Only deterministic, sealed-bid mechanisms are covered for auctions and VCG: dominant-strategy incentive compatibility in general, and Bayes–Nash equilibrium for single-parameter mechanisms. Not yet formalized:
the sponsored-search payment formula (Lecture 3, (8)–(9)), the greedy knapsack rule and its
1/2-approximation (Lecture 4, §2.2, Theorem 2.1), ironing for irregular distributions, regular
distributions whose virtual valuation is unbounded below at `0` (such as `f(v) = 2v`),
optimality among Bayesian incentive-compatible mechanisms (Lecture 5, §3.2), the revelation
principle, first-price equilibria for non-uniform or asymmetric priors and their uniqueness
(Hartline, §2.9), the all-pay auction, a measurable argmax for virtual-welfare maximization, the
Green–Laffont/Holmström characterization of DSIC welfare maximizers, and any
computational cost of allocation rules. See `ROADMAP.md` and issues #2947, #3001 and #3173.

For facility location, only single-facility mechanisms optimizing expected social cost (sum of
distances) are formalized. Strategyproof onto rules are characterized on intervals, trees, and
single shortest cycles / cycle graphs (`isStrategyProof_and_surjective_iff_exists_treeEMVS`,
`exists_cycleDictator_of_isShortestCycle`, `exists_dictatorship_of_cycleGraph`); arbitrary
non-shortest cycles, multi-cycle/block consistency, and the full cyclic-network quotient-tree
characterization (issue #4327) remain open. Also not yet formalized: maximum-cost (egalitarian)
objectives, multiple-facility (`k ≥ 2`) location, and impossibility/lower-bound theorems beyond
`1 ≤ α`.

For social choice, Arrow's theorem and the Gibbard–Satterthwaite theorem are formalized for strict
individual rankings. A finite electorate is necessary, but the infinite-electorate counterexample
built from a nonprincipal ultrafilter (Fishburn 1970) is not formalized. Also not formalized are the
corollary for individual weak orders, May's theorem, quantitative (Kalai) versions of Arrow's
theorem, and the complexity of winner determination and manipulation. See `ROADMAP.md` and issue
#3282.

[alonfeldmanprocacciatennenholtz10]: ../sources.md#alonfeldmanprocacciatennenholtz10
[hartline21]: ../sources.md#hartline21
[moulin80]: ../sources.md#moulin80
[nisan07]: ../sources.md#nisan07
[procacciatennenholtz13]: ../sources.md#procacciatennenholtz13
[schummervohra02]: ../sources.md#schummervohra02
