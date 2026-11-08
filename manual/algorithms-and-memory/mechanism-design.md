# Mechanism design

The modules under `Complexity/GameTheory/Mechanism/` formalize sealed-bid mechanisms with
quasilinear utilities, following Roughgarden's CS364A lecture notes (2013), Lectures 2–5 and 7.
They are mathematical models of incentives: allocation and payment rules are arbitrary real
functions, and no running time is charged. Hardness and approximation of the allocation
problems, such as knapsack, are separate questions. Preference aggregation without money, starting
with Arrow's impossibility theorem, is in `Complexity/GameTheory/SocialChoice/` and is described
[below](#social-choice-arrows-impossibility-theorem).

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

## Revenue maximization: virtual values and Myerson's optimal auction

Import `Complexity.GameTheory.Mechanism.OptimalAuction` (Lecture 5; Myerson 1981). Valuations are
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

## Social choice: Arrow's impossibility theorem

Import `Complexity.GameTheory.SocialChoice.Arrow`. The namespace `Cslib.GameTheory.SocialChoice`
models preference aggregation: there are no payments or utilities, only rankings. Voters `V` rank
alternatives `A`.

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

## Worked examples

The [checked examples](../../ComplexityTests/GameTheory/MechanismDesign.lean) show the following:

- A Vickrey auction on bids `(3, 5, 4)`: bidder `1` wins and pays `4`. With a tie on `(5, 5)`,
  bidder `0` wins.
- A single-bidder rule that allocates only to low bids is not monotone and so not
  implementable.
- For the linear rule `xᵢ(b) = bᵢ`, Myerson's payment is `bᵢ²/2` and the mechanism is DSIC.
- In a two-agent public project, VCG charges the pivotal agent its externality `1`.
- Knapsack feasibility holds and fails on small inputs, and the existence theorems are
  nonvacuous.

The [social choice examples](../../ComplexityTests/GameTheory/SocialChoice.lean) are a `module`
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

The [optimal-auction examples](../../ComplexityTests/GameTheory/OptimalAuction.lean) use
`U[0, 1]`, which has reserve price `1/2`. With two bidders, bids `(0.3, 0.4)` do not sell. On
`(0.6, 0.2)` bidder `0` pays `1/2`. On `(0.7, 0.9)` bidder `1` pays `0.7`. The plain Vickrey rule
is not a virtual-welfare maximizer, and Myerson's theorem compares Vickrey with and without the
reserve, so its hypotheses are satisfiable. The rising density `f(v) = 2v` on `[0, 1]` fails
`IsRegular` for every choice of `f(0)`, which illustrates the endpoint convention.

To prove that a concrete rule is implementable, prove `IsMonotone` by `intro i b hb z hz z' hz'
hzz'` followed by `change` to the explicit curve inequality. Then apply `myerson_isDSIC`, or, for
0-1 rules, give a threshold and use `isMonotone_of_threshold`. If monotonicity fails at some
nonnegative profile, the rule is not implementable at all (`isImplementable_iff_isMonotone`), as
in the `lowBidRule` example. A failure caused only by negative bids is irrelevant: change the
rule there, since `Mechanism.IsDSIC.congr` shows that DSIC ignores profiles with a negative
entry.

## Known Limitations

Only dominant-strategy, deterministic, sealed-bid mechanisms are covered. Not yet formalized:
the sponsored-search payment formula (Lecture 3, (8)–(9)), the greedy knapsack rule and its
1/2-approximation (Lecture 4, §2.2, Theorem 2.1), ironing for irregular distributions, regular
distributions whose virtual valuation is unbounded below at `0` (such as `f(v) = 2v`),
optimality among Bayesian incentive-compatible mechanisms (Lecture 5, §3.2), revenue equivalence
and first-price equilibria, a measurable argmax for virtual-welfare maximization, the
Green–Laffont/Holmström characterization of DSIC welfare maximizers, a bridge exhibiting
single-parameter mechanisms as general ones (for example VCG specializing to Vickrey), and any
computational cost of allocation rules. See `ROADMAP.md` and issues #2947 and #3001.

For social choice, only Arrow's theorem for strict individual rankings is formalized. A finite
electorate is necessary, but the infinite-electorate counterexample built from a nonprincipal
ultrafilter (Fishburn 1970) is not formalized. Also not formalized are the corollary for
individual weak orders, the Gibbard–Satterthwaite theorem, May's theorem, quantitative (Kalai)
versions of Arrow's theorem and the complexity of winner determination and manipulation. See
`ROADMAP.md` and issue #3282.
