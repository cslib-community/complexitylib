# Strategic games, congestion and the price of anarchy

[Chapter index](index.md) · [Online and streaming models](online-and-streaming.md)

This page covers finite strategic games in cost-minimization form, potential games, mixed Nash
equilibria and Nash's theorem, correlated equilibria, atomic and nonatomic congestion games, price-of-anarchy and
price-of-stability bounds, fair cost-sharing games, strong Nash equilibria, no-regret (Hedge)
dynamics, and bimatrix games with the Lemke–Howson parity argument. Most of it is mathematics about real-valued costs or payoffs with no machine model. The
exception is the membership of pure Nash equilibria of explicit congestion games in `PLS`, which
uses the native polynomial-time interface [cslib-frontier][complexitylib].

## The strategic-game layer

[CslibFrontier/GameTheory/Strategic/Basic.lean](../../CslibFrontier/GameTheory/Strategic/Basic.lean)
defines `CostGame ι S`. Player `i` chooses from `S i`, and `cost i s : ℝ` is that player's cost at
the profile `s : ∀ i, S i`. Players minimize cost. To use a payoff-maximization game, negate the
utilities. A unilateral deviation is `Function.update s i a`, which needs `[DecidableEq ι]`. The
module provides:

- `IsPureNash s`: no deviation strictly lowers the deviator's cost.
- `Improves t s`: `t` is one strictly improving deviation away from `s`.
- `socialCost s`: the sum of all players' costs.

`isPureNash_iff_forall_not_improves` relates the first two. The layer is intended as the base
for the planned mechanism-design work.

[Potential.lean](../../CslibFrontier/GameTheory/Strategic/Potential.lean) defines exact, ordinal and
generalized ordinal potentials. These are the notions of Monderer and Shapley
[mondererShapley96][mondererShapley96], with costs in place of payoffs, so every inequality is
reversed. The finite improvement property `HasFIP` says there is no infinite improvement path, and
`hasFIP_iff_wellFounded` turns it into well-foundedness of `Improves`. The main results:

- **Existence of equilibria.** With finitely many profiles, a generalized ordinal potential gives
  the FIP (`IsGeneralizedOrdinalPotential.hasFIP`). The FIP then gives a pure Nash equilibrium
  (`HasFIP.exists_isPureNash`).
- **Convergence of dynamics.** Under the FIP, better-response dynamics from any profile reach a
  pure Nash equilibrium (`HasFIP.exists_reflTransGen_isPureNash`).
- **Characterization.** With finitely many profiles, the FIP holds exactly when some generalized
  ordinal potential exists (`hasFIP_iff_exists_isGeneralizedOrdinalPotential`, Lemma 2.5). The
  proof uses the reachable-profile count of the source's footnote 12.
- **Uniqueness.** With finitely many players, two exact potentials differ by a constant
  (`IsExactPotential.sub_eq_sub`, Lemma 2.7).

The finiteness hypotheses are stated as `Finite (∀ i, S i)` or `Finite ι`.

## Smoothness and coarse correlated equilibria

[Smooth.lean](../../CslibFrontier/GameTheory/Strategic/Smooth.lean) defines Roughgarden's
`(λ, μ)`-smoothness `IsSmooth lam μ` [roughgarden15][roughgarden15]. The parameter is spelled
`lam` because `λ` is a Lean keyword. Coarse correlated equilibria are finitely supported
distributions `σ : Convexity.StdSimplex ℝ (∀ i, S i)`, and expectations are
`σ.weights.sum (fun s w => w * …)`. This is the same representation as the
[minimax module](../../CslibFrontier/Probability/Minimax.lean).

Assume `μ < 1`. `IsSmooth.socialCost_le_of_isPureNash` bounds the social cost of a pure Nash
equilibrium by `λ / (1 - μ)` times that of any profile. `IsSmooth.expected_socialCost_le` gives
the same bound for coarse correlated equilibria. `IsSmooth.expected_socialCost_le_of_forall_le`
allows an additive slack `ε i` in player `i`'s equilibrium inequality and yields
`(λ * socialCost s' + ∑ i, ε i) / (1 - μ)`. That is the static form of the no-regret bound, where
the slack is each player's average regret.

## Mixed strategies and no-regret dynamics

[Mixed.lean](../../CslibFrontier/GameTheory/Strategic/Mixed.lean) represents mixed strategies as
vectors `p : ∀ i, S i → ℝ`. The product distribution `productDist` has weight
`productWeight p s = ∏ i, p i (s i)` on the profile `s`. The expected cost vector
`deviationCost G p i a` is player `i`'s expected cost for playing `a` while the others follow `p`
[roughgarden13cs364a][roughgarden13cs364a]. `sum_mul_deviationCost` shows that averaging this
vector against `p i` gives player `i`'s expected cost under `productDist`. So a learner facing
these vectors has the regret of the player in the game.

[NoRegret.lean](../../CslibFrontier/GameTheory/Strategic/NoRegret.lean) handles arbitrary sequences
`σ : ℕ → StdSimplex ℝ (∀ i, S i)` of outcome distributions; regret is stated as a hypothesis on
expected costs. `timeAverage σ T hT` is `(1/T) ∑ t < T, σ t`. The main results:

- `CostGame.timeAverage_le_add` (Lecture 17, Proposition 3.1): regret at most `R i` makes the time
  average a coarse correlated equilibrium up to slack `R i / T`.
- `IsSmooth.sum_expected_socialCost_le` (Lecture 17, Corollary 3.3): in a smooth game with
  `μ < 1`, the total expected social cost of `T` rounds is at most
  `(T λ socialCost s' + ∑ i, R i) / (1 - μ)`.
- `IsSmooth.timeAverage_expected_socialCost_le`: the same bound for the time average.

[Hedge.lean](../../CslibFrontier/GameTheory/Strategic/Hedge.lean) defines the dynamics in which every
player runs a multiplicative update on its expected cost vectors (`mwuWeight`, `mwuProb`). The
players' losses are coupled, but `prob_mwuLoss` identifies each player's mixed strategies with the
single-learner `Experts.prob` against the loss sequence it faces. So the
[online-learning bounds](../circuits-logic-and-other-models/learning-and-testing.md) apply without
change. `hedgeProb G M T` runs Hedge on costs divided by a bound `M`, with the tuned rate
`√(ln |S i| / T)`, and `hedgeDist` is its outcome distribution. The main results, assuming costs
bounded by `M > 0` and `T ≥ ln |S i|`:

- `hedge_regret_le`: each player's regret is at most `2 M √(T ln |S i|)`.
- `IsSmooth.timeAverage_hedgeDist_socialCost_le`: the time-averaged expected social cost is at
  most `(λ socialCost s' + 2 M ∑ i, √(ln |S i| / T)) / (1 - μ)`.
- `timeAverage_hedgeDist_le_add`: the time average is an approximate coarse correlated equilibrium.

[Congestion/Hedge.lean](../../CslibFrontier/GameTheory/Congestion/Hedge.lean) specializes the bound to
affine congestion games: `5/2 socialCost s' + 3 M ∑ i, √(ln |S i| / T)`.

## Mixed Nash equilibria and Nash's theorem

[Nash.lean](../../CslibFrontier/GameTheory/Strategic/Nash.lean) defines `expectedCost G p i`, player
`i`'s expected cost under the product distribution of the mixed strategies `p`, and
`IsMixedNash p`: every `p i` is a probability vector (`IsMixedStrategy`, from
[MixedStrategy.lean](../../CslibFrontier/GameTheory/MixedStrategy.lean)), and
`expectedCost G p i ≤ deviationCost G p i a` for every player `i` and pure strategy `a`. This is
Definition 3.2 of [roughgarden13cs364a][roughgarden13cs364a], Lecture 13. The headline is
`CostGame.exists_isMixedNash`, **Nash's theorem** [nash51][nash51]: a game with finitely many
players, each with a finite nonempty strategy set, has a mixed Nash equilibrium. Write
`G.exists_isMixedNash`; the instances needed are `[Fintype ι] [DecidableEq ι]`,
`[∀ i, Fintype (S i)]` and `[∀ i, Nonempty (S i)]`.

The proof follows Nash. `nashMap` moves each mixed strategy towards the pure strategies that would
lower the player's cost, in proportion to the gain `max 0 (expectedCost - deviationCost)`, and
renormalizes. Its fixed points are exactly the mixed Nash equilibria (`isFixedPt_nashMap_iff`), and
Brouwer's theorem for products of simplices (`Cslib.Brouwer.exists_isFixedPt_pi_simplex`, see
[search problems](../machines-and-classes/search-and-promises.md)) gives a fixed point. Related
results:

- `isMixedNash_single_iff`: pure Nash equilibria are exactly the mixed Nash equilibria made of
  point masses `Pi.single (s i) 1`; `IsPureNash.isMixedNash` is one direction.
- `IsMixedNash.deviationCost_eq_of_pos`: a pure strategy in the support of an equilibrium strategy
  attains the expected cost.
- `IsMixedNash.expectedCost_le_update`: deviations to mixed strategies gain nothing either. It rests
  on `deviationCost_update_self` in `Mixed.lean`: the expected cost vector of player `i` depends on
  `p i` only through its total mass.
- `IsMixedNash.isCoarseCorrelatedEquilibrium`: the product distribution of a mixed Nash equilibrium
  is a coarse correlated equilibrium.

[Bimatrix/Existence.lean](../../CslibFrontier/GameTheory/Bimatrix/Existence.lean) derives
`BimatrixGame.exists_isNash` for every bimatrix game with nonempty strategy sets, with no
nondegeneracy hypothesis. It views the game as a two-player cost game indexed by `Bool` with the
negated payoffs, lifting both strategy sets to a common universe. Each player's expected cost
vector is the negated matrix–vector product of expected payoffs, by `sum_productWeight_mul_apply`
in `Mixed.lean`: under the product weights, a function of one player's strategy has its expectation
under that player's mixed strategy.

To check a candidate equilibrium, compute `deviationCost` for each pure strategy and compare it
with `expectedCost`, which `sum_mul_deviationCost_eq_expectedCost` writes as their average.
`deviationCost_def` and `productWeight_def` unfold the sums. The checked example
[Strategic.lean](../../CslibFrontierTests/GameTheory/Strategic.lean) does this for uniform mixing
in matching pennies. The existence proof is nonconstructive: nothing here computes an
equilibrium or bounds the complexity of finding one.

## Correlated equilibria

[Correlated.lean](../../CslibFrontier/GameTheory/Strategic/Correlated.lean) defines
`IsCorrelatedEquilibrium σ` for a finitely supported distribution `σ` on profiles, by switching
functions as in [roughgarden13cs364a][roughgarden13cs364a], Lecture 18, §1. For every player `i`
and every `δ : S i → S i`, the expected cost of `i` under `σ` is at most its expected cost after
replacing its recommendation `s i` by `δ (s i)`. `isCorrelatedEquilibrium_iff` gives the
conditional form, Definition 3.3 of Lecture 13: for every recommendation `a` and deviation `b`,
compare the expected costs on the event `s i = a`. Both sides are multiplied by the probability
of the event, so the condition makes sense when that probability is zero. The iff needs
`[∀ i, DecidableEq (S i)]` but no finiteness.

The equilibrium concepts are nested as in Figure 2 of Lecture 13, and each inclusion has a lemma:

- `IsPureNash.isCorrelatedEquilibrium`: a pure Nash equilibrium as a point mass;
- `IsMixedNash.isCorrelatedEquilibrium`: the product distribution `productDist` of a mixed Nash
  equilibrium. Conditioned on its own recommendation, a player still faces the others' mixed
  strategies;
- `IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium`: constant switching functions are fixed
  deviations.

`exists_isCorrelatedEquilibrium` follows from Nash's theorem; it takes `[Finite ι]`,
`[∀ i, Finite (S i)]` and `[∀ i, Nonempty (S i)]`. The checked examples in the test file
[GameTheory/Correlated.lean](../../CslibFrontierTests/GameTheory/Correlated.lean) show that the
inclusions are strict. The traffic light of Lecture 13, §3.4, mixes the pure equilibria (stop, go) and (go, stop)
evenly: it is a correlated equilibrium but not the product distribution of any mixed strategies.
In Rock–Paper–Scissors, the uniform distribution on the six outcomes without a tie is a coarse
correlated equilibrium but not a correlated equilibrium. Since `a + 1` beats `a` there, a player
recommended `a` gains by switching to `a + 2`.

[SwapRegretDynamics.lean](../../CslibFrontier/GameTheory/Strategic/SwapRegretDynamics.lean) defines
`IsApproxCorrelatedEquilibrium ε σ`, where the expected cost bound for player `i` is relaxed by
`ε i`. If after `T > 0` rounds every player `i` has total expected swap regret at most `R i`, then
the time average of the product distributions is an `(R i / T)`-approximate correlated equilibrium
(`timeAverage_productDist_isApproxCorrelatedEquilibrium`, Lecture 18, Proposition 1.3 of
[roughgarden13cs364a][roughgarden13cs364a]; Theorem 3 of [blummansour07][blummansour07]).

`blumMansourDynamics G T` constructs the coupled multi-player Blum–Mansour trajectory with Hedge
copies tuned for a fixed finite horizon `T`, and `blumMansourDynamics_eq_blumMansourProb`
identifies each player's trajectory with the single-learner Blum–Mansour algorithm against its
realized `deviationCost` sequence. Under `[Fintype ι] [DecidableEq ι]`, `[∀ i, Fintype (S i)]`,
`[∀ i, DecidableEq (S i)]`, `[∀ i, Nonempty (S i)]`, costs in `[-1, 1]` (`∀ i s, |G.cost i s| ≤ 1`),
`m_i = |S i| ≥ 2`, and `T > 0` satisfying `m_i ln m_i ≤ T`,
`blumMansour_isApproxCorrelatedEquilibrium` proves that the time average of the first `T` rounds
is an approximate correlated equilibrium with exact slack `2 √(m_i ln m_i / T)` ([blummansour07][blummansour07],
Corollary 7). This is a fixed-horizon (`T`-indexed), full-information expected-cost analysis: it
does not establish anytime convergence independent of `T`, sampled play, last-iterate convergence,
or a running-time theorem.

The checked theorem `CslibFrontierTests.GameTheory.SwapRegretDynamics.blumMansour_pennies` in
[GameTheory/SwapRegretDynamics.lean](../../CslibFrontierTests/GameTheory/SwapRegretDynamics.lean)
instantiates this unconditionally on matching pennies for every `T ≥ 2`:

```bash
lake build CslibFrontierTests.GameTheory.SwapRegretDynamics
```

## Atomic congestion games

[Congestion/Basic.lean](../../CslibFrontier/GameTheory/Congestion/Basic.lean) defines
`CongestionGame ι S E`. Strategy `a` of player `i` uses the finite resource set `resources i a`,
and `latency e k : ℝ` is the per-user cost of resource `e` at load `k`. Latencies are arbitrary
functions: neither monotonicity nor nonnegativity is assumed. `toCostGame` gives the strategic
game, and `load s e` counts the users of `e`. The main results:

- `isExactPotential_rosenthalPotential`: Rosenthal's potential is exact [rosenthal73][rosenthal73].
  Hence `exists_isPureNash` and `hasFIP` hold, assuming finite resources, finite strategy sets and
  nonempty strategy sets.
- `socialCost_toCostGame`: the social cost equals `∑ e, load * latency`.
- `load_update_le`: a deviation raises a load by at most one.

[Congestion/Affine.lean](../../CslibFrontier/GameTheory/Congestion/Affine.lean) treats affine
latencies, `HasAffineLatencies`: `latency e k = a e * k + b e` with `a e, b e ≥ 0`.
`isSmooth_of_hasAffineLatencies` proves `(5/3, 1/3)`-smoothness. The proof rests on the
Christodoulou–Koutsoupias inequality `mul_add_one_le_five_thirds_sq_add_one_third_sq`. Two price
of anarchy bounds of `5/2` follow:

- `socialCost_le_of_isPureNash` for pure Nash equilibria;
- `expected_socialCost_le` for coarse correlated equilibria.

`exists_socialCost_eq_five_halves_mul` shows that `5/2` is attained, by a three-player game on six
resources.

## The price of stability

The price of stability compares the *best* pure Nash equilibrium with the optimum
[roughgardenTardos07][roughgardenTardos07]. As for the price of anarchy, the library defines no
ratio. A price-of-stability bound `ρ` is the statement that some pure Nash equilibrium `s`
satisfies `socialCost s ≤ ρ * socialCost s'` for every profile `s'`.

[Strategic/Stability.lean](../../CslibFrontier/GameTheory/Strategic/Stability.lean) proves the potential
function method (Theorem 19.13 of [tardosWexler07][tardosWexler07]). Suppose a generalized ordinal
potential `Φ` satisfies `socialCost s ≤ A * Φ s` and `Φ s ≤ B * socialCost s` for every profile,
with `0 ≤ A`, and there are finitely many profiles. The source assumes an exact potential with
`A, B > 0`. The main results:

- `IsGeneralizedOrdinalPotential.exists_isPureNash_socialCost_le`: a global minimizer of `Φ` is a
  pure Nash equilibrium within `A * B` of the optimum.
- `IsGeneralizedOrdinalPotential.exists_reflTransGen_isPureNash_socialCost_le`: better-response
  dynamics from any `s₀` reach a pure Nash equilibrium of social cost at most
  `A * B * socialCost s₀`.

The method has two applications to atomic congestion games:

- **Affine latencies.** [Congestion/Stability.lean](../../CslibFrontier/GameTheory/Congestion/Stability.lean)
  proves `rosenthalPotential_le_socialCost` for nondecreasing latencies and
  `socialCost_le_two_mul_rosenthalPotential` for nonnegative affine latencies. These are the bounds
  of Exercise 55 of [roughgarden13cs364a][roughgarden13cs364a], Exercise Set #7. The method then
  gives a price of stability at most `2` (`exists_isPureNash_socialCost_le_two_mul`). This bound is
  not tight.
- **Fair cost sharing.** [Congestion/CostSharing.lean](../../CslibFrontier/GameTheory/Congestion/CostSharing.lean)
  defines `fairCostSharing resources c`, the congestion game with latency `c e / k`. It is the
  network cost-sharing game of Lecture #15, with paths abstracted to resource sets. Its social cost
  is the total cost of the resources in use (`socialCost_fairCostSharing`). Rosenthal's potential
  is `∑ e, c e * H (load s e)`, and with nonnegative costs it lies between `socialCost` and
  `H k * socialCost` (Lemma 19.8). So the price of stability is at most `H k`
  (`exists_isPureNash_fairCostSharing_socialCost_le_harmonic_mul`). This is the theorem of
  [anshelevichDKTWR08][anshelevichDKTWR08], proved as in Theorem 19.10 and Lecture #15,
  Theorem 2.1.

The opt-out game `optOut k ε` shows that `H k` is tight. Player `i` opts out on a private resource
of cost `1 / (i + 1)` or shares a resource of cost `1 + ε`. For `ε > 0`, `isPureNash_optOut_iff`
shows that everyone opting out, of social cost `H k`, is the unique pure Nash equilibrium.
`exists_forall_isPureNash_optOut_mul_lt` turns this into the statement that no factor `r < H k`
works. The source's network has extra zero-cost edges; they change no player's cost and are
omitted.

## Strong Nash equilibria

[Strategic/StrongNash.lean](../../CslibFrontier/GameTheory/Strategic/StrongNash.lean) defines
coalitional deviations in two strengths, because the literature uses "strong equilibrium" for both.

- `IsBeneficialDeviation G s A t` follows Lecture #15, Definition 3.1 of
  [roughgarden13cs364a][roughgarden13cs364a]. It says that at `A.piecewise t s`, where the
  coalition `A` plays as in `t` and the others as in `s`, no member of `A` pays more and some
  member pays less. `IsStrongNash s` says that no coalition has one.
- `IsStrictlyBeneficialDeviation G s A t` says that `A` is nonempty and every member of `A` pays
  strictly less, as in Exercise 23.6 of [babaioffChuangFeldman07][babaioffChuangFeldman07].
  `IsStrongEquilibrium s` says that no coalition has one.

Every strong Nash equilibrium is a strong equilibrium (`IsStrongNash.isStrongEquilibrium`). The
converse fails, as the tests below check. Both are pure Nash equilibria
(`IsStrongEquilibrium.isPureNash`, `IsStrongNash.isPureNash`). A strong Nash equilibrium is also
Pareto optimal, or Pareto efficient (`IsStrongNash.not_pareto`). `isStrongEquilibrium_iff` is the
form used in proofs: against any joint deviation of a nonempty coalition, some member does not
gain.

[Congestion/StrongNash.lean](../../CslibFrontier/GameTheory/Congestion/StrongNash.lean) proves the
theorem that Lecture #15, Theorem 3.2 attributes to
[epsteinFeldmanMansour09][epsteinFeldmanMansour09]: **every strong Nash equilibrium of a `k`-player
fair cost-sharing game costs at most `H k` times the optimum**
(`socialCost_fairCostSharing_le_harmonic_mul_of_isStrongNash`). Unlike the price-of-stability
bound, it covers every strong Nash equilibrium, but it does not assert that one exists.

The proof only uses that no nonempty coalition has a deviation from which every member strictly
gains, so the library proves the bound for strong equilibria
(`socialCost_fairCostSharing_le_harmonic_mul_of_isStrongEquilibrium`). The strong Nash version
follows through the bridge. The proof follows displays (5)–(8) of the lecture. It peels members
off the grand coalition, uses that the players outside a coalition only lower a member's shares,
and telescopes the coalition's Rosenthal potential. It only needs latencies that are nonincreasing
on loads `≥ 1`, so `socialCost_le_rosenthalPotential_of_isStrongEquilibrium` states it for every
such congestion game: a strong equilibrium costs at most Rosenthal's potential of every profile.

For `ε > 0`, everyone opting out is the unique strong Nash equilibrium of the opt-out game, and its
unique strong equilibrium (`isStrongNash_optOut_iff`, `isStrongEquilibrium_optOut_iff`). So `H k`
is tight for both notions (`exists_isStrongNash_optOut_mul_lt`).

When all players share the strategy set and the resource map, as in a network with a common source
and sink, the strong Nash equilibria are exactly the minimum-cost profiles
(`isStrongNash_fairCostSharing_iff`, Exercise Set #8, Exercise 67).

- Every strong Nash equilibrium is a social optimum
  (`socialCost_fairCostSharing_le_of_isStrongNash`). This uses Pareto optimality, so it is stated
  for `IsStrongNash`.
- Conversely, every minimum-cost profile is a strong Nash equilibrium
  (`isStrongNash_fairCostSharing_of_le`). Every player always pays at least `OPT / k`, and at an
  optimum nobody pays more.
- Everyone playing a cheapest strategy is a strong Nash equilibrium
  (`isStrongNash_fairCostSharing_const`), so `exists_isStrongNash_fairCostSharing_const` gives
  existence and a price of anarchy of `1` for strong Nash equilibria.

## Pure Nash equilibria of congestion games are in PLS

[Congestion/PLS.lean](../../CslibFrontier/GameTheory/Congestion/PLS.lean) formalizes the
PLS-membership claim of [roughgarden13cs364a][roughgarden13cs364a], Lecture #19, §3, for
congestion games with explicitly listed strategy sets. A `CongestionCode` lists each player's
strategies as lists of resource indices, and each resource's cost table `[c_e(1), c_e(2), …]`.
`encCongestion` writes resource indices in unary and costs as natural numbers in binary; the source
allows arbitrary costs `c_e(i)`. Missing table entries read as `0`, out-of-range resource indices
are ignored, and a player with no listed strategy gets the empty one. `toGame` reads the code as a `CongestionGame`, so `IsPureNash` is the library's notion.

A profile is a bit string of length `vertexLength = players * width`. Player `i`'s block of
`width` bits decodes to the number of ones in it, clamped to a strategy index, so every string of
that length is a profile. `step` applies the first deviation that strictly lowers Rosenthal's
potential, or stays put. The source's step plays a best response; the local optima are the same.
The main results:

- `pureNash_eq_localOptRel`: the search problem `PureNash` *equals* the `localOptRel` of
  `vertexLength`, `step` and the natural-number potential. It is not merely reducible to it.
- `pureNash_mem_PLS` and `pureNash_mem_TFNP`: finding a pure Nash equilibrium is in `PLS`, and is
  therefore a total `FNP` problem.
- `pureNash_iff`: a decidable characterization, used by the tests with `decide`.

PLS-hardness [fabrikantPapadimitriouTalwar04][fabrikantPapadimitriouTalwar04] is not formalized.

## Nonatomic selfish routing

[Congestion/Nonatomic.lean](../../CslibFrontier/GameTheory/Congestion/Nonatomic.lean) models
Roughgarden–Tardos selfish routing [roughgardenTardos02][roughgardenTardos02]. Network paths are
abstracted to finite resource sets: a path `p` of commodity `commodity p` uses `resources p`.
Flows are functions `f : P → ℝ`, and the definitions are:

- `IsFeasible f`: `f` is nonnegative and routes exactly `rate k` on the paths of commodity `k`.
- `cost f`: the total latency `∑ p, f p * pathLatency f p`.
- `IsWardrop f`: every flow-carrying path is a shortest path of its commodity. This is the
  source's Lemma 2.2 characterization, taken as the definition. It agrees with the source's
  Definition 2.1 for continuous nondecreasing latencies (Lemma 2.2), in particular for the affine
  latencies of the `4/3` theorem.

The module proves the variational inequality `IsWardrop.cost_le_sum_mul_pathLatency` and
`cost_nonneg`. Existence of Wardrop flows is not proved; every bound below is about any given one.

### The Pigou bound

[Congestion/PigouBound.lean](../../CslibFrontier/GameTheory/Congestion/PigouBound.lean) proves
Roughgarden's theorem that the price of anarchy depends only on the class of latency functions,
not on the network [roughgarden03][roughgarden03]. It follows the presentation of
[roughgarden13cs364a][roughgarden13cs364a], Lecture #11. A *Pigou-like network*,
`pigouNetwork c r`, routes `r` units over two parallel links with latencies `c` and the constant
`c r`. `pigouRatio c r x` is the ratio `r c(r) / (x c(x) + (r - x) c(r))`. The *Pigou bound*
`pigouBound C : ℝ≥0∞` is its supremum over `c ∈ C` and `r, x ≥ 0`. It lives in `ℝ≥0∞` because it
can be infinite, as it is for polynomials of unbounded degree. The main results:

- `IsWardrop.cost_le_toReal_pigouBound_mul` (Lecture #11, Theorem 3.3): suppose every resource
  latency lies in `C` and is nonnegative and nondecreasing on `[0, ∞)`, and `pigouBound C ≠ ⊤`.
  Then a Wardrop flow costs at most `(pigouBound C).toReal` times any feasible flow, with any
  number of commodities and any resource sets. Continuity is not needed.
- `IsWardrop.cost_le_mul_of_forall_mul_le`: the same proof for any `α ≥ 0` that satisfies the
  edgewise inequality `r c(r) ≤ α (x c(x) + (r - x) c(r))`. Use it for a class whose bound you
  know but have not computed as a supremum.
- `exists_lt_cost_of_lt_pigouBound` and `pigouBound_le_ofReal_iff` ([roughgarden03][roughgarden03],
  Theorem 4.2): suppose also that `C` contains every nonnegative constant function. Then
  Pigou-like networks come arbitrarily close to `pigouBound C`, so it is the exact worst-case price
  of anarchy over all games with latencies in `C`.
- `pigouBound_polynomialLatencies` (Proposition 5.1): `polynomialLatencies d` is the class of
  polynomials of degree at most `d` with nonnegative coefficients, and its bound is
  `(1 - d (d+1)^{-(d+1)/d})⁻¹`. `pigouBound_le_ofReal_inv_one_sub` reduces such computations to the
  inequality `x (c(r) - c(x)) ≤ β r c(r)`. `pow_mem_polynomialLatencies` and
  `const_mem_polynomialLatencies` place `x ^ d` and the nonnegative constants in the class, so the
  tightness theorems above apply to it.
- `IsWardrop.cost_le_of_mem_polynomialLatencies` is the resulting price-of-anarchy bound.
  `exists_cost_eq_mul_of_mem_polynomialLatencies` attains it with Pigou's `x ^ d` network.
- `IsWardrop.cost_le` and `exists_cost_eq_four_thirds_mul` are the affine case `d = 1`: a bound of
  `4/3` (Theorem 4.5 of [roughgardenTardos02][roughgardenTardos02]), attained by Pigou's example.
  `HasAffineLatencies.latency_mem_polynomialLatencies` and `pigouBound_polynomialLatencies_one`
  connect the two.

To bound a new latency class, first prove that its members are nonnegative and nondecreasing on
`[0, ∞)`. Then bound `pigouBound C` with `pigouBound_le` or `pigouBound_le_ofReal_inv_one_sub`,
and apply `IsWardrop.cost_le_toReal_pigouBound_mul`. To show the bound is tight, use
`pigouNetwork`, `pigouNetwork_cost`, `pigouNetwork_isWardrop` and `pigouNetwork_isFeasible`.
The Pigou bound uses Lean's `a / 0 = 0`. That changes nothing unless every function of `C`
vanishes on `(0, ∞)` (see `one_le_pigouBound`).

## Bimatrix games and the Lemke–Howson parity argument

[Bimatrix/Basic.lean](../../CslibFrontier/GameTheory/Bimatrix/Basic.lean) defines
`BimatrixGame M N`, a two-player game with payoff matrices `A B : Matrix M N ℝ`. Unlike
`CostGame`, players maximize payoffs, following von Stengel [vonstengel07][vonstengel07]. Mixed
strategies are plain vectors with `IsMixedStrategy x` (nonnegative, summing to `1`), defined in
[MixedStrategy.lean](../../CslibFrontier/GameTheory/MixedStrategy.lean);
`isMixedStrategy_iff_mem_range_weights` identifies them with the weights of `Convexity.StdSimplex`. The module defines best responses, `IsNash` and `IsNondegenerate`, the
source's Definition 3.2: no mixed strategy with support of size `k` has more than `k` pure best
responses. It proves the best response condition (`isBestResponse₁_iff`, Proposition 3.1) and the
equal support sizes of equilibria of nondegenerate games (`IsNash.ncard_support_eq`,
Proposition 3.3). Adding a constant to all payoffs (`addConst`) changes neither the equilibria nor
nondegeneracy.

The combinatorial core lives in two layers:

- [Foundations/LinearAlgebra/Matrix/Vertex.lean](../../CslibFrontier/Foundations/LinearAlgebra/Matrix/Vertex.lean)
  is game-free polyhedral API for a system `A *ᵥ x ≤ b` over a linearly ordered field. It has tight
  rows (`tightRows`), vertices as basic feasible solutions (`IsVertex`), nondegenerate systems
  (at most `card ι` tight rows at a feasible point) and adjacency. For a nondegenerate system with
  recession cone `{0}`, a feasible point with `card ι` tight rows is a vertex
  (`isVertex_of_card_tightRows`). Dropping any tight row `l` of a vertex leads to a unique other
  vertex keeping the remaining rows tight (`IsVertex.exists_pivot`, `IsVertex.eq_of_erase_subset`,
  packaged as `pivotVertex`). The adjacent vertices are exactly these pivots
  (`vertexAdj_iff_exists_pivotVertex`).
- [Bimatrix/LemkeHowson.lean](../../CslibFrontier/GameTheory/Bimatrix/LemkeHowson.lean) takes two such
  systems whose rows share a label set `κ` with `card κ = card ι₁ + card ι₂`. For a missing label
  `k`, `LemkeHowson.graph` is a `SimpleGraph` on the `k`-almost completely labelled vertex pairs
  (`LemkeHowson.Node`). Completely labelled nodes have degree `1` and all others degree `2`
  (`ncard_neighborSet_of_completelyLabeled`, `ncard_neighborSet_of_not_completelyLabeled`). By the
  handshake lemma, the number of completely labelled vertex pairs is even
  (`even_ncard_completelyLabeled`).

[Bimatrix/BestResponsePolytope.lean](../../CslibFrontier/GameTheory/Bimatrix/BestResponsePolytope.lean)
instantiates this with the best response polytopes `P = {x ≥ 0, Bᵀ x ≤ 1}` and
`Q = {A y ≤ 1, y ≥ 0}` of the source's (3.6), with labels `M ⊕ N` (`matP`, `rhsP`, `matQ`,
`rhsQ`). Nondegeneracy of the game makes both systems nondegenerate
(`IsNondegenerate.isNondegenerateSystem_matP`), and positive payoffs make them bounded. For
positive payoffs, `setOf_completelyLabeled_eq` shows that the completely labelled vertex pairs are
`(0, 0)` and the Nash equilibria rescaled by the inverse equilibrium payoffs (`toPolytopes`). The
source assumes (3.5) (`A` and `Bᵀ` nonnegative without zero columns); the library instead shifts
payoffs to be positive with `exists_addConst_pos`. The headline is
`IsNondegenerate.odd_ncard_isNash`: a nondegenerate bimatrix game (with `M` and `N` nonempty) has
an odd number of Nash equilibria, the source's Corollary 3.7. `IsNondegenerate.exists_isNash` and
`IsNondegenerate.finite_setOf_isNash` follow, so `hG.exists_isNash` works for
`hG : G.IsNondegenerate`. Existence for all bimatrix games is `BimatrixGame.exists_isNash`, from
Nash's theorem (see the section on mixed Nash equilibria); the parity argument adds the odd count
and finiteness for nondegenerate games.
The algorithm is due to Lemke and Howson [lemkehowson64][lemkehowson64].

Only the undirected parity argument is formalized. The Lemke–Howson path is not run as an
algorithm, and nothing is said about its length. There is no orientation of the paths and no bit
sizes of the rational vertices. Games are not encoded as a TFNP search problem, so this does not
show that two-player Nash is in PPAD.

## Working with the API

A small instance is a structure literal. Pure Nash conditions over finite strategy sets can often
be closed by reducing loads to natural numbers and using `decide`. The cost comparisons are real,
so do the counting in `ℕ` and transfer it with `Nat.cast_le` or `exact_mod_cast`.
[CslibFrontierTests/GameTheory/Congestion.lean](../../CslibFrontierTests/GameTheory/Congestion.lean)
shows the pattern on a two-player, two-link game with price of anarchy `4/3`. It also checks that
quadratic latencies are not affine, that `5/2` and `4/3` cannot be lowered, and Wardrop and
non-Wardrop flows. [CslibFrontierTests/GameTheory/PigouBound.lean](../../CslibFrontierTests/GameTheory/PigouBound.lean)
checks Pigou's ratio `4/3`, the Pigou bounds `1` and `4/3` for degrees `0` and `1`, and a
quadratic network whose equilibrium costs `8/5` times a feasible flow, more than the affine bound.
It also checks that polynomials of unbounded degree have an infinite Pigou bound. It applies the
tightness theorem and both directions of `pigouBound_le_ofReal_iff`: `4/3` bounds every game with
affine latencies and no `β < 4/3` does. [CslibFrontierTests/GameTheory/Strategic.lean](../../CslibFrontierTests/GameTheory/Strategic.lean)
checks the following:

- the Monderer–Shapley Prisoner's Dilemma with its exact potential;
- matching pennies, which has no pure equilibrium, no FIP and no generalized ordinal potential;
- point-mass coarse correlated equilibria;
- uniform mixing in matching pennies, which is a mixed Nash equilibrium and, as a product
  distribution, a coarse correlated equilibrium;
- Nash's theorem on matching pennies, whose mixed equilibria cannot be point masses, and point-mass
  mixed equilibria in the Prisoner's Dilemma;
- Proposition 3.1 on a constant equilibrium sequence.

[CslibFrontierTests/GameTheory/Correlated.lean](../../CslibFrontierTests/GameTheory/Correlated.lean)
checks the bridges to correlated equilibria on these games and the strict hierarchy: the traffic
light is a correlated equilibrium that is not a product distribution, and the no-tie distribution
of Rock–Paper–Scissors is a coarse correlated equilibrium that is not correlated.

The congestion tests also check that Hedge dynamics start uniform, and they apply the Hedge
price-of-anarchy bound to the two-link game for every horizon.
[CslibFrontierTests/GameTheory/SwapRegretDynamics.lean](../../CslibFrontierTests/GameTheory/SwapRegretDynamics.lean)
instantiates the unconditional Blum–Mansour bound on matching pennies for every `T ≥ 2` and checks
the `t = 0` learner identity at `T = 4`.
[CslibFrontierTests/GameTheory/Stability.lean](../../CslibFrontierTests/GameTheory/Stability.lean) checks
the following price-of-stability instances:

- the potential function method on a coordination game whose worst equilibrium costs twice its
  best;
- the bounds `socialCost / 2 ≤ Φ ≤ socialCost`, both strict, on the two-link game;
- a two-player VHS-or-Betamax game with two equilibria;
- the opt-out game with three players. It also checks that `isPureNash_optOut_iff` fails for
  `ε = 0`.

[CslibFrontierTests/GameTheory/StrongNash.lean](../../CslibFrontierTests/GameTheory/StrongNash.lean)
checks strong Nash equilibria on the same games:

- the bad equilibria of the coordination and VHS-or-Betamax games are not strong, and the good ones
  are. For VHS or Betamax this is checked both directly and through
  `isStrongNash_fairCostSharing_iff`;
- the `H 2` bound for VHS or Betamax, and the strong Nash equilibrium of the three-player opt-out
  game with the `H 3` bound and its tightness;
- with `ε = 0`, everyone opting out of the two-player opt-out game is a pure Nash equilibrium and a
  strong equilibrium, but not a strong Nash equilibrium. This separates the two notions;
- a game with an increasing latency whose strong Nash equilibrium costs more than Rosenthal's
  potential, so the nonincreasing-latency hypothesis cannot be dropped.

[CslibFrontierTests/GameTheory/CongestionPLS.lean](../../CslibFrontierTests/GameTheory/CongestionPLS.lean)
decides `PureNash` on a two-player code, at one equilibrium and two non-equilibria. It also checks
the `step` map, clamping, a player with no listed strategy, and out-of-range resources.

[CslibFrontierTests/GameTheory/Bimatrix.lean](../../CslibFrontierTests/GameTheory/Bimatrix.lean) checks
the three equilibria of von Stengel's `3 × 2` example (3.3). It shows that the identity
coordination game is nondegenerate, so `IsNondegenerate.odd_ncard_isNash` applies. The zero game
is degenerate, and its infinitely many equilibria show that the hypothesis cannot be dropped;
`exists_isNash` still applies to it. The file also checks a vertex and a non-vertex of an interval and a degenerate system. Finally, the
artificial pair `(0, 0)` has degree `1` in the Lemke–Howson graph of the shifted coordination
game.

## Known Limitations

Existence of Wardrop flows and weighted congestion games are not formalized. For the Pigou bound, the tight lower bounds of
[roughgarden03][roughgarden03] for classes without the constant functions (diverse classes on
parallel links, Theorem 4.5, and inhomogeneous classes on unions of paths, Theorem 4.9) and the
M/M/1 and M/G/1 delay functions of its Section 5 are not formalized. Nor are the tight price of
stability of affine congestion games (below `2`), the existence of strong Nash equilibria beyond
common strategy sets (the network classes of [epsteinFeldmanMansour09][epsteinFeldmanMansour09]),
the network of Lecture #15, Figure 4, which has none, and price-of-stability bounds for undirected
network design. The same holds for the Monderer–Shapley isomorphism between potential games and
congestion games (Theorems 2.8 and 3.2) and for hardness of finding equilibria: pure Nash equilibria
of congestion games are in `PLS`, but their PLS-completeness (Lecture #19, Theorem 3.1) and
PPAD-completeness of mixed equilibria are not formalized. Neither are exponentially long
better-response paths or the polynomial-time algorithm for symmetric network congestion games. These
are ROADMAP directions under [#2900](https://github.com/cslib-community/cslib-frontier/issues/2900).
Two-player Nash in PPAD, degenerate bimatrix games and the Lemke–Howson algorithm are tracked in
[#3391](https://github.com/cslib-community/cslib-frontier/issues/3391). Hedge and Blum–Mansour
swap-regret dynamics are full-information, deterministic, and fixed-horizon (`T`-indexed): they work
with expected costs, not anytime step sizes independent of `T`, sampled play or bandit feedback,
running-time bounds, or last-iterate convergence.
The theorems of Rosenthal, Christodoulou–Koutsoupias and Awerbuch–Azar–Epstein are attributed as
cited in the Monderer–Shapley and Roughgarden papers; their own texts were not consulted.

[anshelevichDKTWR08]: ../sources.md#anshelevichdktwr08
[babaioffChuangFeldman07]: ../sources.md#babaioffchuangfeldman07
[blummansour07]: ../sources.md#blummansour07
[complexitylib]: ../sources.md#complexitylib
[epsteinFeldmanMansour09]: ../sources.md#epsteinfeldmanmansour09
[fabrikantPapadimitriouTalwar04]: ../sources.md#fabrikantpapadimitrioutalwar04
[lemkehowson64]: ../sources.md#lemkehowson64
[mondererShapley96]: ../sources.md#monderershapley96
[nash51]: ../sources.md#nash51
[rosenthal73]: ../sources.md#rosenthal73
[roughgarden03]: ../sources.md#roughgarden03
[roughgarden13cs364a]: ../sources.md#roughgarden13cs364a
[roughgarden15]: ../sources.md#roughgarden15
[roughgardenTardos02]: ../sources.md#roughgardentardos02
[roughgardenTardos07]: ../sources.md#roughgardentardos07
[tardosWexler07]: ../sources.md#tardoswexler07
[vonstengel07]: ../sources.md#vonstengel07
