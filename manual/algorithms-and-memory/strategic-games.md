# Strategic games, congestion and the price of anarchy

[Chapter index](index.md) · [Online and streaming models](online-and-streaming.md)

This page covers finite strategic games in cost-minimization form, potential games, atomic and
nonatomic congestion games, price-of-anarchy bounds, no-regret (Hedge) dynamics, and bimatrix games
with the Lemke–Howson parity argument. All of it is mathematics about real-valued costs or
payoffs. No machine model is involved, and equilibrium computation
carries no resource claim [complexitylib][complexitylib].

## The strategic-game layer

[Complexity/GameTheory/Strategic/Basic.lean](../../Complexity/GameTheory/Strategic/Basic.lean)
defines `CostGame ι S`. Player `i` chooses from `S i`, and `cost i s : ℝ` is that player's cost at
the profile `s : ∀ i, S i`. Players minimize cost. To use a payoff-maximization game, negate the
utilities. A unilateral deviation is `Function.update s i a`, which needs `[DecidableEq ι]`. The
module provides:

- `IsPureNash s`: no deviation strictly lowers the deviator's cost.
- `Improves t s`: `t` is one strictly improving deviation away from `s`.
- `socialCost s`: the sum of all players' costs.

`isPureNash_iff_forall_not_improves` relates the first two. The layer is intended as the base
for the planned mechanism-design work.

[Potential.lean](../../Complexity/GameTheory/Strategic/Potential.lean) defines exact, ordinal and
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

[Smooth.lean](../../Complexity/GameTheory/Strategic/Smooth.lean) defines Roughgarden's
`(λ, μ)`-smoothness `IsSmooth lam μ` [roughgarden15][roughgarden15]. The parameter is spelled
`lam` because `λ` is a Lean keyword. Coarse correlated equilibria are finitely supported
distributions `σ : Convexity.StdSimplex ℝ (∀ i, S i)`, and expectations are
`σ.weights.sum (fun s w => w * …)`. This is the same representation as the
[minimax module](../../Complexity/Probability/Minimax.lean).

Assume `μ < 1`. `IsSmooth.socialCost_le_of_isPureNash` bounds the social cost of a pure Nash
equilibrium by `λ / (1 - μ)` times that of any profile. `IsSmooth.expected_socialCost_le` gives
the same bound for coarse correlated equilibria. `IsSmooth.expected_socialCost_le_of_forall_le`
allows an additive slack `ε i` in player `i`'s equilibrium inequality and yields
`(λ * socialCost s' + ∑ i, ε i) / (1 - μ)`. That is the static form of the no-regret bound, where
the slack is each player's average regret.

## Mixed strategies and no-regret dynamics

[Mixed.lean](../../Complexity/GameTheory/Strategic/Mixed.lean) represents mixed strategies as
vectors `p : ∀ i, S i → ℝ`. The product distribution `productDist` has weight
`productWeight p s = ∏ i, p i (s i)` on the profile `s`. The expected cost vector
`deviationCost G p i a` is player `i`'s expected cost for playing `a` while the others follow `p`
[roughgarden13cs364a][roughgarden13cs364a]. `sum_mul_deviationCost` shows that averaging this
vector against `p i` gives player `i`'s expected cost under `productDist`. So a learner facing
these vectors has the regret of the player in the game.

[NoRegret.lean](../../Complexity/GameTheory/Strategic/NoRegret.lean) handles arbitrary sequences
`σ : ℕ → StdSimplex ℝ (∀ i, S i)` of outcome distributions; regret is stated as a hypothesis on
expected costs. `timeAverage σ T hT` is `(1/T) ∑ t < T, σ t`. The main results:

- `CostGame.timeAverage_le_add` (Lecture 17, Proposition 3.1): regret at most `R i` makes the time
  average a coarse correlated equilibrium up to slack `R i / T`.
- `IsSmooth.sum_expected_socialCost_le` (Lecture 17, Corollary 3.3): in a smooth game with
  `μ < 1`, the total expected social cost of `T` rounds is at most
  `(T λ socialCost s' + ∑ i, R i) / (1 - μ)`.
- `IsSmooth.timeAverage_expected_socialCost_le`: the same bound for the time average.

[Hedge.lean](../../Complexity/GameTheory/Strategic/Hedge.lean) defines the dynamics in which every
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

[Congestion/Hedge.lean](../../Complexity/GameTheory/Congestion/Hedge.lean) specializes the bound to
affine congestion games: `5/2 socialCost s' + 3 M ∑ i, √(ln |S i| / T)`.

## Atomic congestion games

[Congestion/Basic.lean](../../Complexity/GameTheory/Congestion/Basic.lean) defines
`CongestionGame ι S E`. Strategy `a` of player `i` uses the finite resource set `resources i a`,
and `latency e k : ℝ` is the per-user cost of resource `e` at load `k`. Latencies are arbitrary
functions: neither monotonicity nor nonnegativity is assumed. `toCostGame` gives the strategic
game, and `load s e` counts the users of `e`. The main results:

- `isExactPotential_rosenthalPotential`: Rosenthal's potential is exact [rosenthal73][rosenthal73].
  Hence `exists_isPureNash` and `hasFIP` hold, assuming finite resources, finite strategy sets and
  nonempty strategy sets.
- `socialCost_toCostGame`: the social cost equals `∑ e, load * latency`.
- `load_update_le`: a deviation raises a load by at most one.

[Congestion/Affine.lean](../../Complexity/GameTheory/Congestion/Affine.lean) treats affine
latencies, `HasAffineLatencies`: `latency e k = a e * k + b e` with `a e, b e ≥ 0`.
`isSmooth_of_hasAffineLatencies` proves `(5/3, 1/3)`-smoothness. The proof rests on the
Christodoulou–Koutsoupias inequality `mul_add_one_le_five_thirds_sq_add_one_third_sq`. Two price
of anarchy bounds of `5/2` follow:

- `socialCost_le_of_isPureNash` for pure Nash equilibria;
- `expected_socialCost_le` for coarse correlated equilibria.

`exists_socialCost_eq_five_halves_mul` shows that `5/2` is attained, by a three-player game on six
resources.

## Nonatomic selfish routing

[Congestion/Nonatomic.lean](../../Complexity/GameTheory/Congestion/Nonatomic.lean) models
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

[Congestion/PigouBound.lean](../../Complexity/GameTheory/Congestion/PigouBound.lean) proves
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
  inequality `x (c(r) - c(x)) ≤ β r c(r)`.
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

[Bimatrix/Basic.lean](../../Complexity/GameTheory/Bimatrix/Basic.lean) defines
`BimatrixGame M N`, a two-player game with payoff matrices `A B : Matrix M N ℝ`. Unlike
`CostGame`, players maximize payoffs, following von Stengel [vonstengel07][vonstengel07]. Mixed
strategies are plain vectors with `IsMixedStrategy x` (nonnegative, summing to `1`), as in
`Strategic/Mixed.lean`; `isMixedStrategy_iff_mem_range_weights` identifies them with the weights of
`Convexity.StdSimplex`. The module defines best responses, `IsNash` and `IsNondegenerate`, the
source's Definition 3.2: no mixed strategy with support of size `k` has more than `k` pure best
responses. It proves the best response condition (`isBestResponse₁_iff`, Proposition 3.1) and the
equal support sizes of equilibria of nondegenerate games (`IsNash.ncard_support_eq`,
Proposition 3.3). Adding a constant to all payoffs (`addConst`) changes neither the equilibria nor
nondegeneracy.

The combinatorial core lives in two layers:

- [Foundations/LinearAlgebra/Matrix/Vertex.lean](../../Complexity/Foundations/LinearAlgebra/Matrix/Vertex.lean)
  is game-free polyhedral API for a system `A *ᵥ x ≤ b` over a linearly ordered field. It has tight
  rows (`tightRows`), vertices as basic feasible solutions (`IsVertex`), nondegenerate systems
  (at most `card ι` tight rows at a feasible point) and adjacency. For a nondegenerate system with
  recession cone `{0}`, a feasible point with `card ι` tight rows is a vertex
  (`isVertex_of_card_tightRows`). Dropping any tight row `l` of a vertex leads to a unique other
  vertex keeping the remaining rows tight (`IsVertex.exists_pivot`, `IsVertex.eq_of_erase_subset`,
  packaged as `pivotVertex`). The adjacent vertices are exactly these pivots
  (`vertexAdj_iff_exists_pivotVertex`).
- [Bimatrix/LemkeHowson.lean](../../Complexity/GameTheory/Bimatrix/LemkeHowson.lean) takes two such
  systems whose rows share a label set `κ` with `card κ = card ι₁ + card ι₂`. For a missing label
  `k`, `LemkeHowson.graph` is a `SimpleGraph` on the `k`-almost completely labelled vertex pairs
  (`LemkeHowson.Node`). Completely labelled nodes have degree `1` and all others degree `2`
  (`ncard_neighborSet_of_completelyLabeled`, `ncard_neighborSet_of_not_completelyLabeled`). By the
  handshake lemma, the number of completely labelled vertex pairs is even
  (`even_ncard_completelyLabeled`).

[Bimatrix/BestResponsePolytope.lean](../../Complexity/GameTheory/Bimatrix/BestResponsePolytope.lean)
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
`hG : G.IsNondegenerate`. Existence here is the special case of Nash's theorem for nondegenerate
bimatrix games only. The name `BimatrixGame.exists_isNash` is kept free for the general theorem.
The algorithm is due to Lemke and Howson [lemkehowson64][lemkehowson64].

Only the undirected parity argument is formalized. The Lemke–Howson path is not run as an
algorithm, and nothing is said about its length. There is no orientation of the paths and no bit
sizes of the rational vertices. Games are not encoded as a TFNP search problem, so this does not
show that two-player Nash is in PPAD.

## Working with the API

A small instance is a structure literal. Pure Nash conditions over finite strategy sets can often
be closed by reducing loads to natural numbers and using `decide`. The cost comparisons are real,
so do the counting in `ℕ` and transfer it with `Nat.cast_le` or `exact_mod_cast`.
[ComplexityTests/GameTheory/Congestion.lean](../../ComplexityTests/GameTheory/Congestion.lean)
shows the pattern on a two-player, two-link game with price of anarchy `4/3`. It also checks that
quadratic latencies are not affine, that `5/2` and `4/3` cannot be lowered, and Wardrop and
non-Wardrop flows. [ComplexityTests/GameTheory/PigouBound.lean](../../ComplexityTests/GameTheory/PigouBound.lean)
checks Pigou's ratio `4/3`, the Pigou bounds `1` and `4/3` for degrees `0` and `1`, and a
quadratic network whose equilibrium costs `8/5` times a feasible flow, more than the affine bound.
It also checks that polynomials of unbounded degree have an infinite Pigou bound. It applies the
tightness theorem and both directions of `pigouBound_le_ofReal_iff`: `4/3` bounds every game with
affine latencies and `13/10` does not. [ComplexityTests/GameTheory/Strategic.lean](../../ComplexityTests/GameTheory/Strategic.lean)
checks the following:

- the Monderer–Shapley Prisoner's Dilemma with its exact potential;
- matching pennies, which has no pure equilibrium, no FIP and no generalized ordinal potential;
- point-mass coarse correlated equilibria;
- uniform mixing in matching pennies, which is a coarse correlated equilibrium;
- Proposition 3.1 on a constant equilibrium sequence.

The congestion tests also check that Hedge dynamics start uniform, and they apply the Hedge
price-of-anarchy bound to the two-link game for every horizon.

[ComplexityTests/GameTheory/Bimatrix.lean](../../ComplexityTests/GameTheory/Bimatrix.lean) checks
the three equilibria of von Stengel's `3 × 2` example (3.3). It shows that the identity
coordination game is nondegenerate, so `IsNondegenerate.odd_ncard_isNash` applies. The zero game
is degenerate, and its infinitely many equilibria show that the hypothesis cannot be dropped. The
file also checks a vertex and a non-vertex of an interval and a degenerate system. Finally, the
artificial pair `(0, 0)` has degree `1` in the Lemke–Howson graph of the shifted coordination
game.

## Known Limitations

Mixed Nash equilibria are formalized only for bimatrix games. Their existence is proved only for
nondegenerate bimatrix games, through the parity argument above; Nash's theorem for general finite
games is not formalized. Correlated equilibria (with swap regret), existence of Wardrop flows, and
weighted congestion games are not formalized. For the Pigou bound, the tight lower bounds of
[roughgarden03][roughgarden03] for classes without the constant functions (diverse classes on
parallel links, Theorem 4.5, and inhomogeneous classes on unions of paths, Theorem 4.9) and the
M/M/1 and M/G/1 delay functions of its Section 5 are not formalized. The same holds for the
Monderer–Shapley isomorphism between potential games and congestion games (Theorems 2.8 and 3.2)
and for the complexity of finding equilibria (PLS- and PPAD-completeness). These are ROADMAP
directions under [#2900](https://github.com/cslib-community/complexitylib/issues/2900). Two-player
Nash in PPAD, degenerate bimatrix games and the Lemke–Howson algorithm are tracked in
[#3391](https://github.com/cslib-community/complexitylib/issues/3391).
Hedge dynamics are full-information and deterministic: they work with expected costs, not sampled
play or bandit feedback, and only time-average guarantees are proved, not last-iterate convergence.
The theorems of Rosenthal, Christodoulou–Koutsoupias and Awerbuch–Azar–Epstein are attributed as
cited in the Monderer–Shapley and Roughgarden papers; their own texts were not consulted.

[complexitylib]: ../sources.md#complexitylib
[lemkehowson64]: ../sources.md#lemkehowson64
[mondererShapley96]: ../sources.md#monderershapley96
[rosenthal73]: ../sources.md#rosenthal73
[roughgarden03]: ../sources.md#roughgarden03
[roughgarden13cs364a]: ../sources.md#roughgarden13cs364a
[roughgarden15]: ../sources.md#roughgarden15
[roughgardenTardos02]: ../sources.md#roughgardentardos02
[vonstengel07]: ../sources.md#vonstengel07
