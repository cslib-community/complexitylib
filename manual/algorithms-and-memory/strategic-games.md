# Strategic games, congestion and the price of anarchy

[Chapter index](index.md) · [Online and streaming models](online-and-streaming.md)

This page covers finite strategic games in cost-minimization form, potential games, atomic and
nonatomic congestion games, and price-of-anarchy bounds. All of it is mathematics about
real-valued costs. No machine model is involved, and equilibrium computation carries no resource
claim [complexitylib][complexitylib].

## The strategic-game layer

[Complexity/GameTheory/Strategic/Basic.lean](../../Complexity/GameTheory/Strategic/Basic.lean)
defines `CostGame ι S`. Player `i` chooses from `S i`, and `cost i s : ℝ` is that player's cost at
the profile `s : ∀ i, S i`. Players minimize cost. To use a payoff-maximization game, negate the
utilities. A unilateral deviation is `Function.update s i a`, which needs `[DecidableEq ι]`. The
module provides:

- `IsPureNash s`: no deviation strictly lowers the deviator's cost.
- `Improves t s`: `t` is one strictly improving deviation away from `s`.
- `socialCost s`: the sum of all players' costs.

`isPureNash_iff_forall_not_improves` relates the first two. The mechanism-design modules build
on this layer.

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
`σ.weights.sum (fun s w => w * …)`. This is the same representation as the minimax module.

Assume `μ < 1`. `IsSmooth.socialCost_le_of_isPureNash` bounds the social cost of a pure Nash
equilibrium by `λ / (1 - μ)` times that of any profile. `IsSmooth.expected_socialCost_le` gives
the same bound for coarse correlated equilibria. `IsSmooth.expected_socialCost_le_of_forall_le`
allows an additive slack `ε i` in player `i`'s equilibrium inequality and yields
`(λ * socialCost s' + ∑ i, ε i) / (1 - μ)`. That is the static form of the no-regret bound, where
the slack is each player's average regret. No learning dynamics are formalized.

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
  Definition 2.1 only for continuous nondecreasing latencies.

The main results:

- `IsWardrop.cost_le_sum_mul_pathLatency`: the variational inequality.
- `IsWardrop.cost_le`: with nonnegative affine latencies, a Wardrop flow costs at most `4/3` times
  any feasible flow (Theorem 4.5). Existence of Wardrop flows is not proved; the theorem is about
  any given one.
- `exists_cost_eq_four_thirds_mul`: Pigou's example attains `4/3`.

## Working with the API

A small instance is a structure literal. Pure Nash conditions over finite strategy sets can often
be closed by reducing loads to natural numbers and using `decide`. The cost comparisons are real,
so do the counting in `ℕ` and transfer it with `Nat.cast_le` or `exact_mod_cast`.
[ComplexityTests/GameTheory/Congestion.lean](../../ComplexityTests/GameTheory/Congestion.lean)
shows the pattern on a two-player, two-link game with price of anarchy `4/3`. It also checks that
quadratic latencies are not affine, that `5/2` and `4/3` cannot be lowered, and Wardrop and
non-Wardrop flows. [ComplexityTests/GameTheory/Strategic.lean](../../ComplexityTests/GameTheory/Strategic.lean)
checks the following:

- the Monderer–Shapley Prisoner's Dilemma with its exact potential;
- matching pennies, which has no pure equilibrium, no FIP and no generalized ordinal potential;
- point-mass coarse correlated equilibria.

## Known Limitations

Mixed and correlated equilibria, existence of Wardrop flows, and weighted congestion games are not
formalized. The same holds for the Monderer–Shapley isomorphism between potential games and
congestion games (Theorems 2.8 and 3.2) and for the complexity of finding equilibria (PLS- and
PPAD-completeness). These are ROADMAP directions under [#2900](https://github.com/cslib-community/complexitylib/issues/2900).
The theorems of Rosenthal, Christodoulou–Koutsoupias and Awerbuch–Azar–Epstein are attributed as
cited in the Monderer–Shapley and Roughgarden papers; their own texts were not consulted.

[complexitylib]: ../sources.md#complexitylib
[mondererShapley96]: ../sources.md#monderershapley96
[rosenthal73]: ../sources.md#rosenthal73
[roughgarden15]: ../sources.md#roughgarden15
[roughgardenTardos02]: ../sources.md#roughgardentardos02
