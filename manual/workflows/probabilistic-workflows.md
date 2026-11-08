# Work with randomized and oracle programs

Start with three separate questions: what program is being described, what distribution it denotes, and what machine implements it. `ProbComp α` describes finite-uniform sampling with ordinary `do` notation; `ProbComp.eval` interprets that syntax as a `PMF α`. `ProbOracleComp spec α` adds external requests whose reply types are given by `spec`. The underlying `OracleComp` is a free program over a typed request interface. A PMF supplies mathematical probability semantics; merely writing a PMF does not supply a sampler or a runtime certificate. The [programs and realization reference](../programs-crypto-and-probability/programs-and-realization.md) explains these layers and their sources. [complexitylib][complexitylib]

## Transport a distribution bound through a map

Import [TotalVariation/Map.lean](../../Complexity/Foundations/MeasureTheory/Measure/TotalVariation/Map.lean).
For finite measures `μ` and `ν` and a measurable function `f`, apply
`MeasureTheory.tvDist_map_le μ ν hf` to bound the distance of their pushforwards by
`tvDist μ ν`. The measures may have different total masses. The extended-valued theorem
`etvDist_map_le` has the same hypotheses and avoids conversion to real numbers.

This is Mathlib's full-L1 convention: distinct probability atoms have distance `2`,
and the distance of `2 • dirac x` from the zero measure is `2` as well. The finite-measure
instances matter because real `tvDist` is defined as zero if its extended value is infinite.
A previously proved bound transports with `(tvDist_map_le μ ν hf).trans h`;
no density, injectivity or probability normalization is required.

The [checked clients](../../ComplexityTests/TotalVariationMap.lean) include identity,
strict coarsening from distance `2` to `0`, unequal masses, and the canonical measurable
map from `ℝ` to `UnitAddCircle`. Run `scripts/build.sh ComplexityTests.TotalVariationMap`.
The theorem transports an existing bound; it does not identify the output laws. The Gaussian
projection and mod-one bounds of
[issue #2734](https://github.com/cslib-community/complexitylib/issues/2734) apply it to actual laws.

## Combine component and mixture-weight errors

Import [TotalVariation/Mixture.lean](../../Complexity/Foundations/MeasureTheory/Measure/TotalVariation/Mixture.lean).
For a finite index set `s`, finite measures `μ i`, `ν i`, and weights `a i`, `b i : ℝ≥0`,
`MeasureTheory.tvDist_finsetSum_smul_le s a b μ ν` bounds the distance between their actual
weighted sums by the sum of
`a i * tvDist (μ i) (ν i) + |a i - b i| * (ν i).real Set.univ`.
The weights need not sum to one, and the component measures need not be probabilities.
The actual total mass in the second term is necessary for arbitrary finite measures.

For common weights use `tvDist_nnreal_smul`; for a fixed component with changed weights use
`tvDist_nnreal_smul_same`. The latter is an equality, including zero weights and the zero
measure. `tvDist_add_le` (and `etvDist_add_le`) and `tvDist_finsetSum_le` handle binary and
finite sums directly. All statements keep the full-L1
convention: distinct probability atoms have distance two.

The [checked clients](../../ComplexityTests/TotalVariationMixture.lean) include sharp unequal-mass
examples and a tagged mixture on `Fin 6 × ℝ`. In that client, actual finite-PMF weights sum
to one; component errors bounded by `4 * ε` and a weight discrepancy bounded by `δ` give a
joint error of `4 * ε + δ`. The tags are actual measurable pushforwards, so map contraction
supplies their component bounds. Run `scripts/build.sh ComplexityTests.TotalVariationMixture`.
The [Regev joint experiment](https://github.com/cslib-community/complexitylib/issues/2767) still
has to discharge those bounds for its actual Gaussian laws and residue marginal.

## Condition and compare finite PMFs

Import [PMF/Filter.lean](../../Complexity/Probability/PMF/Filter.lean) to rewrite a conditioned
law `p.filter s h`. Mathlib's `PMF.filter` takes a support witness `h : ∃ a ∈ s, a ∈ p.support`,
so each lemma assumes such a witness for every conditioned law it mentions; an event of
probability zero cannot be conditioned on. `toOuterMeasure_filter_mul_eq_inter` states
`Pr_{p | s}[t] · Pr_p[s] = Pr_p[s ∩ t]` without dividing. `filter_filter`, `filter_map` (for a
preimage event `f ⁻¹' s`) and `filter_eq_self_of_support_subset` move conditioning past a second
condition, a relabeling and an almost sure event. For a two-stage law
`μ.bind fun a => (K a).map (a, ·)`, `filter_bind_pair` conditions the first stage on an event about
`a` and keeps the kernel. When the second draw is independent of the first,
`filter_bind_pair_prod` conditions both factors on a rectangle `s ×ˢ t`, and
`map_snd_filter_bind_pair_prod` shows that the condition on `a` does not affect the law of `b`.

Import [StatisticalDistance/Event.lean](../../Complexity/Probability/StatisticalDistance/Event.lean)
to turn a distance bound into event bounds. Here `dist` is cslib's statistical distance on PMFs
over a finite type, active after `open scoped Cslib.Probability.PMF`. It uses the half-L1
convention: distinct point masses have distance `1`, half of Mathlib's `tvDist` above.
`abs_toOuterMeasure_toReal_sub_le_dist p q E` bounds `|Pr_p[E] − Pr_q[E]|` by `dist p q`;
`abs_bind_apply_toReal_sub_le_dist p q T b` does the same for the probability that a randomized
distinguisher `T` outputs `b`. `dist_map_of_injective` keeps the distance unchanged under an
injective relabeling. For a second-moment tail bound on a finite PMF without measure-theoretic side
conditions, import [PMF/Chebyshev.lean](../../Complexity/Probability/PMF/Chebyshev.lean): by
`sum_mul_ite_le_sum_mul_sq_div`, the mass where `|f a − m| ≥ c` is at most
`∑ a, p(a) (f a − m)² / c²`. Import
[Product/Split.lean](../../Complexity/Probability/Product/Split.lean) to split an independent
product `pi p` along a predicate `P`: by `pi_map_piEquivPiSubtypeProd`, the coordinates
satisfying `P` and the remaining coordinates form two independent products.

The [checked clients](../../ComplexityTests/PMFConditioning.lean) condition two fair bits on
rectangles, split off one of two fair bits, and relabel two point masses injectively. Run
`scripts/build.sh ComplexityTests.PMFConditioning`.

## Polarize statistical distance

Sahai and Vadhan's polarization of statistical distance (Sahai–Vadhan 2003, §3) is formalized on
explicit distributions over finite types, with the half-L1 `dist` above.

- **XOR construction.** Import
  [StatisticalDistance/XOR.lean](../../Complexity/Probability/StatisticalDistance/XOR.lean).
  `xorMix p₀ p₁ k c` draws selector bits of parity `c` uniformly, then coordinate `i` from `p₀`
  or `p₁` according to bit `i`. For `k ≠ 0`, `dist_xorMix` proves
  `dist (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) = dist p₀ p₁ ^ k`.
  `dist_xorMix_le` gives the upper bound for every `k`. The identity fails at `k = 0`, where both
  sides live on a one-point type.
- **Direct-product lower bound.** Import
  [StatisticalDistance/DirectProduct.lean](../../Complexity/Probability/StatisticalDistance/DirectProduct.lean).
  `one_sub_two_mul_exp_le_dist_iid` proves `1 - 2 exp (-k δ² / 2) ≤ dist (iid μ k) (iid ν k)` from
  Hoeffding's inequality. The matching upper bound `k δ` is `dist_iid_le`.
- **Polarization.** Import
  [StatisticalDistance/Polarization.lean](../../Complexity/Probability/StatisticalDistance/Polarization.lean).
  `polarize p₀ p₁ λ ℓ k c` applies the XOR construction on `k` coordinates to `ℓ` independent
  copies of the XOR construction on `λ` coordinates. `dist_polarize_le` bounds its distance by
  `(ℓ δ^λ)^k`, and `one_sub_two_mul_mul_exp_le_dist_polarize` bounds it below by
  `1 - 2 k exp (-ℓ δ^(2λ) / 2)`. For constant thresholds `0 ≤ β < α² ≤ 1`,
  `exists_polarization` provides constants `m ≠ 0` and `b`. With these, `λ = m (⌊log₂ k⌋ + 1)` and
  `ℓ = 2 ^ (b (⌊log₂ k⌋ + 1))` are polynomially bounded in `k`. Distance `≥ α` then becomes
  `≥ 1 - 2⁻ᵏ`, and distance `≤ β` becomes `≤ 2⁻ᵏ`. Use it as
  `obtain ⟨m, b, hm, hlam, hell, h⟩ := exists_polarization hβ hβα hα hα1`, then
  `(h p₀ p₁ k).1` for the far side and `(h p₀ p₁ k).2` for the near side.

The checked clients in [Polarization.lean](../../ComplexityTests/Polarization.lean) cover the
following:

- the exact XOR distance `1/8` of a uniform bit against a point mass;
- the failure of the identity at `k = 0`;
- a direct-product bound at `32` copies;
- the thresholds `α = 2/3`, `β = 1/3`.

Run `scripts/build.sh ComplexityTests.Polarization`.

### Polarize circuit samplers and Statistical Difference instances

A circuit `C : Circuit σ n m` is a sampler. `C.outputDist I` is the distribution of its outputs on
uniform inputs, defined in
[Circuit/OutputDistribution.lean](../../Complexity/Computability/Circuit/OutputDistribution.lean).
`Circuit.outputDist_replicate` says that `C.replicate k` samples `iid (C.outputDist I) k`, with the
`k` output blocks flattened by `Cslib.BitString.blocksEquiv`.

- **XOR and polarization circuits.** Import
  [Circuit/Boolean/Polarization.lean](../../Complexity/Computability/Circuit/Boolean/Polarization.lean).
  For De Morgan circuits `C₀ C₁ : Circuit signature n m`, `xorMixCircuit C₀ C₁ j c` reads `j`
  selector bits and then `j + 1` data blocks. It samples
  `xorMix (C₀.outputDist _) (C₁.outputDist _) (j + 1) c` (`outputDist_xorMixCircuit`). The selector
  is completed to parity `c` by `BitString.parityComplete`, from
  [XORSampling.lean](../../Complexity/Probability/StatisticalDistance/XORSampling.lean).
  `polarizeCircuit C₀ C₁ lam ell k c` samples `polarize … (lam + 1) ell (k + 1) c`
  (`outputDist_polarizeCircuit`). Note that the coordinate counts are passed as predecessors.
  `dist_outputDist_polarizeCircuit` transfers the distance bounds of `polarize` unchanged.
- **Statistical Difference.** Import
  [Problems/StatisticalDifference.lean](../../Complexity/Computability/Complexity/Problems/StatisticalDifference.lean).
  An `SDInstance` is a pair of De Morgan circuits with common input and output counts, and
  `StatisticalDifference α β` is `PromiseProblem.gapMax` of `SDInstance.distance`.
  `SDInstance.exists_polarize` is the Polarization Lemma on instances, for constant thresholds
  `0 ≤ β < α² ≤ 1`. It passes `m (⌊log₂ (k + 1)⌋ + 1) - 1` as `lam`, so there are
  `m (⌊log₂ (k + 1)⌋ + 1)` inner coordinates. It passes `2 ^ (b (⌊log₂ (k + 1)⌋ + 1))` as `ell`,
  the number of copies, and `k` as the outer argument, so there are `k + 1` outer coordinates.
  `StatisticalDifference.exists_mapsTo_polarize` states the result as `Set.MapsTo` into
  `StatisticalDifference (1 - (1/2)^(k+1)) ((1/2)^(k+1))`, for `k ≠ 0`.

This is the semantic half of the reduction only. Polynomial-time computability of the
polarization map on encoded instances, with `k` growing with the instance length, is not formalized
yet. Neither is SZK. [Issue #3205](https://github.com/cslib-community/complexitylib/issues/3205)
tracks both. The checked clients in
[StatisticalDifference.lean](../../ComplexityTests/StatisticalDifference.lean) cover:

- parity completion;
- the XOR circuit on two constant circuits;
- a far instance and a near instance against `SD^{2/3,1/3}`;
- both instances pushed through the Polarization Lemma.

Run `scripts/build.sh ComplexityTests.StatisticalDifference`.

## Bound the mixing time of a finite Markov chain

Import [MarkovChain/Coupling.lean](../../Complexity/Probability/MarkovChain/Coupling.lean). A chain
`P : Cslib.Probability.MarkovChain S` is a transition kernel `S → PMF S`, and `P ^ t` is its
`t`-step kernel, so `pow_add_apply` is Chapman–Kolmogorov. Prove a stationary law with
`IsStationary P π` (`π.bind P = π`), or more easily with detailed balance
`IsReversible P π` and `IsReversible.isStationary`. To get a chain with a given target,
[MarkovChain/Metropolis.lean](../../Complexity/Probability/MarkovChain/Metropolis.lean) builds
`metropolis Ψ π` from any proposal chain `Ψ`, and `isReversible_metropolis` holds without
positivity or symmetry hypotheses. With `[Fintype S]`,
[MarkovChain/Mixing.lean](../../Complexity/Probability/MarkovChain/Mixing.lean) defines
`distToStationary P π t` (`d(t)`, a maximum over starting states of cslib's half-L1 `dist`),
`distPair P t` (`d̄(t)`) and `mixingTime P π ε : ℕ∞`, which is `⊤` when the chain never comes
within `ε`. Nothing assumes irreducibility or aperiodicity: the periodic flip on `Bool` has
`t_mix(ε) = ⊤` for every `ε < 1/2`. For stationary `π`, `IsStationary.mixingTime_le_iff` turns a
mixing-time goal into `d(t) ≤ ε`, and `IsStationary.mixingTime_le_ceil_logb_mul` amplifies
`t_mix(1/4)` to `t_mix(ε)`.

To bound `d(t)`, build a chain `Q` on `S × S` and prove `IsMarkovianCoupling P Q`, i.e. that both
coordinates of `Q z` have the laws `P z.1` and `P z.2`. Then
`distToStationary_le_of_coupling hπ (fun _ _ => Q) (fun _ _ => hQ) hε` bounds `d(t)` by any `ε`
that bounds `(((Q ^ t) (x, y)).toOuterMeasure {w | w.1 ≠ w.2}).toReal` for all starting pairs.
The bounded event is "the copies differ at time `t`", not the source's coupling-time tail, and is
never larger. The theorem covers time-homogeneous Markovian couplings only, but needs no
stickiness. To bound the event, `PMF.toOuterMeasure_bind_le_mul_ennreal` from
[PMF/Event.lean](../../Complexity/Probability/PMF/Event.lean) gives a step-by-step induction. The
worked client is [BitString/LazyRandomWalk.lean](../../Complexity/Probability/BitString/LazyRandomWalk.lean):
for the lazy hypercube walk `Cslib.BitString.lazyRandomWalk ι`, `mixingTime_lazyRandomWalk_le`
proves `t_mix(ε) ≤ ⌈n log n + n log ε⁻¹⌉`. The ceiling is necessary, as the `n = 1`, `ε = 2/5`
check shows.

When a coupling of all pairs is hard to build, use path coupling from
[MarkovChain/PathCoupling.lean](../../Complexity/Probability/MarkovChain/PathCoupling.lean). Choose
a neighbor relation `N` and a cost `ρ` with `IsPathMetric N ρ`: `ρ` vanishes on the diagonal, is
at least one off it, and every `x ≠ y` has a neighbor `z ≠ x` of `x` with
`ρ x z + ρ z y ≤ ρ x y`. The path metric of `N` with edge lengths at least one satisfies this, but
`ρ` need not be symmetric or satisfy the triangle inequality. For Hamming distance on
`∀ i, β i`, `isPathMetric_hammingDist` supplies this. Then couple one step from neighbors only:
for `N x y`, give `ω : PMF (S × S)` with marginals `P x` and `P y` and
`∑ p, (ω p).toReal * ρ p.1 p.2 ≤ κ * ρ x y`.
`IsStationary.mixingTime_le_of_pathCoupling` turns `0 ≤ κ ≤ exp (-α)` with `0 < α`, and
`ρ ≤ D` with `0 < D`, into `t_mix(ε) ≤ ⌈(log D - log ε) / α⌉` for `0 < ε`, and
`dist_pow_le_of_pathCoupling` gives the underlying
`‖Pᵗ(x, ·) - Pᵗ(y, ·)‖_TV ≤ κᵗ ρ(x, y)`. Optimal couplings of the one-step laws come from
`exists_coupling_toReal_eq_dist` in
[StatisticalDistance/OptimalCoupling.lean](../../Complexity/Probability/StatisticalDistance/OptimalCoupling.lean),
and `dist_uniformOfFinset_le` bounds the distance between uniform laws on nearly equal sets. The
worked client is [MarkovChain/Coloring.lean](../../Complexity/Probability/MarkovChain/Coloring.lean):
for Glauber dynamics on `q`-colorings with `q > 2Δ`, `mixingTime_glauberColoring_le` proves
`t_mix(ε) ≤ ⌈((q - Δ) / (q - 2Δ)) n (log n - log ε)⌉`. Its stationary law needs a proper coloring,
which `SimpleGraph.properColorings_nonempty` provides from greedy coloring
(`SimpleGraph.colorable_of_maxDegree_lt`). Proper colorings, allowed colors and the closure of
proper colorings under recoloring live in
[SimpleGraph/ProperColoring.lean](../../Complexity/Foundations/Combinatorics/SimpleGraph/ProperColoring.lean).

If the chain is confined to a set `C` closed under `P` and does not mix on all of `S`, use the
`_on` forms: `IsPathMetricOn C N ρ` asks for the conditions only on `C`, with geodesic steps in
`C`, and `isPathMetricOn_hammingDist` supplies it for any `C` closed under copying one coordinate.
`dist_pow_le_of_pathCoupling_on` and `IsStationary.dist_le_of_pathCoupling_on` then need couplings
only for neighbors in `C`, and bound the distance from starts in `C`, for a stationary law
supported in `C`. The client is Glauber dynamics with a frozen boundary,
`glauberColoringOn G q U hU`, which recolors only vertices of `U`. On the proper colorings
`G.frozenColorings q U b` that agree with `b` off `U`, `dist_glauberColoringOn_frozen_le_of_le`
gives the sampling time of Levin and Peres, (14.23). It needs `2Δ < q`, `|U| ≤ n`, a start `x`
that agrees with `b` off `U`, a nonempty `G.frozenColorings q U b` (from `mem_frozenColorings_self`
when `b` is proper), `0 < δ` and `t ≥ ((q - Δ) / (q - 2Δ)) n (log n - log δ)`, and gives distance
at most `δ` to the uniform law on `G.frozenColorings q U b`; `dist_glauberColoringOn_edge` in the
checks below instantiates it. For approximate counting,
[Coloring/Ratio.lean](../../Complexity/Probability/MarkovChain/Coloring/Ratio.lean) proves their
Lemma 14.16, `inv_exp_mul_le_card_frozenColorings_erase_div`: freezing one more vertex keeps at
least a `1 / (e q)` fraction of the colorings.
[Coloring/Count.lean](../../Complexity/Probability/MarkovChain/Coloring/Count.lean) proves their
Theorem 14.14, `le_toOuterMeasure_coloringCountEstimator`: `coloringCountEstimator` multiplies,
over the `n` vertices, the fraction of `a` frozen-boundary samples in which one more vertex keeps
its color, and with `t` and `a` as in (14.21) it is within relative error `ε` of
`1 / |properColorings|` with probability at least `1 - η`. The concentration step is the generic
product estimator of [Product/Estimator.lean](../../Complexity/Probability/Product/Estimator.lean):
`le_toOuterMeasure_productEstimate` needs each stage probability within relative error
`ε / (6 n)` of a target `r k ≥ b > 0` and `48 n ≤ 5 η ε² a b`, and proves it from the exact
mean and second moment of independent empirical frequencies by Chebyshev's inequality. Both
results concern only the law of `W`. The `n t a` Glauber updates are not charged in any cost
model, so this is not yet the fully polynomial randomized approximation scheme of Levin and Peres,
Remark 14.15.

The [checked clients](../../ComplexityTests/MarkovChain.lean) compute `d(t) = (2/3)(1/4)^t` and
`t_mix(1/4) = 1` exactly for a two-state chain with non-uniform stationary law, show that the flip
chain never mixes, compute a Metropolis acceptance probability, and give the hypercube instance
with `n = 1`. The [path-coupling checks](../../ComplexityTests/PathCoupling.lean) instantiate the
coloring bound on a single edge, show that the condition `ρ ≥ 1` off the diagonal cannot be
dropped, and compute the frozen colorings, the ratio of Lemma 14.16 and the frozen sampling time
on a single edge. The [counting checks](../../ComplexityTests/ColoringCount.lean) instantiate
Theorem 14.14 on a single edge, show that its sample sizes can always be met, and show that one
sample per stage never gives relative error `1 / 2` there. Run
`scripts/build.sh ComplexityTests.MarkovChain ComplexityTests.PathCoupling ComplexityTests.ColoringCount`.
A goal of the form `t_mix(ε) = k` needs both directions: `mixingTime_le_of_distToStationary_le`
for `≤`, and `(hπ : P.IsStationary π).mixingTime_le_iff` at `k - 1` for `≥`.

## Test for a perfect matching with a random determinant

Import [Matching/Edmonds.lean](../../Complexity/Algorithms/Matching/Edmonds.lean). A bipartite
graph is `G : V × V → Bool` on a finite type `V` of left and right vertices, the representation
of `Cslib.Circuits.BipartiteMatching.HasPerfectMatching`. `edmondsMatrix G` has the indeterminate
`X (i, j)` at each edge and `0` elsewhere. `det_edmondsMatrix_ne_zero_iff` is Edmonds' criterion
(Edmonds 1967):
over any nontrivial commutative ring, the determinant is a nonzero polynomial exactly when `G` has
a perfect matching. The randomized test of Lovász evaluates `edmondsEval G r`, the same matrix
with values `r : V × V → R`. Its error is one-sided: `det_edmondsEval_eq_zero` gives determinant
`0` at every `r` when there is no perfect matching. When there is one, over an integral domain,
`card_det_edmondsEval_eq_zero_div_le` bounds the proportion of `r ∈ S ^ (V × V)` with determinant
`0` by `|V| / |S|`. `exists_det_edmondsEval_ne_zero` turns any `S` with more than `|V|`
elements into a detecting choice of values. The probability is a counting ratio over
`Fintype.piFinset`, not a `PMF`, and no machine running time is certified for the determinant.

The bound comes from two lemmas in
[MvPolynomial/SchwartzZippel.lean](../../Complexity/Foundations/Data/MvPolynomial/SchwartzZippel.lean):
`MvPolynomial.schwartz_zippel_totalDegree_fintype` extends Mathlib's Schwartz–Zippel lemma from
the variables `Fin n` to any finite type, and `MvPolynomial.totalDegree_det_le` bounds the total
degree of a determinant of polynomials. Use them for other symbolic-determinant tests.

The [checked clients](../../ComplexityTests/EdmondsMatching.lean) compute the `2 × 2`
determinant of the complete graph, apply the test to a graph whose right vertex `1` is
unmatched, and show that values from the one-element set `{0}` miss the matching of a single edge.
The bound `|V| < |S|` comes from Schwartz–Zippel and is not sharp in general: the determinant has
degree at most `1` in each variable, so over an integral domain any `S` with two elements detects a
perfect matching (not formalized). Run
`scripts/build.sh ComplexityTests.EdmondsMatching`.

For a general graph, import [Matching/Tutte.lean](../../Complexity/Algorithms/Matching/Tutte.lean).
The graph is a Mathlib `G : SimpleGraph V` with `[DecidableRel G.Adj]` on a finite, linearly ordered
`V`, and a perfect matching is `∃ M : G.Subgraph, M.IsPerfectMatching`. `tutteMatrix G` has one
indeterminate per unordered pair, `X s(i, j)` at an edge with `i < j` and `-X s(i, j)` at an edge
with `j < i`. `det_tutteMatrix_ne_zero_iff` is Tutte's matrix theorem, proved here over any
nontrivial commutative ring (the sources state it over a field). For Tutte's combinatorial
odd-component criterion use Mathlib's `SimpleGraph.tutte`. The randomized test uses `tutteEval G r` with `r : Sym2 V → R`. As in the bipartite case,
`det_tutteEval_eq_zero` gives no false positives, `card_det_tutteEval_eq_zero_div_le` bounds false
negatives by `|V| / |S|` over an integral domain, and `exists_det_tutteEval_ne_zero` finds detecting
values in any `S` with more than `|V|` elements. Two reusable pieces sit underneath:
`Matrix.det_eq_sum_even_cycleType_of_transpose_eq_neg` in
[SkewDeterminant.lean](../../Complexity/Foundations/LinearAlgebra/Matrix/SkewDeterminant.lean)
(odd cycles cancel in a skew-symmetric determinant, via `Equiv.Perm.reverseCycle` in
[ReverseCycle.lean](../../Complexity/Foundations/GroupTheory/Perm/ReverseCycle.lean); an alternating
matrix of odd order has determinant `0`), and `SimpleGraph.exists_isPerfectMatching_of_perm` in
[PermMatching.lean](../../Complexity/Foundations/Combinatorics/SimpleGraph/PermMatching.lean) (a
permutation along the edges with only even cycles gives a perfect matching). The
[checked clients](../../ComplexityTests/TutteMatching.lean), a `module`, compute the determinant
`r²` of a single edge and its `2 / 3` probability bound over `{0, 1, 2}`, extract and detect a
perfect matching of `K₄` from the rotation of `Fin 4`, show that the triangle's Tutte matrix is
singular at all values and that the star `K₁,₃` has the zero Tutte polynomial, and show that the
zero-diagonal hypothesis is needed over `ZMod 2`. Run
`scripts/build.sh ComplexityTests.TutteMatching`.

To find the matching rather than only detect it, import
[Matching/MVV.lean](../../Complexity/Algorithms/Matching/MVV.lean), the algebraic core of
Mulmuley, Vazirani and Vazirani for bipartite graphs. `weightedEdmonds G w` is the Edmonds matrix
over `ℤ` at the values `2 ^ w (i, j)`. When `IsUniqueMinMatching G w σ₀` holds,
`matchingWeight_eq_padicValInt_det` recovers the weight `W` of `σ₀` as the `2`-adic valuation of
the determinant, and `apply_eq_iff_not_two_pow_succ_dvd_mul_adjugate` gives
`σ₀ i = j ↔ ¬ 2 ^ (W + 1) ∣ B i j * adj(B) j i`. The procedure itself is the named relation
`mvvOutput G w`, and `mvvOutput_iff_apply_eq` says that on isolating weights it outputs exactly
`σ₀`. Edge weights are functions `Edges G → Fin N`, read as `1, …, N` by `extendWeight`.
`half_le_dens_exists_isUniqueMinMatching` applies the isolation lemma when `2 |E| ≤ N`, and
`half_le_dens_mvv` states that `MVVSucceeds G (extendWeight w)` (the output is a perfect matching)
holds for at least half of the weight functions. Module clients work through the characterization
lemmas `isUniqueMinMatching_iff`, `matchingWeight_def`, `mvvOutput_iff`, `mvvSucceeds_iff`,
`mem_matchingEdges`, `extendWeight_of_edge` and `extendWeight_of_not_edge`. MVV state the
determinant lemmas for the Tutte matrix of a general graph; general graphs and the parallel
determinant and inverse computations are not formalized. The
[checked clients](../../ComplexityTests/MVVMatching.lean), a `module`, recover the identity
matching on `K₂,₂` from the determinant `-12` and show that equal weights make the determinant
vanish. Run `scripts/build.sh ComplexityTests.MVVMatching`.

## Compose local embeddings and extract a strategy

Import [CorrelatedSampling/Embeddability.lean](../../Complexity/Probability/CorrelatedSampling/Embeddability.lean)
for `IsEmbeddable P₀ P₁ ε`, Holenstein's Definition 5.1 [holenstein09][holenstein09]. From
`(x, y) ~ P₀`, Alice and Bob use shared randomness, but no communication, to produce `s` and `t`
so that `((x, y), (s, t))` is within statistical distance `ε` of `P₁`. The types may live in any
universes, and `IsEmbeddable.of_dist_le` accepts randomness from any type.

- `IsEmbeddable.mono` weakens the error.
- `IsEmbeddable.map` lets each party post-process its own output, for instance to forget part of
  it.
- `IsEmbeddable.trans` composes two embeddings and adds their errors. The second embedding's input
  is the law of `((x, s), (y, t))` under `P₁`; the result is regrouped as
  `((x, y), ((s, u), (t, v)))`.
- `isEmbeddable_map_fst_of_apply_eq_mul` embeds exactly when the masses of a law of
  `((x, y), (s, t))` factor as `c x y · f x s · g y t`, with `f` and `g` finite. The same file
  proves Lemmas 5.2 and 5.4 and Corollary 5.3.
- `dist_withKernel_condY_le` bounds the left side of the second hypothesis of Corollary 5.3,
  `dist J (withKernel P₀ fun xy => condY J xy.2)`, by the distance of `J` from the law that keeps
  `(y, s)` and redraws `x` from a kernel `K` with `P₀ = P_Y K`, plus the distance of the
  `y`-marginals. `dist_withKernel_condX_le` is the mirror image for the first hypothesis.

Import [TwoProverGame.lean](../../Complexity/Computability/PCP/TwoProverGame.lean) to use an
embedding against a game `G`. For tuple strategies `ha` and `hb` of `G.pow n`,
`G.winsOn ha hb C` is the event that every coordinate in `C : Finset (Fin n)` is won, and
`G.winProbOn ha hb C` is its probability. `winProbOn_insert_le` is the strategy extraction in the
proof of Lemma 6.5, multiplied out so that it never divides by `Pr[W_C]`. Its premises are a
support witness `hC` for `G.winsOn ha hb C` and an embedding of `G.questions`, with error `ε`, in
the law of `((x j, y j), (x, y))` under `(G.pow n).questions.filter (G.winsOn ha hb C) hC`. It
concludes `G.winProbOn ha hb (insert j C) ≤ G.winProbOn ha hb C * (G.value + ε)`. If
`Pr[W_C] = 0`, the same inequality follows from `winProbOn_anti` without an embedding. The general
step, `toOuterMeasure_accepts_le_value_add`, turns any embedding of the questions into a strategy
with shared randomness and bounds its success by `G.value + ε`.

The [embedding clients](../../ComplexityTests/Embeddability.lean) compose two exact embeddings
(copy, negate, forget the copies), apply the product-form criterion, and draw shared randomness
from `ULift.{2} Bool`. The [CHSH client](../../ComplexityTests/TwoProverGame.lean) extracts a
strategy from the one-fold repetition with `C = ∅`, which bounds every strategy of `chsh.pow 1`
by `chsh.value`. Run `scripts/build.sh ComplexityTests.Embeddability ComplexityTests.TwoProverGame`.
The next three sections supply the embedding premise at each free coordinate, through the
coordinate embedding of Lemma 6.4;
[the next section](#model-the-coordinates-of-the-parallel-repetition-proof) sets up its random
variables. [Bound the value of a parallel repetition](#bound-the-value-of-a-parallel-repetition)
states Lemma 6.4 as one theorem and proves the parallel repetition theorem.

## Model the coordinates of the parallel repetition proof

Import [ParallelRepetition/CoordinateModel.lean](../../Complexity/Computability/PCP/ParallelRepetition/CoordinateModel.lean)
to work with the random variables of the proof of Holenstein's Lemma 6.4 [holenstein09][holenstein09].
Fix a game `G` with finite question types, tuple strategies `ha` and `hb` of `G.pow n`, a set
`C : Finset (Fin n)` of conditioned coordinates, and a support witness `hC` for
`G.winsOn ha hb C`, as in `winProbOn_insert_le`. The coordinates `j : {i // i ∉ C}` are free.
Holenstein conditions on `C = {k + 1, …, n}`; any `C` works here.

- A sample `ω : Sample X Y C` is a pair `(d, q)`: a bit `d j` for each free coordinate and a
  question pair `q i` for each coordinate. `sampleLaw G C` draws the bits uniformly and the pairs
  independently from `G.questions`, with masses given by `sampleLaw_apply`.
  `condLaw G C ha hb hC` conditions it on winning every coordinate in `C`. Write each law of the
  proof as the image `(condLaw G C ha hb hC).map f` of this one law.
- The variables are functions of `ω`. `revealed C ω` is Holenstein's `T`: the pairs on `C`, and at
  each free `j` one half of the pair, `inl x` when the bit is `true` and `inr y` when it is
  `false`. So the bit `false` plays the role of Holenstein's `D_j = 0`, and `pairGiven G (.inr y)`
  draws Alice's question from `P_{X | Y = y}`. `answers C ha hb ω.2` is `V`, the answers on `C`.
  `ω.2 j` is the whole pair at `j`, where Holenstein's `U_j` is only its hidden half.
  `shared ha hb j ω` is `S`: `T` without its half at `j`, together with `V`.
- `map_condLaw_questions` identifies the image of `condLaw` under
  `fun ω => (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2)` with `(G.pow n).questions.filter (G.winsOn ha hb C) hC`,
  the law in `winProbOn_insert_le`. `map_snd_condLaw` writes the pairs as a conditioned product,
  the input of `sq_sum_dist_map_filter_pi_le`, and `toOuterMeasure_pi_winsOnPairs` gives the
  probability of the event.
- `toOuterMeasure_condLaw_bit` proves `Pr[D_j = b | W_C] = 1 / 2`, the premise of Claim 6.1
  (`dist_filter_le_two_mul`). `map_filter_condLaw_bit` removes a condition `D_j = b` from the law
  of any variable that ignores the bit `d j`; for `shared`, `shared_update` proves that it does.
- `map_sampleLaw_eq_sideJoint` and `map_fst_sideKernel` show that the law of `((T, V), U)` has the
  form that Corollary 4.3 requires. `sum_dist_condLaw_le` is the resulting (6.5): summed over the
  free `j`, the distance between the law of `((T, V), ω.2 j)` under `condLaw` and the law that
  redraws the pair at `j` from `pairGiven G` of its revealed half is at most
  `√(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])) / 2)`. The logarithms are natural; Holenstein's
  (6.6) uses bits and has no factor `1 / 2`.

The [coordinate-model clients](../../ComplexityTests/RepetitionCoordinateModel.lean) compute
`pairGiven` and a sample mass for the CHSH questions, derive from (6.5) that the redrawn law is
exact when `C = ∅`, remove the bit condition from the law of `S`, and pass an embedding into the
model's law to `winProbOn_insert_le`. Run
`scripts/build.sh ComplexityTests.RepetitionCoordinateModel`. The next section carries the proof
from (6.5) to the first stage of the embedding.

## Embed the questions at a free coordinate

Import [ParallelRepetition/Embedding.lean](../../Complexity/Computability/PCP/ParallelRepetition/Embedding.lean)
for the steps (6.7)–(6.16) of the proof of Holenstein's Lemma 6.4 [holenstein09][holenstein09]
and the first stage of its embedding. The setting is that of the previous section. Write
`E := √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])) / 2)` for the bound of (6.5), and `J` for the law
`(condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)` of `((x_j, y_j), S)`.

- `sum_dist_map_condLaw_shared_le hC b` is (6.7)–(6.12). Conditioning both laws of (6.5) on the
  bit `D_j = b` at most doubles their distance (Claim 6.1), and the condition then drops because
  `S` and the pair at `j` ignore the bit. Summed over the free `j`, `J` is within `2 E` of the law
  that keeps `S` and the half `reveal b (ω.2 j)` and redraws the pair from `pairGiven G`.
  `b = false` keeps Bob's question, as in (6.12); `b = true` keeps Alice's.
- `sum_dist_map_condLaw_pair_le hC` is (6.14): summed over the free `j`, the pair at `j` under
  `condLaw` is within `√(#Cᶜ ln (1 / Pr[W_C]) / 2) ≤ E` of `G.questions`.
- `sum_dist_condLaw_withKernel_condY_le hC` and `sum_dist_condLaw_withKernel_condX_le hC` are
  (6.15) and (6.16): summed over the free `j`, `J` is within `3 E` of
  `withKernel G.questions fun xy => condY J xy.2` and of the `condX` analogue. These are the two
  hypotheses of Corollary 5.3 (`isEmbeddable_diag_of_dist_le`). They follow from (6.12) and
  (6.14) by the generic triangle step `dist_withKernel_condY_le` (and `dist_withKernel_condX_le`)
  of [Compose local embeddings and extract a strategy](#compose-local-embeddings-and-extract-a-strategy),
  with `K` drawing one question of `G` given the other.
- `exists_isEmbeddable_condLaw_shared hC` is the first stage. It gives errors
  `ε : {i // i ∉ C} → ℝ` such that `G.questions` embeds with error `ε j` in
  `(condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω))`, and
  `∑ j, ε j ≤ 27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`. The constant is
  `27 = 7 · 3 + 2 · 3`, from the library's Corollary 5.3 error `7 ε₁ + 2 ε₂`; Holenstein's is
  `15`, from `3 ε₁ + 2 ε₂`, with logarithms in bits and no factor `1 / √2`. `27 / √2 ≈ 19.09` is
  within the constant `21` that the sharpened recursion of Lemma 7.1 accepts.

To use a single coordinate, pick `j` with `ε j` at most the average, by
`Finset.exists_le_of_sum_le`; the error is then at most
`27 / √2 · √((#C ln (|A| |B|) + ln (1 / Pr[W_C])) / #Cᶜ)`. The
[embedding clients](../../ComplexityTests/RepetitionEmbedding.lean) do this, and check that with
`C = ∅` every coordinate has the law of `G.questions` and the first stage is exact. Run
`scripts/build.sh ComplexityTests.RepetitionEmbedding`.
[The next section](#extend-the-coordinate-embedding-to-the-question-tuples) proves the second
stage (6.17)–(6.19), which adds the remaining questions through Lemma 5.4, and composes the two
stages.

## Extend the coordinate embedding to the question tuples

Import [ParallelRepetition/Factorization.lean](../../Complexity/Computability/PCP/ParallelRepetition/Factorization.lean)
for the second stage of the proof of Holenstein's Lemma 6.4 [holenstein09][holenstein09], in the
setting of the previous two sections. Write `S` for `shared ha hb j ω` and `(x, y)` for the question
tuples `(Prod.fst ∘ ω.2, Prod.snd ∘ ω.2)`. Holenstein's first stage embeds the questions in
`((x j, S), (y j, S))`; the second extends this to the whole tuples, and the parties then forget
`S`.

- `exists_map_condLaw_apply_eq_mul` is the product form (5.5) of the conditioned law. The mass of
  `(((x j, S), (y j, S)), (x, y))` under `condLaw` factors as `c · f · g`, where `f` depends only
  on Alice's view `(x j, S)` and her tuple `x`, and `g` only on Bob's view `(y j, S)` and `y`.
  Holenstein reaches this form through the Markov chains (6.17)–(6.19) and his Claims 6.2 and 6.3;
  the library computes the masses directly instead.
- `isEmbeddable_map_condLaw_tuples` applies Lemma 5.4 in this form
  (`isEmbeddable_map_fst_of_apply_eq_mul`): the law of `((x j, S), (y j, S))` embeds with error `0`
  in the law of `(((x j, S), (y j, S)), (x, y))`. Its input is the first stage's law of
  `((x j, y j), (S, S))` regrouped as `IsEmbeddable.trans` requires; after `rw [PMF.map_comp]` it is
  the second premise of `IsEmbeddable.trans`.
- `isEmbeddable_filter_questions_of_shared` composes the two stages and forgets `S`. Its premise is
  an embedding of a law `P₀` in
  `(condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω))`, which is
  exactly the per-coordinate embedding of `exists_isEmbeddable_condLaw_shared` in the previous
  section. Directly from Corollary 5.3, `isEmbeddable_diag_of_dist_le J P₀ h₁ h₂` gives such an
  embedding after `rw [PMF.map_comp]`. The conclusion, with the same error, is the embedding premise
  of `winProbOn_insert_le`.

The [factorization clients](../../ComplexityTests/RepetitionFactorization.lean) pass the distance
bounds of Corollary 5.3 for `J` through the second stage to `winProbOn_insert_le`. In the one-fold
repetition with `C = ∅`, `S` is trivial and the first stage is exact, so they bound the probability
of winning the coordinate by `G.value`. Run `scripts/build.sh ComplexityTests.RepetitionFactorization`.
With the previous section, every free coordinate `j` thus supplies the premise of
`winProbOn_insert_le` with error `ε j`. [The next section](#bound-the-value-of-a-parallel-repetition)
states Lemma 6.4 as one theorem, chooses the coordinate of Lemma 6.5 and proves the parallel
repetition theorem.

## Bound the value of a parallel repetition

Import [ParallelRepetition.lean](../../Complexity/Computability/PCP/ParallelRepetition.lean) for
Holenstein's parallel repetition theorem, his Theorem 2.5 [holenstein09][holenstein09]. Fix a game
`G : TwoProverGame X Y A B` with `[Finite X] [Finite Y] [Fintype A] [Fintype B]` and a proof
`hAB : 2 ≤ Fintype.card A * Fintype.card B`. Holenstein's Lemma 7.1 needs `log (|A| |B|) ≥ 1`;
the hypothesis also makes both answer types nonempty. The strategies of `G.pow n` are arbitrary
maps of question tuples to answer tuples, as in `TwoProverGame.pow` and `TwoProverGame.value`.

- `G.value_pow_le hAB n` is Theorem 2.5:
  `(G.pow n).value ≤ (1 - (1 - G.value) ^ 3 / 6000) ^ ((n : ℝ) / Real.logb 2 (Fintype.card A * Fintype.card B))`.
- `G.value_pow_le_of_value_le hAB hv n` takes `hv : G.value ≤ 1 - ε` and gives the same bound with
  `ε ^ 3` in place of `(1 - G.value) ^ 3`. Any real `ε` is allowed; for `ε ≤ 0` the bound is at
  least `1`.
- `G.winProb_pow_le hAB ha hb` is the bound for one pair of strategies `ha` and `hb`.
- `G.exists_isEmbeddable_filter_questions ha hb hC` is Lemma 6.4, the composition of the two
  stages of the previous sections. At every free coordinate `j : {i // i ∉ C}`, `G.questions` embeds
  with error `ε j` in the law of `((x j, y j), (x, y))` under
  `(G.pow n).questions.filter (G.winsOn ha hb C) hC`, the premise of `winProbOn_insert_le`, and
  `∑ j, ε j ≤ 27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`.
- `G.exists_winProbOn_insert_le ha hb hCu` is Lemma 6.5, multiplied out. For `hCu : C ≠ univ`, it
  gives `j ∉ C` with
  `Pr[W_{insert j C}] ≤ Pr[W_C] (v(G) + 27 / √2 · √((#C ln (|A| |B|) + ln (1 / Pr[W_C])) / (n - #C)))`.
  It needs no support witness: if `Pr[W_C] = 0`, any free coordinate works. It picks a coordinate
  with at most the average error of Lemma 6.4, by `Finset.exists_le_of_sum_le`.

The proof of Theorem 2.5 adds the coordinates of Lemma 6.5 one at a time, starting from `∅`, so
that `p_m = Pr[W_{C_m}]` satisfies the recursion of `ParallelRepetition.le_rpow_of_step`, Holenstein's
(7.6). The step has the constant `27 / √2 ≈ 19.09` and natural logarithms, where Holenstein's has
`15` and bits; `ln x ≤ log₂ x` for `x ≥ 1` passes to `L = log₂ (|A| |B|)`, and the sharpened
recursion accepts any constant up to `21`. The final bound has Holenstein's constant `6000`.

To use the bound for concrete answer types, compute the exponent: rewrite the product of the
cardinalities as a power of two and apply `Real.logb_rpow`. For CHSH, `|A| |B| = 4` and the
exponent is `n / 2`. [CHSH.lean](../../Complexity/Computability/PCP/TwoProverGame/CHSH.lean)
proves that CHSH has value `3/4` (`TwoProverGame.value_chsh`), and the [parallel repetition clients](../../ComplexityTests/ParallelRepetition.lean)
derive `(3/4)^n ≤ v(CHSHⁿ) ≤ (1 - (1/4)³ / 6000)^{n / 2}`. They also show that the value of the
repetition tends to zero for every game of value below one, and apply Lemma 6.5 with nothing
conditioned, which gives a coordinate won with probability at most `G.value`. Run
`scripts/build.sh ComplexityTests.ParallelRepetition`.

For Label Cover, import
[LabelCover/Repetition.lean](../../Complexity/Computability/PCP/Approximation/LabelCover/Repetition.lean)
and open `Cslib.PCP.Encoded`. For an instance `g : Graph (β → γ)` with `[Fintype β] [Fintype γ]`
and `[DecidableEq γ]`, apply `LabelCoverRepetition.one_sub_unsatVal_pow_le hpar hβγ hε k`. Its
premises are that the instance has no parallel edges (`hpar : g.NoParallelEdges`, decidable), that
`2 ≤ Fintype.card β * Fintype.card γ`, and `hε : ε ≤ (g.toGraph projectionEval).unsatVal`. The
conclusion bounds the satisfied proportion `1 - ((pow k g).toGraph projectionEval).unsatVal` of the
`k`-fold repetition `LabelCoverRepetition.pow k g`. The bound does not require the edge list to be
nonempty or well formed. The vertex numbers of the repetition grow like `(n + 1) ^ (2 ^ k)`
(`LabelCoverRepetition.vertices_pow_le`), so its polynomial-time compilation holds for each fixed
`k` only. The [Label Cover repetition clients](../../ComplexityTests/LabelCoverRepetition.lean)
compute the numbering of a two-fold repetition, separate instances without parallel edges from
instances with them, and bound the repetitions of an instance of value `1/2` by
`(1 - (1/2)³ / 6000)^{k / 2}`.

For a hardness result, import
[LabelCover/SmallSoundness.lean](../../Complexity/Computability/PCP/Approximation/LabelCover/SmallSoundness.lean).
`polyTimeReducible_GapTwoCSP_GapLabelCover_pow a b hab encA hε hε1 hk` reduces
`GapTwoCSP α (1 - ε)` to Label Cover over `k`-tuples, for any finite alphabet `α` with two
distinct symbols, `0 < ε ≤ 1` and `0 < k`. The soundness is
`(1 - (ε / 2)³ / 6000)^{k / log₂ (|α|² |α|)}`. Apply `Graph.deloop` before
`LabelCoverIncidence.reduce`: loop removal makes a binary CSP instance loopless without changing
its value (`Graph.isLoopless_deloop`, `Graph.unsatVal_deloop`), and the incidence reduction of a
loopless instance has no parallel edges (`LabelCoverIncidence.noParallelEdges_reduce`). Compose with a hard source through
`PromiseProblem.NPHard.trans`, as `GapLabelCover_npHard_pow` does with `GapTwoCSP_npHard`, and
weaken the soundness with `PromiseProblem.NPHard.mono`, as `exists_GapLabelCover_npHard` does. The
[small-soundness clients](../../ComplexityTests/LabelCoverSmallSoundness.lean) remove a concrete
loop, show that the incidence reduction of a loop has parallel edges and has none after loop
removal, and instantiate both hardness theorems. Run
`scripts/build.sh ComplexityTests.LabelCoverRepetition ComplexityTests.LabelCoverSmallSoundness`.
Håstad's reductions from Label Cover remain open
([#886](https://github.com/cslib-community/complexitylib/issues/886)).

## Project a continuous Gaussian density

Import [Gaussian/Standard.lean](../../Complexity/Foundations/Probability/Gaussian/Standard.lean)
when a calculation starts from the density `exp (-π * ‖x‖² / s²) / s^dim` relative to
ambient volume. For `s > 0`, `gaussianWeight_withDensity_eq_map_stdGaussian` identifies
this actual measure with `stdGaussian E` scaled by `s / √(2π)`. It reuses the normalized
`Measure.withDensity` construction; it does not introduce another Gaussian measure.

Apply `gaussianWeight_withDensity_map_inner s hs z` to identify the law of `⟪z, x⟫`
as `gaussianReal 0 (((s * ‖z‖)^2 / (2 * Real.pi)).toNNReal)`. The theorem includes
`z = 0` and dimension zero, where the law is a point mass. The
[checked clients](../../ComplexityTests/GaussianStandard.lean) recover the standard law
at width `√(2π)` and compute variance `32/π` at width `4` with scalar projection `2`.
These are analytic measure identities. Projection of a discrete-coset Gaussian convolution
and its mod-one error bound are proved in [#2734](https://github.com/cslib-community/complexitylib/issues/2734);
no sampler or runtime certificate follows from this identification.

## Describe a discrete Gaussian law

Import [Gaussian/Discrete.lean](../../Complexity/Foundations/Probability/Gaussian/Discrete.lean)
for `ZLattice.discreteGaussian L s hs c`, a PMF on a discrete `ℤ`-submodule `L` of a
finite-dimensional real normed space. Supply `hs : 0 < s`; the center `c` is any ambient
point. `summable_gaussianWeight` proves convergence of the infinite lattice sum, and
`gaussianMass_pos` proves its strict positivity. `discreteGaussian_apply` gives each
probability as `exp (-π * ‖z - c‖² / s²)` divided by that total mass. No full-rank assumption
is needed.

Use `map_add_discreteGaussian` to move the law along a lattice translation, and
`support_discreteGaussian` to discharge point-support obligations. The
[checked examples](../../ComplexityTests/DiscreteGaussian.lean) use the infinite integer
lattice at the off-lattice center `1/2`, distinguish its law from a point mass, and check the
zero lattice. This is a mathematical distribution, with no efficient sampler or smoothing
bound. Regev's quantum worst-case/average-case reduction remains open in
[issue #1213](https://github.com/cslib-community/complexitylib/issues/1213).

For a quantitative radius estimate, import
[Gaussian/DiscreteTail.lean](../../Complexity/Foundations/Probability/Gaussian/DiscreteTail.lean).
Choose a second width `t > s` and a radius `R ≥ 0`.
`summable_discreteGaussian_mul_exp` proves that the exponential norm-square moment is finite;
`tsum_toReal_discreteGaussian_mul_exp` identifies it with `gaussianMass L t c / gaussianMass L s c`.
Writing `κ = π * (1 / s² - 1 / t²) > 0`, `discreteGaussian_norm_ge_le` bounds the probability
of `R ≤ ‖z - c‖` by `exp (-κ * R²)` times that same ratio. The checked integer-lattice
client uses `s = 1`, `t = 2`, center `1/2` and radius `2`, giving the decay factor `exp (-3π)`.
The ratio remains explicit for arbitrary centers. For a full-rank lattice centered at zero,
the [centered bounds below](#bound-a-centered-discrete-gaussian) control this ratio using
Poisson summation. These distributional estimates supply no sampling algorithm.

To vary the center continuously, import
[Gaussian/Periodization.lean](../../Complexity/Foundations/Probability/Gaussian/Periodization.lean).
`ZLattice.continuous_gaussianMass L s hs` proves continuity of the normalizer for `hs : 0 < s`.
The proof establishes summable sup norms of the lattice translates on every compact set, so
the continuous sum comes from local uniform convergence.

For other decaying functions, import
[Lattice/Periodization.lean](../../Complexity/Foundations/Analysis/Lattice/Periodization.lean).
Supply a bundled continuous map `f : C(E, F)` into a complete normed additive group, a real exponent
`b > Module.finrank ℤ L`, and `f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))`.
`ZLattice.continuous_tsum_translate` proves continuity of `x ↦ ∑' z : L, f (x + z)`;
`continuous_automorphize` proves continuity of Mathlib's existing `QuotientAddGroup.automorphize`
on the quotient of `E` by `L.toAddSubgroup`. For a Schwartz function, import
[Lattice/Schwartz.lean](../../Complexity/Foundations/Analysis/Lattice/Schwartz.lean) and use
`SchwartzMap.continuous_automorphize` directly. The
[checked clients](../../ComplexityTests/LatticePeriodization.lean) include a nonzero Schwartz
bump, an infinite integer lattice, a skew two-dimensional basis, and a rank-zero lattice on
an off-center compact interval. For Fourier coefficient identification, see
[the quotient-integral workflow below](#unfold-a-lattice-fourier-coefficient). For the full
formula, use the Poisson API below.

## Apply lattice Poisson summation

Import [Lattice/Poisson.lean](../../Complexity/Foundations/Analysis/Lattice/Poisson.lean).
Here `E` is a finite-dimensional real inner-product space with its canonical volume. Supply a
discrete `L : Submodule ℤ E` and `[IsZLattice ℝ L]`, which requires the lattice to span `E`.
For a Schwartz function `f`, `SchwartzMap.tsum_eq_tsum_fourier_lattice f L x` identifies the
sum of `f (x + z)` with the dual-lattice Fourier sum, divided by `ZLattice.covolume L`.
The dual is Mathlib's existing `LinearMap.BilinForm.dualSubmodule (innerₗ E) L`; the character
at dual frequency `w` is `exp(2πi * inner x w)`. Convergence of both sums is proved from
Schwartz decay. The generic `ZLattice.tsum_eq_tsum_fourier_of_rpow_decay` accepts explicit
polynomial decay, integrability and summability of the actual Fourier samples when a function
is not supplied as a Schwartz map.

For Gaussian mass, import
[Gaussian/Poisson.lean](../../Complexity/Foundations/Probability/Gaussian/Poisson.lean) and apply
`ZLattice.gaussianMass_eq_tsum_dual L s hs c` with `hs : 0 < s` and any center `c`.
This is an equality in `ℂ`: the real mass equals `s^dim / covolume L` times the dual sum of
`gaussianWeight (1 / s) w` multiplied by `exp(-2πi * inner c w)`.
The negative phase comes from evaluating the periodization at `-c`. The theorem includes
dimension zero and arbitrary full-rank bases, including skew bases. It proves the required
Gaussian integrability and Fourier summability; it does not assume a Poisson identity.

The complete [LatticePoisson.lean examples](../../ComplexityTests/LatticePoisson.lean) apply
both endpoints to a skew basis of covolume `2`, check opposite character signs at a nonzero
frequency, and check the dimension-zero covolume and mass of `1`. From the repository root,
run `scripts/build.sh ComplexityTests.LatticePoisson` to check these clients. If the
full-rank instance is missing, start from the basis-spanned lattice in these examples;
continuity alone also applies to lower-rank lattices, but this Poisson formula needs full rank.
For centered truncation and uniform shifted-mass control, use the bounds below.
Quotient-distribution consequences, efficient sampling and Regev's quantum reduction remain open.

## Bound a centered discrete Gaussian

Import [Gaussian/CenteredTail.lean](../../Complexity/Foundations/Probability/Gaussian/CenteredTail.lean).
Use a finite-dimensional real inner-product space, a discrete full-rank lattice
`L : Submodule ℤ E`, and center `0`. Write `n = Module.finrank ℝ E`.
For `0 < s ≤ t`, `ZLattice.gaussianMass_zero_div_le L s hs t hst` bounds
`gaussianMass L t 0 / gaussianMass L s 0` by `(t / s)^n`. The estimate is uniform over these
lattices and follows from the proved Poisson identity and positive dual Gaussian weights.
Equal widths and dimension zero are included.

`ZLattice.discreteGaussian_zero_norm_ge_le L s hs R hR` bounds the probability of
`R ≤ ‖z‖`, for `R ≥ 0`, by `2^n * exp(-3π R² / (4s²))`. For the source-radius endpoint,
use `discreteGaussian_zero_norm_gt_sqrt_lt L s hs`: the probability of
`s * sqrt n < ‖z‖` is strictly less than `(1 / 4)^n`. Both the event and the inequality are
strict, as in Regev's Lemma 2.5. In dimension zero the event is empty and the bound is `1`.
These results control the probability discarded by centered finite-radius truncation;
uniform shifted-mass control is described next, while an efficient sampler remains separate.

The [complete checked clients](../../ComplexityTests/DiscreteGaussianCenteredTail.lean)
use the infinite lattice generated by `2` in the real line. They instantiate mass scaling,
equal widths, and width `2` with radius `2`; the lattice point exactly at that radius is
excluded by the strict event. They also check the dimension-zero empty-event probability.
Run `scripts/build.sh ComplexityTests.DiscreteGaussianCenteredTail` from the repository root.
A missing full-rank instance can be supplied by the basis-spanned construction in that file.
For a nonzero center, the earlier tail bound retains its explicit normalizer ratio.

## Control Gaussian mass uniformly over centers

Import [Gaussian/Smoothing.lean](../../Complexity/Foundations/Probability/Gaussian/Smoothing.lean).
For a discrete full-rank lattice `L` in a finite-dimensional real inner-product space,
write `D = LinearMap.BilinForm.dualSubmodule (innerₗ E) L`, `n = Module.finrank ℝ E`,
and take `s > 0`. The error `δ = gaussianMass D (1 / s) 0 - 1` is the actual convergent
Gaussian sum over nonzero dual lattice points, by `gaussianMass_zero_sub_one_eq_tsum`.
It is nonnegative; it is not an extra comparison assumption.

`ZLattice.abs_gaussianMass_normalized_sub_one_le L s hs c` proves, for every center `c`,
`abs(covolume L / s^n * gaussianMass L s c - 1) ≤ δ`.
Given `δ ≤ ε`, `gaussianMass_mem_Icc_of_dual_mass_le` gives the mass interval
`(s^n / covolume L) * (1 ± ε)`. This is the dual-tail form of Regev's Claim 3.8;
the source's translate `L + c` corresponds to center `-c` in the library.

To obtain the small error, supply a positive lower bound `a` for the norm of every nonzero
point of `D`. The sufficient numerical condition is
`2^n * exp(-3πs²a² / 4) ≤ ε / (1 + ε)`, with `ε > 0`.
`gaussianMass_dual_sub_one_le_of_gap` proves `δ ≤ ε` from this condition using the
centered Gaussian tail. `eventually_gaussianMass_dual_sub_one_le` proves that the bound
holds for all sufficiently large widths for every such lattice and every positive error.
It obtains a genuine positive dual gap from the dual lattice’s discrete topology.

The [checked clients](../../ComplexityTests/DiscreteGaussianShiftBounds.lean) use `2ℤ`,
its dual gap `1/2`, width `2`, error `1/2`, and center `1`, which is outside the lattice.
They also check the empty nonzero dual sum and exact normalized mass in dimension zero.
Run `scripts/build.sh ComplexityTests.DiscreteGaussianShiftBounds` from the repository root.
A width too small to satisfy the sufficient condition can still use the unconditional
actual-dual-error bound. The [quotient probability](#compare-an-actual-gaussian-quotient-distribution-with-uniform-measure)
and [coset-convolution](#add-continuous-gaussian-noise-to-a-coset-gaussian) consequences are
described below; a minimum smoothing parameter and efficient sampler remain separate.

## Condition a discrete Gaussian on coefficient residues

Import [Gaussian/CoefficientFiber.lean](../../Complexity/Foundations/Probability/Gaussian/CoefficientFiber.lean).
Give an integer basis `b` of the discrete lattice, a positive modulus `p`, a width `r > 0`,
and an arbitrary center `c`. `ZLattice.coefficientMod L b p` reduces the basis coordinates
into `ι → ZMod p`; `coefficientLift` supplies their least-nonnegative-coordinate representative
`u`. With `open scoped Pointwise`, the canonical submodule `(p : ℝ) • L` is the image of
multiplication by `p`.

`map_coefficientMod_discreteGaussian_apply` identifies each residue probability as
`gaussianMass (p • L) r (c - u) / gaussianMass L r c`, in `ENNReal` form.
`map_coefficientMod_discreteGaussian_pos` proves every event has positive probability.
`filter_coefficientMod_discreteGaussian` then identifies the actual `PMF.filter` with a draw
from `discreteGaussian (p • L) r hr (c - u)` followed by translation by `u`.
There is no index or covolume factor in this conditional law.

`map_coefficientMod_pair_discreteGaussian` reconstructs the tagged sample by drawing its
actual residue marginal and then the corresponding coset Gaussian. These weights are not
assumed uniform. The [checked clients](../../ComplexityTests/DiscreteGaussianCoefficientFiber.lean)
use the infinite lattice `2ℤ`, composite modulus `6`, residue `1`, and center `1/2`:
the representative is `2`, the scalar lattice contains `12`, and the conditional center is
`-3/2`. Rank-zero and dimension-zero cases are also checked. Run
`scripts/build.sh ComplexityTests.DiscreteGaussianCoefficientFiber` to check the clients.

This is the exact conditioning step used in Regev's Lemma 3.11, not its joint LWE sample
bound or an efficient sampling procedure. The [joint experiment](https://github.com/cslib-community/complexitylib/issues/2767)
and the [full reduction](https://github.com/cslib-community/complexitylib/issues/1213) remain separate.

## Fold a density onto a quotient

Import [QuotientDensity.lean](../../Complexity/Foundations/MeasureTheory/Group/QuotientDensity.lean)
to push a nonnegative density through a countable additive-subgroup quotient. Given a measurable
`f : G → ℝ≥0∞`, measurable subgroup translations, an invariant ambient measure `μ`, and
`hF : IsAddFundamentalDomain Γ.op F μ`, apply
`QuotientAddGroup.map_withDensity_eq_withDensity_automorphize hF hf`. It identifies the image of
`μ.withDensity f` with the density `QuotientAddGroup.automorphize f` relative to the image of
`μ.restrict F`. At the coset of `x`, that density sums `f (x + γ)` over subgroup elements.

The theorem derives measurability on the canonical quotient measurable space and allows infinite
values and infinite total mass. It does not require a measurable fundamental domain beyond the
null-measurability already in `hF`. The [checked clients](../../ComplexityTests/QuotientDensity.lean)
cover bottom and top subgroups, a two-element group, infinite densities on a null measure, and
the Borel measurable space of a discrete lattice quotient. The following Gaussian consumer
proves the required probability normalizations before applying a distance formula.

## Compare an actual Gaussian quotient distribution with uniform measure

Import [Gaussian/Quotient.lean](../../Complexity/Foundations/Probability/Gaussian/Quotient.lean).
Let `L` be a discrete full-rank lattice in a finite-dimensional real inner-product space `E`,
let `n = Module.finrank ℝ E`, and take `s > 0`. Use `q = QuotientAddGroup.mk`, the
canonical map to the quotient by `L.toAddSubgroup`, and an actual fundamental domain
`hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume`. The opposite subgroup acts by right
translation, the convention of Mathlib's quotient measures, while the lattice APIs give
fundamental domains for `L` itself. In a commutative group the two have the same fundamental
domains, and `MeasureTheory.isAddFundamentalDomain_op_iff` from
[FundamentalDomain.lean](../../Complexity/Foundations/MeasureTheory/Group/FundamentalDomain.lean)
converts between them. When `L` is `Submodule.span ℤ (Set.range b)` for a real basis `b`,
`isAddFundamentalDomain_op_iff.mpr (ZSpan.isAddFundamentalDomain' b volume)` supplies `hF`
for `F = ZSpan.fundamentalDomain b`, as in the checked clients below. The measures are ordinary
`Measure.withDensity`, `Measure.map` and scalar multiplication:

- The ambient Gaussian is `volume.withDensity (fun x => ENNReal.ofReal
  (gaussianWeight s x / s^n))`. Its probability normalization is
  `ProbabilityTheory.isProbabilityMeasure_gaussianWeight s hs`.
- The uniform reference is `(ENNReal.ofReal (ZLattice.covolume L))⁻¹ •
  Measure.map q (volume.restrict F)`.
  `ZLattice.measure_eq_ofReal_covolume_of_op L volume hF` identifies `volume F` with the
  covolume; `ZLattice.isProbabilityMeasure_normalized_quotient L volume hF`,
  `normalized_quotient_eq` and `isAddLeftInvariant_normalized_quotient` prove probability
  normalization, independence from the chosen fundamental domain, and translation invariance.

`ZLattice.map_gaussianWeight_eq_withDensity L s hs hF` identifies the actual Gaussian
pushforward's density relative to this reference. At `q x`, the real density is
`covolume L / s^n * gaussianMass L s (-x)`; the opposite center comes from summing
`gaussianWeight s (x + z)`. The representative identity is available as
`automorphize_gaussianWeight_coe`.

`ZLattice.tvDist_gaussian_quotient_le L s hs hF` bounds the distance between these actual
probability measures by `gaussianMass D (1 / s) 0 - 1`, where `D` is the existing dual
submodule. Compose it with `gaussianMass_dual_sub_one_le_of_gap` for a numerical sufficient
width condition. `eventually_tvDist_gaussian_quotient_le L hF ε hε` proves that every positive
error is achieved at all sufficiently large positive widths. The bound does not assume a
small dual mass or a conclusion about the quotient distribution.

Here `tvDist` is full L1, matching Regev's printed page 13 convention with range `[0, 2]`;
there is no extra factor of one half in the stated bound. This is a precise quotient
consequence of Claim 3.8, not a uniform probability on all of real space or the convolution
statement of Claim 3.9. Efficient sampling and the quantum reduction remain open.

The [checked clients](../../ComplexityTests/DiscreteGaussianShiftBounds.lean) reuse `2ℤ`
with covolume `2`, width `2`, and its proved dual gap `1/2`. They check both probability
normalizations, the actual density at the off-lattice representative `1`, full-L1 distance
at most `1/2`, and eventual small error. In dimension zero, the two actual measures are
proved equal and their distance is zero. Run
`scripts/build.sh ComplexityTests.DiscreteGaussianShiftBounds` from the repository root.

## Convolve a singular law with a density

Import [ConvolutionDensity.lean](../../Complexity/Foundations/MeasureTheory/Group/ConvolutionDensity.lean).
For a measurable group with measurable multiplication and inversion, let `σ` and `μ` be
s-finite measures, let `μ` be left invariant, and supply `hf : Measurable f` for
`f : G → ℝ≥0∞`. Apply
`MeasureTheory.mconv_withDensity_eq_withDensity_lintegral hf` to identify
`Measure.mconv σ (μ.withDensity f)` with a density relative to `μ`: at `x`, integrate
`f (y⁻¹ * x)` against `σ`. The theorem derives measurability of that density.

For additive groups, use `conv_withDensity_eq_withDensity_lintegral`; the translated density
is `f (-y + x)`. The first measure can be singular, such as a discrete distribution.
The existing two-density convolution theorem requires both input laws to have densities with
respect to the same reference measure. This theorem needs only the second one to have a density.
It allows infinite total mass and infinite density values, and assumes no integrability or
probability normalization.

The [checked clients](../../ComplexityTests/ConvolutionDensity.lean) translate an actual
Gaussian by an atom and recover the variance-two Gaussian from two variance-one inputs.
A noncommutative permutation-group example checks the order of translation; infinite-density
and zero-input cases check the absence of hidden finiteness premises. Run
`scripts/build.sh ComplexityTests.ConvolutionDensity` from the repository root.
The [lattice Gaussian convolution bound](https://github.com/cslib-community/complexitylib/issues/2707)
below supplies its actual discrete weights, completion of the square and quantitative error proof.

## Add continuous Gaussian noise to a coset Gaussian

Import [Gaussian/Convolution.lean](../../Complexity/Foundations/Probability/Gaussian/Convolution.lean).
Take a discrete full-rank lattice `L`, an arbitrary translate `u`, positive widths `r`, `s`,
and positive `t` with `t² = r² + s²`. Thus `t` is the positive square root of the sum.
The coset law on `L + u` samples `discreteGaussian L r hr (-u)` and maps `z` to `z + u`.
The continuous noise measure is
`volume.withDensity (fun x => ENNReal.ofReal (gaussianWeight s x / s^n))`,
where `n = Module.finrank ℝ E`. The experiment is their actual `Measure.conv`.

Write `h = r*s/t` and `A_w(c) = covolume L / w^n * gaussianMass L w c` for this paragraph.
`ZLattice.conv_discreteGaussian_eq_withDensity` identifies the experiment's density relative
to the normalized continuous Gaussian of width `t` as
`A_h((r/t)² • x - u) / A_r(-u)`.
The proof completes the square and integrates the actual countable mixture; it does not
assume a convolution or smoothing conclusion. The denominator is strictly positive.

With `D` the existing dual submodule and `δ_w = gaussianMass D (1/w) 0 - 1`,
`tvDist_conv_discreteGaussian_le` proves the unconditional bound
`(δ_h + δ_r) / A_r(-u)`. Both measures are probability measures and the relative density is
integrable. `tvDist` here is the full-L1 distance, matching Regev's convention and ranging
from `0` to `2`; there is no factor of one half in this theorem.

For the source's `4ε` conclusion, `tvDist_conv_discreteGaussian_le_of_dual_mass_le` accepts
`0 ≤ ε < 1/2` and the actual sum bound `δ_h ≤ ε`.
`tvDist_conv_discreteGaussian_le_of_gap` proves that premise from a positive lower bound
`a` on nonzero dual norms and `2^n * exp(-3πh²a²/4) ≤ ε/(1+ε)`, with `ε > 0`.
The [checked clients](../../ComplexityTests/DiscreteGaussianConvolution.lean) use `L = 2ℤ`,
`u = 1/2`, `r = 3`, `s = 4`, `t = 5`, `a = 1/2`, and a proved numerical criterion giving
distance at most `4/7`. They also prove equality of the actual measures in dimension zero.
Run `scripts/build.sh ComplexityTests.DiscreteGaussianConvolution` to check them.

This proves the bounded analytic Claim 3.9 consequence with an explicit sufficient width
criterion. The scalar and mod-one laws are handled below; the minimum smoothing parameter,
search-LWE experiment, efficient finite-precision sampling and quantum implementation remain
separate.

## Project the coset experiment and reduce modulo one

Import [Gaussian/Projection.lean](../../Complexity/Foundations/Probability/Gaussian/Projection.lean)
for the actual experiment `⟪z, v⟫ + e`, where `v` is drawn from the discrete Gaussian on
`L + u` and `e` is an independent scalar `gaussianReal` of variance `α²/(2π)`.
The coset draw is the existing `discreteGaussian L r hr (-u)`, mapped by `v ↦ v + u`.
For `r, α > 0`, the comparison Gaussian has variance `((r * ‖z‖)² + α²)/(2π)`.

`tvDist_conv_map_inner_discreteGaussian_le_of_dual_mass_le` bounds their full-L1 distance
by `4ε`, for `0 ≤ ε < 1/2`, when the actual nonzero dual mass at reciprocal width
`√(1/r² + (‖z‖/α)²)` is at most `ε`. The `_of_gap` theorem discharges that mass bound
from a positive dual gap `a` and
`2^dim * exp(-3π h² a²/4) ≤ ε/(1+ε)`, where
`h = 1/√(1/r² + (‖z‖/α)²)` and `ε > 0`. Both theorems cover every `z`, including `z = 0`
and dimension zero, under their stated premise; at `z = 0` itself, `simp` reduces the
convolution directly to the scalar noise law with no smoothing condition.

Use `tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_dual_mass_le` or
`tvDist_map_mod_one_conv_map_inner_discreteGaussian_le_of_gap` for the same bound
after mapping both measures by the canonical `ℝ → UnitAddCircle` coercion. This compares
actual probability measures, with no density-series assumption.
The [checked clients](../../ComplexityTests/DiscreteGaussianProjection.lean) use `2ℤ`,
off-lattice shift `1/2`, `r = 3`, `α = 8` and projection vector `2`. They prove the dual gap
`1/2` and numerical criterion at `ε = 1/7`, yielding distance at most `4/7` on both the
real line and the circle. The input scalar noise has variance `32/π`, and the comparison
has variance `50/π`.

The convention is Regev's full-L1 distance from printed page 13, with range `[0,2]`.
The source's mod-one Gaussian sampling law is represented by its actual measure pushforward;
its periodic-density series, the joint LWE sample law in Lemma 3.11, efficient sampling,
finite precision and the quantum reduction remain separate work.

## Certify a closed randomized routine

Use `IsPPTOn input output program` when the required conclusion is a uniform, strict polynomial-time implementation on encoded types. The encodings are embeddings into bit lists. One finite-control fair-coin machine and one polynomial clock must work for every input, with exact equality of encoded output laws. Output writing is charged. This is the contract to request before proving a probabilistic routine efficient.

<!-- worked-example -->

**Worked example: Compose a fair coin with a certified callback**

**Goal:** certify a coin-sampling routine, then a scan whose deterministic callback has a supplied polynomial-time certificate.

Open [ComplexityTests/PPTTactic.lean](../../ComplexityTests/PPTTactic.lean). Its entry import is `Complexity.Tactic.PPT`; the file also imports `Complexity.Crypto.Computational.GGM.Evaluation` for later clients. The following contextual excerpt uses its `open Cslib Cslib.Probability Turing.MultiTapeTM`. It is copied from the checked file, not independently checked as a standalone snippet.

<!-- excerpt: ppt-coin-reverse -->
```lean
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt
```

The working sequence is: choose the input/output encodings, write the program, supply certificates for named callbacks, and invoke `ppt`. It combines probabilistic composition rules with deterministic `polytime` automation. For a callback, the missing obligation is often a deterministic certificate with the exact captured-argument encoding. This second contextual excerpt, from the same client, makes that obligation visible:

<!-- excerpt: ppt-callback-scan -->
```lean
example (test : List Bool × Bool × ℕ → Bool)
    (htest : ComputableInPolyTime test
      (encPair encBits (encPair encBool encUnary)) encBool) :
    IsPPTOn encBits encBool (fun word => do
      let bit ← ProbComp.uniform Bool
      pure ((List.range word.length).any fun i => test (word, bit, i))) := by
  fail_if_success (clear htest; ppt)
  ppt
```

**Result:** native efficiency of the whole sampling-and-scan routine. This does not establish the application-specific meaning of `test`.

**When it fails:** compare tuple association and encodings before unfolding the machine. Here the scan index is unary; a binary certificate is a different contract. For folds, inspect the client's explicit `PolyBounded` growth premise. For a named routine, the same file demonstrates registering its proved theorem with `@[program_certificate]`.

<!-- /worked-example -->

Also check the sampler itself. `ProbComp.uniform (Fin 3)` has exact uniform semantics, but a strictly bounded fair-coin machine cannot give each outcome probability one third. The client deliberately tests that `ppt` does not certify it for free. Use an applicable dyadic sampler or the library's approximate-sampling results, carrying the approximation error into the later probability proof.

## Bound a centered-binomial sampler tail

[CenteredBinomial/Concentration.lean](../../Complexity/Languages/Probabilistic/CenteredBinomial/Concentration.lean)
bounds the law of the existing `sampleCenteredBinomial η` program. For `η > 0` and real
`B ≥ 0`, `sampleCenteredBinomial_tail_le` gives
`Pr[B ≤ |z|] ≤ 4 exp(-B²/(2η))`; `sampleCenteredBinomial_strict_tail_le` gives the same
bound for `B < |z|`. This original two-count union bound is not optimal. Width zero remains
`pure 0`, so its strict and non-strict zero cutoffs differ.

The [checked clients](../../ComplexityTests/CenteredBinomialConcentration.lean) show positive
mass at both width-eight endpoints, an empty strict tail above eight, and a non-strict tail
bound below one. They also certify the actual growing program with `η = 8(l+1)` as
`IsPPTOn encUnary encIntBin` and bound its strict tail above `4(l+1)` by `4 exp(-(l+1))`.
The native certificate charges unary width and signed binary output; this scalar result
supplies neither encryption correctness nor a security reduction.

## Certify an adaptive oracle client

For native oracle efficiency, start with `WordOracleComp Operation α`: finite operation names and word payloads/replies.

<!-- worked-example -->

**Worked example: Bound the reply prefix of an adaptive oracle call**

**Goal:** certify the oracle client's native runtime while allowing its next query to depend on the previous reply.

Open [ComplexityTests/OracleComposition.lean](../../ComplexityTests/OracleComposition.lean), whose main import is `Complexity.Computability.Probabilistic.Oracle.Composition`. Its query-bound examples additionally import `Complexity.Computability.Probabilistic.QueryBounds`. This contextual excerpt uses the file's `open Cslib Cslib.Probability Turing Turing.MultiTapeTM`:

<!-- excerpt: oracle-adaptive-prefix -->
```lean
private noncomputable def adaptive (word : List Bool) : WordOracleComp Bool (List Bool) := do
  let first ← List.take 1 <$> ProbOracleComp.query (false, word)
  if first = [true] then List.take word.length <$> ProbOracleComp.query (true, first)
  else pure []

-- The certificate is found compositionally from the bounded-prefix query and the conditional.
private theorem adaptive_isOraclePPTOn : IsOraclePPTOn encBits encBits adaptive := by
  unfold adaptive
  fun_prop
```

First specify the operation set and request representation. Then bound the amount of each reply inspected or retained, prove deterministic preprocessing efficient, and compose the query/conditional rules.

**Result:** one machine and clock work for every input, state type, stateful handler and initial state, preserving the joint law of output and final oracle state. The certificate charges request construction and reply access; the external handler's computation remains external.

Next inspect behavior under a concrete handler. The same client defines `counting`, which increments a counter on every call. Its semantic examples establish final count one on the unselected branch and two on the selected branch. This catches interaction differences that equality of output marginals could hide. For the simpler `runWith` interface, open [ComplexityTests/OracleSemantics.lean](../../ComplexityTests/OracleSemantics.lean).

Use `adaptive_isOraclePPTOn.query_bounds` to obtain polynomial bounds on external call count and request length. A separately proved `IsCostBounded` charges chosen requests along every path; `ProbOracleComp.IsQueryBounded` counts external calls rather than private samples. Neither bound by itself pays for arbitrary Lean callbacks. For an average rather than a worst-case charge, [QueryCount/Expected.lean](../../Complexity/Languages/Probabilistic/QueryCount/Expected.lean) defines `OracleComp.expectedCost handler cost program`, the expected total cost when the calls are answered by PMF-valued `handler`. `expectedCost_bind` is Wald's identity for sequencing, `expectedCost_interpret` follows a handler substitution, and `expectedCost_le_of_isCostBounded` bounds the expectation by a pathwise `IsCostBounded` budget. The [local-decoding model](../circuits-logic-and-other-models/query-and-communication.md#locally-decodable-codes) measures smoothness this way.

**When it fails:** if `fun_prop` fails on returning an entire oracle reply, check whether the requested conclusion permits unbounded output. The linked client contains explicit failure examples and the bounded-prefix repair.

<!-- /worked-example -->

When replacing the external handler with an implementation, open [Oracle/Substitution.lean](../../Complexity/Computability/Probabilistic/Oracle/Substitution.lean). The plain-certificate variant `IsOraclePPTOn.run_interpret_preprocess_open'` requires efficient preparation, initialization and handling, plus an invariant and bounds on reply length and added encoded state. Its `hresources` premise also certifies a uniform unary computation of the resource allowance from the original caller and request; an abstract polynomial bound alone does not supply this certificate. Repeated state doubling explains why “each call is polynomial time” is insufficient.

## Derive adaptive decapsulation security

Import [`KEMFromPKE/CCA.lean`](../../Complexity/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean) when the starting assumption is `WordINDCCA2 keyGen encrypt decrypt`. Apply `WordINDCCA2.indistinguishable_encryptKeyEncaps` with the unary polynomial-time certificate for `keyLen`. It proves security of the actual `encryptKeyEncaps` constructor against adaptive postchallenge queries, with exact loss one. The [complete checked client](../../ComplexityTests/Crypto/KEMFromPKECCA.lean) uses `keyLen n = 2 * n` and keeps `n` as the security parameter.

For a runtime conclusion, use `isPPTOn_kemCCAGames_encryptKeyEncaps` with native key generation, encryption, decryption and adversary certificates. For correctness, apply `decrypt_encryptKeyEncaps_some` to a supported encapsulation and the original encryptor's supported-output correctness. These are separate contracts. The same test file checks a correct empty-key instance and distinguishes `none` from `some []`.

Check freshness against raw ciphertext words. The test's native `adaptiveTagDistinguisher` first observes rejection of the exact challenge, then flips a redundant tag and queries again. Because the malformed scheme ignores that tag, the distinct word reveals the key. Its exact advantage is `1 - 2^(-keyLen n)`; the comparison uses a bounded reply prefix, so its strict oracle runtime certificate holds even for arbitrarily long external replies.

For hybrid ciphertexts, use [`hybridDecrypt`](../../Complexity/Crypto/Computational/Encryption/Hybrid.lean)
with Option-valued decapsulation and symmetric decryption. It first checks that re-encoding
`(unframe ct, dropFrame ct)` gives exactly `ct`, then propagates either component's `none` result.
Apply `hybridDecrypt_hybridEncrypt` with component correctness returning `some k` and `some msg`;
`computableInPolyTime_hybridDecrypt` takes the corresponding certificates with `encOption` outputs.
The [hybrid clients](../../ComplexityTests/Crypto/HybridEncryption.lean) show why the framing check
matters: `[true, true]` and `[true, true, false]` have the same projections, but only the latter
is a canonical pair. They also check accepted empty plaintext (`[true]` as an oracle reply),
rejection (`[]`), and exact challenge-word rejection.

For the symmetric leg of CCA composition, import
[`Hybrid/DEMCCA.lean`](../../Complexity/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean).
`hybridDEMGame` uses the existing two-phase `cca2GameOn`: it retains the original joint KEM key
and encapsulation distribution, samples the hidden key from `E.keyGen n`, and redirects the
selected KEM component to that key in both phases. Challenge messages must each have length `n`.
`eval_hybridDEMGame` proves exact equality with the existing symmetric `ccaOneTimeGame`, and
`OneTimeINDCCA.indistinguishable_hybridDEMGame` supplies the loss-one security conclusion.
The native reduction certificate charges both adaptive phases and bounds every external reply read;
`isPPTOn_hybridDEMGame` also certifies the closed experiment.
For ciphertext reply bounds, `SymmetricCipher.exists_ciphertext_length_bound` returns a native
unary cap `ctBound n ℓ`, uniform over keys actually sampled by `E.keyGen n` and all messages
of length `ℓ`. Its runtime guarantee also covers messages outside the cipher's correctness
and security domain. The current `n`-bit reductions use its diagonal specialization
`SymmetricCipher.exists_ciphertext_length_bound_of_length_eq` (`ctBound n := bound n n`); this
bound does not extend their security claims to arbitrary words. The
[authenticated-encryption clients](../../ComplexityTests/Crypto/AuthenticatedEncryption.lean)
check independent lengths and show why an all-message bound cannot depend only on `n`.

The [checked clients](../../ComplexityTests/Crypto/HybridDEMCCA.lean) apply the result to the
existing PRF Encrypt-then-MAC cipher, expose an insecure echo cipher, and run a zero-width
prechallenge/challenge/postchallenge trace. They distinguish an empty encryption reply from an
encoded successful empty plaintext.

For the complete `n`-bit-message composition, import
[`Hybrid/CompositionCCA.lean`](../../Complexity/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
and apply `hybrid_indcca2On`. Supply the existing KEM CCA indistinguishability assumption,
`E.OneTimeINDCCA`, native algorithms, supported KEM correctness, and a native postprocessor
`F` satisfying `(uniformList (keyLen n)).map (F n) = eval (E.keyGen n)` for every `n`.
Postprocess every successful decapsulation with `Option.map (F n)` too. The conclusion uses
`INDCCA2On` with both challenge lengths equal to `n`, not unrestricted `WordINDCCA2`.
`exists_hybridCCA_reductions` returns native KEM and symmetric adversaries and the exact
`2 * KEM advantage + symmetric advantage` bound. Reply caps are derived from supported
secret-key lengths and the native decryptor; external replies need no assumed length bound.

The [complete composition clients](../../ComplexityTests/Crypto/HybridCompositionCCA.lean)
use `IsPPTOn.exists_total_seeded_evaluator` for arbitrary actual key generators and split `3*n`
uniform bits into the PRF Encrypt-then-MAC cipher's actual framed keys. Those keys have encoded
length `4*n+1` and are not uniform words of that length. For perfect correctness, apply
`hybridDecrypt_postprocessed_hybridEncrypt` with a supported-real-key premise: the total evaluator
provides it for every seed, while the simple split map needs real keys of length `3*n`.
The clients also distinguish failed decapsulation from accepted empty keys, detect omitted
postprocessing on forwarded replies, and exhibit a failed real hop without KEM correctness.

When the KEM instead derandomizes an explicit-coin public-key encryption scheme `encDet : PK → M → R → CT` with a mandatory re-encryption check (`T[PKE, G]`, `FO^⊥`, and domain-separated implicit-rejection `FO-notbot`), import [`FujisakiOkamoto.lean`](../../Complexity/Crypto/Protocols/KEM/FujisakiOkamoto.lean) rather than `KEMFromPKE.lean`. That module supplies `ExplicitCoinPKE` (`DeltaCorrect`, `GammaSpread`, `indCpaGame`) together with the deterministic recovery and re-encryption rigidity lemmas (`decT_encT_eq_some`, `encT_of_decT_eq_some`, `Scheme.decapsBot_encT_eq_some`, `Scheme.decapsBot_eq_none_of_reencrypt_ne`, `Scheme.decapsNotBot_encT_eq`, `Scheme.decapsNotBot_of_reencrypt_ne`; checked clients in [`ComplexityTests/Crypto/FujisakiOkamoto.lean`](../../ComplexityTests/Crypto/FujisakiOkamoto.lean)); random-oracle IND-CCA security games and reductions are not included in this module.

## Certify a list accumulator

Import `Complexity.Computability.Probabilistic.Fold` for
`IsPPTOn.foldlM_of_bounded_growth` and `IsOraclePPTOn.foldlM_of_bounded_growth`.
They certify ordinary `List.foldlM` with the accumulator as the step's first argument.
Supply plain polynomial-time certificates for the input list and initial accumulator, a joint
step certificate, and a constant bound on the encoded accumulator's growth at every supported
result. For an oracle fold that bound covers arbitrary external replies; truncate replies or
prove a suitable support bound before applying it.

The complete [ProbabilisticFold client](../../ComplexityTests/ProbabilisticFold.lean) checks a
noncommutative accumulator, an oracle fold's ordered calls and final external
counter, and an empty fold that makes no calls. From the configured repository root, run
`scripts/build.sh --wfail --iofail ComplexityTests.ProbabilisticFold`. The fallback argument
only totalizes the internal iteration step; it is never used on an empty list. If the growth
premise fails, check the output encoding and reply cap rather than assuming that efficient
individual steps make an arbitrarily growing accumulator efficient.

## Connect a randomized RAM loop to its answer law

Use this route when a randomized Word-RAM loop already exists and you want to derive its answer
distribution from an oracle specification. First choose the observed value, a supported-state
postcondition and explicit instruction and random-call budgets. Import
[Randomized/LoopSegmentLaw.lean](../../Complexity/Computability/WordRAM/Randomized/LoopSegmentLaw.lean).
`LoopSegmentLaw` retains the existing `LoopSegment` execution witness and bounds every supported
path. Its exact equality describes the chosen observation's PMF; its instruction budget is an
upper bound, not an assertion that every run takes the same time.
Random-call budgets use the existing [randomized RAM convention](../algorithms-and-memory/wordram-and-bridges.md),
which gives finite-interval sampling its own instruction and resource semantics.

From the repository root, open the complete
[WordRAMLoopSegmentLaw client](../../ComplexityTests/WordRAMLoopSegmentLaw.lean), including its
import, namespace and concrete starting state. Follow three steps:

1. Prove the body's `ExecRandLaw`, including its supported-state postcondition and budgets.
   `LoopSegmentLaw.single` requires the active guard and adds two instructions for loop control.
2. For several segments, use `LoopSegmentLaw.trans`. Supply the next law for **every** state
   satisfying the preceding postcondition; instruction and random-call budgets add.
3. Use `LoopSegmentLaw.finish` after proving the guard false on the entire final postcondition.
   It adds two instructions for the exit check and yields the existing `ExecRandLaw`.

The linked one-bit fixture sets a register to one and exits. Its budget is five instructions:
one body instruction, two control instructions and two exit instructions, with zero random calls.
From a configured checkout, check that client and the specification-law examples with:

```bash
scripts/build.sh --wfail --iofail ComplexityTests.WordRAMLoopSegmentLaw ComplexityTests.KargerFastCutLaw
```

A successful build checks the paid loop and the triangle, recursive seven-vertex and zero-cut
graph cases. If composition fails, compare the continuation law's observation and postcondition
with the preceding segment. If finishing fails, prove the exit condition for all supported
states. A query-count bound alone does not supply either instruction bound.

For the larger application, follow
[KargerFastCutLaw](../../ComplexityTests/KargerFastCutLaw.lean) into
[Lean/Karger/FastCut](../../Complexity/Algorithms/Lean/Karger/FastCut.lean), then
[KargerStein](../../Complexity/Algorithms/WordRAM/KargerStein.lean). The specification restarts
both recursive branches from the same parent graph and interprets their replies independently.
Its success statements concern a minimum-cut **value**, with the stated positive-minimum-cut
hypothesis; cut support also covers the zero-cut fixture. The native laws retain their word-fit,
frame and supported-path resource premises. To pass from a code observation to a halted cut
answer, [Karger/OutputLaw](../../Complexity/Algorithms/WordRAM/Karger/OutputLaw.lean)'s
`program_of_law` additionally requires fitting input words, cut support and allowance for the
final halt. This specification bridge leaves the memory-oracle contraction realization and
recursive frame-stack migration open.

## Use the bounded H4 hierarchy clients

For selected correction/pilot cutoffs, import
[HierarchyCutoffs](../../Complexity/Foundations/Probability/HierarchyCutoffs.lean).
Supply a `FourthRootHierarchyParams 16 1 16 32 8` witness and both ordered retention laws;
`correctionSampling` and `pilotSampling` derive the incoming count from the existing detector.
Their public projection equations let ordinary imports inspect recipe parameters without
unfolding opaque constructors. `correction_col_support` and `pilot_col_support` apply to
arbitrary raw, preparation and maximum children. The support margins use the actual Q/ρ gates.

For finite prime frame environments, start with
[HierarchyRankCutoffs](../../Complexity/Foundations/Probability/HierarchyRankCutoffs.lean)
and its [complete regression client](../../ComplexityTests/HierarchyCutoffs.lean).
The constructor examples use H=4, P=5 and horizon zero on a positive singleton matrix.
These constructors have two independent full-environment seeds. For the genuine mean of
one actual environment, import
[HierarchyCorrectionMean](../../Complexity/Foundations/Probability/HierarchyCorrectionMean.lean)
and follow its [complete regression client](../../ComplexityTests/HierarchyCorrectionMean.lean).
`terminalSplit` retains every spectator coordinate. Use `genuine_request_mean_usage` for
an independent usage grid rate, including narrower usage; the same-rate specialization is
`genuine_request_mean_density`. Both transport the source-conditioned average through the
split and derive source nonemptiness and the actual usage density. Supply a nonzero padding
multiplier, injective identifiers, an admissible request, a finite prime rank horizon, equal
true source/terminal stage rates, and a nonnegative substochastic matrix C bounded entrywise
by that rate. The usage exponent need not belong to the rank horizon: its box has positive
side at every finite exponent. The children are the existing raw input, its genuine joint
source/usage preparation and the final pilot maximum. The target remains the existing
correction iterate on the true split channels. `CorrectionSampling.withUsage` reuses all gates
and source/incoming laws, replacing only the measured usage marginal and terminal pair bound.

The P=5 client has different nonempty source and terminal copy suffixes and a genuine final
pilot proved zero from its detector rank. Its narrower-usage example fixes source/rank exponent
1 and uses usage exponent 2, with actual densities 81/625 and 16/625 and a strictly positive
complete request mean. Thus the usage change is observable in the actual environment.

For a sampling source narrower than the true stage, import
[HierarchySourceSampling](../../Complexity/Foundations/Probability/HierarchySourceSampling.lean)
and use `source_request_mean`; follow its
[complete regression client](../../ComplexityTests/HierarchySourceSampling.lean).
Supply source exponent `s`, stage exponent `k`, `k ≤ s`, and a horizon containing `s`.
The true `stageSource` retains the source role and suffix at the terminal stage rate.
`stageRaw` and `stageMaximum` use these genuine stage channels. `sourcePreparation`
uses the actual sampling source for its incoming gate. `source_normalizer` identifies its
joint actual source/usage mean on the same environment, and `stage_atomCutoff_eq`
preserves the true cutoff. `CorrectionSampling.withSource` changes only the sampling-source
pair law, preserving the true input, final pilot, gates and incoming budget. The common
`correctionRequest_eq_split` avoids rebuilding the split transport for each choice of children.

To compare genuine targets across request roles and copy suffixes, import
[HierarchyCanonicalTargets](../../Complexity/Foundations/Probability/HierarchyCanonicalTargets.lean).
Use `stage_correctionIter_eq_of_terminal_rate` to identify the left and negative correction
targets at a common stage rate. `source_request_mean_canonical` combines this transport with
the actual narrower-source correction mean, retaining its literal usage-density divisor.
The proof integrates source spectators and permutes each padded frame seed; it does not
identify samples at an unchanged environment. The
[regression client](../../ComplexityTests/HierarchyCanonicalTargets.lean) checks actual residual
requests with different terminal roles and radix-two suffixes, a positive target and an
unequal-rate complete correction mean.

For a genuine source-reset dense child, import
[HierarchyDenseChildren](../../Complexity/Foundations/Probability/HierarchyDenseChildren.lean).
Build `denseChild` from the deterministic hierarchy base, bin cutoff and genuine
`densePreparation`. `dense_normalizer` integrates the actual joint source/usage mean;
`denseChild_terminal` then removes source and spectator dependence pointwise. For a
left correction sharing the midpoint with that reset source, use
[HierarchySharedMidpoint](../../Complexity/Foundations/Probability/HierarchySharedMidpoint.lean).
`sourceChild_mul_denseChild_mean` conditions the single full environment on the old
source and terminal events. Supply three distinct roles, the complete right-source reset,
the finite horizon and narrower-source hypotheses, and the dense support/gate bounds.
The left midpoint hit and literal midpoint-density divisor remain in the sample.
The [checked client](../../ComplexityTests/HierarchySharedMidpoint.lean) evaluates a positive
product with unequal rates, nonempty suffixes and a free fourth role.

For signed assembly import
[HierarchySignedMean](../../Complexity/Foundations/Probability/HierarchySignedMean.lean).
`canonicalRequestChild` matches normalized index j and evaluates `sourceChild` at j.val;
`correctionAtomTask_last_succ` proves the final structural dispatch. Request size stays
`HP.k` as statistical precision varies. `sourceChild_mean_on_terminal_event` derives the
negative mean from genuine correction normalization and zero off usage, with no target-mean
premise. The actual negative request has rank rate f and usage min(parent terminal, f).
`canonical_rawSample_mean` proves the literal one-bin mean `C_bin + E*C_bin - E` on
one full environment. `canonical_residual_bins_mean` sums `rawPositiveSample` over the
existing routed-bin partition with route one, then subtracts `rawNegativeSample` once.
Its exact finite cover and narrower-source horizon are explicit; summing unchanged signed
rawSample bins would subtract E repeatedly. The
[checked signed client](../../ComplexityTests/HierarchySignedMean.lean) keeps nonempty
suffixes, unequal rates and a free spectator, checks two statistical walk precisions,
positive genuine final correction/product terms, a nonconstant product and two-bin assembly.

For finite absolute estimated-child propagation import
[HierarchyEstimatedMean](../../Complexity/Foundations/Probability/HierarchyEstimatedMean.lean).
`estimated_residual_bins_mean_error` compares actual bounded `incomingChildren` at fixed
`Request HP.k` with `canonicalRequestChild`. Supply the genuine C/top-rate cap, monotone
bin scales with adjacent ratio at most 16, and the same cover/horizon and dense-gate contracts.
`boundedRoutedBinCutoff_div_eq` proves true-input agreement before the bounded evaluator is
used. The product splits as estimatedLeft*(estimatedRight-canonicalRight) +
(estimatedLeft-canonicalLeft)*canonicalRight. Actual correction range `2*Q(atomCap)` and
genuine dense range `2*max cap 16` pay the two errors. Importance and midpoint densities
stay literal; positive-bin errors are summed and the negative error occurs once.
The [checked error client](../../ComplexityTests/HierarchyChildError.lean) instantiates the
actual two-bin cap and exact adjacent ratio on the shared spectator/suffix fixture.

[FirstMeanError](../../Complexity/Foundations/Probability/NormalizedAtomRows/FirstMeanError.lean)
then proves `actualEstimatedResidual_first_mean_le`: the completed full-terminal raw walk
preserves this input mean and the actual first prefix has bound
`min 1 (absoluteError / (rate kt + genuineResidual x y))`. The genuine residual is nonnegative.
This direction does not convert clipped relative error into absolute error. Preparation still
uses the full-rank maximum in `preparationError`. Recursive root/relative budgets, copy-stage
routing, numerical reserves, parameter/workspace bounds and native RL=L remain open.

The P=5 regression has source/stage/usage exponents 2/1/3, actual densities
16/625, 81/625 and 1/625, different nonempty copy suffixes, and a free spectator role.
It proves a positive complete actual request mean with the genuine final pilot. Usage
exponent 3 is outside the required source/stage horizon 2.

To discharge the raw input fourth moment for a positive-iteration residual, import
[HierarchyRawMoment](../../Complexity/Foundations/Probability/HierarchyRawMoment.lean)
and apply `rawIncomingNormalized_noise_le_lower`. Supply positive N, u, row rank K and
incoming rank Kc. The selected cutoff laws derive the actual left correction child's
range `CA = 2 * Q(atomCap)`, row support K and incoming support Kc, for arbitrary raw,
preparatory and pilot children. Its source-released product costs
`K^3 * CA^4 * Kc * (rate(km) / u)` times the weighted right-child fourth moment.
`incomingMomentBudget` adds the actual weighted direct and negative child moments, with
a conservative factor 64 for the signed sum. The right child includes the exact usage
ratio and midpoint marginal divisor from `rawSample`; it never takes the old source as
an extra argument. All children may share every rank coordinate.

The [checked examples](../../ComplexityTests/HierarchyRawMoment.lean) include a complete
P=5 residual with input moment one and positive correction product, different nonempty
copy suffixes and a spectator. A correlated two-factor example has exact moment 257/2.
An identity family with one nonzero per row and column has moment n at N=u=1, so support
and range caps alone do not imply a width-independent unnormalized moment. The new client
requires lower-child moments to be paid by a later induction; it assumes no final raw or
noise certificate. Zero correction remains literal; the moment/noise bridge here treats
positive iterations. Pilot/copy paths, quantitative lower-child budgets, summation and
recursive/native correctness remain open.

For the first compression signal, import
[FirstSignal](../../Complexity/Foundations/Probability/NormalizedAtomRows/FirstSignal.lean)
and apply `actualFirstSignal_noise_le_lower`. Its precision-indexed inputs are genuine
`rawIncomingNormalized` samples on one fixed positive structural `Request q`.
For a genuine hierarchy use `q = HP.k` and `HP.k_pos`; precision j changes child
estimates and walk lengths, not the request type or final correction index. `firstSignalIncrement` takes successive conditional-walk
differences from zero; `actualPrefix_firstSignalIncrement` identifies prefix i with walk
i+1 divided by `rate k`. Stationarity on the full terminal slice, including empty slices,
then identifies `actualNoiseEntry` with centered walk noise divided by
`rate k * (1 + G / rate k)`.

The endpoint row moment is bounded directly by `rate k` to the inverse fourth power,
times `32 * lambda^(2*steps(i+1))`, times the explicit lower-child
`incomingMomentBudget` at budget i+1. No maximum-entry conversion, hidden width constant,
or independence assumption is used. The
[regressions](../../ComplexityTests/ActualFirstSignal.lean) check nonzero nonconstant
telescoping prefixes, zero inputs, empty slices and a nonconstant random mean/moment.
For a numerical payment, import
[FirstPayment](../../Complexity/Foundations/Probability/NormalizedAtomRows/FirstPayment.lean).
Supply CB≥0 and a proved [0,CB] range for the actual bin cutoff.
`normalizedRequest_mem_Icc` gives direct/right range 2CB; correction range remains
CA=2Q(atomCap). `incomingMomentBudget_le_payment` pays all three child norms on the
same full environment. For N=P and u=rate(ks), with ks and km in the declared horizon,
each bounded row pays at most 16P times its fourth-power bound. This deliberately retains
the full endpoint width P; it does not infer sparse support for an arbitrary bounded cutoff.
The correction product still uses its existing proved K/Kc support bounds.

`firstSignalPayment` evaluates both actual usage ratios as exact grid frame-mass ratios,
with usage exponent max(k,kb) or max(k,km). The right factor keeps rate(km) divided by
its actual midpoint density. The resulting finite payment retains P, the rounded frame
masses, and rate(km)/rate(ks); none is hidden in a universal constant.
`actualFirstSignal_noise_le_payment` keeps rate(k)^(-4), and
`actualFirstSignal_noise_le_dyadic` uses the shared `spectralWalkLength` at child budget i+1
to pay the dyadic fourth-power noise contract for ε>0. The
[actual-bin regressions](../../ComplexityTests/ActualFirstPayment.lean) use
`boundedRoutedBinCutoff` with a genuine polynomial switch, top cap HP.k+2, adjacent-scale
ratio 16 and explicit CB=max(HP.k+2,16). They check a nonzero complete residual, negative-input
clipping, a chosen actual i=2 noise client, exact logarithmic steps and zero/empty edges.

For the preparatory second signal, import
[SecondSignal](../../Complexity/Foundations/Probability/NormalizedAtomRows/SecondSignal.lean).
`selectedPreparation` applies the selected preparation cutoff and full terminal-rank
gate to a supplied **completed raw child in matrix units**. `completedRawChild` names the
actual conditional H4 walk of `rawIncomingNormalized` used by FirstSignal and FirstPayment.
Apply preparation after this raw walk, then average preparation on source × usage.
`hierarchyTaskRecipe_residualPreparation` checks the existing hierarchy evaluator reads
that completed child before the nonlinear recipe. All source, midpoint, terminal, usage
and copy data remain on the same environment. `rawSamplePreparation` is the optional
unaveraged finite client; it does not identify the recursive preparation evaluator. `actualSelectedSecondSignal_noise` bounds
its endpoint row noise by `ζ^4 * 32 * lambda^(2*steps(i+1)) * rowNormPow(T_(i+1))`
on source × usage. Stationarity identifies the actual second noise with
`|ζ| * |walk_(i+1) - rowSliceMean(T_(i+1))|`. The initial second signal is literally zero,
and `firstSignalIncrement` retains its existing full-rank first prefix.

The preparation is in [0,1] and has fewer than K nonzero retained rank entries per row.
For usage exponent kt≥k, `selectedPreparation_support_moment` applies the generic
sparse-row bound **before walk averaging**. Its payment is
`K * (N*u)^(-1) * sum_x density(sourceRetains x)`, without independence of the input,
support or source. `source_density_sum` evaluates the sum as `P * (side(P,ks)/P)^4`,
including nonempty copy suffixes and D=0. With N=P, u=rate(ks), and ks in the declared
horizon, `selectedPreparation_moment_le` gives 16K. No sparsity of the averaged
walk is claimed.

`actualSelectedSecondSignal_noise_le` feeds that input payment into the actual second
prefix: its noise moment is at most `ζ^4 * 32 * lambda^(2*steps(i+1)) * 16K`.
For ε>0, the shared `spectralWalkLength` takes lambda and coefficient ζ^4*512K
and gives an explicit natural ceiling of a base-lambda logarithm;
`actualSelectedSecondSignal_noise_le_dyadic` accepts this length or any larger one and
pays `(ε * 64^(-dyadicSlack(m,i)))^4`. The length uses input budget i+1. The extra 1 in
its logarithm denominator also handles zero scaling and capacity. ε=0 is excluded from
this finite-length guarantee: a positive spectral upper bound never vanishes in finitely
many steps.

The [regressions](../../ComplexityTests/ActualSecondSignal.lean) check positive, nonconstant
selected preparation, the actual H4 second-prefix client with the
chosen steps, D=0 with a nonempty suffix, two-signal prefixes, zero children, and empty
usage through compression. Mixing controls noise around the selected input's own mean.

For deterministic preparation bias, import
[MeanBias](../../Complexity/Foundations/Probability/NormalizedAtomRows/MeanBias.lean).
`preparation_stability_constants` uses polynomial entry-cutoff regularity and the actual
hierarchy rho fourth-root regularity. `preparation_sub_genuinePrep_le` compares signed
residual A to G on the same full terminal rank slice: its bound is
`(Lh * |A σ x y - G x y| + Lρ * rank₁(fullRank, |A σ x · - G x ·|)) / rate k`.
`preparationError_le` accepts explicit absolute entry and full-rank envelopes; it needs
no target-size bound. `preparation_mean_bias_le` averages this error over the actual joint
source × usage slice against `genuinePrep(G)` and `genuineMean`, including empty slices.
`actualSelectedSecondSignal_mean_bias_le` accepts any completed raw child.
`actualCompletedSecondSignal_mean_bias_le` keeps that same structural q at every precision
and instantiates it with the actual raw H4 walk
and the ζ-scaled preparation prefix at input budget i+1. `firstSignal_raw_error` and
`preparationError_eq_firstPrefix` identify its absolute errors with the actual first-prefix
errors, retaining rate(k) and the full-rank maximum. The first prefix is F_j/rate(k);
`atomPrep` itself divides by rate(k), so preparing that prefix directly would divide twice. The clipped
second deterministic discrepancy is at most `min 1 (|ζ| * jointMean(preparationError))`.
All source/copy suffixes, rates, role data and correlations remain present. The first
coordinate is unchanged. The regressions evaluate a positive nonconstant genuine target,
a perturbed-residual bias of one, exact-zero perturbation and empty usage. The ordering
regression has raw values 0 and 2: preparation of their average is 1, while the average
of their preparations is 1/2. A seven-step actual H4 completed child retains a positive
preparation and a zero endpoint.

For quantitative second deterministic envelopes, import
[SecondEnvelope](../../Complexity/Foundations/Probability/NormalizedAtomRows/SecondEnvelope.lean).
`secondMeanEnvelope` is the actual B1: `min 1 (|ζ| * jointMean(preparationError))`.
`actualSelectedSecondSignal_mean_le_envelope` and
`actualCompletedSecondSignal_mean_le_envelope` bound the actual clipped second mean by B1.
For usage contained in full terminal rank, `secondMeanEnvelope_moment` pays its fourth row
moment by `P * (|ζ| * (Lh + Lρ) / rate k)^4` times the completed raw absolute error moment.
Conditional Jensen cancels the joint densities; repeating the full-rank maximum over usage
endpoints costs the visible width P. No independence or target-size cap is used.

`actualCompletedRaw_absolute_moment_le_payment` splits `A-G = (A-μ)+(μ-G)` at the actual
full-rank input mean μ, paying `8 * (32 * λ^(2*steps) * firstSignalPayment + ROW(error))`.
The centered noise is in RAW matrix units; relative `actualNoiseEntry` cannot be substituted
without restoring its rate and target factors. `actualCompletedSecondSignal_envelope_payment`
then pays B1 with the same explicit width and inverse rate. Its mean-error hypothesis is
absolute, before clipping. For actual finite bins,
`actualEstimatedResidual_second_envelope_moment` discharges that mean-error step with
`estimated_residual_bins_mean_error`: positive costs sum and the negative cost is charged once.
The shared [estimated input](../../Complexity/Foundations/Probability/HierarchyEstimatedInput.lean)
names exactly that positive-bin sum minus one negative request, with fixed `Request HP.k`
and independent precision. Its pointwise range uses the actual left support at most K,
zero extension off midpoint usage, and dense ranges `2 * CB_i`: the product costs
`K * CA * 2 * CB_i`, rather than ambient width P. Here `CA = 2 * Q(atomCap)`,
`CB_0 = cap` and `CB_i = 16` for fine bounded routed bins. The finite scale sum retains
all rates, exact rounded-grid importance ratios and the midpoint marginal divisor.
`estimatedResidualInput_moment_le` pays `16 * P * bound^4` at `N=P, u=rate ks`;
the second-envelope client uses this payment without a retained raw-input-moment premise.
The canonical residual remains at km, with full rank and normalization at kt, finite
coverage, narrower-source horizon, all suffixes and one shared environment.

`actualEstimatedFirstSignal_noise_le_dyadic` pays actual first-prefix row noise using the
same input and the inverse parent-rate fourth power. For scaled centered RAW noise,
`estimatedResidualInput_scaled_noise_le_dyadic` feeds `spectralWalkLength` the coefficient
`amplification * 32 * 16 * P * bound^4`. For B1 the amplification is
`P * (|ζ| * (Lh + Lρ) / rate kt)^4`; this retains RAW matrix units.
Positive tolerance is required. The [finite input tests](../../ComplexityTests/HierarchyEstimatedInput.lean)
include a positive nonconstant two-bin input, exact once-negative arithmetic, independent
precisions, separate top/fine caps, support versus width, chosen amplified steps and zero/empty edges.
The [regressions](../../ComplexityTests/SecondEnvelope.lean) check a positive nonconstant
spectator raw child and B1, exact-zero/empty edges, actual clipped-mean comparison and an exact
two-endpoint counterexample to dropping width.

[ReserveOutput](../../Complexity/Foundations/Probability/NormalizedAtomRows/ReserveOutput.lean)
assembles the actual finite output from explicit lower-child conditional-error-cost fourth
moments. `actualEstimatedResidual_output_from_cost_reserves` derives common deterministic B
matrices by finite maxima of the actual first/B1 envelopes divided by `2^dyadicSlack`.
The first payment uses absolute mean error over `rate kt + G`; the second retains
`A = P * (|ζ| * (Lh + Lρ) / rate kt)^4`. At horizon m its uniform child-cost reserve is
`tolerance^4 / (1 + rate kt^(-4) + A)`, where `tolerance = ε / (2 * (m + 1))`.
This finite allocation pays both common-B moments without claiming growth independent of m.
RAW steps are the maximum of the actual first-noise requirement and the fully amplified
`(1 + A)` RAW requirement. Preparation steps use the existing 16K payment. The target is
`genuineNormalizedRecipe` at the canonical residual, identified with `normalizedRequest`
by `genuineNormalizedRecipe_eq_request`; capacities are actually `(K+1)*2^(64*slack)`.
The theorem derives nonnegativity, row mass and zero extension, with finite cover,
narrower-source horizon, gate/cutoff/cap and routing agreements still explicit.
The [new regressions](../../ComplexityTests/ReserveOutput.lean) evaluate a positive,
nonconstant full-matrix input with a free spectator, show the once-negative arithmetic,
compute nonzero common B and check the actual completed prefix at index zero.
The bounded fixture does not assert the canonical routed-bin mean or recursive reserves.
A separate actual lower-child conditional-cost client proves that the finite reserve is
satisfiable at some positive tolerance; it does not claim that tolerance is small.

[ChildRootReserve](../../Complexity/Foundations/Probability/NormalizedAtomRows/ChildRootReserve.lean)
now pays that cost reserve from actual normalized lower-child rooted moments.
[RootReserveOutput](../../Complexity/Foundations/Probability/NormalizedAtomRows/RootReserveOutput.lean)
reuses the same output assembly. Its target is still the genuine canonical residual.
The cost API retains only the union of actual estimated/canonical left supports. Both left
children vanish off midpoint usage, so right errors are charged only at their reset source z.
Left errors use the old source and midpoint terminal. Each lower budget uses its own full
terminal rank; min-rate usage is proved to lie in that rank, with every suffix unchanged.

The sufficient allocation is deliberately conservative. Put `CA = 2 Q(atomCap)`,
`CB = 2 max(cap,16)`, `B = max(CA,CB)` and let `A` be `residualCostCoefficient`.
Its literal formula is `8 ((n+1)^4 sum_i 8 (D_i + 8 P^4 (CA^4+CB^4) T_i) + N)`,
where `D_i`, `T_i`, and `N` are endpoint sums of the fourth powers of the direct,
importance-times-midpoint, and once-negative coefficients. Their rounded grid densities
remain literal. Set `scale = P^2 / (P rate ks) * A` and
`delta = tolerance^4 / (1 + rate kt^(-4) + amplification)`.
For each called request r, a rooted row moment at most
`delta / (1+scale) / (1 + (4 B^(3/4))^4 P r.source.rate) / (1 + #calls)`
pays the desired reserve, where `calls = residualErrorCalls` contains the direct/left/right
requests per positive bin and the special negative request once. In particular
`#calls ≤ 3(n+1)+1`; it counts requests, not environment atoms. The proof keeps a sum
of child ordinary errors on their own source/usage domains for each environment, applies
conditional Jensen to the actual cost, and swaps finite sums with expectation. Bounded
root-to-ordinary conversion then pays each integrated child moment. Repeating this sum
over parent pairs costs the explicit `P²`; child source normalization costs `P r.source.rate`.
There is no environment-cardinality or inverse minimum-atom-probability factor, and no
independence assumption on children. Exact midpoint density and importance factors remain
in `A`. This finite transport does not establish useful recursive parameter growth.
The ordinary-error conversion applies only to bounded normalized estimated and canonical
outputs, never to the signed raw target divided by a rate. The
[domain regressions](../../ComplexityTests/ChildRootReserve.lean) check an off-source error
ignored by the actual product, full-rank masks, two-bin/once-negative coefficients,
canonical-zero and positive nonconstant normalized outputs. A sparse, mask-sensitive
normalized-child regression also checks an integrated budget that permits a unit error at
a retained atom; the corresponding per-atom allowance would be strictly less than one.

Deriving small numerical errors from recursive lower-child relative estimates, numerical
reserves, recursive budget induction, copy routing, parameter/workspace bounds and native RL=L
remain open. Row mass does not provide a uniform target bound, and clipped relative error
alone does not provide an absolute residual error.

For a coarser source, `source_incoming_cost_le` quantifies the generic incoming cost as
`32 * R * (sourceRate / stageRate)`; the fixed incoming rank is not proved to pay that
inflated budget. Arbitrary coarser sampling sources, a fully assembled recursive hierarchy,
lower-child budget induction, native realization and RL=L remain in
[issue #1721](https://github.com/cslib-community/complexitylib/issues/1721).

## Extract an emitted pseudorandom prefix

Import [Stretch/Prefix.lean](../../Complexity/Crypto/Computational/Stretch/Prefix.lean).
Use `PRGStretch.length_take_forwardIterate` and `take_forwardIterate_prefix` with the global
one-bit length promise. The latter compares `ℓ ≤ L` rounds only after discarding the final
seed: take `ℓ` bits from either run. Do not apply it to the complete retained-seed output.

`polyTime_take_forwardIterate` certifies the map from a complete seed and unary round count
to the emitted prefix. Compose its round count with the plaintext length to obtain a native
XOR pad computation; the [checked PRGStretch client](../../ComplexityTests/PRGStretch.lean)
proves actual encryption/recovery and distinguishes emission order from its reversal.
For security, apply `indistinguishable_take_forwardIterate` to the existing one-bit
`PseudorandomGenerator` assumption and a native unary length schedule `L`. The seed law stays
`uniformList n`; the output law is compared with `uniformList (L n)`. This covers `L n = 0`
and seed width zero, but does not yet supply adaptive-message cipher security.

## Carry the certificate into a security proof

Keep efficiency and security as separate goals. In [Crypto/Computational/Basic.lean](../../Complexity/Crypto/Computational/Basic.lean), computational indistinguishability quantifies over certified strict-PPT distinguishers. It does not require the compared PMF ensembles to be efficiently sampleable or polynomially bounded in length. Check those properties separately when the intended construction needs them.

Specify the experiment, admissible adversaries, success event and assumption; prove the reduction's efficiency using the routines above; then prove the probability or advantage inequality. Semantic rewrites and native certificates discharge different obligations. If a proposed reduction only has a query bound, return to the realization step before calling it a computational security reduction. Use the [security-game reference](../programs-crypto-and-probability/security-games-and-primitives.md) to choose the correct primitive and adversary model.

[complexitylib]: ../sources.md#complexitylib
[holenstein09]: ../sources.md#holenstein09

The two reserve-output theorems choose their output constant after the fixed hierarchy,
ζ, scale and positive floor, before the prime, environment width, horizon, prefix length
and raw/preparation/maximum families. Select this constant before allocating recursive
child accuracies. Uniformity of that coefficient does not remove any displayed finite
allocation or walk-length losses and supplies no recursive accuracy theorem.

[HierarchyCorrectionStability](../../Complexity/Foundations/Probability/HierarchyCorrectionStability.lean)
factors the actual correction request into its unit-pilot coefficient and `γ(maximum y)`.
The coefficient lies in `[0, 2 Q(atomCap)]`, even for signed raw/preparation estimates.
If `Lγ` is the hierarchy's fourth-root Lipschitz constant for γ, the fourth-root output
change is at most `(2 Q(atomCap))^(1/4) Lγ |maximum y - maximum' y|`. The integrated theorem
keeps both children on the same full environment and the original source/full-terminal
masks; its loss is `((2 Q(atomCap))^(1/4) Lγ)^4`. It does not silently transport a vertex
error to a different source or remove any width/rate coefficient from that transport.

For all three changing child classes, use
[HierarchyCorrectionRawStability](../../Complexity/Foundations/Probability/HierarchyCorrectionRawStability.lean).
Its selected preparation theorem and normalized recipe bound retain the actual HP row
and pilot gates, auxiliary incoming scores, both ranks, and signed unbounded raw entries.
The bounded atom cutoff and denominator root regularity control outputs globally; no
raw target cap is assumed. Preparation errors pass through the actual same-environment
joint source/usage mean, followed by `max (1/2) (min 1 mean)`.

The pointwise actual-request theorem keeps the entry, full terminal-row, source-column
and full source×terminal maxima. Its integrated contract retains the original source and
full terminal masks: RAW absolute row error costs `64 (Cr / terminalRate)^4 width^2`,
PREP source/usage row error costs `64 Cp^4`, and ordinary maximum error on the same
source/full-terminal pairs costs `64 Cm^4`. The three constants depend only on HP.
Usage inclusion in rank and zero extension allow conditional Jensen on PREP without
charging full-environment atom costs. Every child can depend on the same full environment.
The [regressions](../../ComplexityTests/HierarchyCorrectionRawStability.lean) include nonzero
separate/joint perturbations and row/incoming rank sensitivity; the dyadic maximum
regression above remains in place.

For the actual pilot score, detector and running maximum recipes, use
[PilotRowStability](../../Complexity/Foundations/Probability/PilotRowStability.lean).
The score contract keeps the signed raw inputs in the original K-rank and pays ordinary
fourth-moment row error with `width * ((Lϕ + Lρ) / rate)^4`. Its constants come from the
fixed HP cutoffs before domains, rates or child tables. The detector first takes its actual
source mean and terminal-conditioned mean: Jensen pays the source-rank maximum by the
sum of fourth powers on that same finite source slice. The literal-payment theorem retains those means and the finite source sum.
[PilotDetectorTransport](../../Complexity/Foundations/Probability/PilotDetectorTransport.lean)
reinserts the terminal conditioning by finite Fubini: its integrated score payment is
`width * childSourceRate / (parentSourceRate * terminalDensityLowerBound)` times the
child row moment. All outer coordinates and both actual integration variables remain in
that moment. A positive terminal-density lower bound is explicit; empty conditioning
still gives zero in the underlying detector contract.
The clipped running maximum pays the sum of its previous-maximum and current-detector
fourth moments, on the original pair masks.

[HierarchyPilotStability](../../Complexity/Foundations/Probability/HierarchyPilotStability.lean)
also transports this payment through `terminalSplit` to actual full H4 rank environments.
The child source resets to the terminal stage rate with its role and suffix unchanged;
the terminal frame keeps its own role and suffix. Composing with the actual score contract
pays raw errors with an additional `width * (C / terminalRate)^4`, where `C` is selected
at fixed HP before the prime, request or children. The score can depend on every outer
coordinate and its terminal frame. This is the literal detector recipe, whose score argument
has no dependence on the internally averaged source seed. No independent recursive child
realization is inferred from the product used by finite Fubini. The same module
provides `correctionRequest_stageDetector_root_moment`, combining the transported current
score/detector payment, previous maximum, and changing RAW/PREP correction children, retaining
its RAW width²/rate⁴ and PREP source/usage payments. It requires no assumed final-maximum
error. The [checked pilot client](../../ComplexityTests/PilotRowStability.lean) changes the raw
K-rank from zero to the gate cutoff while fixing the inspected entry, and checks changes to
the actual score, detector and maximum, a correlated nonzero moment, and empty/zero cases.
The shared [rank API](../../Complexity/Foundations/Data/Finset/KthLargest/Stability.lean)
also removes repeated normalization proofs in dense and correction preparation.

For a computed initial-pilot fragment, use
[InitialPilotScore](../../Complexity/Foundations/Probability/InitialPilotScore.lean).
It evaluates the dense bin from the stage-zero base matrix and its actual preparation,
uses the literal zero correction of the first pilot input, walks that RAW sample on
all H4 coordinates, and passes the completed matrix to the actual score recipe on the
same environment. Both requests strictly decrease the existing constructor rank;
statistical accuracy does not change `HP.k`.

The fixed-HP score constant is chosen before the prime, roles, rates or base matrix.
The finite budget is `width * (L / terminalRate)^4 * 32 * inputFourthMoment`, where the
input moment is the literal finite sum of the computed dense sample. The step count is
`max 1 (spectralWalkLength gap budget tolerance 0)`, so positive tolerance gives an actual
positive-length call even at zero budget. This is a mathematical finite allocation,
not a certified efficient procedure for choosing the budget or executing the walk.
The general payment targets the score of the bin's conditional mean. At equal parent/bin
terminal rates, dense normalization proves that mean is the matrix-unit bin. For a
nonnegative substochastic base covered by a single bin,
`initialPilotScore_allocated_of_single_bin` therefore bounds error against the actual
initial score of that base without a supplied child-error or desired-mean certificate.

The [computed regression](../../ComplexityTests/InitialPilotScore.lean) uses a bounded routed
top bin with a smooth scalar switch, the identity base over `ZMod 5`, source exponent one,
full terminal rate, distinct roles and nonempty suffixes. Its computed lower RAW walk and
upper score are both one or both zero according to the same original source frame, at
positive allocated lengths. The two environments agree on every other role, including
the terminal frame. This is a nonconstant correlated exact-on-slice case; it does
not establish nonzero mixing error or later recursive closure.

The [source-aware detector](../../Complexity/Foundations/Probability/InitialPilotDetector.lean)
now consumes that completed score through the literal source/terminal split. The score request
resets the source rate to the terminal stage rate while preserving roles and suffixes.
`environmentDetector` reconstructs the child environment from all source spectators and the
terminal frame; these are integration variables, not fresh independent seeds for child calls.
Conditional Jensen and finite Fubini pay the score moment by
`width * stageRate / (parentSourceRate * terminalDensity)`. The actual padded terminal marginal
is proved separately. The old terminal-only detector and transport theorems specialize the
shared proof when their child ignores the source argument.

`initialPilotDetector_allocated` composes that payment with the actual dense RAW allocation
and score theorem, under the same nonnegative substochastic, equal-rate, covering single-bin
hypotheses. `initialPilotDetector_accuracy` calibrates the lower tolerance before either call
to obtain detector error at most `ε^4`. The reference is proved equal to the original canonical
column detector, retaining its cutoffs and rank. The constant is fixed at HP before field,
request or children. Allocation uses the finite computed input moment; no efficient allocation
procedure is claimed.

The regression proves that no terminal-only function represents the actual allocated score.
A two-environment source-aware kernel evaluates that score to `1/2` using replicated rank
entries; this tests the new argument dependence, not an injective hierarchy instance.
The full-frame initial detector has a checked concrete payment `80 * ε^4`. The small-field
RAW/score fixture remains exact on retained slices and does not show nonzero finite-walk
mixing error. In particular, a large padded detector rank can erase its score variation.

The [first positive direct pilot constructor](../../Complexity/Foundations/Probability/InitialPilotCorrection.lean)
now consumes the actual completed RAW table and the initial clipped maximum of zero and that
source-aware detector. Its fixed-HP root constants precede the field and requests. The RAW
length uses the computed dense input moment; the detector uses the existing source-aware
allocation. Both positive tolerances are calibrated before the calls, and the resulting direct
constructor has root error at most `ε^4` under the same covering-single-bin and finite-horizon
hypotheses. On nonnegative inputs bounded by the stage rate, its reference is the canonical
first `pilotCorrection`, with the original Q, rate and gamma multiplier.

The direct constructor in `hierarchyTaskEval` differs from the stochastic normalized child.
The latter is also constructed here: preparation is recomputed from the completed RAW table,
then averaged by the actual conditional H4 walk. `initialPilotNormalized` consumes that walk,
the unmodified RAW ranks and the completed maximum through the original source/usage
normalizer. Same-slice stationarity proves that the preparatory walk preserves this
literal normalizer exactly; pointwise PREP need not converge to pointwise true preparation.
The decoder's reusable stability API therefore accepts the normalizer difference directly.
The former pointwise PREP moment estimate is retained as an optional coarse bound, not the
allocation route.

The actual pre-walk incoming preparation responds to RAW perturbations through the original
row, incoming-column and source-by-terminal ranks. Conditional Jensen and the full rectangle
maximum pay this response with explicit width squared and inverse terminal-rate fourth power,
without an environment-cardinality or atom penalty. `initialPilotNormalized_accuracy` chooses
RAW and detector tolerances before either call, uses preparation parameter one (two graph steps),
and proves root error at most `ε^4` against the original true normalized request. It retains
the original clipped denominator and actual source-aware detector/maximum. HP.k stays fixed;
constants precede fields, requests and child tables. The same covering single-bin, equal-rate,
finite-horizon and dense-mean hypotheses remain explicit. No true-PREP oracle is used.

The [completed stochastic first pilot correction](../../Complexity/Foundations/Probability/InitialPilotCompleted.lean)
now averages that actual normalized child on the original source/usage H4 slice.
`initialTrueNormalized_mean` specializes the existing pilot sampling law through the
literal terminal split, deriving incoming margins from the canonical detector and frame
channels. Its target is the genuine first `pilotCorrection`, not a clipped replacement.
This specialization requires **common source, terminal-rank and usage rates** `f = rate k`,
nonnegative substochastic `C` with entries at most `f`, a finite horizon, nonzero padding,
and the fixed injective identifier `id`, with the original copy suffixes. On the joint retained slice,
the matrix-unit importance factor is **`f`**: `f * mean(trueNormalized) = pilotCorrection 1`.
The source-only convention instead uses `f / π_usage`; applying that factor to an already
usage-conditioned mean would introduce an erroneous inverse density.

`initialPilotCompleted` performs the outer walk of the computed normalized child, then
multiplies by `f`. It keeps all original source, usage and terminal masks and varies the
full shared environment. Centered walk noise and mean bias are paid separately. The
normalized range is `B = 2 * HP.Q HP.atomCap`, giving the explicit input-moment bound
`P^2 / (P * rate ks) * B^4`. Conditional Jensen and root-to-ordinary error conversion pay
the mean bias by `Kroot * rootDistPow`, where `Kroot = (4 * B^(3/4))^4`. Neither payment
extracts environment atoms or supplies the desired mean/error as a hypothesis.

`initialPilotCompleted_accuracy` proves **ordinary fourth-moment error at most `ε^4` in
parent matrix units** under the common-rate and covering-dense-single-bin hypotheses.
It fixes `payment = 8 * f^4 * (1 + Kroot)` and positive `δ = ε / (1 + payment)`, then chooses
the positive outer length from the known range, before completing lower calls. The existing
normalized allocator then fixes positive RAW/detector tolerances before their calls;
preparation uses parameter one. Its regularity constants are selected at fixed HP before
the prime, requests or child tables. No pointwise PREP accuracy or independent recursive
reseeding is used. Finite input-moment allocations carry no effective/native resource claim.
This completes the bounded first stochastic pilot fragment, while #1721/#1444 remain open.

The checked small-field client computes a positive upper correction `Q(1)` and an actual
preparatory walk equal to one on the retained diagonal. The normalized child and its
completed outer walk also compute
`Q(1)`, with the literal conditional denominator derived as one and a positive allocated
outer length. A separate full-channel identity-base client discharges every hypothesis of
the completed canonical accuracy theorem. A nonunit-rate joint-mean regression retains
the factor `rate 1`, so it cannot silently be replaced by one. Changing only the source frame makes
both zero; a zero base also gives a zero upper correction at positive RAW allocation
and stays zero after the completed outer walk. The
actual hierarchy hypotheses imply that its detector rank exceeds five, so its full detector
is zero. This is an injective small-field, exact-on-slice limit with a nonzero correction;
it does not supply nonzero detector variation or finite-walk mixing error.

Full well-founded approximate evaluation remains open: later pilot/correction iterations,
general finite bin sums, recursive closure and growth, copy routing, native workspace and
RL=L are not supplied by this single-bin first-pilot fragment. This partial construction is not
a selected headline abstract.

The regressions additionally check a correlated detector moment of
`1/32`, a distinct child normalization `1/16`, and nonconstant padded frame source/rank
densities `16/625` and `81/625`.

## Unfold a lattice Fourier coefficient

Import [`Complexity.Foundations.Analysis.Lattice.Fourier`](../../Complexity/Foundations/Analysis/Lattice/Fourier.lean)
to integrate a periodized function at a dual frequency. For a countable `L : Submodule ℤ E`
in a finite-dimensional real inner-product space, supply `IsAddFundamentalDomain L s volume`,
`Integrable f` for `f : E → ℂ`, and membership of `w` in
`LinearMap.BilinForm.dualSubmodule (innerₗ E) L`. Then
`ZLattice.integral_fourierChar_tsum_translate` identifies the integral over `s` of
`(Real.fourierChar (-⟪x,w⟫) : ℂ) * ∑' z : L, f (x + z)` with the Fourier transform of `f`
evaluated at `w`.
The character is `exp(-2πi⟪x,w⟫)`. The domain integral uses ambient volume without a
covolume divisor; it is not the coefficient for probability-normalized quotient measure.

For a real basis `b`, `ZSpan.isAddFundamentalDomain b volume` supplies the domain
`ZSpan.fundamentalDomain b` of `Submodule.span ℤ (Set.range b)`. The basis may be sheared.
For a Schwartz function, use `f.integrable`; for a Gaussian, the checked
[`LatticeFourier.lean` clients](../../ComplexityTests/LatticeFourier.lean) derive integrability
and evaluate the Fourier coefficient using Mathlib's Gaussian transform. They include the basis
`(1,0), (1/2,1)` with nonzero dual frequency `(2,0)`, its Gaussian coefficient `exp(-4π)`,
and the zero-frequency mass identity. Run `scripts/build.sh ComplexityTests.LatticeFourier`
from the repository root to check these complete examples.

Integrability supplies the almost-everywhere convergence needed for exchanging the sum and
integral. No pointwise convergence or uniform convergence assumption is hidden in this theorem.
The [Poisson API](#apply-lattice-poisson-summation) supplies continuity, reconstruction and
covolume normalization for the stated analytic hypotheses. Smoothing estimates remain separate.

## Compute a Gaussian sign-disagreement probability

Import
[`Complexity.Foundations.Probability.Gaussian.Sheppard`](../../Complexity/Foundations/Probability/Gaussian/Sheppard.lean)
and open the `ProbabilityTheory` namespace to use Sheppard's formula. The space `E` is any
finite-dimensional real inner-product space with its Borel σ-algebra, and `stdGaussian E` is
Mathlib's standard Gaussian measure on it. The event is
`{x | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪v, x⟫}`: zero lies in the half-open interval between the two
projections, so they have opposite signs, up to the null event that a projection is zero.

- For nonzero `u` and `v`, `measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu hv` gives
  probability `InnerProductGeometry.angle u v / π`. The norms need not be equal.
- For unit vectors, `measureReal_stdGaussian_zero_mem_uIoc_eq_arccos hu hv` gives
  `arccos ⟪u, v⟫ / π`, the ρ-correlated form of O'Donnell's Example 11.19 with `ρ = ⟪u, v⟫`.

The checked [`GaussianSheppard.lean` clients](../../ComplexityTests/GaussianSheppard.lean)
evaluate both forms in `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`: angle `π/4`
with unequal norms gives `1/4`, orthogonal unit vectors give `1/2`, opposite vectors give `1`,
and the events for `v` and `-v` have probabilities summing to `1`. Run
`scripts/build.sh ComplexityTests.GaussianSheppard` from the repository root to check them.

If a proof needs only an upper bound, or the vectors may be zero, the older
`measureReal_stdGaussian_mem_uIoc_le_angle` (equal norms, any threshold `t`) still applies. For
Gaussian noise stability and its halfspace formula, see
[Compute Gaussian noise stability](#compute-gaussian-noise-stability).

## Compute Gaussian noise stability

Import
[`Complexity.Foundations.Probability.Gaussian.Correlated`](../../Complexity/Foundations/Probability/Gaussian/Correlated.lean)
and open the `ProbabilityTheory` namespace. `correlatedGaussian ρ : Measure (ℝ × ℝ)` is the law
of `(g₁, ρ g₁ + √(1 - ρ²) g₂)` for independent standard Gaussians, and
`correlatedGaussianPi ι ρ` is its `ι`-indexed product, the law of a `ρ`-correlated pair of
vectors in `ι → ℝ`. `gaussianNoiseStability ρ f` is `∫ p, f p.1 * f p.2` against that product.
Most theorems assume `|ρ| ≤ 1`, since `√(1 - ρ²)` is `0` in Lean outside that range.

- To identify a correlated pair, `stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv` says
  that unit-vector projections `(⟪u, X⟫, ⟪v, X⟫)` of `stdGaussian E` have law
  `correlatedGaussian ⟪u, v⟫`. Any other jointly Gaussian law with means `0`, variances `1` and
  covariance `ρ` equals it by `eq_correlatedGaussian`.
- For halfspaces through the origin with `a ≠ 0`, `gaussianNoiseStability_ite_pos_dotProduct hρ ha`
  (open, `0 < a ⬝ᵥ z`) and `gaussianNoiseStability_ite_nonneg_dotProduct hρ ha` (closed) both give
  `1 - 2 / π * arccos ρ`.
- For one coordinate, `gaussianNoiseStability_indicator_Iic_eval hρ i` gives
  `1 / 2 - arccos ρ / (2 * π)` for the indicator of `z i ≤ 0`. For any measurable function of a
  projection, `gaussianNoiseStability_comp_dotProduct` reduces stability to an integral against
  `correlatedGaussian ρ`.

The checked [`GaussianCorrelated.lean` clients](../../ComplexityTests/GaussianCorrelated.lean)
evaluate halfspace stability at `ρ = 1, 0, 1/2, -1`, Example 11.19 at `ρ = 0`, a concrete
projection pair and the `ρ = ±1` laws. Run `scripts/build.sh ComplexityTests.GaussianCorrelated`
from the repository root to check them.

Halfspaces are stated with `a ⬝ᵥ z` on `ι → ℝ`, which has no inner-product instance, and the
open form uses `sgn 0 = -1`. Stability is defined for every `f`. The Bochner integral is `0`
when `f z * f z'` is not integrable, so prove integrability before reading a value off a
non-`L²` function. For the noise operator `U_ρ`, see
[Apply the Gaussian noise operator](#apply-the-gaussian-noise-operator).

## Apply the Gaussian noise operator

Import
[`Complexity.Foundations.Probability.Gaussian.NoiseOperator`](../../Complexity/Foundations/Probability/Gaussian/NoiseOperator.lean)
and open the `ProbabilityTheory` namespace. Write `γ` for the product measure
`Measure.pi fun _ : ι => gaussianReal 0 1` on `ι → ℝ`. Then
`gaussianNoiseOp ρ f z = ∫ g, f (fun i => ρ * z i + √(1 - ρ ^ 2) * g i) ∂γ` is O'Donnell's
`U_ρ f` (Definition 11.12). It is defined for every `ρ` and `f`, and theorems that need the book's
range assume `|ρ| ≤ 1`.

- `measurePreserving_gaussianNoise hρ`: the noisy point `ρ z + √(1 - ρ²) g` is again distributed
  as `γ` when `z` and `g` are independent.
- `eLpNorm_gaussianNoiseOp_le hρ hp hf`: `U_ρ` is a contraction on every `L^p`, `1 ≤ p ≤ ∞`,
  with only `AEStronglyMeasurable f γ` assumed. For `hf : MemLp f p γ`, the dot-notation form
  `hf.gaussianNoiseOp hρ hp` (`MeasureTheory.MemLp.gaussianNoiseOp`) gives membership.
- `gaussianNoiseStability_eq_integral_mul_gaussianNoiseOp hρ hf` rewrites `Stab_ρ[f]` as
  `∫ z, f z * gaussianNoiseOp ρ f z ∂γ` for `f ∈ L²(γ)`. `integral_mul_gaussianNoiseOp_comm` is
  self-adjointness, and `integral_gaussianNoiseOp` is mean preservation for integrable `f`.
- `gaussianNoiseOp_dotProduct ρ a z` computes `U_ρ (a ⬝ᵥ ·) z = ρ * (a ⬝ᵥ z)` exactly, the
  linear case of Fact 11.13.

The checked [`GaussianNoiseOperator.lean` clients](../../ComplexityTests/GaussianNoiseOperator.lean)
cover coordinate and linear inputs, `U_0` and `U_1`, the stability of a constant and of a
coordinate, a self-adjointness and an additivity instance, `L²` and `L^∞` contraction, and mean
preservation. Run `scripts/build.sh ComplexityTests.GaussianNoiseOperator` from the repository
root to check them.

Additivity, `gaussianNoiseOp_add`, holds only `γ`-almost everywhere, because the Bochner integral
is `0` off the integrable functions; scaling by a constant holds everywhere. For multilinear
polynomials, the semigroup law `U_ρ U_σ = U_ρσ` and continuity at `ρ = 1`, see
[Compose Gaussian noise operators](#compose-gaussian-noise-operators). Hermite expansions are not
part of this module.

## Compose Gaussian noise operators

Multilinear polynomials stay in
[`Complexity.Foundations.Probability.Gaussian.NoiseOperator`](../../Complexity/Foundations/Probability/Gaussian/NoiseOperator.lean),
and the semigroup law and continuity live in
[`Complexity.Foundations.Probability.Gaussian.NoiseSemigroup`](../../Complexity/Foundations/Probability/Gaussian/NoiseSemigroup.lean).
Open the `ProbabilityTheory` namespace, and write `γ` for
`Measure.pi fun _ : ι => gaussianReal 0 1` as before.

- `gaussianNoiseOp_prod ρ S z` evaluates a monomial pointwise:
  `U_ρ (∏ i ∈ S, x i) z = ρ ^ #S * ∏ i ∈ S, z i`, for every `ρ` and with no integrability
  hypothesis. `gaussianNoiseOp_sum_mul_prod` does the same for a finite sum
  `∑ k ∈ s, c k * ∏ i ∈ S k, x i`, which is O'Donnell's `U_ρ f (z) = f (ρ z)` (Fact 11.13).
- `gaussianNoiseOp_gaussianNoiseOp hρ₁ hρ₂ hf` is the semigroup law
  `U_ρ₁ (U_ρ₂ f) =ᵐ[γ] U_{ρ₁ ρ₂} f` for `|ρ₁|, |ρ₂| ≤ 1` and integrable `f` (Exercise 11.4). It is
  an almost-everywhere identity, so rewrite inside integrals or norms with `integral_congr_ae` or
  `eLpNorm_congr_ae`, not pointwise.
- `tendsto_eLpNorm_gaussianNoiseOp_sub hf` gives `‖U_ρ f - f‖₁ → 0` as `ρ → 1⁻` along
  `𝓝[<] 1`, for integrable `f` (Proposition 11.17).

The supporting finset-product integrals over product probability measures,
`MeasureTheory.Integrable.finset_prod_pi` and `MeasureTheory.integral_finset_prod_pi_eq_prod`,
are in
[`Complexity.Foundations.MeasureTheory.Integral.Pi`](../../Complexity/Foundations/MeasureTheory/Integral/Pi.lean).

The checked [`GaussianNoiseSemigroup.lean` clients](../../ComplexityTests/GaussianNoiseSemigroup.lean)
compute `U_{1/2} U_{1/2} (x₀ x₁)` both through the semigroup law and through Fact 11.13 twice,
check the boundary cases `ρ₂ = 0` and `ρ₁ = -1`, and apply continuity to a coordinate and to a
discontinuous halfspace indicator. Run `scripts/build.sh ComplexityTests.GaussianNoiseSemigroup`
from the repository root to check them; the monomial clients are in
`ComplexityTests.GaussianNoiseOperator`.

Smoothness of `U_ρ f` for `|ρ| < 1` (Proposition 11.16) is not formalized.

## Evaluate a multi-component conditional walk via validated words

Import
[`Complexity.Probability.PairwiseIndependentHash.ProductValidatedWords`](../../Complexity/Probability/PairwiseIndependentHash/ProductValidatedWords.lean)
and open `Cslib.Probability` to express `t` steps of the lazy conditional product walk over `J`
retention slices and a free-bit torus `(ZMod M)^H` on the ambient space
`ComponentSpace H M P = (∀ j, FrameChannel (P j) H 1) × (Fin H → ZMod M)` (Section 6.1, Lemma 6.3,
items 1–4 of [OpenAI's logspace preprint](../sources.md#openai-logspace26)).

- Each step label `ComponentLazyStep H J` has `4 * (J + 1) * H^2` choices (`card_componentLazyStep`),
  and each candidate wrap vector lies in `affineWrapBox H = {-3, …, 3}^H` of size `7^H`
  (`card_affineWrapBox`), independently of `P`, `L`, `M`, `y` and `t`.
- Every length-`t` word permutation `componentWordPerm L w z` is a bijection of
  `ComponentSpace H M P` independent of the retained identifiers `y` and preserves uniform
  expectations (`expect_componentWordPerm`).
- Retained identifiers `y` enter only through the endpoint wrap test `IsValidComponentWord`: on
  `ComponentSlice H M P L y`, a unique wrap word in `(affineWrapBox H)^t` survives
  (`existsUnique_isValidComponentWord`, `componentWordWrap_mem`) and matches the exact slice walk
  trajectory (`componentWordPerm_wrap_eq`), so averaging over move words `w` and summing over
  wrap words `z` without dividing by `(7^H)^t` equals `walk^t`
  (`walk_pow_componentMove_eq_expect_word`, and iteratively `walk_pow_componentMove_eq_iterate`).

The checked [`ProductValidatedWords.lean` clients](../../ComplexityTests/ProductValidatedWords.lean)
verify concrete alphabet sizes and step wraps on two channels (`𝔽₅`, `𝔽₇`) plus `(ZMod 8)^3` and
combine `walk_pow_componentMove_eq_expect_word` with `ComponentGap` and `SliceFourthMoment` to
bound the `L²` and `L⁴` central moments of the explicit validated-word estimator. Run
`scripts/build.sh ComplexityTests.ProductValidatedWords` from the repository root to check them.
This module covers items 1–4 (distributional and combinatorial word identities); explicit machine
or streaming space realization (the post-item space bound of Lemma 6.3) is separate.
