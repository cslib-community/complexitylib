# Work with randomized and oracle programs

Start with three separate questions: what program is being described, what distribution it denotes, and what machine implements it. `ProbComp α` describes finite-uniform sampling with ordinary `do` notation; `ProbComp.eval` interprets that syntax as a `PMF α`. `ProbOracleComp spec α` adds external requests whose reply types are given by `spec`. The underlying `OracleComp` is a free program over a typed request interface. A PMF supplies mathematical probability semantics; merely writing a PMF does not supply a sampler or a runtime certificate. The [programs and realization reference](../programs-crypto-and-probability/programs-and-realization.md) explains these layers and their sources. [cslib-frontier][complexitylib]

## Witness seedless extraction failure

Import [Extractor/Basic.lean](../../CslibFrontier/Probability/Extractor/Basic.lean).
For a deterministic `f : BitString n → BitString m` and explicit proofs `hn : 1 ≤ n`
and `hm : 1 ≤ m`, apply `exists_minEntropy_map_first_eq_pure hn hm f`.
The resulting source has real min-entropy at least `(n : ℝ) - 1`; its first output
coordinate (index zero) is a point mass, and its output has statistical distance at
least `1 / 2` from uniform. `not_isExtractor_bitString` gives the immediate failure
of extraction with a `Unit` seed and error strictly below `1 / 2`.
For arbitrary finite nonempty inputs, `exists_minEntropy_map_eq_pure_bool` supplies
the reusable Boolean-fiber witness, with entropy `log₂ |Input| - 1`.

This formalizes Chapter 16, exercise 7 of the January 8, 2007 Arora–Barak draft,
printed page 319 (PDF page 335): the source's first coordinate is indexed by one
in the book. Distance uses the probability convention (half the L1 distance).
These are information-theoretic distributions; no sampler or runtime is asserted.
Exercise 12 is covered by the hashing corollary below; broader extractor objectives in issue #895 remain open.
The [ordinary-import clients](../../CslibFrontierTests/SeedlessExtractor.lean) check
`n = m = 1`, multibit identity, sharpness of the distance bound and constant output.
From a configured checkout, run `scripts/build.sh CslibFrontierTests.SeedlessExtractor`.

## Apply the draft leftover hash lemma

Import [Extractor/LeftoverHash.lean](../../CslibFrontier/Probability/Extractor/LeftoverHash.lean).
For `hash : BitString t → BitString n → BitString k`, prove positive `δ` and
`IsUniversalHash (PMF.uniformOfFintype (BitString t)) hash
(ENNReal.ofReal ((1 + δ) / (2 : ℝ) ^ k))`.
Apply `IsUniversalHash.isStrongExtractor_of_entropy_div` for a strong extractor,
or `IsUniversalHash.isExtractor_append_of_entropy_div` for the book's output
`Fin.append (hash s x) s`: digest first, seed last. Both require source min-entropy
at least `(k : ℝ) / δ` and give error `Real.sqrt (2 * δ)`.
These are Lemma 16.42 and Exercise 16.12 of the January 2007 draft, for all lengths
and positive `δ`, including zero digest length. They assert no runtime or short seed.
The [checked clients](../../CslibFrontierTests/LeftoverHashDraft.lean) use an 8-bit
uniform source and Boolean matrix hash, and check zero digest, large error and order.
Run `scripts/build.sh CslibFrontierTests.LeftoverHashDraft` in a configured checkout.

## Transport a distribution bound through a map

Import [TotalVariation/Map.lean](../../CslibFrontier/Foundations/MeasureTheory/Measure/TotalVariation/Map.lean).
For finite measures `μ` and `ν` and a measurable function `f`, apply
`MeasureTheory.tvDist_map_le μ ν hf` to bound the distance of their pushforwards by
`tvDist μ ν`. The measures may have different total masses. The extended-valued theorem
`etvDist_map_le` has the same hypotheses and avoids conversion to real numbers.

This is Mathlib's full-L1 convention: distinct probability atoms have distance `2`,
and the distance of `2 • dirac x` from the zero measure is `2` as well. The finite-measure
instances matter because real `tvDist` is defined as zero if its extended value is infinite.
A previously proved bound transports with `(tvDist_map_le μ ν hf).trans h`;
no density, injectivity or probability normalization is required.

The [checked clients](../../CslibFrontierTests/TotalVariationMap.lean) include identity,
strict coarsening from distance `2` to `0`, unequal masses, and the canonical measurable
map from `ℝ` to `UnitAddCircle`. Run `scripts/build.sh CslibFrontierTests.TotalVariationMap`.
The theorem transports an existing bound; it does not identify the output laws. The Gaussian
projection and mod-one bounds of
[issue #2734](https://github.com/cslib-community/cslib-frontier/issues/2734) apply it to actual laws.

## Combine component and mixture-weight errors

Import [TotalVariation/Mixture.lean](../../CslibFrontier/Foundations/MeasureTheory/Measure/TotalVariation/Mixture.lean).
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

The [checked clients](../../CslibFrontierTests/TotalVariationMixture.lean) include sharp unequal-mass
examples and a tagged mixture on `Fin 6 × ℝ`. In that client, actual finite-PMF weights sum
to one; component errors bounded by `4 * ε` and a weight discrepancy bounded by `δ` give a
joint error of `4 * ε + δ`. The tags are actual measurable pushforwards, so map contraction
supplies their component bounds. Run `scripts/build.sh CslibFrontierTests.TotalVariationMixture`.
The [Regev joint experiment](https://github.com/cslib-community/cslib-frontier/issues/2767) still
has to discharge those bounds for its actual Gaussian laws and residue marginal.

## Bound an event count by its first moment

Import [EventCount.lean](../../CslibFrontier/Probability/EventCount.lean) when an algorithm counts
events indexed by a list. After `open Cslib.Probability`, apply
`PMF.tsum_mul_countP_le μ E B l hE`: if each event `{ω | E ω x}` for `x ∈ l` has probability at
most `B`, the expected count is at most `l.length * B`. The list may repeat entries and the
events may be dependent. The theorem imposes no finiteness or measurable-space requirement on
the sample type.

For a measure `μ`, use `measurable_and_lintegral_countP_le μ E B l hmeas hE`. Its two conclusions
give measurability of the count and the same bound on its Lebesgue integral. Supply measurability
and a measure bound for each event; probability normalization is unnecessary. This is the shared
first-moment argument used by both discrete and continuous LSH analyses.

The [checked clients](../../CslibFrontierTests/EventCount.lean) cover an empty list on an infinite
sample space, two identical fair-coin events whose expected count is exactly one, and a measure
of total mass two. Run `scripts/build.sh CslibFrontierTests.EventCount`.

## Condition and compare finite PMFs

Import [PMF/Filter.lean](../../CslibFrontier/Probability/PMF/Filter.lean) to rewrite a conditioned
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
To state that two observables of a PMF are independent, import
[PMF/Independence.lean](../../CslibFrontier/Probability/PMF/Independence.lean):
`indepFun_iff_map_pair_eq_bind` identifies Mathlib's `IndepFun f g p.toMeasure` with this
two-stage form `p.map (f, g) = (p.map f).bind fun a => (p.map g).map (a, ·)`. When `Y` is
moreover uniform on a finite type, state `IndepUniform ν X Y`, consume it with `.map_pair_eq`,
and use `indepUniform_iff` to split it into `IndepFun` and `ν.map Y = uniformOfFintype _`.

Import [StatisticalDistance/Event.lean](../../CslibFrontier/Probability/StatisticalDistance/Event.lean)
to turn a distance bound into event bounds. Here `dist` is cslib's statistical distance on PMFs
over a finite type, active after `open scoped Cslib.Probability.PMF`. It uses the half-L1
convention: distinct point masses have distance `1`, half of Mathlib's `tvDist` above.
[StatisticalDistance/TotalVariation.lean](../../CslibFrontier/Probability/StatisticalDistance/TotalVariation.lean)
connects the three notions: `dist_eq_tvDist_toMeasure_div_two` converts `dist` to `tvDist`,
`closeTo_coe_iff_dist_le` states that the all-event `CloseTo μ ν ε` is exactly `dist μ ν ≤ ε`, and
`closeTo_iff_etvDist_le` states that it is exactly a total variation bound `2 * ε`, also on
infinite types with measurable singletons. The real-valued form `closeTo_ofReal_iff_tvDist_le`
needs `0 ≤ ε`: a negative error becomes `0` under `ENNReal.ofReal`.
`abs_toOuterMeasure_toReal_sub_le_dist p q E` bounds `|Pr_p[E] − Pr_q[E]|` by `dist p q`;
`abs_bind_apply_toReal_sub_le_dist p q T b` does the same for the probability that a randomized
distinguisher `T` outputs `b`. `dist_map_of_injective` keeps the distance unchanged under an
injective relabeling. For a second-moment tail bound on a finite PMF without measure-theoretic side
conditions, import [PMF/Chebyshev.lean](../../CslibFrontier/Probability/PMF/Chebyshev.lean): by
`sum_mul_ite_le_sum_mul_sq_div`, the mass where `|f a − m| ≥ c` is at most
`∑ a, p(a) (f a − m)² / c²`. The first-moment form for a function `f` with values in `[0, 1]`
is `toOuterMeasure_toReal_le_tsum_div` in
[PMF/Markov.lean](../../CslibFrontier/Probability/PMF/Markov.lean). Import
[Product/Split.lean](../../CslibFrontier/Probability/Product/Split.lean) to split an independent
product `pi p` along a predicate `P`: by `pi_map_piEquivPiSubtypeProd`, the coordinates
satisfying `P` and the remaining coordinates form two independent products. Its corollaries
`pi_map_restrict` and `pi_map_comp_injective` give the marginal law: restricting `pi p` to the
coordinates satisfying `P`, or reading it along an injection `e` of index types as
`fun a k => a (e k)`, gives the independent product of the selected factors. For a product indexed
by a sum type `ι ⊕ κ`, `bind_pi_sum` samples the two summands as independent products inside a
`bind`. Use these instead of counting tuples when the factors are not uniform. `pi_map_curry` in
[Product/Reindex.lean](../../CslibFrontier/Probability/Product/Reindex.lean) splits a product
indexed by `ι × κ` into independent blocks, and `toOuterMeasure_pi_forall` in
[Product/Event.lean](../../CslibFrontier/Probability/Product/Event.lean) is the probability of a
box `{u | ∀ i, u i ∈ E i}`. For `Fin k`-indexed tuples with different factors, `PMF.piFin` in
[IID.lean](../../CslibFrontier/Probability/IID.lean) generalizes `iid`, and
[IID/Event.lean](../../CslibFrontier/Probability/IID/Event.lean) gives its box and union bounds
`toOuterMeasure_piFin_forall` and `toOuterMeasure_toReal_piFin_exists_le`. To move a finite
statistic of i.i.d. samples from a measure into this setting, import
[Product/MapMeasure.lean](../../CslibFrontier/Probability/Product/MapMeasure.lean):
`map_measurePi_eq_toMeasure_pi` identifies the image of `Measure.pi μ` under coordinatewise
almost everywhere measurable maps into finite types with
`(pi fun i => ((μ i).map (g i)).toPMF).toMeasure`. The finite-product bounds then apply:
Hoeffding's `pi_sum_abs_sub_mean_ge` in
[Concentration.lean](../../CslibFrontier/Probability/Concentration.lean) and the Chernoff lower
tail `pi_sum_le_one_sub_mul` in [Chernoff.lean](../../CslibFrontier/Probability/Chernoff.lean). For
a uniform draw on a finite group, import
[Uniform.lean](../../CslibFrontier/Probability/Uniform.lean): `uniformOfFintype_map_add_left` and
`uniformOfFintype_bind_add_left`, with their `_right` forms, remove a fixed mask as in the one-time
pad, and the `_sub_left` and `_sub_right` forms in
[Uniform/Translate.lean](../../CslibFrontier/Probability/Uniform/Translate.lean) do the same for
`c - x` and `x - c`;
`uniformOfFintype_map_addHom` and `uniformOfFintype_map_monoidHom` push the uniform law
through a surjective homomorphism; and `uniformOfFintype_map_comp` reads a uniform function
through an injection. For a dependent function, `uniformOfFintype_map_comp_dep` in
[Product/Split.lean](../../CslibFrontier/Probability/Product/Split.lean) needs only nonempty
fibres. On any finite type, `uniformOfFintype_bind_bijective` in
[PMF/Uniform.lean](../../CslibFrontier/Probability/PMF/Uniform.lean) changes variables in a uniform
draw along a bijection. For a biased bit, use `coin p` from
[PMF/Coin.lean](../../CslibFrontier/Probability/PMF/Coin.lean), with `p : unitInterval`; Mathlib's
`PMF.bernoulli` is deprecated. `toMeasure_coin` identifies `(coin p).toMeasure` with Mathlib's
`ProbabilityTheory.bernoulliMeasure true false p`, and `entropy_coin` in
[Entropy/Fano.lean](../../CslibFrontier/Probability/Entropy/Fano.lean) is its entropy `h₂(p)`. For
uniform `k`-element subsets `uniformOfFinset (A.powersetCard k) _`, import
[PMF/UniformPowerset.lean](../../CslibFrontier/Probability/PMF/UniformPowerset.lean) for uniform
one-element deletion when `1 ≤ k ≤ A.card` (`uniformOfFinset_powersetCard_erase`), hit-or-erase
invariance when querying an element `p ∈ A` with `1 ≤ k ≤ A.card`—returning `U.erase p` when
`p ∈ U` and a uniform deletion otherwise, which distributes uniformly over `(k - 1)`-subsets of
`A.erase p` (`uniformOfFinset_powersetCard_hitOrErase`; an outside query `p ∉ A` instead uses the
plain erasure law)—and exact miss probability `(A.card - k) / A.card` for `p ∈ A` and
`k ≤ A.card` (`toOuterMeasure_uniformOfFinset_powersetCard_notMem`, including `k = 0`).

The [checked clients](../../CslibFrontierTests/PMFConditioning.lean) condition two fair bits on
rectangles, split off one of two fair bits, relabel two point masses injectively, restrict, reindex
and curry independent coins of different biases, and compute the probability that three coins all
show `true`. Run
`scripts/build.sh CslibFrontierTests.PMFConditioning`.

For real conditional expectations on a finite product distribution `PMF.pi p` (`∀ i : ι, α i`) given
coordinate assignments on `fixed : Finset ι`, import
[Product/ConditionalExpectation.lean](../../CslibFrontier/Probability/Product/ConditionalExpectation.lean).
`PMF.condExpect p f fixed x` sums `f` against the product of `(p i)` over unfixed coordinates `i ∉ fixed`
without requiring positive cylinder mass, so it extends smoothly outside `(PMF.pi p).support` while
identifying `(PMF.pi p).filter …` with `fixedPi p fixed x` whenever fixed coordinates lie in
`(p i).support` (`filter_pi_cylinder`). `condExpect_empty` recovers the full product expectation,
`condExpect_univ` evaluates `f x`, `sum_mul_condExpect_insert` is the one-coordinate tower law, and
`exists_condExpect_insert_le` / `exists_le_condExpect_insert` produce support-valued coordinate
choices preserving the conditional expectation.

Real-valued probabilities lie in `[0, 1]`. The lower bound is `ENNReal.toReal_nonneg`; for the
upper bound, import [PMF/ToReal.lean](../../CslibFrontier/Probability/PMF/ToReal.lean) and use
`PMF.toReal_apply_le_one μ a` for an outcome or `PMF.toOuterMeasure_toReal_le_one μ s` for an
event (these short names need `open Cslib.Probability`), rather than converting `μ a ≤ 1` through
`ENNReal.toReal` by hand. The `Pr[e]` notation module re-exports this file, so `Pr[e] ≤ 1` is
`PMF.toReal_apply_le_one _ true`; the
[checked examples](../../CslibFrontierTests/ProbabilityNotation.lean) bound a program and a set event.
Run `scripts/build.sh CslibFrontierTests.ProbabilityNotation`.

For a Boolean distribution `p : PMF Bool`, import
[PMF/Bool.lean](../../CslibFrontier/Probability/PMF/Bool.lean) and use
`PMF.apply_true_add_apply_false p : p true + p false = 1` rather than rewriting with `tsum_bool`
and `PMF.tsum_coe` by hand. Its real forms are `PMF.toReal_true_add_toReal_false` and
`PMF.toReal_false_eq_one_sub`. The same module bounds Boolean events written as `(p.map E) true`:
`PMF.map_true_mono`, `PMF.map_true_le_add`, the union bounds `PMF.map_true_le_sum` (over any
`s : Finset ι`) and `PMF.map_any_range_true_le_sum`, `PMF.map_apply_true` (the expectation of the
indicator of `E`), and `PMF.map_not_true` for complements. A two-stage experiment
`p.bind fun a => PMF.pure (E a)` is `p.map E` by definition, so these lemmas apply to it directly.
To compose an event bound through `PMF.bind`, use the `PMF.toOuterMeasure_bind_*` lemmas in
[PMF/EventBind.lean](../../CslibFrontier/Probability/PMF/EventBind.lean). The
[checked examples](../../CslibFrontierTests/PMFBool.lean) recover the mass of `false` from the mass of
`true` and apply the finite union bound; run `scripts/build.sh CslibFrontierTests.PMFBool`.

To show that a pushforward or a two-stage experiment is deterministic, import
[PMF/Support.lean](../../CslibFrontier/Probability/PMF/Support.lean): `PMF.map_eq_pure_iff` says
`p.map f = PMF.pure b` exactly when `f a = b` for every `a ∈ p.support`, and
`PMF.bind_eq_pure_of_forall_mem_support` gives `p.bind f = PMF.pure b` from `f a = PMF.pure b` on the
support. Perfect-correctness statements of the form `Pr[correct] = 1` written as
`(...).map isCorrect = PMF.pure true` reduce to a pointwise check this way, and
`PMF.ne_of_map_eq_pure` separates two distributions whose pushforwards are different point masses.
The same module records that pairing with a constant (`snd_eq_of_mem_support_map_pair`) or lifting
into `StateT` (`snd_eq_of_mem_support_lift`, `toOuterMeasure_lift_eq_zero`) keeps the state fixed on
the support. The [checked examples](../../CslibFrontierTests/PMFSupport.lean) cover each direction;
run `scripts/build.sh CslibFrontierTests.PMFSupport`.

For a guessing bound, import
[PMF/UniformPoint.lean](../../CslibFrontier/Probability/PMF/UniformPoint.lean) instead of summing
over the uniform law by hand. For any law `μ`, `PMF.bind_pure_decide_eq_apply_true μ a` (and its
`'` and `map_` forms for the other comparison order and for `μ.map`) says an equality test against
`a` accepts with probability `μ a`. `PMF.uniformOfFintype_bind_decide_eq_apply_true a` specializes
it: a uniform draw equals `a` with probability `(Fintype.card α)⁻¹`, and
`PMF.uniformOfFintype_bind_pure_apply_true_le` gives the upper bound `(Fintype.card α)⁻¹` for any
test accepting at most one value, such as comparing a fixed point with an injective image of the
draw. For an event written as a set, `PMF.toOuterMeasure_uniformOfFintype_le_of_subsingleton` gives
the same bound when the set has at most one member; for the preimage of a point under an injective
`f`, supply `Set.subsingleton_singleton.preimage hf`. The
[fixed-group Diffie–Hellman checks](../../CslibFrontierTests/Crypto/DiffieHellmanFinite.lean)
compute discrete-logarithm advantages `1 / q` with it.

To compare two-stage experiments at one outcome, import
[PMF/BindCompare.lean](../../CslibFrontier/Probability/PMF/BindCompare.lean) instead of expanding
`PMF.bind_apply` into sums. `PMF.bind_apply_add_of_forall` and `PMF.bind_apply_add_eq_on_support`
carry a pointwise sum identity between continuations over to the experiments,
`PMF.bind_apply_le_add_of_ne` bounds continuations that are close away from one first-stage result,
and `PMF.bind_apply_eq_of_good` equates stateful experiments that agree until a bad state. The
one-sided comparisons on the support are in
[PMF/Bind.lean](../../CslibFrontier/Probability/PMF/Bind.lean).

Moving a bound between `ℝ≥0∞` and `ℝ` or `ℝ≥0` (`ENNReal.toReal_mono`, `ENNReal.toReal_add`,
`ENNReal.toNNReal_mono`, `ENNReal.toReal_sum`) needs every term to be finite. Import
[PMF/Finiteness.lean](../../CslibFrontier/Probability/PMF/Finiteness.lean) and discharge each side
condition with `by finiteness`, in place, instead of assembling it from `ENNReal.add_ne_top`,
`ENNReal.sum_ne_top` and `PMF.apply_ne_top`. The module makes Mathlib's `finiteness` know that a
mass `p a`, an event probability `p.toOuterMeasure s` and a finite sum of finite terms are finite,
and lets it apply hypotheses such as `h : ∀ i, f i ≠ ∞`. Mathlib already covers sums, products,
powers, casts and inverses of nonzero terms, and hypotheses `x ≠ ∞` or `x < _`; the module keeps
the `x < _` case working alongside its sum rule. A factor with no such reason, such as an arbitrary
`x : ℝ≥0∞`, makes it fail, often only after Aesop's rule-application limit; add a hypothesis
`x ≠ ∞` or prove that factor separately. Each successful call costs roughly 100 to 800 heartbeats
of Aesop search and positivity, so where the explicit term is
a single `PMF.apply_ne_top _ _` keep the term. To compare success probabilities, import
[Game/Order.lean](../../CslibFrontier/Crypto/Game/Order.lean):
`apply Game.succProbability_mono` leaves the goal `g₁ true ≤ g₂ true`, without unfolding
`Game.succProbability`, and `Game.succProbability_le_add_of_advantage_le` turns a bound on
`Game.advantage g₀ g₁` into `succProbability g₀ ≤ succProbability g₁ + B`. The [checked examples](../../CslibFrontierTests/PMFFiniteness.lean) cover
each rule and the failure.

## Count the fair coins used by an exact sampler

Import [DDGTree.lean](../../CslibFrontier/Probability/DDGTree.lean) to describe an exact sampler as
a discrete distribution generating tree. Such a tree reads fair bits and stops at an
outcome-labelled leaf, and it may be infinite. A `DDGTree α` is given by its prefix labelling
`output : List Bool → Option α`, with leaves absorbing. `T.run n` is the law of the outcome after
`n` fair bits, where `none` means "still running". `T.Generates p` states that the eventual output
has law `p`. `T.expectedFlips` is the tail sum `∑ₙ P(T > n)`. For trees that halt almost surely,
`expectedFlips_eq_tsum_mul` converts it to `∑ₖ (k + 1) P(T = k + 1)`, and
`tendsto_run_none_of_generates` shows that every generator of a `PMF` distribution halts almost
surely. A tree that fails to halt with positive probability has `expectedFlips = ⊤`
(`expectedFlips_eq_top`). `T.output <$> BitString.sampleList n` is the same experiment written as a
`ProbComp`; its `eval` is `T.run n`.

Import [DDGTree/KnuthYao.lean](../../CslibFrontier/Probability/DDGTree/KnuthYao.lean) for the
entropy bounds ([Knuth–Yao 1976](../sources.md#knuthyao76);
[Cover–Thomas §5.11](../sources.md#coverthomas06)), stated for distributions on a finite type:

- `entropy_le_expectedFlips hT : ENNReal.ofReal (PMF.entropy p) ≤ T.expectedFlips` for every
  `hT : T.Generates p`;
- `knuthYao p` generates `p` (`knuthYao_generates`), has the least expected cost
  (`isLeast_expectedFlips_knuthYao`; pointwise `run_knuthYao_none_le`), and satisfies
  `expectedFlips_knuthYao_lt : (knuthYao p).expectedFlips < ENNReal.ofReal (PMF.entropy p + 2)`;
- `exists_generates_expectedFlips_eq_entropy_iff`: some tree attains `H(p)` exactly when every
  positive `p a` is a power of `1/2`.

To compute the optimal cost for a concrete `p`, rewrite with `expectedFlips_knuthYao` to
`∑ₐ knuthYaoCost (p a).toReal`. Then use `knuthYaoCost_inv_two_pow` for dyadic masses, or sum the
truncation errors `truncErr` directly. To build a tree from a count profile, use `ofCounts t`. In
that tree, `t k a` of the `2 ^ k` depth-`k` positions lie at or below a leaf labelled `a`; a leaf at
depth `j ≤ k` counts `2 ^ (k - j)` times. Equivalently, `t k a / 2 ^ k` is the probability of having
output `a` within `k` flips (`run_ofCounts`). The profile must be inherited,
`2 * t k a ≤ t (k + 1) a`, and must satisfy the Kraft-type budget `∑ₐ t k a ≤ 2 ^ k`.

The [checked clients](../../CslibFrontierTests/KnuthYao.lean) cover the fair coin (`1` flip), the
dyadic `(1/2, 1/4, 1/4)` (`3/2` flips, equal to the entropy) and `(2/3, 1/3)`. For the last, the
optimal cost is exactly `2`, no generating tree does better, and the entropy is strictly smaller.
They also cover a non-halting tree that generates nothing and has infinite cost. Run
`scripts/build.sh CslibFrontierTests.KnuthYao`. The model counts coin flips only; it does not certify
that `knuthYao p` is computable from an encoding of `p`, or bound its running time.

To run the same trees on a biased coin, import
[DDGTree/Biased.lean](../../CslibFrontier/Probability/DDGTree/Biased.lean). `T.runWith c n`,
`T.outputProbWith c`, `T.GeneratesWith c p` and `T.expectedFlipsWith c` replace fair bits by
independent flips of `c : PMF Bool`; `run_eq_runWith` and its siblings recover the fair-bit API at
`PMF.uniformOfFintype Bool`. `T.expectedCostWith c w` charges `w n` for flip number `n + 1`, which
is read exactly when the tree has not stopped after `n` flips, so it is `∑ₙ w n P(T > n)`. Use a
tree rather than an `OracleComp` program when the sampler loops without a bound: oracle programs
are finite call trees, so `OracleComp.retry` only expresses the truncated loop, with a visible
failure outcome. `vonNeumann` reads flips in pairs until they differ
([Arora–Barak draft Lemma 7.15](../../results/arora-barak-2007.md#chapter-7-randomized-computation)).
On `PMF.coin ρ` with `0 < ρ < 1`, `vonNeumann_generatesWith_coin` gives an exactly fair bit and
`expectedFlipsWith_coin_vonNeumann` gives exactly `ENNReal.ofReal (ρ * (1 - ρ))⁻¹` flips.
`exists_generatesWith_coin_iff` shows that `0 < ρ < 1` is necessary: at bias `0` or `1` the coin is
deterministic (`runWith_pure`). In the other direction, import
[DDGTree/Digits.lean](../../CslibFrontier/Probability/DDGTree/Digits.lean) for Lemma 7.14.
`coinOfDigits d` compares fair bits with a binary expansion `d` of `ρ`, stated as
`HasSum (fun i => if d i then 2⁻¹ ^ (i + 1) else 0) ρ`. Use the expansion `0.111⋯` for `ρ = 1`.
It generates `PMF.coin ρ` (`coinOfDigits_generates`) and reads exactly two fair bits in expectation
(`expectedFlips_coinOfDigits`). Its expected digit cost is `∑ₙ w n 2⁻ⁿ`
(`expectedCostWith_coinOfDigits`), which is finite for polynomially bounded `w`.
[Computability/Probabilistic/CoinOfDigits.lean](../../CslibFrontier/Computability/Probabilistic/CoinOfDigits.lean)
instantiates `w` with the time bound of a multitape machine computing the digits from `encUnary`.
The comparison loop itself is charged one unit per flip, not compiled to a machine. The
[checked clients](../../CslibFrontierTests/BiasedCoinSamplers.lean) cover bias `1/3` (`9/2` flips),
the impossible bias `0`, `ρ = 1` and a constant digit machine; run
`scripts/build.sh CslibFrontierTests.BiasedCoinSamplers`.

When an exact sampler instead repeats a fixed-width `width`-bit decoder `attempt : List Bool → Option α`,
import [DDGTree/Rejection.lean](../../CslibFrontier/Probability/DDGTree/Rejection.lean) for
`BlockRejectionSpec`, [Languages/Probabilistic/RejectionSampling.lean](../../CslibFrontier/Languages/Probabilistic/RejectionSampling.lean)
for the `ProbComp` programs (`sampleBlockTrials`, `sampleSeededTrials`, `sampleBlockCapped`), and
[Computability/Probabilistic/RejectionSampling.lean](../../CslibFrontier/Computability/Probabilistic/RejectionSampling.lean)
for strict `IsPPTOn` certificates (`isPPTOn_sampleSeededTrials`, `isPPTOn_sampleBlockTrials`,
`isPPTOn_sampleBlockCapped`) when `trials` and `width` are computed in `encUnary`, the `attempt`
decoder is polynomial-time on input-and-block pairs, and (`sampleBlockCapped`) the `fallback` map
is polynomial-time. On the unbounded
side, `spec.toDDGTree` satisfies `run_toDDGTree` (`n / width` trials after `n` fair bits), generates
the target law when `0 < width` and `acceptProb ≠ 0` (`toDDGTree_generates`), and reads
`width / acceptProb` fair bits in expectation (`expectedFlips_toDDGTree`, including `⊤` when
`acceptProb = 0`). On the capped side, `runTrials_none` gives exact failure `rejectProb ^ t` and
`dist_runCapped_le` bounds fallback statistical distance by `(rejectProb ^ t).toReal`.
`uniformFinTree` and `uniformFinRejectionSpec` specialize this to `Fin n` (`≤ 2 * Nat.clog 2 n`
expected flips, `k` flips at `2 ^ k`, and `≤ (1 / 2) ^ t` capped failure; `dyadicFinRejectionSpec`
and `subsetDyadicSpec` cover `dyadicSize n` and finite subsets). The
[checked clients](../../CslibFrontierTests/FairBitRejectionAndCondExp.lean) verify exact `8 / 3` and
`24 / 5` flip counts on `Fin 3` and `Fin 5`, capped `Fin 3` bounds, the never-accepting `⊤`
boundary, subset sampling on `Fin 6`, and `IsPPTOn`; run
`scripts/build.sh CslibFrontierTests.FairBitRejectionAndCondExp`.

## Polarize statistical distance

Sahai and Vadhan's polarization of statistical distance is formalized on explicit distributions
over finite types, with the half-L1 `dist` above. The source is Sahai–Vadhan 2003, §3.2: the
Polarization Lemma is Lemma 3.3, extended to thresholds `α² > β` in the remark after its proof; the
Direct Product Lemma is Lemma 3.4 and the XOR Lemma is Lemma 3.5. Statistical Difference is defined
in §3.1 with the strict thresholds `2/3` and `1/3`; the variant `SD^{α,β}` with non-strict
thresholds, used below, is defined on p. 234.

- **XOR construction.** Import
  [StatisticalDistance/XOR.lean](../../CslibFrontier/Probability/StatisticalDistance/XOR.lean).
  `xorMix p₀ p₁ k c` draws selector bits of parity `c` uniformly, then coordinate `i` from `p₀`
  or `p₁` according to bit `i`. For `k ≠ 0`, `dist_xorMix` proves
  `dist (xorMix p₀ p₁ k false) (xorMix p₀ p₁ k true) = dist p₀ p₁ ^ k`.
  `dist_xorMix_le` gives the upper bound for every `k`. The identity fails at `k = 0`, where both
  sides live on a one-point type.
- **Direct-product lower bound.** Import
  [StatisticalDistance/DirectProduct.lean](../../CslibFrontier/Probability/StatisticalDistance/DirectProduct.lean).
  `one_sub_two_mul_exp_le_dist_iid` proves `1 - 2 exp (-k δ² / 2) ≤ dist (iid μ k) (iid ν k)` from
  Hoeffding's inequality. The matching upper bound `k δ` is `dist_iid_le`.
- **Polarization.** Import
  [StatisticalDistance/Polarization.lean](../../CslibFrontier/Probability/StatisticalDistance/Polarization.lean).
  `polarize p₀ p₁ λ ℓ k c` applies the XOR construction on `k` coordinates to `ℓ` independent
  copies of the XOR construction on `λ` coordinates. `dist_polarize_le` bounds its distance by
  `(ℓ δ^λ)^k`, and `one_sub_two_mul_mul_exp_le_dist_polarize` bounds it below by
  `1 - 2 k exp (-ℓ δ^(2λ) / 2)`. For constant thresholds `0 ≤ β < α² ≤ 1`,
  `exists_polarization` provides constants `m ≠ 0` and `b`. With these, `λ = m (⌊log₂ k⌋ + 1)` and
  `ℓ = 2 ^ (b (⌊log₂ k⌋ + 1))` are polynomially bounded in `k`. Distance `≥ α` then becomes
  `≥ 1 - 2⁻ᵏ`, and distance `≤ β` becomes `≤ 2⁻ᵏ`. Use it as
  `obtain ⟨m, b, hm, hlam, hell, h⟩ := exists_polarization hβ hβα hα hα1`, then
  `(h p₀ p₁ k).1` for the far side and `(h p₀ p₁ k).2` for the near side.

The checked clients in [Polarization.lean](../../CslibFrontierTests/Polarization.lean) cover the
following:

- the exact XOR distance `1/8` of a uniform bit against a point mass;
- the failure of the identity at `k = 0`;
- a direct-product bound at `32` copies;
- the thresholds `α = 2/3`, `β = 1/3`.

Run `scripts/build.sh CslibFrontierTests.Polarization`.

### Polarize circuit samplers and Statistical Difference instances

A circuit `C : Circuit σ n m` is a sampler. `C.outputDist I` is the distribution of its outputs on
uniform inputs, defined in
[Circuit/OutputDistribution.lean](../../CslibFrontier/Computability/Circuit/OutputDistribution.lean).
`Circuit.outputDist_replicate` says that `C.replicate k` samples `iid (C.outputDist I) k`, with the
`k` output blocks flattened by `Cslib.BitString.blocksEquiv`.

- **XOR and polarization circuits.** Import
  [Circuit/Boolean/Polarization.lean](../../CslibFrontier/Computability/Circuit/Boolean/Polarization.lean).
  For De Morgan circuits `C₀ C₁ : Circuit signature n m`, `xorMixCircuit C₀ C₁ j c` reads `j`
  selector bits and then `j + 1` data blocks. It samples
  `xorMix (C₀.outputDist _) (C₁.outputDist _) (j + 1) c` (`outputDist_xorMixCircuit`). The selector
  is completed to parity `c` by `BitString.parityComplete`, from
  [XORSampling.lean](../../CslibFrontier/Probability/StatisticalDistance/XORSampling.lean).
  `polarizeCircuit C₀ C₁ lam ell k c` samples `polarize … (lam + 1) ell (k + 1) c`
  (`outputDist_polarizeCircuit`). Note that the coordinate counts are passed as predecessors.
  `dist_outputDist_polarizeCircuit` transfers the distance bounds of `polarize` unchanged.
- **Statistical Difference.** Import
  [Problems/StatisticalDifference.lean](../../CslibFrontier/Computability/Complexity/Problems/StatisticalDifference.lean).
  An `SDInstance` is a pair of De Morgan circuits with common input and output counts, and
  `StatisticalDifference α β` is `PromiseProblem.gapMax` of `SDInstance.distance`.
  `SDInstance.exists_polarize` is the Polarization Lemma on instances, for constant thresholds
  `0 ≤ β < α² ≤ 1`. It passes `m (⌊log₂ (k + 1)⌋ + 1) - 1` as `lam`, so there are
  `m (⌊log₂ (k + 1)⌋ + 1)` inner coordinates. It passes `2 ^ (b (⌊log₂ (k + 1)⌋ + 1))` as `ell`,
  the number of copies, and `k` as the outer argument, so there are `k + 1` outer coordinates.
  `StatisticalDifference.exists_mapsTo_polarize` states the result as `Set.MapsTo` into
  `StatisticalDifference (1 - (1/2)^(k+1)) ((1/2)^(k+1))`, for `k ≠ 0`.
- **Polynomial-time polarization.** Import
  [Problems/StatisticalDifference/PolyTime.lean](../../CslibFrontier/Computability/Complexity/Problems/StatisticalDifference/PolyTime.lean).
  `encSDInstance` encodes the input and output counts in unary, followed by both circuit codes.
  `SDInstance.computableInPolyTime_polarize` makes `x.polarize (lam x) (ell x) (k x)`
  polynomial-time whenever the three parameters are polynomial-time with unary output.
  `SDInstance.computableInPolyTime_polarize_comp` is the general form. There the instance and the
  parameters are polynomial-time functions of any encoded input; `computableInPolyTime_polarize_log`
  specializes it to the parameters of `SDInstance.exists_polarize`.
  `SDInstance.exists_computableInPolyTime_polarize_unary` is the source's form, with the error
  parameter `k` a separate unary input: one map on `encPair encSDInstance encUnary` with error
  `(1/2)^(k + 1)`.
  `SDInstance.exists_computableInPolyTime_polarize` instead takes `k = K x` for a function `K` of
  the instance. Use
  `obtain ⟨m, b, hm, h⟩ := …`, then `h K hK` for any polynomial-time unary `K`. It returns the
  polynomial-time certificate and the two distance bounds with error `(1/2)^(K x + 1)`.
  Two corollaries cover the common cases. With `K x` the encoded length,
  `SDInstance.exists_computableInPolyTime_polarize_length` gives error `(1/2)^(|x| + 1)`. With `K`
  constant, `StatisticalDifference.polyTimeReducible` is a `PromiseProblem.PolyTimeReducible`
  from `SD^{α,β}` to `SD^{α',β'}`, for all constants `0 < β' < α' < 1`.
  The raw code generators behind the certificate are in
  [Circuit/Boolean/Polarization/PolyTime.lean](../../CslibFrontier/Computability/Circuit/Boolean/Polarization/PolyTime.lean).
  Import that module directly to use them; `StatisticalDifference/PolyTime.lean` does not
  re-export it. Each generator has a `_code` lemma stating exact agreement with the typed circuit.
  `polarizeCode` builds on `replicateCode`, from
  [CodeReplication.lean](../../CslibFrontier/Computability/Circuit/Boolean/CodeReplication.lean),
  and on `muxCode`, from
  [Comparison/PolyTime.lean](../../CslibFrontier/Computability/Circuit/Boolean/Comparison/PolyTime.lean).

The thresholds are constants with `0 ≤ β < α² ≤ 1`, and the circuits are De Morgan circuits with
common input and output counts. SZK itself is not formalized yet;
[issue #3205](https://github.com/cslib-community/cslib-frontier/issues/3205) tracks it. The checked
clients in [StatisticalDifference.lean](../../CslibFrontierTests/StatisticalDifference.lean) cover:

- parity completion;
- the XOR circuit on two constant circuits;
- a far instance and a near instance against `SD^{2/3,1/3}`;
- both instances pushed through the Polarization Lemma.

The clients in
[StatisticalDifferencePolyTime.lean](../../CslibFrontierTests/StatisticalDifferencePolyTime.lean)
cover:

- a concrete replicated code and its typed agreement;
- the multiplexer gate count;
- a polynomial-time polarization map with fixed parameters;
- the reduction from `SD^{2/3,1/3}` to `SD^{9/10,1/10}` on the far and the near instance;
- the length-indexed polarization on the same instances;
- the polarization with the error parameter `k` in unary on the same instances, for every `k`;
- `SDInstance.computableInPolyTime_polarize_comp` on `p ↦ p.1.polarize 1 2 p.2` over
  `encPair encSDInstance encUnary`.

Run `scripts/build.sh CslibFrontierTests.StatisticalDifference` and
`scripts/build.sh CslibFrontierTests.StatisticalDifferencePolyTime`.

## Compare distributions by Hellinger distance and chi-square divergence

For finite distributions (`PMF α` with `[Finite α]` / `[Fintype α]`), Hellinger distance and
Pearson `χ²` divergence complement half-`L¹` statistical distance (`dist`) with exact product
tensorization and comparison inequalities ([Tsybakov, Section 2.4](../sources.md#tsybakov09);
[Canonne, §3.1 and Appendix B](../sources.md#canonne22)):

- **Bhattacharyya coefficient and Hellinger distance.** Import
  [Hellinger.lean](../../CslibFrontier/Probability/Hellinger.lean). The definitions
  [`bhattacharyya`](../../CslibFrontier/Probability/Hellinger.lean#L135)
  (`∑' a, √((p a).toReal * (q a).toReal) ∈ [0, 1]`),
  [`hellingerSq`](../../CslibFrontier/Probability/Hellinger.lean#L139) (`1 - bhattacharyya p q`),
  and [`hellingerDist`](../../CslibFrontier/Probability/Hellinger.lean#L143)
  (`√(hellingerSq p q) ∈ [0, 1]`)—along with their symmetry, `[0, 1]` bounds, and definiteness
  (`= 0 ↔ p = q`)—apply to any `PMF α`, while the theorem API below assumes finite types
  `[Finite α]` / `[Fintype α]`. No competing `MetricSpace (PMF α)` instance is registered because
  `Cslib.Probability.PMF` already uses that slot for half-`L¹` `dist`;
  [`hellingerDist_triangle`](../../CslibFrontier/Probability/Hellinger.lean#L306) supplies the
  metric triangle inequality directly.
- **Total-variation comparison and `n`-fold i.i.d. tensorization (finite types).**
  [`hellingerSq_le_dist`](../../CslibFrontier/Probability/Hellinger.lean#L347) and
  [`dist_le_sqrt_two_mul_hellingerDist`](../../CslibFrontier/Probability/Hellinger.lean#L400) give
  `h²(p, q) ≤ dist p q ≤ √2 * h(p, q)` (with `tvDist` corollaries on `toMeasure`).
  [`bhattacharyya_pi`](../../CslibFrontier/Probability/Hellinger.lean#L428) and
  [`bhattacharyya_iid`](../../CslibFrontier/Probability/Hellinger.lean#L446) prove multiplicative
  tensorization, yielding the sample-complexity acceptance bound
  [`dist_iid_le_sqrt_two_mul_nat_mul_hellingerDist`](../../CslibFrontier/Probability/Hellinger.lean#L499):
  `dist (iid p n) (iid q n) ≤ √(2 * n) * hellingerDist p q`. Markov kernel and map data
  processing are [`hellingerDist_bind_le`](../../CslibFrontier/Probability/Hellinger.lean#L578) and
  [`hellingerDist_map_le`](../../CslibFrontier/Probability/Hellinger.lean#L597).
- **Pearson `χ²` divergence and Ingster / Le Cam mixture bounds (finite types).** Import
  [ChiSquare.lean](../../CslibFrontier/Probability/ChiSquare.lean).
  [`echiSquare`](../../CslibFrontier/Probability/ChiSquare.lean#L142) (`ℝ≥0∞`-valued
  `∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a`, with reference distribution `q`
  as the **second** argument matching `klDiv p.toMeasure q.toMeasure`) and real-valued
  [`chiSquare`](../../CslibFrontier/Probability/ChiSquare.lean#L148) (`(echiSquare p q).toReal`)
  are defined on any `PMF α`, together with nonnegativity and self-vanishing. All remaining
  theorems require `[Finite α]` / `[Fintype α]` (on countably infinite types, `p.support ⊆ q.support`
  alone does not imply finite divergence):
  [`echiSquare_ne_top_iff`](../../CslibFrontier/Probability/ChiSquare.lean#L167) equates finiteness
  to `p.support ⊆ q.support`, and real-valued theorems state `p.support ⊆ q.support` explicitly so
  `x / 0 = 0` never hides off-support mass. These cover tensorization
  ([`one_add_chiSquare_pi`](../../CslibFrontier/Probability/ChiSquare.lean#L299),
  [`one_add_chiSquare_iid`](../../CslibFrontier/Probability/ChiSquare.lean#L329)), TV upper bounds
  ([`dist_le_sqrt_chiSquare_div_two`](../../CslibFrontier/Probability/ChiSquare.lean#L366),
  [`tvDist_le_sqrt_chiSquare`](../../CslibFrontier/Probability/ChiSquare.lean#L384)), data
  processing ([`chiSquare_bind_le`](../../CslibFrontier/Probability/ChiSquare.lean#L401)), the
  mixture second-moment identity
  ([`one_add_chiSquare_bind_eq`](../../CslibFrontier/Probability/ChiSquare.lean#L505),
  [`one_add_chiSquare_bind_iid_eq`](../../CslibFrontier/Probability/ChiSquare.lean#L555)), and the
  comparison hierarchy `2 h² ≤ KL ≤ log (1 + χ²) ≤ χ²`
  ([`two_mul_hellingerSq_le_toReal_klDiv`](../../CslibFrontier/Probability/ChiSquare.lean#L573),
  [`toReal_klDiv_le_log_one_add_chiSquare`](../../CslibFrontier/Probability/ChiSquare.lean#L614),
  [`two_mul_hellingerSq_le_chiSquare`](../../CslibFrontier/Probability/ChiSquare.lean#L656)).

The checked clients in [HellingerChiSquare.lean](../../CslibFrontierTests/HellingerChiSquare.lean)
cover disjoint point masses (`echiSquare = ⊤`), rational Bernoulli pairs, the triangle inequality,
`pi`/`iid` tensorization, close Pythagorean-triple coins at `n = 10`, `map`/`bind` data
processing, `2 h² ≤ KL ≤ log (1 + χ²) ≤ χ²`, and an Ingster/Le Cam two-point mixture bound. Run
`scripts/build.sh CslibFrontierTests.HellingerChiSquare`.

## Select a hypothesis from a finite family

Import [Likelihood.lean](../../CslibFrontier/Probability/HypothesisSelection/Likelihood.lean),
[LeCamBirge.lean](../../CslibFrontier/Probability/HypothesisSelection/LeCamBirge.lean), and
[Tournament.lean](../../CslibFrontier/Probability/HypothesisSelection/Tournament.lean) to test pairs
of discrete distributions and localize an unknown distribution `p : PMF α` from i.i.d. samples
`iid p n` over a finite alphabet `α`.

- **Likelihood-ratio Chernoff and realizable MLE.**
  [Likelihood.lean](../../CslibFrontier/Probability/HypothesisSelection/Likelihood.lean) proves the
  weighted likelihood-ratio bound `Cslib.Probability.PMF.toOuterMeasure_mul_le_bhattacharyya_div_sqrt`,
  single-sample `toOuterMeasure_le_bhattacharyya`, and `n`-fold i.i.d. Chernoff bound
  `toOuterMeasure_iid_le_bhattacharyya_pow` (`≤ Real.exp (-n * hellingerDist p q ^ 2)` via
  `toOuterMeasure_iid_le_exp_hellingerDist`). Over any nonempty finite family `models` (`s : Finset ι`
  with `mle`, or `Fin M` with `mleFin`), `mle_hellingerDist_gt_le` and `mleFin_hellingerDist_gt_le`
  show that when `models i₀` generates the samples, maximum likelihood selects a model within
  Hellinger radius `r ≥ 0` except with probability at most `(M - 1) * Real.exp (-n * r ^ 2)`,
  giving sample complexity `Real.log (M / δ) / r ^ 2` (`mleFin_hellingerDist_ge_le_of_log`,
  [Canonne](../sources.md#canonne22), [Tsybakov](../sources.md#tsybakov09)). Bare MLE is not robust
  under misspecification: assigning zero probability to a single observed atom rejects a near-optimal
  model immediately.
- **Robust Le Cam–Birgé and Scheffé pairwise tests.**
  [LeCamBirge.lean](../../CslibFrontier/Probability/HypothesisSelection/LeCamBirge.lean) defines the
  clipped midpoint likelihood-ratio square root `birgeWeight q₀ q₁ a` (`√((q₀(a) + 2 q₁(a)) /
  (2 q₀(a) + q₁(a)))`, `1` where both vanish, always in `[1 / √2, √2]`) and `leCamBirgeTest`
  (comparing `∏ i, birgeWeight q₀ q₁ (x i) < 1`). Under any `p` with
  `10 * hellingerDist p q₀ ≤ hellingerDist q₀ q₁`, `leCamBirgeTest_false_le` bounds false
  rejection by `Real.exp (-n * hellingerSq q₀ q₁ / 25)` (`leCamBirgeTest_false_le_of_radius` gives
  `Real.exp (-4 * n * r ^ 2)` when `h(p, q₀) ≤ r` and `10 * r ≤ h(q₀, q₁)`, and `leCamBirgeTest_true_le`
  / `leCamBirgeTest_true_le_of_radius` are symmetric). For total variation, `scheffeTest` compares
  `empiricalMass (scheffeSet q₀ q₁) x` against `(q₀(A) + q₁(A)) / 2` and achieves error at most
  `Real.exp (-2 * n * γ ^ 2)` whenever `dist p q₀ + γ ≤ dist q₀ q₁ / 2` (`scheffeTest_false_le`,
  `scheffeTest_true_le`).
- **Parameter-free tournaments and finite covers.**
  [Tournament.lean](../../CslibFrontier/Probability/HypothesisSelection/Tournament.lean) defines two
  agnostic tournament selectors needing no prior bound on the approximation radius. `scheffeSelect`
  (`scheffeSelectFin`) minimizes `scheffeScore` (worst empirical discrepancy over challengers'
  Scheffé sets), achieving `dist p q_hat ≤ 3 * dist p q₀ + 2 * γ` simultaneously for all `q₀ ∈ s`
  except with probability at most `2 * M * (M - 1) * Real.exp (-2 * n * γ ^ 2)`
  (`scheffeSelect_prob_gt_le`, `scheffeSelectFin_ge_le_of_log`, `scheffeSelect_of_cover`).
  `birgeTournamentSelect` (`birgeTournamentSelectFin`) minimizes `maxDefeatRadius` across pairwise
  `leCamBirgeTest` matches: whenever some candidate satisfies `hellingerDist p (models i₀) ≤ r`, the
  output satisfies `hellingerDist p (models i_hat) ≤ 11 * r` except with probability at most
  `2 * (M - 1) * Real.exp (-4 * n * r ^ 2)` (`birgeTournamentSelect_prob_gt_le`,
  `birgeTournamentSelectFin_ge_le_of_log`), giving agnostic `11 * r` selection over any finite
  `r`-Hellinger cover (`birgeTournamentSelect_of_cover`). The `1/3`–`2/3` `birgeWeight` constants,
  one-sided `scheffeScore`, and tournament proofs are this library's formulation ([Le Cam 1973](../sources.md#lecam73),
  [Birgé 1983](../sources.md#birge83), and [Devroye–Lugosi 2001](../sources.md#devroyelugosi01) were
  not inspected beyond bibliographic metadata).

Model boundaries: all results are non-asymptotic bounds for discrete i.i.d. `PMF` tuples
`Fin n → α` on finite alphabets `α` and finite candidate families (`hs : s.Nonempty` or `NeZero M`),
assuming exact evaluation of `PMF` masses rather than continuous densities, unbounded alphabets, or
streaming space/time bounds. The checked clients in
[HypothesisSelection.lean](../../CslibFrontierTests/HypothesisSelection.lean) verify `bhattacharyya`
and `n = 20` Chernoff decay for `coin (1 / 5)` vs. `coin (4 / 5)`, `n = 64` sample complexity for
`mleFin` on three coins, a concrete zero-likelihood counterexample (`twoCoinsDetHalf` on nine `true`
and one `false` samples) where `mleFin` picks the wrong model while both `scheffeSelectFin` and
`birgeTournamentSelectFin` recover the near-optimal model, and probabilistic `scheffeSelectFin`,
`birgeTournamentSelectFin`, and finite-cover bounds under `coin (201 / 1000)` misspecification. Run
`scripts/build.sh CslibFrontierTests.HypothesisSelection`.

## Bound the mixing time of a finite Markov chain

Import [MarkovChain/Coupling.lean](../../CslibFrontier/Probability/MarkovChain/Coupling.lean). A chain
`P : Cslib.Probability.MarkovChain S` is a transition kernel `S → PMF S`, and `P ^ t` is its
`t`-step kernel, so `pow_add_apply` is Chapman–Kolmogorov. Prove a stationary law with
`IsStationary P π` (`π.bind P = π`), or more easily with detailed balance
`IsReversible P π` and `IsReversible.isStationary`. To get a chain with a given target,
[MarkovChain/Metropolis.lean](../../CslibFrontier/Probability/MarkovChain/Metropolis.lean) builds
`metropolis Ψ π` from any proposal chain `Ψ`, and `isReversible_metropolis` holds without
positivity or symmetry hypotheses. With `[Fintype S]`,
[MarkovChain/Mixing.lean](../../CslibFrontier/Probability/MarkovChain/Mixing.lean) defines
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
[PMF/EventBind.lean](../../CslibFrontier/Probability/PMF/EventBind.lean) gives a step-by-step induction. The
worked client is [BitString/LazyRandomWalk.lean](../../CslibFrontier/Probability/BitString/LazyRandomWalk.lean):
for the lazy hypercube walk `Cslib.BitString.lazyRandomWalk ι`, `mixingTime_lazyRandomWalk_le`
proves `t_mix(ε) ≤ ⌈n log n + n log ε⁻¹⌉`. The ceiling is necessary, as the `n = 1`, `ε = 2/5`
check shows.

When a coupling of all pairs is hard to build, use path coupling from
[MarkovChain/PathCoupling.lean](../../CslibFrontier/Probability/MarkovChain/PathCoupling.lean). Choose
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
[StatisticalDistance/OptimalCoupling.lean](../../CslibFrontier/Probability/StatisticalDistance/OptimalCoupling.lean),
and `dist_uniformOfFinset_le` bounds the distance between uniform laws on nearly equal sets. The
worked client is [MarkovChain/Coloring.lean](../../CslibFrontier/Probability/MarkovChain/Coloring.lean):
for Glauber dynamics on `q`-colorings with `q > 2Δ`, `mixingTime_glauberColoring_le` proves
`t_mix(ε) ≤ ⌈((q - Δ) / (q - 2Δ)) n (log n - log ε)⌉`. Its stationary law needs a proper coloring,
which `SimpleGraph.properColorings_nonempty` provides from greedy coloring
(`SimpleGraph.colorable_of_maxDegree_lt`). Proper colorings, allowed colors and the closure of
proper colorings under recoloring live in
[SimpleGraph/ProperColoring.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/ProperColoring.lean).

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
[Coloring/Ratio.lean](../../CslibFrontier/Probability/MarkovChain/Coloring/Ratio.lean) proves their
Lemma 14.16, `inv_exp_mul_le_card_frozenColorings_erase_div`: freezing one more vertex keeps at
least a `1 / (e q)` fraction of the colorings.
[Coloring/Count.lean](../../CslibFrontier/Probability/MarkovChain/Coloring/Count.lean) proves their
Theorem 14.14, `le_toOuterMeasure_coloringCountEstimator`: `coloringCountEstimator` multiplies,
over the `n` vertices, the fraction of `a` frozen-boundary samples in which one more vertex keeps
its color, and with `t` and `a` as in (14.21) it is within relative error `ε` of
`1 / |properColorings|` with probability at least `1 - η`. The concentration step is the generic
product estimator of [Product/Estimator.lean](../../CslibFrontier/Probability/Product/Estimator.lean):
`le_toOuterMeasure_productEstimate` needs each stage probability within relative error
`ε / (6 n)` of a target `r k ≥ b > 0` and `48 n ≤ 5 η ε² a b`, and proves it from the exact
mean and second moment of independent empirical frequencies by Chebyshev's inequality. Both
results concern only the law of `W`. The `n t a` Glauber updates are not charged in any cost
model, so this is not yet the fully polynomial randomized approximation scheme of Levin and Peres,
Remark 14.15.

The [checked clients](../../CslibFrontierTests/MarkovChain.lean) compute `d(t) = (2/3)(1/4)^t` and
`t_mix(1/4) = 1` exactly for a two-state chain with non-uniform stationary law, show that the flip
chain never mixes, compute a Metropolis acceptance probability, and give the hypercube instance
with `n = 1`. The [path-coupling checks](../../CslibFrontierTests/PathCoupling.lean) instantiate the
coloring bound on a single edge, show that the condition `ρ ≥ 1` off the diagonal cannot be
dropped, and compute the frozen colorings, the ratio of Lemma 14.16 and the frozen sampling time
on a single edge. The [counting checks](../../CslibFrontierTests/ColoringCount.lean) instantiate
Theorem 14.14 on a single edge, show that its sample sizes can always be met, and show that one
sample per stage never gives relative error `1 / 2` there. Run
`scripts/build.sh CslibFrontierTests.MarkovChain CslibFrontierTests.PathCoupling CslibFrontierTests.ColoringCount`.
A goal of the form `t_mix(ε) = k` needs both directions: `mixingTime_le_of_distToStationary_le`
for `≤`, and `(hπ : P.IsStationary π).mixingTime_le_iff` at `k - 1` for `≥`.

## Bound expected hitting and return times of a finite Markov chain

Import [MarkovChain/HittingTime.lean](../../CslibFrontier/Probability/MarkovChain/HittingTime.lean).
For `P : MarkovChain V` with `[Fintype V] [DecidableEq V]`, `survival P v t x` is the probability
`P_x(τ_v > t)` that the chain started at `x` avoids `v` at times `0, …, t`, defined by conditioning
on the first step. `hittingTime P v x = ∑' t, survival P v t x` is the expected hitting time
`E_x[τ_v]`, and `returnTime P v` is the expected return time `E_v[τ⁺_v]`. Both take values in
`ℝ≥0∞`: they are exact expectations, possibly `⊤`, not truncated sums, and need no summability
side conditions.

Work with them through these lemmas rather than unfolding the tail sums.
`hittingTime_eq_of_ne` and `returnTime_eq` are the first-step equations, and
`hittingTime_le_add` is the triangle inequality `E_x[τ_w] ≤ E_x[τ_v] + E_v[τ_w]`.
`mul_survival_le_hittingTime` is Markov's inequality `(t + 1) P_x(τ_v > t) ≤ E_x[τ_v]`, which
turns an expectation bound into a bound on the probability that a `t`-step walk misses `v`.
Kac's formula `mul_returnTime_eq` needs a stationary measure `π : V → ℝ≥0∞`, given as
`∀ y, ∑ x, π x * P x y = π y`, and finiteness of `∑ x, π x * hittingTime P v x`; it gives
`π v * returnTime P v = ∑ x, π x`. `IsStationary.mul_returnTime_eq_one` is the version for a
stationary `PMF`. Finiteness comes from `hittingTime_ne_top`: give a set `S` closed under
transitions of positive probability from which `v` is reachable along such transitions. Pass
`Set.univ` for an irreducible chain, or a connected component.

[MarkovChain/RandomWalk.lean](../../CslibFrontier/Probability/MarkovChain/RandomWalk.lean) is the
worked client. `randomWalk G` is the simple random walk on a finite `SimpleGraph`, and an
isolated vertex stays put, so it is a chain for every graph. The degrees are stationary
(`sum_degree_mul_randomWalk`), so Kac's formula gives `degree_mul_returnTime_randomWalk`,
`deg v * E_v[τ⁺_v] = 2 |E|`, for a connected graph. Then `hittingTime_randomWalk_add_degree_le`
proves `E_u[τ_v] + deg v ≤ 2 |E|` for every edge (Goldreich, Exercise 6.19), and
`hittingTime_randomWalk_le_dist_mul` proves `E_u[τ_v] ≤ dist(u, v) · 2 |E|`. The
[checked clients](../../CslibFrontierTests/RandomWalkHitting.lean) state Exercise 6.19 in the
source's form, compute `E_0[τ_1] = 1` and `E_0[τ⁺_0] = 2` on a single edge (so the edge bound is
an equality there), and instantiate it on a triangle. Run
`scripts/build.sh CslibFrontierTests.RandomWalkHitting`.

For regular multigraphs, import
[MarkovChain/RotationMap.lean](../../CslibFrontier/Probability/MarkovChain/RotationMap.lean).
`G.randomWalk` follows a uniformly random edge label of `G : RotationMap V D`, with
`randomWalk_apply` giving `edgeCount x y / |D|`. Use it when the statement counts label
sequences, as Arora and Barak's Chapter 7 does: `survival_randomWalk_mul_pow` identifies
`survival` with the fraction of label sequences `k : Fin T → D` whose `walkAt` avoids the target.
The uniform law is the unique stationary law on a connected graph
(`isStationary_randomWalk_iff`), from the maximum principle `eq_of_forall_sum_edgeCount_mul_eq`
in [Expander/Harmonic.lean](../../CslibFrontier/Foundations/Combinatorics/Expander/Harmonic.lean),
which needs no Markov-chain import. Also, `returnTime_randomWalk_eq_card` gives the expected return
time as the size of the component. `hittingTime_randomWalk_le_length_mul` bounds `E_u[τ_v]` by
`ℓ |D| n` along a path of length `ℓ` in `G.toSimpleGraph`. With `|D| ≤ n`,
`hittingTime_randomWalk_le_hundred_mul` and `ten_mul_card_filter_walkAt_ne_le` give the
textbook `100 k n²` and `1000 n³`-step statements.
[Expander/Visits.lean](../../CslibFrontier/Foundations/Combinatorics/Expander/Visits.lean)
adds the law of large numbers for visit counts without aperiodicity. It is a graph module and needs
no Markov-chain import. `eventually_visits_mem_Icc` bounds the fraction of label sequences whose
`visits u v` fall outside `[(1 - ε) t / n, (1 + ε) t / n]`, and `visits_eq` unfolds `visits` to
the number of times `1, …, t` at which `walkAt` is at `v`. Its reusable step is `exists_abs_sum_walk_pow_le`, uniform
Cesàro convergence `∑_{j < N} Pʲ f = o(N)` for `f` of total `0` on a connected graph, which comes
from Mathlib's mean ergodic theorem applied to `walkEuclidean`. The
[checked clients](../../CslibFrontierTests/RegularRandomWalk.lean) restate them in source form and
compute the return time `2` on a single edge; run
`scripts/build.sh CslibFrontierTests.RegularRandomWalk`. If a proof needs `∑ y, P x y = 1`, use
`sum_apply`. Do not convert to `ℝ` before the finiteness lemmas are available, since `toReal`
sends `⊤` to `0`.

## Test for a perfect matching with a random determinant

Import [Matching/Edmonds.lean](../../CslibFrontier/Algorithms/Matching/Edmonds.lean). A bipartite
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
[MvPolynomial/SchwartzZippel.lean](../../CslibFrontier/Foundations/Data/MvPolynomial/SchwartzZippel.lean):
`MvPolynomial.schwartz_zippel_totalDegree_fintype` extends Mathlib's Schwartz–Zippel lemma from
the variables `Fin n` to any finite type, and `MvPolynomial.totalDegree_det_le` bounds the total
degree of a determinant of polynomials. Use them for other symbolic-determinant tests. The same
module has two consequences. `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card` finds a
nonvanishing point of `S ^ σ` when the total degree is below `|S|`; the `exists_det_…_ne_zero`
theorems use it. `MvPolynomial.card_filter_eval_eq_zero_mul_card_le` is the counting form over a
finite domain, `#zeros * q ≤ d * q ^ n`. For one variable under a uniform `PMF`,
[PMF/PolynomialAgreement.lean](../../CslibFrontier/Probability/PMF/PolynomialAgreement.lean) has
`Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_of_eval_eq`: two distinct polynomials of
degree at most `d` agree at a uniform point with probability at most `d / |R|`. The round
soundness proofs of the sum-check and GKR protocols use it.

The [checked clients](../../CslibFrontierTests/EdmondsMatching.lean) compute the `2 × 2`
determinant of the complete graph, apply the test to a graph whose right vertex `1` is
unmatched, and show that values from the one-element set `{0}` miss the matching of a single edge.
The hypothesis `|V| < |S|` is not sharp. `exists_det_edmondsEval_ne_zero` applies Mathlib's
`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` with the total degree `|V|` as a crude bound on
each variable's degree. The determinant has degree at most `1` in each variable, so the same lemma
shows that over an integral domain any `S` with two elements detects a perfect matching (not
formalized). Run
`scripts/build.sh CslibFrontierTests.EdmondsMatching`.

For a general graph, import [Matching/Tutte.lean](../../CslibFrontier/Algorithms/Matching/Tutte.lean).
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
[SkewDeterminant.lean](../../CslibFrontier/Foundations/LinearAlgebra/Matrix/SkewDeterminant.lean)
(odd cycles cancel in a skew-symmetric determinant, via `Equiv.Perm.reverseCycle` in
[ReverseCycle.lean](../../CslibFrontier/Foundations/GroupTheory/Perm/ReverseCycle.lean); an alternating
matrix of odd order has determinant `0`), and `SimpleGraph.exists_isPerfectMatching_of_perm` in
[PermMatching.lean](../../CslibFrontier/Foundations/Combinatorics/SimpleGraph/PermMatching.lean) (a
permutation along the edges with only even cycles gives a perfect matching). The
[checked clients](../../CslibFrontierTests/TutteMatching.lean), a `module`, compute the determinant
`r²` of a single edge and its `2 / 3` probability bound over `{0, 1, 2}`, extract and detect a
perfect matching of `K₄` from the rotation of `Fin 4`, show that the triangle's Tutte matrix is
singular at all values and that the star `K₁,₃` has the zero Tutte polynomial, and show that the
zero-diagonal hypothesis is needed over `ZMod 2`. Run
`scripts/build.sh CslibFrontierTests.TutteMatching`.

To find the matching rather than only detect it, import
[Matching/MVV.lean](../../CslibFrontier/Algorithms/Matching/MVV.lean), the algebraic core of
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
[checked clients](../../CslibFrontierTests/MVVMatching.lean), a `module`, recover the identity
matching on `K₂,₂` from the determinant `-12` and show that equal weights make the determinant
vanish. Run `scripts/build.sh CslibFrontierTests.MVVMatching`.

## Compose local embeddings and extract a strategy

Import [CorrelatedSampling/Embeddability.lean](../../CslibFrontier/Probability/CorrelatedSampling/Embeddability.lean)
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

Import [TwoProverGame.lean](../../CslibFrontier/Computability/PCP/TwoProverGame.lean) to use an
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

The [embedding clients](../../CslibFrontierTests/Embeddability.lean) compose two exact embeddings
(copy, negate, forget the copies), apply the product-form criterion, and draw shared randomness
from `ULift.{2} Bool`. The [CHSH client](../../CslibFrontierTests/TwoProverGame.lean) extracts a
strategy from the one-fold repetition with `C = ∅`, which bounds every strategy of `chsh.pow 1`
by `chsh.value`. Run `scripts/build.sh CslibFrontierTests.Embeddability CslibFrontierTests.TwoProverGame`.
The next three sections supply the embedding premise at each free coordinate, through the
coordinate embedding of Lemma 6.4;
[the next section](#model-the-coordinates-of-the-parallel-repetition-proof) sets up its random
variables. [Bound the value of a parallel repetition](#bound-the-value-of-a-parallel-repetition)
states Lemma 6.4 as one theorem and proves the parallel repetition theorem.

## Model the coordinates of the parallel repetition proof

Import [ParallelRepetition/CoordinateModel.lean](../../CslibFrontier/Computability/PCP/ParallelRepetition/CoordinateModel.lean)
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

The [coordinate-model clients](../../CslibFrontierTests/RepetitionCoordinateModel.lean) compute
`pairGiven` and a sample mass for the CHSH questions, derive from (6.5) that the redrawn law is
exact when `C = ∅`, remove the bit condition from the law of `S`, and pass an embedding into the
model's law to `winProbOn_insert_le`. Run
`scripts/build.sh CslibFrontierTests.RepetitionCoordinateModel`. The next section carries the proof
from (6.5) to the first stage of the embedding.

## Embed the questions at a free coordinate

Import [ParallelRepetition/Embedding.lean](../../CslibFrontier/Computability/PCP/ParallelRepetition/Embedding.lean)
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
[embedding clients](../../CslibFrontierTests/RepetitionEmbedding.lean) do this, and check that with
`C = ∅` every coordinate has the law of `G.questions` and the first stage is exact. Run
`scripts/build.sh CslibFrontierTests.RepetitionEmbedding`.
[The next section](#extend-the-coordinate-embedding-to-the-question-tuples) proves the second
stage (6.17)–(6.19), which adds the remaining questions through Lemma 5.4, and composes the two
stages.

## Extend the coordinate embedding to the question tuples

Import [ParallelRepetition/Factorization.lean](../../CslibFrontier/Computability/PCP/ParallelRepetition/Factorization.lean)
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

The [factorization clients](../../CslibFrontierTests/RepetitionFactorization.lean) pass the distance
bounds of Corollary 5.3 for `J` through the second stage to `winProbOn_insert_le`. In the one-fold
repetition with `C = ∅`, `S` is trivial and the first stage is exact, so they bound the probability
of winning the coordinate by `G.value`. Run `scripts/build.sh CslibFrontierTests.RepetitionFactorization`.
With the previous section, every free coordinate `j` thus supplies the premise of
`winProbOn_insert_le` with error `ε j`. [The next section](#bound-the-value-of-a-parallel-repetition)
states Lemma 6.4 as one theorem, chooses the coordinate of Lemma 6.5 and proves the parallel
repetition theorem.

## Bound the value of a parallel repetition

Import [ParallelRepetition.lean](../../CslibFrontier/Computability/PCP/ParallelRepetition.lean) for
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
cardinalities as a power of two and apply `Real.logb_rpow`, or `Real.logb_two_pow` from
[Logb.lean](../../CslibFrontier/Foundations/Analysis/SpecialFunctions/Logb.lean) when the
exponent is a natural number. For CHSH, `|A| |B| = 4` and the
exponent is `n / 2`. [CHSH.lean](../../CslibFrontier/Computability/PCP/TwoProverGame/CHSH.lean)
proves that CHSH has value `3/4` (`TwoProverGame.value_chsh`), and the [parallel repetition clients](../../CslibFrontierTests/ParallelRepetition.lean)
derive `(3/4)^n ≤ v(CHSHⁿ) ≤ (1 - (1/4)³ / 6000)^{n / 2}`. They also show that the value of the
repetition tends to zero for every game of value below one, and apply Lemma 6.5 with nothing
conditioned, which gives a coordinate won with probability at most `G.value`. Run
`scripts/build.sh CslibFrontierTests.ParallelRepetition`.

For Label Cover, import
[LabelCover/Repetition.lean](../../CslibFrontier/Computability/PCP/Approximation/LabelCover/Repetition.lean)
and open `Cslib.PCP.Encoded`. For an instance `g : Graph (β → γ)` with `[Fintype β] [Fintype γ]`
and `[DecidableEq γ]`, apply `LabelCoverRepetition.one_sub_unsatVal_pow_le hpar hβγ hε k`. Its
premises are that the instance has no parallel edges (`hpar : g.NoParallelEdges`, decidable), that
`2 ≤ Fintype.card β * Fintype.card γ`, and `hε : ε ≤ (g.toGraph projectionEval).unsatVal`. The
conclusion bounds the satisfied proportion `1 - ((pow k g).toGraph projectionEval).unsatVal` of the
`k`-fold repetition `LabelCoverRepetition.pow k g`. The bound does not require the edge list to be
nonempty or well formed. The vertex numbers of the repetition grow like `(n + 1) ^ (2 ^ k)`
(`LabelCoverRepetition.vertices_pow_le`), so its polynomial-time compilation holds for each fixed
`k` only. The [Label Cover repetition clients](../../CslibFrontierTests/LabelCoverRepetition.lean)
compute the numbering of a two-fold repetition, separate instances without parallel edges from
instances with them, and bound the repetitions of an instance of value `1/2` by
`(1 - (1/2)³ / 6000)^{k / 2}`.

For a hardness result, import
[LabelCover/SmallSoundness.lean](../../CslibFrontier/Computability/PCP/Approximation/LabelCover/SmallSoundness.lean).
`polyTimeReducible_GapTwoCSP_GapLabelCover_pow a b hab encA hε hε1 hk` reduces
`GapTwoCSP α (1 - ε)` to Label Cover over `k`-tuples, for any finite alphabet `α` with two
distinct symbols, `0 < ε ≤ 1` and `0 < k`. The soundness is
`(1 - (ε / 2)³ / 6000)^{k / log₂ (|α|² |α|)}`. Apply `Graph.deloop` before
`LabelCoverIncidence.reduce`: loop removal makes a binary CSP instance loopless without changing
its value (`Graph.isLoopless_deloop`, `Graph.unsatVal_deloop`), and the incidence reduction of a
loopless instance has no parallel edges (`LabelCoverIncidence.noParallelEdges_reduce`). Compose with a hard source through
`PromiseProblem.NPHard.trans`, as `GapLabelCover_npHard_pow` does with `GapTwoCSP_npHard`, and
weaken the soundness with `PromiseProblem.NPHard.mono`, as `exists_GapLabelCover_npHard` does. The
[small-soundness clients](../../CslibFrontierTests/LabelCoverSmallSoundness.lean) remove a concrete
loop, show that the incidence reduction of a loop has parallel edges and has none after loop
removal, and instantiate both hardness theorems. Run
`scripts/build.sh CslibFrontierTests.LabelCoverRepetition CslibFrontierTests.LabelCoverSmallSoundness`.
For constant-factor Set Cover inapproximability from `exists_GapLabelCover_npHard` and its
`c * log n` soundness gap, see
[LundYannakakis.lean](../../CslibFrontier/Computability/PCP/Approximation/SetCover/LundYannakakis.lean)
and [Set Cover approximation hardness](../algorithms-and-memory/approximation-algorithms.md#set-cover-approximation-hardness).
Håstad's reductions from Label Cover remain open
([#886](https://github.com/cslib-community/cslib-frontier/issues/886)).

## Project a continuous Gaussian density

Import [Gaussian/Standard.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Standard.lean)
when a calculation starts from the density `exp (-π * ‖x‖² / s²) / s^dim` relative to
ambient volume. For `s > 0`, `gaussianWeight_withDensity_eq_map_stdGaussian` identifies
this actual measure with `stdGaussian E` scaled by `s / √(2π)`. It reuses the normalized
`Measure.withDensity` construction; it does not introduce another Gaussian measure.

Apply `gaussianWeight_withDensity_map_inner s hs z` to identify the law of `⟪z, x⟫`
as `gaussianReal 0 (((s * ‖z‖)^2 / (2 * Real.pi)).toNNReal)`. The theorem includes
`z = 0` and dimension zero, where the law is a point mass. The
[checked clients](../../CslibFrontierTests/GaussianStandard.lean) recover the standard law
at width `√(2π)` and compute variance `32/π` at width `4` with scalar projection `2`.
These are analytic measure identities. Projection of a discrete-coset Gaussian convolution
and its mod-one error bound are proved in [#2734](https://github.com/cslib-community/cslib-frontier/issues/2734);
no sampler or runtime certificate follows from this identification.

## Describe a discrete Gaussian law

Import [Gaussian/Discrete.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Discrete.lean)
for `ZLattice.discreteGaussian L s hs c`, a PMF on a discrete `ℤ`-submodule `L` of a
finite-dimensional real normed space. Supply `hs : 0 < s`; the center `c` is any ambient
point. `summable_gaussianWeight` proves convergence of the infinite lattice sum, and
`gaussianMass_pos` proves its strict positivity. `discreteGaussian_apply` gives each
probability as `exp (-π * ‖z - c‖² / s²)` divided by that total mass. No full-rank assumption
is needed.

Use `map_add_discreteGaussian` to move the law along a lattice translation, and
`support_discreteGaussian` to discharge point-support obligations. The
[checked examples](../../CslibFrontierTests/DiscreteGaussian.lean) use the infinite integer
lattice at the off-lattice center `1/2`, distinguish its law from a point mass, and check the
zero lattice. This is a mathematical distribution, with no efficient sampler or smoothing
bound. Regev's quantum worst-case/average-case reduction remains open in
[issue #1213](https://github.com/cslib-community/cslib-frontier/issues/1213).

For a quantitative radius estimate, import
[Gaussian/DiscreteTail.lean](../../CslibFrontier/Foundations/Probability/Gaussian/DiscreteTail.lean).
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
[Gaussian/Periodization.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Periodization.lean).
`ZLattice.continuous_gaussianMass L s hs` proves continuity of the normalizer for `hs : 0 < s`.
The proof establishes summable sup norms of the lattice translates on every compact set, so
the continuous sum comes from local uniform convergence.

For other decaying functions, import
[Lattice/Periodization.lean](../../CslibFrontier/Foundations/Analysis/Lattice/Periodization.lean).
Supply a bundled continuous map `f : C(E, F)` into a complete normed additive group, a real exponent
`b > Module.finrank ℤ L`, and `f =O[cocompact E] (fun x ↦ ‖x‖ ^ (-b))`.
`ZLattice.continuous_tsum_translate` proves continuity of `x ↦ ∑' z : L, f (x + z)`;
`continuous_automorphize` proves continuity of Mathlib's existing `QuotientAddGroup.automorphize`
on the quotient of `E` by `L.toAddSubgroup`. For a Schwartz function, import
[Lattice/Schwartz.lean](../../CslibFrontier/Foundations/Analysis/Lattice/Schwartz.lean) and use
`SchwartzMap.continuous_automorphize` directly. The
[checked clients](../../CslibFrontierTests/LatticePeriodization.lean) include a nonzero Schwartz
bump, an infinite integer lattice, a skew two-dimensional basis, and a rank-zero lattice on
an off-center compact interval. For Fourier coefficient identification, see
[the quotient-integral workflow below](#unfold-a-lattice-fourier-coefficient). For the full
formula, use the Poisson API below.

## Apply lattice Poisson summation

Import [Lattice/Poisson.lean](../../CslibFrontier/Foundations/Analysis/Lattice/Poisson.lean).
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
[Gaussian/Poisson.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Poisson.lean) and apply
`ZLattice.gaussianMass_eq_tsum_dual L s hs c` with `hs : 0 < s` and any center `c`.
This is an equality in `ℂ`: the real mass equals `s^dim / covolume L` times the dual sum of
`gaussianWeight (1 / s) w` multiplied by `exp(-2πi * inner c w)`.
The negative phase comes from evaluating the periodization at `-c`. The theorem includes
dimension zero and arbitrary full-rank bases, including skew bases. It proves the required
Gaussian integrability and Fourier summability; it does not assume a Poisson identity.

The complete [LatticePoisson.lean examples](../../CslibFrontierTests/LatticePoisson.lean) apply
both endpoints to a skew basis of covolume `2`, check opposite character signs at a nonzero
frequency, and check the dimension-zero covolume and mass of `1`. From the repository root,
run `scripts/build.sh CslibFrontierTests.LatticePoisson` to check these clients. If the
full-rank instance is missing, start from the basis-spanned lattice in these examples;
continuity alone also applies to lower-rank lattices, but this Poisson formula needs full rank.
For centered truncation and uniform shifted-mass control, use the bounds below.
Quotient-distribution consequences, efficient sampling and Regev's quantum reduction remain open.

## Bound a centered discrete Gaussian

Import [Gaussian/CenteredTail.lean](../../CslibFrontier/Foundations/Probability/Gaussian/CenteredTail.lean).
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

The [complete checked clients](../../CslibFrontierTests/DiscreteGaussianCenteredTail.lean)
use the infinite lattice generated by `2` in the real line. They instantiate mass scaling,
equal widths, and width `2` with radius `2`; the lattice point exactly at that radius is
excluded by the strict event. They also check the dimension-zero empty-event probability.
Run `scripts/build.sh CslibFrontierTests.DiscreteGaussianCenteredTail` from the repository root.
A missing full-rank instance can be supplied by the basis-spanned construction in that file.
For a nonzero center, the earlier tail bound retains its explicit normalizer ratio.

## Control Gaussian mass uniformly over centers

Import [Gaussian/Smoothing.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Smoothing.lean).
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

The [checked clients](../../CslibFrontierTests/DiscreteGaussianShiftBounds.lean) use `2ℤ`,
its dual gap `1/2`, width `2`, error `1/2`, and center `1`, which is outside the lattice.
They also check the empty nonzero dual sum and exact normalized mass in dimension zero.
Run `scripts/build.sh CslibFrontierTests.DiscreteGaussianShiftBounds` from the repository root.
A width too small to satisfy the sufficient condition can still use the unconditional
actual-dual-error bound. The [quotient probability](#compare-an-actual-gaussian-quotient-distribution-with-uniform-measure)
and [coset-convolution](#add-continuous-gaussian-noise-to-a-coset-gaussian) consequences are
described below; a minimum smoothing parameter and efficient sampler remain separate.

## Condition a discrete Gaussian on coefficient residues

Import [Gaussian/CoefficientFiber.lean](../../CslibFrontier/Foundations/Probability/Gaussian/CoefficientFiber.lean).
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
assumed uniform. The [checked clients](../../CslibFrontierTests/DiscreteGaussianCoefficientFiber.lean)
use the infinite lattice `2ℤ`, composite modulus `6`, residue `1`, and center `1/2`:
the representative is `2`, the scalar lattice contains `12`, and the conditional center is
`-3/2`. Rank-zero and dimension-zero cases are also checked. Run
`scripts/build.sh CslibFrontierTests.DiscreteGaussianCoefficientFiber` to check the clients.

This is the exact conditioning step used in Regev's Lemma 3.11, not its joint LWE sample
bound or an efficient sampling procedure. The [joint experiment](https://github.com/cslib-community/cslib-frontier/issues/2767)
and the [full reduction](https://github.com/cslib-community/cslib-frontier/issues/1213) remain separate.

## Fold a density onto a quotient

Import [QuotientDensity.lean](../../CslibFrontier/Foundations/MeasureTheory/Group/QuotientDensity.lean)
to push a nonnegative density through a countable additive-subgroup quotient. Given a measurable
`f : G → ℝ≥0∞`, measurable subgroup translations, an invariant ambient measure `μ`, and
`hF : IsAddFundamentalDomain Γ.op F μ`, apply
`QuotientAddGroup.map_withDensity_eq_withDensity_automorphize hF hf`. It identifies the image of
`μ.withDensity f` with the density `QuotientAddGroup.automorphize f` relative to the image of
`μ.restrict F`. At the coset of `x`, that density sums `f (x + γ)` over subgroup elements.

The theorem derives measurability on the canonical quotient measurable space and allows infinite
values and infinite total mass. It does not require a measurable fundamental domain beyond the
null-measurability already in `hF`. The [checked clients](../../CslibFrontierTests/QuotientDensity.lean)
cover bottom and top subgroups, a two-element group, infinite densities on a null measure, and
the Borel measurable space of a discrete lattice quotient. The following Gaussian consumer
proves the required probability normalizations before applying a distance formula.

## Compare an actual Gaussian quotient distribution with uniform measure

Import [Gaussian/Quotient.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Quotient.lean).
Let `L` be a discrete full-rank lattice in a finite-dimensional real inner-product space `E`,
let `n = Module.finrank ℝ E`, and take `s > 0`. Use `q = QuotientAddGroup.mk`, the
canonical map to the quotient by `L.toAddSubgroup`, and an actual fundamental domain
`hF : IsAddFundamentalDomain L.toAddSubgroup.op F volume`. The opposite subgroup acts by right
translation, the convention of Mathlib's quotient measures, while the lattice APIs give
fundamental domains for `L` itself. In a commutative group the two have the same fundamental
domains, and `MeasureTheory.isAddFundamentalDomain_op_iff` from
[FundamentalDomain.lean](../../CslibFrontier/Foundations/MeasureTheory/Group/FundamentalDomain.lean)
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

The [checked clients](../../CslibFrontierTests/DiscreteGaussianShiftBounds.lean) reuse `2ℤ`
with covolume `2`, width `2`, and its proved dual gap `1/2`. They check both probability
normalizations, the actual density at the off-lattice representative `1`, full-L1 distance
at most `1/2`, and eventual small error. In dimension zero, the two actual measures are
proved equal and their distance is zero. Run
`scripts/build.sh CslibFrontierTests.DiscreteGaussianShiftBounds` from the repository root.

## Convolve a singular law with a density

Import [ConvolutionDensity.lean](../../CslibFrontier/Foundations/MeasureTheory/Group/ConvolutionDensity.lean).
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

The [checked clients](../../CslibFrontierTests/ConvolutionDensity.lean) translate an actual
Gaussian by an atom and recover the variance-two Gaussian from two variance-one inputs.
A noncommutative permutation-group example checks the order of translation; infinite-density
and zero-input cases check the absence of hidden finiteness premises. Run
`scripts/build.sh CslibFrontierTests.ConvolutionDensity` from the repository root.
The [lattice Gaussian convolution bound](https://github.com/cslib-community/cslib-frontier/issues/2707)
below supplies its actual discrete weights, completion of the square and quantitative error proof.

## Add continuous Gaussian noise to a coset Gaussian

Import [Gaussian/Convolution.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Convolution.lean).
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
The [checked clients](../../CslibFrontierTests/DiscreteGaussianConvolution.lean) use `L = 2ℤ`,
`u = 1/2`, `r = 3`, `s = 4`, `t = 5`, `a = 1/2`, and a proved numerical criterion giving
distance at most `4/7`. They also prove equality of the actual measures in dimension zero.
Run `scripts/build.sh CslibFrontierTests.DiscreteGaussianConvolution` to check them.

This proves the bounded analytic Claim 3.9 consequence with an explicit sufficient width
criterion. The scalar and mod-one laws are handled below; the minimum smoothing parameter,
search-LWE experiment, efficient finite-precision sampling and quantum implementation remain
separate.

## Project the coset experiment and reduce modulo one

Import [Gaussian/Projection.lean](../../CslibFrontier/Foundations/Probability/Gaussian/Projection.lean)
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
The [checked clients](../../CslibFrontierTests/DiscreteGaussianProjection.lean) use `2ℤ`,
off-lattice shift `1/2`, `r = 3`, `α = 8` and projection vector `2`. They prove the dual gap
`1/2` and numerical criterion at `ε = 1/7`, yielding distance at most `4/7` on both the
real line and the circle. The input scalar noise has variance `32/π`, and the comparison
has variance `50/π`.

The convention is Regev's full-L1 distance from printed page 13, with range `[0,2]`.
The source's mod-one Gaussian sampling law is represented by its actual measure pushforward;
its periodic-density series, the joint LWE sample law in Lemma 3.11, efficient sampling,
finite precision and the quantum reduction remain separate work.

## State a probability and sample uniformly

Import [Notation.lean](../../CslibFrontier/Languages/Probabilistic/Notation.lean) and
`open Probability`. Public statements then write probabilities the way the textbooks do:

- A named advantage is `ℝ≥0`, defined through `Experiment.advantage`, `Experiment.succProbability`
  or the `Game` API, because `Negligible`, `Indistinguishable` and the reductions take `ℝ≥0`. As
  real numbers they are `|Pr[e₀] - Pr[e₁]|` and `Pr[e]`; rewrite with `Experiment.coe_advantage`
  and `Experiment.coe_succProbability` (plain `simp` also proves them, so they are not `simp` lemmas).
- Every other probability is `Pr[e] : ℝ`: one-sided bounds `Pr[e] ≤ 1 / q`, exact values
  `Pr[e] = 1 / 2`, hop differences and biases. A statement does not write
  `(ProbComp.eval e true).toReal`, `ProbComp.eval e true ≤ …` in `ℝ≥0∞`,
  `Game.succProbability (ProbComp.eval e)` or a real-cast `Game.advantage` of two laws.
- An exact hop that is an equality of distributions stays one (`ProbComp.eval G₁ = ProbComp.eval G₂`,
  or `G₁ = G₂` by `rfl`): it is stronger than `Pr[G₁] = Pr[G₂]` and works with `rw`.
- `ℝ≥0∞` masses stay inside `PMF` algebra: private lemmas and `eval_*`/`bind_apply_*` facts whose
  consumers are other `PMF` proofs.

Sample uniformly with `$ᵗ α`, the textbook `a ←$ α`: a program reads `let a ← $ᵗ ZMod q`. It is
notation for `ProbComp.uniform α` and adds no constant, so `ProbComp.eval_uniform`, `pmf_norm` and
every other lemma about `ProbComp.uniform` apply unchanged, and goals print `ProbComp.uniform α` as
`$ᵗ α`. Its argument is an application at most, so a product type needs parentheses:
`$ᵗ (ZMod q × Bool)`. The SPDZ MAC-check bounds in
[SPDZ.lean](../../CslibFrontier/Crypto/Protocols/MPC/SPDZ.lean) use both
(`probability_macCheckSoundnessGame_le : Pr[macCheckSoundnessGame p T err deltaShift] ≤ 2 / p`), and the
[checked examples](../../CslibFrontierTests/ProbabilityNotation.lean) cover the elaborated term,
its printing inside `do` blocks and `simp`.

## Normalize the law of a program

To compute with `ProbComp.eval` of a `do` block, import
[Norm.lean](../../CslibFrontier/Languages/Probabilistic/Norm.lean) in the proof and call
`simp only [pmf_norm]`. It rewrites the law into right-nested `PMF.bind`s, with returned values
substituted and maps pushed into the continuations: the shape that `PMF.bind_congr_on_support`,
`PMF.bind_apply` and the support lemmas expect. The set is curated, so later steps may rely on its
normal form; it does not unfold support membership or probability masses. The checked examples in
[PMFNorm.lean](../../CslibFrontierTests/PMFNorm.lean) show the normal form of each kind of term.
To prove that two normal forms differ only in the order of independent samples, use `pmf_swap`
([Reorder independent samples](../design-and-assurance/automation.md#reorder-independent-samples)).

## Bind a program inside a distribution

A game that has to stay a `PMF`, for example because its setup law is not sampleable, can bind
programs directly once it imports
[Lift.lean](../../CslibFrontier/Languages/Probabilistic/Lift.lean). Write
`let ((x, y), s) ← A.choose ()` instead of `let ((x, y), s) ← ProbComp.eval (A.choose ())`, and end
the block with `A.guess s c` instead of `ProbComp.eval (A.guess s c)`. The lift is `ProbComp.eval`,
so the lifted definition equals the explicit one by `rfl`. `simp only [pmf_norm]` rewrites each lift
back to `ProbComp.eval`, after which the existing law lemmas apply. Use `ProbComp.liftM_eq_eval`
for a bare `rw` after `unfold`. With the import, any program passed where a distribution is
expected is lifted silently: `Game.advantage program μ` elaborates. So public statements keep
naming `ProbComp.eval`, `Pr[e]` or `Experiment` explicitly, and the lift is for definition bodies.
`Pr[e]` on a program still elaborates to `(ProbComp.eval e true).toReal`. A computational
experiment that is a program throughout stays a `ProbComp Bool`. The
[checked examples](../../CslibFrontierTests/ProbabilisticLift.lean) prove a chooser/guesser game
equal to its explicit form both ways. Run `scripts/build.sh CslibFrontierTests.ProbabilisticLift`.

## Invert a support membership

A proof that starts from `h : x ∈ m.support` usually needs the intermediate results that produced
`x`. Import [SuppCases.lean](../../CslibFrontier/Tactic/SuppCases.lean) in the proof and call
`supp_cases h with ⟨a, ha, b, hb, rfl⟩`. It rewrites `h` through every `bind`, `map`, `pure`,
`if` and uniform draw of `m`, for a `PMF`, `ProbComp.eval`, or `OracleComp.supportWith` and
`OracleComp.support` (so `ProbComp`), into existentials in program order, then applies the
`rcases` pattern. A uniform draw contributes only its witness, a returned pair is split into its
components, and a conditional becomes a disjunction, so a pattern such as `⟨-, h⟩ | ⟨-, h⟩` splits
it. Without `with`, `supp_cases h` destructures completely, substitutes every equation that has a
local variable on one side and closes the goal when two different constructors are equated, such
as `false = true`; the names it introduces are inaccessible, so use this form when the rest of the
proof refers to hypotheses only by type, through `‹_›`, `assumption` or `omega`.

When `m` is a definition or a local `let`, pass it as in `supp_cases h [realRoundHandler]` or
`supp_cases h [ν_det]`; the same list takes a hypothesis that decides a condition. The tactic fails
when `h` is not a support membership, and when `supp_norm` cannot rewrite it, usually because
something needs unfolding first. `simp only [supp_norm] at h` gives the rewritten form without
destructuring it. Membership in a `dite` and an `ExecRand` derivation are not covered; induct on
the derivation and call `supp_cases` in each case, as the proofs in
[Structured.lean](../../CslibFrontier/Computability/WordRAM/Randomized/Structured.lean) do. The
checked examples, including the failure messages, are in
[SuppCases.lean](../../CslibFrontierTests/SuppCases.lean).

## Certify a closed randomized routine

Use `IsPPTOn input output program` when the required conclusion is a uniform, strict polynomial-time implementation on encoded types. The encodings are embeddings into bit lists. One finite-control fair-coin machine and one polynomial clock must work for every input, with exact equality of encoded output laws. Output writing is charged. This is the contract to request before proving a probabilistic routine efficient.

<!-- worked-example -->

**Worked example: Compose a fair coin with a certified callback**

**Goal:** certify a coin-sampling routine, then a scan whose deterministic callback has a supplied polynomial-time certificate.

Open [CslibFrontierTests/PPTTactic.lean](../../CslibFrontierTests/PPTTactic.lean). Its entry import is `CslibFrontier.Tactic.PPT`; the file also imports `CslibFrontier.Crypto.Computational.GGM.Evaluation` for later clients. The following contextual excerpt uses its `open Cslib Cslib.Probability Turing.MultiTapeTM`. It is copied from the checked file, not independently checked as a standalone snippet.

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

`ppt` pays a search cost at every call, even on small goals. When a file certifies many inverters or reductions, or `ppt` fails on an adversary call whose inputs need preparation, compose the rules directly. Start with `IsPPTOn.isPPT`, then bind each sampled word with `(ComputableInPolyTime.sampleList h).bind_with`. Call the adversary through `IsPPT.preprocess`, which takes separate tidy certificates for the parameter and auxiliary input; `ComputableInPolyTime.tidy` converts plain ones. Close the deterministic leaves with `fun_prop`. The more general `IsPPTOn.preprocess` takes one certificate for the pair. Given `.prod` of two projections, it cannot infer the preparation function, so `fun_prop` meets goals with unassigned metavariables. The [InaccessibleEntropy client](../../CslibFrontierTests/Crypto/InaccessibleEntropy.lean) checks this pattern on a small inverter:

<!-- excerpt: ppt-explicit-adversary-call -->
```lean
example {A : ℕ → List Bool → ProbComp (List Bool)} (hA : IsPPT encBits A) :
    IsPPT encBits (fun n y => do
      let pad ← Cslib.BitString.sampleList n
      let raw ← A n (y ++ pad)
      return raw.take n) := by
  apply IsPPTOn.isPPT
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  exact (hA.preprocess (ComputableInPolyTime.tidy (by fun_prop))
    (ComputableInPolyTime.tidy (by fun_prop))).bind_with
    (ComputableInPolyTime.isPPTOn (by fun_prop))
```

The inverters in the [InaccessibleEntropy development](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean) are certified this way. In November 2026 a `ppt` call there cost about 11,000–14,000 heartbeats even on small goals, against a few hundred for the explicit proof. Without the right definition hints, a call could exhaust Aesop's rule limit.

## Bound a centered-binomial sampler tail

[CenteredBinomial/Concentration.lean](../../CslibFrontier/Languages/Probabilistic/CenteredBinomial/Concentration.lean)
bounds the law of the existing `sampleCenteredBinomial η` program. For `η > 0` and real
`B ≥ 0`, `sampleCenteredBinomial_tail_le` gives
`Pr[B ≤ |z|] ≤ 4 exp(-B²/(2η))`; `sampleCenteredBinomial_strict_tail_le` gives the same
bound for `B < |z|`. This original two-count union bound is not optimal. Width zero remains
`pure 0`, so its strict and non-strict zero cutoffs differ.

The [checked clients](../../CslibFrontierTests/CenteredBinomialConcentration.lean) show positive
mass at both width-eight endpoints, an empty strict tail above eight, and a non-strict tail
bound below one. They also certify the actual growing program with `η = 8(l+1)` as
`IsPPTOn encUnary encIntBin` and bound its strict tail above `4(l+1)` by `4 exp(-(l+1))`.
The native certificate charges unary width and signed binary output; this scalar result
supplies neither encryption correctness nor a security reduction.

## Substitute an oracle while preserving private samples

Import [Oracle/Substitution.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Substitution.lean).
Write a replacement handler as a `ProbOracleComp` program, then use
`ProbOracleComp.simulate handler adversary`. Only external queries reach `handler`; private
samples remain sampling requests in the resulting program. The handler can make its own private
samples and external queries.

Open the [checked client](../../CslibFrontierTests/ProbOracleSubstitution.lean), whose import is
`CslibFrontier.Languages.Probabilistic.Oracle.Substitution`. This excerpt uses its `open Cslib`:

<!-- excerpt: private-sampling-substitution -->
```lean
private noncomputable def adversary : ProbOracleComp (fun _ : Bool => ℕ) (Bool × ℕ) := do
  let bit ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let reply ← ProbOracleComp.query bit
  return (bit, reply)

private noncomputable def maskedQuery (bit : Bool) : ProbOracleComp (fun _ : Bool => ℕ) ℕ := do
  let mask ← ProbOracleComp.sample (ProbComp.uniform Bool)
  ProbOracleComp.query (bit ^^ mask)

private noncomputable def reduction : ProbOracleComp (fun _ : Bool => ℕ) (Bool × ℕ) :=
  ProbOracleComp.simulate maskedQuery adversary
```

The client proves that `reduction` makes two private draws, in order, followed by one external
query, and retains the adversary's original bit in its result. Supply the random sampler and
any oracle state once, in the surrounding `OracleComp.interpret`. The theorem
`ProbOracleComp.interpret_simulate` composes that interpreter with the replacement handler;
the reduction proof need not split the private-sampling branch of `sumHandler`.

Run `scripts/build.sh CslibFrontierTests.ProbOracleSubstitution` from the repository root.
The additional stateful example checks that four adaptive target queries share one counter,
including across a private draw, and the dependent-reply example checks that query-specific
response types are preserved. For the cryptographic clients, inspect
[hybridDEMContinuation](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean)
and [hybridKEMCCAContinuation](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean):
each phase names only the oracle simulation it needs.

To bound a substituted program's queries, import
[Oracle/Substitution/QueryCount.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Substitution/QueryCount.lean).
`hQ.simulate hhandler` keeps the adversary's budget `hQ` when every handler program makes at
most one query, and `isCostBounded_simulate` does the same for general costs. Neither needs a case
split on the private-sampling branch. The forward lift
[PRP.StrongAdversary.isQueryBounded_ofForward](../../CslibFrontier/Crypto/Primitives/PRP/Finite.lean)
is a one-line client.

To analyse a substituted program against a stateful oracle, for example in an identical-until-bad
hop, import
[Oracle/Substitution/RunWith.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Substitution/RunWith.lean).
`ProbOracleComp.runWith_simulate` rewrites `runWith oracle (simulate handler A)` to a run of `A`
whose queries each run `handler q` against `oracle`. The block-mode reduction
[blockModeReduction](../../CslibFrontier/Crypto/Computational/Encryption/RandomFunctionHybrid.lean)
uses it for its fresh-sampling hop and in the CTR and OFB collision bounds.

If an existing proof needs the underlying interpreter, unfold `ProbOracleComp.simulate` to
reuse its laws and native efficiency certificates. Substitution preserves the free program;
it does not by itself certify its runtime. This separation follows VCVio's treatment of
[untouched oracle effects](https://github.com/Verified-zkEVM/VCVio/blob/87bc1892fff1982e97cfd8c7303c9d1f2bfdc2f9/VCVio/OracleComp/SimSemantics/Append/Core.lean).

## Run a word adversary against a typed oracle

When a game's adversary sends word requests but the oracle is naturally typed, import
[Oracle/Codec.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Codec.lean) and describe
the channel once as an `OracleCodec Op Q spec`: `encodeQuery` writes each query as a request,
`decodeQuery` recognizes exactly those requests, and `encodeReply` writes each reply. Then
`c.adapt P` runs the word program `P` against the typed oracle, answering requests that carry no
query with `[]` and no call. Do not write the decoding handler by hand.

`OracleCodec.run_adapt` and `OracleCodec.runWith_adapt` say that the typed run of `c.adapt P` is
the word run of `P` against `c.wordOracle O`. So a word game equals the typed game of the adapted
adversary exactly when its oracle is `c.wordOracle` of the typed one: it answers requests carrying
no query with `[]`, leaving its state unchanged, and answers the others through the typed oracle.
Prove that once for the game's oracle, as a pointwise equation, and keep the word channel when it
fails. `isQueryBounded_adapt` keeps the adversary's budget; `isCostBounded_adapt` keeps a general
cost budget when each query costs at most its request.

`OracleCodec.bitString n` carries `n`-bit strings on a single channel. `comap` transports a codec
along an equivalence of queries, and `withOp` puts one copy of a single-channel codec on each
channel. In [the Luby–Rackoff reduction](../../CslibFrontier/Crypto/Computational/LubyRackoff.lean),
`pairCodec` and `strongPairCodec` are built this way, and `pairCodec_wordOracle` and
`strongPairCodec_wordOracle` are the pointwise equations for its random-permutation games. The
[checked client](../../CslibFrontierTests/OracleCodec.lean) runs a word adversary with one
malformed and one well-formed request against a stateful typed oracle. Check it with
`scripts/build.sh --wfail --iofail CslibFrontierTests.OracleCodec`.

## Compare two runs one step at a time

To relate the laws of two loops, prove the relation for one step and lift it. Import
[Iteration/Chain.lean](../../CslibFrontier/Languages/Probabilistic/Iteration/Chain.lean) to write a
loop as a chain of distributions: `ProbComp.eval_iterate` for a closed loop and
`OracleComp.run_interpret_iterate_pmf` for a loop run with a probabilistic stateful handler. When
only the step laws agree, `ProbComp.eval_iterate_congr` gives equal loop laws directly.

Then import [PMF/Coupling.lean](../../CslibFrontier/Probability/PMF/Coupling.lean).
`PMF.map_iterate_bind_of_invariant` lifts a state representation that commutes with every step.
`PMF.iterate_bind_comm_of_invariant` handles the case where the ideal chain first draws a hidden
sample `k` and then runs on a smaller state. The link between the two chains is the law
`(exp a).map (·, rep a)`, where `exp a` samples what the real state `a` has not yet fixed, as in
lazy and eager sampling. The local step equation is needed only on states satisfying an invariant
indexed by the round. Each lemma returns the lifted equation together with that invariant on the
reachable states, so you can chain hops. `bind_bind_comm_of_invariant` and `map_bind_of_invariant`
are the one-step forms for straight-line code, and `iterate_bind_invariant` gives only the
invariant.

For an adaptive program with a query budget, import
[Oracle/QueryBoundedSimulation.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/QueryBoundedSimulation.lean).
`ProbOracleComp.IsQueryBounded.run_interpret_bind_comm_of_invariant` lifts the same link through
every external query. Its invariant is indexed by the remaining budget, for example room in a
bounded cache. Without a budget, use `run_interpret_simulation_of_invariant` or
`run_interpret_map_state_of_invariant` from
[Simulation.lean](../../CslibFrontier/Languages/Probabilistic/Simulation.lean). The open-round loops
of [CCA/Interleaved.lean](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean)
and the certification and key-expansion hops of
[TreeSignature/Security.lean](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean)
are worked clients.

## Pass a query adapter through an eager/lazy game hop

Import [Oracle/Substitution.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Substitution.lean)
and [RandomOracle/Probabilistic.lean](../../CslibFrontier/Languages/Probabilistic/RandomOracle/Probabilistic.lean).
Write the query conversion as a `ProbOracleComp` handler, then apply the eager/lazy theorem to
`ProbOracleComp.simulate handler program`. The same adapted program is used on both sides:
one interpreter samples the random function eagerly, and the other fills its cache on demand.

The [checked adapter](../../CslibFrontierTests/RandomOracleAdapter.lean) accepts one-bit words and
rejects other words. Its client repeats a query across a private draw and an invalid query.
The following excerpt uses the test file's `open Cslib Cslib.Probability`:

<!-- excerpt: random-oracle-adapter -->
```lean
private def oneBitQuery (word : List Bool) : ProbOracleComp (fun _ : Bool => Bool) (List Bool) :=
  match word with
  | [bit] => List.singleton <$> ProbOracleComp.query bit
  | _ => pure []

private noncomputable def repeated : ProbOracleComp (fun _ : List Bool => List Bool) Bool := do
  let first ← ProbOracleComp.query [false]
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let rejected ← ProbOracleComp.query []
  let second ← ProbOracleComp.query [false]
  return (first == second) && rejected.isEmpty && coin

private noncomputable def adapted : ProbOracleComp (fun _ : Bool => Bool) Bool :=
  ProbOracleComp.simulate oneBitQuery repeated
```

Apply `RandomOracle.interpret_prob_eq_memoize` to `adapted`. When cache keys and sampled values
have different representations, use `interpret_prob_eq_memoize_map` instead. Then
`ProbOracleComp.interpret_simulate` composes the surrounding interpreter with the adapter;
prove the adapter's response equation for each valid or rejected query. Import
[Oracle/Norm.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/Norm.lean) and use
`simp only [runWith_norm, pmf_norm]` to normalize closed runs and their state threading.

The test also computes the complete cached run: its result is the fresh private coin, and its
cache contains exactly the first sampled answer at `false`. Rejection adds no cache entry and
the repeated query reuses that answer. Check it with
`scripts/build.sh --wfail --iofail CslibFrontierTests.RandomOracleAdapter`.

In [the PRF game](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/RandomOracle.lean),
`prfIdealGame_eq_cached` uses this route after converting a valid word to a bit string. In
[GGM](../../CslibFrontier/Crypto/Computational/GGM/Expansion.lean), `prefix_eager` also converts the
query to its prefix. The proof of `expansionGame_uniform` then follows three named game hops:
cached parent expansions become an eager prefix table, `childTableEquiv` reindexes that table
into child labels, and those labels become the next level's cache. The prefix-length and
child-table equations remain local mathematical obligations. These eager tables are used to
prove distributional equalities; the executable reductions retain their existing separate
runtime and query-bound certificates.

## Replace a game's own caches by complete tables

Use this route when a game keeps its random-oracle caches in its own state, such as association
lists in a record or several caches for several oracles, rather than running a program through
`memoize`. Import
[RandomOracle/Represented.lean](../../CslibFrontier/Languages/Probabilistic/RandomOracle/Represented.lean).

1. Join the oracles into one interface with `⊕ₒ` and write each game query as an oracle program
   over it. Write the lazy handler and the complete-table handler as `interpret` of the same
   program, so the game logic is stated once.
2. Choose `rep : State → RandomOracle.Cache spec`, the cache that the state represents. Build it
   from one cache per oracle with `RandomOracle.Cache.sum` from
   [RandomOracle/Sum.lean](../../CslibFrontier/Languages/Probabilistic/RandomOracle/Sum.lean),
   which `Represented.lean` re-exports, and read list caches with `RandomOracle.ofList`.
3. Prove the per-call step: each lazy handler call, with its next state mapped by `rep`, is
   `RandomOracle.answer` on the represented cache. On a joined cache, `answer_sum_inl` and
   `answer_sum_inr` reduce this to one side, and `RandomOracle.eval_zoom_memoize_map` proves it for
   a `zoomStateT`/`memoize` cache.
4. Apply `RandomOracle.eval_run_interpret_eq_complete_bind`, or `run_interpret_eq_complete_bind`
   for a handler that already returns `PMF`. The run's result law becomes completing `rep s` once
   and answering every call from the table. `RandomOracle.bind_complete_sum` then splits the
   completed table into one independent table per oracle.

The checked clients are `Scheme.eval_romIndCcaExperiment_eq_eager` in
[FujisakiOkamoto/Security.lean](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Security.lean),
with two caches for `G` and `H` and a decapsulation oracle given as a program over both, which
proves the step once for the `FO-notbot` and `FO^⊥` games, and
`Scheme.eval_coupledGame_eq_eagerCoupledGame` in
[NotBot/Lazy.lean](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NotBot/Lazy.lean),
with three caches and a key-derivation query that calls two oracles. Check them, and the
approximate client below, with
`scripts/build.sh --wfail --iofail CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot`.

This proves an exact equality, so step 3 fails when a handler also inspects its caches directly,
for example a decapsulation filter that checks whether a message was already queried. Such a hop
needs an approximate simulation instead. Import
[Simulation/CloseTo.lean](../../CslibFrontier/Languages/Probabilistic/Simulation/CloseTo.lean) and
apply `OracleComp.closeTo_run_interpret_simulation_readOnly` with
`relate s := RandomOracle.complete distribution (rep s)` and a cost function that charges only the
calls that read the cache. For each call, `RandomOracle.eval_run_interpret_bind_complete` gives the
joint law of the answer and the completed final cache. On the calls that answer as a lazy oracle
this is already the eager side, so only the cache-reading calls need a statistical-distance bound.
The checked client is `closeTo_cachedCoupledBotGame_eagerCoupledBotGame` in
[FujisakiOkamoto/Bot.lean](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Bot.lean),
whose `G` and `H` calls are exact and whose decapsulation call costs `2^{-γ}` by spreadness.

## Certify an adaptive oracle client

For native oracle efficiency, start with `WordOracleComp Operation α`: finite operation names and word payloads/replies.

<!-- worked-example -->

**Worked example: Bound the reply prefix of an adaptive oracle call**

**Goal:** certify the oracle client's native runtime while allowing its next query to depend on the previous reply.

Open [CslibFrontierTests/OracleComposition.lean](../../CslibFrontierTests/OracleComposition.lean), whose main import is `CslibFrontier.Computability.Probabilistic.Oracle.Composition`. Its query-bound examples additionally import `CslibFrontier.Computability.Probabilistic.QueryBounds`. This contextual excerpt uses the file's `open Cslib Cslib.Probability Turing Turing.MultiTapeTM`:

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

First specify the operation set and request representation. Then bound the amount of each reply inspected or retained, prove deterministic preprocessing efficient, and compose the query/conditional rules. With `CslibFrontier.Tactic.PPT` imported, `ppt [adaptive]` does both steps: it unfolds the hint and composes the oracle program with the same plain rules. It also unfolds local encoding `let`s and uses certificates stored in fields of local structures, so a reduction's handler that samples with a scheme `S` needs no separate `have` for `S.encrypt_ppt`. The [oracle `ppt` client](../../CslibFrontierTests/OraclePPTTactic.lean) certifies the encrypt-then-MAC handler this way and checks the failure cases.

**Result:** one machine and clock work for every input, state type, stateful handler and initial state, preserving the joint law of output and final oracle state. The certificate charges request construction and reply access; the external handler's computation remains external.

Next inspect behavior under a concrete handler. The same client defines `counting`, which increments a counter on every call. Its semantic examples establish final count one on the unselected branch and two on the selected branch. This catches interaction differences that equality of output marginals could hide. For the simpler `runWith` interface, open [CslibFrontierTests/OracleSemantics.lean](../../CslibFrontierTests/OracleSemantics.lean).

Use `adaptive_isOraclePPTOn.query_bounds` to obtain polynomial bounds on external call count and request length. A separately proved `IsCostBounded` charges chosen requests along every path; `ProbOracleComp.IsQueryBounded` counts external calls rather than private samples. Neither bound by itself pays for arbitrary Lean callbacks. A call budget `n` becomes a cost budget `n * c` when every call, or every call satisfying a `QueriesSatisfy` predicate, costs at most `c` ([QueryCount/Scale.lean](../../CslibFrontier/Languages/Probabilistic/QueryCount/Scale.lean)). For an average rather than a worst-case charge, [QueryCount/Expected.lean](../../CslibFrontier/Languages/Probabilistic/QueryCount/Expected.lean) defines `OracleComp.expectedCost handler cost program`, the expected total cost when the calls are answered by PMF-valued `handler`. `expectedCost_bind` is Wald's identity for sequencing, `expectedCost_interpret` follows a handler substitution, and `expectedCost_le_of_isCostBounded` bounds the expectation by a pathwise `IsCostBounded` budget. The [local-decoding model](../circuits-logic-and-other-models/query-and-communication.md#locally-decodable-codes) measures smoothness this way.

**When it fails:** if `fun_prop` fails on returning an entire oracle reply, check whether the requested conclusion permits unbounded output. The linked client contains explicit failure examples and the bounded-prefix repair.

<!-- /worked-example -->

When replacing the external handler with an implementation, open [Oracle/Substitution.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/Substitution.lean). The plain-certificate variant `IsOraclePPTOn.run_interpret_preprocess_open'` requires efficient preparation, initialization and handling, plus an invariant and bounds on reply length and added encoded state. Its `hresources` premise also certifies a uniform unary computation of the resource allowance from the original caller and request; an abstract polynomial bound alone does not supply this certificate. Repeated state doubling explains why “each call is polynomial time” is insufficient.

When the allowance is polynomially bounded but not conveniently computed, apply `IsOraclePPTOn.run_interpret_preprocess_open_of_polyBounded` instead (the uniform-clock form is `IsOraclePPT.run_interpret_preprocess_open_of_polyBounded` in [Oracle/Parameter.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/Parameter.lean)). Its `hresources` premise is only `PolyBounded` growth of `resources caller request` in the length of the encoded caller–request pair, so no unary computation of the allowance is needed; both certificate variants are derived from it. The other premises are unchanged: the invariant must still hold for every handler result in the support under every external oracle, and the allowance must still bound each reply and the added encoded state. [`isPPTOn_runWithEncryption`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyCPA.lean) is a checked client: it proves the allowance's growth with `growth_poly` from the security parameter and the lengths of the public key and the request.

When the run is written with [`runState`](../../CslibFrontier/Languages/Probabilistic/Oracle/RunState.lean) as `((program (prepare a)).runState (oracle a)).run (initial a)`, certify it with `IsOraclePPTOn.isPPTOn_runState`, or `IsOraclePPT.isPPTOn_runState` for a parameterized program, from [Oracle/RunState.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/RunState.lean). They are `run_interpret_preprocess` and `run_interpret_preprocess'` restated on `runState`, with plain polynomial-time preparation, initial state and allowance in both: the oracle certificate applies the stateful oracle to caller, request and state, which `fun_prop` can certify, and the invariant and allowance are unchanged. The [checked client](../../CslibFrontierTests/OracleRunStatePPT.lean) certifies a run against a stateful oracle.

## Bound stateful identical-until-bad hops and random-oracle collisions

When two stateful oracle handlers agree until an internal collision or guessing event occurs, import [UntilBad/Flag.lean](../../CslibFrontier/Languages/Probabilistic/UntilBad/Flag.lean) (and [Crypto/Game/UntilBad.lean](../../CslibFrontier/Crypto/Game/UntilBad.lean) for `Game.advantage`) instead of defining an ad hoc `State × Bool` wrapper and proving `absorb_first`, `absorb_second` and `Sum.inl` private-sampling cases by hand:

- **Monotone Boolean bad flags (`withBadFlag`, `IdenticalUntilBad.of_flag`).** Given one-step kernels `step₁ step₂ : (q : Query) → State → PMF (spec q × (State × Bool))` returning an answer, next state and per-call bad indicator, `OracleComp.withBadFlag stepᵢ` latches the flag with `||` on `State × Bool` under `FlagBad st := st.2 = true`. `OracleComp.identicalUntilBad_withBadFlag` (and `ProbOracleComp.identicalUntilBad_withBadFlag`) discharges flag absorption automatically and asks only for pointwise agreement on unflagged outcomes `step₁ q s (a, (s', false)) = step₂ q s (a, (s', false))`. When a handler already acts on `State × Bool`, use `IsFlagMonotone` with `IdenticalUntilBad.of_flag`.
- **Recovering unflagged `ProbOracleComp.runWith` executions.** `ProbOracleComp.IdenticalUntilBad` lifts `OracleComp.IdenticalUntilBad` across `ProbComp.unifOracle` coin draws, providing `run_apply`, `bind_apply_le`, `bad_eq`, `abs_sub_le`, `closeTo_run`, `closeTo_bind` and `ProbOracleComp.IdenticalUntilBad.advantage_le` directly on `ProbOracleComp.runWith`. Apply `ProbOracleComp.runWith_withBadFlag_map_fst` (or `ProbOracleComp.runWith_map_fst`) to project away the Boolean flag whenever each step's `(a, s')` marginal matches the unflagged handler.
- **Linear vs. triangular (`choose 2`) bad-event union bounds.** Use `ProbOracleComp.toOuterMeasure_bad_le` when each call's bad probability is bounded against a real-valued budget growth. When each call from a good state `s` triggers `bad` with probability proportional to an integer table size (`size s * δ`) and grows `size` by at most `1`, import [UntilBad/ChooseTwo.lean](../../CslibFrontier/Languages/Probabilistic/UntilBad/ChooseTwo.lean) and apply `OracleComp.toOuterMeasure_bad_choose_two_le` or `ProbOracleComp.toOuterMeasure_bad_choose_two_le` for the sharp triangular sum `(n * size s + n.choose 2) * δ`. When active calls (`cost₁`, budget `k₁`) risk `bad` and grow `size` while passive calls (`cost₂`, budget `k₂`) only grow `size`, `OracleComp.toOuterMeasure_bad_choose_two_cost_le` and `ProbOracleComp.toOuterMeasure_bad_choose_two_cost_le` give `(k₁ * size s + k₁ * k₂ + k₁.choose 2) * δ`.
- **Random-oracle min-entropy programming and birthday collisions.** Import [RandomOracle/Programming.lean](../../CslibFrontier/Languages/Probabilistic/RandomOracle/Programming.lean) (and [CloseTo/RandomOracle.lean](../../CslibFrontier/Crypto/Game/CloseTo/RandomOracle.lean) for `Game.advantage` wrappers):
  - `RandomOracle.toOuterMeasure_exists_mem_fst_eq_le` bounds `μ.toOuterMeasure {a | ∃ e ∈ cache, e.1 = f a}` by `cache.length * δ` whenever `∀ q, (μ.map f) q ≤ δ`, and `RandomOracle.map_comp_apply_le_of_injective` transports that guessing bound through an injective key embedding.
  - `RandomOracle.lazyProgramHandler` and `RandomOracle.overwriteProgramHandler` (with flagged counterparts `flaggedLazyProgramHandler` and `flaggedOverwriteProgramHandler` used in [FiatShamir.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamir.lean) and [FiatShamirNIZK.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamirNIZK.lean)) model a two-channel experiment (`Req ⊕ Query`) whose active `.inl req` calls sample `ts ← samplePre req` with guessing bound `δ` at `point req ts` and either query `memoize (fun _ => dist)` lazily or overwrite `(point req ts, c)` with a fresh `c ← dist`. `closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two` and `closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two` (plus `advantage_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two_le`) bound the programming-collision error by `(q_S * cache.length + q_S * q_H + q_S.choose 2) * δ`, with rectangular corollaries `q_S * (cache.length + q_S + q_H) * δ`.
  - `RandomOracle.toOuterMeasure_collision_memoize_uniform_le` and `RandomOracle.toOuterMeasure_hasOutputCollision_memoize_uniform_le` (with `runWith` variants for `ProbOracleComp`) prove the `q`-query random-oracle output-collision birthday bound `q.choose 2 / Fintype.card Digest` starting from `[]`.
- **Two independent random oracles as two lists.** When a protocol calls two random oracles, such as a Merkle hash and a Fiat–Shamir challenge oracle, import [RandomOracle/Sum.lean](../../CslibFrontier/Languages/Probabilistic/RandomOracle/Sum.lean) and run it under `RandomOracle.memoizeSum dist₁ dist₂`, which keeps one association list per oracle. `RandomOracle.run_interpret_memoizeSum` shows that the two lists implement the lazy random oracle `RandomOracle.answer (sumHandler dist₁ dist₂)` on their joined cache `Cache.sum (ofList tr₁) (ofList tr₂)`, and `map_fst_run_interpret_memoizeSum_nil` gives the output distribution from empty lists. One call unfolds with `memoizeSum_inl`/`_inr` and inverts with `mem_support_memoizeSum_inl`/`_inr`; `run_interpret_memoizeSum_liftLeft`/`_liftRight` reduce a one-sided subprogram to ordinary `memoize`, and `mem_support_run_interpret_memoizeSum` carries per-list invariants (for example `mem_support_memoize_nodup`). Per-oracle query budgets of embedded subprograms come from `IsCostBounded.liftLeft`/`liftRight` and `liftLeft_of_cost_inl_eq_zero`/`liftRight_of_cost_inr_eq_zero` in [QueryCount/Sum.lean](../../CslibFrontier/Languages/Probabilistic/QueryCount/Sum.lean). `micaliMemoize` and `bcsMemoize` are the two instances.

The [checked clients](../../CslibFrontierTests/Crypto/UntilBadROMFramework.lean) verify concrete sharpness of `toOuterMeasure_bad_choose_two_le` and `HasOutputCollision` at `q = 2` on `Bool` (`= 1 / 2`), exercise `ProbOracleComp.IdenticalUntilBad` and `withBadFlag` on a randomized 2-query client, check exact min-entropy list-key collision mass on `Fin 4`, and compare the nontrivial `3 / 4` sharpened programming bound against the vacuous `3 / 2` rectangular bound at `q_S = 2, q_H = 1, δ = 1 / 4`. Run `scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.UntilBadROMFramework`. These bounds depend only on pathwise query/cost budgets and PMF semantics; native `IsOraclePPTOn` / `IsPPTOn` runtime certificates remain separate obligations.

## Derive adaptive decapsulation security

Import [`KEMFromPKE/CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean) when the starting assumption is `WordINDCCA2 keyGen encrypt decrypt`. Apply `WordINDCCA2.indistinguishable_encryptKeyEncaps` with the unary polynomial-time certificate for `keyLen`. It proves security of the actual `encryptKeyEncaps` constructor against adaptive postchallenge queries, with exact loss one. The [complete checked client](../../CslibFrontierTests/Crypto/KEMFromPKECCA.lean) uses `keyLen n = 2 * n` and keeps `n` as the security parameter.

For a runtime conclusion, use `isPPTOn_kemCCAGames_encryptKeyEncaps` with native key generation, encryption, decryption and adversary certificates. For correctness, apply `decrypt_encryptKeyEncaps_some` to a supported encapsulation and the original encryptor's supported-output correctness. These are separate contracts. The same test file checks a correct empty-key instance and distinguishes `none` from `some []`.

Check freshness against raw ciphertext words. The test's native `adaptiveTagDistinguisher` first observes rejection of the exact challenge, then flips a redundant tag and queries again. Because the malformed scheme ignores that tag, the distinct word reveals the key. Its exact advantage is `1 - 2^(-keyLen n)`; the comparison uses a bounded reply prefix, so its strict oracle runtime certificate holds even for arbitrarily long external replies.

For hybrid ciphertexts, use [`hybridDecrypt`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid.lean)
with Option-valued decapsulation and symmetric decryption. It first checks that re-encoding
`(unframe ct, dropFrame ct)` gives exactly `ct`, then propagates either component's `none` result.
Apply `hybridDecrypt_hybridEncrypt` with component correctness returning `some k` and `some msg`;
`computableInPolyTime_hybridDecrypt` takes the corresponding certificates with `encOption` outputs.
The [hybrid clients](../../CslibFrontierTests/Crypto/HybridEncryption.lean) show why the framing check
matters: `[true, true]` and `[true, true, false]` have the same projections, but only the latter
is a canonical pair. They also check accepted empty plaintext (`[true]` as an oracle reply),
rejection (`[]`), and exact challenge-word rejection.

For the symmetric leg of CCA composition, import
[`Hybrid/DEMCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean).
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
[authenticated-encryption clients](../../CslibFrontierTests/Crypto/AuthenticatedEncryption.lean)
check independent lengths and show why an all-message bound cannot depend only on `n`.

The [checked clients](../../CslibFrontierTests/Crypto/HybridDEMCCA.lean) apply the result to the
existing PRF Encrypt-then-MAC cipher, expose an insecure echo cipher, and run a zero-width
prechallenge/challenge/postchallenge trace. They distinguish an empty encryption reply from an
encoded successful empty plaintext.

For the complete `n`-bit-message composition, import
[`Hybrid/CompositionCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
and apply `hybrid_indcca2On`. Supply the existing KEM CCA indistinguishability assumption,
`E.OneTimeINDCCA`, native algorithms, supported KEM correctness, and a native postprocessor
`F` satisfying `(uniformList (keyLen n)).map (F n) = eval (E.keyGen n)` for every `n`.
Postprocess every successful decapsulation with `Option.map (F n)` too. The conclusion uses
`INDCCA2On` with both challenge lengths equal to `n`, not unrestricted `WordINDCCA2`.
`exists_hybridCCA_reductions` returns a `HybridCCAReductions` record: native KEM and symmetric
adversaries `kem` and `dem` with the exact `2 * KEM advantage + symmetric advantage` bound
`advantage_le`. Reply caps are derived from supported
secret-key lengths and the native decryptor; external replies need no assumed length bound.

The [complete composition clients](../../CslibFrontierTests/Crypto/HybridCompositionCCA.lean)
use `IsPPTOn.exists_total_seeded_evaluator` for arbitrary actual key generators and split `3*n`
uniform bits into the PRF Encrypt-then-MAC cipher's actual framed keys. Those keys have encoded
length `4*n+1` and are not uniform words of that length. For perfect correctness, apply
`hybridDecrypt_postprocessed_hybridEncrypt` with a supported-real-key premise: the total evaluator
provides it for every seed, while the simple split map needs real keys of length `3*n`.
The clients also distinguish failed decapsulation from accepted empty keys, detect omitted
postprocessing on forwarded replies, and exhibit a failed real hop without KEM correctness.

For a concrete PKE that needs the generic explicit-coin interface but not an FO transform, import
[`PKE/ExplicitCoin.lean`](../../CslibFrontier/Crypto/Protocols/PKE/ExplicitCoin.lean) directly.
It owns `ExplicitCoinPKE`, `DeltaCorrect`, `GammaSpread`, two-stage IND-CPA `cpaAdvantage` (the
shared `PKE.cpaExperiment` of `toPKE`), and the narrower fixed-message `indCpaGame`; the FO module
publicly re-exports that API for existing transform clients. State new IND-CPA hypotheses with
`cpaAdvantage`: a bound for every fixed message pair does not give two-stage security.

When the KEM instead derandomizes an explicit-coin public-key encryption scheme `encDet : PK → M → R → CT` with a mandatory re-encryption check (`T[PKE, G]`, `FO^⊥`, and domain-separated implicit-rejection `FO-notbot`), import [`FujisakiOkamoto.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto.lean) and [`FujisakiOkamoto/Security.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Security.lean) rather than `KEMFromPKE.lean`. Those modules supply `ExplicitCoinPKE` (`DeltaCorrect`, `GammaSpread`, `cpaAdvantage`), deterministic recovery and re-encryption rigidity lemmas (`decT_encT_eq_some`, `encT_of_decT_eq_some`, `Scheme.decapsBot_encT_eq_some`, `Scheme.decapsBot_eq_none_of_reencrypt_ne`, `Scheme.decapsNotBot_encT_eq`, `Scheme.decapsNotBot_of_reencrypt_ne`), and the `FO-notbot` ROM IND-CCA games (`Scheme.roIndCcaGame`, `Scheme.eagerIndCcaGame`, `Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`, `Scheme.indCcaRomAdvantage_eq_eager`) and keyless two-stage IND-CPA reduction (`Scheme.simHandler`, `Scheme.romCpaReduction`, `Scheme.simFilterOwExperiment`, `Scheme.succProbability_simFilterOwExperiment_le`; checked clients in [`CslibFrontierTests/Crypto/FujisakiOkamoto.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamoto.lean)); the IND-CCA bound `Scheme.indCcaRomAdvantage_le` for adversaries with explicit coins (`RandomizedROAdversary`) from two-stage IND-CPA security of the one reduction `romCpaReduction A`, `δ`-correctness and `γ`-spreadness is in [`FujisakiOkamoto/NotBot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NotBot.lean), with its hybrid games in `NotBot/Hybrids.lean` and one module per hop, while [`FujisakiOkamoto/Bot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Bot.lean) (`Scheme.roIndCcaBotGame`, `Scheme.indCcaBotAdvantage_le`) and [`FujisakiOkamoto/SpreadNecessity.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/SpreadNecessity.lean) (`unspreadPointPKE`, `probeDecapsAdv`, `advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv`; checked client in [`CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean)) prove the corresponding ROM IND-CCA bound for explicit-rejection `FO^⊥ = U^⊥ ∘ T` and the necessity of its `qD · 2^{-γ}` spreadness term, and [`FujisakiOkamoto/NoCheck.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NoCheck.lean) (`leakyPKE`, `decapsNotBot_leakyPKE_some`, `Scheme.decapsNoCheck`, `Scheme.eagerNoCheckGame`, `leakAdv`, `advantage_eagerNoCheckGame_leakAdv`) proves that dropping the re-encryption check breaks `FO-notbot` with advantage `≥ 1 - (n + 1) / |K|` for a perfectly correct `P` and uniform keys.

## Certify a list accumulator

Import `CslibFrontier.Computability.Probabilistic.Fold` for
`IsPPTOn.foldlM_of_bounded_growth` and `IsOraclePPTOn.foldlM_of_bounded_growth`.
They certify ordinary `List.foldlM` with the accumulator as the step's first argument.
Supply plain polynomial-time certificates for the input list and initial accumulator, a joint
step certificate, and a constant bound on the encoded accumulator's growth at every supported
result. For an oracle fold that bound covers arbitrary external replies; truncate replies or
prove a suitable support bound before applying it.

The complete [ProbabilisticFold client](../../CslibFrontierTests/ProbabilisticFold.lean) checks a
noncommutative accumulator, an oracle fold's ordered calls and final external
counter, and an empty fold that makes no calls. From the configured repository root, run
`scripts/build.sh --wfail --iofail CslibFrontierTests.ProbabilisticFold`. The fallback argument
only totalizes the internal iteration step; it is never used on an empty list. If the growth
premise fails, check the output encoding and reply cap rather than assuming that efficient
individual steps make an arbitrarily growing accumulator efficient.

## Connect a randomized RAM loop to its answer law

Use this route when a randomized Word-RAM loop already exists and you want to derive its answer
distribution from an oracle specification. First choose the observed value, a supported-state
postcondition and explicit instruction and random-call budgets. Import
[Randomized/LoopSegmentLaw.lean](../../CslibFrontier/Computability/WordRAM/Randomized/LoopSegmentLaw.lean).
`LoopSegmentLaw` retains the existing `LoopSegment` execution witness and bounds every supported
path. Its exact equality describes the chosen observation's PMF; its instruction budget is an
upper bound, not an assertion that every run takes the same time.
Random-call budgets use the existing [randomized RAM convention](../algorithms-and-memory/wordram-and-bridges.md),
which gives finite-interval sampling its own instruction and resource semantics.

From the repository root, open the complete
[WordRAMLoopSegmentLaw client](../../CslibFrontierTests/WordRAMLoopSegmentLaw.lean), including its
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
scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMLoopSegmentLaw CslibFrontierTests.KargerFastCutLaw
```

A successful build checks the paid loop and the triangle, recursive seven-vertex and zero-cut
graph cases. If composition fails, compare the continuation law's observation and postcondition
with the preceding segment. If finishing fails, prove the exit condition for all supported
states. A query-count bound alone does not supply either instruction bound.

For the larger application, follow
[KargerFastCutLaw](../../CslibFrontierTests/KargerFastCutLaw.lean) into
[Lean/Karger/FastCut](../../CslibFrontier/Algorithms/Lean/Karger/FastCut.lean), then
[KargerStein](../../CslibFrontier/Algorithms/WordRAM/KargerStein.lean). The specification restarts
both recursive branches from the same parent graph and interprets their replies independently.
Its success statements concern a minimum-cut **value**, with the stated positive-minimum-cut
hypothesis; cut support also covers the zero-cut fixture. The native laws retain their word-fit,
frame and supported-path resource premises. To pass from a code observation to a halted cut
answer, [Karger/OutputLaw](../../CslibFrontier/Algorithms/WordRAM/Karger/OutputLaw.lean)'s
`program_of_law` additionally requires fitting input words, cut support and allowance for the
final halt. This specification bridge leaves the memory-oracle contraction realization and
recursive frame-stack migration open.

## Use the bounded H4 hierarchy clients

For selected correction/pilot cutoffs, import
[HierarchyCutoffs](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCutoffs.lean).
Supply a `FourthRootHierarchyParams 16 1 16 32 8` witness and both ordered retention laws;
`correctionSampling` and `pilotSampling` derive the incoming count from the existing detector.
Their public projection equations let ordinary imports inspect recipe parameters without
unfolding opaque constructors. `correction_col_support` and `pilot_col_support` apply to
arbitrary raw, preparation and maximum children. The support margins use the actual Q/ρ gates.

For finite prime frame environments, start with
[HierarchyRankCutoffs](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyRankCutoffs.lean)
and its [complete regression client](../../CslibFrontierTests/HierarchyCutoffs.lean).
The constructor examples use H=4, P=5 and horizon zero on a positive singleton matrix.
These constructors have two independent full-environment seeds. For the genuine mean of
one actual environment, import
[HierarchyCorrectionMean](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCorrectionMean.lean)
and follow its [complete regression client](../../CslibFrontierTests/HierarchyCorrectionMean.lean).
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
[HierarchySourceSampling](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchySourceSampling.lean)
and use `source_request_mean`; follow its
[complete regression client](../../CslibFrontierTests/HierarchySourceSampling.lean).
Supply source exponent `s`, stage exponent `k`, `k ≤ s`, and a horizon containing `s`.
The true `stageSource` retains the source role and suffix at the terminal stage rate.
`stageRaw` and `stageMaximum` use these genuine stage channels. `sourcePreparation`
uses the actual sampling source for its incoming gate. `source_normalizer` identifies its
joint actual source/usage mean on the same environment, and `stage_atomCutoff_eq`
preserves the true cutoff. `CorrectionSampling.withSource` changes only the sampling-source
pair law, preserving the true input, final pilot, gates and incoming budget. The common
`correctionRequest_eq_split` avoids rebuilding the split transport for each choice of children.

To compare genuine targets across request roles and copy suffixes, import
[HierarchyCanonicalTargets](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCanonicalTargets.lean).
Use `stage_correctionIter_eq_of_terminal_rate` to identify the left and negative correction
targets at a common stage rate. `source_request_mean_canonical` combines this transport with
the actual narrower-source correction mean, retaining its literal usage-density divisor.
The proof integrates source spectators and permutes each padded frame seed; it does not
identify samples at an unchanged environment. The
[regression client](../../CslibFrontierTests/HierarchyCanonicalTargets.lean) checks actual residual
requests with different terminal roles and radix-two suffixes, a positive target and an
unequal-rate complete correction mean.

For a genuine source-reset dense child, import
[HierarchyDenseChildren](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyDenseChildren.lean).
Build `denseChild` from the deterministic hierarchy base, bin cutoff and genuine
`densePreparation`. `dense_normalizer` integrates the actual joint source/usage mean;
`denseChild_terminal` then removes source and spectator dependence pointwise. For a
left correction sharing the midpoint with that reset source, use
[HierarchySharedMidpoint](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchySharedMidpoint.lean).
`sourceChild_mul_denseChild_mean` conditions the single full environment on the old
source and terminal events. Supply three distinct roles, the complete right-source reset,
the finite horizon and narrower-source hypotheses, and the dense support/gate bounds.
The left midpoint hit and literal midpoint-density divisor remain in the sample.
The [checked client](../../CslibFrontierTests/HierarchySharedMidpoint.lean) evaluates a positive
product with unequal rates, nonempty suffixes and a free fourth role.

For signed assembly import
[HierarchySignedMean](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchySignedMean.lean).
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
[checked signed client](../../CslibFrontierTests/HierarchySignedMean.lean) keeps nonempty
suffixes, unequal rates and a free spectator, checks two statistical walk precisions,
positive genuine final correction/product terms, a nonconstant product and two-bin assembly.

For finite absolute estimated-child propagation import
[HierarchyEstimatedMean](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyEstimatedMean.lean).
`estimated_residual_bins_mean_error` compares actual bounded `incomingChildren` at fixed
`Request HP.k` with `canonicalRequestChild`. Supply the genuine C/top-rate cap, monotone
bin scales with adjacent ratio at most 16, and the same cover/horizon and dense-gate contracts.
`boundedRoutedBinCutoff_div_eq` proves true-input agreement before the bounded evaluator is
used. The product splits as estimatedLeft*(estimatedRight-canonicalRight) +
(estimatedLeft-canonicalLeft)*canonicalRight. Actual correction range `2*Q(atomCap)` and
genuine dense range `2*max cap 16` pay the two errors. Importance and midpoint densities
stay literal; positive-bin errors are summed and the negative error occurs once.
The [checked error client](../../CslibFrontierTests/HierarchyChildError.lean) instantiates the
actual two-bin cap and exact adjacent ratio on the shared spectator/suffix fixture.

[FirstMeanError](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/FirstMeanError.lean)
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
[HierarchyRawMoment](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyRawMoment.lean)
and apply `rawIncomingNormalized_noise_le_lower`. Supply positive N, u, row rank K and
incoming rank Kc. The selected cutoff laws derive the actual left correction child's
range `CA = 2 * Q(atomCap)`, row support K and incoming support Kc, for arbitrary raw,
preparatory and pilot children. Its source-released product costs
`K^3 * CA^4 * Kc * (rate(km) / u)` times the weighted right-child fourth moment.
`incomingMomentBudget` adds the actual weighted direct and negative child moments, with
a conservative factor 64 for the signed sum. The right child includes the exact usage
ratio and midpoint marginal divisor from `rawSample`; it never takes the old source as
an extra argument. All children may share every rank coordinate.

The [checked examples](../../CslibFrontierTests/HierarchyRawMoment.lean) include a complete
P=5 residual with input moment one and positive correction product, different nonempty
copy suffixes and a spectator. A correlated two-factor example has exact moment 257/2.
An identity family with one nonzero per row and column has moment n at N=u=1, so support
and range caps alone do not imply a width-independent unnormalized moment. The new client
requires lower-child moments to be paid by a later induction; it assumes no final raw or
noise certificate. Zero correction remains literal; the moment/noise bridge here treats
positive iterations. Pilot/copy paths, quantitative lower-child budgets, summation and
recursive/native correctness remain open.

For the first compression signal, import
[FirstSignal](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/FirstSignal.lean)
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
[regressions](../../CslibFrontierTests/ActualFirstSignal.lean) check nonzero nonconstant
telescoping prefixes, zero inputs, empty slices and a nonconstant random mean/moment.
For a numerical payment, import
[FirstPayment](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/FirstPayment.lean).
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
[actual-bin regressions](../../CslibFrontierTests/ActualFirstPayment.lean) use
`boundedRoutedBinCutoff` with a genuine polynomial switch, top cap HP.k+2, adjacent-scale
ratio 16 and explicit CB=max(HP.k+2,16). They check a nonzero complete residual, negative-input
clipping, a chosen actual i=2 noise client, exact logarithmic steps and zero/empty edges.

For the preparatory second signal, import
[SecondSignal](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/SecondSignal.lean).
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

The [regressions](../../CslibFrontierTests/ActualSecondSignal.lean) check positive, nonconstant
selected preparation, the actual H4 second-prefix client with the
chosen steps, D=0 with a nonempty suffix, two-signal prefixes, zero children, and empty
usage through compression. Mixing controls noise around the selected input's own mean.

For deterministic preparation bias, import
[MeanBias](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/MeanBias.lean).
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
[SecondEnvelope](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/SecondEnvelope.lean).
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
The shared [estimated input](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyEstimatedInput.lean)
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
Positive tolerance is required. The [finite input tests](../../CslibFrontierTests/HierarchyEstimatedInput.lean)
include a positive nonconstant two-bin input, exact once-negative arithmetic, independent
precisions, separate top/fine caps, support versus width, chosen amplified steps and zero/empty edges.
The [regressions](../../CslibFrontierTests/SecondEnvelope.lean) check a positive nonconstant
spectator raw child and B1, exact-zero/empty edges, actual clipped-mean comparison and an exact
two-endpoint counterexample to dropping width.

[ReserveOutput](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ReserveOutput.lean)
assembles the actual finite output from explicit lower-child conditional-error-cost fourth
moments. Its finite geometric, routing and cutoff hypotheses are the documented fields of
`ReserveOutputContext`; `ReserveOutputChildren` contains the independently supplied raw,
preparation and maximum families. Their shared
[OutputContext](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/OutputContext.lean)
module gives named constructions `amplification`, `tolerance`, `rawSteps`, `prepSteps`,
`rawWalk`, `prepWalk`, `cost` and `increment`. The records are supplied after the output
constant is selected: `Cbound` depends on HP, ζ, scale and the positive floor, before P,
J, the prime instance, horizon, prefix length or child families. These names preserve the
finite terms and their explicit losses; they do not bundle the output guarantee.
`actualEstimatedResidual_output_from_cost_reserves` derives common deterministic B
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
The [regressions](../../CslibFrontierTests/ReserveOutput.lean) construct an inhabited shared
context with two bins and distinct full/usage exponents, evaluate a positive nonconstant
full-matrix input with a free spectator, show the once-negative arithmetic,
compute nonzero common B and check the actual completed prefix at index zero.
The bounded fixture does not assert the canonical routed-bin mean or recursive reserves.
A separate actual lower-child conditional-cost client proves that the finite reserve is
satisfiable at some positive tolerance; it does not claim that tolerance is small.

[ChildRootReserve](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ChildRootReserve.lean)
now pays that cost reserve from actual normalized lower-child rooted moments.
[RootReserveOutput](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/RootReserveOutput.lean)
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
[domain regressions](../../CslibFrontierTests/ChildRootReserve.lean) check an off-source error
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
lower-child budget induction, native realization and RL=L remain unproved by this API.
The scope and status of this route are recorded in
[issue #1721](https://github.com/cslib-community/cslib-frontier/issues/1721); the shared-context
extraction maintains its existing finite results and does not resume the dropped route.

## Extract an emitted pseudorandom prefix

Import [Stretch/Prefix.lean](../../CslibFrontier/Crypto/Computational/Stretch/Prefix.lean).
Use `PRGStretch.length_take_forwardIterate` and `take_forwardIterate_prefix` with the global
one-bit length promise. The latter compares `ℓ ≤ L` rounds only after discarding the final
seed: take `ℓ` bits from either run. Do not apply it to the complete retained-seed output.

`polyTime_take_forwardIterate` certifies the map from a complete seed and unary round count
to the emitted prefix. Compose its round count with the plaintext length to obtain a native
XOR pad computation; the [checked PRGStretch client](../../CslibFrontierTests/PRGStretch.lean)
proves actual encryption/recovery and distinguishes emission order from its reversal.
For security, apply `indistinguishable_take_forwardIterate` to the existing one-bit
`PseudorandomGenerator` assumption and a native unary length schedule `L`. The seed law stays
`uniformList n`; the output law is compared with `uniformList (L n)`. This covers `L n = 0`
and seed width zero, but does not yet supply adaptive-message cipher security.

## Carry the certificate into a security proof

Keep efficiency and security as separate goals. In [Crypto/Computational/Basic.lean](../../CslibFrontier/Crypto/Computational/Basic.lean), computational indistinguishability quantifies over certified strict-PPT distinguishers. It does not require the compared PMF ensembles to be efficiently sampleable or polynomially bounded in length. Check those properties separately when the intended construction needs them.

Specify the experiment, admissible adversaries, success event and assumption; prove the reduction's efficiency using the routines above; then prove the probability or advantage inequality. Semantic rewrites and native certificates discharge different obligations. If a proposed reduction only has a query bound, return to the realization step before calling it a computational security reduction. Use the [security-game reference](../programs-crypto-and-probability/security-games-and-primitives.md) to choose the correct primitive and adversary model. The final theorem keeps only the premises that [Security theorems and efficiency witnesses](../programs-crypto-and-probability/security-games-and-primitives.md#security-theorems-and-efficiency-witnesses) allows: named hardness assumptions, the adversary's class and properties of components that the cited result takes as given, never a bound on the reduction it builds.

[complexitylib]: ../sources.md#complexitylib
[holenstein09]: ../sources.md#holenstein09

The two reserve-output theorems choose their output constant after the fixed hierarchy,
ζ, scale and positive floor, before the prime, environment width, horizon, prefix length
and raw/preparation/maximum families. Select this constant before allocating recursive
child accuracies. Uniformity of that coefficient does not remove any displayed finite
allocation or walk-length losses and supplies no recursive accuracy theorem.

[HierarchyCorrectionStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCorrectionStability.lean)
factors the actual correction request into its unit-pilot coefficient and `γ(maximum y)`.
The coefficient lies in `[0, 2 Q(atomCap)]`, even for signed raw/preparation estimates.
If `Lγ` is the hierarchy's fourth-root Lipschitz constant for γ, the fourth-root output
change is at most `(2 Q(atomCap))^(1/4) Lγ |maximum y - maximum' y|`. The integrated theorem
keeps both children on the same full environment and the original source/full-terminal
masks; its loss is `((2 Q(atomCap))^(1/4) Lγ)^4`. It does not silently transport a vertex
error to a different source or remove any width/rate coefficient from that transport.

For all three changing child classes, use
[HierarchyCorrectionRawStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCorrectionRawStability.lean).
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
The [regressions](../../CslibFrontierTests/HierarchyCorrectionRawStability.lean) include nonzero
separate/joint perturbations and row/incoming rank sensitivity; the dyadic maximum
regression above remains in place.

For the actual pilot score, detector and running maximum recipes, use
[PilotRowStability](../../CslibFrontier/Computability/LogSpaceDerandomization/PilotRowStability.lean).
The score contract keeps the signed raw inputs in the original K-rank and pays ordinary
fourth-moment row error with `width * ((Lϕ + Lρ) / rate)^4`. Its constants come from the
fixed HP cutoffs before domains, rates or child tables. The detector first takes its actual
source mean and terminal-conditioned mean: Jensen pays the source-rank maximum by the
sum of fourth powers on that same finite source slice. The literal-payment theorem retains those means and the finite source sum.
[PilotDetectorTransport](../../CslibFrontier/Computability/LogSpaceDerandomization/PilotDetectorTransport.lean)
reinserts the terminal conditioning by finite Fubini: its integrated score payment is
`width * childSourceRate / (parentSourceRate * terminalDensityLowerBound)` times the
child row moment. All outer coordinates and both actual integration variables remain in
that moment. A positive terminal-density lower bound is explicit; empty conditioning
still gives zero in the underlying detector contract.
The clipped running maximum pays the sum of its previous-maximum and current-detector
fourth moments, on the original pair masks.

[HierarchyPilotStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyPilotStability.lean)
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
error. The [checked pilot client](../../CslibFrontierTests/PilotRowStability.lean) changes the raw
K-rank from zero to the gate cutoff while fixing the inspected entry, and checks changes to
the actual score, detector and maximum, a correlated nonzero moment, and empty/zero cases.
The shared [rank API](../../CslibFrontier/Foundations/Data/Finset/KthLargest/Stability.lean)
also removes repeated normalization proofs in dense and correction preparation.

For a computed initial-pilot fragment, use
[InitialPilotScore](../../CslibFrontier/Computability/LogSpaceDerandomization/InitialPilotScore.lean).
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

The [computed regression](../../CslibFrontierTests/InitialPilotScore.lean) uses a bounded routed
top bin with a smooth scalar switch, the identity base over `ZMod 5`, source exponent one,
full terminal rate, distinct roles and nonempty suffixes. Its computed lower RAW walk and
upper score are both one or both zero according to the same original source frame, at
positive allocated lengths. The two environments agree on every other role, including
the terminal frame. This is a nonconstant correlated exact-on-slice case; it does
not establish nonzero mixing error or later recursive closure.

The [source-aware detector](../../CslibFrontier/Computability/LogSpaceDerandomization/InitialPilotDetector.lean)
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

The [first positive direct pilot constructor](../../CslibFrontier/Computability/LogSpaceDerandomization/InitialPilotCorrection.lean)
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

The [completed stochastic first pilot correction](../../CslibFrontier/Computability/LogSpaceDerandomization/InitialPilotCompleted.lean)
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
RL=L are not supplied by this single-bin first-pilot fragment.

The regressions additionally check a correlated detector moment of
`1/32`, a distinct child normalization `1/16`, and nonconstant padded frame source/rank
densities `16/625` and `81/625`.

## Unfold a lattice Fourier coefficient

Import [`CslibFrontier.Foundations.Analysis.Lattice.Fourier`](../../CslibFrontier/Foundations/Analysis/Lattice/Fourier.lean)
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
[`LatticeFourier.lean` clients](../../CslibFrontierTests/LatticeFourier.lean) derive integrability
and evaluate the Fourier coefficient using Mathlib's Gaussian transform. They include the basis
`(1,0), (1/2,1)` with nonzero dual frequency `(2,0)`, its Gaussian coefficient `exp(-4π)`,
and the zero-frequency mass identity. Run `scripts/build.sh CslibFrontierTests.LatticeFourier`
from the repository root to check these complete examples.

Integrability supplies the almost-everywhere convergence needed for exchanging the sum and
integral. No pointwise convergence or uniform convergence assumption is hidden in this theorem.
The [Poisson API](#apply-lattice-poisson-summation) supplies continuity, reconstruction and
covolume normalization for the stated analytic hypotheses. Smoothing estimates remain separate.

## Compute a Gaussian sign-disagreement probability

Import
[`CslibFrontier.Foundations.Probability.Gaussian.Sheppard`](../../CslibFrontier/Foundations/Probability/Gaussian/Sheppard.lean)
and open the `ProbabilityTheory` namespace to use Sheppard's formula. The space `E` is any
finite-dimensional real inner-product space with its Borel σ-algebra, and `stdGaussian E` is
Mathlib's standard Gaussian measure on it. The event is
`{x | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪v, x⟫}`: zero lies in the half-open interval between the two
projections, so they have opposite signs, up to the null event that a projection is zero.

- For nonzero `u` and `v`, `measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu hv` gives
  probability `InnerProductGeometry.angle u v / π`. The norms need not be equal.
- For unit vectors, `measureReal_stdGaussian_zero_mem_uIoc_eq_arccos hu hv` gives
  `arccos ⟪u, v⟫ / π`, the ρ-correlated form of O'Donnell's Example 11.19 with `ρ = ⟪u, v⟫`.

The checked [`GaussianSheppard.lean` clients](../../CslibFrontierTests/GaussianSheppard.lean)
evaluate both forms in `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℝ (Fin 3)`: angle `π/4`
with unequal norms gives `1/4`, orthogonal unit vectors give `1/2`, opposite vectors give `1`,
and the events for `v` and `-v` have probabilities summing to `1`. Run
`scripts/build.sh CslibFrontierTests.GaussianSheppard` from the repository root to check them.

If a proof needs only an upper bound, or the vectors may be zero, the older
`measureReal_stdGaussian_mem_uIoc_le_angle` (equal norms, any threshold `t`) still applies. For
Gaussian noise stability and its halfspace formula, see
[Compute Gaussian noise stability](#compute-gaussian-noise-stability).

## Compute Gaussian noise stability

Import
[`CslibFrontier.Foundations.Probability.Gaussian.Correlated`](../../CslibFrontier/Foundations/Probability/Gaussian/Correlated.lean)
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

The checked [`GaussianCorrelated.lean` clients](../../CslibFrontierTests/GaussianCorrelated.lean)
evaluate halfspace stability at `ρ = 1, 0, 1/2, -1`, Example 11.19 at `ρ = 0`, a concrete
projection pair and the `ρ = ±1` laws. Run `scripts/build.sh CslibFrontierTests.GaussianCorrelated`
from the repository root to check them.

Halfspaces are stated with `a ⬝ᵥ z` on `ι → ℝ`, which has no inner-product instance, and the
open form uses `sgn 0 = -1`. Stability is defined for every `f`. The Bochner integral is `0`
when `f z * f z'` is not integrable, so prove integrability before reading a value off a
non-`L²` function. For the noise operator `U_ρ`, see
[Apply the Gaussian noise operator](#apply-the-gaussian-noise-operator).

## Apply the Gaussian noise operator

Import
[`CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator`](../../CslibFrontier/Foundations/Probability/Gaussian/NoiseOperator.lean)
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

The checked [`GaussianNoiseOperator.lean` clients](../../CslibFrontierTests/GaussianNoiseOperator.lean)
cover coordinate and linear inputs, `U_0` and `U_1`, the stability of a constant and of a
coordinate, a self-adjointness and an additivity instance, `L²` and `L^∞` contraction, and mean
preservation. Run `scripts/build.sh CslibFrontierTests.GaussianNoiseOperator` from the repository
root to check them.

Additivity, `gaussianNoiseOp_add`, holds only `γ`-almost everywhere, because the Bochner integral
is `0` off the integrable functions; scaling by a constant holds everywhere. For multilinear
polynomials, the semigroup law `U_ρ U_σ = U_ρσ` and continuity at `ρ = 1`, see
[Compose Gaussian noise operators](#compose-gaussian-noise-operators). For `U_ρ` on Hermite
expansions (Proposition 11.37), see
[Expand Gaussian functions in the Hermite basis](#expand-gaussian-functions-in-the-hermite-basis).

## Compose Gaussian noise operators

Multilinear polynomials stay in
[`CslibFrontier.Foundations.Probability.Gaussian.NoiseOperator`](../../CslibFrontier/Foundations/Probability/Gaussian/NoiseOperator.lean),
and the semigroup law and continuity live in
[`CslibFrontier.Foundations.Probability.Gaussian.NoiseSemigroup`](../../CslibFrontier/Foundations/Probability/Gaussian/NoiseSemigroup.lean).
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
[`CslibFrontier.Foundations.MeasureTheory.Integral.Pi`](../../CslibFrontier/Foundations/MeasureTheory/Integral/Pi.lean).

The checked [`GaussianNoiseSemigroup.lean` clients](../../CslibFrontierTests/GaussianNoiseSemigroup.lean)
compute `U_{1/2} U_{1/2} (x₀ x₁)` both through the semigroup law and through Fact 11.13 twice,
check the boundary cases `ρ₂ = 0` and `ρ₁ = -1`, and apply continuity to a coordinate and to a
discontinuous halfspace indicator. Run `scripts/build.sh CslibFrontierTests.GaussianNoiseSemigroup`
from the repository root to check them; the monomial clients are in
`CslibFrontierTests.GaussianNoiseOperator`.

Smoothness of `U_ρ f` for `|ρ| < 1` (Proposition 11.16) is in
[Show that Gaussian noise smooths](#show-that-gaussian-noise-smooths).
For the derivative of `ρ ↦ U_ρ f` in `L²`, see
[Differentiate Gaussian noise with the Ornstein–Uhlenbeck operator](#differentiate-gaussian-noise-with-the-ornsteinuhlenbeck-operator).

## Show that Gaussian noise smooths

Import
[`CslibFrontier.Foundations.Probability.Gaussian.NoiseSmooth`](../../CslibFrontier/Foundations/Probability/Gaussian/NoiseSmooth.lean)
and open the `ProbabilityTheory` namespace, together with `open scoped ContDiff` for the `∞`
order of smoothness. Write `γ` for `Measure.pi fun _ : ι => gaussianReal 0 1` as before.

- `contDiff_gaussianNoiseOp hρ hf : ContDiff ℝ ∞ (gaussianNoiseOp ρ f)` for `hρ : |ρ| < 1` and
  `hf : Integrable f γ` (Proposition 11.16). It concerns the pointwise integral
  `gaussianNoiseOp ρ f` of Definition 11.12, so it holds at every point: for
  `h := contDiff_gaussianNoiseOp hρ hf`, `h.continuous` gives continuity and
  `(h.differentiable (by simp)).differentiableAt` differentiability at any `z`
  (`ContDiff.differentiable` takes the side condition `∞ ≠ 0`). At `ρ = ±1` there is no noise and
  the conclusion fails for discontinuous `f`.
- `gaussianNoiseOp_congr_ae_of_abs_lt_one hρ h : gaussianNoiseOp ρ f = gaussianNoiseOp ρ f'` for
  `hρ : |ρ| < 1` and `h : f =ᵐ[γ] f'`, with no measurability hypothesis. It is an equality of
  functions, not only `γ`-almost everywhere as `gaussianNoiseOp_congr_ae` gives for `|ρ| ≤ 1`, so
  `U_ρ f` is a canonical smooth function of the `L¹` class of `f`: changing `f` on a `γ`-null set
  changes `U_ρ f` nowhere.
- `gaussianNoiseOp_eq_integral_prod_div_mul hρ hf z` writes `U_ρ f z` as an integral against the
  Mehler kernel (kernel or density form): for `hρ : |ρ| < 1` and
  `hf : AEStronglyMeasurable f γ`, `gaussianNoiseOp ρ f z` is the integral against `γ` of
  `(∏ i, gaussianPDFReal (ρ * z i) (1 - ρ ^ 2).toNNReal (y i) / gaussianPDFReal 0 1 (y i)) * f y`.
  The one-dimensional density, `gaussianReal_eq_withDensity_div m hv` for `hv : v ≠ 0`, is in
  [`CslibFrontier.Foundations.Probability.Gaussian.Real`](../../CslibFrontier/Foundations/Probability/Gaussian/Real.lean).

The proof writes `U_ρ f` as a Gaussian in `z` times a Laplace transform
`z ↦ ∫ y, exp (φ y z) • h y` with all exponential moments. Its smoothness is the general
`contDiff_integral_exp_smul hφ hg hint : ContDiff ℝ ∞ fun w => ∫ a, rexp (φ a w) • g a ∂μ`, for
`φ : α → V →L[ℝ] ℝ` with `hφ : AEStronglyMeasurable φ μ`, `g : α → E` with
`hg : AEStronglyMeasurable g μ` and values in a complete space, and
`hint : ∀ c, Integrable (fun a => rexp (c * ‖φ a‖) * ‖g a‖) μ`. It and the derivative formula
`hasFDerivAt_integral_exp_smul`, both in the root namespace, are in
[`CslibFrontier.Foundations.Analysis.Calculus.ParametricIntegralExp`](../../CslibFrontier/Foundations/Analysis/Calculus/ParametricIntegralExp.lean).
Products of densities are in
[`CslibFrontier.Foundations.MeasureTheory.Constructions.PiWithDensity`](../../CslibFrontier/Foundations/MeasureTheory/Constructions/PiWithDensity.lean):
`MeasureTheory.Measure.pi_withDensity hf` identifies `Measure.pi fun i => (μ i).withDensity (f i)`
with `(Measure.pi μ).withDensity fun x => ∏ i, f i (x i)` for `[∀ i, SigmaFinite (μ i)]`,
measurable densities `hf : ∀ i, Measurable (f i)` and
`[∀ i, SigmaFinite ((μ i).withDensity (f i))]` (the last is needed to form the left-hand side).
Its proof uses the Tonelli theorem `MeasureTheory.lintegral_fintype_prod_eq_prod hf`,
`∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i` for σ-finite `μ i` and measurable
`f i`, with its `Fin n` form `MeasureTheory.lintegral_fin_nat_prod_eq_prod`, both in
[`CslibFrontier.Foundations.MeasureTheory.Integral.Pi`](../../CslibFrontier/Foundations/MeasureTheory/Integral/Pi.lean).
Its direct Bochner counterpart is Mathlib's `MeasureTheory.integral_fintype_prod_eq_prod`; for a
product over a subset of the coordinates under product probability measures, use
`MeasureTheory.integral_finset_prod_pi_eq_prod` from the previous section.

The checked [`GaussianNoiseSmooth.lean` clients](../../CslibFrontierTests/GaussianNoiseSmooth.lean)
show that `U_{1/2}` of a discontinuous halfspace indicator is smooth and continuous, that
`U_{-1/2}` of it is differentiable at the jump, that `U_1` of it is not smooth, that the Mehler
kernel integrates to `1`, and that `U_{1/2}` of the indicator of a point vanishes everywhere. They
also apply `contDiff_integral_exp_smul` to the moment generating function of a standard Gaussian,
`lintegral_fintype_prod_eq_prod` to a product of two Gaussian densities, and `pi_withDensity` to
the standard Gaussian measure on `ℝ²`. Run `scripts/build.sh CslibFrontierTests.GaussianNoiseSmooth`
from the repository root to check them. Analyticity of `U_ρ f` and bounds on its derivatives are
not formalized.

## Integrate Hermite polynomials against a Gaussian

Gaussian integration by parts is in
[`CslibFrontier.Foundations.Probability.Gaussian.Stein`](../../CslibFrontier/Foundations/Probability/Gaussian/Stein.lean),
the Hermite facts in
[`CslibFrontier.Foundations.Probability.Gaussian.Hermite`](../../CslibFrontier/Foundations/Probability/Gaussian/Hermite.lean),
and polynomial identities for Mathlib's probabilists' `Polynomial.hermite` in
[`CslibFrontier.Foundations.RingTheory.Polynomial.Hermite`](../../CslibFrontier/Foundations/RingTheory/Polynomial/Hermite.lean).
Open `ProbabilityTheory` and `Polynomial`; `hermite n : ℤ[X]` is evaluated at a real point with
`aeval x (hermite n)`.

- `integral_sub_mul_gaussianReal hf hfi hxf hf'` is Stein's lemma
  `∫ (x - μ) * f x ∂gaussianReal μ v = v * ∫ f' x ∂gaussianReal μ v`, for `f` with derivative `f'`
  everywhere and the three integrability hypotheses. For a polynomial `p`,
  `integral_sub_mul_eval_gaussianReal p` needs no hypotheses.
- `derivative_hermite_succ` (`H_{n+1}' = (n + 1) H_n`) and `hermite_succ_succ` (the three-term
  recurrence) are the polynomial inputs.
- `integral_eval_mul_aeval_hermite p k` moves derivatives onto `p`:
  `E[p · H_k] = E[p^{(k)}]` under `gaussianReal 0 1`. `integral_aeval_hermite_mul_aeval_hermite`
  is O'Donnell's (11.9), `E[H_j H_k] = if j = k then j! else 0`.
- `normalizedHermite j x = H_j(x) / √(j!)` (Definition 11.29) with `normalizedHermite_def`,
  `_zero`, `_one`, `_two`; `integral_normalizedHermite_mul_normalizedHermite` is orthonormality.
  `integral_normalizedHermite_gaussianNoise hρ` gives the eigenvalue identity
  `E_g[h_n(ρ x + √(1 - ρ²) g)] = ρ ^ n h_n(x)`, and
  `integral_correlatedGaussian_normalizedHermite hρ j k` is Proposition 11.31.
- `multiHermite α z = ∏ i, h_{α i}(z i)` (Definition 11.32) with `multiHermite_def`.
  `gaussianNoiseOp_multiHermite hρ α z` is the pointwise eigenvalue identity
  `U_ρ h_α = ρ ^ |α| h_α`; `integral_multiHermite_mul_multiHermite` is orthonormality under
  `Measure.pi fun _ => gaussianReal 0 1`; and `integral_correlatedGaussianPi_multiHermite hρ α β` is
  Proposition 11.33. `multiHermite_indicator S z` identifies `h_S` with the monomial `∏ i ∈ S, z i`.
  All `ρ` hypotheses are `|ρ| ≤ 1`.

The checked [`GaussianHermite.lean` clients](../../CslibFrontierTests/GaussianHermite.lean)
compute `H_2'` and `H_3` from the recurrence, apply Stein's lemma to the identity, check the
eigenvalue and norm of `h_2`, `E[h_1 h_3] = 0`, `E[H_3²] = 6` and `E[x³ H_3] = 6`, instantiate
Propositions 11.31 and 11.33 in one and two dimensions, and recover Fact 11.13 from
`multiHermite_indicator`. Run `scripts/build.sh CslibFrontierTests.GaussianHermite` from the
repository root to check them.

For completeness of the Hermite basis, Hermite coefficients and Plancherel, see
[Expand Gaussian functions in the Hermite basis](#expand-gaussian-functions-in-the-hermite-basis);
for the Hermite differential equation and the Ornstein–Uhlenbeck operator, see
[Differentiate Gaussian noise with the Ornstein–Uhlenbeck operator](#differentiate-gaussian-noise-with-the-ornsteinuhlenbeck-operator).

## Expand Gaussian functions in the Hermite basis

Import
[`CslibFrontier.Foundations.Probability.Gaussian.HermiteExpansion`](../../CslibFrontier/Foundations/Probability/Gaussian/HermiteExpansion.lean)
for the Hermite basis and expansions, and
[`CslibFrontier.Foundations.Probability.Gaussian.PolynomialDense`](../../CslibFrontier/Foundations/Probability/Gaussian/PolynomialDense.lean)
for the density of polynomials. Open `MeasureTheory` and `ProbabilityTheory`, and write `γ` for
`Measure.pi fun _ : ι => gaussianReal 0 1` on `ι → ℝ` with `[Fintype ι]`. Membership in `L²(γ)` is
`hf : MemLp f 2 γ`, and `hf.toLp f : Lp ℝ 2 γ` is the class of `f`; `memLp_multiHermite α` supplies
it for `h_α`.

- `topologicalClosure_span_prod_pow_pi_gaussianReal` says the monomials `∏ i, z i ^ k i` span a
  dense subspace of `Lp ℝ 2 γ` (Theorem 11.22 for `p = 2`). For a single function,
  `exists_eLpNorm_sub_eval_lt_pi_gaussianReal hf hε` gives a polynomial
  `p : MvPolynomial ι ℝ` with `eLpNorm (f - fun z => MvPolynomial.eval z p) 2 γ < ε` for
  `0 < ε`. `ae_eq_zero_of_forall_integral_mul_prod_pow_eq_zero_pi_gaussianReal hf h` is the
  underlying fact: an `L²` function orthogonal to every monomial is `0` almost everywhere.
- `hermiteBasis ι : HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 γ)` is the Hermite basis (Proposition 11.33),
  with `hermiteBasis_apply α` identifying its vectors with the classes of `h_α`.
  `orthonormal_multiHermite` and `topologicalClosure_span_multiHermite` are its two halves. In one
  dimension, `normalizedHermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1))` is
  Proposition 11.30, with `normalizedHermiteBasis_apply j` giving the class of `h_j` (membership
  `memLp_normalizedHermite j`, in the `Hermite` module).
- `hermiteCoeff f α = ∫ z, f z * multiHermite α z ∂γ` is `f̂(α)`, unfolded by `hermiteCoeff_def`;
  `hermiteBasis_repr hf α` says it is the `α`-th coordinate of `hf.toLp f`, and
  `hermiteCoeff_coeFn v α` says the same for an element `v` of `L²(γ)`. Conversely,
  `hermiteBasis_repr_tsum_smul hc α` reads off the coordinates of `∑' β, c β • hermiteBasis ι β`
  for `c ∈ ℓ²`. `hermiteCoeff_zero f`
  is the mean `∫ z, f z ∂γ`; `hermiteCoeff_add hf hg α` (both in `L²`), `hermiteCoeff_const_mul`
  and `hermiteCoeff_congr_ae` give linearity and invariance under `=ᵐ[γ]`.
- `hermiteCoeff_multiHermite α β` is `if α = β then 1 else 0`. For a finite combination,
  `hermiteCoeff_sum_mul_multiHermite s c β α` gives `∑ j ∈ s, if β j = α then c j else 0`, and
  `hermiteCoeff_sum_mul_prod s c T` (with `[DecidableEq ι]`) reads off the coefficient
  `if T ∈ s then c T else 0` of a multilinear polynomial `∑ S ∈ s, c S * ∏ i ∈ S, z i` at the
  indicator multi-index of `T` (Remark 11.35).
- `hasSum_hermiteCoeff_smul hf` is the Hermite expansion `f = ∑ α, f̂(α) h_α` in `Lp ℝ 2 γ`
  (Definition 11.34), and `tendsto_sum_degree_le_hermiteCoeff_smul hf` (with `[DecidableEq ι]`)
  its partial sums over `∑ i, α i ≤ k`. Uniqueness holds in both forms: any `c` whose
  degree-ordered partial sums converge to `hf.toLp f`
  (`hermiteCoeff_eq_of_tendsto_sum_degree_le hf h`, the book's definition), or with
  `HasSum (fun α => c α • (memLp_multiHermite α).toLp (multiHermite α)) (hf.toLp f)`
  (`hermiteCoeff_eq_of_hasSum hf h`), equals `hermiteCoeff f`.
- Plancherel and Parseval (Proposition 11.36) are `hasSum_hermiteCoeff_mul_hermiteCoeff hf hg` and
  `hasSum_hermiteCoeff_sq hf`, with `tsum` forms
  `integral_mul_eq_tsum_hermiteCoeff_mul_hermiteCoeff` and `integral_sq_eq_tsum_hermiteCoeff_sq`.
- For `|ρ| ≤ 1`, `hermiteCoeff_gaussianNoiseOp hρ hf α` is `(U_ρ f)^(α) = ρ ^ |α| f̂(α)`, and
  `hasSum_hermiteCoeff_gaussianNoiseOp_smul hρ hf` the expansion of `U_ρ f` (Proposition 11.37).
  `hasSum_gaussianNoiseStability hρ hf` and `gaussianNoiseStability_eq_tsum hρ hf` give
  `Stab_ρ[f] = ∑ α, ρ ^ |α| f̂(α)²`.

Like `gaussianNoiseStability`, `hermiteCoeff f` is defined for every `f`, and is `0` at `α` when
`f * h_α` is not integrable; every expansion theorem takes `MemLp f 2 γ`. The inner product of two
`L²` classes, `⟪hf.toLp f, hg.toLp g⟫ = ∫ conj (f a) * g a ∂μ`, is
`MeasureTheory.L2.inner_toLp_toLp` in
[`CslibFrontier.Foundations.MeasureTheory.Function.L2Space`](../../CslibFrontier/Foundations/MeasureTheory/Function/L2Space.lean).
To prove that another family `v k` of real `L²(μ)` functions spans a dense subspace, use
`MeasureTheory.L2.topologicalClosure_span_toLp_eq_top hv h` from the same module, where `h` says
that every `f ∈ L²(μ)` with `∫ a, f a * v k a ∂μ = 0` for all `k` is `0` almost everywhere.

The checked [`GaussianHermiteExpansion.lean` clients](../../CslibFrontierTests/GaussianHermiteExpansion.lean)
approximate a halfspace indicator by a polynomial, read basis coordinates in both bases, compute
`E[(z₀ z₁)²] = 1` and `E[x⁴] = 3` by Parseval and `E[x² h₂] = √2` by Plancherel, read off a
multilinear polynomial's coefficient, compute the mean `f̂(0) = 1 / 2` of a halfspace indicator,
truncate expansions by degree, recover Proposition 11.37 from uniqueness and compute
`Stab_ρ[h_α] = ρ ^ |α|` from the series. Run
`scripts/build.sh CslibFrontierTests.GaussianHermiteExpansion` from the repository root to check
them.

Theorem 11.22 is formalized only for `p = 2`, where the orthogonal complement of the
polynomials in the Hilbert space `L²(γ)` is `0`. The duality argument used here would need, for
`p > 2`, every continuous linear functional on `L^p` to be integration against an `L^q` function,
which Mathlib does not provide.
The case `1 ≤ p < 2` follows from `p = 2`, since `‖·‖_p ≤ ‖·‖_2` for a probability measure and
`L²` is dense in `L^p`, but it is not stated.

## Differentiate Gaussian noise with the Ornstein–Uhlenbeck operator

Import
[`CslibFrontier.Foundations.Probability.Gaussian.OrnsteinUhlenbeck`](../../CslibFrontier/Foundations/Probability/Gaussian/OrnsteinUhlenbeck.lean)
and open `MeasureTheory` and `ProbabilityTheory`. Write `γ` for
`Measure.pi fun _ : ι => gaussianReal 0 1` with `[Fintype ι]`, and `|α|` for the total degree
`((∑ i, α i : ℕ) : ℝ)`, as the statements do. O'Donnell's Ornstein–Uhlenbeck operator
`L f = (d/dρ) U_ρ f |_{ρ = 1}` (Definition 11.24) appears in two forms.

- On smooth functions, it is the differential expression `x · ∇f - Δf` (Proposition 11.26).
  Partial derivatives are derivatives along coordinate lines,
  `∂ᵢ f z = deriv (fun t => f (Function.update z i t)) (z i)`, and the statements that use them
  take `[DecidableEq ι]`.
- On `L²(γ)`, it is `ornsteinUhlenbeck f : Lp ℝ 2 γ`, the Hermite series
  `∑' α, (|α| * hermiteCoeff f α) • hermiteBasis ι α`, unfolded by `ornsteinUhlenbeck_def`. Its
  domain is the predicate `MemOrnsteinUhlenbeckDomain f`: `MemLp f 2 γ` and
  `Summable fun α => |α| ^ 2 * hermiteCoeff f α ^ 2`. Build or split it with
  `memOrnsteinUhlenbeckDomain_iff`, `.memLp` and `.summable`. Outside the domain,
  `ornsteinUhlenbeck f` is a junk value; theorems about `L f` assume the domain.

### The differential form

- `Polynomial.X_mul_derivative_hermite_sub n`, in
  [`CslibFrontier.Foundations.RingTheory.Polynomial.Hermite`](../../CslibFrontier/Foundations/RingTheory/Polynomial/Hermite.lean),
  is the Hermite differential equation `X * H_n' - H_n'' = n * H_n` in `ℤ[X]` (Exercise 11.10(c)).
  `mul_deriv_normalizedHermite_sub n x` evaluates it for `h_n`, and
  `sum_mul_deriv_multiHermite_update_sub α z` is `x · ∇h_α - Δh_α = |α| h_α` (Propositions 11.26
  and 11.40 on the Hermite basis).
- `integral_mul_deriv_sub_deriv_deriv_mul_gaussianReal hf hg h₁ h₂ h₃ h₄` is integration by parts
  `E[(x f' - f'') g] = E[f' g']` under `gaussianReal 0 1` (Proposition 11.28 in one dimension).
  It needs `Differentiable ℝ (deriv f)`, `Differentiable ℝ g` and integrability of `f' g`,
  `x f' g`, `f'' g` and `f' g'`; it is Stein's lemma `integral_sub_mul_gaussianReal` applied to
  `f' g`.
- `integral_mul_deriv_update_sub_mul_pi_gaussianReal i …` is the same formula for one coordinate
  under `γ`. `integral_sum_mul_deriv_update_sub_mul_pi_gaussianReal` sums it to
  `⟨x · ∇f - Δf, g⟩ = ∑ i, ⟨∂ᵢf, ∂ᵢg⟩` (Exercise 11.8). Each of its hypotheses is quantified over
  `i`, and the differentiability hypotheses also over every line `z`.
- The reduction to one dimension uses `MeasureTheory.integral_integral_update` and
  `MeasureTheory.ae_integrable_update` in
  [`CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate`](../../CslibFrontier/Foundations/MeasureTheory/Integral/PiUpdate.lean).

### The operator on `L²`

Derivatives of `ρ ↦ U_ρ f` are taken of any family `u : ℝ → Lp ℝ 2 γ` with
`hu : ∀ ρ, |ρ| ≤ 1 → u ρ =ᵐ[γ] gaussianNoiseOp ρ f`; its values outside `[-1, 1]` do not matter.
For instance, take
`u ρ = if hρ : |ρ| ≤ 1 then (hf.gaussianNoiseOp hρ one_le_two).toLp (gaussianNoiseOp ρ f) else 0`,
where `hu` follows from `MemLp.coeFn_toLp`. The hypothesis on `f` is `MemLp f 2 γ` or
`MemOrnsteinUhlenbeckDomain f`, as each statement below says.

- **Coordinates.** `hermiteBasis_repr_ornsteinUhlenbeck hf α` and
  `hermiteCoeff_ornsteinUhlenbeck hf α` give `(L f)^(α) = |α| f̂(α)` for `f` in the domain
  (Proposition 11.40). `memℓp_two_sum_mul_iff` converts between `Memℓp (fun α => |α| * c α) 2`
  and `Summable fun α => |α| ^ 2 * c α ^ 2`.
- **Definition 11.24.** For `f` in the domain,
  `hasDerivWithinAt_gaussianNoiseOp hf hu` says that `u` has left derivative `L f` at `ρ = 1`
  (`HasDerivWithinAt u (ornsteinUhlenbeck f) (Set.Iic 1) 1`).
  `hasDerivWithinAt_gaussianNoiseOp_exp_neg_zero hf hu` is the same in exponential time `ρ = e^{-t}`:
  `t ↦ u (Real.exp (-t))` has right derivative `-ornsteinUhlenbeck f` at `t = 0`.
- **Exercise 11.18.** Take `hf : MemLp f 2 γ`.
  - `eq_ornsteinUhlenbeck_of_hasDerivWithinAt hf hu hg` says that every left derivative `g` at
    `ρ = 1` equals `ornsteinUhlenbeck f`.
  - `memOrnsteinUhlenbeckDomain_of_hasDerivWithinAt hf hu hg` says that such a derivative exists
    only on the domain.
  - `exists_hasDerivWithinAt_gaussianNoiseOp_iff hf hu` is the resulting equivalence.
  - `memOrnsteinUhlenbeckDomain_gaussianNoiseOp hf hρ` is part (c): `U_ρ f` is in the domain for
    every `f ∈ L²` and `|ρ| < 1`.
  - `MemOrnsteinUhlenbeckDomain.gaussianNoiseOp hf hρ` says that `U_ρ` preserves the domain for
    `|ρ| ≤ 1`.
- **Proposition 11.27.** `hasDerivAt_gaussianNoiseOp hf hu hρ` takes `hf : MemLp f 2 γ` and
  `|ρ| < 1`, including `ρ = 0`. It gives the derivative
  `∑' α, (|α| * ρ ^ (∑ i, α i - 1) * hermiteCoeff f α) • hermiteBasis ι α`.
  - `memℓp_mul_pow_mul_hermiteCoeff hf hρ` together with `hermiteBasis_repr_tsum_smul` (in
    `HermiteExpansion`) reads off its coordinates.
  - For `ρ ≠ 0`, `hasDerivAt_gaussianNoiseOp_eq_inv_smul_ornsteinUhlenbeck hf hu hρ hρ0` gives
    `ρ⁻¹ • ornsteinUhlenbeck (gaussianNoiseOp ρ f)` with only `MemLp f 2 γ`.
  - For `f` in the domain, `hasDerivAt_gaussianNoiseOp_eq_inv_smul_gaussianNoiseOp` gives
    `ρ⁻¹ U_ρ L f`.
  - `ornsteinUhlenbeck_gaussianNoiseOp hf hρ` is `L (U_ρ f) = U_ρ (L f)` in `Lp ℝ 2 γ` for
    `|ρ| ≤ 1`.
  - `hasDerivAt_gaussianNoiseOp_exp_neg hf hu ht` is `(d/dt) U_{e^{-t}} f = -L U_{e^{-t}} f` for
    `0 < t`.
  - On the domain, `hasDerivWithinAt_Icc_gaussianNoiseOp hf hu hρ` gives the series derivative
    within `Set.Icc (-1) 1` at every `|ρ| ≤ 1`, including the endpoints.

To identify two vectors of `Lp ℝ 2 γ`, compare Hermite coordinates: rewrite with the lemmas above
and with `hermiteBasis_repr` and `hermiteCoeff_coeFn` from the `HermiteExpansion` module, then
apply `(hermiteBasis ι).repr.injective`. A derivative is unique, so `HasDerivAt.unique` transfers
the computed coordinates to any other derivative.

### Checked clients and scope

The checked [`GaussianOrnsteinUhlenbeck.lean` clients](../../CslibFrontierTests/GaussianOrnsteinUhlenbeck.lean)
cover the following:

- the Hermite equation for `H_2 = X² - 1` and the eigenvalue identity for `h_1`;
- the value `1` of the integration-by-parts formula for `f = g = id`, for a coordinate on
  `Unit → ℝ` and for `z₀` on `Fin 2 → ℝ`;
- for `f = h_β`:
  - the coordinates of `L h_β`;
  - `L h_β` as the left derivative at `1`, its uniqueness, and the exponential-time form at
    `t = 0`;
  - the derivative at `|ρ| < 1`;
  - `ρ⁻¹ L U_ρ h_β` and `ρ⁻¹ U_ρ L h_β` at `ρ = 1/2`;
  - the form for `t > 0`;
- a function `f = ∑ n, (n + 1)⁻¹ h_n` in `L²` but outside the domain:
  - `ρ ↦ U_ρ f` has no left derivative at `1`;
  - `U_{1/2} f` is in the domain;
  - `ρ ↦ U_ρ f` is still differentiable at `ρ = 1/2`.

Run `scripts/build.sh CslibFrontierTests.GaussianOrnsteinUhlenbeck` from the repository root to
check them.

Not formalized:

- Proposition 11.26 for general smooth `f`; the identification of `ornsteinUhlenbeck f` with
  `x · ∇f - Δf` is proved only for Hermite polynomials;
- the symmetric form `⟨f, L g⟩ = ⟨L f, g⟩` of Proposition 11.28 on `L²`;
- pointwise, rather than `L²`, derivatives of `U_ρ f`;
- `L` as a Mathlib unbounded operator (`LinearPMap`). Here it is a function with a separate domain
  predicate.

The book derives Proposition 11.27 from the semigroup law; here it is read off the Hermite
expansion of `U_ρ f`.

## Compare bits with Gaussians by the invariance principle

Import
[`CslibFrontier.Foundations.BooleanAnalysis.Invariance`](../../CslibFrontier/Foundations/BooleanAnalysis/Invariance.lean)
for functions on the cube, or
[`CslibFrontier.Foundations.Probability.Multilinear.Invariance`](../../CslibFrontier/Foundations/Probability/Multilinear/Invariance.lean)
for formal multilinear polynomials. Open `ProbabilityTheory` (and `Cslib.BitString` for the cube).
A formal multilinear polynomial is its coefficient function `c : Finset ι → ℝ`;
`multilinearEval c z = ∑ S, c S * ∏ i ∈ S, z i` and `multilinearInfluence c i = ∑ S ∋ i, c S ^ 2`.
Degree at most `k` is the hypothesis `∀ S, k < #S → c S = 0`. The variables are independent with
laws `μ i : Measure ℝ`, through `Measure.pi μ`, and `HasInvarianceMoments (μ i)` is O'Donnell's
Hypothesis 11.65: mean `0`, second moment `1`, third moment `0` and fourth moment at most `9`. Its
first field, `memLp_four : MemLp id 4 μ`, also requires the fourth moment to be finite, so that the
moment integrals are meaningful. The structure does not include `IsProbabilityMeasure`; the
theorems take `[∀ i, IsProbabilityMeasure (μ i)]` as a separate instance argument.
`hasInvarianceMoments_gaussianReal` and `hasInvarianceMoments_rademacher` supply it for standard
Gaussians and uniform random signs.

- `abs_integral_comp_multilinearEval_sub_le` is the Basic Invariance Principle (O'Donnell, §11.6,
  eq. (11.29)): for `ψ` that is `C⁴` with `|iteratedDeriv 4 ψ| ≤ C`, the expectations of
  `ψ (multilinearEval c ·)` under `Measure.pi μ` and `Measure.pi ν` differ by at most
  `C / 12 * 9 ^ k * ∑ t, multilinearInfluence c t ^ 2`.
- `abs_integral_comp_multilinearEval_sub_le_of_influence_le` is Corollary 11.67. It assumes
  `∑ S with S ≠ ∅, c S ^ 2 ≤ 1` (variance at most one) and `multilinearInfluence c t ≤ ε` for every
  `t`, together with `0 ≤ ε`, and bounds the difference by `C / 12 * k * 9 ^ k * ε`.
- `abs_integral_comp_multilinearEval_sub_le_of_contDiff_three` is the `C³` form
  `C / 3 * 3 ^ k * ∑ t, multilinearInfluence c t ^ ((3 : ℝ) / 2)`. It is the analogue, under
  Hypothesis 11.65, of Remark 11.66, whose hypothesis is `(2, 3, ρ)`-hypercontractivity instead.
- On the cube, `abs_expect_comp_sub_integral_comp_multilinearEval_le` and its `_of_influence_le` and
  `_of_contDiff_three` forms compare `𝔼 x, ψ (f x)` at uniform bits with
  `∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ`. They assume `totalDegree f ≤ k`
  and use `influence i f` and the variance `𝔼 x, (f x - 𝔼 y, f y) ^ 2`. The translation goes
  through `integral_pi_rademacher`, `multilinearEval_fourierCoeff_signVal` and
  `multilinearInfluence_fourierCoeff`.

The proof is the replacement method. `MeasureTheory.abs_integral_pi_sub_le_sum` in
[`PiUpdate`](../../CslibFrontier/Foundations/MeasureTheory/Integral/PiUpdate.lean) telescopes over the
hybrids `Measure.pi (s.piecewise ν μ)` and applies to any integrand. The Bonami Lemma for these
variables, `integral_multilinearEval_pow_four_le`, is in
[`Multilinear/Bonami`](../../CslibFrontier/Foundations/Probability/Multilinear/Bonami.lean). It is
the case `B = 9`, variance `1`, of `isReasonable_multilinearEval` in the same file (Corollary 9.6),
and is derived from it. Cauchy–Schwarz for real integrals,
`MeasureTheory.sq_integral_mul_le`, needs no sign condition. It is in
[`Integral/CauchySchwarz`](../../CslibFrontier/Foundations/MeasureTheory/Integral/CauchySchwarz.lean)
with `MeasureTheory.integrable_pow_of_memLp` and `MeasureTheory.integrable_abs_pow_of_memLp`, which
give integrability of the moments of order `j ≤ n` of a variable in `Lⁿ`.

The checked [`MultilinearInvariance.lean` clients](../../CslibFrontierTests/MultilinearInvariance.lean)
cover Hypothesis 11.65 for Gaussians and signs and its failure for a point mass, and bits versus
Gaussians for any function of two bits with `ψ = cos` (`C⁴`) and `ψ = sin` (`C³`). They also show
that a degree-`0` polynomial has exactly equal expectations. Run
`scripts/build.sh CslibFrontierTests.MultilinearInvariance` from the repository root to check them.

### Lipschitz tests and noise-smoothed functions

For a test function that is only Lipschitz (Corollary 11.68), import
[`CslibFrontier.Foundations.Probability.Multilinear.InvarianceLipschitz`](../../CslibFrontier/Foundations/Probability/Multilinear/InvarianceLipschitz.lean).
`abs_integral_comp_multilinearEval_sub_le_of_lipschitzWith μ ν hμ hν hc hvar hε0 hε hψ` takes the
hypotheses of `abs_integral_comp_multilinearEval_sub_le_of_influence_le` with
`hψ : LipschitzWith K ψ` (`K : ℝ≥0`) in place of the `C⁴` bound, and bounds the difference by
`9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ)`. Integrability of `ψ (multilinearEval c ·)` is proved inside.
The general transfer behind it, `abs_integral_comp_sub_le_of_lipschitzWith hτ h hψ` with
`hτ : 0 ≤ τ`, applies to any two real random variables `X` and `Y`, on different probability
spaces if needed. Here `h` must prove, for every `C⁴` `φ` with `|φ''''| ≤ C`, that `φ ∘ X` and
`φ ∘ Y` are integrable and that their expectations differ by at most `C * τ ^ 4`; measurability of
`X` and `Y` follows from `h`. The result bounds the difference for `ψ` by `16 * K * τ`.
`LipschitzWith.abs_integral_comp_sub_le_sqrt hψ hX hY`, next to Cauchy–Schwarz in
[`Integral/CauchySchwarz`](../../CslibFrontier/Foundations/MeasureTheory/Integral/CauchySchwarz.lean),
gives `|∫ ψ (X ω) - ∫ ψ (Y ω)| ≤ K * √(∫ (X ω - Y ω) ^ 2)` for `MemLp X 2 P` and `MemLp Y 2 P` on a
probability space, and `abs_integral_comp_multilinearEval_sub_le_sqrt μ hμ hψ c d` bounds the
difference for two polynomials `c` and `d` by `K * √(∑ S, (c S - d S) ^ 2)`.

The smoothing is in
[`LipschitzSmoothing.lean`](../../CslibFrontier/Foundations/Analysis/Calculus/LipschitzSmoothing.lean)
(namespace `Real`). `Real.movingAverage h φ s = h⁻¹ * ∫ t in 0..h, φ (s + t)`
(`Real.movingAverage_def`). For continuous `φ`, `Real.hasDerivAt_movingAverage` and
`Real.contDiff_iterate_movingAverage` show that `(Real.movingAverage h)^[m] φ` is `ContDiff ℝ m`.
For `hψ : LipschitzWith K ψ` and `0 < h`, `hψ.abs_iterate_movingAverage_sub_le` gives
`|(movingAverage h)^[m] ψ s - ψ s| ≤ m * K * h`, and
`hψ.abs_iteratedDeriv_iterate_movingAverage_le` gives `|iteratedDeriv (k + 1) _ s| ≤
2 ^ k * K / h ^ k` for `k < m`. `hψ.exists_contDiff_smoothing m hη` is a finite-order form of
Proposition 11.58: a `Cᵐ` function within `K * η` of `ψ` whose `(k + 1)`-th derivative is at most
`(2 * m) ^ k * K / η ^ k`. O'Donnell smooths with a Gaussian, which gives one `C^∞` function for
every order. Here the function and the constant `(2 * m) ^ k` depend on the chosen order `m`, but
the constants are explicit.

On the cube, import
[`CslibFrontier.Foundations.BooleanAnalysis.InvarianceNoise`](../../CslibFrontier/Foundations/BooleanAnalysis/InvarianceNoise.lean)
(namespace `Cslib.BitString`). Its theorems compare `𝔼 x, ψ (f x)` at uniform bits with
`∫ y, ψ (multilinearEval (fourierCoeff f) y) ∂Measure.pi μ` for laws with
`hμ : ∀ i, HasInvarianceMoments (μ i)`, as the cube theorems above do, and take `μ` explicitly.

- `abs_expect_comp_sub_integral_comp_multilinearEval_le_of_lipschitzWith μ hμ hf hvar hε0 hε hψ`
  is inequality (11.31), Corollary 11.68 on the cube, with the bound
  `9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ)`.
- No degree hypothesis is needed in Corollary 11.69. For any `f`, `k : ℕ`, `hvar`, `hε0 : 0 ≤ ε` and
  `hε : ∀ t, ∑ S with t ∈ S ∧ #S ≤ k, fourierCoeff f S ^ 2 ≤ ε` (the influences of `f^{≤k}`),
  `abs_expect_comp_sub_integral_comp_multilinearEval_le_add_sqrt μ hμ k hvar hε0 hε hψ` is
  inequality (11.32): the difference is at most
  `9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) + 2 * K * √(∑ S with k < #S, fourierCoeff f S ^ 2)`.
- A function `h` has no `(ε, δ)`-notable coordinates when
  `hε : ∀ i, stableInfluence (1 - δ) i h ≤ ε` (O'Donnell's Definition 6.9; `stableInfluence_eq_sum`
  gives `∑ S with i ∈ S, (1 - δ) ^ (#S - 1) * fourierCoeff h S ^ 2`). With `hvar` for `h` and
  `0 ≤ δ ≤ 1`,
  `abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_add_pow μ hμ k hvar hε0 hδ0 hδ1 hε hψ`
  is inequality (11.33) in its sharper form: for `f = noiseOp (1 - δ) h` the difference is at most
  `9 * K * 2 ^ k * ε ^ (1 / 4 : ℝ) + 2 * K * (1 - δ) ^ k` for every `k`. The book then bounds
  `(1 - δ) ^ k ≤ exp (-k δ)`.
- `abs_expect_comp_noiseOp_sub_integral_comp_multilinearEval_le_of_lipschitzWith μ hμ hvar hε0 hε1
  hδ0 hδ hε hψ`, for `0 ≤ ε ≤ 1` and `0 ≤ δ ≤ 1 / 20`, is the second statement of Corollary 11.69
  with the explicit constant `15`: the difference is at most `15 * K * ε ^ (δ / 3)`. The proof
  takes `k = ⌊-log ε / 3⌋₊` and treats `ε = 0` by letting `k → ∞`.
- `abs_expect_comp_sub_le_sqrt hψ f g` bounds `|𝔼 x, ψ (f x) - 𝔼 x, ψ (g x)|` by
  `K * √(∑ S, (fourierCoeff f S - fourierCoeff g S) ^ 2)`.

The noise lemmas these use are `sq_fourierCoeff_noiseOp_le` (`(T_ρ f)^(S) ^ 2 ≤ f̂(S) ^ 2` for
`|ρ| ≤ 1`) and `expect_sub_expect_sq_noiseOp_le` (`Var[T_ρ f] ≤ Var[f]`) in `Noise.lean`, and `influence_noiseOp_le_stableInfluence`
(`Inf_i[T_ρ f] ≤ Inf_i^{(ρ)}[f]` for `0 ≤ ρ ≤ 1`), `stableInfluence_noiseOp_le`
(`Inf_i^{(ρ)}[T_σ f] ≤ Inf_i^{(ρ)}[f]` for `0 ≤ ρ` and `|σ| ≤ 1`) and `stableInfluence_mono`
(increasing in `ρ ≥ 0`) in `StableInfluence.lean`.

The checked [`InvarianceLipschitz.lean` clients](../../CslibFrontierTests/InvarianceLipschitz.lean)
smooth `|·|` with explicit bounds, check that its moving average stays `1`-Lipschitz, and apply
Proposition 11.58 to it. For Corollary 11.68 they use the normalized sum and the clamp `u ↦ min 1 (max 0 u)`: the bound
is `18 * m⁻¹ ^ (1/4)`, which for `m = 100⁴` is `18 / 100`, below the trivial bound `1`. They also
instantiate the general and cube (11.31) Lipschitz forms. For Corollary 11.69 they apply (11.32)
with `k = 1` to `∑ aᵢ xᵢ + θ χ_{[n+2]}` with `∑ aᵢ² + θ² ≤ 1` and `aᵢ² ≤ ε`, giving the bound
`9 * 2 * ε ^ (1 / 4) + 2 |θ|` with both terms nonzero. They show that a linear form has
`(1 - δ)`-stable influences `aᵢ²`, compare them across rates and under noise, and conclude that it
has no `(ε, δ)`-notable coordinates when every `aᵢ² ≤ ε`; for the normalized sum of `m = 100⁶⁰` signs and `δ = 1 / 20` the clamp gives the bound
`15 * (1 / m) ^ (1 / 60) = 0.15`, below the trivial bound `1`. Run
`scripts/build.sh CslibFrontierTests.InvarianceLipschitz` from the repository root to check them.

### Reasonable random variables

`IsReasonable B X P`, in
[`Reasonable.lean`](../../CslibFrontier/Foundations/Probability/Reasonable.lean) (namespace
`ProbabilityTheory`), bundles `MemLp X 4 P` with `∫ X ^ 4 ≤ B * (∫ X ^ 2) ^ 2` (O'Donnell,
Definition 9.1). On a finite type, the tail and anticoncentration bounds of
[`PaleyZygmund.lean`](../../CslibFrontier/Foundations/Data/Finset/PaleyZygmund.lean) take the
inequality `𝔼 X ^ 4 ≤ B * (𝔼 X ^ 2) ^ 2` directly, and `isReasonable_uniformOn_univ_iff` converts
between the two. `hasInvarianceMoments_iff`, in
[`Multilinear/Bonami.lean`](../../CslibFrontier/Foundations/Probability/Multilinear/Bonami.lean),
states that `HasInvarianceMoments μ` is `IsReasonable 9 id μ` together with the moments `0`, `1`
and `0`. **The Bonami Lemma** (O'Donnell, Corollary 9.6), `isReasonable_multilinearEval` in
[`Multilinear/Bonami`](../../CslibFrontier/Foundations/Probability/Multilinear/Bonami.lean), takes
laws `μ i` with `IsReasonable B id (μ i)`, `∫ z, z ∂μ i = 0` and `∫ z, z ^ 3 ∂μ i = 0`, and a
polynomial `c` with `c S = 0` whenever `k < #S`, and concludes
`IsReasonable (max B 9 ^ k) (multilinearEval c) (Measure.pi μ)`. The laws may differ and their
second moments are not normalized. `IsReasonable.mono`,
`IsReasonable.const_mul` and `HasLaw.isReasonable_iff` change `B`, rescale and transfer along a
law. A `±1`-valued variable is
`1`-reasonable by `isReasonable_one_of_sq_eq_one`, with its moments from
`integral_sq_eq_one_of_sq_eq_one` and `integral_pow_three_eq_integral_of_sq_eq_one`. For
`hg : HasLaw g (gaussianReal 0 1) P`, `hg.isReasonable_three_of_gaussianReal` gives
`3`-reasonableness, and `hg.integral_eq_zero_of_gaussianReal`,
`hg.integral_sq_eq_one_of_gaussianReal` and `hg.integral_pow_three_eq_zero_of_gaussianReal`
(in [`Gaussian/Moments.lean`](../../CslibFrontier/Foundations/Probability/Gaussian/Moments.lean))
give its moments. The checked [`Reasonable.lean` clients](../../CslibFrontierTests/Reasonable.lean)
cover standard and rescaled Gaussians, uniformly random signs, Hypothesis 11.65 from
reasonableness, a uniform `0`/`1` bit, which is `2`-reasonable but not `1`-reasonable, and the
Bonami Lemma for a sparse sign (`±1` with probability `1 / 20` each), which is `10`-reasonable
but not `9`-reasonable: polynomials in two of them are `100`-reasonable, sharply so for their
product, and sums of `n` of them are `10`-reasonable. Run
`scripts/build.sh CslibFrontierTests.Reasonable` from the repository root to check them.

The following are not formalized: the Lévy-distance form
(Corollary 11.70), cdf-closeness through the Carbery–Wright theorem (Theorem 11.71), the general
Invariance Principle with hypercontractive ensembles, and Majority Is Stablest.

## Evaluate a multi-component conditional walk via validated words

Import
[`CslibFrontier.Probability.PairwiseIndependentHash.ProductValidatedWords`](../../CslibFrontier/Probability/PairwiseIndependentHash/ProductValidatedWords.lean)
and open `Cslib.Probability` to express `t` steps of the lazy conditional product walk over `J`
retention slices and a free-bit torus `(ZMod M)^H` on the ambient space
`ComponentSpace H M P = (∀ j, FrameChannel (P j) H 1) × (Fin H → ZMod M)` (Section 6.1, Lemma 6.3,
items 1–4 of [OpenAI's logspace preprint](../sources.md#openai-logspace26)).
The results on the slice `ComponentSlice H M P L y` (`componentWordWrap_mem`,
`componentWordPerm_wrap_eq` and the two walk identities below) need the instances
`[∀ j, Fact (P j).Prime]` and `[∀ j, NeZero (L j)]` and a proof `hL : ∀ j, L j ≤ P j`, which also
fixes the reindexing `componentEquiv M hL y` in their statements; the checked clients below show
how to discharge them for concrete `P` and `L`.

- Each step label `ComponentLazyStep H J` has `4 * (J + 1) * H^2` choices (`card_componentLazyStep`),
  and each candidate wrap vector lies in `affineWrapBox H = {-3, …, 3}^H` of size `7^H`
  (`card_affineWrapBox`), independently of `P`, `L`, `M`, `y` and `t`.
- Every length-`t` word permutation `componentWordPerm L w z` is a bijection of
  `ComponentSpace H M P` independent of the retained identifiers `y` and preserves uniform
  expectations (`expect_componentWordPerm`).
- Retained identifiers `y` enter only through the endpoint wrap test `IsValidComponentWord`: on
  `ComponentSlice H M P L y`, a unique wrap word in `(affineWrapBox H)^t` survives
  (`existsUnique_isValidComponentWord`, `componentWordWrap_mem`). It reaches the endpoint
  `(G.pow t).neighbor A w` of the walk along `w` (`componentWordPerm_wrap_eq`), where
  `G = (ofPerms (componentMove H M P L)).lazy.reindex (componentEquiv M hL y).symm` is the
  reindexed lazy product multigraph and `G.pow t` is its `t`-th power from
  [`Expander/Power.lean`](../../CslibFrontier/Foundations/Combinatorics/Expander/Power.lean). So
  averaging over move words `w` and summing over wrap words `z` without dividing by `(7^H)^t`
  equals `walk^t` (`walk_pow_componentMove_eq_expect_word`, and iteratively
  `walk_pow_componentMove_eq_iterate`).

The checked [`ProductValidatedWords.lean` clients](../../CslibFrontierTests/ProductValidatedWords.lean)
verify concrete alphabet sizes and step wraps on two channels, over `ZMod 5` and `ZMod 7`, plus the
torus `(ZMod 8)^3`. They check that a one-step word reaches the one-step neighbor, and combine
`walk_pow_componentMove_eq_expect_word` with `ComponentGap` and `SliceFourthMoment` to bound the
`L²` and `L⁴` central moments of the explicit validated-word estimator. Run
`scripts/build.sh CslibFrontierTests.ProductValidatedWords` from the repository root to check them.
This module covers items 1–4 (distributional and combinatorial word identities); explicit machine
or streaming space realization (the post-item space bound of Lemma 6.3) is separate.

## Bound bad visits along an expander walk

Import [VisitCount.lean](../../CslibFrontier/Foundations/Combinatorics/Expander/VisitCount.lean).
Let `G : RotationMap V D`, with finite nonempty vertex type `V` and incident-port type `D`.
Write `L = t + 1` for the number of visited vertices, `m : ℕ` for an integer visit threshold,
and `q = dens W + G.spectralExpansion ^ 2` for a bad-vertex set `W`.
For this set, `G.visitCount W p` counts all `t+1` vertices, including the
initial vertex. Apply `dens_filter_selected_walkAt_mem_le` to arbitrary selected times,
`expect_choose_visitCount_le` for factorial moments, and `dens_filter_visitCount_gt_le`
for strict integer tails. `dens_filter_visitCount_half_lt` bounds a strict majority of
bad samples by `(32 * dens W)^((t+1)/4)` when expansion is below `sqrt(dens W)`.
The [checked clients](../../CslibFrontierTests/ExpanderVisitCount.lean) cover nonconsecutive
times excluding zero, computed counts, boundaries, and even/odd majority events.
Goldreich Exercise 8.44's strict displayed integer bound needs positive `q` and
`1≤m≤L`; the general non-strict tails include degenerate cases. These are uniform-start
probabilities on vertices and port sequences, not a sampler or runtime certificate.

From the repository root, run `scripts/build.sh CslibFrontierTests.ExpanderVisitCount`
to check the examples.

## Bound adapted Bernoulli counts and hitting times by stochastic domination

Import [`CslibFrontier.Probability.StochasticDomination`](../../CslibFrontier/Probability/StochasticDomination.lean)
(or its constituent submodules) and open `Cslib.Probability` when proving tail bounds or expected
stopping-time bounds for sequences of adapted events whose step-wise conditional success
probabilities satisfy lower or upper bounds.

- **First-order stochastic order**:
  [`StochasticDomination/Basic.lean`](../../CslibFrontier/Probability/StochasticDomination/Basic.lean)
  defines `StochasticallyDominates μ ν` on `Measure α` (`ν U ≤ μ U` for measurable upper sets)
  and `PMF.StochasticallyDominates p q` on `PMF α`. Equate them with measurable monotone
  `ℝ≥0∞`-valued Lebesgue expectations on `SFinite` measures (`stochasticallyDominates_iff_lintegral`),
  with measurable monotone Bochner expectations on probability measures (`IsProbabilityMeasure μ`,
  `IsProbabilityMeasure ν`) for functions integrable under both `μ` and `ν`
  (`stochasticallyDominates_iff_integral`, which fails for unequal-mass measures), with upper tails
  on `ℕ` (`stochasticallyDominates_nat_iff_Ici`) and probability-measure lower tails /
  `ProbabilityTheory.cdf` (`stochasticallyDominates_nat_iff_Iio`,
  `stochasticallyDominates_real_iff_cdf`), `Bool` coin laws (`PMF.stochasticallyDominates_bool_iff`),
  couplings (`StochasticallyDominates.of_coupling`), and closure under `map`, `bind` (on `SFinite`
  measures), and `add_prod`.
- **Poisson-binomial and binomial benchmarks**:
  [`PoissonBinomial.lean`](../../CslibFrontier/Probability/PoissonBinomial.lean) defines
  `PMF.poissonBinomial : List unitInterval → PMF ℕ` with convolution (`poissonBinomial_append`),
  permutation invariance (`poissonBinomial_perm`), independent-coin product equivalence
  (`poissonBinomial_eq_map_pi`), and `ProbabilityTheory.binomial` specialization
  (`toMeasure_poissonBinomial_replicate`).
  [`StochasticDomination/PoissonBinomial.lean`](../../CslibFrontier/Probability/StochasticDomination/PoissonBinomial.lean)
  proves parameter monotonicity (`poissonBinomial_stochasticallyDominates_of_forall₂`,
  `binomial_stochasticallyDominates_of_le`, `binomial_stochasticallyDominates_of_nat_le`) and, for
  strictly positive success probability `0 < (p : ℝ)`, the exact negative-binomial waiting-time
  series `tsum_binomial_real_Iio : ∑' t, (ProbabilityTheory.binomial t p).real (Set.Iio r) = r / p`.
- **Finite-horizon adapted processes**:
  [`StochasticDomination/Adapted.lean`](../../CslibFrontier/Probability/StochasticDomination/Adapted.lean)
  defines `adaptedCount A n` on general `Filtration ℕ m` (under `IsProbabilityMeasure P` and
  `MeasurableSet[ℱ (t + 1)] (A t)`) with both lower- and upper-envelope domination
  (`adaptedCount_stochasticallyDominates_poissonBinomial`,
  `poissonBinomial_stochasticallyDominates_adaptedCount`), active-before-target binomial tails
  requiring the lower bound `p` only while `adaptedCount A t < r`
  (`adaptedCount_real_Iio_le_binomial`), specializations to Markov Ionescu–Tulcea trajectories
  (`traj_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `poissonBinomial_stochasticallyDominates_traj_adaptedCount`,
  `trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial`,
  `poissonBinomial_stochasticallyDominates_trajMeasure_adaptedCount`), and finite-horizon
  sequential `PMF` processes (`PMF.seqProcess`, `PMF.seqCount`,
  `PMF.seqCount_stochasticallyDominates_poissonBinomial`, `PMF.seqCount_active_toReal_Iio_le`).
- **Sequential processes with unreachable histories**:
  [`StochasticDomination/SequentialSupport.lean`](../../CslibFrontier/Probability/StochasticDomination/SequentialSupport.lean)
  provides `PMF.seqCount_stochasticallyDominates_poissonBinomial_of_support` and
  `PMF.seqCount_active_toReal_Iio_le_of_support`. Their probability envelopes are required only
  when `h ∈ (PMF.seqProcess step t).support`; the latter also requires the original count to be
  below the target. Use these when invariants of actual responses fail on impossible histories.
  The response type can have unbounded discrete support. `PMF.seqCount_congr_on_support`
  transfers counts between events agreeing at every reachable prefix. The checked
  [`SequentialSupport.lean` client](../../CslibFrontierTests/SequentialSupport.lean) uses geometric
  metadata and fair success bits: actual histories have authenticated tags, while an impossible
  unauthenticated prefix has zero success probability and violates the older all-prefix premise.
  For an upper envelope, use
  [`StochasticDomination/SequentialUpper.lean`](../../CslibFrontier/Probability/StochasticDomination/SequentialUpper.lean):
  `PMF.poissonBinomial_replicate_stochasticallyDominates_seqCount_of_support` bounds the count
  by `poissonBinomial (List.replicate n p)` when each reached-prefix event probability is at
  most `p`. `PMF.seqCount_toReal_Ici_le_of_support` exposes the binomial upper tail directly.
  The same checked client complements its event: its probability is still one-half on actual
  histories, but becomes one at the impossible prefix. The proof reuses the lower comparison
  and [`PoissonBinomial/Reflection.lean`](../../CslibFrontier/Probability/PoissonBinomial/Reflection.lean),
  which derives count reflection from `BitString.weight_not`; callers need no separate
  comparison induction or assumptions on impossible histories. These are probability lemmas;
  they do not by themselves instantiate a stochastic-oracle deadline lower bound.
- **Infinite-horizon stopping-time means**:
  [`StochasticDomination/Stopping.lean`](../../CslibFrontier/Probability/StochasticDomination/Stopping.lean)
  proves the `WithTop ℕ` tail-sum identity (`lintegral_withTopToENNReal` for measurable `τ`, and
  `integral_untopD_eq_tsum_real_lt` under `IsFiniteMeasure P`, measurable `τ`, and summability of
  `fun n => P.real {n < τ}`, certifying `τ ≠ ⊤` a.e. and integrability of
  `((τ ·).untopD 0 : ℝ)`). Under `IsProbabilityMeasure P` (or `IsMarkovKernel (κ n)` with an initial `[IsProbabilityMeasure μ₀]` for mixtures, or just `IsMarkovKernel (κ n)` for fixed prefixes), adapted events
  `MeasurableSet[ℱ (t + 1)] (A t)`, and strictly positive success probability `0 < (p : ℝ)`,
  `stoppingTime_mean_le_of_adaptedCount_le` assumes `P[A t | ℱ t] ≥ p` a.e. before `τ` (`{t < τ}`)
  and `r ≤ adaptedCount A n ω → τ ω ≤ n` to deduce `τ ≠ ⊤` a.e., integrability of
  `((τ ·).untopD 0 : ℝ)`, and `𝔼[(τ ·).untopD 0] ≤ r / p`; the hitting-time specializations
  (`countHittingTime_mean_le`, `traj_countHittingTime_mean_le`,
  `trajMeasure_countHittingTime_mean_le`) assume the conditional lower bound `p` while
  `adaptedCount A t < r`.

The checked [`StochasticDomination.lean` clients](../../CslibFrontierTests/StochasticDomination.lean)
verify concrete `ℕ`/`ℝ`/`Bool` order inequalities (`lintegral_le`, `integral_le`, `bind`), exact
heterogeneous `poissonBinomial` masses and means, `ProbabilityTheory.binomial` comparison, a
state-dependent sequential `PMF` process, lower/upper `Kernel.trajMeasure` envelopes, a
target-stopped `Kernel.trajMeasure` process whose success probability drops to `0` once `r = 2`
successes are reached while satisfying `𝔼[τ_2] ≤ 4`, and a truncated stopping time strictly
distinct from `countHittingTime`. Run `scripts/build.sh CslibFrontierTests.StochasticDomination` from
the repository root to check them.
Instantiating these theorems on oracle-program executions remains open until the stochastic-oracle
semantics ([#2530](https://github.com/cslib-community/cslib-frontier/pull/2530)) lands on `main`.
