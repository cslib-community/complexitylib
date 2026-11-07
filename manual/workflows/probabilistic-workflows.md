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

The [checked clients](../../ComplexityTests/MarkovChain.lean) compute `d(t) = (2/3)(1/4)^t` and
`t_mix(1/4) = 1` exactly for a two-state chain with non-uniform stationary law, show that the flip
chain never mixes, compute a Metropolis acceptance probability, and give the hypercube instance
with `n = 1`. Run
`scripts/build.sh ComplexityTests.MarkovChain`. A goal of the form `t_mix(ε) = k` needs both
directions: `mixingTime_le_of_distToStationary_le` for `≤`, and
`(hπ : P.IsStationary π).mixingTime_le_iff` at `k - 1` for `≥`.

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
exponent is `n / 2`. The [CHSH client](../../ComplexityTests/TwoProverGame.lean) proves that
CHSH has value `3/4`, and the [parallel repetition clients](../../ComplexityTests/ParallelRepetition.lean)
derive `(3/4)^n ≤ v(CHSHⁿ) ≤ (1 - (1/4)³ / 6000)^{n / 2}`. They also show that the value of the
repetition tends to zero for every game of value below one, and apply Lemma 6.5 with nothing
conditioned, which gives a coordinate won with probability at most `G.value`. Run
`scripts/build.sh ComplexityTests.ParallelRepetition`. The library does not yet use
the theorem for small-soundness Label Cover
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

Use `adaptive_isOraclePPTOn.query_bounds` to obtain polynomial bounds on external call count and request length. A separately proved `IsCostBounded` charges chosen requests along every path; `ProbOracleComp.IsQueryBounded` counts external calls rather than private samples. Neither bound by itself pays for arbitrary Lean callbacks.

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

For literal executed residual calls, import
[HierarchyProductTransport](../../Complexity/Foundations/Probability/HierarchyProductTransport.lean).
`positiveSample_residual_compressed` extracts the compressed direct/reset-right calls
and the evaluated normalized left correction. `finiteInput_residual_root_payment` keeps
the actual per-bin `binBudget` and the separate negative `childBudget`, and consumes each
child's scalar rooted allowance on its own source/usage masks. Successful calls and
estimated-child range/usage bounds remain premises. The conservative field-width, bin,
importance and density costs stay explicit; they are not paid from the precision schedule.
The [execution clients](../../ComplexityTests/HierarchyProductTransport.lean) distinguish
supplied nonzero histories from recursively available compressed calls.

[HierarchyProductMean](../../Complexity/Foundations/Probability/HierarchyProductMean.lean)
identifies that finite canonical reference with the actual residual $C+EC-E$.
`residualCanonicalInput_mean` derives preparation support and rank thresholds from the
polynomial/hierarchy laws; `residualCanonicalInput_stage_mean` transports the result to
the request's true stage channels. The base is nonnegative and row-substochastic, its
entries are bounded by the terminal rank rate, every positive entry in the queried column
is covered by the finite bin family, and the source/horizon/stage bounds remain explicit.
The source may be narrower than the terminal. `finiteInput_residual_mean_payment` composes this identity
with the conditional executed root payment on one environment, subtracting the negative
correction once. The [canonical client](../../ComplexityTests/HierarchyProductMean.lean)
has two actual bins, unequal nonempty reset suffixes and positive genuine $E$ and $EC$.
It executes a supplied canonical history; it does not establish simultaneous recursive
compressed availability or allocate the conservative scalar allowances.

[HierarchyProductAllocation](../../Complexity/Foundations/Probability/HierarchyProductAllocation.lean)
provides a sharper coupled product-mean comparison. Successful normalized evaluation
supplies the left incoming cap; the genuine dense-right gate supplies its row support.
`residualProduct_compressed_mean_root_le` keeps both calls at the actual `binBudget`
and compares their literal product means on the right child's own usage slice, with
constant 33554432 and the right-source factor `terminalRate / sourceRate`.
The common environment is unchanged. Parent-terminal conditioning, bin importance,
midpoint density, signed finite-bin assembly and precision allocation remain separate.
The [allocation clients](../../ComplexityTests/HierarchyProductAllocation.lean) also
fix the structural charge before choosing arbitrarily large admitted fields: nominal
child accuracy cannot supply the old conservative sufficient allowance, whose full-rate
scale is at least $8P^2$. This is an obstruction to that allowance, not an actual-error
lower bound. A supplied-history normalization client checks the structural incoming cap;
it does not construct simultaneous recursive execution.

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
The unused coarse pointwise PREP moment estimate has been removed; the stationary
normalizer contract supplies the allocation route.

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

The [shared statistical-budget evaluator](../../Complexity/Foundations/Probability/HierarchyBudgetEvaluator.lean)
supplies a partial stage-zero path over the existing `HierarchyTask.Request`. It keeps HP.k
fixed and shares whole row/vector history on the original three-role environment. The unaveraged
`finiteInput` helper retains finite positive-bin assembly and one residual subtraction. Public RAW
instead takes both actual last-budget samples of each dyadic slack group, assembles their
signed differences, and completes the whole group once. The common graph and length make this
literally the sum of completed rays (`completedGroup_initial_rays`), including empty retained
slices. The residual is one signed ray outside the positive-bin sum. The horizon is
`Nat.log2 M + 1`, using compression's existing `dyadicSlack` schedule. Each group's walk length
pays its own slack factor; `completedGroup_initial_grid` proves centered fourth moment noise at
most `(2^(-precision) * 64^(-slack))^4` for the assembled initial group, from actual recursive
calls and the original H4 graph. An empty initial ray list keeps zero without calling history
or validating a frame.

For structural execution, import
[HierarchyRawExecution](../../Complexity/Foundations/Probability/HierarchyRawExecution.lean).
Every raw task now samples literal zero at budget zero, without accessing children.
Active stage-zero later pilot inputs, actual inputs and residuals dispatch through the
same dyadic RAW program; iteration-zero inputs retain their established pilot equality.
`completedGroup_available` and `raw_available` consume the two actual endpoint samples
of each nonempty group and distinct source/usage grid channels for completion. Equal-budget
groups need no samples. These are conditional execution laws, not recursive availability.
The [raw execution client](../../ComplexityTests/HierarchyRawExecution.lean) executes
fine budget one against coarse zero: two positive rays contribute six each and the
single negative ray contributes minus one, giving eleven. Its perturbation check keeps
the error against a nonzero coarse reference. Nonconstant constructors with nonpositive
own precision still return `none`; their coarse canonical accuracy remains a separate gap.

The [approximate-history transport](../../Complexity/Foundations/Probability/HierarchyApproximateHistory.lean)
provides an alternative history whose dense inputs execute the actual `compressedBin` at
their own budgets. Production dense leaves retain their semantic implementation. Successful
literal direct/left/reset-right calls use the existing support-restricted signed-residual
error payment. For the initial parent, the actual zero correction annihilates the product,
so its error is exactly the weighted computed direct-child error. A strict lower-budget
availability hypothesis constructs both changing-budget initial samples, including the zero
coarse boundary, before taking their difference. Common completion does not increase the
uncentered fourth moment; a paired perturbation costs at most eight times the sum of its
two endpoint moments on the unchanged source/usage masks. The positive-scale, oversized-floor
regression executes compression and has diagonal error exactly one; it is deliberately outside
the small-floor accuracy allocation. These results do not yet pay the changing-request rooted
child moments or assemble the full parent reserve/compression induction.

The free per-request magnitude input has been removed. Primitive bin cutoffs have a certified
uniform cap; allocation uses explicit finite bin, endpoint-rate and density charges. Those
amplitudes are proved sufficient for all initial paired samples and their assembled group. Their sufficiency for other
constructors and the total noise/bin payment remain open. These conservative finite charges
include vertex width and do not establish the intended uniform growth or native workspace bound.

Dense leaves require positive budget. Every RAW sample has a literal zero-budget approximation;
the initial pilot case also has finite bounds against its assembled sample and canonical bin in
matrix units. The global root-metric coarse-precision payment remains open. Active later pilot/main
RAW and stage-zero residual requests now use their scheduled dispatch. Inactive recursive calls,
invalid frames and unsupported constructors remain unavailable. The exact base matrix and literal
zero-iteration constants retain their existing semantics.

The budget-64 public evaluator regression still computes a nonconstant source-dependent row
from two nonzero half-bins. Separate regressions check its unequal 32/0 paired budgets and the
cancellation of its 63/62 group. These initial exact-slice examples do not demonstrate a
positive-iteration canonical induction or nonzero mixing error. Successful normalized rows have
budget-independent range/usage/support laws, and successor maxima retain their local error
payment. Pointwise input sparsity is **not** asserted to survive a walk.

The [compressed-bin consumer](../../Complexity/Foundations/Probability/HierarchyCompressedBin.lean)
now computes first prefixes from those actual history groups on full terminal rank, completes
its corresponding bin preparation on source × usage, and runs the real two-signal iterate with
`compatibleCapacity`. Its decoder accepts the actual bin numerator and gate. The shared
`normalizedRequest_eq_output` identity also accepts these functions, and
`evaluate_dense_eq_output` identifies the public dense evaluator with that decoder and its
actual preparation. Existing fixed-HP clients use this same scalar decoder.

This distinction matters: the earlier `actualNormalizedCompatible` and reserve-output theorems
still target `genuineNormalizedRecipe`, with the HP atom cutoff and polynomial preparation.
They are not canonical-error theorems for an arbitrary routed bin, unnormalized RAW, or an
incoming/max-decorated correction. The new consumer does not replace RAW or the correction
request. Its generic range, usage and postcompression row-support theorem assumes the actual
bin's separated entry threshold; it never transports sparsity through a conditional walk.

A checked budget-64 consumer uses both genuine half-bins and their original evaluator history.
Its first nonzero prefix follows the coarse zero group. Its computed bin preparation supplies
the second slot on the same environment, with positive scale and floor `HP.η / 4`, and all
seven actual capacity/floor updates are executed. The resulting nonconstant source-dependent
row has zero fourth-root row error against the actual dense normalized-bin target and proved
postcompression support. This is an initial exact-slice case with constant bin preparation;
it does not prove a general inductive parent error bound or a nonzero mixing-error example.
Out-of-range array defaults are used only beyond the executed horizon, not as unavailable
recursive calls or zero approximations.

The [routed-bin preparation laws](../../Complexity/Foundations/Probability/RoutedBinPreparation.lean)
now provide a concrete alternative to unconstrained preparation: the existing polynomial
cutoff vanishes on light inputs, is one wherever the bounded routed numerator is nonzero,
and has a globally Lipschitz fourth root. Its constants precede bin scales and routing.
The [checked instance](../../ComplexityTests/RoutedBinPreparation.lean) uses a nonzero routed
top bin and checks the zero side; constant-one preparation fails that light-input contract.
The [actual unrouted numerator](../../Complexity/Foundations/Probability/UnroutedBinRegularity.lean)
now has a globally Lipschitz fourth root for the polynomial switch on `[1/2,1]`
and positive scales with constant adjacent ratio at least two. The constant depends
only on that ratio and the top cap, before bin indices or child values. The fine-bin
proof factors the literal switch difference; the top bin retains its actual clipping.
`DenseBinRecipe.polynomialUnrouted` combines this numerator with the existing polynomial
preparation and HP row gate. The [checked recipe](../../ComplexityTests/UnroutedBinRegularity.lean)
uses the geometric ratio-16 grid: top values at and above cap two equal two, fine
values at 8, 12 and 16 equal 8, 6 and 0, and light/negative values vanish. Its nonempty
hierarchy witness checks both root bounds, numerator range/support and preparation
coverage, including `h 0 = 0` and `h 1 = 1`. The old compressed fixture remains
construction-only.

The [shared decoder kernel](../../Complexity/Foundations/Analysis/RowCompression/Decoder.lean)
now extracts the common-loss comparison used by the fixed-HP client and combines the existing
saturated iterate comparison with stationary-reference preservation. Its explicit coefficients
let the [unrouted decoder](../../Complexity/Foundations/Probability/UnroutedBinDecoder.lean)
choose one accuracy constant before scales, bin index, rows and schedules. Top clipping and fine
upper vanishing give saturation at `max cap 16`; numerator monotonicity is not required.
The actual decoder also has fewer than `HP.K` nonzero terminal entries after compression,
for arbitrary defaults and second signals, without assuming sparse walk inputs.
`BudgetData.exists_compressedBin_root_bound` consumes this kernel for the actual `compressedBin`
against the genuine dense normalized recipe on a deterministic canonical matrix, with polynomial
preparation, full terminal rank and the original source/usage conditional mean.

The older all-prefix comparison still charges prefix zero. The
[sharp shared kernel](../../Complexity/Foundations/Analysis/RowCompression/DecoderSharp.lean)
now avoids that charge: `BudgetData.exists_compressedBin_sharp_noOverflow` compares the actual
zero-start `compressedBin` with the same dense polynomial-preparation target, conditional on
no overflow and post-increment clipped errors. Its bound is a weighted sum of those errors plus
the final raw error. The final coefficient is chosen before the compression floor, scales, bin,
prime and rows. The stationary coefficient is explicitly `36 L + 72 L / δ`; reducing δ alone
does not pay the earlier errors. The actual scheduled envelopes must pay the weighted sum.
The shared first-overflow tail also chooses its coefficient before δ and starts errors at the
already-added overflow input. Fixed-HP stationary, no-overflow and tail clients specialize these
shared proofs. The actual-bin tail now compares against truth by combining its preloaded
comparison with preserved stationary continuation and the weighted pre-overflow loss.
The [shared integrated proof](../../Complexity/Foundations/Probability/CompressionIntegrated.lean)
serves both fixed-HP atoms and the ratio-16 numerator. It uses actual postcompression support,
keeps heavy first-overflow tails explicit, and pays false overflow with the raw-prefix fourth
moment at `j + 1`. It assumes no independence between masks, errors and events.
`BudgetData.exists_compressedBin_integrated` consumes successful actual prefix and preparation
executions and bounds the executed compressed output against `denseChild` with polynomial
preparation on canonical G. Its second signal keeps the genuine joint source/usage mean;
polynomial preparation supplies range and light-entry annihilation. The first signal and its
rank mask remain full-terminal; the second signal and final output remain usage-masked.

The zero-start regression uses the actual ratio-16 top/fine numerator and polynomial preparation,
with nonzero truth and a provably inaccurate prefix zero, then checks zero discrepancy after an
exact increment. The integrated regression uses the same Bool environment for masks and increments and checks
zero fourth moment without a prefix-zero accuracy premise. First overflow at group zero is
also checked against truth. These are decoder regressions, not evaluator-history accuracy
fixtures. The separate positive evaluator-history regression now uses actual ratio-16 bins
and polynomial preparation on a full-rate identity input: its top bin carries the input, its
fine bin is zero, both scheduled groups execute without overflow, and the compressed output
has zero rooted error against the actual dense polynomial target. This stationary example
has no nonconstant mixing error. The older constant-one half-bin example remains a
construction fixture, not valid polynomial geometry.

[`HierarchyInitialHistory.lean`](../../Complexity/Foundations/Probability/HierarchyInitialHistory.lean)
expands actual first prefixes as sums of completed groups with their own walk lengths.
`BudgetData.initialPrefix_mean` sums their literal conditional means, while
`BudgetData.initialGroupInput_sum` telescopes the fine/coarse budgets bin by bin and retains
both inactive-fine and initial-coarse boundary terms. The centered prefix noise is a sum of
correlated group noises, paid by finite Minkowski and geometric dyadic decay without a group
count. `BudgetData.initial_actualNoiseEntry` supplies that payment in the existing predecoder
statistics API. First-signal weighted stationary noise and overflow-noise tails are paid
unconditionally. Multiplying the stationary coefficient by the scheduled floor leaves the
explicit `36 L floor + 72 L` factor; shrinking the floor alone does not pay the bias.

[`HierarchyInitialMean.lean`](../../Complexity/Foundations/Probability/HierarchyInitialMean.lean)
now derives each actual initial sample's canonical matrix-unit mean on the original
source/terminal event, including unequal bin rates. For a nonnegative substochastic base,
actual polynomial ratio-16 bins through index `n` sum to the entry times the switch at
`entry / rate n`. `BudgetData.initialPrefix_polynomial_mean` combines this coverage with
`initialGroupInput_sum`: the prefix mean deficit is exactly omitted fine coverage plus
inactive fine-bin mass plus the initial coarse boundary. These are separate charges;
scalar coverage alone does not make a sample's fine budget active.

`BudgetData.initialFirstSignal_clippedMean` identifies the actual first predecoder statistic
with the clipping at one of that deficit divided by `rankRate + baseEntry`.
`BudgetData.initial_requestSignals_envelope` supplies a post-increment raw-prefix envelope
for the actual bin-preparation target: deterministic first deficit, centered first noise,
and the remaining second discrepancy. It preserves the initial canonical base target,
not a residual-specific mean. Apply the first-noise payments separately. The preparation transport below refines the
remaining discrepancy; the scheduled second-noise payment is given below, while combined
integrated output payments remain open.
The [actual-history regression](../../ComplexityTests/PolynomialBudgetHistory.lean) checks
early inactive loss and its final disappearance, a nonzero fine-bin mean at rate `1/16`,
and a positive omitted entry of size `1/256`. The unequal-rate examples check successful
histories and their conditional means; they do not claim final compressed accuracy.

[`HierarchyInitialMeanPayment.lean`](../../Complexity/Foundations/Probability/HierarchyInitialMeanPayment.lean)
pays the finite first-mean charges without assuming output accuracy. The chosen horizon makes
the initial coarse boundary zero, including at budget zero. Omitted coverage costs at most
`rate n`; inactive mass is bounded by the primitive bin cap times the sum of actual inactive
bin rates, with inactivity determined by `lastBudget` and `sampleScale`. Division retains
`rankRate + baseEntry` before the uniform bound divides by rank rate.

If every retained scale cutoff is strictly below `M > 1`, only group zero can remain inactive.
The actual first clipped mean's final bound is `rate n / rankRate`. Its stationary preloss is
bounded by `36 L δ + 72 L` times the sum of `rate n / (1023 * rankRate)` and the initial cap/rate
charge times `(1/1024)^(2^log2 M)`. The first floor pays this initial loss; reducing δ alone
does not remove the surviving coefficient. The real predecoder consumer permits a different
maximizing retained endpoint at every prefix. The deterministic heavy-tail consumer uses the
actual base's heavy event and retains the integrated row norm of a uniform finite charge.
That coarse norm is explicit and need not shrink; it is not a proved reserve allocation.
No noise is discounted using heavy-event rarity.

The actual-history regressions consume the final payment for nonzero fine and omitted-positive
entries at budget eight, check the full four-group stationary charge, and retain a positive
uniform charge at budget two, where the fine scale cutoff does not fit. These are first-mean
payments, not final compressed-output accuracy or a nonconstant mixing example.

[`HierarchyInitialPreparation.lean`](../../Complexity/Foundations/Probability/HierarchyInitialPreparation.lean)
transports the actual postincrement `F(j+1)` error through polynomial preparation and the
full-terminal HP rank gate. It reuses absolute preparation sensitivity and conditional Jensen
on the original source × usage environment. The first-history error is split in matrix units
into the exact omitted/inactive/coarse deficit and the centered scheduled first noise.
The second deterministic envelope has fourth moment at most
`P * (|ζ| * (Lh + Lρ) / rankRate)^4 * 8 * (firstNoiseMoment + deficitMoment)`.
The deficit moment is the literal full-rank row norm; global allocation must still pay it.
There is no independent reseed or conversion of a clipped relative error into absolute error.

The successful preparation-walk list is identified with the literal `compressedBin`
executions. `BudgetData.initial_requestSignals_two_envelopes` bounds their raw-prefix
clipped error using the paid first deterministic charge, the second deterministic envelope,
and the two centered noises separately. Full terminal rank, usage masks, source/rank/usage
rates, suffixes and prefix `j+1` are preserved. Apply the second-noise payment below
to its separate usage statistic.
The actual-history regression has strictly positive early preparation bias `η/4`, zero final
and off-diagonal bias, consumes the sensitivity envelope and its integrated payment, and
retains the actual successful prefix/preparation executions. This is a stationary fixture,
not a nonconstant mixing example or a general compressed-output accuracy theorem.

For the literal scheduled second walks, import
[`HierarchyInitialSecondNoise.lean`](../../Complexity/Foundations/Probability/HierarchyInitialSecondNoise.lean).
Start with a `BudgetData`, a bin whose auxiliary cutoff lies in [0,1], the original grid
source/usage request and a successful preparation-list execution. No first-history accuracy
premise is needed for centered noise. `BudgetData.one_le_magnitude` proves the existing derived
allocation covers one; `BudgetData.binPreparation_mem_Icc` bounds each literal input.
`BudgetData.preparationWalks_noise` applies `completion_noise` with that allocation and its
original length, request precision and dyadic slack. `BudgetData.preparationWalks_mean` is
the shared stationarity rule for the executed list entry.

`BudgetData.initialSecondSignal_noise_moment` pays the usage row statistic at raw prefix
`j+1` by `(|ζ| * 2^(-requestPrecision M r) * 64^(-dyadicSlack(m,j)))^4`.
Its first history, full-terminal rank and the original environment are retained; zeta may
have either sign or be zero. For a nonnegative base target, `BudgetData.initialSecondSignal_noise`
gives the corresponding row-maximum bound. With `e = |ζ| * 2^(-requestPrecision M r)`,
`BudgetData.initialSecondSignal_preloss` pays stationary noise by
`((36 L floor + 72 L) * e / 511)^4`, and
`BudgetData.initialSecondSignal_overflowNoise` pays an actual overflow-selected noise tail
by `(e * 7/9)^4` unconditionally. Its selector may depend on every walk.
`BudgetData.initialSecondSignal_falseNoise` pays the scheduled raw-prefix false charges by
`64 K radius^4 / floor^4 * e^4 / 63`.
`BudgetData.initialSignals_falseNoise` adds the already-paid first-noise charge on full rank
to this second-noise charge on usage, preserving their distinct precisions and rates.
These bounds do not include deterministic mean envelopes or allocate global reserves.

For a successful `compressedBin`, apply `BudgetData.compressedBin_secondNoise` to its output
equality to obtain the actual first history, preparation list and all second-noise row budgets.
This avoids supplying replacement walk or oracle families. The actual-history regression above
checks this consumer on its positive stationary output and exact zero second prefixes at ζ=0 despite
positive final preparation. A separate nonconstant supplied history
checks two different preparation values and the actual allocated usage-walk bound with ζ=-3;
it does not establish positive residual noise or a nonconstant evaluator induction case.

For the finite four-max assembly, import
[`HierarchyInitialIntegrated.lean`](../../Complexity/Foundations/Probability/HierarchyInitialIntegrated.lean).
`NormalizedMoments.actualMeanMax` takes the first deterministic discrepancy on full terminal
rank and the second on usage. `NormalizedMoments.actualFourMax` adds these to the two actual
centered noise maxima. `BudgetData.exists_compressedBin_fourMax` supplies those literal
maxima to the integrated decoder using successful first-history, preparation-list and
compressed-output executions. Callers no longer supply clipped-error envelopes or a final
accuracy hypothesis. The preparation support and genuine-target identities are shared with
the earlier deterministic-envelope consumer.

Write `a(j,ν)` for the fourth root of the actual deterministic mean-maximum moment,
`e₀ = 2^(-requestPrecision M {r with usage := r.terminal}) * (64/63) / rate ka`,
and `e₁ = |ζ| * 2^(-requestPrecision M r)`.
`BudgetData.initialFourMax_moment` pays the four-max moment by
`(a(j,0) + a(j,1) + (e₀+e₁)*64^(-dyadicSlack(m,j)))^4`.
`BudgetData.initialFourMax_preloss` pays its weighted stationary moment by
`(sum_j floor_j*(a(j,0)+a(j,1)) + floor*(e₀+e₁)/511)^4`, using finite Minkowski
without counting prefixes. The decoder's stationary coefficient still multiplies this
payment; its inverse-floor term is not removed.

`BudgetData.initialFourMax_tail` leaves the fourth root of the **deterministic** selected
heavy mean-tail moment, plus `(e₀+e₁)*7/9`, inside the fourth power. Both noises are paid
unconditionally; only the deterministic tail norm can receive a later rarity discount.
`BudgetData.initialSignals_falseBudget` consumes the existing two-noise charge payment:
with `w_j = 64 K radius^4/(capacity_j*floor_j^4)` and
`c = 64 K radius^4/floor^4`, its RHS is
`64*(sum_j w_j*(meanMoment(j,0)+meanMoment(j,1)) + c*e₀^4/63 + c*e₁^4/63)`.
This uses raw postincrement moments on the respective masks and requires usage to be
contained in terminal rank. The shared `NormalizedMoments.raw_prefix_four_budget` permits
four distinct budgets; the prior uniform raw-prefix client now specializes it.

The actual-history regression consumes the successful positive stationary compressed output
with the four-max decoder bound under its small-scale condition, and checks the zero-zeta
moment payment on the genuine early history. The latter keeps the positive early first-mean
deficit. These clients do not demonstrate nonconstant evaluator mixing or global induction.
For one finite paid output inequality, import
[`HierarchyInitialPaid.lean`](../../Complexity/Foundations/Probability/HierarchyInitialPaid.lean)
and use `BudgetData.exists_compressedBin_paid`. It consumes successful actual first-history,
preparation-list and `compressedBin` executions on the canonical polynomial geometry.
The constant $C$ is chosen before the positive floor, and $C_{pre}$ after it.
There is no supplied final-error or free budget premise.

For each postincrement prefix $j+1$, write $q_j$ for `initialMeanCharge`, and $D_j$ for
the fourth-power row norm of `initialPolynomialLoss` on the **full terminal rank**.
The preparation payment is
$J_j=P(|\zeta|(L_h+L_\rho)/\operatorname{rate}(k_a))^4
\cdot 8((e_0\operatorname{rate}(k_a)64^{-\operatorname{dyadicSlack}(m,j)})^4+D_j)$.
`BudgetData.initialFirstMean_moments` bounds the first maximum by the vertex moment of
the constant $q_j$ and its raw row moment by the corresponding constant row moment.
The shared `Cslib.RowCompression.vertex_row_max` transports the second maximum to its
usage-row moment, which the existing preparation Jensen theorem bounds by $J_j$.
Thus $a_j$ is now the sum of the fourth roots of the constant-charge vertex moment and
$J_j$, rather than an unpaid actual mean-maximum norm.

The single output RHS substitutes these $a_j$ in the stationary sum and final-prefix
payment, substitutes both geometric noise payments, and replaces the raw false-charge
moments by $64\sum_j w_j(\lVert q_j\rVert_{row}^4+J_j)$ plus the two noise charges.
The outer factor $64$ from the four-term fourth-power split remains distinct from
$w_j$'s decoder coefficient. The selected deterministic heavy-tail norm stays explicit;
both of its noise terms are paid unconditionally. The budget-2 regression consumes this
inequality on the actual positive stationary output, retaining the genuine early deficit.
It is not a nonconstant evaluator-mixing or general induction example.

The next finite allocation is in
[`HierarchyInitialAllocation.lean`](../../Complexity/Foundations/Probability/HierarchyInitialAllocation.lean).
`BudgetData.exists_compressedBin_allocated` consumes `exists_compressedBin_paid` and pays
the full-rank deficit by the fourth row moment of the constant
$d_j=\operatorname{rate}(n)+\operatorname{initialInactiveCharge}(M,j,r)$.
This follows pointwise from omitted polynomial coverage plus the literal inactive bins;
the coarse boundary is zero. No lower bound on positive base entries is needed.
In the preceding formula for $J_j$, replace $D_j$ by this constant-charge moment.

Both deterministic means now receive actual heavy-event rarity. Write
$\epsilon_{0,i}=\lVert q_i\rVert_{row}$ and $\epsilon_{1,i}=J_i^{1/4}$.
The selected mean-tail root is replaced by the explicit finite payment

$$
T=\sum_{j<m}\left(\frac{2+256/\delta_j}{\operatorname{capacity}_j}\right)^{1/4}
\sum_{j\le i<m}28^{m-i}(\epsilon_{0,i}+\epsilon_{1,i}).
$$

Here $m=\lfloor\log_2 M\rfloor+1$, $\delta_j=\operatorname{dyadicFloor}(\delta,m,j)$
and the capacity is the actual `compatibleCapacity HP.K m j`.
The shared `NormalizedMoments.integrated_mean_tail_schedule` applies actual rarity to
each deterministic prefix before finite Minkowski. There is no environment-cardinality
factor. Noise stays outside rarity: the output tail still contains $(e_0+e_1)7/9$,
and the stationary, final and raw false-charge noise constants are unchanged.

For sufficient budget $M>1$ with every retained literal scale cutoff strictly below $M$,
`initialMeanCharge_le_schedule` gives
$q_i\le\operatorname{rate}(n)/\operatorname{rate}(k_a)+\mathbf1_{i=0}A/\operatorname{rate}(k_a)$,
where $A=\operatorname{binCap}\sum_{b\in\operatorname{bins}}\operatorname{binRate}(b)$.
`initialMeanCharge_tail_schedule` isolates the possible early inactive payment with its
exact coefficient $v_0 28^m$ in the double sum. It is not charged at every later prefix.
The actual-history tests retain positive early deficit, exact final deficit zero,
the budget-2 insufficient-cutoff edge, and the sufficient-budget-8 schedule.
They also consume the new successful-output inequality on the genuine budget-2 history.

The allocation depends on retained depth $n$, source and rank rates, width $P$, actual
scale cutoffs, and the positive floor. Depth and source exponent must fit the field horizon;
actual rarity additionally requires $k_a\le H.\operatorname{maxExponent}$, with $k_a\le k_u$.
The decoder constant precedes the floor; the stationary constant follows it. Shrinking
the floor alone does not remove the stationary bias and also affects the rarity and
false-charge denominators.

The geometric continuation is in
[`HierarchyInitialGeometric.lean`](../../Complexity/Foundations/Probability/HierarchyInitialGeometric.lean).
`initialGeometricRHS` names the complete computed payment, including stationary, final,
tail and raw terms. `exists_compressedBin_geometric` returns precisely this payment and removes the
finite double tail sum and raw mean false-charge sum. It assumes the concrete sufficient
cutoff inequality $c(1+4(n+k_a))<M$, where $c$ is the actual `slack`.
For $U(t)=\lVert t\rVert_{row}^4$ with the original full-rank masks, set

$$
S=8P\left(\frac{|\zeta|(L_h+L_\rho)}{\operatorname{rate}(k_a)}\right)^4,\qquad
J_-=S\left((e_0\operatorname{rate}(k_a)/64)^4+U(\operatorname{rate}(n))\right),
$$

and obtain $J_+$ by replacing $\operatorname{rate}(n)$ with
$\operatorname{rate}(n)+A$. Write
$D_-=U(\operatorname{rate}(n)/\operatorname{rate}(k_a))$ and
$D_+=U((\operatorname{rate}(n)+A)/\operatorname{rate}(k_a))$.
The deterministic tail is at most

$$
\frac{(2+256/\delta)^{1/4}}{63}(D_-^{1/4}+J_-^{1/4})
+v_0 28^m(D_+^{1/4}+J_+^{1/4}),
$$

where $v_0$ is the literal first rarity root. The raw mean charge is at most
$c_{\rm false}(D_-+J_-)/63+w_0(D_++J_+)$, with the actual false-charge
coefficient and first weight from the preceding theorem. Both means and the preparation
are paid; these envelopes are computed from actual rates and row moments, not supplied
final budgets. Stationary/final payments and all unconditional centered-noise payments
are unchanged. The budget-8 regression proves successful prefixes, preparation walks
and compression, then consumes this full inequality on that execution.

The reusable
[`ScheduleAllocation.lean`](../../Complexity/Foundations/Probability/NormalizedAtomRows/ScheduleAllocation.lean)
proves the numerical majorants. Capacity exponent 64, inverse-floor exponent 10 and
factor-$128^d$ tail growth leave at least $64^{-d}$ decay after taking fourth roots.
In particular, `compatible_first_rarity_decay` proves
$v_0 28^m\le(2+256/\delta)^{1/4}64^{-2^{\lfloor\log_2 M\rfloor}}$.
The exceptional false weight also stays literal; its definition is
$w_0=c_{\rm false}(K+1)^{-1}2^{-24\cdot2^{\lfloor\log_2 M\rfloor}}$.
`compatible_false_weight_decay` checks the coarser bound
$w_j\le c_{\rm false}1048576^{-d_j}$, including the inverse fourth power of the floor.
For $d_0\ge n$, `compatible_first_false_width` consequently pays both width factors:
$w_0P^2\le4c_{\rm false}262144^{-n}$. The early moment must still be bounded before
using this scalar inequality. These rarity bounds apply to deterministic means, never to
correlated centered noise.

[`HierarchyInitialFeasibility.lean`](../../Complexity/Foundations/Probability/HierarchyInitialFeasibility.lean)
checks the actual guard constants:

$$
p=M/(16c)-2(k_a+k_s)-\operatorname{rankCharge}\operatorname{rank},\qquad
h_b=4(k_a-b).
$$

For $n=\lfloor M/(128c)\rfloor\ge1$, $k_s,k_a\le n$ and structural rank cost at
most $n$, `slow_depth_guards` proves all retained cutoffs below $M$ and
$p\ge M/(64c)\ge2n$. Usage does not change `requestPrecision`; usage-row masks and
costs nevertheless remain in the analytic statements. If identifiers are already below
$2^n$, Bertrand supplies a prime $2^n<P\le2^{n+1}$ with the stated depth/identifier
horizon. No arbitrary future stage or copy growth is provided. The checked scalar bounds
are $P^2\operatorname{rate}(n)^4\le4\cdot16384^{-n}$,
$P(2^{-p})^4\le2\cdot128^{-n}$ and, crucially,
$P^2(2^{-p})^4\le4\cdot64^{-n}$ for $p\ge2n$. The last inequality pays the second
width factor that a preparation moment can carry; the one-width inequality alone does
not do so. `fixed_request_depth_guards` fixes $k_s,k_a,k_u$ and structural rank before
choosing $n$, and proves eventual guards at $M=128cn$, whose literal depth floor is $n$.
The source marginal estimate in `grid_vertex_moment_le` is independent of field width;
`grid_row_moment_le` reuses it and pays the remaining row width. The complete assembly is in
[`HierarchyInitialUniform.lean`](../../Complexity/Foundations/Probability/HierarchyInitialUniform.lean).
`initialGeometricRHS_uniform` chooses a single $D\ge0$ before depth, prime, base matrix,
request and suffixes and proves

$$
\operatorname{initialGeometricRHS}\le D\,64^{-n}.
$$

The fixed parameters are the source/terminal exponents, HP, both sensitivities, zeta,
positive floor, decoder constants and a uniform primitive bin-cap bound. The estimate is
uniform over every prime $P\le2^{n+1}$ satisfying the source horizon and every input
satisfying the actual scale and precision guards. It therefore includes every admissible
nonnegative substochastic base. No varying-field transport is needed.

The finite bin-rate sum is at most $16/15$. Positive groups have zero inactive charge;
their row and two-width preparation moments are $O(64^{-n})$. The exceptional first
moments are at most a fixed constant times $P^2$. Their scheduled stationary floor,
rarity and raw false weights absorb that growth because $d_0\ge n$ at $M=128cn$.
Every stationary, final, deterministic-tail, raw false-charge and unconditional-noise
term of the literal RHS is included. No final accuracy budget is assumed, and neither
noise receives rarity.

`initialGeometricRHS_uniform_small` proves uniform arbitrary accuracy by geometric
convergence. `fixed_charge_linear_guards` fixes slack and a structural-charge bound before
choosing depth and pays both actual precisions and the scale budget.
`exists_compressedBin_uniform_accuracy` preserves the order $C$, then positive floor,
then $C_{\rm pre}$, then fixed request constants, requested accuracy and depth. It
constructs both actual histories and a successful compressed output with error at most
the requested positive accuracy, and identifies its dense target with the actual
positive-budget `.baseNormalized` result of `BudgetData.evaluate`. The regression chooses
bounded primes after depth,
uses a nonzero identity base, nonempty suffixes and fixed nonzero usage exponent, and
consumes this existence theorem. This is an initial ratio-16 polynomial-bin result;
it supplies no general recursive evaluator induction.

The [actual initial-constructor bridge](../../Complexity/Foundations/Probability/HierarchyEvaluatorInitial.lean)
also identifies the initial pilot and actual `.input 0` outputs with their own final
history prefixes. The actual input now executes the shared zero-correction RAW recipe;
its own task rank still sets its precision and walk lengths. Full terminal usage is
required by this bridge. The existing deficit and unconditional noise payment consequently
bounds its canonical matrix-unit error, with omitted/inactive/coarse charges retained.
`evaluate_score_child` executes a score from an actual strictly lower-budget pilot input
and pays its full-rank error with explicit width and inverse-rate costs. The nonzero
identity fixture executes `.input 0` and this score successor and keeps the zero-budget
input unavailable.

`evaluate_lower_dense_contract` quantifies over every positive $m<M$ and every changing
dense request/bin. It proves availability, the constructor-correct target, range, usage
vanishing, terminal-row support, and zero rooted errors on both its own source/usage
and source/full-rank masks. This is the **exact dense seed** contract: the evaluator still
reads the genuine semantic dense leaves. It is not the simultaneous recursive row/vector
invariant. In particular the uniform compressed comparison does not replace those leaves
inside `evaluate`; doing so invalidates the exact initial-history calculations and needs
the changing-request IH. No scalar fixed-request convergence theorem supplies that IH.

The [initial perturbation payment](../../Complexity/Foundations/Probability/HierarchyApproximateHistory.lean)
now derives an ordinary endpoint moment from the actual compressed direct child's rooted
moment on its own source and usage. Successful compression supplies its bounded normalized
range and usage vanishing. The explicit multiplier is
$\sum_y |b\,\pi_a(y)/\pi_{\min(a,b)}(y)|^4$ times
$(4(2\,\mathrm{binCap})^{3/4})^4$. The literal zero left correction eliminates
the product-error charge; the reset-right call must still succeed. No reciprocal
probability of an environment atom or desired parent-error premise enters this comparison.
The paired theorem consumes a strict positive lower-budget IH at each actual scheduled
endpoint. Budget zero is literal zero in both histories and requires no compressed call.
An explicit choice from HP satisfies the scalar cap, margin, preparation and small-floor
premises, yet the budget-one computation has diagonal error one against its genuine dense
target. Low-budget approximation is not assumed exact.

[Executed group and prefix transport](../../Complexity/Foundations/Probability/HierarchyInitialPerturbation.lean)
sums all paired rays before their common completion and every executed group before
compression. Completion contracts the uncentered fourth moment on the same masks. Finite
sums retain the cube of the bin count or prefix length and the sum of actual moment costs.
The returned lists are identified with the literal computed-history executions, including
the changing budgets, rather than independent prefix families. Conditional Jensen and
the existing finite-envelope API also pay one common deterministic mean-error envelope
over all executed prefixes, including prefix zero, by the sum of those prefix payments.
The local two-payment estimates start with
[`positiveSample_initial_compressed_clipped_mean`](../../Complexity/Foundations/Probability/HierarchyInitialPerturbation.lean).
It identifies the literal positive sample and clips its mean discrepancy on the original
joint source/terminal slice. Polynomial support and `initialSample_mean` prove canonical
mean domination by $2\,\mathrm{binCap}\,G(x,y)$ before any signed subtraction. The
approximate child needs nonnegativity, not canonical support; it may be nonzero at a zero
target. Reset-right availability remains a premise even though zero left correction removes
its error. With physical scale $c=b_i\,\mathrm{usageRatio}/\mathrm{rate}(k_a)$, the
conditional fourth-moment charge is $512(6\,\mathrm{binCap}+3)^3c$ times the child's
conditional rooted fourth moment. The scale occurs to the first power. Empty slices use
zero means; no independence is needed. The
[clipped-mean API](../../Complexity/Foundations/Probability/RootMetric/ClippedMean.lean)
also proves scalar fidelity with constant $32K$ and a triangle inequality for finite signed
sums. Apply positive domination to each summand before subtracting fine and coarse means.

[`requestPrecision_initial_scheduled_raw_pay`](../../Complexity/Foundations/Probability/HierarchyInitialFeasibility.lean)
checks a separate ordinary-progress payment at the actual `lastBudget`, including exhausted
budgets. Source inheritance and structural rank decrease follow from the literal direct
request. The structural charge precedes all request exponents. This is a norm-level bound:
its entire coefficient must be raised to the fourth power in a moment payment. Its explicit
window factor has **not** been absorbed by the evaluator's walk allocation.

The own-mask integration is now
[`positiveSample_initial_compressed_clipped_root`](../../Complexity/Foundations/Probability/HierarchyInitialPerturbation.lean).
Fubini cancels the actual joint slice densities. Successful compression and canonical
normalization give equality off the direct child's usage, so its own scalar rooted IH pays
the integrated mean without an environment-atom penalty or approximate canonical support.
For terminal exponent $a$ and bin exponent $i$,
[`initialClippedRootCoefficient`](../../Complexity/Foundations/Probability/HierarchyInitialPerturbation.lean)
uses the coarse coefficient $512(6\,\mathrm{binCap}+3)^3\,\mathrm{rate}(i)/\mathrm{rate}(a)$
when $i\le a$. For $i>a$ it uses
$$
2048\,\mathrm{binCap}^3
\left(\frac{\mathrm{rate}(i)}{\mathrm{rate}(a)}\right)^4
\frac{\mathrm{gridMass}(a)}{\mathrm{gridMass}(i)}.
$$
The fine proof converts bounded normalized child root error to ordinary error on its own
usage slice, then changes terminal normalization before Jensen. Three powers of the
relative usage density remain. Actual masks and child values may be correlated; only the
separate source and terminal role marginals factor. On the admitted horizon, rounded mass
comparison bounds the fine coefficient by
$32768\,\mathrm{binCap}^3(\mathrm{rate}(i)/\mathrm{rate}(a))^3$.
Thus the rate-16 grid gives norm decay $2^{-3(i-a)}$, not a copied rate/mass identity.

[`requestPrecision_initial_clipped_transfer`](../../Complexity/Foundations/Probability/HierarchyInitialFeasibility.lean)
combines this piecewise norm scale with the literal direct child's own precision. The
inherited source cancels and structural rank decreases, leaving $2^{-|i-a|}$ before budget
loss. `requestPrecision_initial_clipped_scheduled` retains the actual
$\max(d,\mathrm{scaleCutoff})/(16\,\mathrm{slack})$ loss.
`requestPrecision_initial_clipped_adjust` uses the literal scale cutoff
$\mathrm{slack}(1+4|i-a|)$, giving the norm payment
$$
2^{-\mathrm{requestPrecision}(M,r)}\,2^{-\mathrm{rankCharge}}\,
2^{d/(16\,\mathrm{slack})+1/16-3|i-a|/4}.
$$
The structural charge is fixed before all source, terminal and bin exponents.
`initialClippedRootEndpoint_le` raises the whole payment to the fourth power and combines
it with the rounded coefficient at the actual scheduled endpoint, with zero endpoints
charged zero. Apply it separately at $d$ and $2d$. This finite allocation retains the prefix
slack cost; it does not pay ordinary progress or preparation.

`pairedSample_initial_compressed_clipped_precision` uses the actual fine/coarse
`lastBudget` calls, strict lower budgets and each direct request's own precision. Equal
budgets and zero endpoints have exact zero charges; reset-right must still succeed at
positive endpoints. `completedGroup_initial_compressed_clipped_mean` preserves means
through each actual stationary completion. `initial_compressed_prefix_clipped_mean`
then sums correlated signed group means. Both now use finite Minkowski on the unchanged
joint slice: group moments are bounded by $(\sum_i \epsilon_i^{1/4})^4$, and prefix moments
by $(\sum_j \epsilon_j^{1/4})^4$. There is no bin-count or prefix-count cube in this clipped
route. Positive domination precedes signed pairing; clipping stays after the common mean.
The ordinary centered-noise route retains its own previous costs.

[`initialClippedRootWindow`](../../Complexity/Foundations/Probability/HierarchyInitialPerturbation.lean)
is a numerical sum of the two endpoint factors above, at $d$ and $2d$. It omits zero
endpoints and equal-budget pairs. Write this sum as $W(M,d,a,r)$ and set
$C=\max(512(6\,\mathrm{binCap}+3)^3,32768\,\mathrm{binCap}^3)$.
`initialClippedRootGroupCharge_le` and `initialClippedRootPrefix_le` bound the actual
finite prefix transport by
$$
\left(2C^{1/4}|c|\,2^{-\mathrm{requestPrecision}(M,r)}\,
2^{-\mathrm{rankCharge}}\sum_{j<p} W(M,\mathrm{dyadicSlack}(m,j),a,r)\right)^4,
\qquad m=\lfloor\log_2 M\rfloor+1.
$$
Consequently `initialClippedRootPrefix_paid` pays this transport at parent precision
provided the explicit joint allocation condition
$$
2C^{1/4}\sum_{j<p}W(M,\mathrm{dyadicSlack}(m,j),a,r)
\le 2^{\mathrm{rankCharge}}
$$
is proved. This condition contains no child error, source precision or field-width factor.
For uniform use, choose the structural charge first and prove the condition for every
allowed budget and terminal exponent. The theorem does not assert that the current
unbounded schedule satisfies it. In particular, stationarity preserves the clipped mean,
so a spectral sampling contraction cannot be applied to erase its slack growth.
The groupwise bound remains available, but the actual initial conditional mean has a
sharper signed telescope. `initial_sample_prefix_mean` applies stationarity separately to
each complete walk, even when lengths differ, and then cancels identical `sample` calls.
`initial_compressed_prefix_mean` supplies the literal compressed children: the same bin,
history, precision exponent, reset source, raw budget and environment occur at a shared
endpoint. Positive calls still require direct and reset-right availability; unavailable
calls are not filled in. Equal-budget groups execute zero. The schedule proves the starting
coarse budget is zero (`initial_start_budget`). Thus at prefix $j+1$ only the fine endpoint
at $d=\mathrm{dyadicSlack}(m,j)$ survives per bin. This cancellation concerns conditional
means; sampled centered noise does not telescope.

`initial_compressed_prefix_clipped_endpoint` applies the sharp own-mask bound only after
this signed cancellation. Its `initialClippedEndpointPrefixCharge` is
$(\sum_i (K(a,i)E_i(M-d))^{1/4})^4$, retaining actual scale cutoffs and zero endpoints.
`initialClippedEndpointWindow` contains only the surviving factor, and
`initialClippedEndpointPrefixCharge_paid` needs
$$
C^{1/4}W_{\mathrm{end}}(M,j,a,r)\le 2^{\mathrm{rankCharge}}.
$$
There is no sum over earlier large-slack windows. For $d\le16\,\mathrm{slack}$,
`initialClippedEndpointWindow_uniform` bounds this window by
$4\sum_{h\in\mathbb Z}\mathrm{scaleMajorant}(h)$ independently of bin count, horizon,
source/terminal exponents and field width. The existing summable majorant has the explicit
value `tsum_scaleMajorant`. `initialClippedEndpointPrefixCharge_uniform_paid` consequently
uses a single structural allocation chosen before those coordinates. Larger surviving
slacks still have their explicit exponential factor. The literal weights do not all
supply decay: stationary preloss uses $\delta 2^{-10d}$; the raw false-event coefficient
is $64K R^4/((K+1)\delta^4)\,2^{-24d}$, where $R=(2\max(\mathrm{cap},16))^{1/4}$.
The final index has $d=1$, though its child budget may still be zero at positive parent
precision. In contrast, the unconditional first-overflow tail uses
$28^{m-i}$ without a rarity discount for correlated transported error.

`initialClippedEndpointPrefixCharge_weighted_le` retains arbitrary nonnegative finite
weights on the endpoint fourth moments. `initialClippedEndpointPrefixCharge_sum_root_le`
retains weighted roots for stationary preloss and mean tails. The actual computed
first-mean minimum consumes the fourth-moment bound in `initialComputedPrecisionMoment_first_weighted_le`, keeping the weighted semantic
deficit separate. For raw false-event allocation use the coefficient indexed by $j$ on
the statistic for prefix $j+1$, as in `initialFourMaxReserve`; stationary and tail payments
use their rooted Minkowski sums. This weighted moment lemma alone does not close
those sums or replace the other three statistics in the reserve.

The existing deterministic mean-tail API has a different weight:
$((2+256/b_j)/n_j)^{1/4}$ outside its sum over $i\ge j$. With the actual floor and
capacity it is at most
$((2+256/\delta)/(K+1))^{1/4}2^{-27d_j/2}$.
Since $d_i\le d_j$ inside that tail, this decay can pay the endpoint factor
$2^{d_i/(16\,\mathrm{slack})}$, with the polynomial factor $28^{m-i}$ still to sum.
`compatible_rarity_decay` proves this coefficient with its $K+1$ gain.
`integrated_fourMax_tail_schedule` applies the deterministic row-tail comparison to the
actual conditional means and uses unique first-overflow summation for the centered noise.
The latter receives no rarity factor, even though all events and samples may be correlated.
`initialClippedEndpointWindow_growing` bounds every surviving window by
$4(\sum_h\mathrm{scaleMajorant}(h))2^{d_i}$, including unrestricted large slack.
`compatible_growing_mean_tail_le` sums the literal $28^{m-i}$ propagation against rarity.
`initialComputedPrecisionMoment_first_tail_le` therefore pays the computed first-mean
rooted tail by a horizon-independent transport coefficient plus its separately weighted
semantic deficit. `initialComputedFirstTailBudget` records this payment.

The existing `initial_compressed_precision_reserve` consumes all four deterministic
first-mean transport payments through `initialFourMaxReserve_le_tail` and
`initialSeparatedReserve`. The latter now accepts separate stationary, final, tail and
aggregate raw payments. Its terminal exponent must be in the field horizon, its floor
must be positive, and its structural charge nonnegative; the initial request has the
stated pilot task. These are explicit hypotheses, not successful parent accuracy.

For $E=4\sum_h\mathrm{scaleMajorant}(h)$, slope-one endpoint growth gives stationary
payment $\delta E/511$. Final slack is one, so its window is at most $E$, even when the
scheduled child budget is zero. The exact raw weight is
$64KR^4/((K+1)\delta^4)\,2^{-24d_j}$ and pays fourth-power endpoint growth with a
summable ratio. `initialComputedPrecisionMoment_first_raw_le` uses
`initialComputedPrecisionMoment_first_weighted_le` on the raw prefix $j+1$ with its
coefficient at $j$; it does not substitute the old unconditional weighted envelope.
`initialComputedFirstPreBudget`, `initialComputedFirstFinalBudget` and
`initialComputedFirstRawBudget` retain the separately weighted semantic deficit.
`initialFirstTransportPayment_exists_charge` chooses one structural charge for the
combined transport part after the fixed decoder/floor/cap and endpoint constants, before
precision, request coordinates, width, field or budget. This isolated transport allocation
excludes semantic deficits and the other three statistics.

The actual reserve consumer uses all these payments. Its raw assembly costs the fixed
factor $4^3=64$ for the four statistics, independent of the number of groups. The second
deterministic mean retains its literal rarity-weighted sum; both centered noises retain
unconditional weighted sums. Semantic omitted/inactive loss remains explicit: the existing
`initialPolynomialLoss_div_le` and `initialMeanCharge_geometric` bound it under their
retained-depth and cutoff-fit premises, which are additional schedule obligations. No
uniform smallness of that deficit follows just from scalar child accuracy. Complete
reserve allocation, ordinary progress and saturated preparation remain open.

For semantic omission, fix the evaluator's retained depth $n$ and a maximum budget
jointly: `BudgetData.bins` cannot change during recursion. The bounded-family interface
requires $c(1+4(n+a))<M\le32cn$, $2a\le n$ and nonnegative structural charge, where
$c$ is `slack` and $a$ is the terminal exponent. `bounded_family_depth_guards` derives
actual retained cutoff fit and $\mathrm{rate}(n)/\mathrm{rate}(a)\le2^{-p(M,r)}$.
`requestPrecision_le_omitted_depth_iff` gives the exact alternative maximum-budget
condition, retaining the source and rank penalties. It rules out taking $M$ arbitrarily
large at fixed $n$ for this exponent comparison.

With $P\le2^{n+1}$, the actual positive-prefix semantic row moment is at most
$32(2^{-p(M,r)}2^{-A\,\mathrm{rank}(r)})^4$
(`initialPolynomialLoss_row_bounded_family`). The rounded source
mass is bounded through `grid_row_moment_le`; nominal rates are not identified with
rounded masses. `initialComputedFirstFinalBudget_bounded_family` pays the semantic term
of the existing final budget. `initialComputedFirstFinalPayment` takes the smaller of
that budget and the paid bound when the numerical family guards hold, retaining the
original envelope otherwise. The existing `initial_compressed_precision_reserve` now
consumes this payment through `initialComputedPrecisionMoment_first_final_payment_le`;
`initialComputedFirstFinalPayment_le` preserves the old unconditional guarantee. The checked
[computed final client](../../ComplexityTests/InitialTwoPayment.lean) composes it with
`initialComputedPrecisionMoment_first_final_le`. The final transport term still retains
its independent structural charge.

The exceptional initial group now has component payments too. `initial_dyadicSlack_half`
proves its literal slack $d\ge M/2$. Under cutoff fit and $P\le2^{n+1}$,
`bounded_family_initial_row_decay` pays even $16P\,2^{-d}$ by
$32(2^{-p(M,r)}2^{-A\,\mathrm{rank}(r)})^4$, keeping the structural rank salary explicit.
`initialPolynomialLoss_first_weighted_family` applies this to the actual clipped semantic
row, permitting its full inactive mass. `initialPolynomialLoss_first_schedule_family`
pays its stationary fourth-power weight $\delta^4 2^{-40d}$, raw coefficient with exact
$K+1$ and $2^{-24d}$, and deterministic rarity-tail weight after all factor-28 propagation.
Index zero is the raw postincrement prefix one; it must not use the next coefficient.
Centered noises receive no rarity discount.

`initialPolynomialLoss_root_bounded_family` now retains the same structural rank salary
in the positive-prefix omission comparison and the exceptional initial group. Writing
$S=32^{1/4}2^{-p(M,r)}2^{-A\,\mathrm{rank}(r)}$, every semantic fourth root is at most
$S2^{d_i}$. For group zero this follows from its literal exponential weight; positive
prefixes use the rounded-source row bound. The existing growing-mean stationary, raw
and deterministic-tail sum lemmas then pay all prefixes without a group-count factor.
The raw prefix $j+1$ still uses coefficient $j$, including its exact $K+1$ gain.

`initialComputedFirstBudgets_bounded_family` assembles all four semantic contributions
with endpoint transport. The existing `initial_compressed_precision_reserve` consumes
these payments in its third, bounded-family separated-reserve bound and retains its two
earlier guarantees. `initialComputedFirstBudgets_exists_charge` invokes
`initialFirstTransportPayment_exists_charge` with one combined endpoint constant: decoder,
floor, capacity, bin cap and child-error coefficient are fixed first; the structural charge
is chosen before field width, retained depth, budget and request exponents. It pays the
complete conditional **first mean**, not the total reserve.

For a nonnegative row-substochastic base, the stronger
[uniform first-mean interface](../../Complexity/Foundations/Probability/HierarchyInitialMeanUniform.lean)
uses true mass rather than a full-width pointwise estimate. It retains full bins through
$n$, grid rates, the polynomial cutoff, admissible source/terminal exponents, positive
actual parent precision, task rank at least one, structural charge at least one and
$M\le32\,\mathrm{slack}\,n$. It needs neither a field-width upper bound nor every
retained bin to be active. The least inactive bin bounds the ratio-16 fine tail;
substochastic row mass cancels field width in the fourth moment.
`initialPolynomialLoss_root_uniform_le` pays every semantic prefix by
$4(1+2\,\mathrm{binCap})2^{-p}2^{-A}2^{d_j}$.
`initialComputedFirstBudgets_uniform` combines that payment with the existing endpoint
transport in the actual stationary, final, tail and raw first-mean budgets.
`initialComputedFirstBudgets_uniform_exists_charge` chooses one charge before the
field, retained depth, budget and endpoint exponents and pays their separated reserve.
The depth-versus-budget condition is essential: fixed retained depth can leave a
positive omission error as requested precision increases.

The [uniform clients](../../ComplexityTests/HierarchyInitialMeanUniform.lean) check
positive omitted mass with inactive retained bins, a terminal exponent beyond half
the retained depth, and a growing admissible prime family chosen after the structural
charge. Their actual precision is positive. The endpoint remains conditional on
separately established child execution and accuracy.

The [checked clients](../../ComplexityTests/PolynomialBudgetHistory.lean) include a family
with that fixed charge, bounded primes, one horizon covering every retained bin, positive
actual parent precision and nonzero diagonal omitted semantic mass. A separate full
reserve client at $P=5$, $M=16$, depth two uses horizon **two**, not the previous component
fixture's horizon one. It consumes the actual computed minimum and assembled reserve,
with lower-child own-request accuracy and direct/reset-right success left as explicit IH
hypotheses. This is not a proof that those hypotheses hold jointly. The existing actual
inactive loss-one and zero/exhausted boundary checks remain. General-stage noise,
progress and preparation, correction products, the full changing-request IH and native
RL=L remain open; production leaves are unchanged.

`initialClippedEndpointWindow_growth` gives a necessary condition for a proposed
allocation $wW_{\mathrm{end}}\le2^A$ when $w\ge1$: every live bin $i$ must satisfy
$$
\frac{d}{16\,\mathrm{slack}}+\frac1{16}-\frac34|i-a|\le A.
$$
The checked regression at $M=8192$, group $1$, slack $1$ and bin/terminal exponent zero
has a positive scheduled child budget and violates this condition for $A=64$, even
before multiplying by $28^{m-i}$.
`initialClippedEndpointWindow_tail_growth` checks the same necessary condition for
the exact rooted tail sum, and its regression rejects that allocation too. Thus these
unconditional tail coefficients do not justify a uniform endpoint-window allocation by themselves. This is a counterexample
to that numerical inference, not to the estimator's accuracy. The deterministic payment above uses the actual rare event instead; ordinary progress
and successful recursive preparation remain independent gaps.

The [allocation regressions](../../ComplexityTests/InitialTwoPayment.lean) retain the older
$M=4$ fixture, whose parent precision is negative. The positive-precision fixture fixes
charge $64$ first, then chooses $M=16(64\,\mathrm{rank}(r)+p)$ for any positive integer $p$
at full source/terminal rate and three bins. Its parent precision is exactly $p$ and its
surviving transport fourth moment is paid by $2^{-4p}$ at every slack at most $16$.
The bound is consumed by `initialComputedPrecisionMoment_first_endpoint_paid`.
This tests positive-precision numerical allocation and the actual minimum, conditional on
the separate child IH; it does not certify recursive availability or a complete reserve.
The executed history regression checks adjacent unequal groups with a shared nonzero
endpoint and exact prefix means after their different completed walks.
The joint positive-precision fixture fixes charge $64$, varies both source and terminal
exponents within the horizon, and checks all four first-mean payments for every positive
integer precision, with no surviving-slack cutoff. A separate test chooses one charge
for `initialFirstTransportPayment` before an arbitrary real precision. The existing
small-floor, nonzero executed compressed-child and zero-boundary full-reserve regressions
remain checked. Neither the conditional numerical tests nor the zero-boundary fixture
prove a nonzero executed full reserve.

The literal computed first-coordinate consumers are
[`initial_compressed_precision_clipped_first`](../../Complexity/Foundations/Probability/HierarchyTransportedPreparation.lean)
and `initial_compressed_precision_clipped_endpoint_first`. They add the semantic
omitted/inactive deficit explicitly. `initialComputedPrecisionMoment` takes the minimum
of the previous mean cost, the groupwise bound and the telescoped endpoint bound. The
existing precision four-statistic, `actualFourMax`, raw `clippedError` and sharp-reserve
proofs consume this minimum. Sharper first-noise and supported preparation payments are
explained below. A covered initial four-statistic reserve allocation is given below;
the simultaneous changing-request invariant and native endpoint remain open.
The [two-atom regression](../../ComplexityTests/InitialTwoPayment.lean) shows why: scalar
rooted fourth error $1/32$ can coexist with centered normalized fourth error $1$ after
physical scaling. It also distinguishes clipping after averaging from averaging clipped
samples. These are finite inference tests, not an executed recursive counterexample.

The [computed-prefix preparation payment](../../Complexity/Foundations/Probability/HierarchyTransportedPreparation.lean)
combines these transported moments with the semantic history's actual omitted/inactive deficit
and centered first noise. `BudgetData.initialTransportMoment` keeps the prefix cube and sum
of group costs explicit; those group costs retain the bin cube and own-request importance
sup norms. `initial_compressed_prefix_absolute` returns the literal computed group list and bounds
its absolute error before preparation. `initial_compressed_mean_moment` separately combines
the conditional-mean perturbation with the semantic deficit, without charging semantic
centered noise to that deterministic payment. `initial_compressed_preparation` applies the polynomial
cutoff and full-terminal rank-gate sensitivity to those prefixes, with the explicit usage
payment $P(|\zeta|(L_h+L_\rho)/\mathrm{rate}(k_a))^4$. It also identifies the actual clipped
second mean and pays centered preparation-walk noise on usage without a rarity discount.

The stronger
[supported preparation interface](../../Complexity/Foundations/Probability/NormalizedAtomRows/SupportedPreparation.lean)
pays the actual second mean without that width factor. Saturating the actual polynomial
entry cutoff and hierarchy rank gate converts clipped relative raw error into preparation
error, including signed approximations and arbitrarily large nonnegative truth. The
union of the two actual preparation supports contains at most $2K$ entries per row.
With $C=2+(L_h+L_\rho)(4\theta+5)$, conditional Jensen bounds the second clipped-mean
moment by $8(2K)(|\zeta|C)^4$ times the sum of the first clipped-mean and centered-noise
moments. Both inputs use the full terminal rank mask; Jensen uses the narrower usage
mask on the original environment.

`initialSecondSignal_relative_mean_moment` maps this to the actual successful
preparation walks. The second-mean coordinate of `initialComputedPrecisionMoment`
takes the smaller of its previous bound and this supported payment; the same actual
four-max and separated-reserve consumers use it.

[HierarchyInitialSecondMeanAllocation](../../Complexity/Foundations/Probability/HierarchyInitialSecondMeanAllocation.lean)
pays the actual second-mean coordinate numerically. `initialSecondMeanConstant` fixes
$\zeta,L_h,L_\rho$ and the primitive hierarchy/bin constants before geometry. The actual
root cost is at most $L_2\,2^{-p}2^{-A}2^{d_j}$; the existing growing-mean schedule
then pays its stationary floor, final value, deterministic rarity tail and raw
false-event sum with literal capacities, postincrement indices and $K+1$ gain.
`initialComputedSecondMeanReserve_exists_charge` chooses one charge after those fixed
constants, before field, depth, endpoints and budget, and pays the reserve containing
these four actual `false/1` sums. It retains positive parent precision, initial/grid
requests, polynomial cutoffs, a nonnegative row-substochastic base, covered depth
$M\le32\,\mathrm{slack}\,n$ and one horizon admitting the full bin family and endpoints.
Its [growing-family test](../../ComplexityTests/HierarchyInitialSecondMeanAllocation.lean)
realizes admissible primes after the charge and checks positive precision and omitted
mass. This does not pay the separate second centered-noise statistic or construct
successful recursive children; neither centered-noise slot receives a rarity discount.

[HierarchyInitialSecondNoiseAllocation](../../Complexity/Foundations/Probability/HierarchyInitialSecondNoiseAllocation.lean)
pays the separate centered noise from the actual selected-preparation usage walks.
The sparse input has fourth moment at most $16K$; squaring the existing logarithmic
spectral payment retains spare decay without changing the computed walk length.
`initialSecondNoiseMoment` intersects this payment with the previous range bound,
retaining $\zeta$, the original source normalization and the full terminal rank mask.
The literal successful preparation-list theorem and `compressedBin_secondNoise_allocated`
identify the actual executed histories. They do not require first-history accuracy or
second-mean stability, and execution remains a premise.
The `true/1` coordinate of `initialComputedPrecisionMoment` consumes this sparse minimum
under `initialSecondNoiseAdmissible`: polynomial auxiliary preparation, the actual grid
source and terminal, an admissible source horizon, and a usage exponent at least the
terminal exponent on the same suffix. The previous range cost remains available.

`initialSecondNoiseMoment_schedule` pays the stationary, final, raw and unconditional
factor-$28$ tail allocations. The charge is chosen after fixed scalar constants and
before geometry, with the explicit field-family condition
$(512K+1)2^{2A}\le P$. This condition pays the structural decay absent from the old
range envelope; it is not an unrestricted-field theorem. The
[checked clients](../../ComplexityTests/HierarchyInitialSecondNoiseAllocation.lean)
include nonconstant selected input with strictly positive centered noise after every
finite production walk length, literal preparation execution, and growing prime-field
families with positive precision. The supplied first history is not asserted recursively
available.

[HierarchyInitialReserveAssembly](../../Complexity/Foundations/Probability/HierarchyInitialReserveAssembly.lean)
collects the four actual costs in `initialComputedFourStatisticReserve`. It preserves
the two deterministic heavy-event payments, the two unconditional centered-noise tails
and the outer raw coefficient $64$. `initialComputedFourStatisticReserve_exists_charge`
chooses one charge after the fixed preparation, decoder, floor and capacity constants,
then pays this mixed-tail reserve by $2^{-4p}$ on the covered field/depth family above.
The first-mean and second-mean inputs still require a nonnegative row-substochastic
base, polynomial cutoffs, positive precision and a horizon admitting the full bin family
and endpoints. `initial_compressed_precision_reserve_fourStatistics` connects the same
actual completed groups and preparation list to this reserve, conditional on the
lower-budget own-request accuracy and separate reset-right execution premises. It checks
the final-payment comparison and the raw fourth-root identities explicitly.
The [joint allocation regression](../../ComplexityTests/HierarchyInitialReserveAssembly.lean)
fixes the common charge before growing budgets, constructs prime horizons realizing the
field and full-bin coverage, and checks positive precision and nonzero omitted semantic
mass together with the complete numerical payment. It does not construct successful
recursive children.
This does not pay the coarser unconditional `initialNumericalReserve`,
which discards the deterministic rarity gain, or construct simultaneous recursive
accuracy and availability.

The [actual-history client](../../ComplexityTests/HierarchySupportedPreparation.lean)
executes its literal walks and checks nonzero second-mean bias paid by first-mean
budget $1/16$ and zero first noise. The
[scalar and rank clients](../../ComplexityTests/SupportedPreparation.lean) realize
hierarchy parameters and test nonzero error, signed input and both saturation cases.
The old `secondMeanEnvelope` remains an absolute fallback and can genuinely grow with
field width; the new theorem bounds the actual preparation discrepancy instead.

`BudgetData.decodePrefixes` is the shared pure decoding step now used by `compressedBin`.
`exists_initial_compressed_fourMax` accepts the literal computed-history group execution and
successful preparation walks, then applies the same sharp parent comparison. Its
`initialFourMaxReserve` retains stationary preloss, final no-overflow error, deterministic
heavy-tail selection and raw false-overflow charges at prefix $j+1$. Constants keep their
order: decoder coefficient, positive floor, preloss coefficient, then width and executions.
`initial_compressed_precision_moments` now supplies all four actual moments directly
from strict lower-budget rooted hypotheses at each direct child's own `requestPrecision`.
The reset-right call must also succeed on its own request. The computed first noise is
centered at its own conditional mean: centering the perturbation costs at most sixteen
in fourth moment, followed by the constant-eight comparison with semantic centered noise.
The first deterministic payment contains the transported mean and omitted/inactive deficit,
while the preparation mean also consumes their supported relative payment. First quantities retain the
full terminal mask; preparation noise retains usage.

`initial_compressed_precision_fourMax` pays both the four-max moment and raw postincrement
clipped error from those four moments. `initial_compressed_precision_reserve` then bounds
the literal `initialFourMaxReserve` by `initialNumericalReserve`. This scalar expression
retains the floor, capacity, stationary coefficient, final prefix, all weighted tail
prefixes, and raw false-event coefficients. It conservatively drops heavy selection,
without giving either noise a rarity discount. Bin/prefix cubes, importance sup norms,
width/rank-rate sensitivity, actual child precision and slack remain explicit numerical
costs. The endpoint payment `initialEndpointCharge` is exactly zero at budget zero;
empty paired groups also cost zero, including equal positive endpoint budgets. The
importance multiplier uses the finite-function sup norm: the existing max row norm
needs only $\|w\|_\infty^4$, rather than $\sum_y |w(y)|^4$. This removes an unnecessary
factor of $P$ for constant weights while retaining the actual importance ratios.
`Cslib.vertexNormPow_sum_ite` uses mutually exclusive first overflows to pay the sum
of their fourth moments. Thus the tail term is
$\sum_j (\sum_{i\ge j}28^{m-i}a_i)^4$, without an outer group-count cube. The
literal heavy events remain in `initialFourMaxReserve`; the numerical comparison
still supplies no rarity discount.

For a single literal completed group, use
`completedGroup_initial_compressed_centered_precision` to retain the spectral factor
before uncentered contraction loses it. This consumes strict lower-budget direct-child
rooted moments on their own usage and actual precision, together with separate
reset-right availability. `pairedSample_initial_compressed_precision_at` requires these
facts only for positive endpoints of an unequal pair, rather than every smaller budget
or inactive bin. Successful compression supplies the bounded range used in
the root-to-ordinary conversion. The actual compressed-minus-semantic input is summed
before completion, then centered on its original source/usage slice. The integrated
comparison retains joint slice densities, including empty slices, and costs
$32\rho^{2\,\mathrm{steps}(M,r,d)}$, with the existing graph gap and walk length.
No noise receives a rarity discount.

`initial_active_pair_losses` proves that unequal executed endpoint budgets force
$c(1+4|i-k_a|)<2d$, and both losses are at most $2d$, even when the coarse endpoint
is zero. `requestPrecision_initial_active_pay` cancels the inherited source and actual
direct-rank decrease against the literal precision formula. Its ordinary scale-plus-
precision exponent is bounded by $25d/(8c)<6d$ for $c\ge1$; it does not use the older
conservative $8w$ window. `initialRootGroupCharge_le_active` feeds this comparison into
`initialActiveRootGroupCharge`, and the completed-group theorem returns that sharp-cancellation
finite envelope as well as the original own-endpoint payment.
`initial_completion_gap_payment` bounds the spectral coefficient by the unchanged
scheduled fourth power $(2^{-\mathrm{precision}(M,r)}64^{-d})^4$ in this consumer. Equal pairs retain zero
charge; a zero endpoint demands no child accuracy. The charge is fixed before request
exponents vary. Complete checked active fine/coarse, equal-positive and exhausted
clients, including an actual budget-one child with diagonal error one feeding the
completed-group bound, are in [PolynomialBudgetHistory](../../ComplexityTests/PolynomialBudgetHistory.lean);
[ActualFirstSignal](../../ComplexityTests/ActualFirstSignal.lean) checks fully correlated
two-atom centered inputs and their raw spectral comparison.

For the literal prefixes, `initial_compressed_centered_first_noise` now sums the
centered compressed-minus-semantic group discrepancies using weighted Minkowski on
these same joint slices. Its fourth-moment payment is the fourth power of the sum
of the individual fourth roots, without a prefix cube. `initialCenteredGroupCharge`
retains the exact spectral factor and endpoint charges; equal/exhausted pairs stay zero.
The semantic `initialRelativeNoiseBudget` is added separately, with no rarity discount.
`initial_compressed_precision_moments` consumes this payment in the first-noise minimum
of `initialComputedPrecisionMoment`. The existing four-max and raw separated-reserve
consumers therefore use the new minimum on actual computed histories.

`initial_importance_norm_le` bounds rounded importance by sixteen on one common
admissible horizon, independently of field width and copy suffixes.
`initialActiveRootGroupCharge_bounded` bounds the finite bin factor when the number of
bins is at most $L+1$. The sharp exponent $25d/(8c)$ is at most $5d$, leaving residual
$2^{-d}$ under the unchanged $64^{-d}$ schedule. Positive parent precision pays the
extra precision factor. `initialComputedPrecisionMoment_firstNoise_exists_charge`
chooses one structural charge from the primitive bin cap, child coefficient and $L$,
before field width, request exponents and budgets, for all terminal exponents at most
$L$ and full bin families of size at most $L+1$. The common admissible horizon and
positive parent precision remain explicit hypotheses. The inverse terminal normalization
is bounded by $\mathrm{rate}(L)^{-1}$ in this family; no cancellation for an unbounded
terminal/bin family is claimed. The checked clients vary the full bin family, horizon
and positive precision under this one charge, and check a fully correlated two-atom
geometrically weighted moment as well as existing nonzero actual child-error/reserve clients.

For unbounded exponents, `initial_normalized_importance_precision_le` keeps rounded
importance, inverse terminal rate and own-request precision together **pointwise**, before
sup norms. If $δ=i-a$, the coarse importance exponent $-4δ$ (or zero in the fine
case) combines with the child's terminal-precision exponent $2δ$ to give $2|δ|$.
Source precision cancels; the bound is sixteen times
$2^{-p}2^{-A}2^{(M-m)/(16c)+2|δ|}$, with actual budgets and direct-rank decrease.
`initial_normalized_active_precision_le` uses the unequal-pair cutoff and both endpoint
losses to bound this by $16\,2^{-p}2^{-A}2^{2d/c-|δ|}$. No absolute terminal
bound or schedule change is needed for this scalar comparison. The checked
[InitialTwoPayment client](../../ComplexityTests/InitialTwoPayment.lean) fixes charge seven,
varies unbounded source/terminal/bin exponents and full finite bin horizons, checks actual
precision $p+2>0$, and checks both endpoints of coarse, equal-scale and fine unequal pairs.
Admissible prime horizons exist for every tested depth. This is numerical allocation,
not simultaneous successful recursive execution.

The normalized row-moment bridge now has an actual consumer.
`rowNormPow_weighted_sub_precision_le` keeps positive own-request precision attached
to the endpoint coefficient before taking a sup norm. It preserves the direct child's
source normalization and its own usage mask, using successful compression's proved
zero extension; enlarging the parent terminal mask costs no inverse terminal density.
`positiveSample_initial_compressed_normalized_precision` and
`pairedSample_initial_compressed_normalized_precision_at` apply this to literal child
executions. Only unequal positive endpoints require direct accuracy and separate
reset-right availability. Equal pairs execute no child; zero endpoints have zero charge.

`completedGroup_initial_compressed_normalized_precision` uses finite Minkowski on these
normalized inputs before actual centered spectral contraction, removing the global bin
cube from this lane. `initialRootGroupCharge` and `initialComputedBoundedCenteredNoise`
remain the bounded fallback.
`initial_normalized_bin_sum_le` sums geometric offsets on both sides of the terminal
scale via the existing summable scale majorant. The fixed primitive constant is
`initialNormalizedNoiseConstant`; no absolute source/terminal cap, field-width payment,
weighted IH, canonical support for approximate children, independence or rarity is used.
The unchanged $64^{-d}$ schedule dominates the at-most $4^d$ input growth, leaving
$16^{-d}$ in `completedGroup_initial_compressed_normalized_paid`.

`initial_compressed_normalized_noise_consumer` constructs literal completed-group lists
from conditional own-request endpoint IH and pays the actual `actualNoiseEntry` first
coordinate, with correlated-prefix Minkowski. The target denominator only contracts the
already normalized discrepancy. `initialComputedPrecisionMoment` now takes the minimum
of both existing fallbacks and `initialComputedNormalizedNoise` whenever
`initialNormalizedNoiseAdmissible` holds. That guard requires nonnegative structural
charge and parent precision, actual grid bin rates and initial task, and one admissible
horizon for the terminal and all bins. `initial_compressed_precision_moments` proves the
new branch on actual computed histories; the existing four-max and raw separated-reserve
consumers use the same updated minimum.

The normalized prefix payment retains $16^{-d}$ decay after correlated-prefix Minkowski.
`sum_propagation_mul_sixteenth_le` pays the literal factor-$28$ unconditional noise tail
with the fixed geometric constant $1792/57$, including the two-unit exponent offset;
it uses no heavy-event rarity. `compatible_sixteenth_noise_schedule` retains the actual
floor, compatible capacity, $K+1$ gain and raw postincrement weights.
`initialComputedPrecisionMoment_firstNoise_weighted_le` and
`initialComputedPrecisionMoment_firstNoise_schedule_le` apply these bounds to the
actual computed first-noise minimum. Each allocation keeps the supported semantic
`initialRelativeNoiseBudget` residual explicitly. The tail residual has its full
factor-$28$ propagation and receives no rarity discount.

`initialComputedFirstCoordinate_reserve_le` exposes the four semantic-noise residuals
beside the unchanged complete first-mean budgets. The checked canonical budget-boundary
primitive now pays those residuals with $4^{-d}$ rooted decay, strengthening the earlier
$2^{-d}$ envelope without changing steps or its support argument. This primitive applies
to canonical semantic input; approximate children still use their own-request transport
bound and separate reset-right availability. Its hypotheses retain the polynomial cutoff,
grid requests, nonnegative row-substochastic base, positive budget, nonnegative parent
precision and one admissible bin/terminal horizon.

`initialComputedPrecisionMoment_firstNoise_polynomial_schedule` pays the complete
actual computed first-noise minimum in the stationary, final, unconditional tail and raw
allocations. Current `meanRowTail`, `integrated_fourMax_tail_schedule` and the actual
reserve consumer use $28^{m-i}$ at root level. We therefore retain that literal weight:
$4(m-i)\le d_i+8$ gives geometric ratio $28/4^4=7/64$ and tail constant $458752/57$.
For transported noise, $2(m-i)\le d_i+2$ gives ratio $28/16^2=7/64$ and constant
$1792/57$. No fourth root of the factor 28 or heavy-rarity discount is inserted into
these unconditional noise sums. Raw allocation keeps the literal capacity, floor,
postincrement index and $K+1$ gain.

`initialComputedFirstCoordinateReserve` adds the complete first-mean budgets to these
actual computed first-noise terms in `initialSeparatedReserve`, including the outer
raw factor 64. `initialComputedFirstCoordinateReserve_exists_charge` pays it with one
charge chosen after the primitive bin cap, child coefficient, floor, decoder and capacity
constants, before field, horizon, requests, depth, budget and precision. It retains the
first mean's original full-bin fixed-depth/bounded-budget family, including width and
budget bounds and the common horizon. The stronger
`initialComputedFirstCoordinateReserve_uniform_exists_charge` in the uniform first-mean
module pays this same actual combined reserve with one charge before the field, depth,
budget and endpoint exponents. It uses the true-mass hypotheses above and retains
$M\le32\,\mathrm{slack}\,n$, strict positive precision, the initial task, and a common
horizon admitting every bin and both endpoint exponents. It removes the extra width,
half-depth and all-retained-bins-active restrictions. This remains a conditional
first-coordinate numerical certificate. The second-mean and sparse second-noise
allocations are described above; successful recursive execution remains separate.
The original `initial_compressed_precision_reserve` still provides the actual `hb` and
weighted raw consumers under explicit lower-child IH; the new certificate pays its
first-coordinate allocations, not the full four-statistic reserve.

The full-bin positive-precision family in InitialTwoPayment also checks the actual
computed minimum's unconditional tail. PolynomialBudgetHistory checks a fully correlated
two-atom tail at every horizon and its nonzero exact third-horizon fourth moment
$(5271/1024)^4$. These are complementary to its actual nonzero child-error execution
fixture, whose centered stationary noise may vanish.

`initialComputedPrecisionMoment_firstNoise_uniform_charge` chooses one charge from the
primitive bin cap and child coefficient before field, horizon, request, budget or precision.
The checked full-bin family in [InitialTwoPayment](../../ComplexityTests/InitialTwoPayment.lean)
has source $n$, terminal $n+1$, bins through $n+2$, and actual positive precision $p+2$,
for unbounded $n,p$. Its actual-noise client retains explicit endpoint execution/IH;
it does not construct a joint successful recursive family. The actual nonzero-child
client in [PolynomialBudgetHistory](../../ComplexityTests/PolynomialBudgetHistory.lean)
also consumes the normalized lane, with a separate reset call and no success demand
for its unused bin. Existing fully correlated two-atom noise clients remain checked.

The existing semantic noise now also has a uniform structural payment, proved in
[HierarchyInitialSemanticNoise](../../Complexity/Foundations/Probability/HierarchyInitialSemanticNoise.lean).
For the polynomial cutoff `boundedRoutedBinCutoff (polynomialSwitch4 (1/2) 1)`
and a nonnegative row-substochastic base, an initial canonical group with $2d<M$ is zero: both positive endpoint
budgets give the same canonical sample, or the cutoff removes both. Thus a nonzero
group has $M\le 2d$. Nonnegative initial request precision bounds the structural
charge by $M$, and the original $64^{-d}$ schedule pays this charge, the budget and
the last dyadic slack. The original correlated-prefix cube is retained and absorbed
using $j\le\log_2 M+1\le M\le2^M$; no independence is assumed.
`initialRelativeNoiseBudget_polynomial_uniform_le` bounds that same semantic budget
by the fourth power of $256\,\mathrm{binCap}\,2^{-p}2^{-A}(1/4)^{\mathrm{slack}}$.

`initialComputedNormalizedNoise_polynomial_uniform_le` combines this with the
normalized transport payment. `initialComputedPrecisionMoment_firstNoise_polynomial_paid`
chooses one natural charge before every field, horizon, bin family, request and budget,
and pays the complete first-noise coordinate of the actual computed minimum by
$(2^{-p}(1/4)^{\mathrm{slack}})^4$. The canonical support argument applies to the
semantic input; approximate children still use the conditional own-request IH above.
The evaluator and walk steps are unchanged.

[HierarchyInitialSemanticNoise](../../ComplexityTests/HierarchyInitialSemanticNoise.lean)
checks a nonzero sample whose early group vanishes and a growing full-bin family
with fixed positive charge and positive precision.
[HierarchyInitialFirstNoise](../../ComplexityTests/HierarchyInitialFirstNoise.lean)
checks the complete computed cost with one charge chosen before arbitrary field,
depth and positive precision, together with existence of admissible prime horizons.
These numerical allocation clients do not construct successful recursive children.

The complete first-coordinate allocation combines the previously assembled bounded
first mean with complete first noise under the stated guards and conditional child
execution/IH. The supported second mean, sparse second noise and covered joint initial
reserve are described above. General terminal-rank/product applications, full
changing-request accuracy/availability and native RL=L remain open.
Production leaves are unchanged.

For the same executed prefixes, `initial_compressed_first_noise` now also returns a
pairwise normalized payment. `initialRelativeNoiseBudget` sums the scheduled conditional
group contractions, retaining the joint slice density and the actual centered input
fourth moment divided by $(\mathrm{rate}(k_a)+G(x,y))^4$. The literal
`initialGroupInput` retains bin importance weights and fine/coarse availability; correlated
groups pay the cube of the number of included groups. Empty slices contribute zero.
`initialGroupInput_relative_fourth_le` derives the finite input/target relation
$$
\mathbb E_{\sigma\mid x,y}
\left|\frac{A_d(\sigma,x,y)-\mathbb E[A_d\mid x,y]}
{\mathrm{rate}(k_a)+G(x,y)}\right|^4
\le \left(\frac{2\,\mathrm{magnitude}(r)}{\mathrm{rate}(k_a)+G(x,y)}\right)^4.
$$
This generic magnitude estimate supplies no rate or width cancellation for small targets.
For the literal ratio-16 polynomial cutoffs, use
`initialSample_polynomial_relative_bound`, `initialGroupInput_polynomial_relative_bound`
and `initialGroupInput_polynomial_relative_fourth_le` instead. Their hypotheses identify
`binRate = rate` and the actual bounded unrouted polynomial numerator, admit the terminal
and every retained bin exponent in one horizon, and require a nonnegative substochastic
base for the group bound. The pointwise estimates need no source-role or nonzero-padding
premise: they also hold in the degenerate cases. Thus they apply, in particular, to the
usual distinct-role, nonzero-padding admissible parent requests without extra support
assumptions. At most two bins contribute at a pair, and the nested fine/coarse guards
charge each sample once. With $f=\mathrm{rate}(k_a)$ they give
$$
|\mathrm{sample}_i|\le64\,B.\mathrm{binCap}(f+G(x,y)),\qquad
0\le I_d\le128\,B.\mathrm{binCap}(f+G(x,y)).
$$
The normalized centered fourth moment is at most $(256\,B.\mathrm{binCap})^4$,
including empty slices. `initialGroupInput_polynomial_eq_zero` proves exact zero input
where the target is zero, without a positive target floor.
`initialRelativeNoiseBudget_polynomial_le` feeds this bound through the existing scheduled
walk lengths: its upper bound is $(256\,B.\mathrm{binCap})^4$ times the literal
prefix cube times the sum of the scheduled fourth-power tolerances. The proof starts
with the actual joint slice densities, bounds them by one and uses the existing
width/source-rate spectral allocation and `magnitude ≥ 1`.
`initialComputedRelativeMoment_polynomial_firstNoise_le` bounds the actual computed
minimum with this semantic payment, preserving its transported-child charge and absolute
fallback. The [checked clients](../../ComplexityTests/PolynomialBudgetHistory.lean)
cover positive nonconstant canonical inputs, two active adjacent bins, zero targets and
a smaller terminal rate. `initialComputedRelativeMoment` takes the minimum of this
semantic group payment (plus transported centered child error) and the previous absolute
first-noise cost. The actual own-precision four-statistic, four-max and sharp-reserve
consumers use this noise minimum. `initialComputedPrecisionMoment` additionally sharpens
the first mean with the own-mask clipped-prefix payment and first noise with the
centered spectral prefix payment described above. The second mean also uses the
supported relative preparation payment; the second-noise coordinate uses the guarded
sparse minimum above and retains its unconditional range fallback.
The absolute transport fallback pays `initialPerturbationFactor`, the fourth power of the finite sup norm of
$(\mathrm{rate}(k_a)+G(x,y))^{-1}$. The reusable `rowNormPow_mul_le_pi_norm` applies
this fixed pair weight on the original source/terminal masks. Its input is the executed
prefix error already derived from strict lower-budget own-request rooted precision,
including separate reset-right availability; no weighted IH is assumed. For a constant
positive target $g$, the factor is $(\mathrm{rate}(k_a)+g)^{-4}$ and is strictly smaller
than inverse fourth rate. The checked nonconstant perturbation and positive substochastic
target cost client exercise this gain; the actual small-floor nonzero-child and
zero-boundary reserve clients remain checked.

This is a worst-pair refinement after unweighted child/group/prefix transport. It does
**not** retain pair weights inside direct/left/reset-right transport or derive a stronger
pair-weighted rooted IH. If the target vanishes at some pair, the factor can still be the
old inverse fourth rate. `initialPerturbationFactor_eq_of_zero` proves this equality,
and a checked actual small-floor child on the identity target has weighted fourth error
$1/16$ even though that worst-pair factor is unchanged. Such zero entries are allowed for
admissible substochastic matrices. The remaining child obligation needs control of
weighted error on its actual executed support; the existing scalar IH does not supply it.
The new polynomial semantic payment does not pay this transported error, preparation
sensitivity or the other reserve costs. General-stage joint allocation and the
simultaneous changing-request invariant remain open. The own-mask clipped first-mean
comparison now has the corresponding computed compression/reserve consumer described
above; it cannot replace the untruncated sampling payment by itself. No uniform
positive target floor, free parent accuracy or heavy-event rarity discount is assumed.
The checked positive budget-two history has nonzero group input but zero centered
conditional noise: with zero transported error the new first-noise cost vanishes while
the old envelope is positive. This does not assert zero approximate-child error.
A separate nonconstant example checks a strictly positive normalized fourth moment.

Uniform absorption does not follow by increasing the budget in this envelope.
`initialComputedMoment_final_firstNoise_zero` computes the final semantic first-noise
charge, even with zero transported child error, as
$$
\frac{8}{63^4}2^{16k_a}\left(2^{-p(M,\{r\text{ with usage}=r.terminal\})}\right)^4.
$$
`initialComputedMoment_firstNoise_not_uniform` chooses a terminal exponent before
all budgets and requests at which this exceeds any proposed uniform coefficient times
that precision fourth power. Its exponent is independent of `r.terminal`; there are no
admissibility, horizon/prime-bound or successful-execution guards. For fixed prime it
includes exponents beyond admissible horizons, so this is not a valid-call counterexample.
`initialComputedNumericalReserve_ge_noise` shows the
same factor survives the final reserve summand built from the **old absolute costs**,
multiplied by $128KC^4$. This lower bound does not apply to the new minimum payment.
These are lower bounds on the old **numerical envelope**, not on actual noise or estimator error.
The old absolute preparation sensitivity contains
$P(|\zeta|(L_h+L_\rho)/\mathrm{rate}(k_a))^4$; the supported payment above removes that
width factor from the actual minimum. Raw coefficients retain inverse fourth powers
of the floor and literal $28^{m-i}$ tails. The covered initial four-statistic allocation
is given above. General-stage and changing-request estimates still need their joint
parameter allocation and recursive argument; a fixed-request depth threshold or a
supplied parent-accuracy/four-max budget cannot establish that endpoint.
The [complete checked clients](../../ComplexityTests/PolynomialBudgetHistory.lean) include a
budget-two parent pair whose actual budget-one compressed child has diagonal error one with
valid scalar small-floor parameters, a separately executed reset-right child, and a literal
zero-boundary history consuming preparation sensitivity and the sharp reserve.

**Remaining parent-error gap:** the fixed-request initial compressed-bin allocation is
paid. Allowing $k_a=n$ instead leaves the active charge exactly one, as the retained edge
case checks; that varying-request envelope lies outside the fixed-constant theorem.
Transport from an invariant covering
ALL actual lower-budget calls is unproved. Heavy-event rarity applies only to deterministic mean envelopes; it must not discount
correlated noise. Bounded lower-child root-to-ordinary conversion and same-environment
reset-right-source transport remain to be assembled for general recursive children.
The general initial multi-bin and noninitial parent steps, nonconstant routing, and the
simultaneous compressed parent-error theorem remain open.

The simultaneous all-lower-budget row/vector availability, canonical error, support and range
invariant is unfinished. The finite compressed-bin consumer above is wired, but its general canonical mean/noise
payments from the simultaneous lower-budget invariant remain unproved; the fixed-HP reserve
output theorem does not discharge this routed-bin obligation. Incoming-column
closure, inactive-constructor availability and coarse accuracy, omitted-bin/mean/noise summation,
residual preparation/normalization, weights/rewards and positive-stage copy routing remain open.
The earlier single-bin canonical accuracy result retains its scope. No selected abstract or
headline claim changes; there is no analytic or native RL=L endpoint here.

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
