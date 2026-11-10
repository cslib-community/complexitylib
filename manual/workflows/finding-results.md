# Find and apply a result

Search for the contract you need, then inspect the theorem that provides it. The [model map](../model-map.md) routes unfamiliar terminology to source files; the reference chapters explain the representations. Once the goal is fixed, a nearby checked client is usually a better implementation starting point than the library's umbrella import. [cslib-frontier][complexitylib]

## Follow a name to its usable statement

Run searches from the repository root. For circuit construction, this finds both the API and its clients:

```sh
rg -n 'Synthesis.Builder|exists_circuit_outputs' CslibFrontier CslibFrontierTests
```

Read the defining module's imports and namespace before importing it. A file under `CslibFrontier/` commonly extends `Cslib.*`; machine declarations use `Turing.*`. For inherited declarations, search the pinned CSLib source after the [dependency preflight](getting-started.md). Do not assume an identically named declaration in a different checkout has the same type.

Before applying a result, identify its input/output types and encoding, quantified witnesses, size parameter, charged resource, uniformity and side conditions. In particular, check whether a machine is chosen once before all inputs, whether the bound is eventually or pointwise, and whether the theorem requires a valid representation. If these disagree with the [contract you chose](choosing-models.md), find a transport theorem or prove the missing conversion. Changing notation does not establish a model bridge.

## Build a shared Boolean circuit

<!-- worked-example -->

**Worked example: Share one negation between two circuit outputs**

**Goal:** a three-input, two-output Boolean circuit computing `(!x₀ ∧ x₁, !x₀ ∨ x₂)` with at most three gates.

Open [CslibFrontierTests/SynthesisBuilder.lean](../../CslibFrontierTests/SynthesisBuilder.lean). Its imports are `CslibFrontier.Computability.Circuit.Boolean.Word`, `CslibFrontier.Tactic.Synthesis` and `Mathlib.Tactic.FinCases`. The contextual excerpt below requires that file's `open Cslib Cslib.Circuits Cslib.Circuits.Boolean` and checked surrounding context:

<!-- excerpt: synthesis-shared-circuit -->
```lean
example : ∃ c : Circuit signature 3 2,
    c.Computes interpretation (fun x => ![!x 0 && x 1, !x 0 || x 2]) ∧ c.size ≤ 3 := by
  let b := Synthesis.Builder.start interpretation (inputs 3)
  let shared : BooleanFunction 3 := fun x => !x 0
  let b := b.add (Synthesis.of_mem (f := fun x => x 0) (by synthesis_available) |>.not)
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).and
    (Synthesis.of_mem (f := fun x => x 1) (by synthesis_available)))
  let b := b.add ((Synthesis.of_mem (f := shared) (by synthesis_available)).or
    (Synthesis.of_mem (f := fun x => x 2) (by synthesis_available)))
  synthesis_step b using Synthesis.of_mem (f := shared)
  have hcost : b.cost = 3 := rfl
  fail_if_success
    have := b.finish (t := {shared}) (k := 2) (by synthesis_available) (by omega)
  have h := b.finish (k := 3)
    (t := Set.range fun i x => (![!x 0 && x 1, !x 0 || x 2] : BitString 2) i)
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> synthesis_available) (by omega)
  exact h.exists_circuit_outputs
```

The obligations are availability of every gate input, availability of the selected outputs, and the final budget inequality. Begin with input wires; append the negation once; reuse it for AND and OR; finish with the desired output family. `synthesis_available` searches existing wires, while `add` charges the appended construction. The extra reuse step costs zero.

**Result:** a circuit, its evaluation theorem and an upper bound on gate count. The failed two-gate budget checks this builder's accumulated cost; it does not prove an optimal lower bound over all circuits. It also says nothing about native construction time.

**When it fails:** if availability fails, inspect the current wire set: the tactic cannot manufacture a missing negation. If the budget fails, inspect which construction was appended twice.

<!-- /worked-example -->

The [circuit reference](../circuits-logic-and-other-models/circuits-and-formulas.md) explains other bases and measures before you transfer the recipe.

## Compare compressed row outputs

For deterministic two-signal compression comparisons, import
[RowCompression/SaturatedRoot](../../CslibFrontier/Computability/LogSpaceDerandomization/RowCompression/SaturatedRoot.lean)
and open `Cslib.RowCompression`. `exists_iterate_root_bound` compares the actual schedule with
a zero-increment reference sharing its initial loss. Supply first-signal saturation, rank-gate
closure, a uniform output-root range and global root regularity in both signals and the padded
rank. The theorem retains the second signal; it requires a positive horizon, nonnegative true
first entries, small true second entries and bounded common losses. Its constant is uniform in
the schedule and true first-entry magnitudes. The rank uses the full retained set and actual
default, so agreement on a smaller usage set does not suffice.

For the scalar upper-cap step, use
[RowCompression/BoundedCap](../../CslibFrontier/Computability/LogSpaceDerandomization/RowCompression/BoundedCap.lean)'s
`abs_min_add_sub_min_add_le`: relative error at most `1/2` gives capped absolute error
`(4 * θ + 5) * ε` when the common loss has magnitude at most `θ`. This bounds a scalar comparison;
it does not truncate stored states. For the concrete polynomial family, keep importing
[PolynomialAtomRows/Relative](../../CslibFrontier/Computability/LogSpaceDerandomization/PolynomialAtomRows/Relative.lean)
or [ClippedError](../../CslibFrontier/Computability/LogSpaceDerandomization/PolynomialAtomRows/ClippedError.lean);
their public theorem contracts are unchanged and discharge the scalar assumptions themselves.

Open the complete
[two-signal regression client](../../CslibFrontierTests/RowCompressionSaturatedRoot.lean) for the
imports, concrete output, proved scalar contracts and a positive-output fixture. It also checks
that the second coordinate affects the output, arbitrarily large off-usage truth changes the
actual rank gate, and unbounded common loss invalidates the scalar estimate. From a configured
checkout, run:

```sh
scripts/build.sh --wfail --iofail CslibFrontierTests.RowCompressionSaturatedRoot CslibFrontierTests.PolynomialAtomRelative CslibFrontierTests.PolynomialAtomCompression
```

A successful build checks these comparisons and the existing polynomial clients. If the bound
does not apply, check the horizon, loss and small-second-signal hypotheses before changing the
rank domain or adding a cap. These deterministic lemmas do not supply integrated normalized-output
moments, recursive estimator budgets or a native class endpoint.

For the actual hierarchy decoder, import
[NormalizedAtomRows/BoundedLoss](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/BoundedLoss.lean)
and open `Matrix.FourthRootHierarchyParams.NormalizedRow`. `output HP ζ d v r` uses the
actual bounded atom cutoff, core rank gate and `clip (v / ζ)`.
`boundedLoss_root_bound` derives normalized fourth-root error from raw clipped error,
nonnegative truth on the full rank set and common first loss bounded by `atomCap`.
There is no upper bound on true first entries. Its exact saturation identities concern
only output arguments. For a single full H4 environment,
[NormalizedAtomRows/Request](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/Request.lean)'s
`normalizedRequest_eq_output` identifies the existing request, preserving the narrower
usage mask and full terminal rank. The [actual-output regressions](../../CslibFrontierTests/NormalizedAtomRows.lean)
check off-usage rank closure, unbounded-loss failure and positive output after an increment
from zero. These deterministic prerequisites feed the conditional moment route below;
recursive/native RL remains open.

For sharp no-overflow and first-overflow comparisons, import
[NormalizedAtomRows/Sharp](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/Sharp.lean).
`fixed_shape` supplies positive shape and denominator scales. Choose those first, then
use `sharp_noOverflow` or `sharp_firstOverflow`: final/tail coefficients precede the later
positive dyadic floor, while the weighted preloss coefficient may depend on it.
`sharp_compression` keeps the complementary false-first-overflow exclusion explicit.
[RequestSharp](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/RequestSharp.lean)
applies both comparisons to the existing single-environment request; its first-overflow
client derives the preparation mean range from bounded preparation values, even on empty
slices. The [positive-floor exact-increment client](../../CslibFrontierTests/NormalizedAtomSharp.lean)
starts from zero, allows arbitrary nonnegative first magnitude and obtains zero root error
from exact raw prefixes. Run `scripts/build.sh --wfail --iofail CslibFrontierTests.NormalizedAtomSharp`
from a configured checkout. Nonzero raw-prefix moments, false-overflow payments and recursive
reserve choices still need their own proofs; these comparisons do not establish them.

For actual heavy-first-overflow input tails, import
[NormalizedAtomRows/ClippedTail](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ClippedTail.lean)
and open `Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments`.
`integrated_actual_clipped_tail_capacity` uses the actual first-overflow masks at any
capacity sequence dominating `2^(64*dyadicSlack)`. Supply nonnegative genuine row mass,
a deterministic clipped conditional-mean envelope and noise-max fourth moments. The first
channel is conditioned on the full terminal rank set; the second uses the narrower usage
set. `actual_walk_prefix_support` derives literal second-channel zero extension for
conditional-walk telescoping increments starting at zero. Heavy-event rarity discounts only
the deterministic mean term. Correlated noise receives its full moment budget, with no
independence assumption for the adaptively maximizing endpoint. The resulting tail coefficient
has the explicit mean factor `(2 + 256*M/η)/63` and noise factor `7/9`.

The [tail regressions](../../CslibFrontierTests/NormalizedAtomTails.lean) check a nonconstant,
correlated endpoint moment and a nonzero telescoping prefix. From a configured checkout run
`scripts/build.sh --wfail --iofail CslibFrontierTests.NormalizedAtomTails`.
These are conditional compression input estimates; deriving their lower-child envelopes
and noise budgets, recursive reserves and native RL remains separate work.

For the actual normalized-output fourth moment, import
[NormalizedAtomRows/ActualMoment](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ActualMoment.lean)
and keep the same `NormalizedMoments` namespace open.
For the first-signal endpoint row-noise premise, the
[FirstSignal route](probabilistic-workflows.md) derives the bound from genuine
conditional-walk prefixes and explicit lower-child incoming moments. The
[SecondSignal route](probabilistic-workflows.md) constructs the completed-raw selected preparatory
input from those children and derives usage-slice endpoint ROW noise. Its pre-walk
support bound pays 16K on an admitted source horizon, and an explicit logarithmic step
choice discharges the actual second-prefix dyadic budget for positive tolerance. Mixing
around the selected input mean does not establish its convergence to the genuine target.
The [MeanBias route](probabilistic-workflows.md) now controls that deterministic discrepancy
by explicit absolute residual entry and full-rank maximum errors on the same full
environment, using the actual rho gate and joint source × usage mean. It retains the
rate divisor and ζ scaling; deriving numerical errors from recursive relative estimates
remains open.
For an integrated second deterministic envelope, use
[SecondEnvelope](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/SecondEnvelope.lean).
`secondMeanEnvelope_moment` keeps the width P and inverse rank-rate fourth power;
`actualEstimatedResidual_second_envelope_moment` pays it from the finite range/support bound on the shared
`estimatedResidualInput` and finite positive-bin/once-negative child-error costs.
`estimatedResidualInput_moment_le` retains the scale sum, top/fine caps, exact rounded
marginals and width P; it needs no final input-moment certificate. The target stays the canonical
residual at km, while full terminal rank and normalization stay at kt. This is a finite
absolute error bridge; small recursive errors and numerical reserves remain open.
The [FirstPayment route](probabilistic-workflows.md) now supplies a finite first-signal
payment from actual bin/correction ranges, exact importance and midpoint-density factors,
and an explicit retained width P. Both signal clients use `spectralWalkLength`; its
positive-tolerance guarantee leaves numerical mean envelopes, recursive budgets/reserves,
parameter/workspace growth and native RL=L open.
For the finite conditional output from actual lower-child cost moments, use
[ReserveOutput](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ReserveOutput.lean).
It constructs the common B by a finite scaled maximum, chooses both actual walk lengths,
and discharges the compatible-capacity output theorem at the genuine canonical residual.
The explicit allocation depends on the positive prefix horizon; recursive reserve induction,
copy routing and parameter/workspace growth remain open. See the
[probabilistic workflow](probabilistic-workflows.md) for the exact reserve and amplification.
`actual_normalized_fourth_moment_capacity` bounds the row fourth moment of the difference
of output fourth roots by `C*ε^4`. Its output evaluates the actual compression iterate,
unchanged initial default, raw increments and dyadic floor; its first rank is full terminal
rank and its final mask is usage. `genuineNormalizedRecipe_eq_request` identifies the target
with the existing `normalizedRequest`, including its genuine joint preparation mean and
inherited suffixes.

Choose the hierarchy and positive signal scales first, then a positive compression floor η.
The final coefficient may depend on η, but precedes P/J/N/u, row width, positive horizon m
and the capacity sequence. Supply clipped deterministic mean envelopes, their endpoint row
fourth moments, strong endpoint row-noise fourth moments on each channel's own mask, and
actual second-channel zero extension. No true-entry cap or final-output error bound is a
premise. The proof combines the final/no-overflow term, weighted preloss, heavy first-overflow
tails and the complementary false-event union charged at prefix `j+1`. Two actual output
supports give the factor `2K`, without a row-width factor.

The capacities n must satisfy both `K ≤ n i` and `2^(64*dyadicSlack m i) ≤ n i` for i<m.
`compatibleCapacity K m i = (K+1)*2^(64*dyadicSlack m i)` supplies both for arbitrary fixed K;
`actual_normalized_fourth_moment_compatible` applies it to the actual output itself. Increasing
capacity changes the algorithm: event rarity and false-overflow charges are proved at n,
with no assumed output or event monotonicity. The
[capacity regression](../../CslibFrontierTests/NormalizedAtomCapacity.lean) constructs an inhabited
hierarchy with K beyond 2^64, checks both capacity bounds at every horizon and proves positive
uncentered output after a nonzero first increment from zero row/default. Run
`scripts/build.sh --wfail --iofail CslibFrontierTests.NormalizedAtomCapacity`.
These fixtures do not instantiate all stochastic premises. Lower-child contracts, the full
recursive hierarchy estimator and native resources/RL remain open; this conditional result
is not a class equality.

## Read the library statement of a named result

For a named result such as Fagin's theorem, search the [results inventory](../../results/README.md) and the API documentation, then read the library statement in [Fagin/Converse.lean](../../CslibFrontier/Computability/Complexity/Fagin/Converse.lean). Its input convention, with finite relational vocabularies, unary cardinality, framed relation tables and malformed-input rejection, is documented in [Encoding.lean](../../CslibFrontier/Logics/FirstOrder/Encoding.lean). The library theorem `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP` takes an isomorphism-closure hypothesis; its adjacent theorem packages that hypothesis into the equivalence. Choose the form matching your goal and the [finite-model representation](../circuits-logic-and-other-models/finite-model-logic.md).

The library declaration is the reusable API, and its statement is the authoritative contract. An inventory entry records sources and scope; the registry checks the theorem's identity, not whether its semantics match your application. Read the [assurance reference](../design-and-assurance/assurance.md) when deciding what evidence a result already has, and use the [contribution workflow](contributing.md) for any new proof or representation bridge.

[complexitylib]: ../sources.md#complexitylib

For actual output from per-request rooted moments, use
[RootReserveOutput](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/RootReserveOutput.lean)
and its [child reserve payment](../../CslibFrontier/Computability/LogSpaceDerandomization/NormalizedAtomRows/ChildRootReserve.lean).
The full-environment finite allocation is explicit and conservative; it supplies no recursive
accuracy or parameter/workspace closure. The source-reset guard and exact coefficients are
explained in the [probabilistic workflow](probabilistic-workflows.md).

The two reserve-output theorems choose their output constant after the fixed hierarchy,
ζ, scale and positive floor, before the prime, environment width, horizon, prefix length
and raw/preparation/maximum families. Select this constant before allocating recursive
child accuracies. Uniformity of that coefficient does not remove any displayed finite
allocation or walk-length losses and supplies no recursive accuracy theorem.

For changes to the completed pilot maximum with raw and preparation children fixed,
[HierarchyCorrectionStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCorrectionStability.lean)
gives a pointwise fourth-root bound and an integrated actual-request contract. Its
[regressions](../../CslibFrontierTests/HierarchyCorrectionStability.lean) check a nonzero request,
pilot plateaus, a dyadic change of maximum estimate and an empty vertex domain. These are
local sensitivity tests, not a two-level recursive approximate estimator.

For changing completed RAW and PREP children as well, use
[HierarchyCorrectionRawStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyCorrectionRawStability.lean).
Its pointwise theorem displays entry, row, column and full source×terminal maxima at the
actual inverse terminal rate, and the original joint source/usage prep mean error.
The integrated theorem pays RAW absolute row errors with explicit width squared and
inverse-rate fourth power, PREP errors on source/usage rows, and maximum errors on the
original source/full-terminal pairs. Constants are selected at fixed HP before requests
or child tables. The [nonzero fixtures](../../CslibFrontierTests/HierarchyCorrectionRawStability.lean)
perturb RAW and PREP separately and jointly, and distinguish row from incoming ranks.
This supplies a local correction accuracy contract; it does not construct recursive children.

For the pilot's actual score, detector and running maximum local moments, use
[PilotRowStability](../../CslibFrontier/Computability/LogSpaceDerandomization/PilotRowStability.lean).
It keeps the raw K-rank, pays detector source maxima on the actual finite slices after
conditional Jensen, and pays both maximum children. The score row payment displays
one width and inverse rate to the fourth power; detector payments retain their literal
conditional means and sums. [HierarchyPilotStability](../../CslibFrontier/Computability/LogSpaceDerandomization/HierarchyPilotStability.lean)
feeds the previous/current maximum children into the actual correction contract.
The [nonzero client](../../CslibFrontierTests/PilotRowStability.lean) changes a raw rank and
all three recipe outputs. Allocated recursive calls and full environment/rate/bin
transport of these payments remain separate from this local layer.
