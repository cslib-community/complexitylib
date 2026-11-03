# Find and apply a result

Search for the contract you need, then inspect the theorem that provides it. The [model map](../model-map.md) routes unfamiliar terminology to source files; the reference chapters explain the representations. Once the goal is fixed, a nearby checked client is usually a better implementation starting point than the library's umbrella import. [complexitylib][complexitylib]

## Follow a name to its usable statement

Run searches from the repository root. For circuit construction, this finds both the API and its clients:

```sh
rg -n 'Synthesis.Builder|exists_circuit_outputs' Complexity ComplexityTests
```

Read the defining module's imports and namespace before importing it. A file under `Complexity/` commonly extends `Cslib.*`; machine declarations use `Turing.*`. For inherited declarations, search the pinned CSLib source after the [dependency preflight](getting-started.md). Do not assume an identically named declaration in a different checkout has the same type.

Before applying a result, identify its input/output types and encoding, quantified witnesses, size parameter, charged resource, uniformity and side conditions. In particular, check whether a machine is chosen once before all inputs, whether the bound is eventually or pointwise, and whether the theorem requires a valid representation. If these disagree with the [contract you chose](choosing-models.md), find a transport theorem or prove the missing conversion. Changing notation does not establish a model bridge.

## Build a shared Boolean circuit

<!-- worked-example -->

**Worked example: Share one negation between two circuit outputs**

**Goal:** a three-input, two-output Boolean circuit computing `(!x₀ ∧ x₁, !x₀ ∨ x₂)` with at most three gates.

Open [ComplexityTests/SynthesisBuilder.lean](../../ComplexityTests/SynthesisBuilder.lean). Its imports are `Complexity.Computability.Circuit.Boolean.Word`, `Complexity.Tactic.Synthesis` and `Mathlib.Tactic.FinCases`. The contextual excerpt below requires that file's `open Cslib Cslib.Circuits Cslib.Circuits.Boolean` and checked surrounding context:

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
[RowCompression/SaturatedRoot](../../Complexity/Foundations/Analysis/RowCompression/SaturatedRoot.lean)
and open `Cslib.RowCompression`. `exists_iterate_root_bound` compares the actual schedule with
a zero-increment reference sharing its initial loss. Supply first-signal saturation, rank-gate
closure, a uniform output-root range and global root regularity in both signals and the padded
rank. The theorem retains the second signal; it requires a positive horizon, nonnegative true
first entries, small true second entries and bounded common losses. Its constant is uniform in
the schedule and true first-entry magnitudes. The rank uses the full retained set and actual
default, so agreement on a smaller usage set does not suffice.

For the scalar upper-cap step, use
[RowCompression/BoundedCap](../../Complexity/Foundations/Analysis/RowCompression/BoundedCap.lean)'s
`abs_min_add_sub_min_add_le`: relative error at most `1/2` gives capped absolute error
`(4 * θ + 5) * ε` when the common loss has magnitude at most `θ`. This bounds a scalar comparison;
it does not truncate stored states. For the concrete polynomial family, keep importing
[PolynomialAtomRows/Relative](../../Complexity/Foundations/Probability/PolynomialAtomRows/Relative.lean)
or [ClippedError](../../Complexity/Foundations/Probability/PolynomialAtomRows/ClippedError.lean);
their public theorem contracts are unchanged and discharge the scalar assumptions themselves.

Open the complete
[two-signal regression client](../../ComplexityTests/RowCompressionSaturatedRoot.lean) for the
imports, concrete output, proved scalar contracts and a positive-output fixture. It also checks
that the second coordinate affects the output, arbitrarily large off-usage truth changes the
actual rank gate, and unbounded common loss invalidates the scalar estimate. From a configured
checkout, run:

```sh
scripts/build.sh --wfail --iofail ComplexityTests.RowCompressionSaturatedRoot ComplexityTests.PolynomialAtomRelative ComplexityTests.PolynomialAtomCompression
```

A successful build checks these comparisons and the existing polynomial clients. If the bound
does not apply, check the horizon, loss and small-second-signal hypotheses before changing the
rank domain or adding a cap. These deterministic lemmas do not supply integrated normalized-output
moments, recursive estimator budgets or a native class endpoint.

## Read abstracts, bridges and comparison contracts

For a named headline such as Fagin's theorem, locate its entry in `abstracts/catalogue.json`, then read [FaginAbstract.lean](../../abstracts/ComplexityAbstracts/FaginAbstract.lean). Follow `FaginBridge.fagin` to the library result in [Fagin/Converse.lean](../../Complexity/Computability/Complexity/Fagin/Converse.lean). The presentation exposes finite relational vocabularies, unary cardinality, framed relation tables and malformed-input rejection. The library theorem `Cslib.Logic.ESO.definable_iff_queryLanguage_mem_NP` takes an isomorphism-closure hypothesis; its adjacent theorem packages that hypothesis into the equivalence. Choose the form matching your goal and the [finite-model representation](../circuits-logic-and-other-models/finite-model-logic.md).

The abstract is a readable presentation and its bridge proves the connection. The underlying library declaration is normally the reusable API. `#check_abstract` audits dependencies; it does not decide whether the semantics match your application. Likewise, `comparator/` contains selected independently stated contracts and solutions applying library theorems. Its coverage is explicit and limited, so absence from comparator is not a failed theorem check. Read the [assurance reference](../design-and-assurance/assurance.md) when deciding what evidence a result already has, and use the [contribution workflow](contributing.md) for any new proof or representation bridge.

[complexitylib]: ../sources.md#complexitylib
