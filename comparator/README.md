# Independent statement comparisons

These suites check selected complexitylib proofs against separately written mathematical
contracts with Lean's `lake comparator --paranoid`. The command compares theorem statements
and their referenced definitions, checks the permitted axioms, and requires acceptance by Lean's
kernel and every external checker bundled with the pinned toolchain.

The statement files import only the pinned upstream CSLib and Mathlib dependencies. The solution
files apply existing complexitylib theorems to those statements. This separation makes a change
to the solution's interpretation of a statement detectable by comparator.

## Run

Use the repository's `lean-toolchain`, install `bubblewrap` (`bwrap` on `PATH`) on Linux, and
prepare the dependencies as for an ordinary build. The usual cache bootstrap is optional:

```sh
scripts/cache/ensure.sh
python3 scripts/check_comparator.py
```

The default runs `basic` and `automation`, covering four theorems. The larger SAT suite is
explicitly selected:

```sh
python3 scripts/check_comparator.py sat
python3 scripts/check_comparator.py basic automation sat --negative-control
```

The negative control submits ordinary valid proofs of `True` under the two basic theorem names.
It succeeds only when comparator reports the expected theorem-statement mismatch; a build error
or an unavailable sandbox does not count as the expected rejection.

To inspect the generated challenge inputs without running a proof check:

```sh
python3 scripts/check_comparator.py basic automation sat --prepare-only
```

The runner always invokes the official sandboxed `lake comparator --paranoid`. Some containers
and managed hosts prohibit the namespaces that sandbox needs. Such a run fails; the runner
does not disable the sandbox or interpret failure to run as successful verification. Use a
Linux host supporting Lean's sandbox, such as the dedicated Comparator workflow, to complete
the check. Consult Lean's documentation for expert workflows with separately produced exports.

## Contracts

| Suite | Independently stated claim | Existing source theorem |
| --- | --- | --- |
| `basic` | Membership-preserving admissible reductions compose | `Cslib.Complexity.ManyOneReducibleBy.trans` |
| `basic` | A function different from every coordinate projection needs at least one gate | `Cslib.Circuits.one_le_complexity_single` |
| `automation` | Applying a polynomial-time function to half a bitstring and retaining its suffix is polynomial time | `Cslib.Crypto.GoldreichLevin.polyTime_paddedFunction` |
| `automation` | The Boolean inner product of two equal halves is polynomial time | `Cslib.Crypto.GoldreichLevin.polyTime_paddedPredicate` |
| `sat` | For each fixed clause width, an exact model counter has the stated subexponential time and polynomial space bounds | `Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter` |
| `sat` | The independently stated ETH is false | `Cslib.Complexity.CountingNativeEndpoint.not_ETH` |

Each `ComplexityComparator/<Suite>/Statements.lean` defines propositions without importing
complexitylib's implementations. Each corresponding `Solution.lean` proves its fixed
propositions by applying the source theorems. The two automation source proofs use `polytime`.
Their independent contract quantifies a binary finite-state multi-tape machine and polynomial
time and space bounds before the input; it spells out both algorithms and their encodings.

The SAT statements define CNF evaluation, counting assignments of the occurring variables,
binary natural labels, framed serialization, time and space budgets, and ETH explicitly. The
counter and constants precede all formulas for each fixed width. Its exponential parameter is
the number of distinct occurring variables; its polynomial factors use encoded input length.
The exponent is the shifted interpolation scale
`n * log(log(n + 16))^2 / sqrt(log(n + 16))`, and output length is separately charged to the space
bound.

## Trust and scope

The challenge still trusts the meaning of the reviewed statements and the pinned upstream
machine, circuit and mathematical definitions. External kernels establish that the exported
proof proves that formal proposition; they cannot establish that it is the intended informal
mathematical claim. New or changed contracts need semantic review, including quantifiers,
encodings, resource conventions, and nonvacuity.

The statement files, runner, Lake configuration, and pinned upstream dependencies are trusted
inputs. Review changes to them independently. The workflow also runs repository setup and cache
scripts before comparator; its green status alone does not authenticate a hostile submission
that can change those inputs. Adversarial review requires a trusted harness and environment.

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted. There are no permitted
definition holes. A successful suite certifies its named contracts and their proof dependencies
under the checkers' assumptions; it does not certify every theorem or file in the repository.

No admitted proof is committed. The runner generates the deliberate challenge placeholders and
their configurations under the ignored `comparator/ComplexityComparatorChallenges/` directory
before invoking Lake. This source directory is outside `.lake`, so the official build sandbox
cannot modify the trusted challenge source. The solution has no challenge placeholders.

The optional `ComplexityComparator` library builds the committed statements and solutions.
The generated-challenge library has no roots and no default build facets; Lake resolves its
modules only when comparator explicitly requests one. Neither a normal build nor
`lake build @complexitylib` needs generated files or builds admitted challenge stubs. Both
comparator libraries use `roots = []`, so `mk_all` never generates aggregates importing their
children. The default `Complexity` target and test driver are unchanged. To compile just the
committed checks:

```sh
lake build ComplexityComparator
```

The Comparator workflow runs all suites and the negative control. It is manual-only: start it from
the Actions tab or with `gh workflow run comparator.yml --ref <branch>`, for example after
changing the comparator files, the runner or the dependency pins. It no longer runs on every pull
request or push to `main`, because those runs cost far more CI time than the assurance they added.
Results belong to the checked revision and should be read from that run.

See Lean's [proof validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
and [Lake comparator documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)
for the checker and sandbox trust model.
