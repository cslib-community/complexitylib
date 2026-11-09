# Get oriented and build

Start with the kind of claim you want Lean to check. A running Lean function, an equality of probability distributions, and a polynomial-time certificate answer different questions. Complexitylib connects these layers through explicit theorems. Open a client that proves the kind of statement you need, then follow its imports and encodings. [complexitylib][complexitylib]

## Prerequisites and the checkout's version

Use Git, Python 3.11+, Lean's `elan`/`lake` tools and a Lean-capable editor, or a text editor
with command-line checks. An agent, MCP server or account with an AI provider is not required.
Install Lean using its [official setup instructions](https://lean-lang.org/install/).
The checked-out [`lean-toolchain`](../../lean-toolchain) selects the Lean release;
[`lake-manifest.json`](../../lake-manifest.json) selects dependency revisions. Keep those
files together and follow the [current setup instructions](../../README.md#build-a-checkout).
Do not replace them with the historical survey's pins.

**Start:** a shell with Git and `elan` available, outside an existing checkout. Run:

```bash
git clone https://github.com/cslib-community/cslib-frontier.git
cd cslib-frontier
scripts/build.sh --wfail --iofail
```

**Expected result:** the requested library build exits zero under strict warning and
I/O-error settings. It is one build, not the full integration gate. The wrapper tries cache
restoration before Lake; a cache miss may cause compilation. If it fails, keep the first
error and use [build troubleshooting](troubleshooting.md#diagnose-missing-or-stale-artifacts).
The [cache guide](../../scripts/cache/README.md) explains missing artifacts and retries.

Before opening a cold checkout in a Lean editor, run:

```bash
scripts/cache/ensure.sh
```

Bare `lake` does not run this helper. A recent stamp records an attempted restore, not
proof that every artifact was found. MCP is an optional editor-assistance interface. Its commands do not invoke the bootstrap;
run the helper before using MCP in a cold checkout.

## Read the directory names correctly

The package is `complexitylib`; imports start with `CslibFrontier.`. Most declarations live in `Cslib` namespaces; the Turing-machine API uses `Turing`. A module path and its declarations' namespace therefore need not have the same first component.

| Place | Use it for |
|---|---|
| `CslibFrontier/` | Definitions, semantics, resource predicates and theorems |
| `CslibFrontierTests/` | Small clients, edge cases, failure guards and regressions |
| `guide/` | Explanatory chapters with Lean examples |
| `results/` and `CslibFrontierResults/` | Checked inventory of named results and their sources, linked to the API documentation |
| `ROADMAP.md` | Outstanding directions and incomplete endpoints |
| `UPSTREAM.md` and source markers | CSLib coordination and local-copy status |

Import a topic module or tactic module first. `import CslibFrontier` imports the entire library and is usually unnecessary for a small client. The [architecture reference](../design-and-assurance/architecture.md) explains the layers.

## A first worked example

**Start:** the repository is available, you have read the current contribution policy,
and no other task owns the fresh branch and directory names below. From the primary checkout:

```bash
scripts/worktree.sh create docs/manual-first-client manual-first-client HEAD
cd .worktrees/manual-first-client
scripts/build.sh CslibFrontierTests.NPCompleteness CslibFrontierTests.PolyTimePlainDriver --wfail --iofail
```

The helper prepares an isolated working directory and mutable build outputs. `HEAD` is
interpreted relative to the primary checkout; use an explicit revision if you need a
different base. Pick different branch and directory names if these are already in use.
For a source-only checkout or dependency changes, read the helper's
[isolation modes](../../scripts/cache/README.md#automatic-restoration).

**Read the complete client:** open [`CslibFrontierTests/NPCompleteness.lean`](../../CslibFrontierTests/NPCompleteness.lean).
It imports `CslibFrontier.Computability.Complexity.Problems.Clique` and
`CslibFrontier.Tactic.PolyTime`, enters `CslibFrontierTests.NPCompleteness`, and opens
`Cslib.Complexity Turing.MultiTapeTM`. Keep that context. Follow `startsTrue_mem_P`:
its three fields give a Boolean decider, its polynomial-time certificate and its
membership equivalence. Then follow `complementInstance_polyTime`,
`independentSet_to_clique` and `clique_npComplete`. The reduction's direction, encoded
inputs and correctness equivalence are explained in the [deterministic workflow](deterministic-workflows.md).

**Expected result:** both complete test modules elaborate. The first reuses existing
membership, reduction and hardness theorems and checks boundary graphs; the second tests
plain certificate automation. This does not establish a new completeness result or run
all integration gates. The client bodies are canonical source, not copied tutorial files.
The editorial check described here does not itself claim a fresh Lean build.

<!-- worked-example -->

**Worked example: Repair a named-certificate proof**

**Goal:** observe how `polytime` discharges a named certificate's remaining bound when
ordinary `fun_prop` does not, then restore the successful proof in your disposable worktree.

Open the complete client
[`CslibFrontierTests/PolyTimePlainDriver.lean`](../../CslibFrontierTests/PolyTimePlainDriver.lean).
Its imports and `open Turing.MultiTapeTM` are at the top; the following contextual excerpt
is inside `namespace PlainDriverTests`, after the opaque routine and its named certificate:

<!-- excerpt: first-client-negative-guard -->
```lean
-- `fun_prop` cannot discharge the contract; named lookup must expose and solve it through Aesop.
example (B : Cslib.WordRAM.Basis) (c : ℕ) :
    ComputableInPolyTime (checkedNamedConstant B c c) encUnary (encOption encNat) := by
  fail_if_success fun_prop
  polytime
```

**Try the failure:** in your isolated copy only, replace the last two lines by `fun_prop`.
Save and run:

```bash
scripts/build.sh CslibFrontierTests.PolyTimePlainDriver --wfail --iofail
```

The check is expected to fail at that example. Read the diagnostic in the editor or command
output: `fun_prop` finds `checkedNamedConstant_polyTime`, but cannot prove the necessary
assumption `c ≤ c`. The `program_certificate` annotation also registers the theorem with
`fun_prop`; here the extra work is discharging its bound. The
[automation reference](../design-and-assurance/automation.md) explains the shared registration.

**Repair:** restore
`fail_if_success fun_prop` followed by `polytime` and repeat the same command. It is
expected to succeed.

**Result:** `polytime` performs named-certificate lookup and solves the bound;
`fail_if_success` deliberately asserts the weaker tactic's failure. The test file should
be restored to its original contents, with no intentional failure left in a contribution.

**When it fails:** if the original guard itself fails on a future revision, the automation
changed and this exercise needs review. If the original client fails before reaching this
example, use [build troubleshooting](troubleshooting.md#diagnose-missing-or-stale-artifacts)
before drawing conclusions about the tactic.

<!-- /worked-example -->

**Finish:** from that worktree run `git diff --check` and `git status --short`. After
restoring the experiment, the test file should have no diff. For a real change, include
its complete client, the manual-impact assessment and the actual validation result in
the [review handoff](contributing.md#make-the-handoff-reviewable). Never report the
intentional failing build as a successful check.

To remove only this disposable exercise worktree after it is clean and no work needs
preserving, return to the primary checkout and use Git's guarded removal:

```bash
cd ../..
git worktree remove .worktrees/manual-first-client
```

The branch is retained. If Git refuses because files are modified, inspect and preserve
them before retrying; do not force removal. This command is not a cleanup procedure for
another contributor's worktree.

The [Verso guide](../../guide/CslibFrontierGuide.lean) provides further checked tutorials:
[first steps](../../guide/CslibFrontierGuide/FirstSteps.lean),
[NP-completeness](../../guide/CslibFrontierGuide/NPCompleteness.lean),
[streaming](../../guide/CslibFrontierGuide/Streaming.lean), and
[first-order operators](../../guide/CslibFrontierGuide/FirstOrderOperators.lean).
Use those source files for their example bodies. The workflow chapters' quoted Lean
blocks remain contextual excerpts: open each linked full client for its complete imports
and assumptions. Their identity is checked against current source by the manual checker;
that check is not standalone elaboration. [Historical hosted validation](../development-history/timings.md)
has its own dated scope and cannot validate later changes.

## Use Complexitylib from your own project

Match your project's `lean-toolchain` to the chosen Complexitylib revision. Choose a full commit SHA deliberately; `git rev-parse HEAD` in that checkout prints it.
In a TOML Lake project, add this template, replacing the placeholder with that SHA:

```toml
[[require]]
name = "cslib-frontier"
git = "https://github.com/cslib-community/cslib-frontier"
rev = "<the-full-commit-SHA-you-selected>"
```

Run `lake update cslib-frontier` and `lake build` from your project. If you directly require CSLib or Mathlib too, align them with the chosen manifest and include their package names in the update command when changing their pins. Commit the resulting manifest, Lake configuration and toolchain together. Updating only Complexitylib leaves other direct dependencies locked. See the [external-project instructions](../../README.md#use-from-another-lean-project).

[complexitylib]: ../sources.md#complexitylib
