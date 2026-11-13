# Readable security experiments

This page is for anyone adding or changing a security experiment, a reduction or an adversary type under `CslibFrontier/Crypto`. A reader should be able to compare an experiment with its figure in Boneh–Shoup, Katz–Lindell or Goldreich line by line, and word encodings should appear only where efficiency is stated. The rules are in [Security experiments](../../AGENTS.md#security-experiments); the Diffie–Hellman modules show them.

## Write an experiment like its textbook figure

1. **Write the experiment for a fixed instance.** [DiffieHellman/Finite.lean](../../CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean) fixes a group `G` and a generator `g`. `cdhExperiment` is a `ProbComp Bool` program that follows Attack Game 10.5 of [bs23][bs23] step by step: the challenger draws `a` and `b`, the adversary `A : G → G → ProbComp G` receives `a • g` and `b • g`, and the experiment returns whether its answer is `(a * b) • g`. The body mentions no encoding, security parameter or setup, and binds every value by name. Name such a program `…Experiment`.
2. **State the advantage and reductions on that experiment.** `cdhAdvantage` evaluates the experiment once, as a `Game`. A reduction such as `cdhToDDH` is a typed adversary built from another typed adversary. Bounds between fixed-instance advantages need no efficiency hypothesis.
3. **Derive the family game.** In [DiffieHellman.lean](../../CslibFrontier/Crypto/Computational/DiffieHellman.lean), `cdhGame` draws group parameters `d` from the setup law, then evaluates `cdhExperiment` in the group `F.Carrier d`. Name such a game `…Game`. It is the only place that evaluates the experiment with `ProbComp.eval`.
4. **Put the encodings in the efficiency predicate.** `CDHAdversary` is a typed function of the security parameter, the group parameters and two group elements. Its input is the record `CDHInput` with named fields (`secParam`, `groupParameters`, `leftPublic`, `rightPublic`), and `CDHAdversary.IsPPT` says that one uniform strict PPT machine computes the adversary from the record's encoding `encCDHInput`. The assumption `CDH` quantifies over typed adversaries satisfying `IsPPT`. Reductions prove `IsPPT` for the adversaries they build.

## Check a module

To check a module, run the experiment readability check on its area from the repository root:

```bash
python3 scripts/check_experiment_readability.py --list CslibFrontier/Crypto/Computational/DiffieHellman
```

It reads only the sources, needs no build and always succeeds. It prints the number of findings per category, then each one as `path:line: declaration: category` with the counted text:

- `encoding`: a word codec in an experiment or reduction body;
- `eval`: a `ProbComp.eval` in a body, except one that evaluates a fixed experiment;
- `chain`: a positional projection chain;
- `word_adversary`: `List Bool` or `WordOracleComp` in an adversary type.

A module that follows the steps above has no findings. To remove one, move the encoding into the adversary's efficiency predicate, or split the body into a fixed experiment and a family game.

Statements about the experiment write its probability as `Pr[e]`, or through `Experiment.succProbability` and `Experiment.advantage`, and programs sample with `$ᵗ α` ([conventions](../workflows/probabilistic-workflows.md#state-a-probability-and-sample-uniformly)). The probability idiom check lists what remains in an area:

```bash
python3 scripts/check_probability_idioms.py --list CslibFrontier/Crypto/Computational/DiffieHellman
```

Its categories are `eval_statement`, a `ProbComp.eval … true` or `succProbability (ProbComp.eval …)` in a public theorem statement, and `uniform_call`, a `ProbComp.uniform` in a definition body. Mass facts named `eval_…` or `bind_apply_…`, which other `PMF` proofs use, do not count.

Without `--list`, each check compares the modules your branch changes with its baseline (`scripts/experiment_readability_baseline.json`, `scripts/probability_idioms_baseline.json`), as CI does on pull requests. When a count falls, it prints the command that lowers the entry. When one rises, it fails and lists the findings. The experiment check recognizes experiments by their type and name, so a renamed or newly named experiment can change its counts; the scripts' docstrings give the exact conventions, and [Diagnose a readability ratchet failure](../workflows/troubleshooting.md#diagnose-a-readability-ratchet-failure) explains failures. The checks are syntactic. They do not find setup plumbing, duplicate experiments or weakened statements: reviewers check those against the rules.

[bs23]: ../sources.md#bs23
