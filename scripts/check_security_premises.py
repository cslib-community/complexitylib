#!/usr/bin/env python3
"""Keep security theorems from assuming what they should prove (#5293).

Usage: python3 scripts/check_security_premises.py [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline] [--no-build-check] [--baseline FILE]

This checks the rule "Security theorems" in AGENTS.md. A security theorem may assume named
hardness assumptions, stated relative to the setup sampler or component they concern, that the
adversary is in the admitted class, and properties of components that the cited result takes as
given. It must not assume anything about an object that its proof constructs, whether from the
adversary or not (a reduction, distinguisher, simulator, extractor or hybrid): its advantage or
success, its membership in an adversary class, or its efficiency.

`scripts/SecurityPremises.lean` reads the built `.olean` files of the library, so it sees
elaborated statements. A *flagged premise* of a public theorem under `CslibFrontier/Crypto` or in
the namespace `Cslib.Crypto` is a hypothesis whose claim is `Negligible …`, an advantage or
success-probability inequality, a membership `… ∈ 𝒟` or abstract admissibility `Admissible …`,
an `IsPPT…`/`IsOraclePPT…` predicate or an `…Indistinguishable…` predicate, directly or after
unfolding a predicate of the library applied to it, and whose subject mentions a *constructed
object*: a definition of the Crypto tree that is a reduction, distinguisher, adversary, simulator,
extractor, key generator, scheme or similar program, or a distribution or game applied to an
adversary or scheme structure, as opposed to a game, experiment, advantage, ideal law, predicate
or encoding. Bound variables (the input adversary, generic components) never count. The checker
also flags a conclusion `∃ x, … Adv ≤ … Adv(B … x …)` whose bound holds only for some
existentially chosen parameters `x` of a constructed reduction `B`, since the reduction then is
not uniform. And it flags a *realization*: an equation saying that a variable that another premise
makes efficient or admissible (`hD : IsOraclePPT encBool D`) computes a constructed object applied
to another variable (`hreal : eval (prfRealGame family D n) = … nonceFnDistinguisher … (forger
n)`, from the Carter–Wegman theorems that #5347 deleted), so that the theorem takes the reduction
from the caller. The Lean file's docstring gives the exact rules and the known gaps.

`scripts/security_premises_baseline.json` records the flagged theorems that are allowed, one per
line, as `{theorem: {"module": source path, "premises": [binder names], "why": justification}}`.
The conclusion counts as the premise `⊢`, and a premise without an accessible name, such as one
written with an arrow, as `#i` for the theorem's `i`-th binder. An entry is a deliberately
conditional lemma, named and documented as such (an *algebraic helper*, such as a concrete bound
in terms of `Adv(B_A)` that an asymptotic theorem consumes together with `B_A`'s efficiency proof),
a premise that the rule allows but the checker cannot tell apart (a named assumption about a
component the scheme uses, such as circular security or collision resistance of its hash, or the
hypothesis of a cited generic theorem), or a misformalization being fixed under #5293. Every entry
needs a one-line justification.

In a module that the change touches (adds, modifies or deletes, against the merge base of
`--base`, default `origin/main`, and the working tree, as `scripts/check_changed_files.py`
computes it), a flagged premise without an entry fails, and so does an entry that no longer
matches a flagged premise, until the baseline drops it in the same change: the baseline only
shrinks unless a change adds an entry on purpose. A change that adds or modifies the checker or
the baseline enforces every module. Differences in other modules are printed as a notice but do
not fail: a change can cause them without touching those modules, for example by changing a
definition that a flagged premise unfolds. Pull requests run this mode. `--all` enforces every
module. `--report` prints every difference and always succeeds; merge groups and pushes to `main`
run it, so that a queued pull request is never ejected by a change elsewhere. `--list [PREFIX]`
ignores the baseline and prints every flagged theorem in the modules under the path PREFIX.
`--update-baseline` adds entries with an empty justification for the unrecorded flagged premises
of the enforced modules and removes their stale entries; fill in each `why`, or the check fails.

This is a post-build check: it needs the outputs of `lake build CslibFrontier`, and refuses stale
ones unless `--no-build-check` is given.

The check supplements review: a clean run is not evidence that a security theorem is right. It
does not judge vacuous or misdefined notions, games and assumptions; a wrong or nonstandard
assumption (such as an MLWE variant without the short secrets that ML-KEM's security needs);
anything outside `Cslib.Crypto`; or names and docstrings that overclaim. Its rules are syntactic
over elaborated terms, so some premises escape them: one that hides the constructed object in its
own definition body, a distribution applied only to numbers or functions, a bound without an
advantage-named constant, a caller-supplied object whose existence is what the theorem should
prove, and a realization stated other than as an equation.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import lean_outputs as lo  # noqa: E402

BASELINE = ROOT / "scripts/security_premises_baseline.json"
TOOL = "scripts/SecurityPremises.lean"
# A change to the checker or its baseline enforces every module, so that its own CI run sees
# whether the whole library still matches.
CHECKER_FILES = frozenset({TOOL, "scripts/check_security_premises.py",
                           "scripts/security_premises_baseline.json"})
UPDATE = "python3 scripts/check_security_premises.py --update-baseline"
RULE = "AGENTS.md, Security theorems"
CONCLUSION = "⊢"


@dataclass(frozen=True)
class Hit:
    """A flagged theorem: its name, module path and line, and its flagged premises as
    `binder -> (kinds, constructed constants)`."""
    name: str
    path: str
    line: int
    premises: dict[str, tuple[tuple[str, ...], tuple[str, ...]]]


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def library_modules(root: Path) -> list[str]:
    """Every module of the library, from its sources."""
    return sorted(".".join(p.relative_to(root).with_suffix("").parts)
                  for p in (root / "CslibFrontier").rglob("*.lean"))


def parse(output: str) -> tuple[dict[str, Hit], dict]:
    """The hits and the summary line of `scripts/SecurityPremises.lean`'s output."""
    hits, summary = {}, {}
    for line in output.splitlines():
        row = json.loads(line)
        if "n" not in row:
            summary = row
            continue
        premises = {}
        for h in row["h"]:
            kinds, consts = premises.get(h["b"], ((), ()))
            premises[h["b"]] = (tuple(dict.fromkeys(kinds + tuple(h["k"]))),
                                tuple(dict.fromkeys(consts + tuple(h["c"]))))
        hits[row["n"]] = Hit(row["n"], module_path(row["m"]), row["l"], premises)
    return hits, summary


def scan(root: Path, build_dir: Path) -> dict[str, Hit]:
    """Run the Lean reader over every library module."""
    modules = library_modules(root)
    out = subprocess.run(["lake", "env", "lean", "--run", TOOL, str(build_dir)], cwd=root,
                         input="\n".join(modules) + "\n", capture_output=True, text=True)
    if out.returncode:
        sys.exit(f"{TOOL} failed:\n{out.stderr or out.stdout}")
    hits, summary = parse(out.stdout)
    if summary.get("missing"):
        sys.exit(f"build outputs are missing for {len(summary['missing'])} module(s), e.g. "
                 f"{summary['missing'][0]}; run `lake build CslibFrontier` first")
    return hits


def load_baseline(path: Path) -> dict[str, dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    ok = isinstance(data, dict) and all(
        isinstance(v, dict) and set(v) == {"module", "premises", "why"}
        and isinstance(v["module"], str) and isinstance(v["why"], str)
        and isinstance(v["premises"], list) and all(isinstance(p, str) for p in v["premises"])
        for v in data.values())
    if not ok:
        sys.exit(f"{path}: expected a JSON object from theorem names to "
                 '{"module": path, "premises": [binders], "why": justification}')
    return data


def baseline_text(entries: dict[str, dict]) -> str:
    """One entry per line, grouped by module, so concurrent edits rarely touch the same lines."""
    order = sorted(entries, key=lambda n: (entries[n]["module"], n))
    lines = [f" {json.dumps(n, ensure_ascii=False)}: "
             + json.dumps({"module": entries[n]["module"],
                           "premises": sorted(entries[n]["premises"]),
                           "why": entries[n]["why"]}, ensure_ascii=False)
             for n in order]
    return "{\n" + ",\n".join(lines) + ("\n" if lines else "") + "}\n"


@dataclass(frozen=True)
class Problems:
    """Differences from the baseline: unrecorded flagged premises as `(hit, binders)`, entries
    that no longer match as `(theorem, entry, stale binders)`, and entries without a
    justification."""
    new: list[tuple[Hit, list[str]]]
    stale: list[tuple[str, dict, list[str]]]
    unjustified: list[str]

    def __bool__(self) -> bool:
        return bool(self.new or self.stale or self.unjustified)


def compare(hits: dict[str, Hit], baseline: dict[str, dict], paths: set[str] | None) -> Problems:
    """The differences in the modules `paths` (every module when `None`)."""
    def scoped(path: str) -> bool:
        return paths is None or path in paths
    new, stale, unjustified = [], [], []
    for name, hit in sorted(hits.items(), key=lambda i: (i[1].path, i[1].line, i[0])):
        if not scoped(hit.path):
            continue
        recorded = set(baseline.get(name, {}).get("premises", ()))
        missing = [b for b in hit.premises if b not in recorded]
        if missing:
            new.append((hit, missing))
    for name, entry in sorted(baseline.items(), key=lambda i: (i[1]["module"], i[0])):
        hit = hits.get(name)
        if not (scoped(entry["module"]) or (hit and scoped(hit.path))):
            continue
        gone = [b for b in entry["premises"] if not hit or b not in hit.premises]
        if gone or (hit and hit.path != entry["module"]):
            stale.append((name, entry, gone))
        if not entry["why"].strip():
            unjustified.append(name)
    return Problems(new, stale, unjustified)


def outside(everywhere: Problems, here: Problems) -> Problems:
    """The differences of `everywhere` that are not in `here`."""
    return Problems([p for p in everywhere.new if p not in here.new],
                    [p for p in everywhere.stale if p not in here.stale],
                    [p for p in everywhere.unjustified if p not in here.unjustified])


def checker_changed(root: Path, ref: str) -> bool:
    """Whether the change adds or modifies the checker or its baseline."""
    added, modified = cer.ccf.changed_files(root, ref)
    return bool(CHECKER_FILES.intersection(added + modified))


def describe(hit: Hit, binders: list[str]) -> list[str]:
    out = [f"  {hit.path}:{hit.line}: {hit.name}"]
    for b in binders:
        kinds, consts = hit.premises[b]
        what = "conclusion" if b == CONCLUSION else f"premise {b}"
        out.append(f"    {what}: {', '.join(kinds)} about {', '.join(f'`{c}`' for c in consts)}")
    return out


def report(problems: Problems) -> str:
    out = []
    if problems.new:
        out += ["Security theorems may not assume anything about an object that their proof "
                f"constructs, from the adversary or not ({RULE}). Prove the premise instead: "
                "certify the "
                "reduction with an efficiency witness (`isPPT_…`, `isOraclePPT_…` or a "
                "circuit-size bound) and apply the named hardness assumption to it. "
                "A deliberately conditional lemma (an algebraic helper, such as a bound in terms "
                "of `Adv(B_A)`) must say so in its name and docstring and needs a baseline entry "
                f"with a justification (`{UPDATE}`, then fill in `why`).", ""]
        for hit, binders in problems.new:
            out += describe(hit, binders)
    if problems.stale:
        out += ([""] if out else []) + [
            "Baseline entries that no longer match a flagged premise; remove or update them in "
            f"the same change (`{UPDATE}`):"]
        for name, entry, gone in problems.stale:
            detail = f" (no longer flagged: {', '.join(gone)})" if gone else " (module moved)"
            out.append(f"  {entry['module']}: {name}{detail}")
    if problems.unjustified:
        out += ([""] if out else []) + ["Baseline entries without a justification (`why`):"]
        out += [f"  {name}" for name in problems.unjustified]
    return "\n".join(out)


def listing(hits: dict[str, Hit], prefix: str) -> str:
    chosen = sorted((h for h in hits.values() if h.path.startswith(prefix)),
                    key=lambda h: (h.path, h.line, h.name))
    out = [line for hit in chosen for line in describe(hit, list(hit.premises))]
    return "\n".join(out + [f"{len(chosen)} flagged theorem(s)"])


def update(hits: dict[str, Hit], baseline: dict[str, dict], paths: set[str] | None
           ) -> dict[str, dict]:
    """The baseline with the entries of the modules `paths` (all when `None`) matching `hits`:
    existing justifications are kept, new entries get an empty one."""
    def scoped(path: str) -> bool:
        return paths is None or path in paths
    updated = {name: entry for name, entry in baseline.items()
               if not (scoped(entry["module"]) or (name in hits and scoped(hits[name].path)))}
    for name, hit in hits.items():
        if scoped(hit.path):
            old = baseline.get(name, {})
            updated[name] = {"module": hit.path, "premises": sorted(hit.premises),
                             "why": old.get("why", "")}
    return updated


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="enforce in the modules changed since the merge base with this "
                            "revision (default origin/main)")
    scope.add_argument("--all", action="store_true", help="enforce in every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help="ignore the baseline and list every flagged theorem in the modules "
                            "under the path PREFIX; always succeeds")
    parser.add_argument("--update-baseline", action="store_true",
                        help="record the flagged premises of the enforced modules")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)
    if (args.report or args.list is not None) and args.update_baseline:
        parser.error("--report and --list do not combine with --update-baseline")
    if not args.no_build_check and not lo.lake_outputs_current(("CslibFrontier",)):
        sys.exit("build outputs are missing or stale; run `lake build CslibFrontier` "
                 "(or pass --no-build-check)")
    hits = scan(ROOT, lo.DEFAULT_BUILD_DIR)
    if args.list is not None:
        print(listing(hits, args.list))
        return 0
    baseline = load_baseline(args.baseline) if args.baseline.exists() else {}
    whole = args.all or args.report
    if not whole and checker_changed(ROOT, args.base):
        whole = True
        print("This change edits the security-premise checker or its baseline, so every module "
              "is enforced.")
    paths = None if whole else cer.touched_modules(ROOT, args.base)
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    if args.update_baseline:
        updated = update(hits, baseline, paths)
        args.baseline.write_text(baseline_text(updated), encoding="utf-8")
        empty = sorted(n for n, e in updated.items() if not e["why"].strip())
        print(f"Wrote {args.baseline} for {scope_text}."
              + (f" Fill in `why` for: {', '.join(empty)}." if empty else ""))
        return 0
    problems = compare(hits, baseline, paths)
    status = (f"{len(hits)} flagged theorem(s), {len(baseline)} baseline entries, "
              f"checking {scope_text}")
    if args.report:
        if problems:
            print(report(problems) + "\n")
        print(f"{status}; report only, nothing is enforced.")
        return 0
    elsewhere = outside(compare(hits, baseline, None), problems) if paths is not None else None
    if elsewhere:
        print("Not enforced: differences from the baseline in modules this change does not touch. "
              "They fail the next change to those modules. A change can cause them without "
              "touching those modules, for example by changing a definition that a flagged "
              "premise unfolds; if this one did, fix them here.\n\n" + report(elsewhere) + "\n")
        if os.environ.get("GITHUB_ACTIONS") == "true":
            count = len(elsewhere.new) + len(elsewhere.stale) + len(elsewhere.unjustified)
            print(f"::notice title=Security premises::{count} difference(s) from the baseline in "
                  "modules this change does not touch; see the step log.")
    if problems:
        print(report(problems), file=sys.stderr)
        return 1
    print(f"{status}; every flagged premise is recorded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
