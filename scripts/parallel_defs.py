#!/usr/bin/env python3
"""Advisory notice: new definitions that may restate an existing library notion.

Usage: python3 scripts/parallel_defs.py [--base REF | --decl NAME...] [--tiers SIZE:SHARE,...]
           [--max-shared N] [--same-module] [--limit N] [--github] [--no-build-check]

AGENTS.md asks for reuse of existing definitions rather than parallel notions: the same concept
defined again for another carrier type, or a copied verifier or game. This tool points authors and
reviewers at candidates. It examines the public `def`s, `abbrev`s, `structure`s, `class`es and
`inductive`s that a change adds or modifies: those of the `Complexity/` files changed since the
merge base of REF (default `origin/main`) whose code, from the declared name to its end, contains
an added or modified line or the place of a deleted one (an edit to a docstring alone does not
count). With `--decl`, it examines the named declarations instead, for audits and calibration.

`scripts/ParallelDefs.lean` compares each examined declaration with every definition and
inductive type of the built `Complexity` library (instances excluded, private declarations
included). It erases variables, universe levels and the types of `fun` and `let` binders, then
finds the largest subterm that both bodies share and that at most `--max-shared` declarations of
the library contain (default 4, so that common plumbing is ignored); an inductive type's body is
its constructors' types. Pairs where one body mentions the other, as a wrapper or specialization
does, are skipped. The tool reports

1. definitions that are only another library definition applied to their arguments, such as
   `abbrev MCSPAt s := GapMCSP.yesSet s`: a second name for an existing notion;
2. pairs whose shared subterm reaches one of the `--tiers`: with the default `200:0.3,120:0.6`, at
   least 200 nodes making up at least 30% of the smaller body, or at least 120 nodes making up at
   least 60% of it (a near copy).

Candidates within one module, which its author sees anyway, are left out unless `--same-module`.

The defaults were calibrated on `main` and on recent pull requests (the PR that added this tool
records the results): they flag `DecidesWithBoundedError` against `SolvesWithBoundedError` (#884
F7), `MCSPAt` against `GapMCSP.yesSet` (#1048) and the third MCSP certificate verifier (#1034).

A candidate is not a finding. If a pair states the same notion, reuse or generalize the existing
definition; otherwise the PR description says why it differs. The tool is advisory: it always
exits 0, and it skips itself, with a note, when the build outputs are missing or stale. With
`--github` it also writes the candidates to the job summary (`$GITHUB_STEP_SUMMARY`) and as notice
annotations on the examined declarations. It needs `lake build` (the `Complexity` library); CI
runs it after the build with `--no-build-check`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_changed_files as ccf  # noqa: E402

BUILD_DIR = ROOT / ".lake/build/lib/lean"
READER = ROOT / "scripts/ParallelDefs.lean"
HUNK = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", re.M)
# Constants left out of the summary of a shared subterm: instances, parent projections and
# constants too common to say what the subterm is about.
PLUMBING = re.compile(r"^(?:inst|Inst|to[A-Z])")
COMMON = {
    "Nat", "Int", "Bool", "List", "Fin", "Prod", "Option", "Set", "Eq", "Ne", "And", "Or", "Not",
    "Iff", "Exists", "True", "False", "ite", "dite", "id", "Function.comp", "OfNat.ofNat",
    "LE.le", "LT.lt", "GE.ge", "GT.gt", "HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HDiv.hDiv",
    "HMod.hMod", "HPow.hPow", "HSMul.hSMul", "Neg.neg", "Nat.cast", "Int.cast", "DFunLike.coe",
    "Membership.mem", "Prod.mk", "Prod.fst", "Prod.snd", "Fin.val", "Fin.mk", "Subtype.val",
    "Bool.true", "Bool.false",
}


@dataclass
class Finding:
    """A candidate: `name` examined, `other` an existing declaration (or the target of an alias,
    when `size` is 0)."""
    name: str
    path: str
    line: int
    other: str
    other_path: str
    other_line: int
    size: int = 0
    share: float = 0.0
    private: bool = False
    constants: tuple[str, ...] = ()

    def text(self) -> str:
        other = f"`{self.other}`" + (" (private)" if self.private else "")
        where = f"{self.other_path}:{self.other_line}"
        if not self.size:
            return (f"`{self.name}` is {other} ({where}) applied to its arguments: a second name "
                    "for an existing notion.")
        about = f", built from {', '.join(f'`{c}`' for c in self.constants)}" \
            if self.constants else ""
        return (f"`{self.name}` and {other} ({where}) share a {self.size}-node subterm, "
                f"{self.share:.0%} of the smaller body{about}.")


# --- What to examine ----------------------------------------------------------------------------

def module_of(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def path_of(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def added_ranges(diff: str) -> list[tuple[int, int]]:
    """The 1-based line ranges that a `git diff -U0` adds or modifies on its new side. A pure
    deletion (`+N,0`) contributes the lines `N` and `N + 1` around the place of the deleted text,
    so that a deletion inside a declaration marks that declaration."""
    ranges = []
    for start, count in HUNK.findall(diff):
        start, count = int(start), 1 if count == "" else int(count)
        ranges.append((start, start + count - 1) if count else (max(start, 1), start + 1))
    return ranges


def changed_ranges(root: Path, ref: str) -> dict[str, list[tuple[int, int]] | None]:
    """For each `Complexity/` source file a change adds (`None`: all of it) or modifies, the
    lines it adds or modifies, compared to the merge base of `ref` as in
    `scripts/check_changed_files.py`."""
    added, modified = ccf.changed_files(root, ref)
    base = ccf.comparison_base(root, ref)
    out: dict[str, list[tuple[int, int]] | None] = {}
    for rel in added + modified:
        if not (rel.startswith("Complexity/") and rel.endswith(".lean")):
            continue
        if rel in added:
            out[rel] = None
            continue
        diff = ccf.git(root, "diff", "--no-ext-diff", "--no-renames", "--no-color", "-U0", base,
                       "--", rel)
        ranges = added_ranges(diff.stdout)
        if ranges:
            out[rel] = ranges
    return out


def library_modules(root: Path) -> list[str]:
    return sorted(module_of(str(path.relative_to(root)))
                  for path in (root / "Complexity").rglob("*.lean"))


def requests(modules: list[str], changed: dict[str, list[tuple[int, int]] | None],
             decls: list[str]) -> str:
    """The standard input of `scripts/ParallelDefs.lean`."""
    lines = []
    for module in modules:
        rel = path_of(module)
        if rel not in changed:
            lines.append(f"env {module}")
        elif changed[rel] is None:
            lines.append(f"lines {module} *")
        else:
            spec = ",".join(f"{a}-{b}" for a, b in changed[rel])
            lines.append(f"lines {module} {spec}")
    lines += [f"decl {name}" for name in decls]
    return "\n".join(lines) + "\n"


# --- Running the reader and choosing what to report ---------------------------------------------

def run_reader(build_dir: Path, stdin: str, min_size: int, max_shared: int) -> list[dict]:
    """The reader's JSON rows. Other lines on its standard output, such as an elaboration message
    about `scripts/ParallelDefs.lean` itself after a toolchain update, are ignored."""
    out = subprocess.run(["lake", "env", "lean", "--run", str(READER), str(build_dir),
                          str(min_size), str(max_shared)],
                         cwd=ROOT, input=stdin, capture_output=True, text=True)
    if out.returncode:
        raise RuntimeError(f"scripts/ParallelDefs.lean failed: {out.stderr.strip()[-2000:]}")
    return [json.loads(line) for line in out.stdout.splitlines() if line.startswith("{")]


def parse_tiers(spec: str) -> list[tuple[int, float]]:
    """`200:0.3,120:0.6` as `[(200, 0.3), (120, 0.6)]`."""
    tiers = []
    for item in spec.split(","):
        size, _, share = item.partition(":")
        tiers.append((int(size), float(share or 0)))
    if not tiers or any(size < 1 or not 0 <= share <= 1 for size, share in tiers):
        raise ValueError(f"invalid tiers {spec!r}")
    return tiers


def select(rows: list[dict], tiers: list[tuple[int, float]], same_module: bool) -> list[Finding]:
    """The aliases, then the pairs that reach a tier, in the reader's order (largest first);
    without `same_module`, only those across modules."""
    found = [Finding(r["alias"], path_of(r["am"]), r["al"], r["b"], path_of(r["bm"]), r["bl"],
                     private=r["bp"])
             for r in rows if "alias" in r and (same_module or r["am"] != r["bm"])]
    for r in rows:
        if "pair" not in r or (r["am"] == r["bm"] and not same_module):
            continue
        share = r["pair"] / max(1, min(r["as"], r["bs"]))
        if not any(r["pair"] >= size and share >= least for size, least in tiers):
            continue
        constants = tuple(dict.fromkeys(
            c for c in r["c"]
            if c not in COMMON and not PLUMBING.match(c.rsplit(".", 1)[-1])))[:6]
        found.append(Finding(r["a"], path_of(r["am"]), r["al"], r["b"], path_of(r["bm"]),
                             r["bl"], r["pair"], share, r["bp"], constants))
    return found


# --- Reports ------------------------------------------------------------------------------------

ADVICE = ("These are candidates, not findings. If a pair states the same notion, reuse or "
          "generalize the existing definition instead of adding a parallel one; otherwise, say in "
          "the PR description why it differs (AGENTS.md, \"New statements and definitions\").")


def markdown(found: list[Finding], examined: int, limit: int) -> str:
    head = "### Parallel-definition notice (advisory)\n\n"
    if not found:
        return head + (f"No candidate parallel definitions among the {examined} examined "
                       "declarations.\n")
    shown = found[:limit]
    more = f" The first {limit} are listed." if len(found) > limit else ""
    lines = [head + f"{len(found)} candidate(s) among the {examined} examined declarations."
             f"{more} {ADVICE}\n"]
    lines += [f"- {f.path}:{f.line}: {f.text()}" for f in shown]
    return "\n".join(lines) + "\n"


def escape(text: str, prop: bool = False) -> str:
    """Escape a GitHub workflow command's message, or a property value when `prop`."""
    text = text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    return text.replace(":", "%3A").replace(",", "%2C") if prop else text


def annotations(found: list[Finding], limit: int) -> list[str]:
    return [f"::notice file={escape(f.path, True)},line={f.line},"
            f"title={escape('Possible parallel definition', True)}::"
            f"{escape(f.text() + ' Advisory only; see the job summary.')}"
            for f in found[:limit]]


# --- Driver -------------------------------------------------------------------------------------

def outputs_current() -> bool:
    return subprocess.run(["lake", "build", "--no-build", "Complexity"], cwd=ROOT,
                          capture_output=True).returncode == 0


def skip(reason: str, github: bool) -> int:
    message = f"Parallel-definition notice skipped: {reason}."
    print(message)
    if github and os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
            summary.write(f"### Parallel-definition notice (advisory)\n\n{message}\n")
    return 0


def run(args: argparse.Namespace, root: Path, build_dir: Path) -> int:
    changed = {} if args.decl else changed_ranges(root, args.base)
    if not changed and not args.decl:
        print("Parallel-definition notice: no `Complexity/` definitions added or modified.")
        return 0
    if not build_dir.is_dir():
        return skip(f"no build outputs in {build_dir}; run `lake build` first", args.github)
    unbuilt = [rel for rel in changed
               if not (build_dir / rel.removesuffix(".lean")).with_suffix(".olean").is_file()]
    if unbuilt:
        return skip(f"{len(unbuilt)} changed module(s) are not built, e.g. {unbuilt[0]}",
                    args.github)
    if not args.no_build_check and not outputs_current():
        return skip("the build outputs are stale; run `lake build` first", args.github)
    tiers = parse_tiers(args.tiers)
    rows = run_reader(build_dir, requests(library_modules(root), changed, args.decl),
                      min(size for size, _ in tiers), args.max_shared)
    stats = next((r for r in rows if "examined" in r), {"examined": 0, "missing": []})
    found = select(rows, tiers, args.same_module)
    report = markdown(found, stats["examined"], args.limit)
    print(report, end="")
    if stats["missing"]:
        print(f"note: {len(stats['missing'])} library module(s) have no build outputs and were "
              f"not compared, e.g. {stats['missing'][0]}.")
    if args.github:
        for line in annotations(found, args.limit):
            print(line)
        if os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
                summary.write(report)
    return 0


def main(argv: list[str] | None = None, root: Path = ROOT, build_dir: Path = BUILD_DIR) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", default="origin/main",
                        help="comparison ref; changes are taken from its merge base with HEAD")
    parser.add_argument("--decl", action="append", default=[], metavar="NAME",
                        help="examine this declaration instead of the changed ones (repeatable)")
    parser.add_argument("--tiers", default="200:0.3,120:0.6",
                        help="report a pair whose shared subterm has at least SIZE nodes and at "
                        "least SHARE of the smaller body, for some SIZE:SHARE (default "
                        "200:0.3,120:0.6)")
    parser.add_argument("--max-shared", type=int, default=4,
                        help="ignore subterms that more declarations contain (default 4)")
    parser.add_argument("--same-module", action="store_true",
                        help="also report pairs within one module")
    parser.add_argument("--limit", type=int, default=10, help="report at most this many")
    parser.add_argument("--github", action="store_true",
                        help="write the job summary and notice annotations")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    args = parser.parse_args(argv)
    try:
        return run(args, root, build_dir)
    except (Exception, SystemExit) as error:  # advisory: never fail the caller
        return skip(f"the tool failed ({error})", args.github)


if __name__ == "__main__":
    sys.exit(main())
