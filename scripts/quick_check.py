#!/usr/bin/env python3
"""Conservative affected-client checks; never a replacement for the full check."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


class FullCheck(Exception):
    """The change cannot safely use the bounded quick-check path."""


ENCODING_RATCHET = (
    "encoding readability ratchet",
    [sys.executable, "-B", "scripts/check_encoding_readability.py", "--base", "{base}"])
PROJECTION_RATCHET = (
    "projection chain ratchet",
    [sys.executable, "-B", "scripts/check_projection_chains.py", "--base", "{base}"])
# The per-module ratchets of `ci-checks`, which read only the library sources.
RATCHETS = (ENCODING_RATCHET, PROJECTION_RATCHET)

# Data files that no Lean gate reads, each with the source-only check that does read it. A change
# to one runs that check (with `{base}`, the merge base) instead of falling back to the full check.
# Any other non-Lean change, including every Python change under `scripts/`, still falls back.
DATA_CHECKS = {
    # Each is read only by its ratchet, which needs no build
    # (`.github/workflows/lean_action_ci.yml`).
    "scripts/encoding_readability_baseline.json": ENCODING_RATCHET,
    "scripts/projection_chains_baseline.json": PROJECTION_RATCHET,
}

# The source-only `ci-checks` steps, scoped to the changed Lean files: source hygiene reads the
# files under these roots (its default selection), the ratchets the modules under `RATCHET_ROOT`.
# Each takes seconds; the post-build audits need whole-library outputs that quick mode does not
# build, so they stay in the full check.
HYGIENE_ROOTS = ("CslibFrontier/", "CslibFrontierTests/")
RATCHET_ROOT = "CslibFrontier/"


# `lake lint` runs this driver; quick mode passes it flags that only Batteries' runLinter accepts.
LINT_DRIVER = "batteries/runLinter"


@dataclass
class Plan:
    base: str
    targets: list[str]
    checks: list[tuple[str, list[str]]] = field(default_factory=list)  # (label, command)
    lint: dict[str, list[str]] = field(default_factory=dict)  # lint target -> modules it checks
    restore_files: list[str] = field(default_factory=list)  # affected source paths, not target names
    restore_built: list[str] = field(default_factory=list)  # built aggregates and executable helpers


@dataclass
class Executable:
    path: str
    source: Path
    target: str


def git(root: Path, *args: str) -> str:
    result = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)
    if result.returncode or "ambiguous" in result.stderr.lower():
        raise FullCheck(f"Git cannot resolve {args[0]} safely: {result.stderr.strip()}")
    return result.stdout


def imports_from_lean(root: Path, paths: list[str]) -> dict[str, list[str]]:
    helper = Path(__file__).with_name("QuickImports.lean")
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(helper)], cwd=root,
        input=json.dumps(paths), capture_output=True, text=True,
    )
    if result.returncode:
        raise FullCheck(f"native Lean header parser failed: {result.stderr.strip()}")
    try:
        rows = json.loads(result.stdout)
        parsed = {row["path"]: row["imports"] for row in rows}
        if len(rows) != len(paths) or set(parsed) != set(paths):
            raise ValueError("incomplete or duplicate header results")
        if any(not isinstance(xs, list) or any(not isinstance(x, str) for x in xs)
               for xs in parsed.values()):
            raise ValueError("invalid import names")
        return parsed
    except (ValueError, TypeError, KeyError) as error:
        raise FullCheck(f"invalid native header-parser response: {error}") from error


def source_modules(root: Path) -> tuple[dict[str, str], set[str], set[str]]:
    if (root / "lakefile.lean").exists():
        raise FullCheck("dynamic Lake configuration is outside quick-check scope")
    try:
        config = tomllib.loads((root / "lakefile.toml").read_text())
    except (OSError, ValueError) as error:
        raise FullCheck(f"cannot read Lake configuration: {error}") from error
    if config.get("srcDir", ".") != ".":
        raise FullCheck("package source directory is outside quick-check scope")
    libraries = config.get("lean_lib", [])
    if not isinstance(libraries, list) or not libraries:
        raise FullCheck("no Lake libraries were discovered")
    modules: dict[str, str] = {}
    physical_sources: set[Path] = set()
    aggregates: set[str] = set()
    roots: set[str] = set()
    allowed = {"name", "srcDir", "leanOptions", "allowNonModules", "roots", "globs"}
    for library in libraries:
        if not isinstance(library, dict) or set(library) - allowed:
            raise FullCheck("custom Lake library options need full checks")
        name = library.get("name", "")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", name):
            raise FullCheck("unsupported library name")
        source = root / library.get("srcDir", ".")
        if source.is_symlink() or not source.resolve().is_relative_to(root.resolve()):
            raise FullCheck("library source directory escapes the checkout")
        relative = Path(*name.split("."))
        aggregator = source / relative.with_suffix(".lean")
        directory = source / relative
        # The one supported glob layout: no roots and exactly the library's own submodules
        # (`roots = []`, `globs = ["Name.+"]`), which Lake builds without an aggregator file.
        globbed = "roots" in library or "globs" in library
        if globbed and (library.get("roots") != [] or library.get("globs") != [f"{name}.+"]):
            raise FullCheck("custom Lake library roots/globs need full checks")
        if globbed and aggregator.exists():
            raise FullCheck(f"glob library {name} also has an aggregator file")
        if (not globbed and not aggregator.is_file()) or not directory.is_dir():
            raise FullCheck(f"missing library root {name}")
        # rglob does not descend through directory symlinks: reject them explicitly,
        # including the library root, before trusting the discovered import graph.
        if directory.is_symlink() or any(path.is_symlink() for path in directory.rglob("*")):
            raise FullCheck("symlinked source directories/files need full checks")
        roots.add(name)
        if not globbed:
            aggregates.add(name)
        for path in [*([] if globbed else [aggregator]), *sorted(directory.rglob("*.lean"))]:
            if path.is_symlink() or not path.resolve().is_relative_to(source.resolve()):
                raise FullCheck("symlinked source file is outside quick-check scope")
            parts = path.relative_to(source).with_suffix("").parts
            if any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in parts):
                raise FullCheck("unsupported source module path")
            module = ".".join(parts)
            if module in modules:
                raise FullCheck(f"ambiguous local module {module}")
            if path.resolve() in physical_sources:
                raise FullCheck("overlapping library source paths need full checks")
            physical_sources.add(path.resolve())
            modules[module] = path.relative_to(root).as_posix()
    return modules, aggregates, roots


def executable_sources(root: Path) -> list[Executable]:
    """Executable roots and their source directories, for detecting omitted clients.

    Executables importing local modules must be built explicitly: the default build may omit
    them. The project's validation tools only import dependencies and need no additional build.
    """
    config = tomllib.loads((root / "lakefile.toml").read_text())
    executables = config.get("lean_exe", [])
    if not isinstance(executables, list):
        raise FullCheck("invalid executable configuration")
    sources: list[Executable] = []
    for executable in executables:
        if not isinstance(executable, dict):
            raise FullCheck("invalid executable configuration")
        target = executable.get("name", "")
        if not isinstance(target, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9-]*", target):
            raise FullCheck("unsupported executable name")
        name = executable.get("root", target)
        if not isinstance(name, str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", name):
            raise FullCheck("unsupported executable root")
        source = root / executable.get("srcDir", ".")
        path = source / Path(*name.split(".")).with_suffix(".lean")
        if (source.is_symlink() or path.is_symlink() or not path.is_file()
                or not path.resolve().is_relative_to(root.resolve())):
            raise FullCheck("missing or symlinked executable source")
        sources.append(Executable(path.resolve().relative_to(root.resolve()).as_posix(),
                                  source.resolve(), f"@/{target}"))
    return sources


def lint_scope(root: Path, aggregates: set[str], affected: set[str],
               reverse: dict[str, set[str]]) -> dict[str, list[str]]:
    """The fewest modules to lint the affected modules through, each with the modules it checks.

    `lake lint` runs the linters on the modules of the default-target libraries. A change can make
    an argument of an importing client unused, so every affected module of those libraries is
    listed, not only the changed ones. Linting a module covers the declarations of its package
    (first name component) throughout its import closure; a module with no affected importer in
    its own package is therefore linted directly, and covers every listed module it imports. Each
    listed module is assigned to one such target above it, so no declaration is linted twice.
    """
    config = tomllib.loads((root / "lakefile.toml").read_text())
    driver = config.get("lintDriver")
    if driver is None:
        return {}  # No lint gate is configured.
    if driver != LINT_DRIVER:
        raise FullCheck(f"lint driver {driver!r} is outside quick-check scope")
    defaults = config.get("defaultTargets", [])
    if not isinstance(defaults, list) or any(not isinstance(name, str) for name in defaults):
        raise FullCheck("invalid default targets")
    listed = {module for module in affected - aggregates
              if any(module.startswith(name + ".") for name in defaults)}
    package = lambda module: module.split(".")[0]
    above = {module: {consumer for consumer in reverse[module]
                      if consumer in listed and package(consumer) == package(module)}
             for module in listed}
    lint: dict[str, list[str]] = {module: [] for module in listed if not above[module]}
    for module in sorted(listed):
        # Every listed importer chain in the package ends at a target, which imports `module`.
        reached, queue = {module}, deque([module])
        while queue:
            for consumer in above[queue.popleft()] - reached:
                reached.add(consumer)
                queue.append(consumer)
        lint[min(reached & lint.keys())].append(module)
    return dict(sorted(lint.items()))


def make_plan(root: Path, base_ref: str = "origin/main", parser=None) -> Plan:
    if git(root, "ls-files", "--unmerged", "-z"):
        raise FullCheck("unresolved merge entries")
    reference = git(root, "rev-parse", "--verify", "--end-of-options", f"{base_ref}^{{commit}}").strip()
    bases = git(root, "merge-base", "--all", reference, "HEAD").splitlines()
    if len(bases) != 1:
        raise FullCheck("comparison needs exactly one merge base")
    base = bases[0]
    fields = git(root, "diff", "--no-ext-diff", "--no-renames", "--name-status", "-z", base, "--").split("\0")
    fields = fields[:-1] if fields[-1] == "" else fields
    if len(fields) % 2:
        raise FullCheck("unexpected Git change-list format")
    changes = list(zip(fields[::2], fields[1::2]))
    changes += [("A", p) for p in git(root, "ls-files", "--others", "--exclude-standard", "-z").split("\0") if p]
    for status, path in changes:
        if status not in {"A", "M"}:
            raise FullCheck(f"deleted, renamed or unusual change: {path}")
        if not path.endswith(".lean") and path not in DATA_CHECKS:
            raise FullCheck(f"non-Lean change: {path}")
    checks = [(label, [base if part == "{base}" else part for part in command])
              for path, (label, command) in DATA_CHECKS.items() if path in {p for _, p in changes}]
    changes = [(status, path) for status, path in changes if path not in DATA_CHECKS]
    hygiene = sorted(path for _, path in changes if path.startswith(HYGIENE_ROOTS))
    if hygiene:
        checks.insert(0, ("source hygiene (changed files)",
                          [sys.executable, "-B", "scripts/check_hygiene.py", "--check-simp",
                           "--", *hygiene]))
    if any(path.startswith(RATCHET_ROOT) for _, path in changes):
        for label, command in RATCHETS:
            ratchet = (label, [base if part == "{base}" else part for part in command])
            if ratchet not in checks:
                checks.append(ratchet)
    modules, aggregates, roots = source_modules(root)
    visible = set(git(root, "ls-files", "-z").split("\0")) | {p for _, p in changes}
    by_path = {path: module for module, path in modules.items()}
    if set(by_path) - visible:
        raise FullCheck("ignored local Lean source has no reliable Git change record")
    changed: set[str] = set()
    for _, path in changes:
        if path not in by_path:
            raise FullCheck(f"changed Lean source outside known libraries: {path}")
        # runLinter's `--only-modules` is unsound when a linter itself changes.
        if "env_linter" in (root / path).read_text(errors="replace"):
            raise FullCheck(f"changed source mentions a linter: {path}")
        changed.add(by_path[path])
    if changed & aggregates:
        raise FullCheck("a library import aggregate changed")
    executables = executable_sources(root)
    imports = (parser or imports_from_lean)(
        root, list(dict.fromkeys([*by_path, *(exe.path for exe in executables)])))
    executable_targets: set[str] = set()
    if changed:
        for exe in executables:
            # A helper outside the library graph may import a changed module indirectly.
            # Build its executable conservatively instead of silently omitting that client.
            if by_path.get(exe.path) in changed or any(
                    any(dependency == r or dependency.startswith(r + ".") for r in roots) or any(
                        (directory / Path(*dependency.split(".")).with_suffix(".lean")).exists()
                        for directory in (exe.source, root))
                    for dependency in imports[exe.path]):
                executable_targets.add(exe.target)
    reverse: dict[str, set[str]] = defaultdict(set)
    for path, dependencies in imports.items():
        if path not in by_path:
            continue
        consumer = by_path[path]
        for dependency in dependencies:
            if any(dependency == r or dependency.startswith(r + ".") for r in roots):
                if dependency not in modules:
                    raise FullCheck(f"missing local import {dependency} in {path}")
                reverse[dependency].add(consumer)
    affected = set(changed)
    queue = deque(sorted(changed))
    while queue:
        for consumer in sorted(reverse[queue.popleft()]):
            if consumer not in affected:
                affected.add(consumer)
                queue.append(consumer)
    # Traverse aggregates above: a real client importing one must never disappear from the plan.
    selected_executables = [exe for exe in executables if exe.target in executable_targets]
    # An aggregate may warn on an import even when its importing client elaborates silently.
    # Audit aggregates on built clients' import paths, not every root aggregate touched by the
    # change. Executable helpers are outside this graph; include their built aggregates
    # conservatively.
    needed = affected - aggregates
    queue = deque(sorted(needed))
    while queue:
        for dependency in imports[modules[queue.popleft()]]:
            if dependency in modules and dependency not in needed:
                needed.add(dependency)
                queue.append(dependency)
    aggregate_checks = affected & aggregates & needed
    if selected_executables:
        aggregate_checks |= affected & aggregates
    return Plan(base, sorted((affected - aggregates) | executable_targets), checks,
                lint_scope(root, aggregates, affected, reverse),
                sorted({modules[module] for module in affected - aggregates}
                       | {exe.path for exe in selected_executables}),
                sorted({modules[module] for module in aggregate_checks}
                       | {exe.source.relative_to(root.resolve()).as_posix()
                          for exe in selected_executables}))


def run_check(root: Path, command: list[str], label: str) -> int:
    with tempfile.NamedTemporaryFile(prefix="cslib-frontier-quick-", suffix=".log", delete=False) as log:
        path = Path(log.name)
        try:
            result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        except OSError as error:
            print(f"FAIL  {label}: {error}", file=sys.stderr)
            path.unlink(missing_ok=True)
            return 1
    if result.returncode:
        print(f"FAIL  {label}\n" + "\n".join(path.read_text(errors="replace").splitlines()[-60:]), flush=True)
        print(f"Full log: {path}", flush=True)
    else:
        print(f"ok    {label}", flush=True)
        path.unlink()
    return result.returncode


def main(argv: list[str] | None = None, root: Path | None = None) -> int:
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--base", default="origin/main", help="comparison ref; use its merge base with HEAD")
    options = args.parse_args(argv)
    root = root or Path(__file__).resolve().parent.parent
    try:
        plan = make_plan(root, options.base)
    except (FullCheck, OSError, ValueError, TypeError) as error:
        print(f"Quick check falls back to the full check: {error}", flush=True)
        return subprocess.run([str(root / "scripts/check.sh"), "--base", options.base],
                              cwd=root).returncode
    print(f"Quick check against merge base {plan.base}; {len(plan.targets)} affected build targets.",
          flush=True)
    print("This is not full validation: lint covers only the affected library modules, and the "
          "test, style, init-import gates and post-build audits are skipped.", flush=True)
    for label, command in plan.checks:
        status = run_check(root, command, label)
        if status:
            return status
    if not plan.targets:
        print("No Lean source changes; checking import aggregates only.", flush=True)
    for offset in range(0, len(plan.targets), 100):
        batch = plan.targets[offset:offset + 100]
        shown = ", ".join(batch[:10])
        if len(batch) > 10:
            shown += f", ... ({len(batch) - 10} more in this batch)"
        print("Targets: " + shown, flush=True)
        status = run_check(root, ["lake", "build", "--wfail", "--iofail", *batch], "affected modules and clients")
        if status:
            return status
    if plan.targets:
        # Restored outputs carry no warnings for `--wfail` to see (#4523).
        # JSON preserves whitespace in paths and avoids command-line limits for large closures.
        with tempfile.TemporaryDirectory(prefix="cslib-frontier-restores-") as directory:
            files = Path(directory) / "files.json"
            files.write_text(json.dumps(plan.restore_files))
            command = [sys.executable, "-B", "scripts/check_cache_restores.py", "--files-from", str(files)]
            for source in plan.restore_built:
                command.extend(["--built-under", source])
            status = run_check(root, command, "affected files restored from the artifact cache")
        if status:
            return status
    status = run_lint(root, plan)
    if status:
        return status
    return run_check(root, ["lake", "exe", "mk_all", "--check"], "mk_all --check")


def run_lint(root: Path, plan: Plan) -> int:
    """Lint the affected library modules, as `lake lint` would, after the build has made them.

    Each target gets its own runLinter process: one process importing several environments keeps
    each one's oleans in memory, growing by gigabytes per target. Every target runs, so one pass
    reports all failures; each module is checked through exactly one target.
    """
    if not plan.lint:
        return 0
    print(f"Linting {sum(map(len, plan.lint.values()))} affected library modules through "
          f"{len(plan.lint)} modules, one process each.", flush=True)
    failed = 0
    with tempfile.TemporaryDirectory(prefix="cslib-frontier-lint-") as directory:
        for index, (target, modules) in enumerate(plan.lint.items()):
            listing = Path(directory) / f"{index}.txt"
            listing.write_text("".join(module + "\n" for module in modules))
            status = run_check(root, ["lake", "lint", "--", "--no-build",
                                      f"--only-modules={listing}", target], f"lint {target}")
            failed = failed or status
    return failed


if __name__ == "__main__":
    sys.exit(main())
