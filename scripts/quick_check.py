#!/usr/bin/env python3
"""Conservative affected-client checks; never a replacement for the six validation gates."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


class FullCheck(Exception):
    """The change cannot safely use the bounded quick-check path."""


@dataclass
class Plan:
    base: str
    targets: list[str]


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
        if not path.endswith(".lean"):
            raise FullCheck(f"non-Lean change: {path}")
    modules, aggregates, roots = source_modules(root)
    by_path = {path: module for module, path in modules.items()}
    visible = set(git(root, "ls-files", "-z").split("\0")) | {p for _, p in changes}
    if set(by_path) - visible:
        raise FullCheck("ignored local Lean source has no reliable Git change record")
    changed: set[str] = set()
    for _, path in changes:
        if path not in by_path:
            raise FullCheck(f"changed Lean source outside known libraries: {path}")
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
    return Plan(base, sorted((affected - aggregates) | executable_targets))


def run_check(root: Path, command: list[str], label: str) -> int:
    with tempfile.NamedTemporaryFile(prefix="complexitylib-quick-", suffix=".log", delete=False) as log:
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
        print(f"Quick check falls back to all six gates: {error}", flush=True)
        return subprocess.run([str(root / "scripts/check.sh")], cwd=root).returncode
    print(f"Quick check against merge base {plan.base}; {len(plan.targets)} affected build targets.",
          flush=True)
    print("This is not full validation: global test, lint, style and init-import gates are skipped.", flush=True)
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
    return run_check(root, ["lake", "exe", "mk_all", "--check"], "mk_all --check")


if __name__ == "__main__":
    sys.exit(main())
