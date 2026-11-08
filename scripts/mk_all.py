#!/usr/bin/env python3
"""Generate the import aggregators of the Lake libraries, sharded by directory.

Usage:
    python3 scripts/mk_all.py               regenerate every aggregator
    python3 scripts/mk_all.py --check       report missing, stale or extra aggregators
    python3 scripts/mk_all.py --aggregates  print the aggregator modules of the default targets

Each root `R` of a `lean_lib` in `lakefile.toml` has an aggregator `R.lean` beside the directory
`R/`. It imports the modules directly in `R/` and, for each subdirectory `R/D/` that contains
modules, the shard `R.All.D` at `R/All/D.lean`. The shard of a directory imports the modules
directly in it and the shards of its subdirectories, in the same way, so `import R` still imports
every module, and `import R.All.D` imports everything under `R/D/`. Each aggregator lists its
modules and subdirectories in name order, a subdirectory's shard where the subdirectory's name
falls (after a module of the same name). Expanding the shards in place therefore loads the modules
in the order of a single sorted list. Keeping a subdirectory beside its neighbours, instead of
collecting all shards at the top, also avoids a gap that new modules and new subdirectories would
both fill.

Sharding keeps concurrent pull requests apart. GitHub ignores the `merge=union` attribute that
`.gitattributes` sets for the aggregators, so two pull requests that add imports between the
same neighbours conflict on GitHub, although a local `git merge` reports no conflict. Adding a
module changes only the shard of its directory, and the parent directory's shard when the
directory is new.

`R/All/` is reserved for shards, so a shard never collides with a module: the shard of `R/D/E/`
is `R/All/D/E.lean`, while a module `R/D/E.lean` beside the directory, or `R/D/E/All.lean` inside
it, lives elsewhere. The generator refuses a module `R/All.lean`, and refuses to overwrite or
delete a file in `R/All/` that is not in the generated form. Shards carry the root's header
(`module`, the `shake` directive and `public import` for a module-style root, plain `import`
otherwise) and the upstream marker `local-only (project scaffolding)`, which
`scripts/check_hygiene.py` requires of every module under `Complexity/`.

`--check` exits with status 1 when an aggregator is missing or differs from the generated text,
when a file in a reserved shard directory is not a current shard, or when a module is not reached
from its library's root through the aggregators. `lake exe lint-style` lints the modules that the
given modules import directly, by default the imports of the root aggregators, which no longer
list every module. `--aggregates` prints the aggregators of the libraries in `defaultTargets`, so
that `lake exe lint-style $(python3 scripts/mk_all.py --aggregates)` lints every module of those
libraries. Exit status 2 reports an unusable layout: a module path that is not a plain Lean
identifier path, a file in a reserved directory that is not a shard, or an unreadable Lake
configuration.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]

# The reserved directory, under each library root, that holds that library's shards.
SHARD_DIR = "All"
# The header of a module-style aggregator, as Mathlib's `mk_all` writes it.
MODULE_HEADER = "module  -- shake: keep-all --deprecated_module: ignore\n"
SHARD_MARKER = "-- upstream: local-only (project scaffolding)\n"
# A module path component that an `import` line can name without escaping.
COMPONENT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
IMPORT = re.compile(r"(?:public )?import ([A-Za-z_][A-Za-z_0-9.]*)\Z")


class LayoutError(Exception):
    """The source tree or Lake configuration is outside what the generator supports."""


@dataclass(frozen=True)
class Library:
    """One library root: the module `name`, with its sources under `source`."""

    name: str
    source: Path

    @property
    def directory(self) -> Path:
        return self.source.joinpath(*self.name.split("."))

    @property
    def root_file(self) -> Path:
        return self.directory.with_suffix(".lean")

    @property
    def shard_directory(self) -> Path:
        return self.directory / SHARD_DIR

    def shard_file(self, directory: tuple[str, ...]) -> Path:
        """The aggregator of `directory`, given relative to the library directory."""
        if not directory:
            return self.root_file
        return self.shard_directory.joinpath(*directory).with_suffix(".lean")

    def shard_module(self, directory: tuple[str, ...]) -> str:
        return ".".join((self.name, SHARD_DIR, *directory)) if directory else self.name


def read_config(root: Path) -> dict:
    if (root / "lakefile.lean").exists() or not (root / "lakefile.toml").is_file():
        raise LayoutError("the generator needs lakefile.toml; lakefile.lean is unsupported")
    try:
        return tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise LayoutError(f"cannot read lakefile.toml: {error}") from error


def libraries(root: Path, names: set[str] | None = None) -> list[Library]:
    """The library roots that have aggregators: Lake's `roots`, by default the library name.
    A library with `roots = []` (built from `globs`) has none. With `names`, only the roots of
    the libraries with those names."""
    config = read_config(root)
    package_source = root / config.get("srcDir", ".")
    found = []
    for library in config.get("lean_lib", []):
        if names is not None and library.get("name") not in names:
            continue
        source = package_source / library.get("srcDir", ".")
        for name in library.get("roots", [library["name"]]):
            if not all(COMPONENT.fullmatch(part) for part in name.split(".")):
                raise LayoutError(f"unsupported library root name {name!r}")
            found.append(Library(name, source))
    return found


def default_libraries(root: Path) -> list[Library]:
    """The library roots of `defaultTargets`, which a bare `lake build` and `lint-style` use."""
    return libraries(root, set(read_config(root).get("defaultTargets", [])))


def module_paths(library: Library) -> list[tuple[str, ...]]:
    """Each module of the library outside its shard directory, relative to the library directory,
    without the `.lean` suffix."""
    modules = []
    reserved = library.shard_directory.with_suffix(".lean")
    if reserved.exists():
        raise LayoutError(f"{reserved}: the module name {library.name}.{SHARD_DIR} is reserved "
                          "for the shard directory beside it")
    if not library.directory.is_dir():
        return modules
    for path in library.directory.rglob("*.lean"):
        relative = path.relative_to(library.directory)
        if relative.parts[0] == SHARD_DIR:
            continue
        parts = relative.with_suffix("").parts
        if not all(COMPONENT.fullmatch(part) for part in parts):
            raise LayoutError(f"{path}: module path is not a plain Lean identifier path")
        modules.append(parts)
    return sorted(modules)


def uses_module_style(library: Library) -> bool:
    """Whether the aggregators use the module system: they follow the existing root's header,
    as Mathlib's `mk_all` does. A new root is module-style, like every library module here."""
    if not library.root_file.is_file():
        return True
    for line in library.root_file.read_text(encoding="utf-8").splitlines():
        if line.strip() and not line.lstrip().startswith("--"):
            return line.split()[0] == "module"
    return True


def render(imports: set[tuple[str, int, str]], module_style: bool, shard: bool) -> str:
    """An aggregator importing `imports`, given as (sort key, 0 for a module or 1 for a shard,
    module name)."""
    keyword = "public import " if module_style else "import "
    header = (MODULE_HEADER if module_style else "") + (SHARD_MARKER if shard else "")
    return (header + "\n" if header else "") + "".join(
        f"{keyword}{name}\n" for _, _, name in sorted(imports))


def generate(library: Library, modules: list[tuple[str, ...]] | None = None,
             module_style: bool | None = None) -> dict[Path, str]:
    """The aggregators of the library, by path: its root and one shard per directory that
    contains modules."""
    if modules is None:
        modules = module_paths(library)
    if module_style is None:
        module_style = uses_module_style(library)
    imports: dict[tuple[str, ...], set[tuple[str, int, str]]] = defaultdict(set)
    imports[()]  # an empty library still has a root aggregator
    for parts in modules:
        name = ".".join((library.name, *parts))
        directory = parts[:-1]
        imports[directory].add((name, 0, name))
        while directory:
            # A subdirectory sorts under its own name, as its modules would in a single list.
            key = ".".join((library.name, *directory))
            imports[directory[:-1]].add((key, 1, library.shard_module(directory)))
            directory = directory[:-1]
    return {library.shard_file(directory): render(names, module_style, bool(directory))
            for directory, names in imports.items()}


def is_generated(text: str) -> bool:
    """Whether `text` has the shape of a generated aggregator: headers and imports only."""
    return all(line in ("", MODULE_HEADER.rstrip("\n"), SHARD_MARKER.rstrip("\n"))
               or IMPORT.fullmatch(line) for line in text.splitlines())


def existing_shards(library: Library) -> list[Path]:
    """The files in the shard directory; refuse anything the generator would not have written."""
    if not library.shard_directory.is_dir():
        return []
    files = sorted(path for path in library.shard_directory.rglob("*") if not path.is_dir())
    foreign = [path for path in files if path.suffix != ".lean" or path.is_symlink()
               or not is_generated(path.read_text(encoding="utf-8"))]
    if foreign:
        raise LayoutError(f"{library.shard_directory} is reserved for generated shards, but "
                          f"contains other files: {', '.join(map(str, foreign))}")
    return files


def unreached(library: Library, modules: list[tuple[str, ...]]) -> list[str]:
    """The modules that the existing aggregators do not import, following shard imports from
    the root."""
    prefix = f"{library.name}.{SHARD_DIR}."
    reached: set[str] = set()
    pending = [library.root_file]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := IMPORT.fullmatch(line.strip()):
                name = match.group(1)
                if name.startswith(prefix):
                    pending.append(library.shard_file(tuple(name.removeprefix(prefix).split("."))))
                else:
                    reached.add(name)
    names = (".".join((library.name, *parts)) for parts in modules)
    return [name for name in names if name not in reached]


def display(path: Path, root: Path) -> str:
    return str(path.relative_to(root)) if path.is_relative_to(root) else str(path)


def check(root: Path) -> list[str]:
    """Every problem with the aggregators, as messages; empty when they are current."""
    problems = []
    for library in libraries(root):
        modules = module_paths(library)
        expected = generate(library, modules)
        for path, text in sorted(expected.items()):
            if not path.is_file():
                problems.append(f"{display(path, root)} is missing")
            elif path.read_text(encoding="utf-8") != text:
                problems.append(f"{display(path, root)} is out of date")
        for path in existing_shards(library):
            if path not in expected:
                problems.append(f"{display(path, root)} is not the shard of a directory with "
                                "modules")
        missing = unreached(library, modules)
        if missing:
            shown = ", ".join(missing[:10]) + (f" and {len(missing) - 10} more"
                                               if len(missing) > 10 else "")
            problems.append(f"{library.name}.lean does not import {shown}")
    return problems


def update(root: Path) -> list[str]:
    """Write every aggregator, remove obsolete shards, and describe the changes."""
    changes = []
    for library in libraries(root):
        expected = generate(library)
        obsolete = [path for path in existing_shards(library) if path not in expected]
        for path, text in sorted(expected.items()):
            if path.is_file() and path.read_text(encoding="utf-8") == text:
                continue
            changes.append(f"{'Updating' if path.is_file() else 'Creating'} "
                           f"{display(path, root)}")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        for path in obsolete:
            changes.append(f"Removing {display(path, root)}")
            path.unlink()
        if library.shard_directory.is_dir():
            # Deepest first, so that a directory emptied by removing its children goes too.
            for directory in sorted(library.shard_directory.rglob("*"), reverse=True):
                if directory.is_dir() and not any(directory.iterdir()):
                    directory.rmdir()
            if not any(library.shard_directory.iterdir()):
                library.shard_directory.rmdir()
    return changes


def aggregate_modules(root: Path) -> list[str]:
    """The aggregator modules of the default-target libraries."""
    names = []
    for library in default_libraries(root):
        for path in generate(library):
            directory = (() if path == library.root_file else
                         path.relative_to(library.shard_directory).with_suffix("").parts)
            names.append(library.shard_module(directory))
    return sorted(names)


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true",
                      help="exit 1 instead of writing when an aggregator is not current")
    mode.add_argument("--aggregates", action="store_true",
                      help="print the aggregator modules of the default targets, one per line")
    args = parser.parse_args(argv)
    try:
        if args.aggregates:
            print("\n".join(aggregate_modules(root)))
            return 0
        if args.check:
            problems = check(root)
            for problem in problems:
                print(problem)
            if problems:
                print("Run `python3 scripts/mk_all.py` to regenerate the aggregators.")
                return 1
            print("All aggregators are current.")
            return 0
        changes = update(root)
        print("\n".join(changes) if changes else "No update necessary")
        return 0
    except LayoutError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
