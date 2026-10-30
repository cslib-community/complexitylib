#!/usr/bin/env python3
"""Read the build outputs of the three libraries, and the sources they come from.

`lake build Complexity ComplexityTests ComplexityAbstracts` (`lake build` and `lake test`) writes
an `.ilean` file beside each `.olean`. It records every identifier that occurs in the module's
source, including in proofs, with the declarations the module defines. `scripts/LeanOutputs.lean`
reads the `.olean` parts for each constant's kind, export status, statement and declaration range.
This module loads both and refuses stale outputs. `scripts/check_tidy_surface.py`,
`scripts/check_tidy_usage.py`, `scripts/tidy_sweep.py`, `scripts/check_changed_files.py` and
`scripts/audit_queries.py` build on it.
"""

from __future__ import annotations

import filecmp
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from proof_lengths import masks  # noqa: E402

ROOTS = ("Complexity", "ComplexityTests", "ComplexityAbstracts")
# Libraries that Lake builds from a glob (`lakefile.toml`) have no root aggregator file: their
# modules are exactly the source files under their directory.
GLOB_ROOTS = ("ComplexityTests",)
DEFAULT_BUILD_DIR = ROOT / ".lake/build/lib/lean"
# The build outputs read here.
OUTPUT_SUFFIXES = (".ilean", ".olean", ".olean.server", ".olean.private")

# Lean source syntax shared by the tools that read declarations.
ATTR_BLOCK = re.compile(r"@\[((?:[^\[\]]|\[(?:[^\[\]]|\[[^\[\]]*\])*\])*)\]")
ATTRIBUTE_COMMAND = re.compile(
    r"^attribute\s*\[((?:[^\[\]]|\[(?:[^\[\]]|\[[^\[\]]*\])*\])*)\]", re.M)
COMMAND_START = re.compile(
    r"^(?:@\[|/--|/-!|#|(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|"
    r"scoped|local|meta)\s+)*(?:theorem|lemma|def|abbrev|opaque|axiom|instance|structure|class|"
    r"inductive|example|namespace|section|end|open|universe|variable|include|omit|attribute|"
    r"set_option|syntax|macro|macro_rules|elab|elab_rules|notation|notation3|infixl|infixr|infix|"
    r"prefix|postfix|initialize|mutual|export|alias|register_simp_attr|declare_aesop_rule_sets|"
    r"add_decl_doc|deriving)\b)", re.M)
IDENT = re.compile(r"[A-Za-z_À-ɏͰ-Ͽᴀ-ᶿ℀-⅏]"
                   r"[\w'!?₀-ₜᵢ-ᵪ.]*")


def glob_modules(root: str) -> list[str]:
    """The modules of a glob-built library, from its source files."""
    return sorted(".".join(p.relative_to(ROOT).with_suffix("").parts)
                  for p in (ROOT / root).rglob("*.lean"))


def root_modules(glob=glob_modules) -> list[str]:
    """Modules whose imports cover all three libraries: the aggregator roots and every module
    of a glob-built library."""
    return [m for root in ROOTS
            for m in (glob(root) if root in GLOB_ROOTS else [root])]


def module_role(module: str) -> str:
    """`lib`, `test` or `abstract` for a module of one of the three libraries."""
    if module.startswith("ComplexityAbstracts.") or module.startswith("ComplexityTests.Abstracts."):
        return "abstract"
    if module.startswith("ComplexityTests."):
        return "test"
    return "lib"


def source_path(module: str) -> Path:
    rel = module.replace(".", "/") + ".lean"
    return ROOT / ("abstracts/" + rel if module.startswith("ComplexityAbstracts") else rel)


def is_internal(component: str) -> bool:
    """Whether a name component is one Lean generates, such as `_proof_1` or `match_2`."""
    return (component.startswith("_") or component.isdigit()
            or re.fullmatch(r"(?:eq|match|proof|omega)_[\d_]+", component) is not None)


def run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, text=True, check=True, **kwargs)


# --- Freshness ----------------------------------------------------------------------------------

def lake_outputs_current() -> bool:
    """Whether Lake finds the default build outputs of the three libraries current."""
    return subprocess.run(["lake", "build", "--no-build", *ROOTS], cwd=ROOT,
                          capture_output=True).returncode == 0


def output_differences(build_dir: Path, reference: Path) -> list[str]:
    """Report inputs that are missing, extra or different in `build_dir` compared to
    `reference`, as paths relative to them."""
    def inputs(directory: Path) -> set[Path]:
        # The roots' own outputs (`Complexity.ilean`, …) sit beside their directories, and the
        # module inventory comes from their imports.
        files = [p for root in ROOTS
                 for p in [*(directory / root).rglob("*"), *directory.glob(f"{root}.*")]]
        return {p.relative_to(directory) for p in files
                if p.name.endswith(OUTPUT_SUFFIXES) and p.is_file()}
    ours, theirs = inputs(build_dir), inputs(reference)
    changed = {p for p in ours & theirs
               if not filecmp.cmp(build_dir / p, reference / p, shallow=False)}
    return sorted(map(str, (ours ^ theirs) | changed))


def check_outputs(build_dir: Path, skip: bool, current=lake_outputs_current,
                  reference: Path = DEFAULT_BUILD_DIR) -> str:
    """How the build outputs were checked, or exit when they are not current.

    Lake checks only the default build directory, so another directory must hold exactly the
    same outputs as the checked default ones."""
    if skip:
        return "not checked against the sources"
    if not reference.is_dir():
        sys.exit(f"build outputs are missing in {reference}; run `lake build "
                 + " ".join(ROOTS) + "` first")
    if not current():
        sys.exit("build outputs are missing or stale; run `lake build " + " ".join(ROOTS)
                 + "` (or pass --no-build-check)")
    if build_dir.resolve() == reference.resolve():
        return "checked current by `lake build --no-build`"
    differences = output_differences(build_dir, reference)
    if differences:
        sys.exit(f"{build_dir} differs from the current build outputs in {len(differences)} "
                 f"file(s) (e.g. {', '.join(differences[:3])}); pass --no-build-check to "
                 "use it anyway")
    return "checked identical to the current outputs of `lake build --no-build`"


# --- Loading ------------------------------------------------------------------------------------

ROOT_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def listed_modules(text: str) -> list[str]:
    """The modules a root source file imports."""
    return ROOT_IMPORT.findall(text)


def load_ileans(build_dir: Path, missing: list[str] | None = None,
                glob=glob_modules) -> dict[str, dict]:
    """The `.ilean` data of the modules the three libraries' roots import, by module name.

    A long-lived build directory keeps the outputs of modules that were since deleted or moved,
    and `lake build --no-build` does not notice them, so modules are found by following imports
    from the roots rather than by listing files. A glob-built library (`GLOB_ROOTS`) has no root
    file, so its source files are the starting points instead. Every starting point and every
    module they import must have one; a missing file means the build is incomplete. The aggregator
    roots themselves are left out.

    Given a list `missing`, the build may be partial instead (for a tree that does not build
    completely): the modules are those the roots' source files import, and the ones without an
    `.ilean` file are appended to `missing`."""
    if missing is not None:
        ileans = {}
        for root in ROOTS:
            modules = (glob(root) if root in GLOB_ROOTS
                       else listed_modules(source_path(root).read_text()))
            for module in modules:
                path = build_dir / (module.replace(".", "/") + ".ilean")
                if path.is_file():
                    ileans[module] = json.loads(path.read_text())
                else:
                    missing.append(module)
        return ileans
    ileans, todo = {}, [(module, None) for module in root_modules(glob)]
    while todo:
        module, importer = todo.pop()
        if module in ileans:
            continue
        path = build_dir / (module.replace(".", "/") + ".ilean")
        if not path.is_file():
            sys.exit(f"{path} is missing ({'imported by ' + importer if importer else 'a root'}); "
                     "run `lake build " + " ".join(ROOTS) + "` first")
        ileans[module] = json.loads(path.read_text())
        todo.extend((i[0], module) for i in ileans[module]["directImports"]
                    if i[0].split(".")[0] in ROOTS)
    for root in ROOTS:
        if root not in GLOB_ROOTS:
            del ileans[root]
    return ileans


def load_constants(build_dir: Path, modules: list[str], pairs: str | None = None
                   ) -> tuple[dict[str, dict], list[dict]]:
    """Constants of `modules`, and the groups of constants with alpha-equivalent statements;
    `pairs` (`tidy=plain,…`) adds the fields that `scripts/tidy_sweep.py` reads (see
    `scripts/LeanOutputs.lean`)."""
    out = run(["lake", "env", "lean", "--run", "scripts/LeanOutputs.lean", str(build_dir)]
              + ([pairs] if pairs else []),
              input="\n".join(modules) + "\n", capture_output=True).stdout
    constants, duplicates = {}, []
    for line in out.splitlines():
        row = json.loads(line)
        if "dup" in row:
            duplicates.append(row)
        else:
            constants[row["n"]] = row
    return constants, duplicates


class Source:
    """A source file with its masked code split into lines."""

    def __init__(self, path: Path):
        self.text = path.read_text(encoding="utf-8")
        self.code = masks(self.text)[0]
        self.raw_lines = self.text.split("\n")
        self.lines = self.code.split("\n")
        self.starts = [0]
        for raw in self.raw_lines:
            self.starts.append(self.starts[-1] + len(raw) + 1)

    def span(self, line: int, col: int, end_line: int, end_col: int) -> str:
        """Masked code between 1-based lines and code-point columns."""
        if line == end_line:
            return self.lines[line - 1][col:end_col]
        return "\n".join([self.lines[line - 1][col:]] + self.lines[line:end_line - 1]
                         + [self.lines[end_line - 1][:end_col]])

    def offset(self, line0: int, index: int) -> int:
        return self.starts[line0] + index


class Library:
    """Build outputs and sources of the three libraries, loaded lazily where possible."""

    def __init__(self, build_dir: Path, pairs: str | None = None,
                 missing: list[str] | None = None):
        self.build_dir = build_dir
        self.ileans = load_ileans(build_dir, missing)
        self.modules = sorted(m for m in self.ileans if m.startswith("Complexity."))
        self.constants, self.duplicate_rows = load_constants(build_dir, self.modules, pairs)
        self.sources: dict[str, Source] = {}

    def source(self, module: str) -> Source:
        if module not in self.sources:
            self.sources[module] = Source(source_path(module))
        return self.sources[module]

    def references(self, module: str):
        """`(name, defining module, info)` for each constant referenced in `module`."""
        for key, info in self.ileans[module]["references"].items():
            ident = json.loads(key).get("c")
            if ident:
                yield ident["n"], ident["m"], info


def collect_declarations(lib: Library) -> tuple[dict[str, dict], dict[str, str]]:
    """Public declarations written in library sources (the binders recorded in `.ilean` files),
    and the owner of every such name: a structure for its fields and constructors, a definition
    for the lemmas `@[simps]` generates, and the declaration itself otherwise."""
    decls: dict[str, dict] = {}
    owners: dict[str, str] = {}
    for module in lib.modules:
        rel = module.removeprefix("Complexity.").replace(".", "/") + ".lean"
        for name, defined_in, info in lib.references(module):
            if defined_in != module or not info["definition"]:
                continue
            if name.startswith("_private."):
                owners[name] = name
                continue
            const = lib.constants.get(name)
            if not const or not const["e"]:
                continue
            parent = info["definition"][4] if len(info["definition"]) == 5 else None
            role = "decl"
            if const["k"] == "ctor":
                role = "member"
            elif parent and parent != name:
                if not name.startswith(parent + "."):
                    role = "generated"
                elif lib.constants.get(parent, {}).get("k") == "induct":
                    role = "member"
            decls[name] = {
                "name": name, "module": module, "path": rel,
                "role": role, "kind": const["k"], "exported": const["e"],
                "tidy": const["tidy"], "range": const["r"], "parent": parent,
                "lib_refs": set(), "test_refs": set(), "abstract_refs": set(), "local_uses": 0,
                "unfolded_by": set(),
            }
    for name, decl in decls.items():
        owned = decl["role"] != "decl" and decl["parent"] in decls
        owners[name] = decl["parent"] if owned else name
    return decls, owners
