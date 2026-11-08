#!/usr/bin/env python3
"""Report proof-internal tidy usage outside a stated measurement boundary (#862).

This never compares or writes a baseline, rejects a count, or changes S3's allowlist. It reuses
the declaration metadata and freshness checks of `scripts/lean_outputs.py` and the source masks of
`scripts/proof_lengths.py`. Counts are report-only; the proposed Internal/** prefixes are
measurement parameters, not approved exemptions.

Usage: python3 scripts/check_tidy_usage.py --json /tmp/tidy-usage.json
To reproduce the issue's older broad Machines measurement boundary, pass
--internal-prefix Complexity/Computability/Machines/ (this grants no exemption).
Use TIDY_USAGE_NATIVE=1 python3 -B -m unittest discover -s scripts -p test_tidy_usage.py
to check both classic and split Lean metadata readers as well as the lexical regressions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_outputs import (  # noqa: E402
    ATTR_BLOCK, ATTRIBUTE_COMMAND, COMMAND_START, DEFAULT_BUILD_DIR, GLOB_ROOTS, IDENT, ROOT, ROOTS,
    Library, check_outputs, collect_declarations, is_internal, load_constants, module_role, run,
    source_path,
)
from proof_lengths import masks  # noqa: E402


# Report-only S4 measurement. These prefixes describe the proposed target, not an exemption
# from S3 or an assertion that the boundary migration has already happened.
TIDY_INTERNAL_PREFIXES = (
    "Complexity/Computability/Machines/Turing/MultiTape/Internal/",
    "ComplexityTests/Machines/Turing/MultiTape/Internal/",
)
BRIDGE_TOKEN = re.compile(r"\.(?:tidy|of_tidy)(?![\w'!?])")
LOCAL_FUN_PROP = re.compile(r"(?:^|,)\s*local\s+fun_prop\s*(?:,|$)")


def tidy_source_signals(text: str, tidy_names: set[str], known_names: set[str] | None = None
                        ) -> dict:
    """Lexical bridge occurrences and local registrations of known tidy-typed constants.

    Reuse the comment/string/character masks and attribute parser. Name suffix matching is
    conservative: an ambiguous suffix counts if any candidate has a tidy type. Unresolved
    local registrations are retained for review, not silently called plain. This does not
    expand macros, resolve local notation, or count semantic pairs of bridge applications.
    """
    code = masks(text)[1]
    bridges = [{"line": code.count("\n", 0, m.start()) + 1,
                "bridge": m[0][1:]} for m in BRIDGE_TOKEN.finditer(code)]
    local, unresolved = [], []
    blocks = [(m, False) for m in ATTR_BLOCK.finditer(code)]
    blocks += [(m, True) for m in ATTRIBUTE_COMMAND.finditer(code)]
    for block, command in sorted(blocks, key=lambda x: x[0].start()):
        if not LOCAL_FUN_PROP.search(block[1]):
            continue
        after = code[block.end():]
        # An attribute command names one or more targets; an inline attribute precedes a decl.
        if command:
            following = next(COMMAND_START.finditer(code, block.end()), None)
            target_text = code[block.end():following.start() if following else len(code)]
            targets = IDENT.findall(target_text)
            targets = targets[:targets.index("in")] if "in" in targets else targets
        else:
            decl = re.match(r"\s*(?:(?:public|private|protected|noncomputable|unsafe|partial|"
                            r"nonrec|meta)\s+)*(?:theorem|lemma|def|abbrev|instance|opaque)\s+",
                            after)
            target = IDENT.match(after, decl.end()) if decl else None
            targets = [target[0]] if target else []
        line = code.count("\n", 0, block.start()) + 1
        if not targets:
            unresolved.append({"line": line, "target": None})
        for target in targets:
            row = {"line": line, "target": target}
            candidates = [n for n in tidy_names if n == target or n.endswith("." + target)]
            if candidates:
                local.append({**row, "candidates": sorted(candidates)})
            elif target not in (known_names or set()):
                unresolved.append(row)
    return {"bridges": bridges, "local_tidy_fun_prop": local,
            "unresolved_local_fun_prop": unresolved}


def private_tidy_declarations(constants: dict[str, dict], source) -> dict[str, list[dict]]:
    """Private source declarations with tidy in their type, excluding generated children."""
    found: dict[str, list[dict]] = defaultdict(list)
    by_range: dict[tuple, set[str]] = defaultdict(set)
    for name, c in constants.items():
        if c["r"]:
            by_range[c["m"], tuple(c["r"])].add(name)
    for name, c in constants.items():
        if not (name.startswith("_private.") and c["tidy"] and c["r"]):
            continue
        r = c["r"]
        selected = source(c["m"]).span(*r[4:]).strip()
        # An authored anonymous instance selects the keyword, not its auto-generated name.
        # Its auxiliary constants can inherit that same range; retain only the source owner,
        # considering *all* types so a plain owner cannot leave a tidy generated child behind.
        anonymous_instance = selected == "instance" and not is_internal(name.rsplit(".", 1)[-1]) \
            and not any(name.startswith(other + ".") for other in by_range[c["m"], tuple(r)]
                        if other != name)
        if selected and (name.endswith("." + selected) or anonymous_instance):
            found[c["m"]].append({"name": name, "line": r[4], "mentions": c["tidy"]})
    return found


def tidy_usage_report(lib: Library, prefixes: tuple[str, ...] = TIDY_INTERNAL_PREFIXES) -> dict:
    """Per-module report of the S4 boundary, with no baseline comparison or enforcement.

    Public statement counts use exactly S3's source-declaration/type rule. Private counts
    require a source declaration range and a tidy constant in its elaborated type; generated
    constants sharing the owner's range are excluded by matching the selected source name.
    Tests use their own metadata. Guide files have source-only signals and explicitly
    unknown statement counts, since the root build does not elaborate the separate guide.
    """
    modules = sorted(m for m in lib.ileans if m.startswith(
        ("Complexity.", "ComplexityTests.")))
    extra = [m for m in modules if m not in lib.modules]
    constants = dict(lib.constants)
    if extra:
        more, _ = load_constants(lib.build_dir, extra)
        constants.update(more)
    tidy_names = {n for n, c in constants.items() if c["tidy"]}
    # Known suffixes distinguish resolved plain targets from unknown ones without rescanning
    # the entire constant inventory for every source attribute.
    known_suffixes = {".".join(parts[i:]) for n in constants
                      for parts in [n.split(".")] for i in range(len(parts))}
    public_tidy_names = {n for n in tidy_names if not n.startswith("_private.")}
    private_tidy_names: dict[str, set[str]] = defaultdict(set)
    for n in tidy_names - public_tidy_names:
        private_tidy_names[constants[n]["m"]].add(n)
    public, _ = collect_declarations(lib)
    public_by_module = Counter(d["module"] for n, d in public.items()
                               if d["role"] != "generated" and
                               (constants[n]["tidy"] or constants[n].get("tb")))
    private_by_module = private_tidy_declarations(constants, lib.source)
    rows = []
    sources = [(m, source_path(m), True) for m in modules]
    sources += [(str(p.relative_to(ROOT)), p, False) for p in sorted(
        (ROOT / "guide").rglob("*.lean")) if ".lake" not in p.parts]
    for module, path, metadata in sources:
        rel = path.relative_to(ROOT).as_posix()
        if any(rel.startswith(p) for p in prefixes):
            continue
        text = path.read_text()
        signals = tidy_source_signals(text,
                                      public_tidy_names | private_tidy_names[module],
                                      known_suffixes)
        private = private_by_module[module] if metadata else None
        counts = {"public_tidy_statements": public_by_module[module]
                  if module.startswith("Complexity.") else None,
                  "private_tidy_declarations": len(private) if metadata else None,
                  "local_tidy_fun_prop": len(signals["local_tidy_fun_prop"]),
                  "bridge_occurrences": len(signals["bridges"])}
        rows.append({"module": module, "path": rel,
                     "role": module_role(module) if metadata else "guide", "counts": counts,
                     "mentions_tidy": bool(re.search(r"Tidily|IsTidy|\.(?:of_)?tidy\b",
                                                       masks(text)[1])),
                     "private_tidy_declarations": private, **signals})
    keys = ("public_tidy_statements", "private_tidy_declarations",
            "local_tidy_fun_prop", "bridge_occurrences")
    source_hash = hashlib.sha256()
    for path in ([source_path(root) for root in ROOTS if root not in GLOB_ROOTS]
                 + [p for _, p, _ in sources]):
        source_hash.update(path.relative_to(ROOT).as_posix().encode() + b"\0")
        source_hash.update(path.read_bytes() + b"\0")
    provenance = {"revision": run(["git", "rev-parse", "HEAD"], capture_output=True).stdout.strip(),
                  "tree": run(["git", "rev-parse", "HEAD^{tree}"], capture_output=True).stdout.strip(),
                  "dirty": bool(run(["git", "status", "--porcelain"],
                                    capture_output=True).stdout.strip()),
                  "source_dirty": bool(run(["git", "status", "--porcelain", "--",
                      "Complexity", "ComplexityTests", "guide",
                      "Complexity.lean"],
                      capture_output=True).stdout.strip()),
                  "scanned_source_sha256": source_hash.hexdigest(),
                  "scanned_files": len(sources), "build_dir": str(lib.build_dir)}
    return {"provenance": provenance, "internal_prefixes": list(prefixes), "report_only": True,
            "totals": {k: sum(r["counts"][k] or 0 for r in rows) for k in keys},
            "files_mentioning_tidy": sum(r["mentions_tidy"] for r in rows),
            "modules": rows,
            "notes": ["The prefixes are a proposed measurement boundary, not S3 exemptions.",
                "Public counts use S3's declaration/type rule only for library modules, but "
                "this report's stated boundary replaces S3's allowlist. Null is not zero.",
                "Private counts inspect elaborated types, not names or proof bodies; generated "
                "constants are excluded by source selection. Type aliases are not unfolded. "
                "Guide metadata is unavailable.",
                "Bridge counts are lexical occurrences, not semantic round-trip pairs; comments "
                "and literals are masked. Other named erasure APIs are not included.",
                "Local registration targets use conservative suffix matching, without elaborated "
                "name resolution; unresolved targets are listed, not assumed plain."]}


def tidy_usage_markdown(report: dict, top: int = 20) -> str:
    """Human view of the same report-only per-module data, with full detail in JSON."""
    out = ["### Proof-internal tidy usage (S4, report only)", "",
           "Measurement excludes: " + ", ".join(f"`{p}`" for p in report["internal_prefixes"]),
           "", "| Module | Public tidy statements | Private tidy declarations | Local tidy "
           "fun_prop targets | Bridge occurrences |", "|---|---:|---:|---:|---:|"]
    rows = sorted(report["modules"], key=lambda r: (
        -sum(v or 0 for v in r["counts"].values()), r["path"]))
    for row in [r for r in rows if any(r["counts"].values())][:top]:
        values = ["unknown" if v is None else str(v) for v in row["counts"].values()]
        out.append(f"| `{row['path']}` | " + " | ".join(values) + " |")
    out += ["| Total (known counts) | " + " | ".join(map(str, report["totals"].values())) + " |",
            "", f"{report['files_mentioning_tidy']} files mention tidy outside the measurement "
            "boundary. Full per-module locations and unresolved targets are in the JSON report.",
            "", *["- " + note for note in report["notes"]]]
    return "\n".join(out) + "\n"




def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write every module and occurrence")
    parser.add_argument("--markdown", type=Path, help="write the human-readable summary")
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR)
    parser.add_argument("--no-build-check", action="store_true",
                        help="label outputs unchecked instead of requiring source freshness")
    parser.add_argument("--internal-prefix", action="append",
                        help="replace default prefixes with these repo-relative directories; "
                        "repeat for multiple directories (measurement only)")
    args = parser.parse_args(argv)
    prefixes = tuple(args.internal_prefix or TIDY_INTERNAL_PREFIXES)
    if any(not p.endswith("/") or p.startswith("/") or ".." in Path(p).parts for p in prefixes):
        parser.error("internal prefixes must be repo-relative directories ending in /")
    outputs = check_outputs(args.build_dir, args.no_build_check)
    report = tidy_usage_report(Library(args.build_dir), prefixes)
    report["provenance"]["outputs"] = outputs
    text = (f"Revision `{report['provenance']['revision']}`; outputs {outputs}.\n\n"
            + tidy_usage_markdown(report, args.top))
    if args.json:
        args.json.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    if args.markdown:
        args.markdown.write_text(text)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
