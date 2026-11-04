#!/usr/bin/env python3
"""Build the Operator's Manual or the human Agent Operator's Manual.

Requires Pandoc, XeLaTeX and pdfinfo; model diagrams also use Graphviz.
--tex-only skips XeLaTeX/pdfinfo but still renders the diagram assets.
Checks current source excerpts first; does not fetch dependencies or compile Lean.
See manual/BUILD.md. All outputs default to ignored manual/_build/.
"""
import argparse
import subprocess
import sys
from pathlib import Path

from check_operator_manual import check

ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "manual/_build")
    parser.add_argument("--tex-only", action="store_true")
    parser.add_argument("--check-build", type=Path,
                        help="Check an existing build's input hashes without generating files")
    parser.add_argument("--agent-manual", action="store_true",
                        help="Build or check the short human Agent Operator's Manual")
    args = parser.parse_args()
    result = check(ROOT)
    if result["errors"]:
        print("Fix the manual checks before building:", file=sys.stderr)
        for error in result["errors"]:
            print(error, file=sys.stderr)
        return 1
    command = [sys.executable, "-B", str(ROOT / "manual/data/build_manual.py")]
    if args.agent_manual:
        command.append("--agent-manual")
    if args.check_build:
        command.extend(["--check-build", str(args.check_build.resolve())])
    else:
        command.extend(["--output-dir", str(args.output_dir.resolve())])
        if args.tex_only:
            command.append("--tex-only")
    return subprocess.run(command, cwd=ROOT).returncode


if __name__ == "__main__":
    raise SystemExit(main())
