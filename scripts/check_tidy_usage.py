#!/usr/bin/env python3
"""Report proof-internal tidy usage outside a stated measurement boundary (#862).

This never compares or writes a baseline, rejects a count, or changes S3's allowlist. It reuses
quality_report's declaration metadata, freshness checks and source masks. Counts are report-only;
the proposed Internal/** prefixes are measurement parameters, not approved exemptions.

Usage: python3 scripts/check_tidy_usage.py --json /tmp/tidy-usage.json
To reproduce the issue's older broad Machines measurement boundary, pass
--internal-prefix Complexity/Computability/Machines/ (this grants no exemption).
Use TIDY_USAGE_NATIVE=1 python3 -B -m unittest discover -s scripts -p test_tidy_usage.py
to check both classic and split Lean metadata readers as well as the lexical regressions.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import quality_report as qr


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write every module and occurrence")
    parser.add_argument("--markdown", type=Path, help="write the human-readable summary")
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--build-dir", type=Path, default=qr.DEFAULT_BUILD_DIR)
    parser.add_argument("--no-build-check", action="store_true",
                        help="label outputs unchecked instead of requiring source freshness")
    parser.add_argument("--internal-prefix", action="append",
                        help="replace default prefixes with these repo-relative directories; "
                        "repeat for multiple directories (measurement only)")
    args = parser.parse_args(argv)
    prefixes = tuple(args.internal_prefix or qr.TIDY_INTERNAL_PREFIXES)
    if any(not p.endswith("/") or p.startswith("/") or ".." in Path(p).parts for p in prefixes):
        parser.error("internal prefixes must be repo-relative directories ending in /")
    outputs = qr.check_outputs(args.build_dir, args.no_build_check)
    report = qr.tidy_usage_report(qr.Library(args.build_dir), prefixes)
    report["provenance"]["outputs"] = outputs
    text = (f"Revision `{report['provenance']['revision']}`; outputs {outputs}.\n\n"
            + qr.tidy_usage_markdown(report, args.top))
    if args.json:
        args.json.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    if args.markdown:
        args.markdown.write_text(text)
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
