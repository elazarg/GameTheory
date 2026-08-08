"""Command-line entry point for the exact repair/CEGIS experiment."""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any
import json
import sys

from .cegis import run_cegis_manifest
from .model import RationalQuittingGame, parse_fraction
from .report import (
    dump_report,
    make_filter_report,
    make_repair_report,
    verify_report,
)
from .search import SearchConfig, run_repair_ladder


def _load_config(path: str | None) -> SearchConfig:
    if path is None:
        return SearchConfig()
    with Path(path).open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("search config must be a JSON object")
    return SearchConfig.from_dict(data)


def command_ladder(args: argparse.Namespace) -> int:
    game = RationalQuittingGame.from_path(args.table)
    config = _load_config(args.config)
    result = run_repair_ladder(game, config)
    if result.finding is not None:
        report = make_repair_report(game, result, config)
    else:
        best = min(
            (
                trace.best_regret
                for trace in result.trace
                if trace.best_regret is not None
            ),
            default=None,
        )
        report = make_filter_report(
            game,
            fixed_gap=args.filter_gap,
            scope={"repair_ladder": config.to_dict()},
            tested=sum(trace.tested for trace in result.trace),
            minimum_regret=best,
            reason=(
                "The configured finite repair ladder was exhausted.  No "
                "claim is made about arbitrary behavioral profiles."
            ),
        )
    text = dump_report(report, args.output)
    if args.output is None:
        sys.stdout.write(text)
    return 0


def command_verify_report(args: argparse.Namespace) -> int:
    game = RationalQuittingGame.from_path(args.table)
    with Path(args.report).open("r", encoding="utf-8") as handle:
        report = json.load(handle)
    verify_report(game, report)
    print(f"verified {args.report}")
    return 0


def command_cegis(args: argparse.Namespace) -> int:
    run = run_cegis_manifest(args.manifest)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    index: list[dict[str, Any]] = []
    for number, report in enumerate(run.reports):
        safe_name = "".join(
            character if character.isalnum() or character in "-_" else "_"
            for character in report["table"]
        ).strip("_")
        filename = f"{number:04d}-{safe_name or 'candidate'}.json"
        dump_report(report, output_dir / filename)
        index.append(
            {
                "file": filename,
                "table": report["table"],
                "classification": report["classification"],
            }
        )
    summary = {
        "schema": "quitting-table-cegis-summary/v1",
        "manifest": str(Path(args.manifest)),
        "candidates": run.candidates,
        "reused_witnesses": len(run.witnesses),
        "reports": index,
    }
    (output_dir / "index.json").write_text(
        json.dumps(summary, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python3 -m experiments.quitting_repair_cegis",
        description=(
            "Exact rational finite repair search.  Negative exhaustion is "
            "reported only as a bounded filter."
        ),
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    ladder = subparsers.add_parser("ladder", help="run the exact repair ladder")
    ladder.add_argument("table")
    ladder.add_argument("--config")
    ladder.add_argument("--output")
    ladder.add_argument(
        "--filter-gap",
        default="1/10",
        type=parse_fraction,
        help="positive label for an exhausted finite filter (default: 1/10)",
    )
    ladder.set_defaults(handler=command_ladder)

    verify = subparsers.add_parser(
        "verify-report", help="recompute and validate a saved report"
    )
    verify.add_argument("table")
    verify.add_argument("report")
    verify.set_defaults(handler=command_verify_report)

    cegis = subparsers.add_parser(
        "cegis", help="run finite rational-table fixed-gap CEGIS"
    )
    cegis.add_argument("manifest")
    cegis.add_argument("--output-dir", required=True)
    cegis.set_defaults(handler=command_cegis)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return int(args.handler(args))
    except (OSError, TypeError, ValueError, AssertionError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
