#!/usr/bin/env python3
"""Plan and apply diagnostic-position Lean deprecation renames (stdlib only).

Finish the build before planning. Keep source frozen while reviewing/applying
the plan, and start the next build only after apply finishes. This script never
runs Lean or Lake. Review `unmatched` and `remaining_diagnostics` manually.

  python scripts/lean-deprecations.py plan --root . --log build.log --out plan.json
  python scripts/lean-deprecations.py apply --root . --plan plan.json

Columns are Lean's zero-based Unicode character positions; lines are one-based.
Only ordinary qualified identifier tokens at the reported position are edited.
Escaped identifiers, field notation and uncertain positions are skipped. Full
replacement names are retained even when the old source name was unqualified.
Deprecations accompanied by a different-type note always need manual review.
All files are prevalidated before writing; replacements are atomic per file,
not a crash-safe transaction across multiple files. Concurrent edits are unsafe.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PureWindowsPath
import re
import subprocess
import tempfile
import unicodedata


DIAGNOSTIC = re.compile(
    r"^(?:(?P<prefix>warning|error):\s*)?(?P<path>.+?\.lean):"
    r"(?P<line>\d+):(?P<column>\d+):\s*"
    r"(?:(?P<severity>warning|error):\s*)?(?P<message>.*)$"
)
DEPRECATION = re.compile(r"`([^`]+)` has been deprecated:\s*[Uu]se `([^`]+)` instead")
IDENTIFIER = re.compile(r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*", re.UNICODE)
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
RAW_STRING = re.compile(r'r(#+)"')
CHARACTER = re.compile(r"'(?:\\[^\n]|[^'\\\n])'")
LOG_MARKER = re.compile(
    r"^(?:(?:warning|error|info|trace):|\[|(?:\S+\s+)?\[\d+/\d+\]|"
    r"Build (?:completed|failed)|Some required targets)"
)
TYPE_CHANGE = re.compile(r"\bdifferent\s+type\b", re.IGNORECASE)
PLAN_VERSION = 2


def tracked_sources(root):
    """Git, rather than directory membership alone, defines authored files."""
    top = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "--show-toplevel"], text=True
    ).strip()
    if Path(top).resolve() != root:
        raise ValueError("--root must be the repository root")
    names = subprocess.check_output(
        ["git", "-C", str(root), "ls-files", "-z", "--", "GameTheory", "lint"]
    ).decode("utf-8").split("\0")
    return {name for name in names if name.endswith(".lean")}


def source_path(root, tracked, name):
    if PureWindowsPath(name).drive and os.name != "nt":
        raise ValueError("Windows absolute path cannot be resolved on this host")
    path = Path(name.replace("\\", "/"))
    path = (path if path.is_absolute() else root / path).resolve(strict=True)
    try:
        relative = path.relative_to(root).as_posix()
    except ValueError:
        raise ValueError("path is outside the repository") from None
    if relative not in tracked or relative.split("/")[0] not in {"GameTheory", "lint"}:
        raise ValueError("path is not an authored tracked GameTheory/ or lint/ Lean file")
    return path, relative


def protected_spans(text):
    """Conservatively exclude nested comments, strings and escaped names."""
    spans = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif match := RAW_STRING.match(text, i):
            end = text.find('"' + match[1], i + len(match[0]))
            i = len(text) if end < 0 else end + 1 + len(match[1])
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif text[i] == "«":
            end = text.find("»", i + 1)
            i = len(text) if end < 0 else end + 1
        elif match := CHARACTER.match(text, i):
            i += len(match[0])
        else:
            i += 1
            continue
        spans.append((start, min(i, len(text))))
    return spans


def locate(text, line, column, old, new):
    if not IDENTIFIER.fullmatch(old) or not IDENTIFIER.fullmatch(new):
        raise ValueError("unsupported identifier spelling")
    lines = text.split("\n")
    if line < 1 or line > len(lines) or column < 0 or column >= len(lines[line - 1].rstrip("\r")):
        raise ValueError("diagnostic position is out of range")
    offset = sum(len(part) + 1 for part in lines[:line - 1]) + column
    def neighbor(char):
        return char.isalnum() or char in "_'.!?«»" or unicodedata.category(char).startswith("M")

    if offset and neighbor(text[offset - 1]):
        raise ValueError("position is inside a token or uses field notation")
    token = IDENTIFIER.match(text, offset)
    if not token or (token[0] != old and not old.endswith("." + token[0])):
        raise ValueError("exact token at diagnostic position does not match deprecated name")
    end = token.end()
    if end < len(text) and neighbor(text[end]):
        raise ValueError("unsupported token boundary")
    if any(start < end and stop > offset for start, stop in protected_spans(text)):
        raise ValueError("position is in a comment, string, character or escaped identifier")
    return {"line": line, "column": column, "offset": offset, "original": token[0],
            "replacement": new, "old": old, "new": new}


def make_plan(root, logs):
    tracked = tracked_sources(root)
    plan = {"version": PLAN_VERSION, "root": str(root), "files": [], "unmatched": [],
            "remaining_diagnostics": [], "duplicates": 0}
    snapshots, candidates, seen, manual_positions = {}, {}, set(), set()
    for log in logs:
        lines = [ANSI.sub("", line).rstrip()
                 for line in Path(log).read_text(encoding="utf-8-sig").splitlines()]
        for number, raw in enumerate(lines, 1):
            raw = raw.strip()
            diagnostic = DIAGNOSTIC.match(raw)
            finding = {"log": str(log), "log_line": number, "diagnostic": raw}
            if not diagnostic or not (diagnostic["prefix"] or diagnostic["severity"]):
                if "deprecated" in raw:
                    plan["unmatched"].append({**finding, "reason": "unsupported diagnostic format"})
                elif re.match(r"(?:warning|error):", raw):
                    plan["remaining_diagnostics"].append(finding)
                continue
            continuation = []
            for following in lines[number:]:
                if DIAGNOSTIC.match(following.strip()) or LOG_MARKER.match(following.strip()):
                    break
                continuation.append(following)
            if continuation:
                finding["continuation"] = "\n".join(continuation).strip()
            old_new = DEPRECATION.search(diagnostic["message"])
            if not old_new:
                category = "unmatched" if "deprecated" in diagnostic["message"] else "remaining_diagnostics"
                plan[category].append({**finding, "reason": "no supported deprecation replacement"})
                continue
            try:
                path, relative = source_path(root, tracked, diagnostic["path"])
                line, column = int(diagnostic["line"]), int(diagnostic["column"])
                key = (relative, line, column, old_new[1], old_new[2])
                different_type = TYPE_CHANGE.search(raw + "\n" + finding.get("continuation", ""))
                if different_type:
                    if key[:3] not in manual_positions:
                        plan["unmatched"].append({**finding,
                            "reason": "replacement has a different type; manual review required"})
                    manual_positions.add(key[:3])
                if key in seen:
                    plan["duplicates"] += 1
                    continue
                seen.add(key)
                if different_type:
                    continue
                if relative not in snapshots:
                    data = path.read_bytes()
                    snapshots[relative] = (data, data.decode("utf-8"))
                edit = locate(snapshots[relative][1], line, column, old_new[1], old_new[2])
                candidates.setdefault(relative, []).append((edit, finding))
            except (ValueError, OSError) as error:
                plan["unmatched"].append({**finding, "reason": str(error)})
    for relative, entries in sorted(candidates.items()):
        # A repeated diagnostic may carry the note only on a later occurrence.
        # That note vetoes every proposal for the same source location.
        entries = [(edit, finding) for edit, finding in entries
                   if (relative, edit["line"], edit["column"]) not in manual_positions]
        entries.sort(key=lambda entry: entry[0]["offset"])
        conflicts = set()
        for i, (left, _) in enumerate(entries):
            for j in range(i + 1, len(entries)):
                if entries[j][0]["offset"] >= left["offset"] + len(left["original"]):
                    break
                conflicts.update((i, j))
        edits = []
        for i, (edit, finding) in enumerate(entries):
            if i in conflicts:
                plan["unmatched"].append({**finding, "reason": "ambiguous or overlapping proposals"})
            else:
                edits.append(edit)
        if edits:
            plan["files"].append({"path": relative,
                                  "sha256": hashlib.sha256(snapshots[relative][0]).hexdigest(),
                                  "edits": edits})
    return plan


def apply_plan(root, plan):
    if plan.get("version") != PLAN_VERSION or Path(plan["root"]).resolve() != root:
        raise ValueError("plan version or repository root does not match")
    tracked = tracked_sources(root)
    prepared, seen = [], set()
    for file in plan["files"]:
        path, relative = source_path(root, tracked, file["path"])
        if relative in seen:
            raise ValueError("duplicate file entries in plan")
        seen.add(relative)
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != file["sha256"]:
            raise ValueError(f"stale source hash: {relative}")
        text = data.decode("utf-8")
        edits = sorted(file["edits"], key=lambda edit: edit["offset"])
        previous_end = -1
        for edit in edits:
            expected = locate(text, edit["line"], edit["column"], edit["old"], edit["new"])
            if any(edit.get(key) != value for key, value in expected.items()):
                raise ValueError(f"stale or invalid position/text: {relative}")
            if edit["offset"] < previous_end:
                raise ValueError(f"ambiguous or overlapping proposals: {relative}")
            previous_end = edit["offset"] + len(edit["original"])
        for edit in reversed(edits):
            start = edit["offset"]
            text = text[:start] + edit["replacement"] + text[start + len(edit["original"]):]
        prepared.append((path, data, text.encode("utf-8")))

    # Stage only after every file, hash and edit passes. Recheck all original
    # bytes immediately before replacement; callers must still freeze source.
    staged = []
    try:
        for path, original, updated in prepared:
            with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".lean-renames-", delete=False) as temp:
                temp.write(updated)
                staged.append((path, original, Path(temp.name)))
            os.chmod(temp.name, path.stat().st_mode)
        if any(path.read_bytes() != original for path, original, _ in staged):
            raise ValueError("source changed during apply preflight")
        for path, _, temporary in staged:
            os.replace(temporary, path)
    finally:
        for _, _, temporary in staged:
            temporary.unlink(missing_ok=True)
    return len(prepared)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    plan_parser = commands.add_parser("plan")
    plan_parser.add_argument("--root", type=Path, required=True)
    plan_parser.add_argument("--log", type=Path, action="append", required=True)
    plan_parser.add_argument("--out", type=Path, required=True)
    apply_parser = commands.add_parser("apply")
    apply_parser.add_argument("--root", type=Path, required=True)
    apply_parser.add_argument("--plan", type=Path, required=True)
    args = parser.parse_args()
    try:
        root = args.root.resolve(strict=True)
        if args.command == "plan":
            if args.out.resolve().suffix.lower() != ".json":
                raise ValueError("--out must name a JSON file, never a Lean source file")
            plan = make_plan(root, args.log)
            args.out.write_text(json.dumps(plan, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
            print(f"Planned {sum(len(file['edits']) for file in plan['files'])} edits; "
                  f"{len(plan['unmatched'])} unmatched; {len(plan['remaining_diagnostics'])} other diagnostics")
        else:
            plan = json.loads(args.plan.read_text(encoding="utf-8-sig"))
            print(f"Updated {apply_plan(root, plan)} files")
    except (ValueError, OSError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"error: {error}\n")


if __name__ == "__main__":
    main()
