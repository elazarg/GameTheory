import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parents[1] / "lean-deprecations.py"
SPEC = importlib.util.spec_from_file_location("lean_deprecations", SCRIPT)
RENAMES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RENAMES)


class DeprecationTests(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory()
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name).resolve()
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def source(self, name, text, tracked=True):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode("utf-8"))
        if tracked:
            subprocess.run(["git", "-C", str(self.root), "add", "--", name], check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return path

    def log(self, *diagnostics):
        path = self.root / "build.log"
        path.write_text("\n".join(diagnostics) + "\n", encoding="utf-8")
        return path

    @staticmethod
    def diagnostic(path, line, column, old="Old.foo", new="New.foo", severity="error", lake=True):
        message = f"`{old}` has been deprecated: {'Use' if lake else 'use'} `{new}` instead"
        location = f"{path}:{line}:{column}:"
        return f"{severity}: {location} {message}" if lake else f"{location} {severity}: {message}"

    def test_error_warning_and_full_namespace_relocation(self):
        first = self.source("GameTheory/A.lean", "#check Old.foo\n")
        second = self.source("lint/B.lean", "#check foo\n")
        log = self.log(self.diagnostic(first, 1, 7, new="Different.Namespace.bar"),
                       self.diagnostic("lint/B.lean", 1, 7, new="Different.Namespace.bar",
                                       severity="warning", lake=False))
        plan = RENAMES.make_plan(self.root, [log])
        self.assertEqual(len(plan["files"]), 2)
        self.assertEqual(plan["unmatched"], [])
        self.assertEqual(first.read_text(), "#check Old.foo\n")
        RENAMES.apply_plan(self.root, plan)
        self.assertEqual(first.read_text(), "#check Different.Namespace.bar\n")
        self.assertEqual(second.read_text(), "#check Different.Namespace.bar\n")

    def test_unicode_crlf_and_bom_preserved(self):
        line = 'example : Nat := by have α := "😀"; exact foo'
        original = "\ufeff-- η\r\n" + line + "\r\n-- foo remains\r\n"
        source = self.source("GameTheory/Unicode.lean", original)
        plan = RENAMES.make_plan(self.root, [self.log(
            self.diagnostic("GameTheory/Unicode.lean", 2, line.index("foo")))])
        self.assertEqual(plan["files"][0]["edits"][0]["original"], "foo")
        RENAMES.apply_plan(self.root, plan)
        expected = original.replace("exact foo", "exact New.foo").encode("utf-8")
        self.assertEqual(source.read_bytes(), expected)

    def test_duplicate_diagnostics_and_cli_plan_do_not_edit_source(self):
        source = self.source("GameTheory/A.lean", "#check Old.foo\n")
        log = self.log(self.diagnostic("GameTheory/A.lean", 1, 7))
        output = self.root / "plan.json"
        subprocess.run([sys.executable, str(SCRIPT), "plan", "--root", str(self.root),
                        "--log", str(log), "--log", str(log), "--out", str(output)],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        plan = json.loads(output.read_text(encoding="utf-8"))
        self.assertEqual(plan["duplicates"], 1)
        self.assertEqual(len(plan["files"][0]["edits"]), 1)
        self.assertEqual(source.read_bytes(), b"#check Old.foo\n")

    def test_stale_file_rejects_entire_preflight_before_writes(self):
        first = self.source("GameTheory/A.lean", "#check Old.foo\n")
        second = self.source("GameTheory/B.lean", "#check Old.foo\n")
        log = self.log(*(self.diagnostic(f"GameTheory/{name}.lean", 1, 7) for name in "AB"))
        plan = RENAMES.make_plan(self.root, [log])
        second.write_bytes(b"#check Old.foo\n-- changed\n")
        with self.assertRaisesRegex(ValueError, "stale source hash"):
            RENAMES.apply_plan(self.root, plan)
        self.assertEqual(first.read_bytes(), b"#check Old.foo\n")
        self.assertEqual(second.read_bytes(), b"#check Old.foo\n-- changed\n")
        self.assertEqual(list(self.root.rglob(".lean-renames-*")), [])
        second.write_bytes(b"#check Old.foo\n")
        plan["files"][1]["edits"][0]["offset"] += 1
        with self.assertRaisesRegex(ValueError, "position/text"):
            RENAMES.apply_plan(self.root, plan)
        self.assertEqual(first.read_bytes(), b"#check Old.foo\n")

    def test_paths_dependencies_untracked_and_other_diagnostics(self):
        self.source("GameTheory/A.lean", "#check Old.foo\n")
        self.source("GameTheory/Untracked.lean", "#check Old.foo\n", tracked=False)
        self.source(".lake/packages/pkg/GameTheory/Dep.lean", "#check Old.foo\n")
        self.source("Other.lean", "#check Old.foo\n")
        with tempfile.TemporaryDirectory() as outside:
            external = Path(outside) / "Outside.lean"
            external.write_text("#check Old.foo\n", encoding="utf-8")
            paths = ["GameTheory/A.lean", "GameTheory/Untracked.lean",
                     ".lake/packages/pkg/GameTheory/Dep.lean", "Other.lean", str(external)]
            log = self.log(*(self.diagnostic(path, 1, 7) for path in paths),
                           "warning: GameTheory/A.lean:1:0: unused variable",
                           "error: GameTheory/A.lean:2:0: Unknown constant `Measure.isProbabilityMeasure_map`",
                           "error: build failed")
            plan = RENAMES.make_plan(self.root, [log])
        self.assertEqual(len(plan["files"]), 1)
        self.assertEqual(len(plan["unmatched"]), 4)
        self.assertEqual(len(plan["remaining_diagnostics"]), 3)
        self.assertTrue(any("isProbabilityMeasure_map" in entry["diagnostic"]
                            for entry in plan["remaining_diagnostics"]))
        hostile = copy.deepcopy(plan)
        hostile["files"][0]["path"] = ".lake/packages/pkg/GameTheory/Dep.lean"
        with self.assertRaisesRegex(ValueError, "authored tracked"):
            RENAMES.apply_plan(self.root, hostile)

    def test_windows_absolute_diagnostic_parser(self):
        path = r"D:\workspace\games\GameTheory\GameTheory\A.lean"
        for lake in (True, False):
            match = RENAMES.DIAGNOSTIC.match(self.diagnostic(path, 12, 4, lake=lake))
            self.assertEqual(match["path"], path)
            self.assertEqual(match["line"], "12")
            self.assertEqual(match["column"], "4")

    def test_type_change_note_is_manual_but_adjacent_safe_rename_applies(self):
        source = self.source("GameTheory/A.lean", "#check stdSimplex\n#check if_pos\n")
        log = self.log(
            self.diagnostic("GameTheory/A.lean", 1, 7, "stdSimplex", "Convexity.StdSimplex"),
            "", "Note: The updated constant has a different type:",
            "  (R : Type u) → [LE R] → [AddCommMonoid R] → [One R] → Type v → Type (max u v)",
            "instead of", "  (𝕜 : Type u) → (ι : Type v) → [Fintype ι] → Set (ι → 𝕜)",
            self.diagnostic("GameTheory/A.lean", 2, 7, "if_pos", "ite_eq_left"))
        plan = RENAMES.make_plan(self.root, [log])
        self.assertEqual(len(plan["unmatched"]), 1)
        self.assertIn("different type", plan["unmatched"][0]["reason"])
        self.assertIn("instead of", plan["unmatched"][0]["continuation"])
        self.assertEqual([edit["original"] for edit in plan["files"][0]["edits"]], ["if_pos"])
        RENAMES.apply_plan(self.root, plan)
        self.assertEqual(source.read_text(), "#check stdSimplex\n#check ite_eq_left\n")

    def test_type_change_vetoes_earlier_duplicate_and_stops_at_log_markers(self):
        self.source("GameTheory/A.lean", "#check Old.foo\n")
        diagnostic = self.diagnostic("GameTheory/A.lean", 1, 7)
        note = "Note: The updated constant has a different type:"
        plan = RENAMES.make_plan(self.root, [self.log(diagnostic, diagnostic, note)])
        self.assertEqual(plan["files"], [])
        self.assertEqual(plan["duplicates"], 1)
        self.assertEqual(len(plan["unmatched"]), 1)
        conflicting = self.diagnostic("GameTheory/A.lean", 1, 7, new="Other.foo")
        plan = RENAMES.make_plan(self.root, [self.log(diagnostic, conflicting, note)])
        self.assertEqual(plan["files"], [])
        self.assertEqual(len(plan["unmatched"]), 1)
        for marker in ("trace: .> lean next.lean", "✔ [2/3] Built Next", "[Elab.command] next"):
            with self.subTest(marker=marker):
                plan = RENAMES.make_plan(self.root, [self.log(diagnostic, marker, note)])
                self.assertEqual(len(plan["files"][0]["edits"]), 1)
                self.assertEqual(plan["unmatched"], [])

    def test_comments_strings_and_field_notation_are_skipped(self):
        lines = ["-- Old.foo", '/- outer /- inner -/ Old.foo -/',
                 '#check "Old.foo"', '#check r#"Old.foo"#', '#check object.foo',
                 '#check «Old.foo»', '#check Old.foo!']
        self.source("GameTheory/A.lean", "\n".join(lines) + "\n")
        diagnostics = [self.diagnostic("GameTheory/A.lean", i, line.index("Old.foo"))
                       for i, line in enumerate(lines, 1) if "Old.foo" in line]
        diagnostics.append(self.diagnostic("GameTheory/A.lean", 5, lines[4].index("foo")))
        plan = RENAMES.make_plan(self.root, [self.log(*diagnostics)])
        self.assertEqual(plan["files"], [])
        self.assertEqual(len(plan["unmatched"]), len(lines))

    def test_ambiguous_overlapping_and_tampered_proposals(self):
        source = self.source("GameTheory/A.lean", "#check Old.foo\n")
        first = self.diagnostic("GameTheory/A.lean", 1, 7)
        ambiguous = RENAMES.make_plan(self.root, [self.log(
            first, self.diagnostic("GameTheory/A.lean", 1, 7, new="Other.foo"))])
        self.assertEqual(ambiguous["files"], [])
        self.assertEqual(len(ambiguous["unmatched"]), 2)
        plan = RENAMES.make_plan(self.root, [self.log(first)])
        legacy = copy.deepcopy(plan)
        legacy["version"] = 1
        with self.assertRaisesRegex(ValueError, "plan version"):
            RENAMES.apply_plan(self.root, legacy)
        overlapping = copy.deepcopy(plan)
        overlapping["files"][0]["edits"] *= 2
        with self.assertRaisesRegex(ValueError, "overlapping"):
            RENAMES.apply_plan(self.root, overlapping)
        tampered = copy.deepcopy(plan)
        tampered["files"][0]["edits"][0]["original"] = "foo"
        with self.assertRaisesRegex(ValueError, "position/text"):
            RENAMES.apply_plan(self.root, tampered)
        self.assertEqual(source.read_bytes(), b"#check Old.foo\n")


if __name__ == "__main__":
    unittest.main()
