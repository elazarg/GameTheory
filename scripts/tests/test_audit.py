"""Regression checks for source boundaries, coverage, and diagnostic failure."""

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("audit", ROOT / "scripts/audit.py")
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


class SourceAuditTests(unittest.TestCase):
    def setUp(self):
        workspace = tempfile.TemporaryDirectory()
        self.addCleanup(workspace.cleanup)
        self.root = Path(workspace.name)
        self.write("GameTheory/Core/Fixture.lean", "import Mathlib\n")
        self.write("GameTheory.lean", "import GameTheory.Core.Fixture\n")
        self.write("lint/GameTheory/LintAll.lean", "import GameTheory\nimport GameTheory.Core.Fixture\n")
        self.write("lint/GameTheory/AxiomAudit.lean", "import GameTheory.LintAll\n")
        self.write("lakefile.lean", '''import Lake
open Lake DSL
package GameTheory where
  version := v!"4.34.1"
require "leanprover-community" / "mathlib" @ git "v4.34.1"
''')
        self.write("lean-toolchain", "leanprover/lean4:v4.34.1\n")
        self.manifest("lake-manifest.json", [self.mathlib()])

    def write(self, relative, source):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def manifest(self, relative, packages):
        self.write(relative, json.dumps({"packages": packages}))

    @staticmethod
    def mathlib(revision="pin"):
        return {"name": "mathlib", "rev": revision, "inputRev": "v4.34.1"}

    def assert_rejects(self, reason):
        self.assertTrue(any(reason in e for e in audit.check_sources(self.root)), reason)

    def extension(self, source="import Lean\n"):
        self.write("extensions/complexity/lean-toolchain", "leanprover/lean4:v4.34.1\n")
        self.write("extensions/complexity/GameTheoryComplexity.lean", source)
        self.write("extensions/complexity/lint/GameTheoryComplexity/LintAll.lean",
                   "import GameTheoryComplexity\n")
        self.write("extensions/complexity/lint/GameTheoryComplexity/AxiomAudit.lean",
                   "import GameTheoryComplexity.LintAll\n")

    def test_clean_package(self):
        self.assertEqual(audit.check_sources(self.root), [])
        self.assertEqual(audit.check_version(self.root), [])

    def test_block_comment_before_import_cannot_hide_analysis(self):
        self.write("GameTheory/Core/Fixture.lean", "/- boundary -/ import GameTheory.Analysis.Nash\n")
        self.assert_rejects("Analysis/fixed-point dependency outside Analysis")

    def test_comments_and_strings_do_not_create_violations(self):
        self.write("GameTheory/Core/Fixture.lean", '''import Mathlib
/- outer /- axiom -/ import GameTheory.Analysis.Nash -/
-- sorry Function.update
def text := "axiom sorry import Cslib.Models"
def multiline := "
import GameTheory.Analysis.Nash
"
def raw := r#"sorry \" import Cslib.Models"#
''')
        self.assertEqual(audit.check_sources(self.root), [])

    def test_all_supported_import_modifiers_and_quoted_names(self):
        for source in ["meta import all Cslib.Models", "public import «Complexitylib».Classes",
                       "public meta import «GameTheory».«Complexity».Tests",
                       "import/- separator -/GameTheoryComplexity.SampleTest"]:
            with self.subTest(source=source):
                self.write("GameTheory/Core/Fixture.lean", source + "\n")
                self.assert_rejects("base module imports optional complexity surface")

    def test_wrapped_public_imports_keep_boundaries_and_coverage(self):
        self.write("GameTheory.lean", "module\npublic import\nGameTheory.Core.Fixture\n")
        self.write("lint/GameTheory/LintAll.lean",
                   "module\npublic\nimport GameTheory\npublic import\nGameTheory.Core.Fixture\n")
        self.assertEqual(audit.check_sources(self.root), [])
        source = "module\npublic\nimport\n«GameTheory».Analysis.Nash\n"
        self.assertEqual(list(audit.imports(source)), [("GameTheory", "Analysis", "Nash")])
        self.write("GameTheory/Core/Fixture.lean", source)
        self.assert_rejects("Analysis/fixed-point dependency outside Analysis")

    def test_literal_dot_and_comment_markers_in_quoted_identifier(self):
        self.write("GameTheory/Core/Fixture.lean", '''import «GameTheoryComplexity.SampleTest»
import «GameTheoryComplexity/-literal-/name»
import «GameTheoryComplexity--literal-name»
''')
        self.assertEqual(audit.check_sources(self.root), [])

    def test_private_and_attributed_axioms_are_rejected(self):
        for source in ["private axiom bad : False", "@[simp] axiom bad : False"]:
            with self.subTest(source=source):
                self.write("GameTheory/Core/Fixture.lean", source + "\n")
                self.assert_rejects("forbidden token axiom")

    def test_character_quote_cannot_hide_following_axiom(self):
        self.write("GameTheory/Core/Fixture.lean", '''def quote : Char := '"'
private axiom bad : False
''')
        self.assert_rejects("forbidden token axiom")

    def test_placeholders_and_compiler_trust_are_rejected(self):
        for token in ["sorry", "admit", "native_decide"]:
            self.write("GameTheory/Core/Fixture.lean", f"example : True := by {token}\n")
            self.assert_rejects(f"forbidden token {token}")

    def test_profile_update_owner_and_mathematics_boundary(self):
        self.write("GameTheory/Core/Fixture.lean", "def bad := Function.update x i y\n")
        self.assert_rejects("use Profile.update")
        self.write("GameTheory/Math/Fixture.lean", "import GameTheory.Core.Fixture\n")
        self.assert_rejects("Math crosses its dependency boundary")

    def test_library_cannot_import_test_fixture(self):
        self.write("GameTheory/Core/Fixture.lean", "import GameTheory.Tests.Control\n")
        self.assert_rejects("library module imports a fixture")

    def test_new_integer_execution_leaf_has_computability_checks(self):
        self.write("GameTheory/Finite/BimatrixCertificate.lean", "noncomputable def bad := x\n")
        self.assert_rejects("executable leaf uses noncomputable")
        self.write("GameTheory/Finite/BimatrixCertificate.lean", "def bad := Classical.choice x\n")
        self.assert_rejects("executable leaf uses Classical")

    def test_execution_leaves_have_computability_and_import_checks(self):
        leaves = ["Math.ScalarInequalities", "Math.FiniteMinimumScan",
                  "Math.FiniteLexicographicCompare", "Math.IntegerDictionaryFeasibility",
                  "Math.IntegerRatioSelection",
                  "Math.TabulatedBirdDeterminant", "Finite.BimatrixComputedPivot",
                  "Finite.BimatrixComputedOrientation"]
        for leaf in leaves:
            path = "GameTheory/" + leaf.replace(".", "/") + ".lean"
            for source, reason in [
                ("noncomputable def bad := x", "executable leaf uses noncomputable"),
                ("open Classical", "executable leaf uses Classical"),
                ("def bad := Classical.choice x", "executable leaf uses Classical"),
                ("def bad := Fintype.ofFinite X", "executable leaf uses Fintype.ofFinite"),
                ("import GameTheory.Math.Probability.Expectation",
                 "executable leaf imports probability or analysis"),
                ("import Mathlib.Analysis.SpecialFunctions.Pow.Real",
                 "executable leaf imports probability or analysis"),
            ]:
                with self.subTest(leaf=leaf, source=source):
                    self.write(path, source + "\n")
                    self.assertTrue(any(reason in error and path in error
                                        for error in audit.check_sources(self.root)))

    def test_execution_checks_do_not_apply_to_proof_modules(self):
        self.write("GameTheory/Finite/BimatrixComputedPivotCorrectness.lean",
                   "noncomputable def witness := Classical.choice x\n")
        self.assertFalse(any("executable leaf" in error
                             for error in audit.check_sources(self.root)))

    def test_missing_build_trace_fails_diagnostic_audit(self):
        self.assertTrue(all("missing build diagnostic trace" in e
                            for e in audit.check_diagnostics(self.root, "GameTheory")))

    def test_cached_diagnostics_fail_and_dependency_logs_are_separate(self):
        for module in audit.modules(self.root, "GameTheory"):
            path = Path(*module).with_suffix(".trace").as_posix()
            self.write(f".lake/build/lib/lean/{path}", json.dumps({"log": []}))
        for module in audit.modules(self.root / "lint", "GameTheory"):
            path = Path(*module).with_suffix(".trace").as_posix()
            self.write(f".lake/build/lib/lean/{path}", json.dumps({"log": []}))
        self.write(".lake/packages/Dependency/.lake/build/lib/lean/Dependency.trace",
                   json.dumps({"log": [{"level": "info", "message": "upstream suggestion"}]}))
        self.assertEqual(audit.check_diagnostics(self.root, "GameTheory"), [])
        for level in ["info", "warning", "error"]:
            self.write(".lake/build/lib/lean/GameTheory/Core/Fixture.trace",
                       json.dumps({"log": [{"level": level, "message": "control"}]}))
            self.assertEqual(audit.check_diagnostics(self.root, "GameTheory"),
                             [f"GameTheory.Core.Fixture: {level}: control"])

    def test_lint_and_axiom_coverage_cannot_silently_shrink(self):
        self.write("GameTheory/Core/New.lean", "theorem added : True := by trivial\n")
        self.assert_rejects("public module missing from lint imports")
        self.assert_rejects("module missing from axiom audit")
        self.write("GameTheory/Tests/New.lean", "example : True := by trivial\n")
        self.assert_rejects("GameTheory.Tests.New")

    def test_stale_lint_import_is_rejected(self):
        self.write("lint/GameTheory/LintAll.lean", "import GameTheory.Deleted\n")
        self.assert_rejects("stale or fixture lint import")

    def test_optional_dependency_configuration_and_manifest_are_checked(self):
        self.write("lakefile.lean", 'require "owner" / "complexitylib" from git "url"\n')
        self.assert_rejects("base Lake configuration directly requires an optional dependency")
        self.manifest("lake-manifest.json", [self.mathlib(), {"name": "cslib"}])
        self.assert_rejects("base manifest requires optional dependency")

    def test_lake_multiline_strings_do_not_create_dependencies(self):
        with (self.root / "lakefile.lean").open("a", encoding="utf-8") as stream:
            stream.write('def ignored := "\nrequire cslib from git \\\"url\\\"\n"\n')
        self.assertEqual(audit.check_sources(self.root), [])
        self.assertEqual(audit.check_version(self.root), [])

    def test_extension_scope_toolchain_and_mathlib_pins(self):
        self.extension()
        self.assertEqual(audit.check_sources(self.root), [])
        self.manifest("extensions/complexity/lake-manifest.json", [self.mathlib("different")])
        self.assert_rejects("base and complexity Mathlib pins differ")
        self.write("extensions/complexity/lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.assert_rejects("base and complexity toolchains differ")

    def test_extension_rejects_placeholders_and_inspection_commands(self):
        for token in ["sorry", "admit", "axiom", "native_decide"]:
            with self.subTest(token=token):
                self.extension(f"example : True := by {token}\n")
                self.assert_rejects(f"GameTheoryComplexity.lean: forbidden token {token}")
        for command in ["eval", "print", "check", "reduce"]:
            with self.subTest(command=command):
                self.extension(f"#{command} True\n")
                self.assert_rejects("GameTheoryComplexity.lean: inspection command")

    def test_public_extension_rejects_fixtures_and_excluded_trust_surfaces(self):
        for namespace in ["GameTheory", "GameTheoryComplexity"]:
            for branch, reason in [
                ("Experimental.Control", "library module imports a fixture"),
                ("Tests.Control", "library module imports a fixture"),
                ("Core.ControlTest", "library module imports a fixture"),
                ("Frontier.Control", "trusted module imports an excluded trust surface"),
                ("Challenges.Control", "trusted module imports an excluded trust surface"),
            ]:
                with self.subTest(namespace=namespace, branch=branch):
                    self.extension(f"import {namespace}.{branch}\n")
                    self.assert_rejects(f"GameTheoryComplexity.lean: {reason}")

    def test_extension_keeps_its_backend_and_proof_dependency_budget(self):
        self.extension('''import Complexitylib.Classes.P.NormalForm
import Cslib.Models
import GameTheory.Core.Utility
import GameTheoryComplexity.SampleTest
import GameTheoryComplexity.Backend.CompiledSampleTest
noncomputable def proofWitness := Classical.choice x
def transport := Eq.mp h x
''')
        self.assertEqual(audit.check_sources(self.root), [])

    def test_extension_keeps_analysis_and_profile_update_boundaries(self):
        for source, reason in [
            ("import GameTheory.Analysis.Nash\n", "Analysis/fixed-point dependency outside Analysis"),
            ("import FixedPointTheorems.Kakutani\n", "Analysis/fixed-point dependency outside Analysis"),
            ("def bad := Function.update x i y\n", "use Profile.update"),
        ]:
            with self.subTest(source=source):
                self.extension(source)
                self.assert_rejects(reason)

    def test_extension_fixture_can_import_other_fixtures(self):
        self.extension()
        self.write("extensions/complexity/GameTheoryComplexity/Tests/Control.lean",
                   "import GameTheory.Experimental.Control\nimport GameTheory.Tests.Control\n")
        self.write("extensions/complexity/lint/GameTheoryComplexity/AxiomAudit.lean",
                   "import GameTheoryComplexity.LintAll\n"
                   "import GameTheoryComplexity.Tests.Control\n")
        self.assertEqual(audit.check_sources(self.root), [])

    def test_guarded_fixture_evaluations_consume_their_diagnostics(self):
        self.extension()
        path = "extensions/complexity/GameTheoryComplexity/Tests/Control.lean"
        self.write(path, "/-- info: true -/\n#guard_msgs in\n#eval true\n")
        self.write("extensions/complexity/lint/GameTheoryComplexity/AxiomAudit.lean",
                   "import GameTheoryComplexity.LintAll\n"
                   "import GameTheoryComplexity.Tests.Control\n")
        self.assertEqual(audit.check_sources(self.root), [])
        self.write(path, "#guard_msgs in\nexample : True := by trivial\n#eval true\n")
        self.assert_rejects("inspection command emits build diagnostics")

    def test_extension_comments_and_strings_do_not_trigger_shared_checks(self):
        self.extension('''import Lean
/- outer /- axiom -/ import GameTheory.Experimental.Control -/
-- sorry
def text := "admit native_decide import GameTheory.Frontier.Control"
''')
        self.assertEqual(audit.check_sources(self.root), [])

    def test_release_tag_must_match_pins(self):
        self.assertTrue(audit.check_version(self.root, "v4.35.0"))
        self.assertEqual(audit.check_version(self.root, "v4.34.1"), [])


@unittest.skipUnless(shutil.which("lake"), "Lake is required for diagnostic regression checks")
class DiagnosticAuditTests(unittest.TestCase):
    def test_dependency_warning_is_allowed_but_authored_warning_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage Probe\nlean_lib External\n"
                "@[default_target] lean_lib Probe where\n"
                "  leanOptions := #[⟨`warningAsError, true⟩]\n", encoding="utf-8")
            (root / "External.lean").write_text(
                'import Lean\nrun_cmd Lean.logWarning "dependency warning"\n')
            (root / "Probe.lean").write_text("import External\nexample : True := True.intro\n")
            result = subprocess.run(["lake", "build"], cwd=root, capture_output=True,
                                    text=True, encoding="utf-8")
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("dependency warning", result.stdout + result.stderr)
            self.assertEqual(audit.check_diagnostics(root, "Probe"), [])
            (root / "Probe.lean").write_text(
                'import External\nrun_cmd Lean.logWarning "authored warning"\n')
            result = subprocess.run(["lake", "build"], cwd=root, capture_output=True,
                                    text=True, encoding="utf-8")
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("authored warning", result.stdout + result.stderr)

    def test_transitive_axiom_check_rejects_a_private_dependency(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage Probe\nlean_lib GameTheory\nlean_lib Audit\n")
            (root / "GameTheory.lean").write_text(
                "private axiom hidden : False\ntheorem bad : False := hidden\n")
            implementation = (ROOT / "lint/GameTheory/AxiomAudit.lean").read_text(encoding="utf-8")
            body = implementation[implementation.index("open Lean in"):]
            (root / "Audit.lean").write_text(
                "import GameTheory\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\n" + body,
                encoding="utf-8")
            result = subprocess.run(["lake", "--iofail", "build", "Audit"], cwd=root,
                                    capture_output=True, text=True, encoding="utf-8")
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("depends on forbidden axiom", result.stdout + result.stderr)

    def test_import_all_audits_unused_private_modern_module_declarations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage Probe\n"
                "lean_lib External\nlean_lib GameTheory\nlean_lib Audit\n")
            (root / "External.lean").write_text(
                "module\nnamespace External\npublic axiom untrusted : False\nend External\n")
            (root / "GameTheory.lean").write_text(
                "module\nimport External\npublic theorem clean : True := True.intro\n"
                "private theorem hiddenBad : False := External.untrusted\n")
            implementation = (ROOT / "lint/GameTheory/AxiomAudit.lean").read_text(encoding="utf-8")
            body = implementation[implementation.index("open Lean in"):]
            helpers = "meta import Lean.Util.CollectAxioms\nmeta import Lean.Elab.Command\n"
            # The public theorem keeps the ordinary-import control nonempty.
            (root / "Audit.lean").write_text(
                "module\nimport GameTheory\n" + helpers + body, encoding="utf-8")
            ordinary = subprocess.run(["lake", "--iofail", "build", "Audit"], cwd=root,
                                      capture_output=True, text=True, encoding="utf-8")
            self.assertEqual(ordinary.returncode, 0, ordinary.stdout + ordinary.stderr)
            (root / "Audit.lean").write_text(
                "module\nimport all GameTheory\n" + helpers + body, encoding="utf-8")
            complete = subprocess.run(["lake", "--iofail", "build", "Audit"], cwd=root,
                                      capture_output=True, text=True, encoding="utf-8")
            output = complete.stdout + complete.stderr
            self.assertNotEqual(complete.returncode, 0, output)
            self.assertIn("hiddenBad", output)
            self.assertIn("depends on forbidden axiom External.untrusted", output)

    def test_cached_info_message_still_fails_strict_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (root / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage Probe\n@[default_target] lean_lib Probe\n")
            (root / "Probe.lean").write_text('import Lean\nrun_cmd Lean.logInfo "audit control"\n')
            first = subprocess.run(["lake", "build"], cwd=root, capture_output=True, text=True)
            self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
            self.assertTrue(any("audit control" in error
                                for error in audit.check_diagnostics(root, "Probe")))
            strict = subprocess.run(["lake", "--iofail", "build"], cwd=root, capture_output=True, text=True)
            self.assertNotEqual(strict.returncode, 0, strict.stdout + strict.stderr)
            self.assertIn("audit control", strict.stdout + strict.stderr)


if __name__ == "__main__":
    unittest.main()
