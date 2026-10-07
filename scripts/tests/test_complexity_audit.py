"""Check the optional complexity dependency boundary in tiny disposable packages."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
PWSH = shutil.which("pwsh")


@unittest.skipUnless(PWSH, "PowerShell 7 is required for complexity audits")
class ComplexityAuditTests(unittest.TestCase):
    def setUp(self):
        workspace = tempfile.TemporaryDirectory()
        self.addCleanup(workspace.cleanup)
        self.root = Path(workspace.name)
        self.write("GameTheory/Core/Fixture.lean", "import Mathlib\n")
        self.write("GameTheory.lean", "import GameTheory.Core.Fixture\n")
        self.write("lakefile.lean", "import Lake\nopen Lake DSL\npackage GameTheory\n")
        self.write("lean-toolchain", "leanprover/lean4:v4.34.1\n")
        self.write("extensions/complexity/lean-toolchain", "leanprover/lean4:v4.34.1\n")
        self.manifest("lake-manifest.json", [self.mathlib()])
        self.write("scripts/complexity-audit.ps1",
                   (ROOT / "scripts/complexity-audit.ps1").read_text(encoding="utf-8"))

    def write(self, relative, source):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    @staticmethod
    def mathlib(revision="mathlib-shared-pin"):
        return {"name": "mathlib", "type": "git", "rev": revision,
                "url": "https://github.com/leanprover-community/mathlib4"}

    def manifest(self, relative, packages):
        self.write(relative, json.dumps({"packages": packages}))

    def audit(self):
        return subprocess.run(
            [PWSH, "-NoProfile", "-File", str(self.root / "scripts/complexity-audit.ps1")],
            cwd=self.root, text=True, encoding="utf-8",
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )

    def assert_passes(self):
        result = self.audit()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("COMPLEXITY_OPTIONAL_BOUNDARY=PASS", result.stdout)

    def assert_rejects(self, reason):
        result = self.audit()
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(reason, result.stdout + result.stderr)
        self.assertNotIn("COMPLEXITY_OPTIONAL_BOUNDARY=PASS", result.stdout)

    def test_clean_base_without_extension_manifest(self):
        self.assert_passes()

    def test_clean_extension_with_shared_mathlib_and_public_upstream(self):
        self.manifest("extensions/complexity/lake-manifest.json", [self.mathlib(), {
            "name": "complexitylib", "type": "git", "rev": "public-pin",
            "url": "https://github.com/SamuelSchlesinger/complexitylib",
        }])
        self.assert_passes()

    def test_lean_comments_and_escaped_strings_do_not_create_imports(self):
        self.write("GameTheory/Core/Fixture.lean", '''import Mathlib
-- import Complexitylib.Classes.Randomized
/- import GameTheory.Complexity.SampleTest
   /- public import Cslib.Models -/
   import Complexitylib
-/
def ignoredString := "escaped \\" quote; import Complexitylib.Classes.Randomized"
def multilineString := "
import GameTheory.Complexity.SampleTest
"
''')
        self.assert_passes()

    def test_lake_comments_and_strings_do_not_create_dependencies(self):
        self.write("lakefile.lean", '''import Lake
open Lake DSL
package GameTheory
-- require complexitylib from git "ignored"
/-
require cslib from git "ignored"
-/
def ignoredString := "
require GameTheoryComplexity from git \\"ignored\\"
"
''')
        self.assert_passes()

    def test_rejects_every_module_in_multimodule_import(self):
        self.write("GameTheory/Core/Fixture.lean",
                   "import Mathlib Complexitylib.Classes.Randomized\n")
        self.assert_rejects("Base module imports optional complexity surface")

    def test_rejects_meta_imports_and_quoted_module_components(self):
        for imported in [
            "meta import GameTheoryComplexity.SampleTest",
            "public meta import Complexitylib.Classes.Randomized",
            "meta import all Cslib.Models",
            "import «GameTheoryComplexity».SampleTest",
            "public import «Complexitylib».Classes.Randomized",
            "public meta import «GameTheory».«Complexity».SampleTest",
            "import «Cslib».«Models With Spaces»",
        ]:
            with self.subTest(imported=imported):
                self.write("GameTheory/Core/Fixture.lean", f"module\n{imported}\n")
                self.assert_rejects("Base module imports optional complexity surface")

    def test_quoted_literal_dot_is_not_a_module_component_separator(self):
        self.write("GameTheory/Core/Fixture.lean",
                   "module\nimport «GameTheoryComplexity.SampleTest»\n")
        self.assert_passes()

    def test_comment_markers_and_quotes_inside_identifiers_are_literal(self):
        self.write("GameTheory/Core/Fixture.lean", '''module
import «GameTheoryComplexity--ordinary-module»
import «GameTheoryComplexity/-ordinary-/module»
import «GameTheoryComplexity"ordinary"module»
''')
        self.assert_passes()

    def test_meta_imports_inside_comments_and_strings_are_ignored(self):
        self.write("GameTheory/Core/Fixture.lean", '''module
meta import Lean
/- public meta import «Complexitylib».Classes.Randomized -/
def ignoredString := "
meta import GameTheoryComplexity.SampleTest
"
''')
        self.assert_passes()

    def test_comments_cannot_join_import_tokens_and_hide_dependencies(self):
        self.write("GameTheory/Core/Fixture.lean",
                   "import/- separator -/Complexitylib.Classes.Randomized\n")
        self.assert_rejects("Base module imports optional complexity surface")

    def test_rejects_companion_and_cslib_imports_in_root_and_leaf(self):
        for relative, source in [
            ("GameTheory.lean", "public import GameTheory.Complexity.SampleTest\n"),
            ("GameTheory.lean", "import GameTheoryComplexity.SampleTest\n"),
            ("GameTheory/Core/Fixture.lean", "import Cslib.Models\n"),
        ]:
            with self.subTest(relative=relative):
                self.write(relative, source)
                self.assert_rejects("Base module imports optional complexity surface")
                self.write(relative, "import Mathlib\n")

    def test_rejects_lake_require_even_with_unrefreshed_manifest(self):
        for dependency in ["complexitylib", "cslib", "GameTheoryComplexity",
                           '"owner" / "complexitylib"']:
            with self.subTest(dependency=dependency):
                self.write("lakefile.lean", f'import Lake\nrequire {dependency} from git "url"\n')
                self.assert_rejects("Base Lake configuration directly requires an optional dependency")

    def test_rejects_root_manifest_optional_dependencies(self):
        for dependency in ["complexitylib", "cslib", "GameTheoryComplexity"]:
            with self.subTest(dependency=dependency):
                self.manifest("lake-manifest.json", [self.mathlib(), {"name": dependency}])
                self.assert_rejects("Base manifest requires optional dependency")

    def test_rejects_different_toolchains(self):
        self.write("extensions/complexity/lean-toolchain", "leanprover/lean4:v4.35.0-rc3\n")
        self.assert_rejects("Base and complexity toolchains differ")

    def test_rejects_different_or_missing_mathlib_pins(self):
        for packages in [[self.mathlib("another-pin")], [], [self.mathlib(), self.mathlib()]]:
            with self.subTest(packages=packages):
                self.manifest("extensions/complexity/lake-manifest.json", packages)
                self.assert_rejects("Base and complexity Mathlib pins differ")

    def test_rejects_private_compatibility_fork(self):
        self.manifest("extensions/complexity/lake-manifest.json", [self.mathlib(), {
            "name": "complexitylib", "type": "git", "rev": "private-pin",
            "url": "https://github.com/gili-b/VI-NP-verification",
        }])
        self.assert_rejects("Private compatibility fork is not a distributable dependency")

    def test_rejects_new_public_module_omitted_from_lint_driver(self):
        self.write("extensions/complexity/GameTheoryComplexity/Known.lean", "import Init\n")
        self.write("extensions/complexity/lint/GameTheoryComplexity/LintAll.lean",
                   "import GameTheoryComplexity.Known\n")
        self.assert_passes()
        self.write("extensions/complexity/GameTheoryComplexity/NewLeaf.lean",
                   "namespace GameTheory.Complexity\naxiom unaudited : False\n")
        self.assert_rejects("Complexity public module missing from lint imports")

    def test_lint_coverage_includes_umbrella_and_requires_driver(self):
        self.write("extensions/complexity/GameTheoryComplexity.lean", "import Init\n")
        self.assert_rejects("Complexity public modules have no lint import driver")
        self.write("extensions/complexity/lint/GameTheoryComplexity/LintAll.lean", "import Init\n")
        self.assert_rejects("Complexity public module missing from lint imports")
        self.write("extensions/complexity/lint/GameTheoryComplexity/LintAll.lean",
                   "import «GameTheoryComplexity»\n")
        self.assert_passes()

    def test_lint_coverage_excludes_opt_in_experiments_and_test_fixtures(self):
        for module in ["Tests/Consumer", "Experimental/Spike", "ConsumerTest"]:
            self.write(f"extensions/complexity/GameTheoryComplexity/{module}.lean", "import Init\n")
        self.assert_passes()


if __name__ == "__main__":
    unittest.main()
