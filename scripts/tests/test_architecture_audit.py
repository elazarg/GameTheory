"""Exercise audit policy against mutations in a disposable source snapshot."""

from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
PWSH = shutil.which("pwsh")


@unittest.skipUnless(PWSH, "PowerShell 7 is required for architecture audits")
class ArchitectureAuditTests(unittest.TestCase):
    def test_proof_enumeration_and_named_owners_preserve_executable_boundaries(self):
        with tempfile.TemporaryDirectory() as workspace:
            root = Path(workspace)
            shutil.copytree(ROOT / "GameTheory", root / "GameTheory")
            shutil.copy2(ROOT / "GameTheory.lean", root / "GameTheory.lean")
            (root / "scripts").mkdir()
            shutil.copy2(ROOT / "scripts/phase2-audit.ps1", root / "scripts")

            def write(relative, source):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")

            def audit():
                result = subprocess.run(
                    [PWSH, "-NoProfile", "-File", str(root / "scripts/phase2-audit.ps1")],
                    cwd=root, check=True, text=True, encoding="utf-8",
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                return {key: int(value) for key, value in re.findall(
                    r"^([A-Z_0-9]+)=(\d+)$", result.stdout, re.MULTILINE)}

            # A fresh proof leaf may enumerate a Finite carrier locally, but is
            # not automatically authorized to expose raw probability weights.
            write("GameTheory/Core/AuditProof.lean", """
theorem proof [Finite A] : True := by
  let _ : Fintype A := Fintype.ofFinite A
  trivial
-- Function.update Fintype.ofFinite ENNReal
/- outer /- inner ENNReal -/ Fintype.ofFinite -/
def ignoredString := "Function.update Fintype.ofFinite ENNReal"
"""
            )
            baseline = audit()
            self.assertEqual(baseline["ALGORITHM_FINTYPE_OF_FINITE"], 0)
            self.assertEqual(baseline["WEIGHT_INTERNAL_TOKENS_OUTSIDE_OWNERS"], 0)
            self.assertEqual(baseline["ANALYSIS_IMPORTED_OUTSIDE_ROOT"], 0)

            algorithm = root / "GameTheory/Finite/Algorithm.lean"
            with algorithm.open("a", encoding="utf-8") as stream:
                stream.write("\ndef forbiddenEnumeration := Fintype.ofFinite A\n")
            write("GameTheory/Math/Probability/AuditUnowned.lean",
                  "def forbiddenWeight := ENNReal.ofReal 1\n")
            write("GameTheory/Tests/AuditAnalysisImport.lean",
                  "import GameTheory.Analysis.Nash\n")
            write("GameTheory/Core/AuditUpdate.lean",
                  "def forbiddenUpdate := Function.update profile who action\n")
            mutated = audit()

            self.assertEqual(mutated["ALGORITHM_FINTYPE_OF_FINITE"], 1)
            self.assertEqual(mutated["FINTYPE_OF_FINITE"], baseline["FINTYPE_OF_FINITE"] + 1)
            self.assertEqual(mutated["WEIGHT_INTERNAL_TOKENS_OUTSIDE_OWNERS"], 1)
            self.assertEqual(mutated["ANALYSIS_IMPORTED_OUTSIDE_ROOT"], 1)
            self.assertEqual(mutated["FUNCTION_UPDATE_OUTSIDE_PROFILE"],
                             baseline["FUNCTION_UPDATE_OUTSIDE_PROFILE"] + 1)


if __name__ == "__main__":
    unittest.main()
