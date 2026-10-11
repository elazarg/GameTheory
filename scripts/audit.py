#!/usr/bin/env python3
"""Check maintained boundaries, then build, lint and audit axioms.

Run `python scripts/audit.py`; use --source-only during editing, or --complexity
to check/build the optional package (resolved beforehand by Lake).
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
NAME = re.compile(r"(?:«[^»\n]*»|[^\W\d][\w']*)(?:\.(?:«[^»\n]*»|[^\W\d][\w']*))*")
RAW_STRING = re.compile(r'r(#+)"')
CHARACTER = re.compile(r"'(?:\\[^\n]|[^'\\\n])'")
IMPORT = re.compile(r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\r\n]+)")
OPTIONAL = {"GameTheoryComplexity", "Complexitylib", "Cslib"}
# Execution leaves, rather than correctness/proof modules in the same directory.
EXECUTABLE = {
    "GameTheory.Finite.Algorithm", "GameTheory.Finite.BimatrixCertificate",
    "GameTheory.Finite.BimatrixNashCertificate", "GameTheory.Finite.BimatrixTable",
    "GameTheory.Finite.BimatrixPathBinaryCodec",
    "GameTheory.Finite.BimatrixComputedPivot",
    "GameTheory.Finite.BimatrixComputedOrientation",
    "GameTheory.Math.FiniteLexicographicCompare",
    "GameTheory.Math.FiniteMinimumScan",
    "GameTheory.Math.IntegerCramerComputation",
    "GameTheory.Math.IntegerDictionaryComputation",
    "GameTheory.Math.IntegerDictionaryFeasibility",
    "GameTheory.Math.IntegerRatioSelection",
    "GameTheory.Math.ScalarInequalities",
    "GameTheory.Math.TabulatedBirdDeterminant",
    "GameTheory.Mechanism.Knapsack.Aggregate",
    "GameTheory.Mechanism.Knapsack.Algorithm",
    "GameTheory.Mechanism.Knapsack.ApproximationAlgorithm",
}
# These owners align dependent action fibers across structural restrictions.
EQ_MP_OWNERS = {("GameTheory", "Protocol", "ActionRestriction"),
                ("GameTheory", "Protocol", "RestrictionProfile")}


def source_code(source, keep_strings=False):
    """Mask nested comments and strings; preserve lines and quoted identifiers."""
    out = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif source[i] == "«":
            end = source.find("»", i + 1)
            i = len(source) if end < 0 else end + 1
            continue
        elif match := CHARACTER.match(source, i):
            i = match.end()
        elif match := RAW_STRING.match(source, i):
            end = source.find('"' + match[1], i + len(match[0]))
            i = len(source) if end < 0 else end + 1 + len(match[1])
            if keep_strings:
                for j in range(start, min(i, len(source))):
                    if out[j] == "\n":
                        out[j] = "\\n"
                continue
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            if keep_strings:
                for j in range(start, min(i, len(source))):
                    if out[j] == "\n":
                        out[j] = "\\n"
                continue
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)


def imports(source):
    for header in IMPORT.finditer(source_code(source)):
        for name in NAME.findall(header[1]):
            yield tuple(part[1:-1] if part.startswith("«") else part
                        for part in re.findall(r"«[^»]*»|[^.]+", name))


def is_fixture(module):
    # These names denote statistical sample tests, not regression fixtures.
    if module in {("GameTheoryComplexity", "SampleTest"),
                  ("GameTheoryComplexity", "Backend", "CompiledSampleTest")}:
        return False
    return "Tests" in module or "Experimental" in module or module[-1].endswith("Test")


def modules(root, namespace):
    paths = sorted((root / namespace).rglob("*.lean"))
    if (root / f"{namespace}.lean").exists():
        paths.append(root / f"{namespace}.lean")
    return {tuple(p.relative_to(root).with_suffix("").parts): p for p in paths}


def check_sources(root):
    errors = []
    sources = modules(root, "GameTheory")
    check_module_sources(root, sources, errors)
    check_scope(root, "GameTheory", sources, errors)
    check_optional(root, errors)
    return errors


def check_module_sources(root, sources, errors, base=True):
    """Share trust checks; keep the base package's structural rules scoped."""
    for module, path in sources.items():
        text = path.read_text(encoding="utf-8")
        code = source_code(text)
        tokens = set(NAME.findall(code))
        label = path.relative_to(root).as_posix()
        for token in {"sorry", "admit", "axiom", "native_decide", "FinDist"} & tokens:
            errors.append(f"{label}: forbidden token {token}")
        if module != ("GameTheory", "Core", "Signature") and "Function.update" in tokens:
            errors.append(f"{label}: use Profile.update")
        if base and "Experimental" not in module:
            transports = {"cast", "HEq", "Eq.ndrec", "Eq.mp", "Eq.mpr", "Eq.rec"} & tokens
            if module in EQ_MP_OWNERS:
                transports.discard("Eq.mp")
            if module != ("GameTheory", "Core", "Signature") and (transports or "▸" in code):
                errors.append(f"{label}: equality transport outside the profile owner")
            for line, value in enumerate(text.splitlines(), 1):
                if len(value) > 100:
                    errors.append(f"{label}:{line}: line exceeds 100 columns")
        for command in re.finditer(r"(?m)^[ \t]*#(?:eval|print|check|reduce)\b", code):
            # Guarded fixture controls consume their expected diagnostics.
            if is_fixture(module) and re.search(r"#guard_msgs\s+in\s*$", code[:command.start()]):
                continue
            errors.append(f"{label}: inspection command emits build diagnostics")
            break
        if ".".join(module) in EXECUTABLE:
            for token in {"classical", "Classical", "noncomputable", "Fintype.ofFinite"} & tokens:
                errors.append(f"{label}: executable leaf uses {token}")
            if any(token.startswith("Classical.") for token in tokens):
                errors.append(f"{label}: executable leaf uses Classical")
        for dependency in imports(text):
            reason = boundary_violation(module, dependency, base=base)
            if reason:
                errors.append(f"{label}: {reason}: {'.'.join(dependency)}")


def trust_violation(module, dep):
    """Public sources in either package cannot depend on excluded surfaces."""
    if "Experimental" in module:
        return None
    if dep[0] not in {"GameTheory", "GameTheoryComplexity"}:
        return None
    if len(dep) > 1 and dep[1] in {"Frontier", "Challenges"}:
        return "trusted module imports an excluded trust surface"
    if not is_fixture(module) and is_fixture(dep):
        return "library module imports a fixture"
    return None


def boundary_violation(module, dep, base=True):
    """Every forbidden project path has an authored edge checked here."""
    if base and (dep[0] in OPTIONAL or dep[:2] == ("GameTheory", "Complexity")):
        return "base module imports optional complexity surface"
    if dep[0] == "FixedPointTheorems" or dep[:2] == ("GameTheory", "Analysis"):
        if module[:2] != ("GameTheory", "Analysis"):
            return "Analysis/fixed-point dependency outside Analysis"
    if "Experimental" in module:
        return None
    if reason := trust_violation(module, dep):
        return reason
    if not base:
        return None
    branch = module[1] if len(module) > 1 else ""
    if dep[0] == "GameTheory":
        target = dep[1] if len(dep) > 1 else ""
        forbidden = {
            "Math": {"Core", "Protocol", "Languages", "Finite", "Analysis", "Repeated",
                     "Mechanism", "Cooperative", "Congestion", "Stochastic", "Epistemic",
                     "Evolutionary", ""},
            "Core": {"Protocol", "Languages", "Finite", "Analysis"},
            "Protocol": {"Languages", "Finite", "Analysis"},
            "Languages": {"Analysis", "Finite"},
            "Epistemic": {"Core", "Protocol", "Languages", "Finite", "Analysis"},
            "Evolutionary": {"Protocol", "Languages", "Finite", "Analysis"},
            "Repeated": {"Languages", "Finite", "Analysis"},
            "Stochastic": {"Languages", "Finite", "Analysis"},
        }
        if (branch == "Math" and target != "Math") or target in forbidden.get(branch, set()):
            return f"{branch} crosses its dependency boundary"
    if branch == "Core" and dep[:2] in {
            ("Mathlib", "Analysis"), ("Mathlib", "Topology"),
            ("Mathlib", "Dynamics"), ("Mathlib", "Geometry")}:
        return "Core directly imports analytic mathematics"
    if ".".join(module) in EXECUTABLE and (
            dep[:3] == ("GameTheory", "Math", "Probability") or
            dep[:2] in {("Mathlib", "Probability"), ("Mathlib", "Analysis"),
                        ("Mathlib", "Topology"), ("Mathlib", "MeasureTheory")}):
        return "executable leaf imports probability or analysis"
    return None


def check_scope(root, namespace, sources, errors):
    lint = root / "lint" / namespace / "LintAll.lean"
    if not lint.exists():
        errors.append(f"{namespace}: missing lint driver")
        return
    lint_imports = set(imports(lint.read_text(encoding="utf-8")))
    public = {m for m in sources if not is_fixture(m)}
    for module in sorted(public - lint_imports):
        errors.append(f"{namespace}: public module missing from lint imports: {'.'.join(module)}")
    for module in sorted(lint_imports - public):
        errors.append(f"{namespace}: stale or fixture lint import: {'.'.join(module)}")
    axiom = root / "lint" / namespace / "AxiomAudit.lean"
    if not axiom.exists():
        errors.append(f"{namespace}: missing axiom audit")
        return
    covered = lint_imports | set(imports(axiom.read_text(encoding="utf-8")))
    for module in sorted(sources.keys() - covered):
        errors.append(f"{namespace}: module missing from axiom audit: {'.'.join(module)}")


def check_optional(root, errors):
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    for dep in manifest["packages"]:
        if dep["name"].lower() in {n.lower() for n in OPTIONAL}:
            errors.append(f"base manifest requires optional dependency: {dep['name']}")
    config = source_code((root / "lakefile.lean").read_text(encoding="utf-8"), keep_strings=True)
    if re.search(r'(?m)^\s*require\s+(?:(?:"[^"\n]+"|[\w-]+)\s*/\s*)?["«]?'
                 r'(?:complexitylib|cslib|GameTheoryComplexity)(?:["»\s]|$)', config):
        errors.append("base Lake configuration directly requires an optional dependency")
    extension = root / "extensions/complexity"
    if not extension.exists():
        return
    if (root / "lean-toolchain").read_text().strip() != (extension / "lean-toolchain").read_text().strip():
        errors.append("base and complexity toolchains differ")
    sources = modules(extension, "GameTheoryComplexity")
    check_module_sources(extension, sources, errors, base=False)
    check_scope(extension, "GameTheoryComplexity", sources, errors)
    if (extension / "lake-manifest.json").exists():
        other = json.loads((extension / "lake-manifest.json").read_text())["packages"]
        base_pins = [d["rev"] for d in manifest["packages"] if d["name"] == "mathlib"]
        pins = [d["rev"] for d in other if d["name"] == "mathlib"]
        if len(base_pins) != 1 or pins != base_pins:
            errors.append("base and complexity Mathlib pins differ")
        if any("gili-b/VI-NP-verification" in d.get("url", "") for d in other):
            errors.append("private compatibility fork is not a distributable dependency")


def check_version(root, expected=None):
    config = source_code((root / "lakefile.lean").read_text(encoding="utf-8"), keep_strings=True)
    toolchain = (root / "lean-toolchain").read_text().strip().removeprefix("leanprover/lean4:v")
    package = re.findall(r'(?m)^\s*version\s*:=\s*v!"([^"]+)"', config)
    mathlib = re.findall(r'(?m)^\s*require\s+"leanprover-community"\s*/\s*"mathlib"\s*@\s*git\s*"v([^"]+)"', config)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    pins = [p.get("inputRev", "").removeprefix("v") for p in manifest["packages"] if p["name"] == "mathlib"]
    version = expected.removeprefix("v") if expected else toolchain
    if package != [version] or mathlib != [version] or pins != [version] or toolchain != version:
        return [f"package, Lean, Mathlib and release versions must all equal {version}"]
    return []


def check_diagnostics(root, namespace):
    """Reject first-party info/warnings, including those stored by cached builds."""
    sources = modules(root, namespace)
    sources.update(modules(root / "lint", namespace))
    errors = []
    for module in sources:
        trace = root / ".lake/build/lib/lean" / Path(*module).with_suffix(".trace")
        if not trace.exists():
            errors.append(f"{'.'.join(module)}: missing build diagnostic trace")
            continue
        log = json.loads(trace.read_text(encoding="utf-8"))["log"]
        for entry in log:
            if entry["level"] != "trace":
                errors.append(f"{'.'.join(module)}: {entry['level']}: {entry['message']}")
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true", help="skip Lake build, lint and axiom audit")
    parser.add_argument("--complexity", action="store_true", help="build/lint the optional package")
    parser.add_argument("--release-version", help="require this release tag's version")
    args = parser.parse_args()
    errors = check_sources(ROOT) + check_version(ROOT, args.release_version)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    if not args.source_only:
        root, namespace = (ROOT / "extensions/complexity", "GameTheoryComplexity") if args.complexity else (ROOT, "GameTheory")
        config = []
        if args.complexity:
            manifest = json.loads((root / "lake-manifest.json").read_text())
            if any(p["name"] == "GameTheory" and p["type"] == "path"
                   for p in manifest["packages"]):
                config = ["-KgameTheoryPath=../.."]
        # The upstream complexity package emits proof suggestions. Its warnings
        # still fail; all first-party diagnostics are checked from Lake's logs.
        strict = "--wfail" if args.complexity else "--iofail"
        for arguments in [
            ["build"], ["build", f"{namespace}.LintAll", f"{namespace}.AxiomAudit"], ["lint"],
        ]:
            command = ["lake", strict, *config, *arguments]
            print("+ " + " ".join(command), flush=True)
            subprocess.run(command, cwd=root, check=True)
        errors = check_diagnostics(root, namespace)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
    print("Audit passed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
