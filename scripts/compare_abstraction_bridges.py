#!/usr/bin/env python3
"""Reproduce EXP-173 direct/coverage whole-module process comparisons.

Run from the repository root with no concurrent builds or edits. Both variants
compile the same generalized statements; generated sources and logs remain in
ignored .codex/scratch/exp173. Requires the repository's pinned Lean environment.
"""
from pathlib import Path
import subprocess, time, json
root = Path('.codex/scratch/exp173')
root.mkdir(parents=True, exist_ok=True)
files = {'Kuhn': Path('GameTheory/Languages/EFG/Kuhn.lean'), 'Bayesian': Path('GameTheory/Languages/Bayesian/Strategic.lean')}
replacements = {
'Kuhn': [
('''  refine IsNash.of_coverage (source := G.toBehavioralGameForm horizon)
    (sourcePrefers := prefers) (profile := behavioral) ?_ hnash
  intro who replacement
  refine ⟨InformationModel.MixedPolicy.toBehavioral
    (M := G.information) replacement, ?_⟩
  intro hcomparison''', '''  rw [isNash_iff] at hnash ⊢
  intro who replacement
  have hcomparison := hnash who (InformationModel.MixedPolicy.toBehavioral
    (M := G.information) replacement)'''),
('''  refine IsNash.of_coverage (source := (G.toGameForm horizon).mixed)
    (sourcePrefers := prefers) (profile := mixed) ?_ hnash
  intro who replacement
  refine ⟨replacement.toMixed, ?_⟩
  intro hcomparison''', '''  rw [isNash_iff] at hnash ⊢
  intro who replacement
  have hcomparison := hnash who replacement.toMixed''')],
'Bayesian': [
('''    refine IsNash.of_coverage (source := toProtocolForm B)
      (sourcePrefers := prefers) (profile := policies) ?_ hnash
    intro who replacement
    refine ⟨Policy.ofPlan replacement, ?_⟩
    intro hcomparison''', '''    rw [isNash_iff] at hnash ⊢
    intro who replacement
    have hcomparison := hnash who (Policy.ofPlan replacement)'''),
('''    refine IsNash.of_coverage (source := B.toForm)
      (sourcePrefers := Preference.comapOutcome some prefers)
      (profile := planOfPolicyProfile B policies) ?_ hnash
    intro who replacement
    refine ⟨Policy.toPlan replacement, ?_⟩
    intro hcomparison''', '''    rw [isNash_iff] at hnash ⊢
    intro who replacement
    have hcomparison := hnash who (Policy.toPlan replacement)''')]
}
for label,p in files.items():
    coverage = p.read_text(encoding='utf-8')
    for old,new in replacements[label]:
        if old not in coverage:
            assert new in coverage, label
            coverage = coverage.replace(new, old)
    direct = coverage
    for old,new in replacements[label]:
        assert old in direct, label
        direct = direct.replace(old,new)
    (root / (label+'Coverage.lean')).write_text(coverage,encoding='utf-8')
    (root / (label+'Direct.lean')).write_text(direct,encoding='utf-8')
results=[]
for repeat in range(3):
    for label in files:
        for variant in (['Direct','Coverage'] if repeat % 2 == 0 else ['Coverage','Direct']):
            p=root / (label+variant+'.lean')
            command=['lake','env','lean','-DwarningAsError=true','-DrelaxedAutoImplicit=false','-Dlinter.checkUnivs=false','-DmaxSynthPendingDepth=3',str(p)]
            start=time.perf_counter()
            run=subprocess.run(command,capture_output=True,text=True,encoding='utf-8')
            elapsed=time.perf_counter()-start
            (root / (label+variant+str(repeat)+'.log')).write_text(run.stdout+run.stderr,encoding='utf-8')
            result=dict(client=label,variant=variant,repeat=repeat,seconds=elapsed,returncode=run.returncode)
            results.append(result)
            print(json.dumps(result),flush=True)
            (root/'timings.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
            if run.returncode: raise SystemExit(run.stdout+run.stderr)
