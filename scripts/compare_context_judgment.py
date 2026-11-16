#!/usr/bin/env python3
"""Reproduce EXP-176 direct/record guarded-comparison measurements.

Run from the repository root without concurrent builds or source edits.
Generated variants, diagnostics and timings remain under ignored scratch.
"""
from pathlib import Path
import json
import re
import runpy
import statistics
import subprocess
import time

root = Path('.codex/scratch/exp176')
root.mkdir(parents=True, exist_ok=True)
authored = Path('GameTheory/Experimental/Exp176/Comparison.lean')
source = authored if authored.exists() else root / 'ComparisonClients.lean'
mask = runpy.run_path('scripts/audit.py')['source_code']
text = mask(source.read_text(encoding='utf-8'), keep_strings=True)

def remove_decl(text, name):
    match = re.search(r'(?m)^(?:def|theorem) ' + re.escape(name) + r'(?=[\s{(:])', text)
    assert match, name
    rest = text[match.end():]
    end = re.search(r'(?m)^(?:def|theorem|structure|namespace|end)\b', rest)
    assert end, name
    return text[:match.start()] + rest[end.start():]

start = text.index('structure ComparisonContext')
end = text.index('end ComparisonContext', start) + len('end ComparisonContext')
direct = text[:start] + text[end:]
for name in ['context_transport_via_record', 'beliefComparison', 'belief_record_optimal',
             'targetBeliefComparison', 'target_belief_record_optimal']:
    direct = remove_decl(direct, name)
record = text.replace(':=\n  belief_direct_optimal', ":= by\n  refine ⟨trivial, fun _ _ => trivial, ?_⟩\n  intro alternative _\n  exact Or.inl beliefOutcome_true_supported")
for name in ['context_optimal_iff_predicate', 'context_transport_via_predicate',
             'belief_direct_optimal', 'target_belief_direct_optimal']:
    record = remove_decl(record, name)

counts = {}
for label, code in [('Direct', direct), ('Record', record)]:
    (root / (label + 'Comparison.lean')).write_text(code, encoding='utf-8')
    counts[label] = sum(bool(line.strip()) for line in code.splitlines())
(root / 'source-counts.json').write_text(json.dumps(counts, indent=2), encoding='utf-8')
print(json.dumps({'nonblank_code_lines': counts}), flush=True)
results = []
for repeat in range(3):
    for label in (['Direct', 'Record'] if repeat % 2 == 0 else ['Record', 'Direct']):
        path = root / (label + 'Comparison.lean')
        command = ['lake', 'env', 'lean', '-DwarningAsError=true',
                   '-DrelaxedAutoImplicit=false', '-Dlinter.checkUnivs=false',
                   '-DmaxSynthPendingDepth=3', str(path)]
        start = time.perf_counter()
        run = subprocess.run(command, capture_output=True, text=True, encoding='utf-8')
        elapsed = time.perf_counter() - start
        (root / (label + str(repeat) + '.log')).write_text(run.stdout + run.stderr,
                                                       encoding='utf-8')
        row = dict(variant=label, repeat=repeat, seconds=elapsed, returncode=run.returncode)
        results.append(row)
        (root / 'timings.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
        print(json.dumps(row), flush=True)
        if run.returncode:
            raise SystemExit(run.stdout + run.stderr)
print(json.dumps({label: statistics.median(r['seconds'] for r in results
                  if r['variant'] == label) for label in counts}), flush=True)
