#!/usr/bin/env python3
"""Run isolated clean/incremental native-dispatch tests; retain exact command logs."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'evidence' / 'milestone0'
OUT.mkdir(parents=True, exist_ok=True)
(OUT / 'summary.json').unlink(missing_ok=True)
work = Path(tempfile.mkdtemp(prefix='api-builder-smoke-'))
repo = work / 'repo'
shutil.copytree(ROOT, repo, ignore=shutil.ignore_patterns('.git', '.lake', 'evidence', '__pycache__'))
# The old smoke seam is intentionally Lean-only, independent of mathematical recipes.
(repo / 'lakefile.toml').write_text('name = "apiBuilder"\n[[lean_lib]]\nname = "ApiBuilder"\n')
(repo / 'lake-manifest.json').unlink(missing_ok=True)
consumer = repo / 'tests/consumer'
records = []

def run(label, args, expected=0, contains=None):
    p = subprocess.run(args, cwd=consumer, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / (label + '.log')).write_text('$ ' + ' '.join(args) + '\n' + p.stdout + f'\nexit: {p.returncode}\n')
    records.append({'test': label, 'command': args, 'exit': p.returncode})
    assert (p.returncode == 0) == (expected == 0), (label, p.stdout)
    if contains is not None:
        assert contains in p.stdout, (label, p.stdout)
    return p.stdout

def value(label, expected):
    text = run(label, ['lake', 'env', 'lean', 'Check.lean'])
    assert text.strip() == str(expected), (label, text)

try:
    run('toolchain', ['lean', '--version'], contains='b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a')
    before = hashlib.sha256((consumer / 'SmokeConsumer.lean').read_bytes()).hexdigest()
    run('clean-build', ['lake', 'build'])
    value('baseline-value', 21)
    # Prove the checker rejects a stale result before changing any source.
    stale = consumer / 'Stale.lean'
    stale.write_text('import SmokeConsumer\nexample : Generated.value = 22 := rfl\n')
    run('stale-output-control', ['lake', 'env', 'lean', 'Stale.lean'], 1, 'Type mismatch')
    provider = repo / 'tests/provider/SmokeProvider.lean'
    provider.write_text(provider.read_text().replace('helperValue + 1', 'helperValue + 2'))
    run('recipe-body-rebuild', ['lake', 'build'])
    value('recipe-body-value', 22)
    run('updated-proof', ['lake', 'env', 'lean', 'Stale.lean'])
    helper = repo / 'tests/provider/SmokeProvider/Helper.lean'
    helper.write_text(helper.read_text().replace('Nat := 20', 'Nat := 30'))
    run('helper-body-rebuild', ['lake', 'build'])
    value('helper-body-value', 32)
    assert hashlib.sha256((consumer / 'SmokeConsumer.lean').read_bytes()).hexdigest() == before
    run('wrong-entrypoint', ['lake', 'env', 'lean', 'Wrong.lean'], 1, 'unexpected type')
    run('logged-failure', ['lake', 'env', 'lean', 'Failure.lean'], 1, 'intentional provider generation failure')
    (consumer / 'Unused.lean').write_text('module\nmeta import ApiBuilder.Elab\nmeta import SmokeProvider\nopen Lean Elab Command in\nrun_cmd do\n  if (← getEnv).contains `Generated.value then\n    throwError "import activated generated declaration"\n')
    run('unused-import', ['lake', 'env', 'lean', 'Unused.lean'])
    shutil.copyfile(consumer / 'lake-manifest.json', OUT / 'lake-manifest.json')
    (OUT / 'summary.json').write_text(json.dumps({'consumer_sha256': before, 'tests': records}, indent=2) + '\n')
    print('PASS: clean build, fresh import, 21 → 22 → 32, stale control, failures, unused import')
finally:
    print('Isolated test workspace:', work)
