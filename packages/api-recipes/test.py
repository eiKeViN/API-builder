#!/usr/bin/env python3
"""Validate four recipe implementations, public contracts and external use."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'evidence'
OUT.mkdir(exist_ok=True)
ENV = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE='1')
ROWS = []
SOURCES = [ROOT/'ApiRecipes.lean', *sorted((ROOT/'ApiRecipes').glob('*.lean'))]
def hashes(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
FROZEN = hashes(SOURCES)

def run(label, command, *, cwd=ROOT, negative=False, need=()):
    start = time.monotonic()
    p = subprocess.run(command, cwd=cwd, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT/(label+'.log')).write_text('$ '+' '.join(command)+'\n'+p.stdout+f'\nexit: {p.returncode}\n')
    ok = (p.returncode != 0 if negative else p.returncode == 0) and all(s in p.stdout for s in need)
    if negative:
        ok &= not any(s in p.stdout for s in ['unexpected surviving output', 'missing recovered output',
            'unexpected token', 'unknown module prefix', 'object file', 'has not been implemented'])
    else:
        ok &= 'warning:' not in p.stdout
    ROWS.append(dict(case=label, expected_failure=negative, passed=ok, returncode=p.returncode,
        required_diagnostics=list(need), seconds=round(time.monotonic()-start, 3)))
    (OUT/'results.json').write_text(json.dumps(ROWS, indent=2)+'\n')
    print(('PASS ' if ok else 'FAIL ')+label, flush=True)
    assert hashes(SOURCES) == FROZEN, 'producer sources changed during validation'
    if not ok:
        print(p.stdout, flush=True)
        raise SystemExit(1)

def prepare_external(path):
    packages = path/'.lake/packages'
    packages.parent.mkdir(exist_ok=True)
    if not packages.exists():
        packages.symlink_to((ROOT/'.lake/packages').resolve(), target_is_directory=True)
    run(path.name+'-update', ['lake', 'update'], cwd=path)

run('library-and-contracts', ['lake', 'build', 'ApiRecipes', 'ApiRecipesTests.Contracts'])
for name, need in [
    ('NotIff', ('expected an explicit P ↔ Q contract', 'ROLLBACK_OK')),
    ('Sorry', ("forbidden axiom 'sorryAx'", 'ROLLBACK_OK')),
    ('ObservationCollision', ("output collision 'Bad.of_spec'", 'ROLLBACK_OK')),
    ('DuplicateSelection', ("duplicate role 'zero'", 'ROLLBACK_OK')),
    ('UnknownSelection', ("unsupported role 'convolution'", 'ROLLBACK_OK')),
    ('EmptySelection', ('select at least one role', 'ROLLBACK_OK')),
    ('NonPointwiseMultiplication', ('IsMulApply', "failed to generate 'Bad.mul_apply'", 'ROLLBACK_OK', 'RECOVERY_OK')),
    ('MissingEstimate', ("missing field 'estimate'", 'ROLLBACK_OK')),
    ('DuplicateField', ("duplicate field 'bound'", 'ROLLBACK_OK')),
    ('UnknownField', ("unknown field 'typo'", 'ROLLBACK_OK')),
    ('LateBoundFailure', ("failed to generate 'Bad.norm_le'", 'ROLLBACK_OK', 'RECOVERY_OK')),
    ('MissingSourceCapability', ('IsZariskiLocalAtSource', "failed to generate 'Bad.resLE'", 'ROLLBACK_OK', 'RECOVERY_OK')),
    ('LostInstance', ('missing instance or wrong priority',)),
    ('LostSimp', ('missing simp registration',))]:
    run(name, ['lake', 'env', 'lean', f'negative/{name}.lean'], negative=True, need=need)

consumer = ROOT/'tests/consumer'
prepare_external(consumer)
run('external-consumer', ['lake', 'build'], cwd=consumer)

evolution = ROOT/'tests/evolution'
prepare_external(evolution)
stable = hashes([evolution/p for p in ['Generated.lean', 'Reference.lean', 'Client.lean']])
original = (evolution/'Core.lean').read_bytes()
try:
    for label, variant, clean, negative in [
        ('evolution-v1-clean', 'v1', True, False),
        ('evolution-v2-stale-proof', 'v2-broken', False, True),
        ('evolution-v2-adapter-incremental', 'v2-fixed', False, False),
        ('evolution-v2-adapter-clean', 'v2-fixed', True, False)]:
        if clean:
            shutil.rmtree(evolution/'.lake/build', ignore_errors=True)
        (evolution/'Core.lean').write_bytes((evolution/'variants'/(variant+'.lean')).read_bytes())
        run(label, ['lake', 'build'], cwd=evolution, negative=negative,
            need=('Core.lean', 'Type mismatch', 'Iff.rfl') if negative else ())
        assert hashes([evolution/p for p in ['Generated.lean', 'Reference.lean', 'Client.lean']]) == stable
finally:
    (evolution/'Core.lean').write_bytes(original)
summary = dict(lean='4.36.0-rc2', mathlib='6da929dc62a7af33b577a22d4a01c08ddfd4f8f6',
    cases=len(ROWS), all_passed=all(r['passed'] for r in ROWS), recipes=4,
    sources=FROZEN, stable_evolution_clients=stable,
    limits=['Targeted negative controls require the intended diagnostic and rollback/recovery markers.',
            'This validates implementations and clients; it does not measure author productivity.',
            'Rollback covers synchronous Lean state, not external tactic IO.'])
(OUT/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps(summary, indent=2), flush=True)
