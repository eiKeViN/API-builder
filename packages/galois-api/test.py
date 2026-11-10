#!/usr/bin/env python3
"""Compile the standalone package and exercise targeted rejection/recovery controls."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'evidence'
OUT.mkdir(exist_ok=True)
ENV = os.environ.copy()
ENV['MATHLIB_NO_CACHE_ON_UPDATE']='1'
rows=[]

def run(label,command,*,cwd=ROOT,negative=False,need=()):
    start=time.monotonic()
    p=subprocess.run(command,cwd=cwd,env=ENV,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (OUT/(label+'.log')).write_text('$ '+' '.join(command)+'\n'+p.stdout+f'\nexit: {p.returncode}\n')
    ok=(p.returncode != 0) if negative else p.returncode == 0
    ok=ok and all(s in p.stdout for s in need)
    if negative:
        ok=ok and all(s not in p.stdout for s in ['unexpected surviving output','missing recovered output',
            'preflight leaked','pre-existing output lost','unknown module prefix','object file',
            'has not been implemented','unexpected token'])
    rows.append(dict(case=label,expected_failure=negative,passed=ok,returncode=p.returncode,
        required_diagnostics=list(need),seconds=round(time.monotonic()-start,3)))
    print(('PASS ' if ok else 'FAIL ')+label,flush=True)
    (OUT/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
    if not ok:
        print(p.stdout,flush=True)
        raise SystemExit(1)

run('library-and-clients',['lake','build','GaloisApi','GaloisApiTests.Generated',
    'GaloisApiTests.Support','GaloisApiTests.Client','GaloisApiTests.NamedClient',
    'GaloisApiTests.ExtraClient','GaloisApiTests.ImportedCheck','GaloisApiTests.SourceRanges'])
for name,need in [
    ('UnknownRole',("unsupported role 'map_supp'",'ROLLBACK_OK')),
    ('DuplicateRole',("duplicate role 'map_sup'",'ROLLBACK_OK')),
    ('EmptySelection',('select at least one role','ROLLBACK_OK')),
    ('WrongDirection',("unsupported role 'comap_inf'",'ROLLBACK_OK')),
    ('Collision',("output collision 'Bad.map_bot'",'PREFLIGHT_OK')),
    ('WrongGC',("failed to prove 'Bad.map_sup'",'ROLLBACK_OK')),
    ('MissingField',("missing field 'top'",'ROLLBACK_OK')),
    ('DuplicateField',("duplicate field 'inf'",'ROLLBACK_OK')),
    ('UnknownField',("unknown field 'typo'",'ROLLBACK_OK')),
    ('RollbackRecovery',("failed to prove 'Bad.comap_top'",'ROLLBACK_OK','RECOVERY_OK')),
    ('Sorry',("forbidden axiom 'sorryAx'",'ROLLBACK_OK')),
    ('LostRegistration',("missing simp registration for 'map_sup'",))]:
    run(name,['lake','env','lean',f'negative/{name}.lean'],negative=True,need=need)

consumer=ROOT/'tests/consumer'
# Share only mathlib/dependency materialization when the host supports symlinks.
shared=consumer/'.lake/packages'
shared.parent.mkdir(exist_ok=True)
if not shared.exists():
    try: shared.symlink_to(ROOT/'.lake/packages',target_is_directory=True)
    except OSError: pass
run('external-update',['lake','update'],cwd=consumer)
for dep in shared.iterdir():
    cached=ROOT/'.lake/packages'/dep.name/'.lake/build'
    output=dep/'.lake/build'
    if cached.exists() and not output.exists():
        try:
            output.parent.mkdir(exist_ok=True)
            output.symlink_to(cached.resolve(),target_is_directory=True)
        except OSError: pass
run('external-consumer',['lake','build'],cwd=consumer)
sources={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
    for p in [ROOT/'GaloisApi.lean',*sorted((ROOT/'GaloisApi').glob('*.lean'))]}
summary=dict(lean='4.36.0-rc2',mathlib='6da929dc62a7af33b577a22d4a01c08ddfd4f8f6',
    cases=len(rows),all_passed=all(r['passed'] for r in rows),sources=sources,
    limits=['Expected failures require their intended diagnostics and absence/recovery markers.',
            'Command-state rollback covers this synchronous generator, not arbitrary tactic IO.',
            'This is a design/implementation validation, not an author-time productivity benchmark.'])
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
