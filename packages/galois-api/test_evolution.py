#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time

ROOT=Path(__file__).resolve().parent
HERE=ROOT/'tests/evolution'
OUT=ROOT/'evidence/evolution'
OUT.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['MATHLIB_NO_CACHE_ON_UPDATE']='1'
shared=HERE/'.lake/packages';shared.parent.mkdir(exist_ok=True)
if not shared.exists():
    try:shared.symlink_to((ROOT/'.lake/packages').resolve(),target_is_directory=True)
    except OSError:pass
subprocess.run(['lake','update'],cwd=HERE,env=env,check=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
stable={name:sha(HERE/name) for name in ['Reference.lean','Generated.lean','Client.lean']}
core=HERE/'Core.lean';original=core.read_bytes();rows=[]
assert original==(HERE/'variants/v2-fixed.lean').read_bytes(),'preserve edited fixture'
try:
    for name,variant,clean,success in [
        ('v1-clean','v1',True,True),
        ('v2-old-proof-rejected','v2-broken-rfl',False,False),
        ('v2-adapter-incremental','v2-fixed',False,True),
        ('v2-adapter-clean','v2-fixed',True,True)]:
        assert all(sha(HERE/n)==s for n,s in stable.items())
        core.write_bytes((HERE/'variants'/(variant+'.lean')).read_bytes())
        if clean:shutil.rmtree(HERE/'.lake/build',ignore_errors=True)
        t=time.monotonic();p=subprocess.run(['lake','build','Client'],cwd=HERE,env=env,
            text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/(name+'.log')).write_text(p.stdout+f'\nexit: {p.returncode}\n')
        ok=(p.returncode==0)==success
        if not success:ok=ok and 'Core.lean:' in p.stdout and 'Iff.rfl' in p.stdout and 'Type mismatch' in p.stdout
        row=dict(case=name,expected_success=success,returncode=p.returncode,passed=ok,
            clean=clean,stable_sources=stable,seconds=round(time.monotonic()-t,3))
        rows.append(row);print(('PASS ' if ok else 'FAIL ')+name,flush=True)
        if not ok:raise RuntimeError(p.stdout)
finally:
    core.write_bytes(original)
    (OUT/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
assert len(rows)==4 and all(r['passed'] for r in rows)
