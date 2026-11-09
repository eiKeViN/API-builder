#!/usr/bin/env python3
"""Clean project build, source-level upgrade, breaking change and failed rebuild evidence."""
import os, shutil, subprocess, tempfile, hashlib, json, difflib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence'/'evolution';OUT.mkdir(parents=True,exist_ok=True)
(OUT/'summary.json').unlink(missing_ok=True)
work=Path(tempfile.mkdtemp(prefix='api-builder-evolution-'))/'repo'
shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('.git','.lake','evidence','__pycache__'))
(work/'.lake').mkdir();(work/'.lake/packages').symlink_to(ROOT/'.lake/packages',target_is_directory=True)
consumer=work/'tests/extended'
env=os.environ.copy();env['MATHLIB_NO_CACHE_ON_UPDATE']='1'
env['XDG_CACHE_HOME']=str(ROOT.parent/'.cache')
results=[]
def run(label,args,ok=True,contains=None):
 p=subprocess.run(args,cwd=consumer,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(label+'.log')).write_text('$ '+' '.join(args)+'\n'+p.stdout+f'\nexit: {p.returncode}\n')
 assert (p.returncode==0)==ok,(label,p.stdout)
 if contains: assert contains in p.stdout,(label,p.stdout)
 results.append({'test':label,'exit':p.returncode})
 print('PASS',label,flush=True)
 return p.stdout

def treehash(path):
 return {str(p.relative_to(path)):hashlib.sha256(p.read_bytes()).hexdigest() for p in path.rglob('*.lean')}
frozen=treehash(work/'ApiBuilder')
originals={}
for family in ['Order','Continuous']:
 p=consumer/f'Extended/{family}.lean';originals[p]=p.read_text()
 baseline=originals[p].replace('meta import PointedRecipes.Recipes','meta import ApiBuilder.Recipes.BundledMap').replace('PointedRecipes.pointedMap','ApiBuilder.Recipes.bundledMap')
 baseline='\n'.join(x for x in baseline.splitlines() if not x.startswith('  point :=') and not x.startswith('  preserves_point :='))+'\n'
 p.write_text(baseline)
 old=(ROOT/f'Examples/{family}/Client.lean').read_text().replace(f'Examples.{family}.Generated',f'Extended.{family}')
 (consumer/f'Extended/{family}OldClient.lean').write_text(old)
oldhash={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (consumer/'Extended').glob('*OldClient.lean')}
inspect=consumer/'Inspect.lean'
inspect.write_text('''module
public import Extended.Order
public import Extended.Continuous
meta import ApiBuilder.FamilyElab
meta import PointedRecipes.Recipes
#api_check OrderExample.Map
#api_check ContinuousExample.Map
#api_inspect OrderExample.Map
#api_inspect ContinuousExample.Map
''')
run('clean-base',['lake','build','Extended.OrderOldClient','Extended.ContinuousOldClient','PointedRecipes.Recipes'])
before=run('base-receipts',['lake','env','lean','Inspect.lean'])
assert 'toPointedHom' not in before
for p,text in originals.items():p.write_text(text)
run('compatible-upgrade',['lake','build','Extended.OrderOldClient','Extended.ContinuousOldClient','Extended'])
after=run('pointed-receipts',['lake','env','lean','Inspect.lean'])
assert 'toPointedHom_comp' in after
(OUT/'compatible-receipt.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='base',tofile='pointed')))
assert oldhash=={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (consumer/'Extended').glob('*OldClient.lean')}
provider=work/'packages/pointed/PointedRecipes/Recipes.lean';good=provider.read_text()
provider.write_text(good.replace('toPointedHom_comp','pointedComposition'))
run('breaking-generators',['lake','build','Extended.Order','Extended.Continuous'])
broken=run('breaking-receipts',['lake','env','lean','Inspect.lean'])
(OUT/'breaking-receipt.diff').write_text(''.join(difflib.unified_diff(after.splitlines(True),broken.splitlines(True),fromfile='pointed',tofile='breaking')))
run('breaking-old-bridge-client',['lake','build','Extended.OrderClient'],False,'toPointedHom_comp')
provider.write_text(good.replace('buildBridge v point preserves','buildBridge v point preserves\n        logError "intentional upgrade failure"'))
run('late-failure-rebuild',['lake','build','Extended.Order'],False,'intentional upgrade failure')
run('failed-dependent-build',['lake','build','Extended.OrderOldClient'],False,'intentional upgrade failure')
provider.write_text(good)
run('recovery',['lake','build','Extended','Extended.LocalClient'])
recovered=run('recovered-receipts',['lake','env','lean','Inspect.lean'])
assert recovered==after,'logical receipt changed after restoration'
assert frozen==treehash(work/'ApiBuilder'),'framework changed'
(OUT/'summary.json').write_text(json.dumps({'tests':results,'old_clients_sha256':oldhash,'framework_sha256':frozen,'dependencies':'fixed external mathlib build cache reused; all project oleans rebuilt in isolated copy'},indent=2)+'\n')
print('Isolated workspace:',work)
