#!/usr/bin/env python3
"""Run the prototype's supported checks; preserve command output and status."""
import os, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence'/'final';OUT.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['MATHLIB_NO_CACHE_ON_UPDATE']='1';env.setdefault('XDG_CACHE_HOME',str(ROOT.parent/'.cache'))
def run(label,args,cwd=ROOT,expected=0,contains=None):
 p=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(label+'.log')).write_text('$ '+' '.join(args)+'\n'+p.stdout+f'\nexit: {p.returncode}\n')
 assert p.returncode==expected,(label,p.stdout)
 if contains:assert contains in p.stdout,(label,p.stdout)
 print('PASS',label,flush=True)
run('root-build',['lake','build','ApiBuilder','Examples.Order.GoldenClient','Examples.Order.Client','Examples.Continuous.Client','Examples.Check','Examples.Order.BoundCheck','Examples.Order.ChoiceClient','Examples.Order.Dictionaries','Examples.BadRecipes'])
run('contracts',['lake','env','lean','tests/math/Contracts.lean'])
run('provider-build',['lake','build'],ROOT/'packages/pointed')
run('extended-build',['lake','build','Extended','Extended.LocalClient'],ROOT/'tests/extended')
run('unused-provider',['lake','env','lean','Unused.lean'],ROOT/'tests/extended')
run('extension-typo',['lake','env','lean','Typo.lean'],ROOT/'tests/extended',1,'unused field')
run('acceptance',['python3','scripts/test_acceptance.py'])
run('smoke',['python3','scripts/test_smoke.py'])
run('evolution',['python3','scripts/test_evolution.py'])
run('diff-check',['git','diff','--check'])
