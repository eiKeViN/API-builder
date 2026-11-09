#!/usr/bin/env python3
"""Isolated Lean processes; failure only counts with intended diagnostic and no receipt."""
from pathlib import Path
import subprocess
import json
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence'/'acceptance'; OUT.mkdir(parents=True,exist_ok=True)
(OUT/'summary.json').unlink(missing_ok=True)
FIX=ROOT/'tests'/'acceptance'; FIX.mkdir(parents=True,exist_ok=True)
base='''module
public import Examples.Order.Core
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
meta import Examples.BadRecipes
'''
call='''api_family OrderExample.Map using RECIPE where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.composition
'''
absent='''open Lean Elab Command in
run_cmd do
  if (ApiBuilder.receipts.getState (← getEnv)).any (·.family == `OrderExample.Map) then
    throwError "TEST: unexpected accepted receipt"
  logInfo "TEST: no accepted receipt"
'''
cases={}
for label,recipe,diagnostic in [
 ('preparation','preparation','intentional preparation error'),
 ('validator','validator','intentional validator error'),
 ('duplicate_owner','duplicate','duplicate ownership'),
 ('late_proof','lateProof','Type mismatch'),
 ('sorry_axiom','sorryProof','forbidden axiom'),
 ('wrong_entrypoint','wrong','unexpected type'),
 ('polymorphic','polymorphic','no universe parameters')]:
 cases[label]=(base+call.replace('RECIPE','BadRecipes.'+recipe)+absent,diagnostic)
cases['unused_field']=(base+call.replace('RECIPE','ApiBuilder.Recipes.bundledMap')+'  typo := OrderExample.Core.functionView\n'+absent,'unused field')
cases['collision']=(base+'public def OrderExample.Map.ext_iff : Nat := 7\n'+call.replace('RECIPE','ApiBuilder.Recipes.bundledMap')+absent,'output collision')
cases['wrong_composition']=(base+'public def wrongComposition : Nat := 0\n'+call.replace('RECIPE','ApiBuilder.Recipes.bundledMap').replace('composition := OrderExample.Core.composition','composition := wrongComposition')+absent,'Type mismatch')
post='''module
public import Examples.Order.Generated
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
'''
cases['removed_simp']=(post+'attribute [-simp] OrderExample.Map.comp_id\n#api_check OrderExample.Map\n','registration mismatch')
cases['extra_simp']=(post+'attribute [simp] OrderExample.Map.comp_assoc\n#api_check OrderExample.Map\n','registration mismatch')
cases['competing_dictionary']=((FIX/'competing_dictionary.lean').read_text(),'definitional contract mismatch')
results=[]
for label,(source,diagnostic) in cases.items():
 path=FIX/(label+'.lean');path.write_text(source)
 cmd=['lake','env','lean',str(path.relative_to(ROOT))]
 p=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (OUT/(label+'.log')).write_text('$ '+' '.join(cmd)+'\n'+p.stdout+f'\nexit: {p.returncode}\n')
 assert p.returncode!=0 and diagnostic in p.stdout,(label,p.stdout)
 if 'TEST: no accepted receipt' in source:
  assert 'TEST: no accepted receipt' in p.stdout and 'TEST: unexpected accepted receipt' not in p.stdout,(label,p.stdout)
 results.append({'test':label,'exit':p.returncode,'expected_diagnostic':diagnostic})
 print('PASS',label)
(OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
