#!/usr/bin/env python3
"""Reproduce the bounded comparison, adverse controls and representation upgrade."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
OUT = ROOT/'evidence'
OUT.mkdir(exist_ok=True)
ENV = os.environ.copy()
ENV['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
ROWS = []
FROZEN = {
    'MapBaseline/MacroCommand.lean': '74a441bef4c7e3b2660df0beac8e0d4daa34ad402105164bf91c1c15a49ff3d6',
    'MapBaseline/Framework.lean': '51a7fde0eecc1da41b6d34aadf884b8d5bd3516c8998c62b51a44aae9e38193b',
    'MapBaseline/Contract.lean': 'f664497f1893d511e731bead1a93deb793d6f961d29a9d038d397dc2898d10e5',
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_freeze():
    for name, expected in FROZEN.items():
        assert digest(ROOT/name) == expected, f'Frozen source changed: {name}'

def run(group, label, command, *, cwd=ROOT, expected=0, contains=None):
    started = time.monotonic()
    proc = subprocess.run(command,cwd=cwd,env=ENV,text=True,
        stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log = OUT/group/(label+'.log')
    log.parent.mkdir(parents=True,exist_ok=True)
    log.write_text('$ '+' '.join(command)+'\n'+proc.stdout+f'\nexit: {proc.returncode}\n')
    passed = proc.returncode == 0 if expected == 0 else proc.returncode != 0
    if contains: passed = passed and contains in proc.stdout
    passed = passed and 'has not been implemented' not in proc.stdout
    row = dict(group=group,case=label,command=command,
        expected_success=expected==0,returncode=proc.returncode,
        required_diagnostic=contains,passed=passed,
        elapsed_seconds=round(time.monotonic()-started,3),log=str(log.relative_to(ROOT)))
    ROWS.append(row)
    print(('PASS ' if passed else 'FAIL ')+group+'/'+label,flush=True)
    (OUT/'results.json').write_text(json.dumps(ROWS,indent=2)+'\n')
    if not passed:
        print(proc.stdout,flush=True)
        raise SystemExit(1)

def compile_module(group, module):
    source = ROOT/(module.replace('.','/')+'.lean')
    output = ROOT/'.lake/build/lib/lean'/source.relative_to(ROOT).with_suffix('.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    run(group,module,['lean','-o',str(output),str(source)])

def negative(group, family, module, diagnostic):
    run(group,module,['lean',f'negative/{family}/{module}.lean'],expected=1,contains=diagnostic)

def main():
    global ENV
    check_freeze()
    sdk_before = {p: digest(REPO/p) for p in ['ApiBuilder/Family.lean','ApiBuilder/FamilyElab.lean']}
    run('setup','sdk',['lake','build','ApiBuilder.FamilyElab'],cwd=REPO)
    if not (ROOT/'lake-manifest.json').exists():
        run('setup','manifest',['lake','update'])
    ENV['LEAN_PATH'] = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],
        cwd=ROOT,env=ENV,text=True).strip()
    ENV['PATH'] = subprocess.check_output(['lake','env','printenv','PATH'],
        cwd=ROOT,env=ENV,text=True).strip()

    for name in ['Contract','Handwritten','Client','GenericClient','MacroCommand','Macro',
            'MacroClient','MacroNamedArguments','Framework','Specifications','Recipe',
            'RecipeClient','NamedArguments','AllContracts','ImportedCheck']:
        compile_module('maps','MapBaseline.'+name)
    for name, diagnostic in [
        ('RejectMissing','missing role'),
        ('RejectMacroRegistration','missing simp registration'),
        ('RejectRecipeRegistration','registration mismatch'),
        ('RejectExtraAssumption',"map contract: binder mismatch for 'comap_inf'"),
        ('RejectNativeGold','generated proof uses native gold API'),
        ('RejectBinderName','public binder name mismatch')]:
        negative('maps','MapBaseline',name,diagnostic)

    for name in ['Install','Core','NoInstallation','Tests']:
        compile_module('geometry','AGExperiment.'+name)
    for name in ['RejectFiniteSource','RejectProperSource']:
        negative('geometry','AGExperiment',name,'IsZariskiLocalAtSource')
    for name in ['Recipe','RecipeTests']:
        compile_module('geometry','AGExperiment.'+name)
    negative('geometry','AGExperiment','RecipeRejectFiniteSource','IsZariskiLocalAtSource')
    negative('geometry','AGExperiment','RecipeRejectRegistration',"registration mismatch 'instance'")

    check_freeze()
    for name in ['Reference','Macro','MacroClient','Specifications','Recipe',
            'RecipeClient','NamedClient','Checks','ImportedCheck']:
        compile_module('holdout','Holdout.'+name)
    check_freeze()

    run('setup','evolution-suite',[sys.executable,'run_evolution.py'])
    evolution = json.loads((OUT/'evolution/results.json').read_text())
    assert evolution['all_expectations_met'] and len(evolution['cases'])==7
    totals = {g:sum(r['group']==g for r in ROWS) for g in ['maps','geometry','holdout']}
    totals['evolution']=len(evolution['cases'])
    assert totals == {'maps':21,'geometry':10,'holdout':9,'evolution':7},totals
    sdk_after = {p: digest(REPO/p) for p in sdk_before}
    assert sdk_before == sdk_after,'SDK changed during consumer validation'
    check_freeze()
    summary = dict(lean='4.36.0-rc2',
        mathlib='6da929dc62a7af33b577a22d4a01c08ddfd4f8f6',
        expected_outcomes=totals,total_expected_outcomes=sum(totals.values()),
        all_passed=True,frozen_sources=FROZEN,sdk_sources=sdk_after,
        limits=['Bounded source and compile tests, not a productivity or performance benchmark.',
                'Separate-agent adaptation with shared context; no independent human-author study.',
                'Signature checks permit only bijective universe renaming; named binders are checked.',
                'Direct proof dependency checks run at creation; imported rechecks cover types and effects.'])
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2),flush=True)

if __name__ == '__main__':
    main()
