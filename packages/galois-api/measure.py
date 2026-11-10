#!/usr/bin/env python3
"""Inventory implementation and interface-oracle costs separately."""
from pathlib import Path
import hashlib,json,runpy

ROOT=Path(__file__).resolve().parent
scanner=runpy.run_path(str(ROOT.parents[1]/'experiments/api-families/measure_sources.py'))['strip_comments']
files=['GaloisApi.lean','GaloisApi/Basic.lean','GaloisApi/Check.lean',
    'GaloisApiTests/Reference.lean','GaloisApiTests/Generated.lean']
inventory=[]
for name in files:
    p=ROOT/name;source=p.read_text()
    inventory.append(dict(path=name,physical_lines=len(source.splitlines()),
        sloc=sum(bool(l.strip()) for l in scanner(source).splitlines()),
        sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
data=dict(metric='nonblank physical code lines after nested-comment removal',files=inventory,
    interpretation=['The optional checker and independently written reference signatures have real source costs.',
        'The generated consumer includes examples of selection and scope; it is not a minimal cost benchmark.',
        'The dedicated tool now has more usability and failure-handling features than the original 86-SLOC baseline.',
        'Source size does not establish developer-time or lifecycle productivity.'])
(ROOT/'evidence/source-costs.json').write_text(json.dumps(data,indent=2)+'\n')
for f in inventory:print(f['path'],f['sloc'])
