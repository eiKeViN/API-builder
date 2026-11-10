#!/usr/bin/env python3
"""Source inventory using the repository's existing comment/blank-line rules."""
from pathlib import Path
import hashlib
import json
import runpy

ROOT = Path(__file__).resolve().parent
strip_comments = runpy.run_path(str(ROOT.parents[1]/'experiments/api-families/measure_sources.py'))['strip_comments']
groups = {
    'facade': [ROOT/'ApiRecipes.lean'],
    'shared_command_plumbing': [ROOT/'ApiRecipes/Command.lean'],
    'four_recipe_modules': sorted(p for p in (ROOT/'ApiRecipes').glob('*.lean') if p.stem != 'Command'),
    'reference_and_checker': [ROOT/'ApiRecipesTests/Reference.lean', ROOT/'ApiRecipesTests/Support.lean'],
    'clients_and_fixtures': sorted(p for p in (ROOT/'ApiRecipesTests').glob('*.lean') if p.stem not in ['Reference', 'Support'])}
result = {}
for group, paths in groups.items():
    files = [dict(path=str(p.relative_to(ROOT)),
        sloc=sum(bool(line.strip()) for line in strip_comments(p.read_text()).splitlines()),
        sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths]
    result[group] = dict(sloc=sum(row['sloc'] for row in files), files=files)
(ROOT/'evidence/source-costs.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: value['sloc'] for key, value in result.items()}, indent=2))
