# Canonical source costs

Reproduce from this package with `python3 measure_sources.py`; verify an existing measurement with `python3 measure_sources.py --check`. The authoritative machine-readable result is `evidence/costs.json`.

Count all physical Lean lines containing non-comment code, including imports and namespace/check scaffolding. Remove blank lines, `--` comments and nested `/- ... -/` comments while preserving strings. JSON includes file hashes, exact counted line numbers and supplementary nonwhitespace character counts.

**The handwritten API already uses the generic GaloisConnection helpers. The framework adapter requires an independently authored reference, so that oracle is a real input and maintenance cost. Comparing invocation lines alone does not establish productivity.**

| Component | Canonical relative path | Physical lines | SLOC |
|---|---|---:|---:|
| Handwritten/helper, 18 wrappers and creation checks | `MapBaseline/Handwritten.lean` | 122 | 80 |
| Standalone command provider | `MapBaseline/MacroCommand.lean` | 102 | 86 |
| Three-family command consumer and creation checks | `MapBaseline/Macro.lean` | 52 | 33 |
| Independent contract checker | `MapBaseline/Contract.lean` | 70 | 57 |
| Framework adapter | `MapBaseline/Framework.lean` | 70 | 55 |
| Three-family specifications | `MapBaseline/Specifications.lean` | 54 | 49 |
| Three-family recipe consumer | `MapBaseline/Recipe.lean` | 15 | 13 |
| Existing SDK data/audit layer | `../../ApiBuilder/Family.lean` | 118 | 96 |
| Existing SDK command layer | `../../ApiBuilder/FamilyElab.lean` | 61 | 57 |

Complete delivered source dependencies, counting each file once:

- Manual/helper plus its actual creation checker: **137 SLOC**.
- Command plus its actual checker and oracle: **256 SLOC**.
- Recipe's new source, including its required oracle: **340 SLOC**.
- Existing SDK reused by the recipe: **153 SLOC**, reported separately from new authoring.

Pure three-family requests are 9 command lines versus 6 recipe lines. This excludes the specifications, reference, provider, checker and adapter listed above. Recipe rechecks add 3 lines. Canonical handwritten and command modules each also execute three creation-time `#map_contract` checks.

The oracle here implements full independent wrapper declarations. Its signatures are used for comparison; generated proofs cannot call it. The manual self-check does not supply an independent oracle for the intended mathematical signature. The paths also promise different lifecycle features, so these totals are an inventory rather than a same-functionality ranking.

## AG installer

| Component | Canonical relative path | Physical lines | SLOC |
|---|---|---:|---:|
| Common probe/capability input | `AGExperiment/Core.lean` | 79 | 64 |
| Standalone installer | `AGExperiment/Install.lean` | 66 | 51 |
| Additional framework adapter | `AGExperiment/Recipe.lean` | 40 | 35 |
| Standalone consumer and tests, whole file | `AGExperiment/Tests.lean` | 57 | 45 |
| Recipe consumer and tests, whole file | `AGExperiment/RecipeTests.lean` | 42 | 38 |

Both routes share 64 SLOC of concrete probe/capability input and the 51-SLOC installer. Pure installation requests take 8 lines (five core and three source requests); recipe requests take 13 lines plus 5 recheck lines. Whole consumer files also contain tests, so their full-file sizes are listed separately.

## Frozen held-out families

| Component | Canonical relative path | Physical lines | SLOC |
|---|---|---:|---:|
| Command consumer with independent checks | `Holdout/Macro.lean` | 30 | 22 |
| Recipe specifications | `Holdout/Specifications.lean` | 37 | 32 |
| Independent reference, 12 wrappers | `Holdout/Reference.lean` | 45 | 37 |
| Recipe consumer with rechecks | `Holdout/Recipe.lean` | 12 | 10 |

Bare requests are 4 lines for the command and 4 for the recipe. Actual marginal authored source including the new reference is **59 SLOC** for command consumption and **79 SLOC** for specifications plus recipe consumption. Existing generator/checker/adapter/SDK are not recharged, but remain infrastructure and maintenance dependencies.

The reusable producers transfer without edits to these two new objects. These measurements do not establish reduced developer time or long-term maintenance cost. Concrete specifications and independently authored oracle signatures remain costs to simplify and measure.

All paths above are relative to this package. Generated output, dependency source, environment setup and staged duplicate copies are excluded from production totals. JSON separately inventories selected clients and validation harnesses. No Lean source is changed by measurement; scenario totals overlap and must not be added.
