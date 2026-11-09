# Current construction status

The native prototype now has executed stages 0–4 on branch
`codex/native-rebuild-prototype`. The supported vertical demonstration works;
this does not mean every hardening row of the research matrix has passed.

## Authority and fixed inputs

- Repository: eiKeViN/API-builder; initial commit a81cc4e contained only README.
- [Specification](https://chatgpt.com/space/page_daba96657c448191ae0e0ab58804dab4)
  and [source guide](https://chatgpt.com/space/page_52ead59314908191a7631b11eae7f29f)
  were actually read, along with the extracted research archive's BUILD_START,
  SDK audit, design, acceptance matrix and review record.
- Library archive: libfile_50864eaf618c8191a39d23e67c9119fe; SHA-256
  b9162d14aef71c8d50675bea21023fd41ea5a7440903718b4af9672a7f5c0f83.
- Lean v4.36.0-rc2, b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a.
- mathlib 6da929dc62a7af33b577a22d4a01c08ddfd4f8f6.
- Aesop 7d11bfa88558f8d3d90afdf6bd877ed70001498d, resolved by the manifest.
- No push, PR, merge, service deployment or modifications to another project.

## Delivered and checked

| Stage | Actual evidence |
| --- | --- |
| 0 | Separate provider/consumer; body-only recipe/helper edits regenerate 21 → 22 → 32; stale-output control fails; smoke negatives fail |
| 1 | Native contracts/proofs; independent ContinuousMap and OrderHom cores; handwritten ten-role golden API and fresh client |
| 2 | Both ten-role generated APIs; normal coercion/ext/simp/field notation; receipt persistence, native axiom/effect checks, named validators |
| 3 | Independent PointedRecipes Lake package; both families retain ten roles and gain five bridge roles; unchanged SDK |
| 4 | Explicit existing dictionary/id/comp binding; choice operations; competing dictionaries; local recipe; compatible/breaking upgrades; late failure/recovery |

See MILESTONE1.md, MILESTONE2.md and MILESTONE3-4.md for failures encountered and
exact boundaries. RECIPE_SDK.md documents the public provider interface.

`evidence/final` contains aggregate commands and exit statuses.
`evidence/acceptance` contains isolated intended-diagnostic failures; failed
creation cases also assert no accepted receipt. `evidence/evolution` contains
clean-project and incremental upgrade/recovery logs, receipt diffs and source hashes.
The executable tests, not the old research plans, establish these results.

## Remaining limitations

The separate [API-family validation](API_FAMILY_VALIDATION.md) executes 47 bounded
comparisons and adverse controls for map/comap, scheme-property installation and
representation evolution. Dedicated commands already solve the generation tasks;
the experiment does not establish a framework productivity advantage. Its recipe
adapters are kept outside the public SDK in `experiments/api-families`.

- No independent-author usability study: the provider is independently packaged
  and uses a frozen public SDK, but was written by the same agent.
- The two independent consumer families share a consumer test package.
- Provider upgrades are reproducible local source mutations, not published Git
  pin upgrades; version-conflict behavior is not tested.
- Full source-navigation and exhaustive compiler auxiliary/effect ownership,
  all malformed-input/import-order permutations and arbitrary open/dependent
  specifications remain outside the verified surface.
- No metaprogram IO rollback, untrusted-plugin security, or productivity claim.

There is no current source, network or permission blocker. Dependency caches and
the Lean installation are workspace-local. The working tree contains source,
resolved manifests and reproducible logs; generated build artifacts are ignored.
