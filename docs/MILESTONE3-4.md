# External composition and maintenance

## Frozen public SDK

The external provider was authored after framework commit
`2e8d5a31561221b549f6f79619dd580f6b97fb6f`. `ApiBuilder/` is unchanged.
`packages/pointed` is a separate Lake package using the documented public facade.
It introduces named point/preservation inputs and five Pointed.Hom roles, preserves
the original ten roles, and deliberately translates outer-first map composition
to inner-first Pointed.Hom.comp. Both independent fixture families compile with it.
Fresh ordinary clients and explicit imported validators pass. `Extended.LocalRecipe`
separately demonstrates a local coe_comp theorem with no simp registration.

The SDK and provider have the same author; no independent-author usability result
is claimed. Both mathematical consumer cores are independent modules, hosted in
one framework repository and exercised by one separate consumer test package.

## Actual failures and fixes

- The Order fixture initially used `Map.map_point` for its structure proof field.
  This collided with the requested public bridge theorem, and preflight rejected it.
  The author-written fixture now uses `map_point'`. No SDK change or silent binding.
- Creating the consumer's initial manifest triggered mathlib's whole-library cache
  update hook. It was stopped; `MATHLIB_NO_CACHE_ON_UPDATE=1` keeps updates limited
  to manifest resolution and the already requested dependency cache.
- A clean upgrade test initially meta-imported the provider before compiling it.
  The test correctly failed for missing olean, and now explicitly builds the
  provider before inspecting receipts. That failure never counted as a passed gate.

## Executed evolution test

`python3 scripts/test_evolution.py` starts a source-only project copy with no
project build artifacts. Fixed external mathlib dependency artifacts are reused.
It records every command/exit code, receipt text/diffs, old-client source hashes
and framework hashes in `evidence/evolution`.

1. Build both base families and old clients in the fresh copy.
2. Replace only each family invocation with pointedMap plus its two new inputs.
   Rebuild both unchanged old clients and the new bridge clients: success.
3. Change provider output toPointedHom_comp to pointedComposition. Generators and
   receipt checking succeed with a reviewable output diff; the unchanged old
   bridge client fails on the missing original declaration.
4. Restore the interface but append a logged late-generation failure. The family
   build and a subsequent dependent build both fail with that diagnostic.
5. Restore the good provider. Both extended clients, local customization and
   imported validators pass. Recovered receipt text equals the good snapshot.
6. Assert the public framework source hashes never changed during the experiment.

These are local provider source mutations captured by the reproducible script,
not published Git dependency upgrades or a multi-version compatibility solver.
The original milestone-0 test separately proves implementation-only recipe/helper
invalidation by checking generated values 21 → 22 → 32 and a stale-output control.

## Boundaries

The tested vertical prototype is usable for the supported closed, public,
object-indexed families. It is not a security sandbox, arbitrary telescope
elaborator, implicit recipe finder or universal API-effect auditor. Full generated
source navigation, complete compiler auxiliary ownership, dependency-version
conflict permutations and independent-author UX evaluation remain unverified.
No claim about productivity is supported by these tests.
