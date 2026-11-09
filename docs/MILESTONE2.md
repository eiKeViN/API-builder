# Milestone 2: generated native API and acceptance barrier

Actual passing commands and receipts: evidence/milestone2/build.log.
`python3 scripts/test_acceptance.py` records thirteen isolated negative tests,
checks intended diagnostics, and checks receipt absence after failed generation.
`python3 scripts/test_smoke.py` still passes after separating provisional
SmokeRecipe from the ABI-1 nominal Recipe.

Both independent native fixture families now obtain the ten promised roles from
one bundledMap provider. Fresh ordinary clients exercise coercion, field notation,
ext, simp, units, associativity and exposed wrapper bodies. A separate checking
module imports saved receipts and explicitly meta-imports the validator provider.
The bound fixture adopts an existing dictionary/id/comp without redefining them.
The choice fixture compiles with noncomputable operations and propositional laws.
The same-carrier dictionary fixture retains opposite preorder structures.

The acceptance barrier covers preparation, every native declaration, execution,
axiom collection, registration checks and named validators, with local synchronous
elaboration. Only then does the persistent extension add a receipt. Conflicting
imported receipts are retained and an explicit check rejects a nonunique family.
Effects are bounded to the advertised public instance/ext/simp surface. This is
trusted metaprogram execution, not IO rollback or universal effect auditing.

Observed failures fixed during construction:
- An exported recipe reached by a private meta import is intentionally not visible
  in the consumer's public-export environment. Entrypoint resolution now uses normal
  native meta scope; mathematical input/output export checks remain enforced.
- The choice fixture exposed a computability error in a temporary data-valued
  checking declaration. It is now `noncomputable example` and the choice client passes.
- An acceptance run concurrent with a provider rebuild saw a missing olean; that
  run was rejected by the harness, then rerun after build completion. Only the
  complete successful rerun appears in summary.json.

The implementation is documented in RECIPE_SDK.md. The next stage freezes this
framework revision and constructs an independent pointed-recipe package through
its public helper interface. Full source-navigation/auxiliary-declaration auditing
and all malformed-input permutations remain hardening work.
