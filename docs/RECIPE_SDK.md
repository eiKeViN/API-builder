# Public recipe SDK (ABI 1)

Import `ApiBuilder.Recipes.BundledMap` as a **public meta import** in a provider.
Export a monomorphic `public meta def recipe : ApiBuilder.Recipe` and select it
with `api_family Native.Map using Provider.recipe where ...`.
The generation module publicly imports its mathematical core and meta-imports
`ApiBuilder.FamilyElab` and the chosen provider. Checking modules must explicitly
meta-import the validators' provider (a public meta facade works).

The dispatcher parses named identifier fields, rejects duplicates, resolves a
nominal Recipe with empty universe parameters and ABI 1, then calls `prepare`.
`PreparedRecipe` contains consumed keys, named inputs, role/name/owner/binding/
registration records, named validators, and an execution action. Preparation must
not generate declarations. Final unused-key checking is done by the dispatcher,
so base preparation does not reject extension fields. All code is trusted Lean.

Public helper path:

1. `decodeView request : CommandElabM ViewPorts` inspects the named closed
   FunctionView. The supported generated-instance route requires a concrete native
   inductive Hom head equal to the family namespace; aliases/projections fail.
2. `decodeComposition view : CommandElabM CompositionPorts` resolves its input.
3. `buildFunctionView view` emits or binds FunLike, emits ext/ext_iff, and checks
   rigid endpoint dictionary synthesis plus ordinary application at `.default`.
4. `buildComposition ports` typechecks the composition against that exact view,
   then emits or binds id/comp and emits application/unit/associativity laws.
5. `prepareBundledMap request` composes those helpers and advertises ten roles.
   An extension can call it, append its own consumed keys/inputs/outputs/validators,
   and sequence `base.execute` before its own native declarations.

`ViewPorts` exposes request, selected names, native term syntax for Obj/Carrier/Hom/
view, chosen dictionary name and universe parameters. `withViewScope` supplies the
rigid universe parameters for native quotations. `declare request syntax` elaborates
under the original source reference and checks diagnostics. `checkDefEq` elaborates
native terms and compares at `.default`; use rigid lambda-bound endpoints.

Default bindings: `bind_instance`, `bind_id`, `bind_comp`. Bound operations must
already have the requested family names. Bound declarations are never redefined
or reattributed. Imported exact bodies must be exposed or use explicit adapters.

`Validator` is a monomorphic named callback over `FamilyReceipt`. Persist names and
plain data only. `requestFromReceipt` reconstructs named input fields. New validators
are run before receipt insertion and by `#api_check`. `#api_inspect` prints the
actual accepted descriptor. Native axiom checks allow only propext, Classical.choice
and Quot.sound. Advertised instance/ext/simp effects are checked; generated roles
also reject unexpected effects in these three supported categories.

Duplicate ownership, name collisions, preparation/execution/validator errors and
forbidden axioms prevent receipt insertion. Local synchronous elaboration closes
the diagnostic window. This is not arbitrary IO rollback or a plugin sandbox.
The provisional ABI-0 experiment is now named `SmokeRecipe`, avoiding confusion
with the real nominal ABI-1 `Recipe`.
