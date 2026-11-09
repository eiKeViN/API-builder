# API-builder
A Lean framework maintaining reusable recipes for building APIs.

The prototype builds a conventional bundled-map API from a faithful function view
and lawful identity/composition. A separately packaged Pointed recipe adds a native
mathlib bridge without modifying the framework.

```lean
module
public import Examples.Order.Core
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap

api_family OrderExample.Map using ApiBuilder.Recipes.bundledMap where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.composition

#api_check OrderExample.Map
#api_inspect OrderExample.Map
```

The generated interface includes FunLike, ext/ext_iff, id/comp, application laws,
unit laws and associativity. Ordinary downstream users use `f x`, `g.comp f`, `ext`
and `simp`. Recipes and validators are trusted Lean metaprograms; accepted receipts
are written only after synchronous elaboration, axiom and contract checks succeed.

## Build and verify

Use `lean-toolchain` (v4.36.0-rc2) and the committed mathlib manifest. In the prepared
cloud workspace the toolchain is at `/workspace/toolchains/lean-4.36.0-rc2-linux/bin`.
Set a writable cache directory and avoid automatic whole-mathlib cache downloads:

```sh
export PATH=/workspace/toolchains/lean-4.36.0-rc2-linux/bin:$PATH
export XDG_CACHE_HOME=/workspace/.cache
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
lake exe cache get Mathlib.Topology.ContinuousMap.Basic Mathlib.Order.Hom.Basic Mathlib.Tactic.Ext Mathlib.CategoryTheory.Category.Pointed
python3 scripts/check_all.py
```

For a short interactive check:

```sh
lake build Examples.Order.Client Examples.Continuous.Client Examples.Check
(cd tests/extended && lake build Extended Extended.LocalClient)
```

Golden, generated, bound and choice variants deliberately reuse the same native
family names. Test each alternative in its own importing module; do not import
multiple alternative APIs for the same family together.

- [Current status and limits](docs/STATUS.md)
- [Public recipe SDK](docs/RECIPE_SDK.md)
- [Independent provider](packages/pointed/README.md)
- [Executed evolution tests](docs/MILESTONE3-4.md)
- [API-family validation against dedicated generators](docs/API_FAMILY_VALIDATION.md)

This is a bounded prototype, with local source upgrade tests and explicit supported
contracts. The remaining hardening and independent-author evaluation are listed
in the status document.
