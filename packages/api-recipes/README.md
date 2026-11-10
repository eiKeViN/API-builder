# Four reusable API recipes

Four ordinary Lean command modules cover foundational observation/algebra APIs,
normed linear operators and scheme morphism properties. Import the individual
module you need, or `public meta import ApiRecipes` for all four. This standalone
Lake package depends only on mathlib, at the same pin as the rest of this repo;
there is no dependency on the API Builder dispatcher or on `galois-api`.

| Module / command | Author supplies | Generated API | Existing mathematics reused |
| --- | --- | --- | --- |
| `ApiRecipes.Observation` / `iff_api` | An explicit `P ↔ Q` contract and its proof | `iff_spec`, `of_spec`, `to_spec` | `Iff`; a supplied observation proof |
| `ApiRecipes.Pointwise` / `pointwise_api` | A function-like type and an explicit operation list | Native `*_apply` and `coe_*` lemmas | mathlib's `Is*Apply` classes and `FunLike` lemmas |
| `ApiRecipes.BoundedLinear` / `bounded_linear_api` | A linear map, a nonnegative bound and an estimate | A named continuous map, application/linearity, continuity and norm bound | `LinearMap.mkContinuous`, its norm theorem and continuous-linear-map laws |
| `ApiRecipes.SchemeProperty` / `scheme_property_api` | A concrete Prop class with proven aggregate capabilities; selected roles | Concrete composition, pullback and restriction instances | `MorphismProperty` and Zariski locality |

## Foundational: a fixed observation contract

```lean
iff_api DoubleAPI (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := doubled_spec n
```

The predicate and `doubled_spec` can come from a mathematical core whose definition
body is hidden to importing modules. This exports three ordinary theorems. For
example, `DoubleAPI.of_spec (n := n) (hSpec := h)` constructs the predicate, while
`DoubleAPI.to_spec (n := n) (hPred := h)` observes it. Both directions reuse the
generated `iff_spec`; the supplied proof is elaborated once.

Use `iff_api simp ...` to mark only the iff theorem `[simp]`. Default installation
does not unfold every predicate during simplification. The contract must be
syntactically `P ↔ Q`, optionally parenthesized. Ordinary explicit/implicit Lean
binders, including universe-polymorphic `Type*` parameters, are supported.

This wraps an explicitly chosen semantic interface. It does not infer the desired
meaning from a definition's current body, and does not replace mathlib's `mk_iff`
for inductive/structure propositions.

## Foundational: native pointwise algebra names

```lean
open scoped ZeroAtInfty
variable {α : Type*} [TopologicalSpace α]

pointwise_api VanishingAPI for C₀(α, ℝ) only [zero, add, neg, sub]
pointwise_smul_api VanishingAPI for C₀(α, ℝ) scalars ℝ
```

Each selected operation exports two `[simp]` lemmas, such as `add_apply` and
`coe_add`; the coe lemma also receives `[norm_cast]`. Supported operations are
`zero`, `one`, `add`, `mul`, `neg`, `inv`, `sub`, `div`, plus the separate scalar
command. Selection is mandatory and supports incremental installation.

Operations and their `Is*Apply` witnesses must already exist. The command adds
neither operations nor algebraic structure instances. Continuous-linear-map
multiplication is composition: an attempted pointwise multiplication export is
rejected when the corresponding capability is absent. mathlib already provides
the generic algebraic abstraction; this recipe only assembles native frontend
names. Use those generic lemmas directly when native aliases add no value.

## Analysis: a named operator from a bound

```lean
bounded_linear_api ScaleAPI (c : ℝ) using (c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) where
  bound := ‖c‖
  nonneg := norm_nonneg c
  estimate := by
    intro x
    simpa only [LinearMap.smul_apply, LinearMap.id_apply] using (norm_smul c x).le
```

This exports `ScaleAPI.map`, `map_apply`, `map_zero`, `map_add`, `map_smul`,
`continuous`, and `norm_le`. The first is a public exposed noncomputable definition;
the next four are `[simp]` theorems. For example:

```lean
example (c : ℝ) : ‖ScaleAPI.map c‖ ≤ ‖c‖ := ScaleAPI.norm_le (c := c)
```

The norm bound is the exact supplied bound; the explicit nonnegativity proof
justifies that promise. Put all varying operation inputs in explicit named
binders `(arg : Type)`; type/instance parameters belong in the surrounding Lean
section. Those binders are preserved on the outputs, including any proof binders
the author explicitly lists. Generated `x/y/r` argument names receive a suffix
when necessary to avoid capturing an input identifier. `map_smul` retains the
native scalar action; it does not impose a pointwise multiplication operation.

## Algebraic geometry: install only supported closure instances

```lean
scheme_property_api FlatAPI using FlatProbe
  only [comp, pullback_fst, pullback_snd, restrict, resLE] priority 900
```

`FlatProbe` is a concrete class on scheme morphisms. This invocation requires
composition stability, base-change stability, target locality, and source
locality for the respective selected outputs. The optional priority defaults to
1000. No new locality or stability theorem is invented.

The clients use fresh flat/proper classes and a composite finite-étale class.
Before installation, aggregate capabilities alone do not synthesize their
concrete pullback instances; afterward they do. Proper and finite-étale examples
select the four supported composition/base-change/target-restriction roles.
An attempted proper `resLE` installation is rejected for lack of the selected
source-locality capability. That capability is a sufficient route for this
installer, not a necessary mathematical characterization of `resLE` stability.

The external consumer composes this recipe with `iff_api` in the same namespace,
and composes `bounded_linear_api` with `pointwise_api` in a normed-operator client.

## Failure behavior and validation

All selected names are checked before installation. Unknown/duplicate roles and
fields are rejected. A synchronous generation failure restores this command's
Lean state, preserving diagnostics; a corrected command can reuse its namespace.
Generated declarations are checked for nonstandard axiom dependencies, including
`sorryAx`. Rollback does not undo arbitrary external IO performed by user tactics.

With the pinned toolchain on `PATH`:

```sh
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
python3 test.py
python3 measure.py
```

`test.py` records 22 expected outcomes: package/client/interface checks, 14 intended
rejections, external dependency resolution/use, and four representation-evolution
outcomes. Twenty independent expected signatures check names, binder kinds/order,
public parameter names and universe generality; automation checks also cover all
13 generated scheme instances and each tested simp export. Expected failures must
match their intended diagnostics and absence/recovery assertions.

The evolution fixture changes a predicate from an existential to `Nonempty` of a
subtype. The old reflexive observation proof fails; updating only its core adapter
restores clean and incremental builds with the generator, reference and clients
unchanged. Logs, source hashes and the source inventory are in `evidence/`.

The included test runner can share already materialized dependency sources with
its child Lake projects. A new machine still needs the pinned Lean toolchain and
mathlib dependencies/builds; the root repo README describes the cache workflow.
These tests establish working implementations and bounded reuse, without measuring
long-term author productivity or proving that a universal recipe framework is needed.
