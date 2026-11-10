# Galois API tools

A standalone Lean 4 command extension for exporting a conventional map/comap API
from existing mathematics. The package depends only on Lean and mathlib. Its
production modules import neither API Builder nor the evaluation fixtures.

## Ordinary use

```lean
module
public import Mathlib.Algebra.Group.Subgroup.Map
public meta import GaloisApi.Basic
public section

namespace Example
variable {G H : Type*} [Group G] [Group H]
galois_api MapAPI (f : G →* H) using (Subgroup.gc_map_comap f)

example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  MapAPI.map_sup (f := f) (p := p) (q := q)
end Example
```

The command creates public, ordinary `[simp]` theorems named `map_sup`, `map_iSup`,
`map_bot`, `comap_inf`, `comap_iInf`, `comap_top` under the requested namespace.
The namespace is relative to the current namespace; `_root_.Name` is also supported.
Source ranges point to the invocation. Consumers use normal names, `rw`, `simp`
and named arguments. There is no specification metaprogram to author.

The export convention puts section parameters first, then an optional index `ι`,
the supplied operation binders, and `p/q`. Existing mathlib declarations do not
all follow that convention. Preserving an older argument order requires an
explicit wrapper and a matching contract; this tool is not a drop-in rewrite of
every existing mathlib frontend.

## Select a side or install missing members

```lean
galois_map_api MapAPI (f : G →* H) using (Subgroup.gc_map_comap f)
  only [map_sup, map_iSup]
galois_map_api MapAPI (f : G →* H) using (Subgroup.gc_map_comap f)
  only [map_bot]
galois_comap_api MapAPI (f : G →* H) using (Subgroup.gc_map_comap f)
```

These calls replace the whole-family call in the first example. All three Galois
commands accept `only [...]`; the default is their full supported role set.
Names are conventional. For other spellings, ordinary Lean aliases can be used.
Already-present output names cause a preflight error; the tool never infers that
an existing theorem is an appropriate binding.

## Preserve different premise budgets

For a semilinear submodule map, the Galois connection requires a surjective scalar
homomorphism. Its comap preservation laws need no such assumption. Use ordinary
Lean sections to keep the premises separate:

```lean
variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {σ : R →+* S}
section
variable [RingHomSurjective σ]
galois_map_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.gc_map_comap f)
end

preimage_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.comap f) on (Submodule S N) where
  inf := by rfl
  iInf := by ext x; simp only [Submodule.mem_comap, Submodule.mem_iInf]
  top := by rfl
```

Import `Mathlib.Algebra.Module.Submodule.Map` for this example. The three preimage
proofs are explicit mathematical obligations. The generator does not discover
them or acquire stronger assumptions from an unrelated family member.

## Optional interface checks

```lean
public meta import GaloisApi.Check
-- After generation, with a separately authored Reference namespace:
#check_galois_api ModuleAPI against Reference.ModuleAPI
```

The checker validates public names, signatures modulo bijective universe renaming,
binder kinds/order/names, expected simp registration, absence of extra instance/ext
registration, and the standard axiom whitelist. It accepts `only [...]` for a partial
interface and can be called again in a fresh importing module. A reference consists
of independent expected signatures; authoring and maintaining it is a real cost.
Generation itself does not require this reference. Import `GaloisApi` to load both
commands and the checker, or import `GaloisApi.Basic` alone for generation.

## Execution and failure behavior

Every selected output name is checked before generation. Unknown/duplicate roles,
bad field names and omitted preimage proof fields are diagnosed. A failed
synchronous generation restores the Lean command environment, including earlier
outputs in the same batch. Original elaboration diagnostics are retained, and a
corrected command can reuse the same names. Generated proofs using `sorryAx` or
other nonstandard axioms are rejected.

This is ordinary trusted Lean metaprogramming. The rollback concerns compiler
state for this command; it does not undo arbitrary IO performed by user tactics.
Automatic type inference from the mathematical input does not by itself guarantee
compatibility after input changes. Use an explicit reference and downstream clients
when a stable public interface is required.

## Build, test and reuse

With the pinned toolchain and normal mathlib cache prepared:

```sh
lake update
lake build GaloisApi
python3 test.py
python3 test_evolution.py
python3 measure.py
```

The suite covers five subobject APIs, ordinary set image/preimage, partial exports,
root/nested namespaces, public named arguments, source ranges, a separate external
Lake consumer, and targeted failure controls. A real subgroup carrier change from
`Set.image` to subtype `Set.range` is tested with unchanged generator invocation,
reference and client in clean and incremental builds. Results and diagnostics are
in `evidence/`. Wall times are observations, not comparative benchmarks.

For local reuse, add a normal Lake dependency pointing to this package:

```toml
[[require]]
name = "galoisApi"
path = "../API-builder/packages/galois-api"
```

`tests/consumer` is an executed example of a separate package with this dependency.
Git consumers can pin the repository revision and select `packages/galois-api`
with Lake's `subDir` dependency option.

## Architecture

| Module | Responsibility |
| --- | --- |
| `GaloisApi.Basic` | Fixed family schema, native proof generation, selection, preflight and failure recovery |
| `GaloisApi.Check` | Explicit comparison against an independent public interface |
| `GaloisApiTests` / `tests` | Evaluation fixtures, clients, adverse controls and evolution scenarios |

This domain-specific generator can itself implement a reusable recipe. A generic
recipe manager may call it when cross-family composition, ownership records or
shared lifecycle policies are useful. The mathematical generator does not need
that manager to function. See the [design report](../../docs/DEDICATED_GENERATOR_DESIGN.md).
