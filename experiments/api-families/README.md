# Reusable API-family validation

The [result and design decision](../../docs/API_FAMILY_VALIDATION.md) are based on
47 expected outcomes using the repository's fixed Lean/mathlib versions. This is
an isolated experimental package; its generators reuse existing mathematics and
its recipe adapters use the existing ABI-1 SDK.

## Run

From the repository root, with the pinned Lean toolchain on `PATH`:

```sh
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
lake exe cache get Mathlib.Algebra.Group.Subgroup.Map Mathlib.Algebra.Ring.Subring.Basic Mathlib.Algebra.Module.Submodule.Map Mathlib.Algebra.Algebra.Subalgebra.Lattice Mathlib.AlgebraicGeometry.Morphisms.Etale Mathlib.AlgebraicGeometry.Morphisms.Proper
python3 experiments/api-families/run_validation.py
python3 experiments/api-families/measure_sources.py
```

The committed nested manifest inherits the root package and fixed dependencies.
On Linux, its `.lake/packages` may share the root cache via a local symlink;
ordinary Lake dependency materialization also works.

`run_validation.py` checks all positive modules and intended rejection diagnostics.
It then runs seven real clean/incremental representation-evolution cases, restores
the original evolution fixture, and writes `evidence/summary.json`. Direct
`lake build` inside this directory builds the selected positive examples.

## Files

| Path | Responsibility |
| --- | --- |
| `MapBaseline/` | Handwritten/helper API, dedicated generator, shared contract checker, recipe adapter and clients |
| `AGExperiment/` | Capability-gated scheme-property instance installer and recipe alternative |
| `Holdout/` | Two additional consumers authored by a separate agent after the producer interface was provided |
| `Evolution/`, `variants/` | Fixed observation contract/client and four concrete representation variants |
| `negative/` | Intentionally rejected modules, outside the positive library trees |
| `evidence/` | Commands, exits, diagnostics, frozen hashes and measured source inventory |
| `COSTS.md` | Source cost accounting and interpretation |

The macro and recipe AG modules intentionally generate alternative declarations
with the same names; use them in separate importing modules as the runner does.
Frozen source guards deliberately stop the suite if the generator, adapter or
checker changes. Update the protocol and expected hashes explicitly when
conducting a new experiment.

## Environment compatibility

The original managed executor exposed `/proc/self/exe` while its numerical PID
namespace did not match procfs. Official Lean/Lake therefore could not locate
their own executables. `support/selfpath.c` is the exact compatibility shim used:
it normalizes only the current process's equivalent executable path. Lean's
distributed binaries and kernel were unchanged. Normal hosts do not need this.
If this specific procfs mismatch occurs, compile that file as a shared library
and set `LD_PRELOAD` for the run. This support code is excluded from generator
cost totals.
