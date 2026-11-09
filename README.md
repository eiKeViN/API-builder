# API-builder
A Lean framework maintaining reusable recipes for building APIs.

Construction has started with a compiled native-extension/rebuild experiment.
See [status and evidence](docs/STATUS.md) for the exact verified scope and remaining milestones.

With the pinned Lean toolchain (`lean-toolchain`) on PATH:

```sh
lake build
python3 scripts/test_smoke.py
```

The smoke suite uses isolated temporary package copies and leaves provider sources unchanged.
It does not need mathlib. This is not yet the bundled-map API generator.
