# Milestone 1: native fixture cores and handwritten reference

Executed with Lean b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a and mathlib
6da929dc62a7af33b577a22d4a01c08ddfd4f8f6; resolved Aesop is
7d11bfa88558f8d3d90afdf6bd877ed70001498d.

- ContinuousExample.Obj carries its carrier, topology and zero dictionary.
  Map extends ContinuousMap with zero preservation.
- OrderExample.Obj carries its carrier, preorder and point.
  Map extends OrderHom with point preservation.
- Each independent core supplies FunctionView and lawful Composition.
- Examples.Order.Golden handwrites the ten-role API with the same mathematical
  helpers. Native `[ext]` generates ext_iff. GoldenClient verifies function application,
  field notation, ext, simp, associativity, and fresh public wrapper unfolding.
- Mathematical impossibility and choice-operation checks remain in tests/math/Contracts.lean.

Reproduce: `lake build Examples.Continuous.Core Examples.Order.GoldenClient`.
See evidence/milestone1 for actual build status and resolved pins.

The initial `lake update` hook failed trying to write `/home/agent/.cache/mathlib`
(read-only filesystem). Setting `XDG_CACHE_HOME=/workspace/.cache` resolved this
without privilege changes. Only required cache roots and their 981 transitive modules
were requested, not the entire mathlib cache.
