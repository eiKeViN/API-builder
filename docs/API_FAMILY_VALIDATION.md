# API-family validation against dedicated generators

The source audit identified real repetition in native API export and instance
installation. Executed Lean experiments now confirm that small generators can
reuse those patterns across modules. A general recipe framework's productivity
advantage over those generators remains unestablished.

The practical recommendation is to keep generators small, make their public
contracts explicit, and use recipe adapters to investigate composition and
lifecycle checks. The adapters in this experiment remain experimental.

## Scope and fixed inputs

The self-contained [experiment package](../experiments/api-families/README.md)
uses Lean 4.36.0-rc2 (`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`)
and the repository's mathlib pin
`6da929dc62a7af33b577a22d4a01c08ddfd4f8f6`. The initial source audit used
the later `ff2494ea5e438f8a8452db803068acd711fa0059` snapshot. The executed
results concern the pinned experimental package, not a replacement of mathlib's
original declarations or a whole-library duplication census.

The final suite reproduced **47 expected outcomes**. A passing adverse control
means Lean or the relevant checker rejected the intended defect. Source-size
observations are not developer-time or performance measurements. The separate
consumer author was another agent with shared history and access to examples;
this is a bounded transfer test, not a blind or independent human-author study.

## Executed evidence

| Area | Expected outcomes | What was checked |
| --- | ---: | --- |
| map/comap comparison | 21 | Hand-authored/helper, dedicated-command and recipe APIs; clients; exact signatures; binder kinds and public names; attributes; six adverse controls |
| Scheme-property installation | 10 | Five fresh predicate classes, ordinary instance synthesis, capability-gated source restriction, recipe receipts and registration rejection |
| Representation evolution | 7 | Real subgroup-image representation change, unchanged contract/client, clean and incremental rebuilding, body-mirroring counterexample |
| Two additional consumers | 9 | Subsemiring and Subalgebra; macro and recipe variants, composed/named calls, creation-time and fresh-import checks |

[summary.json](../experiments/api-families/evidence/summary.json) records the
fixed versions, counts and source hashes. The package's `evidence/` directory
contains commands, exits and diagnostics. Its runner asserts producer hashes
before and after consumer compilation and that the existing SDK sources remain
unchanged.

## The mathematical helper baseline already exists

The hand-authored frontend calls `GaloisConnection` preservation theorems. It is
therefore also the feature-equivalent generic-helper baseline. Adding a second
six-field mathematical record would duplicate the existing abstraction while
retaining the native-name wrappers. A separate direct-helper client demonstrates
that the mathematical workload can be completed without creating new API names.

For `Subgroup`, `Subring` and semilinear `Submodule`, each frontend supplies:

* `map_sup`, `map_iSup`, `map_bot`;
* `comap_inf`, `comap_iInf`, `comap_top`.

The dedicated command and recipe adapter share one generator. Ordinary consumers
use a short invocation:

```lean
derive_map_comap (f : G →* H) using (Subgroup.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
```

The semilinear case is intentionally asymmetric. Its left-adjoint laws require
`RingHomSurjective σ`; its right-adjoint laws are proved from preimage semantics
without that assumption. Both generated variants preserve the weaker right-side
signatures, and their clients compile without a surjectivity instance.

## Public API quality required more than a successful proof

The common checker is applied to all three frontends. The handwritten frontend
supplies the separately authored signatures; its self-check covers names,
registrations and direct proof dependencies rather than independently validating
its own mathematical statement. For the generated frontends, the checker verifies:

1. Every declared role has the exact fully qualified name.
2. Its type matches a separately authored signature, permitting only bijective
   universe-parameter renaming. Binder kinds/order and public parameter names
   must match.
3. `simp` registration is present, with no unexpected `instance` or `ext` effect.
4. At creation time, the proof has no direct dependency on the reference or the
   corresponding native output theorem. Existing adjunction proofs are allowed.

The clients explicitly name generated declarations. Existing mathlib simp rules
cannot stand in for missing outputs. Lean's module system hides imported proof
bodies, so imported rechecks cover types and effects; body checks run in the
module that creates the declarations.

Six adverse controls were rejected with the intended diagnostics: missing role,
removed macro simp registration, removed recipe simp registration, an extra
surjectivity assumption, direct use of a native gold output theorem, and a renamed
public parameter.
The premise control leaves every map-side signature unchanged, strengthens only
`comap_inf`, and requires a diagnostic naming that role.

Integration found and corrected actual interface defects before the final freeze:
module/public-meta visibility, the semilinear `map_iSup` binder order, and hygiene
scopes in public parameter names. Before the last correction, positional and
rewrite clients passed while named calls failed. Final tests include 18 individual
macro named calls and the additional consumers' eight named-call examples.

The recipe adapter also normalizes the local syntax names explicitly selected by
its closed specification. This is a bounded configuration mechanism, not an
arbitrary hygienic syntax interface.

## Higher-level mathematics: install concrete instances from capabilities

Fresh `ProbeFlat`, `ProbeEtale`, `ProbeSmooth`, `ProbeFinite` and `ProbeProper`
classes avoid reusing the native concrete instances as the test result. They
receive aggregate mathematical capabilities from their native counterparts.
With only those capabilities, the five concrete pullback instance requests fail.

The 51-SLOC dedicated installer then provides 23 concrete instances across the
five probes. For the first three, source restriction is enabled only after Lean
checks a source-locality capability. Requests for that route on the finite and
proper probes fail. The ABI-1 adapter reuses the same installer and accepts five
family receipts. Removing a generated pullback instance's registration causes a
precise `#api_check` rejection.

One refinement to the initial audit is important: source and target locality
give a **sufficient** route to `resLE`, not a necessary characterization.
Separatedness, for example, can use another route involving open-immersion
precomposition. The current negative tests establish absence of the selected
capability/installation, not a general mathematical impossibility theorem.

## Stable observation interfaces survive representation changes

The evolution test changes the actual subgroup-image carrier:

```lean
-- V1
carrier := f '' (p : Set G)
-- V2
carrier := Set.range (fun x : p => f x)
```

The fixed public contract is:

```lean
y ∈ Evolution.map f p ↔ ∃ x ∈ p, f x = y
```

Keeping the old `Iff.rfl` proof after the representation change is rejected.
Replacing only that proof with a subtype/existential adapter restores the old
contract and client in both incremental and clean builds. Client and contract
bytes remain unchanged throughout, with SHA-256 assertions at every step.

A theorem mirroring V2's new body, with RHS `∃ x : p, f x = y`, compiles by itself
but is rejected by the fixed old signature. Thus automatically regenerating a
current-body iff does not establish compatibility. This test uses explicit body
variants and a fixed Lean type check; it does not claim a new iff generator or
general semantic comparator.

## Transfer after freezing the implementation

A separate agent adapted `Subsemiring` and `Subalgebra` without object-specific
producer changes. The final clean run uses the same frozen generator, adapter,
checker and SDK hashes. Each path generates twelve declarations and supports
four composed clients. Creation-time checks and imported receipt checks pass;
named calls include the public type parameters and `f/p/q`.

The transfer remains narrow: both new objects have an existing Galois connection,
and the author saw the interface and examples. Integration corrections preceded
the final freeze. The earlier named-call failures are retained in
[provenance/hygiene-before.log](../experiments/api-families/evidence/provenance/hygiene-before.log).

## Cost and architecture decision

[COSTS.md](../experiments/api-families/COSTS.md) and its machine-readable inventory
count imports, scope boilerplate, configuration, generators, checkers and required
reference declarations. Formatting, comments and blank lines are handled by one
reproducible scanner. Calling-site line counts alone are not the comparison.

The adapter currently requires an independent six-signature reference namespace
for every family. That is useful evaluation infrastructure and a real production
input cost. The reference must not be treated as free merely because the macro
also uses it in the fair checked comparison. The recipe adapter additionally
requires closed metaprogram configuration; the dedicated command is shorter for
these cases.

The two additional consumers illustrate that difference: their checked macro
configuration occupies 22 nonblank lines, versus 42 for recipe specification and
invocation; both share a reference file. These observations support reuse, not a
productivity win for the framework.

The resulting design direction is:

* Keep domain-specific generators as ordinary reusable Lean modules.
* Reuse existing mathematics, `simps`, `mk_iff`, translation and instance builders.
* Specify observable statements, names, binders, attributes and premise budgets.
* Keep the framework adapters experimental while measuring whether reusable
  contracts, composition and upgrade checks justify their configuration cost.

The next product gate should be an independent author using the frozen public
interface during a real library change, compared against the strongest small
command with the same checks. This suite supplies concrete candidates and adverse
controls for that evaluation.
