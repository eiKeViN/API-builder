# Construction status

## Sources actually read (2026-11-09)

- [Prototype contract](https://chatgpt.com/space/page_daba96657c448191ae0e0ab58804dab4)
- [Source guide](https://chatgpt.com/space/page_52ead59314908191a7631b11eae7f29f)
- Library `libfile_50864eaf618c8191a39d23e67c9119fe`, research archive SHA-256
  `b9162d14aef71c8d50675bea21023fd41ea5a7440903718b4af9672a7f5c0f83`.
  Materialized and extracted outside the repository at `/workspace/research`.
  Read BUILD_START, prototype-design, sdk-audit, acceptance-matrix, STATE and review-record.
  Their research-only authorization describes the prior phase; the current construction request supersedes it.
- Initial repository: `a81cc4e`, only the original README, no AGENTS.md found.

## Executed milestone 0

Lean reports `4.36.0-rc2`, commit
`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`.
The official Linux release was extracted under `/workspace/toolchains` as the ordinary user.
Archive SHA-256: `0a0a3208617e9eab92f1041efa83ad94d405e69d172fb654a62dbfa9fbc5313b`.
No system installation, upstream modification, push, PR or deployment.

Three Lake packages exercise a minimal nominal `Recipe` and `api_smoke` command.
The unsafe bridge fixes both runtime type and nominal type name; entrypoints must
have no universe parameters, ABI 0, and pass Lean's default meta-execution checks.
Dynamic use is recorded, with explicit meta imports. Local command scope disables
async elaboration. A logged error makes the command fail.

`python3 scripts/test_smoke.py` copies sources into an isolated temporary workspace,
then records commands, diagnostics and statuses under `evidence/milestone0`:

- Clean separate-provider/consumer build and fresh imported evaluation: **21**.
- A proof expecting **22** fails before mutation (stale-result sensitivity control).
- Recipe body `helperValue + 1` → `helperValue + 2`: ordinary `lake build` rebuilds
  the unchanged consumer; value **22**, and the previous failing proof passes.
- Helper body `20` → `30`, reached through public meta facade: ordinary build
  rebuilds helper, provider and unchanged consumer; value **32**.
- Wrong nominal entrypoint: exit 1 with `ApiBuilder.Recipe expected`.
- Provider logs an error and returns: exit 1, including dispatcher diagnostic.
- Unused provider import does not create `Generated.value`.

The script verifies the consumer source hash remains unchanged. Generated module
body exposure is tested by a fresh ordinary import. Logs retain the exact resolved
local-package manifest. This supports E01/E04/E05/E06 and the declaration portion
of E07; it does not establish all E02/E03 cases or instance/simp side effects.

An initial compilation found that CommandElabM has no MonadWithOptions instance;
using the native `Command.withScope` option mechanism fixed it. No meta check was disabled.

## Scope limits and next gates

This is a compiled milestone-0 experiment, **not a usable bundled-map generator**.
`Recipe.run` and `api_smoke` are deliberately provisional. There are no accepted
family receipts, validators, mathematical API claims, axiom-policy barrier or binding
support yet. The complete acceptance barrier must precede calling milestone 2 usable.

Next: native FunctionView/Composition helpers, two independent mathlib-backed cores,
and handwritten golden API (milestone 1); then ten-role generation and acceptance
barriers; then external PointedRecipes and maintenance gates. Pin mathlib to
`6da929dc62a7af33b577a22d4a01c08ddfd4f8f6` and its Aesop dependency to
`7d11bfa88558f8d3d90afdf6bd877ed70001498d` when those dependencies enter the build.

## Mathematical foundation executed after milestone 0

`ApiBuilder/Mathematics.lean` implements the specified three-universe
FunctionView/Composition records directly using Lean's existing Function.Injective.
It proves extensionality, both units and associativity without mathlib or new axioms.
The root library builds this module.

`lake env lean tests/math/Contracts.lean` is a fresh public-import test. It checks
choice-defined noncomputable identity/composition using only their propositional
laws, proves that forgetting a Bool tag is not injective, and proves that the set
{identity, successor} is not closed under the required composition. These last two
are checked impossibility theorems, **not** generated malformed-input rejection
fixtures. Native `collectAxioms` checks the generic proofs and choice-based core
against propext/Classical.choice/Quot.sound; no sorryAx is permitted. Logs are in
`evidence/mathematics`.

The exact mathlib commit was fetched into ignored `.lake/packages/mathlib` and its
lean-toolchain and resolved Aesop pin verified against the specification. It has
not been added as a package dependency or built: the current tested foundation
needs only Lean. The two required mathlib-backed fixture cores and golden API are
still outstanding, so **milestone 1 is partial**. Milestones 2–4 are unimplemented.
There is no observed permission or source-access blocker. This checkpoint is a
bounded initial construction delivery, not a claim of full prototype completion.
