module
public import MapBaseline.Specifications
public meta import ApiBuilder.FamilyElab
public meta import MapBaseline.Framework

public meta section
namespace MapBaseline.Bad
open Lean Elab Command
def extraAssumption : Framework.SpecificationBuilder := do
  let spec ← Specifications.semilinear
  -- Keep all three map signatures unchanged. Only the advertised comap_inf
  -- acquires the unwanted assumption, so an earlier map binder failure cannot
  -- make this adverse control pass accidentally.
  let bad ← `(command| @[simp] public theorem MapBaseline.Bad.ModuleAPI.comap_inf
    [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p q : Submodule S N) :
      (p ⊓ q).comap f = p.comap f ⊓ q.comap f := rfl)
  pure { spec with
    context := spec.context.push bad
    make := fun family => do
      let c ← spec.make family
      pure { c with names := c.names.set! 3 (mkIdent (family ++ `unused_comap_inf)) } }
end MapBaseline.Bad
end

api_family MapBaseline.Bad.ModuleAPI using MapBaseline.Framework.galoisFrontend where
  specification := MapBaseline.Bad.extraAssumption

run_cmd do
  let rs := ApiBuilder.receipts.getState (← Lean.getEnv)
  if rs.any (·.family == `MapBaseline.Bad.ModuleAPI) then
    throwError "invalid family unexpectedly received an accepted receipt"
