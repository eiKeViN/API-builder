module
public meta import ApiBuilder.SDK
public meta section
namespace ApiBuilder
open Lean Elab Command
/-- Fixed host type and nominal type name; default meta checks remain enabled. -/
private unsafe def evalSmokeRecipe (name : Name) : CommandElabM SmokeRecipe :=
  evalConstCheck SmokeRecipe ``ApiBuilder.SmokeRecipe name
syntax (name := smokeFamily) "api_smoke " ident " using " ident : command
@[command_elab smokeFamily] unsafe def elabSmokeFamily : CommandElab := fun stx => do
  let recipeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let info ← getConstInfo recipeName
  unless info.levelParams.isEmpty do
    throwErrorAt stx[3] "recipe entrypoint must have no universe parameters"
  recordExtraModUseFromDecl recipeName (isMeta := true)
  let recipe ← evalSmokeRecipe recipeName
  unless recipe.abiVersion == 0 do
    throwErrorAt stx[3] "unsupported recipe ABI {recipe.abiVersion}"
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) do
    recipe.run stx[1].getId
    if (← get).messages.hasErrors then
      throwErrorAt stx "recipe generation logged errors"
end ApiBuilder
