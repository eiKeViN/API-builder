module
public meta import ApiRecipes.Command
public meta section
namespace ApiRecipesTests.Support
open Lean Elab Command Meta

private def binders : Expr → List (Name × BinderInfo)
  | .forallE n _ b i => (n, i) :: binders b
  | _ => []

/-- An independent expected declaration supplies the full public signature. -/
def checkType (actual reference : Name) : CommandElabM Unit := do
  unless ((← getEnv).setExporting true).contains actual do
    throwError "contract: missing public declaration '{actual}'"
  let a ← getConstInfo actual
  let b ← getConstInfo reference
  unless a.levelParams.length == b.levelParams.length do
    throwError "contract: universe count mismatch '{actual}'"
  let names := fun e => (binders e).filterMap fun (n, i) =>
    if i == .instImplicit then none else some n
  unless (binders a.type).map Prod.snd == (binders b.type).map Prod.snd && names a.type == names b.type do
    throwError "contract: binder mismatch '{actual}'"
  liftTermElabM do
    let levels ← mkFreshLevelMVarsFor a
    unless ← withTransparency .default (isDefEq (a.type.instantiateLevelParams a.levelParams levels) b.type) do
      throwError "contract: signature mismatch '{actual}'"
    let solved ← levels.mapM instantiateLevelMVars
    let rigid := b.levelParams.map Level.param
    unless solved.all rigid.contains && rigid.all solved.contains do
      throwError "contract: universe generality mismatch '{actual}'"
  ApiRecipes.Command.checkAxioms actual

syntax (name := checkRecipeType) "#check_recipe_type " ident " against " ident : command
@[command_elab checkRecipeType] def elabType : CommandElab := fun s =>
  checkType s[1].getId s[3].getId

syntax (name := recipeAbsent) "#assert_recipe_absent " ident "[" ident,* "]" : command
@[command_elab recipeAbsent] def elabAbsent : CommandElab := fun s => do
  for role in s[3].getSepArgs do
    let name := s[1].getId ++ role.getId
    if (← getEnv).contains name || (← liftCoreM <| isInstance name) then
      throwError "unexpected surviving output '{name}'"
  logInfo "ROLLBACK_OK"

syntax (name := recipePresent) "#assert_recipe_present " ident "[" ident,* "]" : command
@[command_elab recipePresent] def elabPresent : CommandElab := fun s => do
  for role in s[3].getSepArgs do
    unless ((← getEnv).setExporting true).contains (s[1].getId ++ role.getId) do
      throwError "missing recovered output '{role.getId}'"
  logInfo "RECOVERY_OK"

syntax (name := recipeSimp) "#assert_recipe_simp " ident : command
@[command_elab recipeSimp] def elabSimp : CommandElab := fun s => do
  unless (← liftCoreM getSimpTheorems).isLemma (.decl s[1].getId) do
    throwError "contract: missing simp registration '{s[1].getId}'"

syntax (name := recipePlain) "#assert_recipe_plain " ident : command
@[command_elab recipePlain] def elabPlain : CommandElab := fun s => do
  if (← liftCoreM getSimpTheorems).isLemma (.decl s[1].getId) ||
      (← liftCoreM <| isInstance s[1].getId) then
    throwError "contract: unexpected automation registration '{s[1].getId}'"

syntax (name := recipeInstance) "#assert_recipe_instance " ident num : command
@[command_elab recipeInstance] def elabInstance : CommandElab := fun s => do
  unless (← liftCoreM <| getInstancePriority? s[1].getId) == s[2].isNatLit? do
    throwError "contract: missing instance or wrong priority '{s[1].getId}'"

syntax (name := recipeNoDispatcher) "#assert_no_recipe_dispatcher" : command
@[command_elab recipeNoDispatcher] def elabNoDispatcher : CommandElab := fun _ => do
  if (← getEnv).contains `ApiBuilder.Recipe then throwError "unexpected framework dependency"
end ApiRecipesTests.Support
