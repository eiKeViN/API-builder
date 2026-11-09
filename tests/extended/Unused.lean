module
public import Extended.OrderCore
meta import ApiBuilder.FamilyElab
meta import PointedRecipes.Recipes
open Lean Elab Command in
run_cmd do
  for n in [`OrderExample.Map.instFunLike, `OrderExample.Map.ext,
      `OrderExample.Map.toPointedHom] do
    if (← getEnv).contains n then throwError "unused provider activated {n}"
  unless (ApiBuilder.receipts.getState (← getEnv)).isEmpty do
    throwError "unused provider accepted a family"
