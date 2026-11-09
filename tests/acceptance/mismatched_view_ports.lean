module
public import Examples.Order.Core
public import Examples.Continuous.Core
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
meta import Examples.BadRecipes
api_family OrderExample.Map using ApiBuilder.Recipes.bundledMap where
  view := OrderExample.Core.functionView
  composition := ContinuousExample.Core.composition
open Lean Elab Command in
run_cmd do
  if (ApiBuilder.receipts.getState (← getEnv)).any (·.family == `OrderExample.Map) then
    throwError "TEST: unexpected accepted receipt"
  logInfo "TEST: no accepted receipt"
