module
public import Examples.Order.Core
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
meta import Examples.BadRecipes
public def wrongComposition : Nat := 0
api_family OrderExample.Map using ApiBuilder.Recipes.bundledMap where
  view := OrderExample.Core.functionView
  composition := wrongComposition
open Lean Elab Command in
run_cmd do
  if (ApiBuilder.receipts.getState (← getEnv)).any (·.family == `OrderExample.Map) then
    throwError "TEST: unexpected accepted receipt"
  logInfo "TEST: no accepted receipt"
