module
public import Extended.OrderCore
meta import ApiBuilder.FamilyElab
meta import Extended.LocalRecipe
api_family OrderExample.Map using LocalRecipes.localMap where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.composition
#api_check OrderExample.Map
#api_inspect OrderExample.Map
