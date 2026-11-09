module
public import Examples.Order.BoundCore
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
api_family OrderExample.Map using ApiBuilder.Recipes.bundledMap where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.composition
  bind_instance := OrderExample.existingDictionary
  bind_id := OrderExample.Map.id
  bind_comp := OrderExample.Map.comp
#api_check OrderExample.Map
#api_inspect OrderExample.Map
