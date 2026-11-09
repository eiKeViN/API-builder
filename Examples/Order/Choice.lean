module
public import Examples.Order.ChoiceCore
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
api_family OrderExample.Map using ApiBuilder.Recipes.bundledMap where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.choiceComposition
#api_check OrderExample.Map
