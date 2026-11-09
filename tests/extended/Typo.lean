module
public import Extended.OrderCore
public import PointedRecipes.Target
meta import ApiBuilder.FamilyElab
meta import PointedRecipes.Recipes
api_family OrderExample.Map using PointedRecipes.pointedMap where
  view := OrderExample.Core.functionView
  composition := OrderExample.Core.composition
  point := OrderExample.Core.point
  preserves_point := OrderExample.Core.preserves_point
  typo := OrderExample.Core.point
