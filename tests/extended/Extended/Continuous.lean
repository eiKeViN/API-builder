module
public import Extended.ContinuousCore
public import PointedRecipes.Target
meta import ApiBuilder.FamilyElab
meta import PointedRecipes.Recipes
api_family ContinuousExample.Map using PointedRecipes.pointedMap where
  view := ContinuousExample.Core.functionView
  composition := ContinuousExample.Core.composition
  point := ContinuousExample.Core.point
  preserves_point := ContinuousExample.Core.preserves_point
#api_check ContinuousExample.Map
