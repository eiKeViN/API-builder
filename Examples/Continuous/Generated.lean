module
public import Examples.Continuous.Core
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
api_family ContinuousExample.Map using ApiBuilder.Recipes.bundledMap where
  view := ContinuousExample.Core.functionView
  composition := ContinuousExample.Core.composition
#api_check ContinuousExample.Map
#api_inspect ContinuousExample.Map
