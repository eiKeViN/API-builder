module
public import MapBaseline.Specifications
public meta import ApiBuilder.FamilyElab
public meta import MapBaseline.Framework

api_family MapBaseline.Recipe.GroupAPI using MapBaseline.Framework.galoisFrontend where
  specification := MapBaseline.Specifications.group
api_family MapBaseline.Recipe.RingAPI using MapBaseline.Framework.galoisFrontend where
  specification := MapBaseline.Specifications.ring
api_family MapBaseline.Recipe.ModuleAPI using MapBaseline.Framework.galoisFrontend where
  specification := MapBaseline.Specifications.semilinear

#api_check MapBaseline.Recipe.GroupAPI
#api_check MapBaseline.Recipe.RingAPI
#api_check MapBaseline.Recipe.ModuleAPI
