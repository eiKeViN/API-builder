module
public import Holdout.Specifications
public meta import ApiBuilder.FamilyElab
public meta import MapBaseline.Framework

api_family Holdout.Recipe.SubsemiringAPI using MapBaseline.Framework.galoisFrontend where
  specification := Holdout.Specifications.subsemiring
api_family Holdout.Recipe.SubalgebraAPI using MapBaseline.Framework.galoisFrontend where
  specification := Holdout.Specifications.subalgebra

#api_check Holdout.Recipe.SubsemiringAPI
#api_check Holdout.Recipe.SubalgebraAPI
