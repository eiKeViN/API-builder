module
public import AGExperiment.Core
public meta import ApiBuilder.FamilyElab
public meta import AGExperiment.Recipe

api_family AGExperiment.ProbeFinite using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeFinite
  source_restriction := AGExperiment.sourceRestriction
