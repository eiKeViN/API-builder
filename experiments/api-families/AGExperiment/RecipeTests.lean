module
public import AGExperiment.Core
public meta import ApiBuilder.FamilyElab
public meta import AGExperiment.Recipe

public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

api_family AGExperiment.ProbeFlat using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeFlat
  source_restriction := AGExperiment.sourceRestriction
api_family AGExperiment.ProbeEtale using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeEtale
  source_restriction := AGExperiment.sourceRestriction
api_family AGExperiment.ProbeSmooth using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeSmooth
  source_restriction := AGExperiment.sourceRestriction
api_family AGExperiment.ProbeFinite using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeFinite
api_family AGExperiment.ProbeProper using AGExperiment.schemeProperty where
  property := AGExperiment.ProbeProper

#api_check AGExperiment.ProbeFlat
#api_check AGExperiment.ProbeEtale
#api_check AGExperiment.ProbeSmooth
#api_check AGExperiment.ProbeFinite
#api_check AGExperiment.ProbeProper

namespace AGExperiment
variable {X Y S : Scheme} (f : X ⟶ Y)
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeFlat f] : ProbeFlat (f.resLE V U e) := inferInstance
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeEtale f] : ProbeEtale (f.resLE V U e) := inferInstance
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeSmooth f] : ProbeSmooth (f.resLE V U e) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeFinite g] : ProbeFinite (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeProper f] : ProbeProper (pullback.snd f g) := inferInstance
example (U : X.Opens) (V : Y.Opens) (_e : U ≤ f ⁻¹ᵁ V) [ProbeFinite f] : True := by
  fail_if_success have : ProbeFinite (f.resLE V U _e) := inferInstance
  trivial
example (U : X.Opens) (V : Y.Opens) (_e : U ≤ f ⁻¹ᵁ V) [ProbeProper f] : True := by
  fail_if_success have : ProbeProper (f.resLE V U _e) := inferInstance
  trivial
end AGExperiment
