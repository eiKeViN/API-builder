module
public import AGExperiment.Core

public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AGExperiment
variable {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

-- Aggregate mathematical instances alone do not install the concrete-class API.
example [ProbeFlat g] : True := by
  fail_if_success have : ProbeFlat (pullback.fst f g) := inferInstance
  trivial
example [ProbeEtale g] : True := by
  fail_if_success have : ProbeEtale (pullback.fst f g) := inferInstance
  trivial
example [ProbeSmooth g] : True := by
  fail_if_success have : ProbeSmooth (pullback.fst f g) := inferInstance
  trivial
example [ProbeFinite g] : True := by
  fail_if_success have : ProbeFinite (pullback.fst f g) := inferInstance
  trivial
example [ProbeProper g] : True := by
  fail_if_success have : ProbeProper (pullback.fst f g) := inferInstance
  trivial
end AGExperiment
