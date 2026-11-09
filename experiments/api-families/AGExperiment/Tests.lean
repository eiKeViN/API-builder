module
public import AGExperiment.Core
public meta import AGExperiment.Install

public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

install_scheme_property_core AGExperiment.ProbeFlat
install_scheme_property_source AGExperiment.ProbeFlat
install_scheme_property_core AGExperiment.ProbeEtale
install_scheme_property_source AGExperiment.ProbeEtale
install_scheme_property_core AGExperiment.ProbeSmooth
install_scheme_property_source AGExperiment.ProbeSmooth
install_scheme_property_core AGExperiment.ProbeFinite
install_scheme_property_core AGExperiment.ProbeProper

namespace AGExperiment
variable {X Y Z S : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

example [ProbeFlat f] [ProbeFlat g] : ProbeFlat (f ≫ g) := inferInstance
example [ProbeEtale f] [ProbeEtale g] : ProbeEtale (f ≫ g) := inferInstance
example [ProbeSmooth f] [ProbeSmooth g] : ProbeSmooth (f ≫ g) := inferInstance
example [ProbeFinite f] [ProbeFinite g] : ProbeFinite (f ≫ g) := inferInstance
example [ProbeProper f] [ProbeProper g] : ProbeProper (f ≫ g) := inferInstance

example (f : X ⟶ S) (g : Y ⟶ S) [ProbeFlat g] : ProbeFlat (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeEtale g] : ProbeEtale (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeSmooth g] : ProbeSmooth (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeFinite g] : ProbeFinite (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeProper g] : ProbeProper (pullback.fst f g) := inferInstance

example (f : X ⟶ S) (g : Y ⟶ S) [ProbeFlat f] : ProbeFlat (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeEtale f] : ProbeEtale (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeSmooth f] : ProbeSmooth (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeFinite f] : ProbeFinite (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProbeProper f] : ProbeProper (pullback.snd f g) := inferInstance

example (V : Y.Opens) [ProbeFlat f] : ProbeFlat (f ∣_ V) := inferInstance
example (V : Y.Opens) [ProbeEtale f] : ProbeEtale (f ∣_ V) := inferInstance
example (V : Y.Opens) [ProbeSmooth f] : ProbeSmooth (f ∣_ V) := inferInstance
example (V : Y.Opens) [ProbeFinite f] : ProbeFinite (f ∣_ V) := inferInstance
example (V : Y.Opens) [ProbeProper f] : ProbeProper (f ∣_ V) := inferInstance

example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeFlat f] : ProbeFlat (f.resLE V U e) := inferInstance
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeEtale f] : ProbeEtale (f.resLE V U e) := inferInstance
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [ProbeSmooth f] : ProbeSmooth (f.resLE V U e) := inferInstance

-- These failure tests assert absence of unsupported frontend instances, not a
-- formal mathematical negation of locality or a concrete geometric counterexample.
example (U : X.Opens) (V : Y.Opens) (_e : U ≤ f ⁻¹ᵁ V) [ProbeFinite f] : True := by
  fail_if_success have : ProbeFinite (f.resLE V U _e) := inferInstance
  trivial
example (U : X.Opens) (V : Y.Opens) (_e : U ≤ f ⁻¹ᵁ V) [ProbeProper f] : True := by
  fail_if_success have : ProbeProper (f.resLE V U _e) := inferInstance
  trivial

end AGExperiment
