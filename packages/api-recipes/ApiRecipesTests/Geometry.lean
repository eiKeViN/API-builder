module
public import ApiRecipesTests.GeometryCore
public meta import ApiRecipes.SchemeProperty
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ApiRecipesTests.Geometry

-- The core intentionally does not install concrete-class closure instances.
example {X Y S : Scheme} (_f : X ⟶ S) (g : Y ⟶ S) [FlatProbe g] : True := by
  fail_if_success have : FlatProbe (pullback.fst _f g) := inferInstance
  trivial
example {X Y S : Scheme} (_f : X ⟶ S) (g : Y ⟶ S) [FiniteEtaleProbe g] : True := by
  fail_if_success have : FiniteEtaleProbe (pullback.fst _f g) := inferInstance
  trivial

scheme_property_api FlatAPI using FlatProbe only [comp, pullback_fst, pullback_snd, restrict, resLE]
  priority 900
scheme_property_api ProperAPI using ProperProbe only [comp, pullback_fst, pullback_snd, restrict]
scheme_property_api FiniteEtaleAPI using FiniteEtaleProbe only [comp, pullback_fst, pullback_snd, restrict]

variable {X Y Z S : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
example [FlatProbe f] [FlatProbe g] : FlatProbe (f ≫ g) := inferInstance
example [ProperProbe f] [ProperProbe g] : ProperProbe (f ≫ g) := inferInstance
example [FiniteEtaleProbe f] [FiniteEtaleProbe g] : FiniteEtaleProbe (f ≫ g) := inferInstance
example (V : Y.Opens) [FlatProbe f] : FlatProbe (f ∣_ V) := inferInstance
example (V : Y.Opens) [ProperProbe f] : ProperProbe (f ∣_ V) := inferInstance
example (V : Y.Opens) [FiniteEtaleProbe f] : FiniteEtaleProbe (f ∣_ V) := inferInstance
example (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V) [FlatProbe f] :
    FlatProbe (f.resLE V U e) := inferInstance
example (U : X.Opens) (V : Y.Opens) (_e : U ≤ f ⁻¹ᵁ V) [ProperProbe f] : True := by
  fail_if_success have : ProperProbe (f.resLE V U _e) := inferInstance
  trivial

example (f : X ⟶ S) (g : Y ⟶ S) [FlatProbe g] : FlatProbe (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProperProbe g] : ProperProbe (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [FiniteEtaleProbe g] :
    FiniteEtaleProbe (pullback.fst f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [FlatProbe f] : FlatProbe (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [ProperProbe f] : ProperProbe (pullback.snd f g) := inferInstance
example (f : X ⟶ S) (g : Y ⟶ S) [FiniteEtaleProbe f] :
    FiniteEtaleProbe (pullback.snd f g) := inferInstance
end ApiRecipesTests.Geometry
