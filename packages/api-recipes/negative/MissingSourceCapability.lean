module
public import ApiRecipesTests.GeometryCore
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ApiRecipesTests.Geometry
scheme_property_api Bad using ProperProbe only [comp, pullback_fst, pullback_snd, restrict, resLE]
#assert_recipe_absent Bad [comp, pullback_fst, pullback_snd, restrict, resLE]
example {X Y S : Scheme} (_f : X ⟶ S) (g : Y ⟶ S) [ProperProbe g] : True := by
  fail_if_success have : ProperProbe (pullback.fst _f g) := inferInstance
  trivial
scheme_property_api Bad using ProperProbe only [pullback_fst]
#assert_recipe_present Bad [pullback_fst]
example {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [ProperProbe g] :
    ProperProbe (pullback.fst f g) := inferInstance
