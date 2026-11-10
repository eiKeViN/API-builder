module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
iff_api Bad (P : Prop) : P ↔ P := by sorry
#assert_recipe_absent Bad [iff_spec, of_spec, to_spec]
