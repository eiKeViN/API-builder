module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
namespace Bad
lemma of_spec : True := trivial
end Bad
iff_api Bad : True ↔ True := Iff.rfl
#assert_recipe_absent Bad [iff_spec, to_spec]
example : True := Bad.of_spec
