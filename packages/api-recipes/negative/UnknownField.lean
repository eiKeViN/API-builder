module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
bounded_linear_api Bad using (LinearMap.id : ℝ →ₗ[ℝ] ℝ) where
  typo := 1
#assert_recipe_absent Bad [map, map_apply, norm_le]
