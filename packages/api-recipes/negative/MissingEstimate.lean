module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
bounded_linear_api Bad using (LinearMap.id : ℝ →ₗ[ℝ] ℝ) where
  bound := 1
  nonneg := zero_le_one
#assert_recipe_absent Bad [map, map_apply, map_zero, map_add, map_smul, continuous, norm_le]
