module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
bounded_linear_api Bad using (LinearMap.id : ℝ →ₗ[ℝ] ℝ) where
  bound := 1
  bound := 2
  nonneg := zero_le_one
  estimate := by intro x; simp
#assert_recipe_absent Bad [map, map_apply, norm_le]
