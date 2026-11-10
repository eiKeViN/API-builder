module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
bounded_linear_api Bad using (LinearMap.id : ℝ →ₗ[ℝ] ℝ) where
  bound := 1
  nonneg := True.intro
  estimate := by intro x; simp
#assert_recipe_absent Bad [map, map_apply, map_zero, map_add, map_smul, continuous, norm_le]
bounded_linear_api Bad using (LinearMap.id : ℝ →ₗ[ℝ] ℝ) where
  bound := 1
  nonneg := zero_le_one
  estimate := by intro x; simp
#assert_recipe_present Bad [map, map_apply, map_zero, map_add, map_smul, continuous, norm_le]
