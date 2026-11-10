module
public meta import ApiRecipesTests.Support
public meta import ApiRecipes
public section
pointwise_api Bad for (ℝ →L[ℝ] ℝ) only [zero, mul]
#assert_recipe_absent Bad [zero_apply, coe_zero, mul_apply, coe_mul]
pointwise_api Bad for (ℝ →L[ℝ] ℝ) only [zero]
#assert_recipe_present Bad [zero_apply, coe_zero]
