module
public import Mathlib.Analysis.Normed.Operator.Basic
public meta import ApiRecipes.BoundedLinear
public section
namespace ApiRecipesTests.BoundedLinear

section Generic
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

bounded_linear_api GenericAPI (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) using L where
  bound := C
  nonneg := hC
  estimate := h

example (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, ‖L x‖ ≤ C * ‖x‖)
    (x y : E) : GenericAPI.map L C hC h (x + y) = L x + L y := by
  rw [GenericAPI.map_add, GenericAPI.map_apply, GenericAPI.map_apply]
example (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) :
    Continuous (GenericAPI.map L C hC h) := GenericAPI.continuous (L := L) (C := C) (hC := hC) (h := h)
example (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C) (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) :
    ‖GenericAPI.map L C hC h‖ ≤ C := GenericAPI.norm_le (L := L) (C := C) (hC := hC) (h := h)
end Generic

bounded_linear_api ScaleAPI (c : ℝ) using (c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) where
  bound := ‖c‖
  nonneg := norm_nonneg c
  estimate := by intro x; simpa only [LinearMap.smul_apply, LinearMap.id_apply] using (norm_smul c x).le

example (c x : ℝ) : ScaleAPI.map c x = c * x := ScaleAPI.map_apply (c := c) (x := x)
example (c : ℝ) : ‖ScaleAPI.map c‖ ≤ ‖c‖ := ScaleAPI.norm_le (c := c)
example (c r x : ℝ) : ScaleAPI.map c (r • x) = r • ScaleAPI.map c x :=
  ScaleAPI.map_smul (c := c) (r := r) (x := x)
example (c x y : ℝ) : ScaleAPI.map c (x + y) = c * x + c * y := by
  rw [ScaleAPI.map_add]
  simp only [ScaleAPI.map_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
end ApiRecipesTests.BoundedLinear
