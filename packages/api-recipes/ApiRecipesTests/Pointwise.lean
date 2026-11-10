module
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public meta import ApiRecipes.Pointwise
public section
namespace ApiRecipesTests.Pointwise
open scoped ZeroAtInfty BoundedContinuousFunction

section Minimal
variable {F α β : Type*} [FunLike F α β] [Add F] [Add β] [IsAddApply F]
pointwise_api AddOnly for F only [add]
example (f g : F) (x : α) : (f + g) x = f x + g x :=
  AddOnly.add_apply (f := f) (g := g) (x := x)
end Minimal

section Inverse
variable {F α β : Type*} [FunLike F α β] [Inv F] [Inv β] [IsInvApply F]
pointwise_api InverseAPI for F only [inv]
end Inverse

section Division
variable {F α β : Type*} [FunLike F α β] [Div F] [Div β] [IsDivApply F]
pointwise_api InverseAPI for F only [div]
end Division

section InverseClient
variable {F α β : Type*} [FunLike F α β] [Inv F] [Inv β] [IsInvApply F]
  [Div F] [Div β] [IsDivApply F]
example (f g : F) (x : α) : (f⁻¹ / g) x = (f x)⁻¹ / g x := by
  rw [InverseAPI.div_apply, InverseAPI.inv_apply]
end InverseClient

section Vanishing
variable {α : Type*} [TopologicalSpace α]
pointwise_api VanishingAPI for C₀(α, ℝ) only [zero, add, neg, sub]
pointwise_smul_api VanishingAPI for C₀(α, ℝ) scalars ℝ

example (f g : C₀(α, ℝ)) (c : ℝ) (x : α) :
    (c • (f - g) + -f + 0) x = c • (f x - g x) + -f x := by
  simp only [VanishingAPI.add_apply, VanishingAPI.smul_apply, VanishingAPI.sub_apply,
    VanishingAPI.neg_apply, add_zero]
example (f g : C₀(α, ℝ)) : ⇑(f + g) = ⇑f + ⇑g :=
  VanishingAPI.coe_add (f := f) (g := g)
example (f : C₀(α, ℝ)) (c : ℝ) : ⇑(c • f) = c • ⇑f :=
  VanishingAPI.coe_smul (c := c) (f := f)
end Vanishing

section Bounded
variable {α : Type*} [TopologicalSpace α]
pointwise_api BoundedAPI for (α →ᵇ ℝ) only [zero, one, add, mul, neg, sub]
example (f g : α →ᵇ ℝ) (x : α) : ((f + 1) * (g - 0)) x = (f x + 1) * g x := by
  simp only [BoundedAPI.mul_apply, BoundedAPI.add_apply, BoundedAPI.one_apply,
    sub_zero]
end Bounded

section Operators
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]
pointwise_api LinearAPI for (E →L[ℝ] F) only [zero, add, neg, sub]
pointwise_smul_api LinearAPI for (E →L[ℝ] F) scalars ℝ
example (L K : E →L[ℝ] F) (x : E) : (L + K) x = L x + K x :=
  LinearAPI.add_apply (f := L) (g := K) (x := x)
end Operators
end ApiRecipesTests.Pointwise
