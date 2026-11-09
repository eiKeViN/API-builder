module
public import Examples.Order.Generated
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
open OrderExample
noncomputable def selectedPermutation (X : Obj.{u}) : X.Carrier ≃ X.Carrier :=
  Classical.choice ⟨Equiv.refl X.Carrier⟩
noncomputable instance (priority := 2000) competing {X Y : Obj.{u}} :
    FunLike (Map X Y) X.Carrier Y.Carrier where
  coe f x := Core.functionView.view f (selectedPermutation X x)
  coe_injective := by
    intro f g h
    apply Core.functionView.ext
    intro x
    obtain ⟨y, hy⟩ := (selectedPermutation X).surjective x
    simpa only [hy] using congrFun h y
#api_check OrderExample.Map
