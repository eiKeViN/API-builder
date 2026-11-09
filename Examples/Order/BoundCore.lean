module
public import Examples.Order.Core
@[expose] public noncomputable section
namespace OrderExample
instance existingDictionary {X Y : Obj.{u}} : FunLike (Map X Y) X.Carrier Y.Carrier where
  coe := Core.functionView.view
  coe_injective := Core.functionView.view_injective
def Map.id (X : Obj.{u}) : Map X X := Core.composition.identity X
def Map.comp {X Y Z : Obj.{u}} (g : Map Y Z) (f : Map X Y) : Map X Z :=
  Core.composition.compose g f
end OrderExample
