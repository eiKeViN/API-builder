module
public import ApiBuilder.Mathematics
public import Mathlib.Order.Hom.Basic
@[expose] public section
namespace OrderExample
universe u
structure Obj where
  Carrier : Type u
  preorder : Preorder Carrier
  point : Carrier
attribute [instance] Obj.preorder
structure Map (X Y : Obj.{u}) extends OrderHom X.Carrier Y.Carrier where
  map_point : toOrderHom X.point = Y.point
namespace Core
def functionView : ApiBuilder.FunctionView Obj.{u} Obj.Carrier Map where
  view f := f.toOrderHom
  view_injective := by
    intro X Y f g h
    cases f; cases g
    congr
    exact DFunLike.coe_injective h

def composition : ApiBuilder.Composition functionView.{u} where
  identity X := ⟨OrderHom.id, rfl⟩
  compose {X Y Z} g f := ⟨g.toOrderHom.comp f.toOrderHom, by
    change g.toOrderHom (f.toOrderHom X.point) = _
    rw [f.map_point, g.map_point]⟩
  identity_apply _ _ := rfl
  compose_apply _ _ _ := rfl
end Core
end OrderExample
