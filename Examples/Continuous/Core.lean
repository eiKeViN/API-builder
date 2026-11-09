module
public import ApiBuilder.Mathematics
public import Mathlib.Topology.ContinuousMap.Basic
@[expose] public section
namespace ContinuousExample
universe u
structure Obj where
  Carrier : Type u
  topology : TopologicalSpace Carrier
  zero : Zero Carrier
attribute [instance] Obj.topology Obj.zero
structure Map (X Y : Obj.{u}) extends ContinuousMap X.Carrier Y.Carrier where
  map_zero : toContinuousMap 0 = 0
namespace Core
def functionView : ApiBuilder.FunctionView Obj.{u} Obj.Carrier Map where
  view f := f.toContinuousMap
  view_injective := by
    intro X Y f g h
    cases f; cases g
    congr
    exact DFunLike.coe_injective h

def composition : ApiBuilder.Composition functionView.{u} where
  identity X := ⟨ContinuousMap.id X.Carrier, rfl⟩
  compose g f := ⟨g.toContinuousMap.comp f.toContinuousMap, by
    change g.toContinuousMap (f.toContinuousMap 0) = 0
    rw [f.map_zero, g.map_zero]⟩
  identity_apply _ _ := rfl
  compose_apply _ _ _ := rfl
end Core
end ContinuousExample
