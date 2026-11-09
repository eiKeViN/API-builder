module
public import Examples.Order.Core
public import Mathlib.Tactic.Ext
@[expose] public noncomputable section
namespace OrderExample.Map
universe u
variable {X Y Z W : Obj.{u}}
instance instFunLike : FunLike (Map X Y) X.Carrier Y.Carrier where
  coe := Core.functionView.view
  coe_injective := Core.functionView.view_injective
@[ext] theorem ext {f g : Map X Y} (h : ∀ x, f x = g x) : f = g :=
  Core.functionView.ext h
-- ext_iff is emitted by the native ext attribute.
def id (X : Obj.{u}) : Map X X := Core.composition.identity X
def comp (g : Map Y Z) (f : Map X Y) : Map X Z := Core.composition.compose g f
@[simp] theorem id_apply (X : Obj.{u}) (x : X.Carrier) : id X x = x :=
  Core.composition.identity_apply X x
@[simp] theorem comp_apply (g : Map Y Z) (f : Map X Y) (x : X.Carrier) :
    comp g f x = g (f x) := Core.composition.compose_apply g f x
@[simp] theorem comp_id (f : Map X Y) : comp f (id X) = f :=
  Core.composition.comp_id Core.functionView f
@[simp] theorem id_comp (f : Map X Y) : comp (id Y) f = f :=
  Core.composition.id_comp Core.functionView f
theorem comp_assoc (h : Map Z W) (g : Map Y Z) (f : Map X Y) :
    comp (comp h g) f = comp h (comp g f) :=
  Core.composition.comp_assoc Core.functionView h g f
end OrderExample.Map
