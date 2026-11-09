module
public import Examples.Order.Choice
public section
namespace OrderExample
universe u
variable {X Y Z W : Obj.{u}}
example (f : Map X Y) (x : X.Carrier) : (Map.id Y).comp f x = f x := by simp
example (f g : Map X Y) (h : ∀ x, f x = g x) : f = g := by ext x; exact h x
example (h : Map Z W) (g : Map Y Z) (f : Map X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := Map.comp_assoc h g f
example (X : Obj.{u}) : Map.id X = Core.choiceComposition.identity X := rfl
example (g : Map Y Z) (f : Map X Y) : g.comp f = Core.choiceComposition.compose g f := rfl
#check Map.ext_iff
end OrderExample
