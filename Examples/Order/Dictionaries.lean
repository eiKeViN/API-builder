module
public import Examples.Order.Generated
public section
namespace OrderExample
-- Definitionally identical carriers; deliberately opposite order dictionaries.
def forward : Obj := ⟨Nat, inferInstance, 0⟩
def backward : Obj := ⟨Nat, inferInstanceAs (Preorder (OrderDual Nat)), 0⟩
example : forward.Carrier = backward.Carrier := rfl
example (f : Map forward backward) (g : Map backward forward) (x : Nat) :
    g.comp f x = g (f x) := Map.comp_apply g f x
example (f : Map forward backward) : (Map.id backward).comp f = f := by simp
end OrderExample
