module
public import Examples.Order.Core
@[expose] public noncomputable section
namespace OrderExample.Core
universe u
def chosenIdentity (X : Obj.{u}) : Map X X :=
  Classical.choose (show ∃ f : Map X X, ∀ x, functionView.view f x = x from
    ⟨composition.identity X, composition.identity_apply X⟩)
def chosenCompose {X Y Z : Obj.{u}} (g : Map Y Z) (f : Map X Y) : Map X Z :=
  Classical.choose (show ∃ h : Map X Z, ∀ x,
      functionView.view h x = functionView.view g (functionView.view f x) from
    ⟨composition.compose g f, composition.compose_apply g f⟩)
def choiceComposition : ApiBuilder.Composition functionView.{u} where
  identity := chosenIdentity
  compose := chosenCompose
  identity_apply X := Classical.choose_spec (show ∃ f : Map X X, ∀ x, functionView.view f x = x from
    ⟨composition.identity X, composition.identity_apply X⟩)
  compose_apply g f := Classical.choose_spec (show ∃ h, ∀ x,
      functionView.view h x = functionView.view g (functionView.view f x) from
    ⟨composition.compose g f, composition.compose_apply g f⟩)
end OrderExample.Core
