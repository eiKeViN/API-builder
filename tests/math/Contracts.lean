import ApiBuilder.Mathematics
import Lean
open ApiBuilder

-- Public-import proofs exercise three independent universes in the helper module.
def functions : FunctionView (Type u) (fun X => X) (fun X Y => X → Y) where
  view f := f
  view_injective h := h

noncomputable def chosenId (X : Type u) : X → X :=
  Classical.choose (show ∃ f : X → X, ∀ x, f x = x from ⟨id, fun _ => rfl⟩)
noncomputable def chosenComp {X Y Z : Type u} (g : Y → Z) (f : X → Y) : X → Z :=
  Classical.choose (show ∃ h : X → Z, ∀ x, h x = g (f x) from ⟨g ∘ f, fun _ => rfl⟩)
noncomputable def chosen : Composition functions.{u} where
  identity := chosenId
  compose := chosenComp
  identity_apply X := Classical.choose_spec (show ∃ f : X → X, ∀ x, f x = x from ⟨id, fun _ => rfl⟩)
  compose_apply g f := Classical.choose_spec (show ∃ h, ∀ x, h x = g (f x) from ⟨g ∘ f, fun _ => rfl⟩)

example {X Y : Type u} (f : X → Y) : chosen.compose f (chosen.identity X) = f :=
  chosen.comp_id functions f
example {W X Y Z : Type u} (h : Y → Z) (g : X → Y) (f : W → X) :
    chosen.compose (chosen.compose h g) f = chosen.compose h (chosen.compose g f) :=
  chosen.comp_assoc functions h g f

-- Forgetting a real data tag cannot meet faithful observation.
example : ¬ Function.Injective (fun (_ : Bool) => (0 : Nat)) := by
  intro h
  have impossible : false = true := h rfl
  cases impossible

-- Identity and successor do not close under composing successor with itself.
example : ¬ ∃ h : Nat → Nat, (h = id ∨ h = Nat.succ) ∧ ∀ x, h x = x + 2 := by
  rintro ⟨h, (rfl | rfl), law⟩ <;> have bad := law 0 <;> contradiction

open Lean Elab Command in
run_cmd do
  for name in [``FunctionView.ext, ``Composition.comp_id, ``Composition.id_comp,
      ``Composition.comp_assoc, ``chosen] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"
