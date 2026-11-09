module
public import Init
public section
namespace ApiBuilder
universe uObj uCarrier uHom

/-- A chosen faithful observation; intentionally not a typeclass. -/
structure FunctionView (Obj : Type uObj) (Carrier : Obj → Type uCarrier)
    (Hom : Obj → Obj → Type uHom) where
  view : ∀ {X Y : Obj}, Hom X Y → Carrier X → Carrier Y
  view_injective : ∀ {X Y : Obj}, Function.Injective (@view X Y)

/-- The author supplies closure and pointwise laws, including for choice-defined operations. -/
structure Composition {Obj : Type uObj} {Carrier : Obj → Type uCarrier}
    {Hom : Obj → Obj → Type uHom} (V : FunctionView Obj Carrier Hom) where
  identity : ∀ X : Obj, Hom X X
  compose : ∀ {X Y Z : Obj}, Hom Y Z → Hom X Y → Hom X Z
  identity_apply : ∀ (X : Obj) (x : Carrier X), V.view (identity X) x = x
  compose_apply : ∀ {X Y Z : Obj} (g : Hom Y Z) (f : Hom X Y) (x : Carrier X),
    V.view (compose g f) x = V.view g (V.view f x)

variable {Obj : Type uObj} {Carrier : Obj → Type uCarrier}
  {Hom : Obj → Obj → Type uHom} (V : FunctionView Obj Carrier Hom)
  (C : Composition V)

theorem FunctionView.ext {X Y : Obj} {f g : Hom X Y}
    (h : ∀ x, V.view f x = V.view g x) : f = g :=
  V.view_injective (funext h)

theorem Composition.comp_id {X Y : Obj} (f : Hom X Y) :
    C.compose f (C.identity X) = f := by
  apply V.ext
  intro x
  rw [C.compose_apply, C.identity_apply]

theorem Composition.id_comp {X Y : Obj} (f : Hom X Y) :
    C.compose (C.identity Y) f = f := by
  apply V.ext
  intro x
  rw [C.compose_apply, C.identity_apply]

theorem Composition.comp_assoc {W X Y Z : Obj}
    (h : Hom Y Z) (g : Hom X Y) (f : Hom W X) :
    C.compose (C.compose h g) f = C.compose h (C.compose g f) := by
  apply V.ext
  intro x
  rw [C.compose_apply, C.compose_apply, C.compose_apply, C.compose_apply]
end ApiBuilder
