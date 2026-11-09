module
public import Holdout.Macro
public import Holdout.Recipe

public section
namespace Holdout.NamedClient

section Subsemirings
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

example (f : R →+* S) (p q : Subsemiring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Holdout.Macro.SubsemiringAPI.map_sup (R := R) (S := S) (f := f) (p := p) (q := q)
example (f : R →+* S) (p q : Subsemiring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Holdout.Macro.SubsemiringAPI.comap_inf (R := R) (S := S) (f := f) (p := p) (q := q)
example (f : R →+* S) (p q : Subsemiring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Holdout.Recipe.SubsemiringAPI.map_sup (R := R) (S := S) (f := f) (p := p) (q := q)
example (f : R →+* S) (p q : Subsemiring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Holdout.Recipe.SubsemiringAPI.comap_inf (R := R) (S := S) (f := f) (p := p) (q := q)
end Subsemirings

section Subalgebras
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

example (f : A →ₐ[R] B) (p q : Subalgebra R A) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Holdout.Macro.SubalgebraAPI.map_sup (R := R) (A := A) (B := B) (f := f) (p := p) (q := q)
example (f : A →ₐ[R] B) (p q : Subalgebra R B) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Holdout.Macro.SubalgebraAPI.comap_inf (R := R) (A := A) (B := B) (f := f) (p := p) (q := q)
example (f : A →ₐ[R] B) (p q : Subalgebra R A) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Holdout.Recipe.SubalgebraAPI.map_sup (R := R) (A := A) (B := B) (f := f) (p := p) (q := q)
example (f : A →ₐ[R] B) (p q : Subalgebra R B) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Holdout.Recipe.SubalgebraAPI.comap_inf (R := R) (A := A) (B := B) (f := f) (p := p) (q := q)
end Subalgebras

end Holdout.NamedClient
