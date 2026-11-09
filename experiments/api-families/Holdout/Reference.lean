module
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

public section

/- Independently authored signatures for two post-freeze consumers. -/
namespace Holdout.Reference

namespace SubsemiringAPI
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

@[simp] theorem map_sup (f : R →+* S) (p q : Subsemiring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f := (Subsemiring.gc_map_comap f).l_sup
@[simp] theorem map_iSup {ι : Sort*} (f : R →+* S) (p : ι → Subsemiring R) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f := (Subsemiring.gc_map_comap f).l_iSup
@[simp] theorem map_bot (f : R →+* S) :
    (⊥ : Subsemiring R).map f = ⊥ := (Subsemiring.gc_map_comap f).l_bot
@[simp] theorem comap_inf (f : R →+* S) (p q : Subsemiring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f := (Subsemiring.gc_map_comap f).u_inf
@[simp] theorem comap_iInf {ι : Sort*} (f : R →+* S) (p : ι → Subsemiring S) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f := (Subsemiring.gc_map_comap f).u_iInf
@[simp] theorem comap_top (f : R →+* S) :
    (⊤ : Subsemiring S).comap f = ⊤ := (Subsemiring.gc_map_comap f).u_top
end SubsemiringAPI

namespace SubalgebraAPI
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

@[simp] theorem map_sup (f : A →ₐ[R] B) (p q : Subalgebra R A) :
    (p ⊔ q).map f = p.map f ⊔ q.map f := (Subalgebra.gc_map_comap f).l_sup
@[simp] theorem map_iSup {ι : Sort*} (f : A →ₐ[R] B) (p : ι → Subalgebra R A) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f := (Subalgebra.gc_map_comap f).l_iSup
@[simp] theorem map_bot (f : A →ₐ[R] B) :
    (⊥ : Subalgebra R A).map f = ⊥ := (Subalgebra.gc_map_comap f).l_bot
@[simp] theorem comap_inf (f : A →ₐ[R] B) (p q : Subalgebra R B) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f := (Subalgebra.gc_map_comap f).u_inf
@[simp] theorem comap_iInf {ι : Sort*} (f : A →ₐ[R] B) (p : ι → Subalgebra R B) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f := (Subalgebra.gc_map_comap f).u_iInf
@[simp] theorem comap_top (f : A →ₐ[R] B) :
    (⊤ : Subalgebra R B).comap f = ⊤ := (Subalgebra.gc_map_comap f).u_top
end SubalgebraAPI

end Holdout.Reference
