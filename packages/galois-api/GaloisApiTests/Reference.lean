module
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice


public section

/-! A hand-authored frontend, using mathlib's existing mathematical abstraction.
Every declaration has the same public binder order as the command experiment.
-/

namespace GaloisApiTests.Reference

namespace GroupAPI

variable {G H : Type*} [Group G] [Group H]

@[simp] theorem map_sup (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  (Subgroup.gc_map_comap f).l_sup

@[simp] theorem map_iSup {ι : Sort*} (f : G →* H) (p : ι → Subgroup G) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  (Subgroup.gc_map_comap f).l_iSup

@[simp] theorem map_bot (f : G →* H) :
    (⊥ : Subgroup G).map f = ⊥ :=
  (Subgroup.gc_map_comap f).l_bot

@[simp] theorem comap_inf (f : G →* H) (p q : Subgroup H) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  (Subgroup.gc_map_comap f).u_inf

@[simp] theorem comap_iInf {ι : Sort*} (f : G →* H) (p : ι → Subgroup H) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  (Subgroup.gc_map_comap f).u_iInf

@[simp] theorem comap_top (f : G →* H) :
    (⊤ : Subgroup H).comap f = ⊤ :=
  (Subgroup.gc_map_comap f).u_top

end GroupAPI

namespace RingAPI

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S]

@[simp] theorem map_sup (f : R →+* S) (p q : Subring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  (Subring.gc_map_comap f).l_sup

@[simp] theorem map_iSup {ι : Sort*} (f : R →+* S) (p : ι → Subring R) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  (Subring.gc_map_comap f).l_iSup

@[simp] theorem map_bot (f : R →+* S) :
    (⊥ : Subring R).map f = ⊥ :=
  (Subring.gc_map_comap f).l_bot

@[simp] theorem comap_inf (f : R →+* S) (p q : Subring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  (Subring.gc_map_comap f).u_inf

@[simp] theorem comap_iInf {ι : Sort*} (f : R →+* S) (p : ι → Subring S) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  (Subring.gc_map_comap f).u_iInf

@[simp] theorem comap_top (f : R →+* S) :
    (⊤ : Subring S).comap f = ⊤ :=
  (Subring.gc_map_comap f).u_top

end RingAPI

namespace ModuleAPI

variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S}

section Pushforward

variable [RingHomSurjective σ]

@[simp] theorem map_sup (f : M →ₛₗ[σ] N) (p q : Submodule R M) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  (Submodule.gc_map_comap f).l_sup

@[simp] theorem map_iSup {ι : Sort*} (f : M →ₛₗ[σ] N) (p : ι → Submodule R M) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  (Submodule.gc_map_comap f).l_iSup

@[simp] theorem map_bot (f : M →ₛₗ[σ] N) :
    (⊥ : Submodule R M).map f = ⊥ :=
  (Submodule.gc_map_comap f).l_bot

end Pushforward

/- No RingHomSurjective σ in this section. -/
@[simp] theorem comap_inf (f : M →ₛₗ[σ] N) (p q : Submodule S N) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  rfl

@[simp] theorem comap_iInf {ι : Sort*} (f : M →ₛₗ[σ] N) (p : ι → Submodule S N) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f := by
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_iInf]

@[simp] theorem comap_top (f : M →ₛₗ[σ] N) :
    (⊤ : Submodule S N).comap f = ⊤ :=
  rfl

end ModuleAPI

end GaloisApiTests.Reference




namespace GaloisApiTests.Reference

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

end GaloisApiTests.Reference
