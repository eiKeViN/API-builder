module
public import GaloisApiTests.Reference
public meta import GaloisApi
public section

namespace GaloisApiTests.Generated

section Groups
variable {G H : Type*} [Group G] [Group H]
galois_api GroupAPI (f : G →* H) using (Subgroup.gc_map_comap f)
#check_galois_api GroupAPI against GaloisApiTests.Reference.GroupAPI

-- Selection supports gradual installation next to a hand-authored member.
galois_map_api Incremental (f : G →* H) using (Subgroup.gc_map_comap f) only [map_sup]
galois_map_api Incremental (f : G →* H) using (Subgroup.gc_map_comap f) only [map_iSup, map_bot]
galois_comap_api Incremental (f : G →* H) using (Subgroup.gc_map_comap f)
#check_galois_api Incremental against GaloisApiTests.Reference.GroupAPI
#check_galois_api Incremental against GaloisApiTests.Reference.GroupAPI only [comap_inf]
galois_comap_api RightOnly (f : G →* H) using (Subgroup.gc_map_comap f)
#check_galois_api RightOnly against GaloisApiTests.Reference.GroupAPI
  only [comap_inf, comap_iInf, comap_top]
galois_map_api _root_.GaloisApiTests.RootMap (f : G →* H) using (Subgroup.gc_map_comap f)
#check_galois_api _root_.GaloisApiTests.RootMap against GaloisApiTests.Reference.GroupAPI
  only [map_sup, map_iSup, map_bot]
end Groups

section Rings
variable {R S : Type*} [NonAssocRing R] [NonAssocRing S]
galois_api RingAPI (f : R →+* S) using (Subring.gc_map_comap f)
#check_galois_api RingAPI against GaloisApiTests.Reference.RingAPI
end Rings

section Modules
variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {σ : R →+* S}
section
variable [RingHomSurjective σ]
galois_map_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.gc_map_comap f)
end
preimage_api ModuleAPI (f : M →ₛₗ[σ] N) using (Submodule.comap f) on (Submodule S N) where
  inf := by rfl
  iInf := by ext x; simp only [Submodule.mem_comap, Submodule.mem_iInf]
  top := by rfl
#check_galois_api ModuleAPI against GaloisApiTests.Reference.ModuleAPI
end Modules

section Semirings
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
galois_api SubsemiringAPI (f : R →+* S) using (Subsemiring.gc_map_comap f)
#check_galois_api SubsemiringAPI against GaloisApiTests.Reference.SubsemiringAPI
end Semirings

section Algebras
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
galois_api SubalgebraAPI (f : A →ₐ[R] B) using (Subalgebra.gc_map_comap f)
#check_galois_api SubalgebraAPI against GaloisApiTests.Reference.SubalgebraAPI
end Algebras

section Sets
variable {α β : Type*}
galois_api SetAPI (f : α → β) using (Set.image_preimage (f := f))
example (f : α → β) (p q : Set α) : f '' (p ∪ q) = f '' p ∪ f '' q :=
  SetAPI.map_sup (f := f) (p := p) (q := q)
example {ι : Sort*} (f : α → β) (p : ι → Set β) :
    f ⁻¹' (⨅ i, p i) = ⨅ i, f ⁻¹' p i :=
  SetAPI.comap_iInf (ι := ι) (f := f) (p := p)
end Sets

section Semilattices
variable {α : Type*} [SemilatticeSup α]
-- Selecting map_sup must not require a CompleteLattice, bottom, or infimum.
galois_api FiniteSup using (GaloisConnection.id (α := α)) only [map_sup]
example (p q : α) : id (p ⊔ q) = id p ⊔ id q :=
  FiniteSup.map_sup (p := p) (q := q)
end Semilattices

end GaloisApiTests.Generated
