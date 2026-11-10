module
public import GaloisApiTests.Generated

public section

namespace GaloisApiTests.ExtraClient

section Subsemirings
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] {ι : Sort*}

example (f : R →+* S) (p : ι → Subsemiring R) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [GaloisApiTests.Generated.SubsemiringAPI.map_sup, GaloisApiTests.Generated.SubsemiringAPI.map_iSup,
    GaloisApiTests.Generated.SubsemiringAPI.map_bot]

example (f : R →+* S) (p : ι → Subsemiring S) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [GaloisApiTests.Generated.SubsemiringAPI.comap_inf, GaloisApiTests.Generated.SubsemiringAPI.comap_iInf,
    GaloisApiTests.Generated.SubsemiringAPI.comap_top]
end Subsemirings

section Subalgebras
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] {ι : Sort*}

example (f : A →ₐ[R] B) (p : ι → Subalgebra R A) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [GaloisApiTests.Generated.SubalgebraAPI.map_sup, GaloisApiTests.Generated.SubalgebraAPI.map_iSup,
    GaloisApiTests.Generated.SubalgebraAPI.map_bot]

example (f : A →ₐ[R] B) (p : ι → Subalgebra R B) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [GaloisApiTests.Generated.SubalgebraAPI.comap_inf, GaloisApiTests.Generated.SubalgebraAPI.comap_iInf,
    GaloisApiTests.Generated.SubalgebraAPI.comap_top]
end Subalgebras

end GaloisApiTests.ExtraClient
