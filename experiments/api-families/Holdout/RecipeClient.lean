module
public import Holdout.Recipe

public section

namespace Holdout.RecipeClient

section Subsemirings
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] {ι : Sort*}

example (f : R →+* S) (p : ι → Subsemiring R) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [Holdout.Recipe.SubsemiringAPI.map_sup, Holdout.Recipe.SubsemiringAPI.map_iSup,
    Holdout.Recipe.SubsemiringAPI.map_bot]

example (f : R →+* S) (p : ι → Subsemiring S) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [Holdout.Recipe.SubsemiringAPI.comap_inf, Holdout.Recipe.SubsemiringAPI.comap_iInf,
    Holdout.Recipe.SubsemiringAPI.comap_top]
end Subsemirings

section Subalgebras
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] {ι : Sort*}

example (f : A →ₐ[R] B) (p : ι → Subalgebra R A) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [Holdout.Recipe.SubalgebraAPI.map_sup, Holdout.Recipe.SubalgebraAPI.map_iSup,
    Holdout.Recipe.SubalgebraAPI.map_bot]

example (f : A →ₐ[R] B) (p : ι → Subalgebra R B) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [Holdout.Recipe.SubalgebraAPI.comap_inf, Holdout.Recipe.SubalgebraAPI.comap_iInf,
    Holdout.Recipe.SubalgebraAPI.comap_top]
end Subalgebras

end Holdout.RecipeClient
