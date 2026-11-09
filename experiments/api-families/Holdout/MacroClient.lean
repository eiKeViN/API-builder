module
public import Holdout.Macro

public section

namespace Holdout.MacroClient

section Subsemirings
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] {ι : Sort*}

example (f : R →+* S) (p : ι → Subsemiring R) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [Holdout.Macro.SubsemiringAPI.map_sup, Holdout.Macro.SubsemiringAPI.map_iSup,
    Holdout.Macro.SubsemiringAPI.map_bot]

example (f : R →+* S) (p : ι → Subsemiring S) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [Holdout.Macro.SubsemiringAPI.comap_inf, Holdout.Macro.SubsemiringAPI.comap_iInf,
    Holdout.Macro.SubsemiringAPI.comap_top]
end Subsemirings

section Subalgebras
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] {ι : Sort*}

example (f : A →ₐ[R] B) (p : ι → Subalgebra R A) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [Holdout.Macro.SubalgebraAPI.map_sup, Holdout.Macro.SubalgebraAPI.map_iSup,
    Holdout.Macro.SubalgebraAPI.map_bot]

example (f : A →ₐ[R] B) (p : ι → Subalgebra R B) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [Holdout.Macro.SubalgebraAPI.comap_inf, Holdout.Macro.SubalgebraAPI.comap_iInf,
    Holdout.Macro.SubalgebraAPI.comap_top]
end Subalgebras

end Holdout.MacroClient
