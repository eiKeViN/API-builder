module
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Holdout.Reference
public meta import MapBaseline.MacroCommand
public meta import MapBaseline.Contract

public section

namespace Holdout.Macro

namespace SubsemiringAPI
variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

derive_map_comap (f : R →+* S) using (Subsemiring.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
end SubsemiringAPI

namespace SubalgebraAPI
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

derive_map_comap (f : A →ₐ[R] B) using (Subalgebra.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
end SubalgebraAPI

end Holdout.Macro

#map_contract Holdout.Macro.SubsemiringAPI against Holdout.Reference.SubsemiringAPI
#map_contract Holdout.Macro.SubalgebraAPI against Holdout.Reference.SubalgebraAPI
