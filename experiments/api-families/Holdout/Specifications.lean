module
public import Holdout.Reference
public meta import MapBaseline.Framework

public meta section
namespace Holdout.Specifications
open Lean Elab Command MapBaseline.Framework

private def names (family : Name) : Array Ident :=
  MapBaseline.Contract.roles.map (fun role => mkIdent (family ++ role))

def subsemiring : SpecificationBuilder := do
  let ctx := Unhygienic.run `(command|
    variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S])
  pure {
    context := #[ctx]
    reference := `Holdout.Reference.SubsemiringAPI
    make := fun family => do
      pure {
        binders := #[Unhygienic.run `(bracketedBinder| (f : R →+* S))]
        gc := Unhygienic.run `(term| Subsemiring.gc_map_comap f)
        names := names family } }

def subalgebra : SpecificationBuilder := do
  let ctx := Unhygienic.run `(command|
    variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B])
  pure {
    context := #[ctx]
    reference := `Holdout.Reference.SubalgebraAPI
    make := fun family => do
      pure {
        binders := #[Unhygienic.run `(bracketedBinder| (f : A →ₐ[R] B))]
        gc := Unhygienic.run `(term| Subalgebra.gc_map_comap f)
        names := names family } }

end Holdout.Specifications
