module
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import MapBaseline.Handwritten
public meta import MapBaseline.Framework

public meta section
namespace MapBaseline.Specifications
open Lean Elab Command Framework

private def outputNames (family : Name) : Array Ident :=
  Contract.roles.map (fun role => mkIdent (family ++ role))

def group : SpecificationBuilder := do
  let ctx : Command := Unhygienic.run `(command| variable {G H : Type*} [Group G] [Group H])
  pure {
    context := #[ctx]
    reference := `MapBaseline.Handwritten.GroupAPI
    make := fun family => do
      pure {
        binders := #[Unhygienic.run `(bracketedBinder| (f : G →* H))]
        gc := Unhygienic.run `(term| Subgroup.gc_map_comap f)
        names := outputNames family } }

def ring : SpecificationBuilder := do
  let ctx : Command := Unhygienic.run `(command| variable {R S : Type*} [NonAssocRing R] [NonAssocRing S])
  pure {
    context := #[ctx]
    reference := `MapBaseline.Handwritten.RingAPI
    make := fun family => do
      pure {
        binders := #[Unhygienic.run `(bracketedBinder| (f : R →+* S))]
        gc := Unhygienic.run `(term| Subring.gc_map_comap f)
        names := outputNames family } }

def semilinear : SpecificationBuilder := do
  let ctx : Command := Unhygienic.run `(command| variable {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N] {σ : R →+* S})
  pure {
    context := #[ctx]
    reference := `MapBaseline.Handwritten.ModuleAPI
    make := fun family => do
      pure {
        binders := #[Unhygienic.run `(bracketedBinder| (f : M →ₛₗ[σ] N))]
        leftExtra := #[Unhygienic.run `(bracketedBinder| [RingHomSurjective σ])]
        target := Unhygienic.run `(term| Submodule S N)
        comap := Unhygienic.run `(term| Submodule.comap f)
        gc := Unhygienic.run `(term| Submodule.gc_map_comap f)
        names := outputNames family
        rightProofs := some (Unhygienic.run `(term| by rfl),
          Unhygienic.run `(term| by ext x; simp only [Submodule.mem_comap, Submodule.mem_iInf]),
          Unhygienic.run `(term| by rfl)) } }
end MapBaseline.Specifications
