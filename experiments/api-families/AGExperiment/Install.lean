module
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public meta import Lean

/-!
An intentionally small baseline: install concrete-class instances from existing
generic mathlib theorems. This command does not implement API Builder receipts,
bindings, registration audit, or evolution management.
-/

public def AGExperiment.sourceRestriction : Unit := ()

public meta section
namespace AGExperiment
open Lean Elab Command
open CategoryTheory AlgebraicGeometry

def installCore (p : Ident) : CommandElabM Unit :=
    withScope (fun s => { s with opts := s.opts.setBool `backward.isDefEq.respectTransparency.types false }) do
  let comp := mkIdent (p.getId ++ `api_comp)
  let fst := mkIdent (p.getId ++ `api_fst)
  let snd := mkIdent (p.getId ++ `api_snd)
  let restrict := mkIdent (p.getId ++ `api_restrict)
  elabCommand (← `(instance $comp:ident {X Y Z : AlgebraicGeometry.Scheme}
      (f : X ⟶ Y) (g : Y ⟶ Z) [$p f] [$p g] : $p (CategoryTheory.CategoryStruct.comp f g) :=
    CategoryTheory.MorphismProperty.comp_mem (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) f g
      inferInstance inferInstance))
  elabCommand (← `(instance $fst:ident {X Y S : AlgebraicGeometry.Scheme}
      (f : X ⟶ S) (g : Y ⟶ S) [$p g] :
      $p (CategoryTheory.Limits.pullback.fst f g) :=
    CategoryTheory.MorphismProperty.pullback_fst f g inferInstance))
  elabCommand (← `(instance $snd:ident {X Y S : AlgebraicGeometry.Scheme}
      (f : X ⟶ S) (g : Y ⟶ S) [$p f] :
      $p (CategoryTheory.Limits.pullback.snd f g) :=
    CategoryTheory.MorphismProperty.pullback_snd f g inferInstance))
  elabCommand (← `(instance $restrict:ident {X Y : AlgebraicGeometry.Scheme}
      (f : X ⟶ Y) (V : Y.Opens) [$p f] : $p (f ∣_ V) :=
    AlgebraicGeometry.IsZariskiLocalAtTarget.restrict (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f)
      inferInstance V))

def installSource (p : Ident) : CommandElabM Unit :=
    withScope (fun s => { s with opts := s.opts.setBool `backward.isDefEq.respectTransparency.types false }) do
  let sourceContract := mkIdent (p.getId ++ `api_sourceContract)
  let resLE := mkIdent (p.getId ++ `api_resLE)
  -- Check the mathematical capability itself before generating its frontend.
  elabCommand (← `(theorem $sourceContract : AlgebraicGeometry.IsZariskiLocalAtSource
      (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) := inferInstance))
  if (← get).messages.hasErrors then
    throwError "source restriction requires a proven source-locality capability"
  elabCommand (← `(instance $resLE:ident {X Y : AlgebraicGeometry.Scheme}
      (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U ≤ (TopologicalSpace.Opens.map f.base).obj V) [$p f] :
      $p (f.resLE V U e) :=
    AlgebraicGeometry.IsZariskiLocalAtSource.resLE
      (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) (f := f) e inferInstance))

syntax (name := schemePropertyCore) "install_scheme_property_core " ident : command
syntax (name := schemePropertySource) "install_scheme_property_source " ident : command

@[command_elab schemePropertyCore] def elabCore : CommandElab := fun s =>
  installCore ⟨s[1]⟩

@[command_elab schemePropertySource] def elabSource : CommandElab := fun s =>
  installSource ⟨s[1]⟩

end AGExperiment
