module
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public meta import ApiRecipes.Command

/-! Concrete scheme-property instances from independently proved capabilities. -/
public meta section
namespace ApiRecipes.SchemeProperty
open Lean Elab Command ApiRecipes.Command CategoryTheory AlgebraicGeometry

def roles : Array Name := #[`comp, `pullback_fst, `pullback_snd, `restrict, `resLE]

syntax (name := schemePropertyApi) "scheme_property_api " ident " using " ident
  selection (" priority " num)? : command

private partial def priorityArg (s : Syntax) : Option Nat :=
  s.isNatLit? <|> s.getArgs.findSome? priorityArg

@[command_elab schemePropertyApi] def elabScheme : CommandElab := fun s => do
  let family ← familyName ⟨s[1]⟩
  let p : Ident := ⟨s[3]⟩
  let selected ← select roles ⟨s[4]⟩
  let instancePriority := (priorityArg s[5]).getD 1000
  batch <| withScope (fun sc => { sc with opts := sc.opts.setBool `backward.isDefEq.respectTransparency.types false }) do
    preflight family selected
    for role in selected do
      let proof ← match role with
        | `comp => `(fun {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
            [hf : $p f] [hg : $p g] =>
          CategoryTheory.MorphismProperty.comp_mem
            (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) f g hf hg)
        | `pullback_fst => `(fun {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S)
            [hg : $p g] => CategoryTheory.MorphismProperty.pullback_fst
              (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) f g hg)
        | `pullback_snd => `(fun {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S)
            [hf : $p f] => CategoryTheory.MorphismProperty.pullback_snd
              (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) f g hf)
        | `restrict => `(fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (V : Y.Opens)
            [hf : $p f] => AlgebraicGeometry.IsZariskiLocalAtTarget.restrict
              (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) hf V)
        | `resLE => `(fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : X.Opens)
            (V : Y.Opens) (e : U ≤ (TopologicalSpace.Opens.map f.base).obj V) [hf : $p f] =>
          AlgebraicGeometry.IsZariskiLocalAtSource.resLE
            (P := fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => $p f) (f := f) e hf)
        | _ => throwError "recipe: internal unsupported scheme-property role"
      publish (family ++ role) proof (.inst instancePriority)
end ApiRecipes.SchemeProperty
