module
public meta import ApiBuilder.Recipes.BundledMap
public meta section
namespace LocalRecipes
open Lean Elab Command ApiBuilder ApiBuilder.Recipes

def localMap : Recipe where
  prepare r := do
    let base ← prepareBundledMap r
    let v ← decodeView r
    let name := r.family ++ `coe_comp
    pure { base with
      outputs := base.outputs.push { role := `coe_comp, name, owner := `localMap }
      execute := do
        base.execute
        withViewScope v do
          let O := v.obj; let H := v.hom
          let c := mkIdent (r.family ++ `comp)
          let ca := mkIdent (r.family ++ `comp_apply)
          let out := mkIdent name
          declare r (← `(public theorem $out {X Y Z : $O} (g : $H Y Z) (f : $H X Y) :
            (fun x => $c g f x) = (fun x => g (f x)) := funext ($ca g f))) }
end LocalRecipes
