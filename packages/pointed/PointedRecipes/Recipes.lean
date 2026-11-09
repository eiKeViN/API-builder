module
public import PointedRecipes.Target
public meta import ApiBuilder.Recipes.BundledMap
public meta section
namespace PointedRecipes
open Lean Elab Command ApiBuilder ApiBuilder.Recipes

def extraOutputs (r : FamilyRequest) : Array Output :=
  #[(`map_point, #[`simp]), (`toPointedHom, #[]), (`toPointedHom_apply, #[`simp]),
    (`toPointedHom_id, #[]), (`toPointedHom_comp, #[])].map fun (role, regs) =>
      { role, name := r.family ++ role, owner := `pointedBridge, registrations := regs }

def buildBridge (v : ViewPorts) (point preserves : Name) : CommandElabM Unit := withViewScope v do
  let r := v.request; let O := v.obj; let C := v.carrier; let H := v.hom; let V := v.view
  let pt := mkIdent point; let hp := mkIdent preserves
  let mp := mkIdent (r.family ++ `map_point); let cv := mkIdent (r.family ++ `toPointedHom)
  let ap := mkIdent (r.family ++ `toPointedHom_apply)
  let idLaw := mkIdent (r.family ++ `toPointedHom_id)
  let compLaw := mkIdent (r.family ++ `toPointedHom_comp)
  let i := mkIdent (r.family ++ `id); let c := mkIdent (r.family ++ `comp)
  let ia := mkIdent (r.family ++ `id_apply); let ca := mkIdent (r.family ++ `comp_apply)
  declare r (← `(@[simp] public theorem $mp {X Y : $O} (f : $H X Y) :
    f ($pt X) = $pt Y := $hp f))
  declare r (← `(@[expose] public noncomputable def $cv {X Y : $O} (f : $H X Y) :
    Pointed.Hom (Pointed.of ($pt X)) (Pointed.of ($pt Y)) := ⟨($V).view f, $hp f⟩))
  declare r (← `(@[simp] public theorem $ap {X Y : $O} (f : $H X Y) (x : $C X) :
    ($cv f).toFun x = ($V).view f x := rfl))
  declare r (← `(public theorem $idLaw (X : $O) :
    $cv ($i X) = Pointed.Hom.id (Pointed.of ($pt X)) := by
      apply Pointed.Hom.ext
      funext x
      exact $ia X x))
  declare r (← `(public theorem $compLaw {X Y Z : $O} (g : $H Y Z) (f : $H X Y) :
    $cv ($c g f) = Pointed.Hom.comp ($cv f) ($cv g) := by
      apply Pointed.Hom.ext
      funext x
      exact $ca g f x))

def validateBridge (r : FamilyReceipt) : CommandElabM Unit := do
  let req := requestFromReceipt r
  let v ← decodeView req
  let point ← resolvePublic (← req.field `point)
  let preserves ← resolvePublic (← req.field `preserves_point)
  withViewScope v do
    let O := v.obj; let H := v.hom; let V := v.view
    let pt := mkIdent point; let hp := mkIdent preserves
    let cv := mkIdent (r.family ++ `toPointedHom)
    checkDefEq (← `(fun (X Y : $O) (f : $H X Y) => $cv f))
      (← `(fun (X Y : $O) (f : $H X Y) =>
        (⟨($V).view f, $hp f⟩ : Pointed.Hom (Pointed.of ($pt X)) (Pointed.of ($pt Y)))))

def bridgeValidator : Validator := ⟨validateBridge⟩

def pointedMap : Recipe where
  prepare r := do
    let base ← prepareBundledMap r
    let v ← decodeView r
    let point ← resolvePublic (← r.field `point)
    let preserves ← resolvePublic (← r.field `preserves_point)
    pure { base with
      consumed := base.consumed ++ #[`point, `preserves_point]
      inputs := base.inputs ++ #[(`point, point), (`preserves_point, preserves)]
      outputs := base.outputs ++ extraOutputs r
      validators := base.validators.push ``bridgeValidator
      execute := do
        base.execute
        buildBridge v point preserves }
end PointedRecipes
