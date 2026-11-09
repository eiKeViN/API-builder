module
public import ApiBuilder.Mathematics
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Tactic.Ext
public meta import ApiBuilder.Family
public meta section
namespace ApiBuilder.Recipes
open Lean Elab Command Meta

structure ViewPorts where
  request : FamilyRequest
  viewName : Name
  obj : Term
  carrier : Term
  hom : Term
  view : Term
  instanceName : Name
  levels : List Name

structure CompositionPorts where
  view : ViewPorts
  compositionName : Name
  composition : Term

private def toTerm (e : Expr) : CommandElabM Term :=
  liftTermElabM <| withOptions (fun o => o.setBool `pp.universes true) <| PrettyPrinter.delab e

def decodeView (r : FamilyRequest) : CommandElabM ViewPorts := do
  let s ← r.field `view
  let n ← resolvePublic s
  let info ← getConstInfo n
  let ty := info.type
  unless ty.isAppOfArity ``FunctionView 3 do
    throwErrorAt s "view must be a closed FunctionView; open parameters are unsupported"
  let args := ty.getAppArgs
  let hom := args[2]!
  unless hom.isConst && hom.constName! == r.family do
    throwErrorAt s "family must name the concrete Hom head; aliases/projections are unsupported"
  let hinfo ← getConstInfo r.family
  unless hinfo.isInductive do
    throwErrorAt s "generated-instance mode requires a concrete inductive/structure Hom"
  let inst ← match r.fields.find? (·.key == `bind_instance) with
    | some f => resolvePublic f.value
    | none => pure (r.family ++ `instFunLike)
  pure {
    request := r
    viewName := n
    obj := (← toTerm (args[0]!))
    carrier := (← toTerm (args[1]!))
    hom := (← toTerm hom)
    view := (← toTerm (mkConst n (info.levelParams.map Level.param)))
    instanceName := inst
    levels := info.levelParams }

def decodeComposition (v : ViewPorts) : CommandElabM CompositionPorts := do
  let s ← v.request.field `composition
  let n ← resolvePublic s
  pure { view := v, compositionName := n, composition := mkIdent n }

/-- Give quoted native declarations the specification's rigid universe parameters. -/
def withViewScope (v : ViewPorts) (action : CommandElabM α) : CommandElabM α :=
  withScope (fun s => { s with levelNames := v.levels ++ s.levelNames }) action

private def role (r : FamilyRequest) (name : Name) (regs : Array Name := #[]) : Output :=
  { role := name, name := r.family ++ name, owner := `bundledMap, registrations := regs }

def baseOutputs (v : ViewPorts) : Array Output := Id.run do
  let r := v.request
  let bound := r.fields.any (·.key == `bind_instance)
  return #[{ role r `instFunLike #[`instance] with name := v.instanceName, bound },
    role r `ext #[`ext], role r `ext_iff,
    { role r `id with bound := r.fields.any (·.key == `bind_id) },
    { role r `comp with bound := r.fields.any (·.key == `bind_comp) },
    role r `id_apply #[`simp], role r `comp_apply #[`simp],
    role r `comp_id #[`simp], role r `id_comp #[`simp], role r `comp_assoc]

/-- Compare elaborated terms with rigid lambda-bound endpoints at default transparency. -/
def checkDefEq (left right : Term) : CommandElabM Unit := liftTermElabM do
  Term.withoutErrToSorry do
    let lhs ← Term.elabTerm left none
    let rhs ← Term.elabTermEnsuringType right (← inferType lhs)
    Term.synthesizeSyntheticMVarsNoPostponing
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    if lhs.hasExprMVar || rhs.hasExprMVar then throwError "unresolved contract parameters"
    unless ← withTransparency .default (isDefEq lhs rhs) do
      throwError "definitional contract mismatch at default transparency"

def validateView (v : ViewPorts) : CommandElabM Unit := withViewScope v do
  let O := v.obj; let C := v.carrier; let H := v.hom; let V := v.view
  let inst := mkIdent v.instanceName
  checkDefEq (← `(fun (X Y : $O) => (inferInstance : FunLike ($H X Y) ($C X) ($C Y))))
    (← `(fun (X Y : $O) => ($inst : FunLike ($H X Y) ($C X) ($C Y))))
  checkDefEq (← `(fun (X Y : $O) (f : $H X Y) (x : $C X) => f x))
    (← `(fun (X Y : $O) (f : $H X Y) (x : $C X) => ($V).view f x))

def buildFunctionView (v : ViewPorts) : CommandElabM ViewPorts := withViewScope v do
  let r := v.request
  let O := v.obj; let C := v.carrier; let H := v.hom; let V := v.view
  let inst := mkIdent v.instanceName
  if !(r.fields.any (·.key == `bind_instance)) then
    declare r (← `(public noncomputable instance $inst:declId {X Y : $O} :
      FunLike ($H X Y) ($C X) ($C Y) where
        coe := ($V).view
        coe_injective := ($V).view_injective))
  let ext := mkIdent (r.family ++ `ext)
  declare r (← `(@[ext] public theorem $ext {X Y : $O} {f g : $H X Y}
    (h : ∀ x, f x = g x) : f = g := ($V).ext h))
  validateView v
  pure v

def buildComposition (p : CompositionPorts) : CommandElabM CompositionPorts := withViewScope p.view do
  let v := p.view; let r := v.request
  let O := v.obj; let C := v.carrier; let H := v.hom; let V := v.view; let P := p.composition
  -- Native typechecking fixes the view before any operation is emitted.
  declare r (← `(noncomputable example : ApiBuilder.Composition $V := $P))
  let i := mkIdent (r.family ++ `id); let c := mkIdent (r.family ++ `comp)
  unless r.fields.any (·.key == `bind_id) do
    declare r (← `(@[expose] public noncomputable def $i (X : $O) : $H X X := ($P).identity X))
  unless r.fields.any (·.key == `bind_comp) do
    declare r (← `(@[expose] public noncomputable def $c {X Y Z : $O}
    (g : $H Y Z) (f : $H X Y) : $H X Z := ($P).compose g f))
  let ia := mkIdent (r.family ++ `id_apply); let ca := mkIdent (r.family ++ `comp_apply)
  let ci := mkIdent (r.family ++ `comp_id); let ic := mkIdent (r.family ++ `id_comp)
  let assoc := mkIdent (r.family ++ `comp_assoc)
  declare r (← `(@[simp] public theorem $ia (X : $O) (x : $C X) : $i X x = x :=
    ($P).identity_apply X x))
  declare r (← `(@[simp] public theorem $ca {X Y Z : $O} (g : $H Y Z) (f : $H X Y)
    (x : $C X) : $c g f x = g (f x) := ($P).compose_apply g f x))
  declare r (← `(@[simp] public theorem $ci {X Y : $O} (f : $H X Y) : $c f ($i X) = f :=
    ($P).comp_id $V f))
  declare r (← `(@[simp] public theorem $ic {X Y : $O} (f : $H X Y) : $c ($i Y) f = f :=
    ($P).id_comp $V f))
  declare r (← `(public theorem $assoc {W X Y Z : $O}
    (h : $H Y Z) (g : $H X Y) (f : $H W X) :
    $c ($c h g) f = $c h ($c g f) := ($P).comp_assoc $V h g f))
  pure p

/-- Reconstruct only public named input syntax from an imported receipt. -/
def requestFromReceipt (receipt : FamilyReceipt) : FamilyRequest :=
  { family := receipt.family, ref := Syntax.missing,
    fields := receipt.inputs.map fun (key, name) => { key, value := mkIdent name, ref := Syntax.missing } }

/-- Rigid expected dictionary and ordinary application are checked independently. -/
def validateBase (r : FamilyReceipt) : CommandElabM Unit := do
  let v ← decodeView (requestFromReceipt r)
  let p ← decodeComposition v
  validateView v
  withViewScope v do
    let O := v.obj; let C := v.carrier; let H := v.hom; let V := v.view; let P := p.composition
    let inst := mkIdent v.instanceName
    -- This checks the selected dictionary, not just its type.
    declare v.request (← `(example {X Y : $O} :
      (inferInstance : FunLike ($H X Y) ($C X) ($C Y)) = $inst := rfl))
    declare v.request (← `(example {X Y : $O} (f : $H X Y) (x : $C X) : f x = ($V).view f x := rfl))
    let i := mkIdent (r.family ++ `id); let c := mkIdent (r.family ++ `comp)
    checkDefEq (← `(fun (X : $O) => $i X)) (← `(fun (X : $O) => ($P).identity X))
    checkDefEq (← `(fun (X Y Z : $O) (g : $H Y Z) (f : $H X Y) => $c g f))
      (← `(fun (X Y Z : $O) (g : $H Y Z) (f : $H X Y) => ($P).compose g f))
    declare v.request (← `(example (X : $O) : $i X = ($P).identity X := rfl))
    declare v.request (← `(example {X Y Z : $O} (g : $H Y Z) (f : $H X Y) :
      $c g f = ($P).compose g f := rfl))

def baseValidator : Validator := ⟨validateBase⟩

def prepareBundledMap (r : FamilyRequest) : CommandElabM PreparedRecipe := do
  let v ← decodeView r
  let p ← decodeComposition v
  let mut inputs := #[(`view, v.viewName), (`composition, p.compositionName)]
  if r.fields.any (·.key == `bind_instance) then
    inputs := inputs.push (`bind_instance, v.instanceName)
  for (key, roleName) in #[(`bind_id, `id), (`bind_comp, `comp)] do
    if let some field := r.fields.find? (·.key == key) then
      let name ← resolvePublic field.value
      unless name == r.family ++ roleName do
        throwErrorAt field.ref "bound operation must already have public name '{r.family ++ roleName}'"
      inputs := inputs.push (key, name)
  pure {
    consumed := #[`view, `composition, `bind_instance, `bind_id, `bind_comp]
    inputs := inputs
    outputs := baseOutputs v
    validators := #[``baseValidator]
    execute := do
      let _ ← buildFunctionView v
      let _ ← buildComposition p
      pure () }

def bundledMap : Recipe := ⟨1, prepareBundledMap⟩
end ApiBuilder.Recipes
