module
public import Mathlib.Order.GaloisConnection.Basic
public meta import GaloisApi.Basic

public meta section
namespace GaloisApi.Check
open Lean Elab Command Meta

def roles : Array Name :=
  #[`map_sup, `map_iSup, `map_bot, `comap_inf, `comap_iInf, `comap_top]

private def binderKinds : Expr → List BinderInfo
  | .forallE _ _ body info => info :: binderKinds body
  | _ => []

private def publicBinderNames : Expr → List Name
  | .forallE _ _ body .instImplicit => publicBinderNames body
  | .forallE name _ body _ => name :: publicBinderNames body
  | _ => []

/-- Check exported names against an independently authored interface. -/
def check (family reference : Name) (selected : Array Name := roles) : CommandElabM Unit := do
  let simpSet ← liftCoreM Lean.Meta.getSimpTheorems
  for role in selected do
    let actualName := family ++ role
    let referenceName := reference ++ role
    unless ((← getEnv).setExporting true).contains actualName do
      throwError "galois API contract: missing public role '{role}'"
    let some actual := (← getEnv).find? actualName
      | throwError "galois API contract: missing role '{role}' at '{actualName}'"
    let expected ← getConstInfo referenceName
    unless actual.levelParams.length == expected.levelParams.length do
      throwError "galois API contract: universe mismatch for '{role}'"
    unless binderKinds actual.type == binderKinds expected.type do
      throwError "galois API contract: binder mismatch for '{role}'"
    unless publicBinderNames actual.type == publicBinderNames expected.type do
      throwError "galois API contract: public binder name mismatch for '{role}'"
    liftTermElabM do
      let actualLevels ← mkFreshLevelMVarsFor actual
      let actualType := actual.type.instantiateLevelParams actual.levelParams actualLevels
      unless ← withTransparency .default (isDefEq actualType expected.type) do
        throwError "galois API contract: type mismatch for '{role}'; expected exactly the independent signature"
      -- Universe binders may be listed in a different order. Accept only a
      -- bijective renaming onto the rigid reference parameters, not a collapse
      -- or extra level constraint introduced by unification.
      let solved ← actualLevels.mapM instantiateLevelMVars
      let expectedLevels := expected.levelParams.map Level.param
      unless solved.all (fun u => expectedLevels.contains u) &&
          expectedLevels.all (fun u => solved.contains u) do
        throwError "galois API contract: universe generality mismatch for '{role}'"
    unless simpSet.isLemma (.decl actualName) do
      throwError "galois API contract: missing simp registration for '{role}'"
    if ← liftCoreM (Lean.Meta.isInstance actualName) then
      throwError "galois API contract: unexpected instance registration for '{role}'"
    if ← liftCoreM (Lean.Meta.Ext.isExtTheorem actualName) then
      throwError "galois API contract: unexpected ext registration for '{role}'"
    GaloisApi.checkAxioms actualName

private def resolveFamily (id : Ident) : CommandElabM Name := do
  if id.getId.getRoot == `_root_ then return removeRoot id.getId
  let relative := (← getCurrNamespace) ++ id.getId
  let env ← getEnv
  if roles.any (fun r => env.contains (relative ++ r)) then return relative
  return id.getId

syntax (name := checkGaloisApi) "#check_galois_api " ident " against " ident
  (GaloisApi.apiSelection)? : command
@[command_elab checkGaloisApi] def elabContract : CommandElab := fun s => do
  let selected := s[4].getArgs[0]?.map fun t =>
    t[2].getSepArgs.map (fun x => (⟨x⟩ : Ident))
  check (← resolveFamily ⟨s[1]⟩) (← resolveFamily ⟨s[3]⟩)
    (← GaloisApi.selectRoles roles selected)
end GaloisApi.Check
