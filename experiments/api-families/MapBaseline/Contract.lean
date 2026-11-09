module
public import Mathlib.Order.GaloisConnection.Basic
public meta import Lean

public meta section
namespace MapBaseline.Contract
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

/-- This independent checker is shared by hand-authored, macro and recipe APIs.
The reference types are authored separately from the generator. -/
def check (family reference : Name) : CommandElabM Unit := do
  let simpSet ← liftCoreM Lean.Meta.getSimpTheorems
  for role in roles do
    let actualName := family ++ role
    let referenceName := reference ++ role
    let some actual := (← getEnv).find? actualName
      | throwError "map contract: missing role '{role}' at '{actualName}'"
    let expected ← getConstInfo referenceName
    unless actual.levelParams.length == expected.levelParams.length do
      throwError "map contract: universe mismatch for '{role}'"
    unless binderKinds actual.type == binderKinds expected.type do
      throwError "map contract: binder mismatch for '{role}'"
    unless publicBinderNames actual.type == publicBinderNames expected.type do
      throwError "map contract: public binder name mismatch for '{role}'"
    liftTermElabM do
      let actualLevels ← mkFreshLevelMVarsFor actual
      let actualType := actual.type.instantiateLevelParams actual.levelParams actualLevels
      unless ← withTransparency .default (isDefEq actualType expected.type) do
        throwError "map contract: type mismatch for '{role}'; expected exactly the independent signature"
      -- Universe binders may be listed in a different order. Accept only a
      -- bijective renaming onto the rigid reference parameters, not a collapse
      -- or extra level constraint introduced by unification.
      let solved ← actualLevels.mapM instantiateLevelMVars
      let expectedLevels := expected.levelParams.map Level.param
      unless solved.all (fun u => expectedLevels.contains u) &&
          expectedLevels.all (fun u => solved.contains u) do
        throwError "map contract: universe generality mismatch for '{role}'"
    unless simpSet.isLemma (.decl actualName) do
      throwError "map contract: missing simp registration for '{role}'"
    if ← liftCoreM (Lean.Meta.isInstance actualName) then
      throwError "map contract: unexpected instance registration for '{role}'"
    if ← liftCoreM (Lean.Meta.Ext.isExtTheorem actualName) then
      throwError "map contract: unexpected ext registration for '{role}'"
    -- Imported module proofs are intentionally hidden by Lean's module system.
    -- Audit bodies at creation time; imported rechecks cover types and effects.
    if !(← getEnv).isImportedConst actualName then
      if let some value := actual.value? (allowOpaque := true) then
        for dep in value.getUsedConstants do
          if reference.isPrefixOf dep then
            throwError "map contract: generated proof uses reference API '{dep}'"
          for obj in #[`Subgroup, `Submodule, `Subring, `Subsemiring, `Subalgebra] do
            if roles.any (fun r => dep == obj ++ r) then
              throwError "map contract: generated proof uses native gold API '{dep}'"

syntax (name := mapContract) "#map_contract " ident " against " ident : command
@[command_elab mapContract] def elabContract : CommandElab := fun s =>
  check s[1].getId s[3].getId
end MapBaseline.Contract
