module
public meta import ApiBuilder.Family
public meta section
namespace ApiBuilder
open Lean Elab Command
syntax apiField := ident " := " ident
syntax (name := apiFamily) "api_family " ident " using " ident " where " ppLine
  (colGt apiField ppLine)+ : command

private unsafe def evalRecipe (n : Name) : CommandElabM Recipe :=
  evalConstCheck Recipe ``ApiBuilder.Recipe n

@[command_elab apiFamily] unsafe def elabFamily : CommandElab := fun stx => withRef stx do
  withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) do
    let family := stx[1].getId
    unless (← getCurrNamespace).isAnonymous do
      throwError "api_family must occur at the root namespace; family names are fully qualified"
    if (receipts.getState (← getEnv)).any (·.family == family) then
      throwError "family '{family}' already has an accepted receipt"
    let mut fields := #[]
    for f in stx[5].getArgs do
      let key := f[0].getId
      if fields.any (fun (x : Field) => x.key == key) then
        throwErrorAt f "duplicate field '{key}'"
      fields := fields.push { key, value := f[2], ref := f }
    let req : FamilyRequest := { family, ref := stx, fields }
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
    unless (← getConstInfo n).levelParams.isEmpty do
      throwErrorAt stx[3] "recipe entrypoint must have no universe parameters"
    recordExtraModUseFromDecl n (isMeta := true)
    let recipe ← evalRecipe n
    unless recipe.abiVersion == 1 do throwError "unsupported recipe ABI {recipe.abiVersion}"
    let prepared ← recipe.prepare req
    assertNoErrors "preparation"
    for f in fields do
      unless prepared.consumed.contains f.key do throwErrorAt f.ref "unused field '{f.key}'"
    let mut seen : Array Output := #[]
    for out in prepared.outputs do
      if let some old := seen.find? (fun x => x.role == out.role || x.name == out.name) then
        throwError "duplicate ownership: '{old.owner}' and '{out.owner}' claim '{out.role}'"
      if !out.bound && (← getEnv).contains out.name then
        throwError "output collision '{out.name}'; use an explicit binding"
      seen := seen.push out
    prepared.execute
    assertNoErrors "execution"
    let receipt : FamilyReceipt := {
      family, recipe := n, abiVersion := recipe.abiVersion
      inputs := prepared.inputs, outputs := prepared.outputs, validators := prepared.validators }
    checkReceipt receipt
    assertNoErrors "acceptance"
    modifyEnv (receipts.addEntry · receipt)

syntax (name := apiCheck) "#api_check " ident : command
@[command_elab apiCheck] unsafe def elabCheck : CommandElab := fun s => do
  withScope (fun scope => { scope with opts := scope.opts.setBool `Elab.async false }) do
    checkReceipt (← getReceipt s[1].getId)

syntax (name := apiInspect) "#api_inspect " ident : command
@[command_elab apiInspect] def elabInspect : CommandElab := fun s => do
  logInfo m!"{repr (← getReceipt s[1].getId)}"
end ApiBuilder
