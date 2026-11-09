module
public import Lean
public meta section
namespace ApiBuilder
open Lean Elab Command

structure Field where
  key : Name
  value : Syntax
  ref : Syntax

structure FamilyRequest where
  family : Name
  ref : Syntax
  fields : Array Field

/-- Roles describe audited public effects, not a sandbox for trusted Lean code. -/
structure Output where
  role : Name
  name : Name
  owner : Name
  bound : Bool := false
  registrations : Array Name := #[]
  deriving Inhabited, BEq, Repr

structure FamilyReceipt where
  family : Name
  recipe : Name
  abiVersion : Nat
  inputs : Array (Name × Name)
  outputs : Array Output
  validators : Array Name
  deriving Inhabited, BEq, Repr

structure PreparedRecipe where
  consumed : Array Name
  inputs : Array (Name × Name)
  outputs : Array Output
  validators : Array Name
  execute : CommandElabM Unit

structure Recipe where
  abiVersion : Nat := 1
  prepare : FamilyRequest → CommandElabM PreparedRecipe

structure Validator where
  check : FamilyReceipt → CommandElabM Unit

abbrev RecipeM := CommandElabM

initialize receipts : SimplePersistentEnvExtension FamilyReceipt (Array FamilyReceipt) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun xs x => if xs.contains x then xs else xs.push x
    addImportedFn := fun xss => xss.foldl (fun xs ys => ys.foldl
      (fun xs y => if xs.contains y then xs else xs.push y) xs) #[]
  }

def FamilyRequest.field (r : FamilyRequest) (key : Name) : CommandElabM Syntax := do
  match r.fields.find? (·.key == key) with
  | some f => pure f.value
  | none => throwErrorAt r.ref "missing field '{key}'"

def resolvePublic (s : Syntax) : CommandElabM Name := withRef s do
  unless s.isIdent do throwError "expected a closed named declaration"
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  unless ((← getEnv).setExporting true).contains n do
    throwError "input '{n}' must be public"
  pure n

def assertNoErrors (phase : String) : CommandElabM Unit := do
  if (← get).messages.hasErrors then throwError "API acceptance failed during {phase}"

/-- Native elaboration with the original family as expansion source. -/
def declare (r : FamilyRequest) (command : Syntax) : CommandElabM Unit := do
  withRef r.ref <| withMacroExpansion r.ref command <| elabCommand command
  assertNoErrors "declaration elaboration"

/-- Native axiom metadata is authoritative, including across imported interfaces. -/
def checkAxioms (names : Array Name) : CommandElabM Unit := do
  for n in names do
    unless ((← getEnv).setExporting true).contains n do
      throwError "missing public declaration '{n}'"
    let axs ← liftCoreM <| collectAxioms n
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "forbidden axiom '{ax}' in '{n}'"

def checkEffects (r : FamilyReceipt) : CommandElabM Unit := do
  let simpSet ← liftCoreM Lean.Meta.getSimpTheorems
  for out in r.outputs do
    let actual := #[
      (`instance, ← liftCoreM <| Lean.Meta.isInstance out.name),
      (`ext, ← liftCoreM <| Lean.Meta.Ext.isExtTheorem out.name),
      (`simp, simpSet.isLemma (.decl out.name))]
    for (kind, present) in actual do
      if out.registrations.contains kind != present && (!out.bound || out.registrations.contains kind) then
        throwError "registration mismatch '{kind}' on '{out.name}'"

private unsafe def evalValidator (n : Name) : CommandElabM Validator :=
  evalConstCheck Validator ``ApiBuilder.Validator n

unsafe def checkReceipt (r : FamilyReceipt) : CommandElabM Unit := do
  checkEffects r
  checkAxioms (r.inputs.map (·.2) ++ r.outputs.map (·.name))
  for n in r.validators do
    unless (← getConstInfo n).levelParams.isEmpty do
      throwError "validator must have no universe parameters"
    recordExtraModUseFromDecl n (isMeta := true)
    let v ← evalValidator n
    v.check r
    assertNoErrors s!"validator {n}"

def getReceipt (family : Name) : CommandElabM FamilyReceipt := do
  let rs := (receipts.getState (← getEnv)).filter (·.family == family)
  unless rs.size == 1 do throwError "expected one accepted receipt for '{family}', found {rs.size}"
  pure rs[0]!

end ApiBuilder
