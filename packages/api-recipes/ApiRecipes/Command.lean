module
public meta import Lean

/-! Shared declaration plumbing, without a recipe registry or dispatcher. -/
public meta section
namespace ApiRecipes.Command
open Lean Elab Command

private def publicBinders : Expr → Expr
  | .forallE n t b i => .forallE n.eraseMacroScopes t (publicBinders b) i
  | .mdata d b => .mdata d (publicBinders b)
  | e => e

elab "api_recipe_type% " value:term : term => do
  return publicBinders (← Meta.inferType (← Term.elabTerm value none))

elab "api_recipe_domain% " value:term : term => do
  let type ← Meta.inferType (← Term.elabTerm value none)
  let .forallE _ domain _ _ := type
    | throwError "recipe: expected a function when selecting its argument type"
  return domain

def familyName (id : Ident) : CommandElabM Name := do
  if id.getId.getRoot == `_root_ then return removeRoot id.getId
  return (← getCurrNamespace) ++ id.getId

def preflight (family : Name) (roles : Array Name) : CommandElabM Unit := do
  for role in roles do
    let name := family ++ role
    if (← getEnv).contains name then throwError "recipe: output collision '{name}'"

/-- Restore synchronous Lean command state, retaining native diagnostics. -/
def batch (action : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← get
  try
    withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) action
  catch ex =>
    let messages := (← get).messages
    set { saved with messages }
    throw ex

def checkAxioms (name : Name) : CommandElabM Unit := do
  for ax in (← liftCoreM <| collectAxioms name) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "recipe: forbidden axiom '{ax}' in '{name}'"

inductive Effect where
  | plain | simp | coe | inst (priority : Nat)

def publish (name : Name) (value : Term) (effect : Effect := .plain) : CommandElabM Unit := do
  let id := mkIdent (`_root_ ++ name)
  let ref ← getRef
  addDeclarationRangesFromSyntax name ref
  let decl ← match effect with
    | .plain => `(public theorem $id : api_recipe_type% $value := $value)
    | .simp => `(@[simp] public theorem $id : api_recipe_type% $value := $value)
    | .coe => `(@[simp, norm_cast] public theorem $id : api_recipe_type% $value := $value)
    | .inst n =>
      let priority := Syntax.mkNumLit (toString n)
      `(public instance (priority := $priority:num) $id : api_recipe_type% $value := $value)
  withMacroExpansion ref decl <| elabCommand decl
  if (← get).messages.hasErrors then throwError "recipe: failed to generate '{name}'"
  checkAxioms name

abbrev Binders := Array (TSyntax ``Parser.Term.bracketedBinder)

/-- Explicit contracts avoid inferring a reduced reflexive statement from a proof. -/
def publishTyped (name : Name) (bs : Binders) (type proof : Term) (simp := false) : CommandElabM Unit := do
  let id := mkIdent (`_root_ ++ name)
  let ref ← getRef
  addDeclarationRangesFromSyntax name ref
  let decl ← if simp then `(@[simp] public theorem $id $bs:bracketedBinder* : $type := $proof)
    else `(public theorem $id $bs:bracketedBinder* : $type := $proof)
  withMacroExpansion ref decl <| elabCommand decl
  if (← get).messages.hasErrors then throwError "recipe: failed to generate '{name}'"
  checkAxioms name

def publishDefinition (name : Name) (bs : Binders) (value : Term) : CommandElabM Unit := do
  let id := mkIdent (`_root_ ++ name)
  let ref ← getRef
  addDeclarationRangesFromSyntax name ref
  let decl ← `(@[expose] public noncomputable def $id $bs:bracketedBinder* := $value)
  withMacroExpansion ref decl <| elabCommand decl
  if (← get).messages.hasErrors then throwError "recipe: failed to generate '{name}'"
  checkAxioms name

syntax selection := "only" "[" ident,* "]"

def select (allowed : Array Name) (selection : TSyntax ``selection) : CommandElabM (Array Name) := do
  let ids := selection.raw[2].getSepArgs
  if ids.isEmpty then throwError "recipe: select at least one role"
  let mut seen := #[]
  for id in ids do
    let key := id.getId
    unless allowed.contains key do throwErrorAt id "recipe: unsupported role '{key}'"
    if seen.contains key then throwErrorAt id "recipe: duplicate role '{key}'"
    seen := seen.push key
  return allowed.filter seen.contains

/-- Stable public names without capturing an identifier in user-supplied syntax. -/
private partial def syntaxContains (name : Name) (s : Syntax) : Bool :=
  (s.isIdent && s.getId.eraseMacroScopes == name) || s.getArgs.any (syntaxContains name)

def publicIdent (base : Name) (inputs : Array Syntax) : Ident := Id.run do
  let mut name := base
  let mut index := 0
  while inputs.any (syntaxContains name) do
    index := index + 1
    name := base.appendAfter ("_" ++ toString index)
  return mkIdent name

/-- Construction recipes support explicit named operation parameters.
Type/instance parameters can remain in the surrounding Lean section. -/
def explicitArgs (bs : Binders) : CommandElabM (Array Term) := do
  let mut args := #[]
  for b in bs do
    match b with
    | `(bracketedBinder| ($names:ident* : $_)) =>
      for name in names do args := args.push ⟨name.raw⟩
    | _ => throwErrorAt b "recipe: construction parameters must be explicit named binders"
  return args

syntax field := ident " := " term

def fields (allowed : Array Name) (inputs : Array Syntax) : CommandElabM (Array Term) := do
  let mut found : Array (Name × Term) := #[]
  for input in inputs do
    let key := input[0].getId
    unless allowed.contains key do throwErrorAt input "recipe: unknown field '{key}'"
    if found.any (·.1 == key) then throwErrorAt input "recipe: duplicate field '{key}'"
    found := found.push (key, ⟨input[2]⟩)
  for key in allowed do
    unless found.any (·.1 == key) do throwError "recipe: missing field '{key}'"
  return allowed.map fun key => (found.find? (·.1 == key)).get!.2
end ApiRecipes.Command
