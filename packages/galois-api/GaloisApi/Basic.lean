module
public import Mathlib.Order.GaloisConnection.Basic
public meta import Lean.Elab.Command

/-! Native API export from a Galois connection, with a separate weak preimage route.
This module depends on Lean and mathlib; it has no recipe dispatcher or registry. -/

public meta section
namespace GaloisApi
open Lean Elab Command

def mapRoles : Array Name := #[`map_sup, `map_iSup, `map_bot]
def comapRoles : Array Name := #[`comap_inf, `comap_iInf, `comap_top]
def allRoles : Array Name := mapRoles ++ comapRoles

private def publicBinders : Expr → Expr
  | .forallE n t b i => .forallE n.eraseMacroScopes t (publicBinders b) i
  | .mdata d b => .mdata d (publicBinders b)
  | e => e

def checkAxioms (name : Name) : CommandElabM Unit := do
  for ax in (← liftCoreM <| collectAxioms name) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "galois_api: forbidden axiom '{ax}' in '{name}'"

elab "galois_api_type% " proof:term : term => do
  let value ← Term.elabTerm proof none
  return publicBinders (← Meta.inferType value)

private def publish (name : Name) (proof : Term) : CommandElabM Unit := do
  let id := mkIdent (`_root_ ++ name)
  let ref ← getRef
  addDeclarationRangesFromSyntax name ref
  let command ← `(@[simp] public theorem $id : galois_api_type% $proof := $proof)
  withMacroExpansion ref command <| elabCommand command
  if (← get).messages.hasErrors then
    throwError "galois_api: failed to prove '{name}'"
  checkAxioms name

def selectRoles (allowed : Array Name) (chosen : Option (Array Ident)) : CommandElabM (Array Name) := do
  let some chosen := chosen | return allowed
  if chosen.isEmpty then throwError "galois_api: select at least one role"
  let mut seen := #[]
  for id in chosen do
    let n := id.getId
    unless allowed.contains n do throwErrorAt id "galois_api: unsupported role '{n}'"
    if seen.contains n then throwErrorAt id "galois_api: duplicate role '{n}'"
    seen := seen.push n
  return allowed.filter seen.contains

private def familyName (id : Ident) : CommandElabM Name := do
  if id.getId.getRoot == `_root_ then return removeRoot id.getId
  return (← getCurrNamespace) ++ id.getId

private def preflight (family : Name) (roles : Array Name) : CommandElabM Unit := do
  for role in roles do
    let n := family ++ role
    if (← getEnv).contains n then
      throwError "galois_api: output collision '{n}'; select only the missing roles"

/-- Roll back the command environment on a synchronous generation failure.
Native diagnostics are retained. This fixed generator performs no external IO. -/
private def batch (action : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← get
  try
    withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) action
  catch ex =>
    let messages := (← get).messages
    set { saved with messages }
    throw ex

private def generate (family : Name) (bs : Array (TSyntax ``Parser.Term.bracketedBinder))
    (gc : Term) (roles : Array Name) : CommandElabM Unit := batch do
  preflight family roles
  let bs := bs.map (fun b => (⟨b.raw⟩ : TSyntax ``Parser.Term.funBinder))
  let index ← liftCoreM <| mkFreshUserName `uGaloisIndex
  let indexId := mkIdent index
  let level : TSyntax `level := ⟨indexId.raw⟩
  elabCommand (← `(universe $indexId))
  for role in roles do
    let proof ← match role with
      | `map_sup => `(fun $bs:funBinder* (p q : _) =>
          GaloisConnection.l_sup (a₁ := p) (a₂ := q) $gc)
      | `map_iSup => `(fun {ι : Sort $level} $bs:funBinder* (p : ι → _) =>
          GaloisConnection.l_iSup (f := p) $gc)
      | `map_bot => `(fun $bs:funBinder* => GaloisConnection.l_bot $gc)
      | `comap_inf => `(fun $bs:funBinder* (p q : _) =>
          GaloisConnection.u_inf (b₁ := p) (b₂ := q) $gc)
      | `comap_iInf => `(fun {ι : Sort $level} $bs:funBinder* (p : ι → _) =>
          GaloisConnection.u_iInf (f := p) $gc)
      | `comap_top => `(fun $bs:funBinder* => GaloisConnection.u_top $gc)
      | _ => throwError "galois_api: internal unsupported role"
    publish (family ++ role) proof

syntax apiSelection := "only" "[" ident,* "]"
syntax (name := galoisApi) "galois_api " ident bracketedBinder* " using " term
  (apiSelection)? : command
syntax (name := galoisMapApi) "galois_map_api " ident bracketedBinder* " using " term
  (apiSelection)? : command
syntax (name := galoisComapApi) "galois_comap_api " ident bracketedBinder* " using " term
  (apiSelection)? : command

private def chosenRoles (s : Option (TSyntax ``apiSelection)) : Option (Array Ident) :=
  s.map fun t => t.raw[2].getSepArgs.map (fun x => ⟨x⟩)

elab_rules : command
  | `(galois_api $family $bs:bracketedBinder* using $gc $[$selection:apiSelection]?) => do
    generate (← familyName family) bs gc (← selectRoles allRoles (chosenRoles selection))
  | `(galois_map_api $family $bs:bracketedBinder* using $gc $[$selection:apiSelection]?) => do
    generate (← familyName family) bs gc (← selectRoles mapRoles (chosenRoles selection))
  | `(galois_comap_api $family $bs:bracketedBinder* using $gc $[$selection:apiSelection]?) => do
    generate (← familyName family) bs gc (← selectRoles comapRoles (chosenRoles selection))

syntax preimageField := ident " := " term
syntax (name := preimageApi) "preimage_api " ident bracketedBinder* " using " term
  " on " term " where " ppLine (colGt preimageField ppLine)+ : command

@[command_elab preimageApi] def elabPreimage : CommandElab := fun s => do
  let family ← familyName ⟨s[1]⟩
  let bs := s[2].getArgs.map (fun b => (⟨b⟩ : TSyntax ``Parser.Term.funBinder))
  let comap : Term := ⟨s[4]⟩
  let target : Term := ⟨s[6]⟩
  let fields := s[8].getArgs
  let mut inputs : Array (Name × Term) := #[]
  for f in fields do
    let key := f[0].getId
    unless #[`inf, `iInf, `top].contains key do
      throwErrorAt f "preimage_api: unknown field '{key}'"
    if inputs.any (·.1 == key) then throwErrorAt f "preimage_api: duplicate field '{key}'"
    inputs := inputs.push (key, ⟨f[2]⟩)
  for key in #[`inf, `iInf, `top] do
    unless inputs.any (·.1 == key) do throwError "preimage_api: missing field '{key}'"
  let inf := (inputs.find? (·.1 == `inf)).get!.2
  let iInf := (inputs.find? (·.1 == `iInf)).get!.2
  let top := (inputs.find? (·.1 == `top)).get!.2
  batch do
    preflight family comapRoles
    let index ← liftCoreM <| mkFreshUserName `uPreimageIndex
    let indexId := mkIdent index
    let level : TSyntax `level := ⟨indexId.raw⟩
    elabCommand (← `(universe $indexId))
    publish (family ++ `comap_inf) (← `(fun $bs:funBinder* (p q : $target) =>
      ($inf : $comap (p ⊓ q) = $comap p ⊓ $comap q)))
    publish (family ++ `comap_iInf) (← `(fun {ι : Sort $level} $bs:funBinder* (p : ι → $target) =>
      ($iInf : $comap (⨅ i, p i) = ⨅ i, $comap (p i))))
    publish (family ++ `comap_top) (← `(fun $bs:funBinder* => ($top : $comap (⊤ : $target) = ⊤)))

end GaloisApi
