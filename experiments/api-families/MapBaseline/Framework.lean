module
public meta import ApiBuilder.Family
public meta import MapBaseline.MacroCommand
public meta import MapBaseline.Contract

public meta section
namespace MapBaseline.Framework
open Lean Elab Command

/-- Closed syntax configuration. Mathematical proof checking remains native Lean;
this adapter adds lifecycle metadata, not a new proof generator. -/
structure Specification where
  context : Array Command
  make : Name → CommandElabM MacroGenerator.Config
  reference : Name

abbrev SpecificationBuilder := CommandElabM Specification

/-- A specification explicitly chooses public local binder names. Its closed
syntax data is normalized consistently across the context and its references. -/
private def publicSyntax {kind : SyntaxNodeKind} (s : TSyntax kind) : TSyntax kind :=
  ⟨s.raw.rewriteBottomUp fun
    | .ident info raw name resolved => .ident info raw name.eraseMacroScopes resolved
    | other => other⟩

private def publicConfig (c : MacroGenerator.Config) : MacroGenerator.Config :=
  { c with
    binders := c.binders.map publicSyntax
    leftExtra := c.leftExtra.map publicSyntax
    source := publicSyntax c.source, target := publicSyntax c.target
    map := publicSyntax c.map, comap := publicSyntax c.comap
    gc := publicSyntax c.gc
    rightProofs := c.rightProofs.map fun (a, b, d) =>
      (publicSyntax a, publicSyntax b, publicSyntax d) }

private unsafe def getSpecification (name : Name) : CommandElabM Specification := do
  let builder ← evalConstCheck SpecificationBuilder ``SpecificationBuilder name
  builder

private def inputName (r : ApiBuilder.FamilyRequest) : CommandElabM Name :=
  r.field `specification >>= ApiBuilder.resolvePublic

private unsafe def validate (r : ApiBuilder.FamilyReceipt) : CommandElabM Unit := do
  let some (_, name) := r.inputs.find? (fun p => p.1 == `specification)
    | throwError "map contract: missing specification input"
  let spec ← getSpecification name
  Contract.check r.family spec.reference

unsafe def validator : ApiBuilder.Validator := ⟨validate⟩

unsafe def prepare (r : ApiBuilder.FamilyRequest) : CommandElabM ApiBuilder.PreparedRecipe := do
  let name ← inputName r
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do
    throwError "map specification builder must be closed"
  let spec ← getSpecification name
  let outputs := Contract.roles.map fun role => {
    role, name := r.family ++ role, owner := `galoisFrontend, registrations := #[`simp] }
  pure {
    consumed := #[`specification]
    inputs := #[(`specification, name)]
    outputs
    validators := #[``validator]
    execute := withScope id do
      for cmd in spec.context do elabCommand (publicSyntax cmd)
      MacroGenerator.emit (publicConfig (← spec.make r.family))
      ApiBuilder.assertNoErrors "map frontend generation" }

unsafe def galoisFrontend : ApiBuilder.Recipe := ⟨1, prepare⟩
end MapBaseline.Framework
